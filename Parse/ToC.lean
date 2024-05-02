import Parse.Compile
import Parse.Syntax

import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Init.Meta

import Alloy.C
import Alloy.C.Grammar
import Parse.Interval

/-!
  Compilation of Instructions to C
-/

namespace Parse.ToC

open Lean.Elab Command Term Lean Parser Command Std
open scoped Alloy.C Parse.Interval
open Parse.Syntax

def mkNumLit [ToString α] (x: α) : TSyntax `num :=
  TSyntax.mk (Syntax.mkNumLit (ToString.toString x))

inductive MatchType where
  | singleRanged (range: Interval.Interval) (to: Compile.Instruction false)
  | singleChar (char: Char) (to: Compile.Instruction false)
  | noRanges (alts: Array (Char × Compile.Instruction false))
  | mixed (alts: Array (Compile.Check × Compile.Instruction false))

def classifyMatch (alts: Array (Compile.Check × Compile.Instruction false)) : MatchType :=
  if alts.size == 1 then
    let (first, inst) := alts.get! 0
    match first with
    | .char c => .singleChar c inst
    | .map int => .singleRanged int inst
  else
    if alts.all (Compile.Check.isChar ∘ Prod.fst)
      then .noRanges (alts.filterMap (λ(chr, inv) => (· , inv) <$> (Compile.Check.getChar chr)))
      else MatchType.mixed alts

def withSep (alts: Array (TSyntax α)) : Syntax.TSepArray α "," :=
  alts.foldl Syntax.TSepArray.push (Syntax.TSepArray.mk #[] (sep := ","))

def genBitMap (name: Ident) (int: Parse.Interval.Interval) : CommandElabM (TSyntax `Alloy.C.declaration) := do
  let mut alts := #[]

  for i in [0:255] do
    let int := mkNumLit (if int.in i.toUInt8 then 1 else 0)
    let lit ← `(Alloy.C.initializerElem | $int)
    alts := alts.push lit

  let f := withSep alts

  `(Alloy.C.declaration | int $name:ident[255] = {$f,*,})

def mkCharLit (char: Char) : TSyntax `char :=
  TSyntax.mk $ Syntax.mkLit charLitKind (Char.quote char)

def genComparison (name: TSyntax `cExpr) (range: Parse.Interval.Range) : CommandElabM (TSyntax `cExpr) := do
  let fstChar : TSyntax `char := mkCharLit $ Char.ofNat (range.val.fst.toNat)
  if range.val.fst != range.val.snd
    then let sndChar : TSyntax `char := mkCharLit $ Char.ofNat (range.val.snd.toNat)
         if range.val.fst == range.val.snd - 1
          then `(cExpr | ($name == $fstChar || $name == $sndChar))
          else `(cExpr | ($name >= $fstChar && $name <= $sndChar))
    else `(cExpr | ($name == $fstChar))

def genIdent (name: String) (num: Nat) : Ident :=
  mkIdent (Name.mkStr1 s!"parse_{name}_{num}")

def stateIdent (num: Nat) : Ident :=
  genIdent "state" num

structure CompileState where
  state : Nat
  names : Array String
  maps: HashMap Parse.Interval.Interval Nat
  deriving Inhabited

abbrev CompileM := StateT CompileState CommandElabM

def CompileM.get (f: CompileState -> α) : CompileM α :=
  f <$> StateT.get

def CompileM.modify (f: CompileState -> CompileState) : CompileM Unit :=
  StateT.modifyGet (((), ·) ∘ f)

def CompileM.getIntervalMap (int: Parse.Interval.Interval) : CompileM Ident := do
  let maps ← CompileM.get CompileState.maps
  if let some res := maps.find? int
    then pure $ genIdent "bitmap" res
    else do
      let size := maps.size
      CompileM.modify (λstate => { state with maps := state.maps.insert int state.maps.size })
      pure $ genIdent "bitmap" size

def CompileM.run (c: CompileM α) : CommandElabM α :=
  Prod.fst <$> StateT.run c Inhabited.default

def compileInterval (int: Interval.Interval) : CompileM (TSyntax `cExpr) := do
  if int.size == 1
    then let range := int.get! 0
         genComparison (← `(cExpr | *p)) range
    else let map ← CompileM.getIntervalMap int
         `(cExpr| $map[*p])

def compileCheck (check: Compile.Check) : CompileM (TSyntax `cExpr) := do
  match check with
  | .char c => `(cExpr| *p == $(mkCharLit c))
  | .map map => compileInterval map

partial def compileInstruction (code: Array (TSyntax `cStmtLike)): Parse.Compile.Instruction α → CompileM (Array (TSyntax `cStmtLike))
  | .next num next => do
      let code := code.push (← `(cStmt| p += $(mkNumLit num);))
      compileInstruction code next
  | .store prop data next => do
      let names ← CompileM.get CompileState.names
      let prop := mkIdent $ names.get! prop
      let data ←
        match data with
        | some data => `(cExpr| $(mkNumLit data))
        | none => `(cExpr| *p)
      let code := code.push (← `(cStmt| data->$prop = $data;))
      compileInstruction code next
  | .capture prop next => do
      let names ← CompileM.get CompileState.names
      let prop := mkIdent $ names.get! prop
      let code := code.push (← `(cStmt| data->$(prop).start = p;))
      compileInstruction code next
  | .close prop next => do
      let names ← CompileM.get CompileState.names
      let prop := mkIdent $ names.get! prop
      let code := code.push (← `(cStmt| data->$(prop).close = p;))
      compileInstruction code next
  | .check next => do
      let cur ← CompileM.get CompileState.state
      let state := genIdent "state" cur
      let code := code.push (← `(cStmt| if (*p == '\x00') return $state;))
      compileInstruction code next
  | .is str then_ otherwise =>  do
      let cur ← CompileM.get CompileState.state
      let n := mkNumLit (str.toSubstring.bsize)
      let str := TSyntax.mk $ Syntax.mkStrLit str
      let code := code.push (← `(cStmtLike| int result = match_string(data, p, $str, $n);))
      let state := genIdent "state" cur
      let then_ ← compileInstruction #[] then_
      let otherwise ← compileInstruction #[] otherwise
      return code.push (← `(cStmt| switch (result) {
        case paused: return $state;
        case fail: { $otherwise* }
        case succeded: { $then_* }
      }))
  | .switch alts otherwise => do
      let otherwise ← compileInstruction #[] otherwise
      let typ := classifyMatch alts
      match typ with
      | .singleRanged int to =>
        let next ← compileInstruction #[] to
        let int ← compileInterval int
        `(cStmt| if ($int) {
          $next*
        } else {
          $otherwise*
        })
      | .singleChar char to => do
        let then_ ← compileInstruction #[] to
        return code.push (← `(cStmt| if (*p == $(mkCharLit char)) {
          $then_*
        } else {
          $otherwise*
        }))
      | .noRanges alts => do
        let alts ← alts.mapM $ λ(case, to) => do
          let next ← compileInstruction #[] to
          `(cStmt| case $(mkCharLit case):constExpr : { $next* })
        let alts := alts.push (← `(cStmt| default : { $otherwise* }))
        return code.push (← `(cStmt| switch (*p) { $alts* }))
      | .mixed alts =>
        let alts ← alts.mapM $ λ(check, to) => do
          let next ← compileInstruction #[] to
          let map ← compileCheck check
          `(cStmt| if ($map) { $next* })
        let alts := alts.append otherwise
        return code.append alts
  | .goto to => do
      let state := stateIdent to
      return code.push (← `(cStmt| goto $state:ident;))
  | .stop call to => do
      let state := genIdent "state" to
      let code := code.push (← `(cStmt| data->call = $(mkNumLit call);))
      return code.push (← `(cStmt| return $state;))
  | .error errCode => do
      return code.push (← `(cStmt| return -$(mkNumLit (errCode + 1));))

def compileGrammar (name: Ident) (grammar: Syntax.Grammar) : CompileM Syntax := do
  let mut branches := #[]

  CompileM.modify (λmachine => {machine with names := grammar.storage.nodes.map Prod.fst})

  let machine := Parse.Compile.compile grammar

  for (idx, inst) in machine.nodes.mapIdx ((·, ·)) do
    CompileM.modify (λmachine => {machine with state := idx })
    let name := stateIdent idx
    let alts ← compileInstruction #[] inst.instruction
    branches := branches.push (← `(cStmtLike| case $name:ident: $name:ident: {$alts*}))

  let states ← machine.nodes.mapIdxM (λi _ => `(Alloy.C.enumerator| $(genIdent "state" i)))
  let states := withSep states

  let fields ← machine.storage.nodes.mapM $ λ(name, typ) => do
    let typ := match typ with
      | .u8 => mkIdent "uint8_t"
      | .char => mkIdent "uint8_t"
      | .u32 => mkIdent "uint32_t"
      | .u16 => mkIdent "uint16_t"
      | .span => mkIdent "span_t"
    let ident := mkIdent name
    `(Alloy.C.aggrDeclaration| $typ $ident; )

  let zero := mkCharLit (Char.ofNat 0)

  `(alloy c include "lean/lean.h" "stdlib.h" "stdio.h"

    alloy c section
    #define fail 0
    #define paused 1
    #define succeded 2

    enum state_e {
      $states,*
    };

    typedef struct pair {
      const char* start;
      const char* close;
    } span_t;

    typedef struct data_t {
      uint8_t call;
      uint8_t pointer;
      $fields*
    } data_t;
    end

    alloy c opaque_extern_type Data => data_t where
      foreach(s, f) := lean_apply_1(f, s->m_s)
      finalize(s) := lean_dec(s->m_s); free(s)

    alloy c extern
    def $(mkIdent "createData") (s: Unit) : Data := {
      data_t* data = calloc(sizeof(data_t), 0);
      return to_lean<Data>(data);
    }

    alloy c section
      uint32_t match_string(data_t *data, const char* p, char* s, int len) {
        p += data->pointer;
        for(; *p != $zero; p++) {
          if (data->pointer == len-1) {
            data->pointer = 0;
            return succeded;
          } else if (*p == s[data->pointer]) {
            data->pointer += 1;
          } else {
            return fail;
          }
        }
        return paused;
      }

      uint32_t alloy_parse(uint32_t state, data_t *data, const char* p) {
        switch (state) {
          $branches*
          default:
            return -1;
        }
      }
    end

    alloy c extern
    def $name (data_obj: @&Data) (state: UInt32) (s: String) : UInt32 := {
      const char* str = lean_string_cstr(s);
      data_t* data = lean_get_external_data(data_obj);
      int res = alloy_parse(state, data, str);
      return res;
    }
   )

def compile (name: Ident) (grammar: Syntax.Grammar) : CommandElabM Syntax :=
  CompileM.run (compileGrammar name grammar)
