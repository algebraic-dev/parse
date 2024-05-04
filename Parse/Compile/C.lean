import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Init.Meta

import Alloy.C
import Alloy.C.Grammar

import Parse.Lowering
import Parse.Compile.C.Helpers

/-!
  Compiles a [Parse.Syntax.Grammar] into C using the alloy library
-/

namespace Parse.Compile.C

open scoped Alloy.C
open Lean.Elab Command Term Lean Parser Command Std
open Parse.Syntax Parse.Lowering

structure CompileState where
  state : Nat
  names : Array String
  maps: HashMap Interval Nat
  deriving Inhabited

abbrev CompileM := StateT CompileState CommandElabM

def CompileM.get (f: CompileState -> α) : CompileM α :=
  f <$> StateT.get

def CompileM.modify (f: CompileState -> CompileState) : CompileM Unit :=
  StateT.modifyGet (((), ·) ∘ f)

def CompileM.getInterval (int: Interval) : CompileM Ident := do
  let maps ← CompileM.get CompileState.maps
  if let some res := maps.find? int then
    pure $ genParseIdent "bitmap" res
  else do
    let size := maps.size
    CompileM.modify (λstate => { state with maps := state.maps.insert int state.maps.size })
    pure $ genParseIdent "bitmap" size

def CompileM.run (c: CompileM α) : CommandElabM α :=
  Prod.fst <$> StateT.run c Inhabited.default

-- Compile

abbrev Code := Array (TSyntax `cStmtLike)

def compileInterval (int: Interval) : CompileM (TSyntax `cExpr) := do
  `(cExpr| $(← CompileM.getInterval int)[*$pointerName])

def compileCheck (check: Check) : CompileM (TSyntax `cExpr) := do
  match check with
  | .char c => `(cExpr| *p == $(mkCharLit c))
  | .range range => compileRange (← `(cExpr | *$pointerName)) range
  | .interval int => compileInterval int

mutual
  partial def ifStmt (code: Code) (comparison: TSyntax `cExpr) (ok: Instruction false) (otherwise: Instruction false) : CompileM Code := do
    let ok ← compileInstruction #[] ok
    let otherwise ← compileInstruction #[] otherwise
    let code := code.push (← `(cStmtLike | if ($comparison) { $ok* }))
    return code.append otherwise

  partial def compileConsumer (code: Code) : Consumer (Instruction false) → CompileM Code
    | .is str ok otherwise => do
      let cur ← CompileM.get CompileState.state
        let n := mkNumLit (str.toSubstring.bsize)
        let str := TSyntax.mk $ Syntax.mkStrLit str
        let code := code.push (← `(cStmtLike| int result = match_string(data, $str, $n, $pointerName, $endPointerName);))
        let state := genParseIdent "state" cur
        let then_ ← compileInstruction #[] ok
        let otherwise ← compileInstruction #[] otherwise
        return code.push (← `(cStmt| switch (result) {
          case PAUSED: return $state;
          case FAIL: { $otherwise* }
          case SUCCEEDED: { $then_* }
        }))
    | .char chr ok otherwise => do
      let comparison ← `(cExpr| *$pointerName == $(mkCharLit chr))
      ifStmt code comparison ok otherwise
    | .range range ok otherwise => do
      let comparison ← compileRange (← `(cExpr| *$pointerName)) range
      ifStmt code comparison ok otherwise
    | .map int ok otherwise => do
      let comparison ← compileInterval int
      ifStmt code comparison ok otherwise
    | .chars alts otherwise => do
      let otherwise ← compileInstruction #[] otherwise
      let alts ← alts.mapM $ λ(case, to) => do
        let next ← compileInstruction #[] to
        `(cStmt| case $(mkCharLit case):constExpr : { $next* })
      let alts := alts.push (← `(cStmt| default : { $otherwise* }))
      return code.push (← `(cStmt| switch (*p) { $alts* }))
    | .mixed alts otherwise => do
      let otherwise ← compileInstruction #[] otherwise
      let alts ← alts.mapM $ λ(check, to) => do
        let next ← compileInstruction #[] to
        let map ← compileCheck check
        `(cStmt| if ($map) { $next* })
      let alts := alts.append otherwise
      return code.append alts

  partial def compileInstruction (code: Code) : Instruction β → CompileM Code
  | .check next => do
      let cur ← CompileM.get CompileState.state
      let state := genParseIdent "state" cur
      let code := code.push (← `(cStmt| if (*p == '\x00') return $state;))
      compileInstruction code next
    | .next num next => do
      let code := code.push (← `(cStmt| p += $(mkNumLit num);))
      compileInstruction code next
    | .store prop data next => do
      let names ← CompileM.get CompileState.names
      let prop := mkIdent s!"prop_{names.get! prop}"
      let data ←
        match data with
        | some data => `(cExpr| $(mkNumLit data))
        | none => `(cExpr| *p)
      let code := code.push (← `(cStmt| data->$prop = $data;))
      compileInstruction code next
    | .capture prop next => do
      let names ← CompileM.get CompileState.names
      let prop := mkIdent s!"prop_{names.get! prop}_start_span"
      let code := code.push (← `(cStmt| data->$(prop) = p;))
      compileInstruction code next
    | .close prop next => do
      -- need to add callback lol
      let names ← CompileM.get CompileState.names
      let prop := mkIdent s!"prop_{names.get! prop}_start_span"
      let code := code.push (← `(cStmt| data->$(prop) = p;))
      compileInstruction code next
    | .goto to => do
      let state := genParseIdent "state" to
      return code.push (← `(cStmt| goto $state:ident;))
    | .call _ next => do
      -- need to add callbacks!
      compileInstruction code next
    | .error errCode => do
      return code.push (← `(cStmt| return -$(mkNumLit (errCode + 1));))
    | .consumer consumer =>
      compileConsumer code consumer
end

def compileTyp : Typ → Ident
  | .u8 => mkIdent "uint8_t"
  | .char => mkIdent "uint8_t"
  | .u16 => mkIdent "uint16_t"
  | .u32 => mkIdent "uint32_t"
  | .span => mkIdent "uint64_t"

def compilePropName (name: String) : Typ → Ident
  | .span => mkIdent s!"prop_{name}_start_span"
  | _ => mkIdent s!"prop_{name}"

-- Commands

def enumStates (machine: Machine) : CommandElabM (TSyntax `cCmd) := do
  let states ← machine.nodes.mapIdxM (λi _ => `(Alloy.C.enumerator| $(genParseIdent "state" i)))
  let states := withComma states
  `(cCmd|
    enum state_e {
      $states,*
    };
  )

def dataStruct (storage: Storage) : CommandElabM (TSyntax `cCmd) := do
  let fields ← storage.nodes.mapM $ λ(name, typ) => do
    let typName := compileTyp typ
    let ident := compilePropName name typ
    `(Alloy.C.aggrDeclaration| $typName $ident; )

  `(cCmd|
    typedef struct data_t {
      uint8_t call;
      uint8_t pointer;
      $fields*
    } data_t;
  )

def matchStr : CommandElabM (TSyntax `cCmd) := do
  `(cCmd|
    uint32_t match_string(data_t *data, char* s, int len, const char* p, const char* endp) {
      p += data->pointer;
      for(; p != endp; p++) {
        if (data->pointer == len-1) {
          data->pointer = 0;
          return SUCCEEDED;
        } else if (*p == s[data->pointer]) {
          data->pointer += 1;
        } else {
          return FAIL;
        }
      }
      return PAUSED;
    }
  )

def alloyParse (name: Ident) (branches: Array (TSyntax `cStmtLike)) : CommandElabM (TSyntax `cCmd) := do
  `(cCmd|
    uint32_t $name:ident (uint32_t state, data_t *data, const char* p, const char* endp) {
      switch (state) {
        $branches*
        default:
          return -1;
      }
    }
  )

def compileBranch (machine: Machine) : CommandElabM (Array (TSyntax `cStmtLike)) := CompileM.run do
  CompileM.modify (λstate => {state with names := machine.storage.nodes.map Prod.fst})

  let mut branches := #[]

  for (idx, inst) in machine.nodes.mapIdx ((·, ·)) do
    CompileM.modify (λmachine => {machine with state := idx })
    let name := genParseIdent "state" idx
    let alts ← compileInstruction #[] inst.instruction
    branches := branches.push (← `(cStmtLike| case $name:ident: $name:ident: {$alts*}))

  return branches

def compile (name: Ident) (machine: Machine) : CommandElabM (TSyntax `command) := do

  `(
    namespace $name
      alloy c include "lean/lean.h" "stdlib.h" "stdio.h"

      alloy c section
        #define FAIL 0
        #define PAUSED 1
        #define SUCCEEDED 2

        $(← enumStates machine)
        $(← dataStruct machine.storage)
        $(← matchStr)

        $(← alloyParse (mkIdent "alloy_parse") (← compileBranch machine))
      end

      alloy c opaque_extern_type Data => data_t where
        foreach(s, f) := lean_apply_1(f, s->m_s)
        finalize(s) := lean_dec(s->m_s); free(s)

      alloy c extern
      def $(mkIdent "create") (s: Unit) : Data := {
        data_t* data = calloc(sizeof(data_t), 0);
        return to_lean<Data>(data);
      }

      alloy c extern
      def parse (data_obj: @&Data) (state: UInt32) (s: String) (size: UInt32) : UInt32 := {
        const char* str = lean_string_cstr(s);
        const char* strend = str + size;
        data_t* data = lean_get_external_data(data_obj);
        int res = alloy_parse(state, data, str, strend);
        return res;
      }
    end $name
  )
