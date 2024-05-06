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
  props : Array String
  calls : Array String
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

def genCheck (code: Code) : CompileM Code := do
  let cur ← CompileM.get CompileState.state
  let state := genParseIdent "state" cur
  return code.push (← `(cStmt| if (p == endp) return $state;))

def errInst : Instruction false := .error 0

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
      let code ← genCheck code
      let comparison ← `(cExpr| *$pointerName == $(mkCharLit chr))
      ifStmt code comparison ok otherwise
    | .range range ok otherwise => do
      let code ← genCheck code
      let comparison ← compileRange (← `(cExpr| *$pointerName)) range
      ifStmt code comparison ok otherwise
    | .map int ok otherwise => do
      let code ← genCheck code
      let comparison ← compileInterval int
      ifStmt code comparison ok otherwise
    | .chars alts otherwise => do
      let code ← genCheck code
      let otherwise ← compileInstruction #[] otherwise
      let alts ← alts.mapM $ λ(case, to) => do
        let next ← compileInstruction #[] to
        `(cStmt| case $(mkCharLit case):constExpr : { $next* })
      let alts := alts.push (← `(cStmt| default : { $otherwise* }))
      return code.push (← `(cStmt| switch (*p) { $alts* }))
    | .mixed alts otherwise => do
      let code ← genCheck code
      let otherwise ← compileInstruction #[] otherwise
      let alts ← alts.mapM $ λ(check, to) => do
        let next ← compileInstruction #[] to
        let map ← compileCheck check
        `(cStmt| if ($map) { $next* })
      let alts := alts.append otherwise
      return code.append alts

  partial def compileCode (code: Code) : Call → CompileM Code
    | .store method n => do
      let names ← CompileM.get CompileState.names
      let name := mkIdent s!"prop_{names[method]!}"
      return  code.push (← `(cStmt| data->$name = $(mkNumLit n);))
    | .arbitrary n => do
      let names ← CompileM.get CompileState.calls
      let name := mkIdent s!"on_{names[n]!}"
      let code := code.push (← `(cStmt| lean_apply_1(data->callbacks.$name, data->data)))
      let code := code.push (← `(cStmtLike| lean_object* info = lean_ctor_get(obj, 0);))
      let code := code.push (← `(cStmtLike| lean_object* code = lean_ctor_get(obj, 1);))
      return code.push (← `(cStmtLike| data->data = info;))
    | .loadNum n => do
      let names ← CompileM.get CompileState.names
      let name := mkIdent s!"prop_{names[n]!}"
      return  code.push (← `(cStmt| data->$name = *p - '0';))
    | .mulAdd n => do
      let names ← CompileM.get CompileState.names
      let name := mkIdent s!"prop_{names[n]!}"
      let code := code.push (← `(cStmt| data->$name *= 10;))
      return code.push (← `(cStmt| data->$name += *p - '0';))
    | .callStore prop call => do
      let names ← CompileM.get CompileState.calls
      let name := mkIdent s!"on_{names[call]!}"
      let code := code.push (← `(cStmtLike| lean_object* obj = lean_apply_1(data->callbacks.$name, data->data);))
      let code := code.push (← `(cStmtLike| lean_object* info = lean_ctor_get(obj, 0);))
      let code := code.push (← `(cStmtLike| lean_object* code = lean_ctor_get(obj, 1);))
      let code := code.push (← `(cStmtLike| data->data = info;))
      let names ← CompileM.get CompileState.names
      let name := mkIdent s!"prop_{names[prop]!}"
      return code.push (← `(cStmt| data->$name = lean_unbox(code);))

  partial def compileInstruction (code: Code) : Instruction β → CompileM Code
    | .next num next => do
      let code := code.push (← `(cStmt| p += $(mkNumLit num);))
      compileInstruction code next
    | .select call alts otherwise => do
      let code ←
        match call with
        | .call call => compileCode code call
        | .method name => do
          let names ← CompileM.get CompileState.names
          let name := mkIdent s!"prop_{names[name]!}"
          pure (code.push (← `(cStmtLike| uint8_t code = data->$name;)))
      let otherwise ← compileInstruction #[] otherwise
      let alts ← alts.mapM $ λ(case, to) => do
        let next ← compileInstruction #[] to
        `(cStmt| case $(mkNumLit case):constExpr : { $next* })
      let alts := alts.push (← `(cStmt| default : { $otherwise* }))
      return code.push (← `(cStmt| switch (code) { $alts* }))
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
      let prop := mkIdent s!"prop_{names.get! prop}_start_pos"
      let code := code.push (← `(cStmt| data->$(prop) = $pointerName;))
      compileInstruction code next
    | .consume prop next => do
      let names ← CompileM.get CompileState.names
      let prop := mkIdent s!"prop_{names.get! prop}"
      let code := code.push (← `(cStmt| p += data->$prop;))
      compileInstruction code next
    | .close prop next => do
      let names ← CompileM.get CompileState.names
      let name := mkIdent s!"on_{names[prop]!}"
      let start ← `(cExpr| lean_unsigned_to_nat(start));
      let close ← `(cExpr| lean_unsigned_to_nat((uint64_t)p - (uint64_t)data->string));
      let code := code.push (← `(cStmtLike| int start = (uint64_t)data->$(mkIdent s!"prop_{names[prop]!}_start_pos")-(uint64_t)data->string;))
      let code := code.push (← `(cStmtLike| data->$(mkIdent s!"prop_{names[prop]!}_start_pos") = NULL;))
      let code := code.push (← `(cStmtLike| lean_object* obj = lean_apply_3(data->callbacks.$name, $start, $close, data->data)))
      let code := code.push (← `(cStmtLike| lean_object* info = lean_ctor_get(obj, 0);))
      let code := code.push (← `(cStmtLike| lean_object* code = lean_ctor_get(obj, 1);))
      let code := code.push (← `(cStmtLike| data->data = info;))
      compileInstruction code next
    | .goto to => do
      let state := genParseIdent "state" to
      return code.push (← `(cStmt| goto $state:ident;))
    | .call call next => do
      let code ← compileCode code call
      compileInstruction code next
    | .error errCode => do
      let code := code.push (← `(cStmt| data->error = $(mkNumLit errCode)))
      return code.push (← `(cStmt| return -$(mkNumLit errCode);))
    | .consumer consumer =>
      compileConsumer code consumer
end

def compileTyp : Typ → Ident
  | .u8 => mkIdent "uint8_t"
  | .char => mkIdent "uint8_t"
  | .u16 => mkIdent "uint16_t"
  | .u32 => mkIdent "uint32_t"
  | .u64 => mkIdent "uint64_t"
  | .span => mkIdent "span_t"

def compilePropName (name: String) : Typ → Ident
  | .span => mkIdent s!"prop_{name}_start_pos"
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

def callbacksStruct (storage: Storage) : CommandElabM (TSyntax `cCmd) := do
  let fields ← storage.callback.mapM $ λ(name, _) =>
    let name := mkIdent $ Name.mkStr1 s!"on_{name}"
    `(Alloy.C.aggrDeclaration| lean_object *$name:ident )

  `(cCmd|
    typedef struct callbacks {
      $fields*
    } callbacks_t;
  )

def getter (field: String) : CommandElabM (TSyntax `command) := do
  let prop := mkIdent (Name.mkStr2 "Data" field)
  let propName := mkIdent s!"prop_{field}"
  `(command |
    alloy c extern
      def $prop {α: Type} (data_obj: $(mkIdent "Data") α) : UInt64 := {
        data_t* data = lean_get_external_data(data_obj);
        return data->$propName;
      }
  )

def dataStruct (storage: Storage) : CommandElabM (TSyntax `cCmd) := do
  let fields ← storage.props.mapM $ λ(name, typ) => do
    let typName := compileTyp typ
    let ident := compilePropName name typ
    `(Alloy.C.aggrDeclaration| $typName $ident; )

  `(cCmd|
    typedef struct data_t {
      lean_object* data;

      const char* string;
      callbacks_t callbacks;

      uint64_t str_ptr;
      uint64_t error;
      uint64_t state;
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
  CompileM.modify (λstate => {state with names := machine.storage.props.map Prod.fst
                                        ,calls := machine.storage.callback.map Prod.fst})

  let mut branches := #[]


  for (idx, inst) in machine.nodes.mapIdx ((·, ·)) do
    CompileM.modify (λmachine => {machine with state := idx })
    let name := genParseIdent "state" idx
    let alts ← compileInstruction #[] inst.instruction
    branches := branches.push (← `(cStmtLike| case $name:ident: $name:ident: {$alts*}))

  return branches


def spanProps (storage: Storage) : Array String :=
  storage.props.filterMap $ λ(name, typ) =>
    match typ with
    | .span => name
    | _ => none

def resetSpan (name: String) : CommandElabM (TSyntax `cStmtLike) := do
  let prop := mkIdent s!"prop_{name}_start_pos"
  `(cStmtLike|
    if (data->$prop != NULL) {
      data->$prop = str;
    }
  )

def callSpan (str: String) : CommandElabM (TSyntax `cStmtLike) := do
  let name := mkIdent s!"on_{str}"
  let prop := mkIdent s!"prop_{str}_start_pos"
  let start ← `(cExpr| lean_unsigned_to_nat((uint64_t)data->$(mkIdent s!"prop_{str}_start_pos")-(uint64_t)str));
  let close ← `(cExpr| lean_unsigned_to_nat(size));
  let code := (← `(cStmtLike| lean_object* obj = lean_apply_3(data->callbacks.$name, $start, $close, data->data)))
  `(cStmtLike|
    if (data->$prop != NULL) {
      $code
      lean_object* info = lean_ctor_get(obj, 0);
      lean_object* code = lean_ctor_get(obj, 1);
      data->data = info;
    }
  )

def compile (name: Ident) (machine: Machine) : CommandElabM Unit := do

  let params ← machine.storage.callback.mapM (λ(x, isSpan) => do
    let typ ← if isSpan then `(Nat → Nat → α → (α × Int)) else `(α → (α × Int))
    `(Lean.Parser.Term.bracketedBinderF | ($(mkIdent s!"on_{x}") : $typ)))
  let assign ← machine.storage.callback.mapM (λ(x, _) => `(cStmtLike | data->callbacks.$(mkIdent s!"on_{x}"):ident = $(mkIdent s!"on_{x}");))

  let names := spanProps machine.storage
  let resetSpans ← names.mapM resetSpan
  let callSpans ← names.mapM callSpan

  let getters ← (machine.storage.props.filter (λ(_, typ) =>
                  match typ with
                  | .span => false
                  | _ => true)).mapM (getter ∘ Prod.fst)

  let data :=  mkIdent "Data"

  elabCommand =<< `(
    namespace $name
      alloy c include "lean/lean.h" "stdlib.h" "stdio.h"

      alloy c section
        #define FAIL 0
        #define PAUSED 1
        #define SUCCEEDED 2

        typedef const char* span_t;

        $(← enumStates machine)
        $(← callbacksStruct machine.storage)
        $(← dataStruct machine.storage)
        $(← matchStr)

        $(← alloyParse (mkIdent "alloy_parse") (← compileBranch machine))
      end

      alloy c opaque_extern_type $(mkIdent "Data") (α: Type) => data_t where
        foreach(s, f) := lean_apply_1(f, s->m_s)
        finalize(s) := lean_dec(s->m_s); free(s)

      alloy c extern
      def $(mkIdent "create") {α: Type} (info: α) $params* : $(mkIdent "Data") α := {
        data_t* data = (data_t*)calloc(1, sizeof(data_t));
        data->data = info;

        {$assign*}

        return to_lean<$data>(data);
      }

      alloy c extern
      def $(mkIdent "parse") {α: Type} (data_obj: @& $(mkIdent "Data") α) (s: String) (size: UInt32) : UInt32 := {
        const char* str = lean_string_cstr(s);
        const char* strend = str + size;

        data_t* data = lean_get_external_data(data_obj);
        data->string = str;

        { $resetSpans* }

        int res = alloy_parse(data->state, data, str, strend);
        data->state = res;

        { $callSpans* }

        return res;
      }

      alloy c extern
      def $(mkIdent $ Name.mkStr2 "Data" "reset") {α: Type} (data_obj: @& $(mkIdent "Data") α) : $(mkIdent "Data") α := {
        data_t* data = lean_get_external_data(data_obj);
        data->state = 0;
        return data_obj;
      }

      alloy c extern
      def $(mkIdent $ Name.mkStr2 "Data" "error") {α: Type} (data_obj: @& $(mkIdent "Data") α) : UInt64 := {
        data_t* data = lean_get_external_data(data_obj);
        return data->error;
      }
  )

  for getter in getters do
    elabCommand getter
