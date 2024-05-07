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

def identNum (name: String) (nat: Nat) : Ident :=
  mkIdent (Name.mkStr1 s!"{name}_{nat}")

def mangledName (name: String) : CommandElabM Ident := do
  let cur ← getCurrNamespace
  let name := Name.str cur name
  pure $ mkIdent $ Name.mkStr1 s!"{name.mangle}"

abbrev CompileM := StateT CompileState CommandElabM

def CompileM.get (f: CompileState -> α) : CompileM α :=
  f <$> StateT.get

def CompileM.modify (f: CompileState -> CompileState) : CompileM Unit :=
  StateT.modifyGet (((), ·) ∘ f)

def CompileM.getInterval (int: Interval) : CompileM Ident := do
  let maps ← CompileM.get CompileState.maps
  let gen x := mangledName (genParseIdent "bitmap" x).getId.toString
  if let some res := maps.find? int then
    gen res
  else do
    let size := maps.size
    CompileM.modify (λstate => { state with maps := state.maps.insert int state.maps.size })
    gen size

def CompileM.run (c: CompileM α) : CommandElabM α :=
  Prod.fst <$> StateT.run c Inhabited.default

-- Compile

def newIdent : String → Ident := mkIdent ∘ Name.mkStr1

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
  partial def ifStmt (depth: Nat) (code: Code) (comparison: TSyntax `cExpr) (ok: Instruction false) (otherwise: Instruction false) : CompileM Code := do
    let ok ← compileInstruction #[] (depth + 1) ok
    let otherwise ← compileInstruction #[] (depth + 1) otherwise
    let code := code.push (← `(cStmtLike | if ($comparison) { $ok* }))
    return code.append otherwise

  partial def compileConsumer (code: Code) (depth: Nat) : Consumer (Instruction false) → CompileM Code
    | .is str ok otherwise => do
      let match_string ← mangledName "match_string"
      let cur ← CompileM.get CompileState.state
      let n := mkNumLit (str.toSubstring.bsize)
      let str := TSyntax.mk $ Syntax.mkStrLit str
      let code := code.push (← `(cStmtLike| int result = $match_string:ident(data, $str, $n, $pointerName, $endPointerName);))
      let state := genParseIdent "state" cur
      let then_ ← compileInstruction #[] (depth + 1) ok
      let otherwise ← compileInstruction #[] (depth + 1) otherwise
      return code.push (← `(cStmt| switch (result) {
        case PAUSED: return $state;
        case FAIL: { $otherwise* }
        case SUCCEEDED: { $then_* }
        }))
    | .char chr ok otherwise => do
      let code ← genCheck code
      let comparison ← `(cExpr| *$pointerName == $(mkCharLit chr))
      ifStmt depth code comparison ok otherwise
    | .range range ok otherwise => do
      let code ← genCheck code
      let comparison ← compileRange (← `(cExpr| *$pointerName)) range
      ifStmt depth code comparison ok otherwise
    | .map int ok otherwise => do
      let code ← genCheck code
      let comparison ← compileInterval int
      ifStmt depth code comparison ok otherwise
    | .chars alts otherwise => do
      let code ← genCheck code
      let otherwise ← compileInstruction #[] (depth + 1) otherwise
      let alts ← alts.mapM $ λ(case, to) => do
        let next ← compileInstruction #[] (depth + 1) to
        `(cStmt| case $(mkCharLit case):constExpr : { $next* })
      let alts := alts.push (← `(cStmt| default : { $otherwise* }))
      return code.push (← `(cStmt| switch (*p) { $alts* }))
    | .mixed alts otherwise => do
      let code ← genCheck code
      let otherwise ← compileInstruction #[] (depth + 1) otherwise
      let alts ← alts.mapM $ λ(check, to) => do
        let next ← compileInstruction #[] (depth + 1) to
        let map ← compileCheck check
        `(cStmt| if ($map) { $next* })
      let alts := alts.append otherwise
      return code.append alts

  partial def compileCode (code: Code) (depth: Nat) : Call → CompileM Code
    | .store method n => do
      let names ← CompileM.get CompileState.names
      let name := newIdent s!"prop_{names[method]!}"
      return  code.push (← `(cStmt| data->$name = $(mkNumLit n);))
    | .arbitrary n => do
      let names ← CompileM.get CompileState.calls
      let name := newIdent s!"on_{names[n]!}"
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "obj" depth):ident = lean_apply_1(data->callbacks.$name, data->data)))
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "info" depth):ident = lean_ctor_get($(identNum "obj" depth), 0);))
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "code" depth):ident = lean_ctor_get($(identNum "obj" depth), 1);))
      return code.push (← `(cStmtLike| data->data = $(identNum "info" depth):ident;))
    | .loadNum n => do
      let names ← CompileM.get CompileState.names
      let name := newIdent s!"prop_{names[n]!}"
      return  code.push (← `(cStmt| data->$name = *p - '0';))
    | .mulAdd n => do
      let names ← CompileM.get CompileState.names
      let name := newIdent s!"prop_{names[n]!}"
      let code := code.push (← `(cStmt| data->$name *= 10;))
      return code.push (← `(cStmt| data->$name += *p - '0';))
    | .callStore prop call => do
      let names ← CompileM.get CompileState.calls
      let name := newIdent s!"on_{names[call]!}"
      let code := code.push (← `(cStmtLike| lean_inc(data->str);))
      let code := code.push (← `(cStmtLike| lean_inc(data->data);))
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "obj" depth):ident  = lean_apply_1(data->callbacks.$name, data->data);))
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "info" depth):ident  = lean_ctor_get($(identNum "obj" depth):ident , 0);))
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "code" depth):ident  = lean_ctor_get($(identNum "obj" depth):ident , 1);))
      let code := code.push (← `(cStmtLike| data->data = $(identNum "info" depth):ident;))
      let names ← CompileM.get CompileState.names
      let name := newIdent s!"prop_{names[prop]!}"
      return code.push (← `(cStmt| data->$name = lean_unbox($(identNum "code" depth):ident);))

  partial def compileInstruction (code: Code) (depth: Nat) : Instruction β → CompileM Code
    | .next num next => do
      let code := code.push (← `(cStmt| p += $(mkNumLit num);))
      compileInstruction code (depth + 1) next
    | .select call alts otherwise => do
      let code ←
        match call with
        | .call call => compileCode code (depth + 1) call
        | .method name => do
          let names ← CompileM.get CompileState.names
          let name := newIdent s!"prop_{names[name]!}"
          pure (code.push (← `(cStmtLike| uint8_t code = data->$name;)))
      let otherwise ← compileInstruction #[] (depth + 1) otherwise
      let alts ← alts.mapM $ λ(case, to) => do
        let next ← compileInstruction #[] (depth + 1) to
        `(cStmt| case $(mkNumLit case):constExpr : { $next* })
      let alts := alts.push (← `(cStmt| default : { $otherwise* }))
      return code.push (← `(cStmt| switch (code) { $alts* }))
    | .store prop data next => do
      let names ← CompileM.get CompileState.names
      let prop := newIdent s!"prop_{names.get! prop}"
      let data ←
        match data with
        | some data => `(cExpr| $(mkNumLit data))
        | none => `(cExpr| *p)
      let code := code.push (← `(cStmt| data->$prop = $data;))
      compileInstruction code (depth + 1) next
    | .capture prop next => do
      let names ← CompileM.get CompileState.names
      let prop := newIdent s!"prop_{names.get! prop}_start_pos"
      let code := code.push (← `(cStmt| data->$(prop) = $pointerName;))
      compileInstruction code (depth + 1) next
    | .consume prop next => do
      let names ← CompileM.get CompileState.names
      let prop := newIdent s!"prop_{names.get! prop}"
      let code := code.push (← `(cStmt| p += data->$prop;))
      compileInstruction code (depth + 1) next
    | .close prop next => do
      let names ← CompileM.get CompileState.names
      let name := newIdent s!"on_{names[prop]!}"
      let start ← `(cExpr| lean_unsigned_to_nat(start));
      let close ← `(cExpr| lean_unsigned_to_nat((uint64_t)p - (uint64_t)data->string));
      let code := code.push (← `(cStmtLike| int start = (uint64_t)data->$(newIdent s!"prop_{names[prop]!}_start_pos")-(uint64_t)data->string;))
      let code := code.push (← `(cStmtLike| data->$(newIdent s!"prop_{names[prop]!}_start_pos") = NULL;))
      let code := code.push (← `(cStmtLike| lean_inc(data->str);))
      let code := code.push (← `(cStmtLike| lean_inc(data->data);))
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "obj" depth):ident = lean_apply_4(data->callbacks.$name, $start, $close, data->str, data->data)))
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "info" depth):ident = lean_ctor_get($(identNum "obj" depth):ident, 0);))
      let code := code.push (← `(cStmtLike| lean_object* $(identNum "code" depth):ident = lean_ctor_get($(identNum "obj" depth):ident, 1);))
      let code := code.push (← `(cStmtLike| data->data = $(identNum "info" depth):ident;))
      compileInstruction code (depth + 1) next
    | .goto to => do
      let state := genParseIdent "state" to
      let expr ← `(cExpr| $(mkStrLit state.getId.toString))
      let code :=  code.push (← `(cStmt| printf("%s '%c'\n", $expr, *p)))
      return code.push (← `(cStmt| goto $state:ident;))
    | .call call next => do
      let code ← compileCode code (depth + 1) call
      compileInstruction code (depth + 1) next
    | .error errCode => do
      let code := code.push (← `(cStmt| data->error = $(mkNumLit errCode)))
      return code.push (← `(cStmt| return -$(mkNumLit errCode);))
    | .consumer consumer =>
      compileConsumer code depth consumer
end

def compileTyp : Typ → Ident
  | .u8 => newIdent "uint8_t"
  | .char => newIdent "uint8_t"
  | .u16 => newIdent "uint16_t"
  | .u32 => newIdent "uint32_t"
  | .u64 => newIdent "uint64_t"
  | .span => newIdent "span_t"

def compilePropName (name: String) : Typ → Ident
  | .span => newIdent s!"prop_{name}_start_pos"
  | _ => newIdent s!"prop_{name}"

-- Commands

def enumStates (machine: Machine) : CommandElabM (TSyntax `cCmd) := do
  let states ← machine.nodes.mapIdxM (λi _ => `(Alloy.C.enumerator| $(genParseIdent "state" i)))
  let states := withComma states
  `(cCmd|
    enum $(← mangledName "states") {
      $states,*
    };
  )

def callbacksStruct (storage: Storage) : CommandElabM (TSyntax `cCmd) := do
  let fields ← storage.callback.mapM $ λ(name, _) =>
    let name := mkIdent $ Name.mkStr1 s!"on_{name}"
    `(Alloy.C.aggrDeclaration| lean_object *$name:ident )

  let callbacks_t ← mangledName "callbacks_t"

  `(cCmd|
    typedef struct $callbacks_t {
      $fields*
    } $callbacks_t;
  )

def getter (field: String) : CommandElabM (TSyntax `command) := do
  let prop := mkIdent (Name.mkStr2 "Data" field)
  let propName := newIdent s!"prop_{field}"
  let data_t ← mangledName "data_t"
  `(command |
    alloy c extern
      def $prop {α: Type} (data_obj: $(newIdent "Data") α) : UInt64 := {
        $data_t:ident* data = lean_get_external_data(data_obj);
        return data->$propName;
      }
  )

def dataStruct (storage: Storage) : CommandElabM (TSyntax `cCmd) := do
  let fields ← storage.props.mapM $ λ(name, typ) => do
    let typName := compileTyp typ
    let ident := compilePropName name typ
    `(Alloy.C.aggrDeclaration| $typName $ident; )

  let data_t ← mangledName "data_t"
  let callbacks_t ← mangledName "callbacks_t"

  `(cCmd|
    typedef struct $data_t:ident {
      lean_object* data;
      lean_object* str;

      const char* string;
      $callbacks_t callbacks;

      uint64_t str_ptr;
      uint64_t error;
      uint64_t state;
      uint8_t pointer;

      $fields*
    } $data_t:ident;
  )

def matchStr : CommandElabM (TSyntax `cCmd) := do
  let data_t ← mangledName "data_t"
  let match_string ← mangledName "match_string"
  `(cCmd|
    uint32_t $match_string:ident($data_t:ident *data, char* s, int len, const char* p, const char* endp) {
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
  let data_t ← mangledName "data_t"
  `(cCmd|
    uint32_t $name:ident (uint32_t state, $data_t:ident * data, const char* p, const char* endp) {
      switch (state) {
        $branches*
        default:
          return -1;
      }
    }
  )

def compileBranch (machine: Machine) : CommandElabM (Array (TSyntax `cStmtLike) × HashMap Interval Nat) := CompileM.run do
  CompileM.modify (λstate => {state with names := machine.storage.props.map Prod.fst
                                        ,calls := machine.storage.callback.map Prod.fst})

  let mut branches := #[]


  for (idx, inst) in machine.nodes.mapIdx ((·, ·)) do
    CompileM.modify (λmachine => {machine with state := idx })
    let name := genParseIdent "state" idx
    let alts ← compileInstruction #[] 0 inst.instruction
    branches := branches.push (← `(cStmtLike| case $name:ident: $name:ident: {printf("state '%c'\n", *p); {$alts*}}))

  let maps ← CompileState.maps <$> StateT.get

  return (branches, maps)


def spanProps (storage: Storage) : Array String :=
  storage.props.filterMap $ λ(name, typ) =>
    match typ with
    | .span => name
    | _ => none

def resetSpan (name: String) : CommandElabM (TSyntax `cStmtLike) := do
  let prop := newIdent s!"prop_{name}_start_pos"
  `(cStmtLike|
    if (data->$prop != NULL) {
      data->$prop = str;
    }
  )

def callSpan (str: String) : CommandElabM (TSyntax `cStmtLike) := do
  let name := newIdent s!"on_{str}"
  let prop := newIdent s!"prop_{str}_start_pos"
  let start ← `(cExpr| lean_unsigned_to_nat((uint64_t)data->$(newIdent s!"prop_{str}_start_pos")-(uint64_t)str));
  let close ← `(cExpr| lean_unsigned_to_nat(size));
  `(cStmtLike|
    if (data->$prop != NULL) {
      lean_inc(data->str);
      lean_inc(data->data);
      lean_object* obj = lean_apply_4(data->callbacks.$name, $start, $close, data->str, data->data);
      lean_object* info = lean_ctor_get(obj, 0);
      lean_object* code = lean_ctor_get(obj, 1);
      data->data = info;
    }
  )

def genBitMap (name: Ident) (int: Interval) : CommandElabM (TSyntax `Alloy.C.declaration) := do
  let mut alts := #[]

  for i in [0:255] do
    let int := mkNumLit (if int.in i.toUInt8 then 1 else 0)
    let lit ← `(Alloy.C.initializerElem | $int)
    alts := alts.push lit

  let f := withComma alts

  `(Alloy.C.declaration | int $name:ident[255] = {$f,*,})

def bitMaps (maps: HashMap Interval Nat) : CommandElabM (Array (TSyntax  `Alloy.C.declaration)) := do
  let mut result := #[]

  for (int, index) in maps.toArray do
    let bitmap ← mangledName (genParseIdent "bitmap" index).getId.toString
    result := result.push (← genBitMap bitmap int)

  return result

def compile (name: Ident) (machine: Machine) : CommandElabM Unit := do

  let params ← machine.storage.callback.mapM (λ(x, isSpan) => do
    let typ ← if isSpan then `(Nat → Nat → ByteArray → α → (α × Int)) else `(α → (α × Int))
    `(Lean.Parser.Term.bracketedBinderF | ($(newIdent s!"on_{x}") : $typ)))
  let assign ← machine.storage.callback.mapM (λ(x, _) => `(cStmtLike | data->callbacks.$(newIdent s!"on_{x}"):ident = $(newIdent s!"on_{x}");))

  let names := spanProps machine.storage
  let resetSpans ← names.mapM resetSpan
  let callSpans ← names.mapM callSpan

  let getters ← (machine.storage.props.filter (λ(_, typ) =>
                  match typ with
                  | .span => false
                  | _ => true)).mapM (getter ∘ Prod.fst)

  let data :=  newIdent "Data"

  let (branches, maps) ← compileBranch machine

  let data_t ← mangledName "data_t"
  let alloy_parse ← mangledName "alloy_parse"

  let fields := machine.storage.callback.map $ λ(name, _) => mkIdent $ Name.mkStr1 s!"on_{name}"
  let applies ← fields.mapM $ λname => `(cStmtLike| lean_apply_1(f, new_data->callbacks.$name))
  let finalizers ← fields.mapM $ λname => `(cStmtLike| lean_dec(s->callbacks.$name))
  let incs ← fields.mapM $ λname => `(cStmtLike| lean_inc(new_data->callbacks.$name))

  elabCommand =<< `(
    namespace $name
      alloy c include "lean/lean.h" "stdlib.h" "stdio.h" "string.h"

      alloy c section
        #define FAIL 0
        #define PAUSED 1
        #define SUCCEEDED 2

        typedef const char* span_t;

        $(← bitMaps maps)*
        $(← enumStates machine)
        $(← callbacksStruct machine.storage)
        $(← dataStruct machine.storage)
        $(← matchStr)

        $(← alloyParse alloy_parse branches)
      end

      alloy c opaque_extern_type $(newIdent "Data") (α: Type) => $data_t:ident where
        $(newIdent "foreach")(new_data, f) := {
          lean_inc(new_data->str);
          lean_inc(new_data->data);
          {$incs*}

          lean_apply_1(f, new_data->data);
          lean_apply_1(f, new_data->str);
          {$applies*}
        }
        $(newIdent "finalize")(s) := {
          lean_dec(s->data);
          lean_dec(s->str);
          {$finalizers*};
          free(s);
        }


      alloy c extern
      def $(newIdent "create") {α: Type} (info: α) $params* : $(newIdent "Data") α := {
        $data_t:ident* data = ($data_t:ident*)calloc(1, sizeof($data_t:ident));
        data->data = info;
        data->str = lean_mk_string_from_bytes("uwu", 3);

        {$assign*}

        lean_object* data_obj = to_lean<$data>(data);

        return data_obj;
      }

      alloy c extern
      def $(newIdent "parse") {α: Type} (data_obj: $(newIdent "Data") α) (s: ByteArray) (size: UInt32) : $(newIdent "Data") α := {
        if (!lean_is_exclusive(data_obj)) {
          $data_t:ident* new_data = ($data_t:ident*)calloc(1, sizeof($data_t:ident));
          memcpy(new_data, ($data_t:ident*)lean_get_external_data(data_obj), sizeof($data_t:ident));

          lean_inc(new_data->str);
          lean_inc(new_data->data);

          { $incs* }

          data_obj = to_lean<$data>(new_data);
        }

        $data_t:ident* data = lean_get_external_data(data_obj);

        const char* str = (char*) lean_sarray_cptr(s);
        const char* strend = str + lean_sarray_size(s);

        data->string = str;
        data->str = s;

        { $resetSpans* }

        printf ("Here: %.*s\n", lean_sarray_size(s), str);

        int res = $alloy_parse:ident(data->state, data, str, strend);
        data->state = res;

        if (data->error) {
          return data_obj;
        }

        { $callSpans* }

        return data_obj;
      }

      alloy c extern
      def $(mkIdent $ Name.mkStr2 "Data" "reset") {α: Type} (data_obj: @& $(newIdent "Data") α) : $(newIdent "Data") α := {
        $data_t:ident* data = lean_get_external_data(data_obj);
        data->state = 0;
        return data_obj;
      }

      alloy c extern
      def $(mkIdent $ Name.mkStr2 "Data" "error") {α: Type} (data_obj: @& $(newIdent "Data") α) : UInt64 := {
        $data_t:ident* data = lean_get_external_data(data_obj);
        return data->error;
      }

      alloy c extern
      def $(mkIdent $ Name.mkStr2 "Data" "state") {α: Type} (data_obj: @& $(newIdent "Data") α) : UInt64 := {
        $data_t:ident* data = lean_get_external_data(data_obj);
        return data->state;
      }

      alloy c extern
      def $(mkIdent $ Name.mkStr2 "Data" "data") {α: Type} [Inhabited α] (data_obj: @& $(newIdent "Data") α) : α := {
        $data_t:ident* data = lean_get_external_data(data_obj);
        lean_inc(data->data);
        return data->data;
      }
  )

  for getter in getters do
    elabCommand getter
