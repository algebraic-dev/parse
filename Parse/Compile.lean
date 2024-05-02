import Lean.Data

import Parse.Syntax
import Parse.Specialize
import Parse.Interval

/-!
  Module to compile specialized matching trees to instructions
-/

open Lean
open Parse.Syntax Parse.Specialize Parse.Interval

namespace Parse.Compile

inductive Check
  | char (c: Char)
  | map (arr: Interval)
  deriving Repr, Hashable, Inhabited

def Check.isChar : Check → Bool
  | .char _ => true
  | _ => false


def Check.getChar : Check → Option Char
  | .char chr => some chr
  | _ => none

inductive Instruction : Bool → Type
  | next (chars: Nat) (next: Instruction α) : Instruction α
  | store (prop: Nat) (data: Option Nat) (next: Instruction α) : Instruction α
  | capture (prop: Nat) (next: Instruction α) : Instruction α
  | close (prop: Nat) (next: Instruction α) : Instruction α
  | check (next: Instruction α) : Instruction α
  | is (s: String) (then_: Instruction false) (otherwise: Instruction false) : Instruction true
  | switch (cases: Array (Check × Instruction false)) (otherwise: Instruction false) : Instruction true
  | goto (to: Nat) : Instruction α
  | stop (code: Nat) (to: Nat) : Instruction α
  | error (code: Nat) : Instruction α
  deriving Repr, Hashable

structure Inst where
  isCheck : Bool
  instruction : Instruction isCheck
  deriving Repr

instance : Inhabited Inst where
  default := ⟨false, .error 0⟩

instance : Inhabited (Instruction α) where
  default := Instruction.error 0

structure Machine where
  storage: Storage
  names: Array (Option String)
  nodes: Array Inst
  mapper: HashMap String Nat
  deriving Inhabited

def Machine.addNode (machine: Machine) (name: Option String := none) : (Nat × Machine) :=
  let size := machine.names.size
  (size, { machine with names := machine.names.push name
                      , nodes := machine.nodes.push (Inst.mk false (.error 0))
                      , mapper := if let some name := name
                                    then machine.mapper.insert name size
                                    else machine.mapper })

def Machine.setNode (machine: Machine) (idx: Nat) (inst: Inst) : Machine :=
  { machine with nodes := machine.nodes.set! idx inst }

-- Compiler Monad

abbrev CompileM := StateM Machine

def CompileM.addNode (name: Option String := none) : CompileM Nat :=
  StateT.modifyGet (Machine.addNode · name)

def CompileM.setNode (idx: Nat) (code: Inst) : CompileM Unit :=
  StateT.modifyGet (λmachine => ((), machine.setNode idx code))

def CompileM.run (monad: CompileM α) : Machine :=
  StateT.run monad Inhabited.default
  |> Id.run
  |> Prod.snd

-- Compiling

def compileAction' (data: Option Nat) : Action → Instruction α
  | .store prop to => Instruction.store prop data (Instruction.goto to)
  | .capture prop to => Instruction.capture prop (Instruction.goto to)
  | .close prop to => Instruction.close prop (Instruction.goto to)
  | .stop prop to => Instruction.stop prop to
  | .goto to => Instruction.goto to
  | .error code => Instruction.error code

def compileAction (jump: Nat) (capture: Bool) (data: Option Nat) : Action → Instruction α
  | .capture prop to =>
    let jump := if capture then Nat.max 1 jump else jump
    if jump != 0
      then Instruction.capture prop (Instruction.next jump (Instruction.goto to))
      else Instruction.capture prop (Instruction.goto to)
  | action =>
    let jump := if capture then Nat.max 1 jump else jump
    let inst := compileAction' data action
    if jump != 0 then Instruction.next jump inst else inst

partial def compileTree (jump: Nat) (b: Bool) : Tree → CompileM (Instruction b)
  | .fail => return (Instruction.error 0)
  | .done data capture action => return (compileAction jump capture data action)
  | .branch branches default => do
    let otherwise := compileAction jump default.snd.fst (α := false) default.fst default.snd.snd
    let result ←
      match branches with
      | .str branch =>
        let jump := if branch.capture then branch.subject.length else 0
        let next ← compileTree jump false branch.next
        pure (Instruction.is branch.subject next otherwise)
      | .chars alts =>
        let alts ← alts.mapM $ λbranch => do
          let next ← compileTree (if branch.capture then 1 else 0) false branch.next
          pure (branch.subject, Hashable.hash next, next)

        let alts := alts.groupByKey (λx => x.snd.fst)
        let alts := alts.toArray.map (λ(_, val) =>
          let scrutinee := val.map (λx => x.fst)
          let action := (val.get! 0).snd.snd
          let check :=
            if scrutinee.size == 1
              then (Check.char (scrutinee.get! 0))
              else (Check.map (Interval.fromChars scrutinee))
          (check, action))

        pure (Instruction.check $ Instruction.switch alts otherwise)

    match b with
    | true  =>
      pure (if jump != 0 then Instruction.next jump result else result)
    | false => do
      let place ← CompileM.addNode
      CompileM.setNode place (Inst.mk true result)
      let result := Instruction.goto place
      pure (if jump != 0 then Instruction.next jump result else result)

def compile' (grammar: Grammar) : CompileM Unit := do
  StateT.modifyGet (((), ·) ∘ (λx => {x with storage := grammar.storage }))

  for node in grammar.nodes do
    let _ ← CompileM.addNode (name := some node.name)

  for (idx, node) in grammar.nodes.mapIdx ((·, ·)) do
    let tree := Problem.specialize (Problem.fromCases node.cases)
    let inst ← compileTree 0 true tree
    CompileM.setNode idx (Inst.mk true inst)

def compile (grammar: Grammar) : Machine :=
  CompileM.run (compile' grammar)
