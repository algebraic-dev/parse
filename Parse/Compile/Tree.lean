import Lean.Data
import Parse.Compile.Syntax

/-!
  Definition of a machine that follows instructions, it's a middle representation
  for the compilation of the grammar.
-/

open Lean Parse.Syntax

namespace Parse.Tree

/--
  Imperative instructions for checking strings
-/
inductive Instruction
  | when (branches: Array (Char × Instruction)) (default: Instruction)
  | check (s: String) (inv: Instruction) (default: Instruction)
  | start (prop: Tag) (next: Instruction)
  | close (prop: Tag) (next: Instruction)
  | store (prop: Tag) (data: Lean.Syntax) (next: Instruction)
  | next (more: Nat) (next: Instruction)
  | call (func: Lean.Syntax) (to: Nat)
  | error (num: Lean.Syntax)
  | goto (to: Nat)
  | failed
  deriving Repr, Inhabited

def Instruction.isWhen : Instruction → Bool
  | .when _ _ => true
  | _ => false

def Instruction.isCheck : Instruction → Bool
  | .check _ _ _ => true
  | _ => false

structure Machine where
  tags : Names
  calls : HashSet Name
  props : HashMap Name Syntax
  mapper : HashMap Name Nat
  names : Array (Option Tag)
  nodes : Array Instruction
  deriving Inhabited

def Machine.new (tags: Names) : Machine :=
  let default : Machine := Inhabited.default
  { default with tags }

def Machine.createNamedNode (machine: Machine) (name: Tag) : (Machine × Nat) :=
  if let some res := machine.mapper.find? name.getId
    then (machine, res)
    else ({machine with mapper := machine.mapper.insert name.getId (machine.nodes.size)
                       , nodes := machine.nodes.push (Instruction.failed)
                       , names := machine.names.push (some name) }, machine.nodes.size)

def Machine.createNode (machine: Machine) : (Machine × Nat) :=
  ({machine with nodes := machine.nodes.push (Instruction.goto machine.nodes.size)
               , names := machine.names.push none }, machine.nodes.size)

def Machine.setCode (machine: Machine) (nat: Nat) (code: Instruction) : Machine :=
  { machine with nodes := machine.nodes.set! nat code }
