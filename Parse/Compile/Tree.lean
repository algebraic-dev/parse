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

-- Pretty printing

def Array.joinMap (f: α → String) := Array.foldl String.append "" ∘ Array.map f

inductive RoseTree where
  | node (label : String) (children : Array RoseTree)
  deriving Inhabited

partial def Instruction.toTree (arr : Array RoseTree) (x: Instruction) : Array RoseTree :=
  match x with
  | .check str then_ else_ =>
    let alts := #[RoseTree.node "then: " (toTree #[] then_), RoseTree.node "else: " (toTree #[] else_)]
    arr.push (RoseTree.node s!".check {reprStr str}: " alts)
  | .when alts else_ =>
    let alts := alts.map (λ(prefix_, inst) => RoseTree.node s!"{reprStr prefix_}: " (toTree #[] inst))
    let alts := alts.push (RoseTree.node s!"_ =>" (toTree #[] else_))
    arr.push (RoseTree.node s!".when: " alts)
  | .call n nex => arr.push (RoseTree.node s!".call {n} {nex}" #[])
  | .goto n => arr.push (RoseTree.node s!".goto {n}" #[])
  | .error n => arr.push (RoseTree.node s!".error {n}" #[])
  | failed => arr.push (RoseTree.node s!".done" #[])
  | .next n nex => Instruction.toTree (arr.push (RoseTree.node s!".next {n}" #[])) nex
  | .start n nex => Instruction.toTree (arr.push (RoseTree.node s!".start {n}" #[])) nex
  | .close n nex => Instruction.toTree (arr.push (RoseTree.node s!".close {n}" #[])) nex
  | .store n j nex => Instruction.toTree (arr.push (RoseTree.node s!".store {n} {j}" #[])) nex

partial def RoseTree.toString (ident: String) : RoseTree → String
  | .node label child =>
    s!"{ident}{label}\n" ++ Array.joinMap (RoseTree.toString s!"  {ident}") child

def Instruction.toStr (name: String) (instruction: Instruction) : RoseTree :=
  RoseTree.node s!"{name}: " (Instruction.toTree #[] instruction)

def Machine.toStr (machine: Machine) : String :=
  let rose := RoseTree.node "machine: " (machine.nodes.mapIdx (λname inst => Instruction.toStr s!"({name}) {machine.names.get! name}" inst))
  rose.toString ""
