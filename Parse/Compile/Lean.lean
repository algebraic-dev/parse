import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Init.Meta

import Parse.Lowering
import Parse.Compile.C.Helpers

/-!
  Compiles a [Parse.Syntax.Grammar] into Lean
-/

namespace Parse.Compile.LeanC

open Lean.Elab Command Term Lean Parser Command Std
open Parse.Syntax Parse.Lowering

structure CompileState where
  state : Nat
  names : Array String
  props : Array String
  calls : Array String
  maps: HashMap Interval Nat
  deriving Inhabited
