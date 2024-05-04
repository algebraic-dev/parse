import Parse.Lowering.Specialize
import Parse.Lowering.Translate

/-!
  Lowers parts the Syntax into a Instruction Set
-/

namespace Parse.Lowering

export Parse.Lowering.Translate (translate Instruction Machine Check Consumer)
export Parse.Lowering.Interval (Interval Range)
