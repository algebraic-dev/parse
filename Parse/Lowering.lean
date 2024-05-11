import Parse.Lowering.Specialize
import Parse.Lowering.Translate

namespace Parse.Lowering

/-!
  Lowers parts the Syntax into a Instruction Set
-/

export Parse.Lowering.Translate (translate Instruction Machine Check Consumer)
export Parse.Lowering.Interval (Interval Range)
