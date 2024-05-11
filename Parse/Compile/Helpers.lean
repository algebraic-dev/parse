import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Init.Meta

import Parse.Lowering

/-!
  Helpers for building the translator for instruction to actual code.
-/

namespace Parse.Compile

open Lean.Elab Command Term Lean Parser Command Std

def mkNumLit (x: Nat) : TSyntax `num :=
  TSyntax.mk (Syntax.mkNumLit (ToString.toString x))

def mkCharLit (char: Char) : TSyntax `char :=
  TSyntax.mk $ Syntax.mkLit charLitKind (Char.quote char)

def mkStrLit (str: String) : TSyntax `str :=
  TSyntax.mk $ Syntax.mkStrLit str

def withComma (alts: Array (TSyntax α)) : Syntax.TSepArray α "," :=
  alts.foldl Syntax.TSepArray.push (Syntax.TSepArray.mk #[] (sep := ","))

def newIdent : String → Ident := mkIdent ∘ Name.mkStr1

def genParseIdent (name: String) (num: Nat) : Ident :=
  mkIdent (Name.mkStr1 s!"parse_{name}_{num}")

def createOnIdent (name: String) : Ident :=
  let capitalized := name.capitalize
  newIdent s!"on{capitalized}"
