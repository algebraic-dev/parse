import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Init.Meta

import Alloy.C
import Alloy.C.Grammar

import Parse.Lowering

/-!
  Helpers to compile the Grammar to C
-/

namespace Parse.Compile.C

open scoped Alloy.C
open Lean.Elab Command Term Lean Parser Command Std
open Parse.Syntax Parse.Lowering

def pointerName := mkIdent "p"

def endPointerName := mkIdent "endp"

def mkNumLit [ToString α] (x: α) : TSyntax `num :=
  TSyntax.mk (Syntax.mkNumLit (ToString.toString x))

def mkCharLit (char: Char) : TSyntax `char :=
  TSyntax.mk $ Syntax.mkLit charLitKind (Char.quote char)

def mkStrLit (str: String) : TSyntax `string :=
  TSyntax.mk $ Syntax.mkStrLit str

def withComma (alts: Array (TSyntax α)) : Syntax.TSepArray α "," :=
  alts.foldl Syntax.TSepArray.push (Syntax.TSepArray.mk #[] (sep := ","))

def genParseIdent (name: String) (num: Nat) : Ident :=
  mkIdent (Name.mkStr1 s!"parse_{name}_{num}")

def compileRange (name: TSyntax `cExpr) (range: Lowering.Range) : CommandElabM (TSyntax `cExpr) := do
  let fstChar : TSyntax `char := mkCharLit $ Char.ofNat (range.val.fst.toNat)
  if range.val.fst != range.val.snd then
    let sndChar : TSyntax `char := mkCharLit $ Char.ofNat (range.val.snd.toNat)
    if range.val.fst == range.val.snd - 1
      then `(cExpr | ($name == $fstChar || $name == $sndChar))
      else `(cExpr | ($name >= $fstChar && $name <= $sndChar))
  else `(cExpr | ($name == $fstChar))

def compileBitMap (name: Ident) (int: Lowering.Interval) : CommandElabM (TSyntax `Alloy.C.declaration) := do
  let mut alts := #[]

  for i in [0:255] do
    let int := mkNumLit (if int.in i.toUInt8 then 1 else 0)
    let lit ← `(Alloy.C.initializerElem | $int)
    alts := alts.push lit

  let f := withComma alts

  `(Alloy.C.declaration | uint8_t $name:ident[] = {$f,*,})
