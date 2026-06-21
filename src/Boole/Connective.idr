module Boole.Connective

import Boole.Bit

%default total

-----------------------------------------------------------------------
-- 16 BINARY CONNECTIVES OVER B₂
--
-- Source: Wildberger Lecture 258.
-----------------------------------------------------------------------

public export
data Connective : Type where
  Contradiction : Connective
  And           : Connective
  InhibitP      : Connective
  ProjectP      : Connective
  InhibitQ      : Connective
  ProjectQ      : Connective
  Xor           : Connective
  Or            : Connective
  Nor           : Connective
  Xnor          : Connective
  NotQ          : Connective
  ImpPQ         : Connective
  NotP          : Connective
  ImpQP         : Connective
  Nand          : Connective
  Tautology     : Connective

public export
Show Connective where
  show Contradiction = "⊥"
  show And           = "AND"
  show InhibitP      = "P∧¬Q"
  show ProjectP      = "P"
  show InhibitQ      = "Q∧¬P"
  show ProjectQ      = "Q"
  show Xor           = "XOR"
  show Or            = "OR"
  show Nor           = "NOR"
  show Xnor          = "XNOR"
  show NotQ          = "¬Q"
  show ImpPQ         = "P→Q"
  show NotP          = "¬P"
  show ImpQP         = "Q→P"
  show Nand          = "NAND"
  show Tautology     = "⊤"

-----------------------------------------------------------------------
-- EVALUATION
-----------------------------------------------------------------------

||| Evaluate a connective on two BVal inputs.
||| All expressions use Boole arithmetic (+ is XOR, * is AND).
public export
evalConnective : Connective -> BVal -> BVal -> BVal
evalConnective Contradiction _ _ = Zero
evalConnective And           p q = p * q
evalConnective InhibitP      p q = p + p * q
evalConnective ProjectP      p _ = p
evalConnective InhibitQ      p q = q + p * q
evalConnective ProjectQ      _ q = q
evalConnective Xor           p q = p + q
evalConnective Or            p q = p + q + p * q
evalConnective Nor           p q = One + p + q + p * q
evalConnective Xnor          p q = One + p + q
evalConnective NotQ          _ q = One + q
evalConnective ImpPQ         p q = One + p + p * q
evalConnective NotP          p _ = One + p
evalConnective ImpQP         p q = One + q + p * q
evalConnective Nand          p q = One + p * q
evalConnective Tautology     _ _ = One

-----------------------------------------------------------------------
-- BOOLE ALGEBRA EXPRESSIONS (display)
-----------------------------------------------------------------------

public export
booleExpr : Connective -> String
booleExpr Contradiction = "0"
booleExpr And           = "PQ"
booleExpr InhibitP      = "P + PQ"
booleExpr ProjectP      = "P"
booleExpr InhibitQ      = "Q + PQ"
booleExpr ProjectQ      = "Q"
booleExpr Xor           = "P + Q"
booleExpr Or            = "P + Q + PQ"
booleExpr Nor           = "1 + P + Q + PQ"
booleExpr Xnor          = "1 + P + Q"
booleExpr NotQ          = "1 + Q"
booleExpr ImpPQ         = "1 + P + PQ"
booleExpr NotP          = "1 + P"
booleExpr ImpQP         = "1 + Q + PQ"
booleExpr Nand          = "1 + PQ"
booleExpr Tautology     = "1"

-----------------------------------------------------------------------
-- COMPLEMENT
-----------------------------------------------------------------------

public export
negConnective : Connective -> Connective
negConnective Contradiction = Tautology
negConnective And           = Nand
negConnective InhibitP      = ImpQP
negConnective ProjectP      = NotP
negConnective InhibitQ      = ImpPQ
negConnective ProjectQ      = NotQ
negConnective Xor           = Xnor
negConnective Or            = Nor
negConnective Nor           = Or
negConnective Xnor          = Xor
negConnective NotQ          = ProjectQ
negConnective ImpPQ         = InhibitQ
negConnective NotP          = ProjectP
negConnective ImpQP         = InhibitP
negConnective Nand          = And
negConnective Tautology     = Contradiction
