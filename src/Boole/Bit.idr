module Boole.Bit

import Data.Linear
import Math.Interfaces

%default total

-----------------------------------------------------------------------
-- THE BY-FIELD B₂
--
-- Wildberger's "by-field" — the two-element field {0, 1} with
-- addition mod 2 (XOR) and multiplication mod 2 (AND).
--
-- BVal is the algebraic type (like SignedUnit for BoxInt).
-- Bit is the dependent witness indexed by BVal.
--
-- Fundamental laws:
--   x + x = Zero   (self-inverse under addition)
--   x * x = x      (idempotent — Boole's law)
-----------------------------------------------------------------------

||| The two elements of the by-field B₂.
||| Analogous to SignedUnit (Pos | Neg) in BoxInt.
public export
data BVal : Type where
  Zero : BVal
  One  : BVal


-----------------------------------------------------------------------
-- BVAL EQUALITY & DISPLAY
-----------------------------------------------------------------------

public export
Eq BVal where
  Zero == Zero = True
  One  == One  = True
  _    == _    = False

public export
Ord BVal where
  compare Zero Zero = EQ
  compare Zero One  = LT
  compare One  Zero = GT
  compare One  One  = EQ

public export
Show BVal where
  show Zero = "0"
  show One  = "1"

-----------------------------------------------------------------------
-- BY-FIELD ARITHMETIC (mod 2) on BVal
-----------------------------------------------------------------------

||| Addition in B₂ (exclusive or).
||| Zero + Zero = Zero,  Zero + One = One,
||| One + Zero = One,    One + One = Zero.
public export
addBVal : BVal -> BVal -> BVal
addBVal Zero Zero = Zero
addBVal Zero One  = One
addBVal One  Zero = One
addBVal One  One  = Zero

||| Multiplication in B₂ (logical and).
public export
mulBVal : BVal -> BVal -> BVal
mulBVal One One = One
mulBVal _   _   = Zero

||| Negation in B₂ is the identity: -x = x.
public export
negBVal : BVal -> BVal
negBVal x = x

-----------------------------------------------------------------------
-- NUM / NEG INSTANCES
-----------------------------------------------------------------------

public export
Num BVal where
  (+) = addBVal
  (*) = mulBVal
  fromInteger n = if mod n 2 == 0 then Zero else One

public export
Neg BVal where
  negate = negBVal
  (-) x y = addBVal x y

-----------------------------------------------------------------------
-- CONVERSION
-----------------------------------------------------------------------

public export
bvalToNat : BVal -> Nat
bvalToNat Zero = Z
bvalToNat One  = S Z

public export
natToBVal : Nat -> BVal
natToBVal Z     = Zero
natToBVal (S Z) = One
natToBVal (S (S k)) = natToBVal k

public export
bvalToInteger : BVal -> Integer
bvalToInteger Zero = 0
bvalToInteger One  = 1

-----------------------------------------------------------------------
-- ABSOLUTE VALUE
-----------------------------------------------------------------------

public export
Abs BVal where
  abs x = x

-----------------------------------------------------------------------
-- LINEAR INSTANCES
-----------------------------------------------------------------------

public export
LConsumable BVal where
  lconsume Zero = ()
  lconsume One  = ()

public export
LComonoid BVal where
  lcomult Zero = Builtin.(#) Zero Zero
  lcomult One  = Builtin.(#) One One

public export
LEq BVal where
  lEq Zero Zero = Builtin.(#) True  (Builtin.(#) Zero Zero)
  lEq One  One  = Builtin.(#) True  (Builtin.(#) One  One)
  lEq Zero One  = Builtin.(#) False (Builtin.(#) Zero One)
  lEq One  Zero = Builtin.(#) False (Builtin.(#) One  Zero)
