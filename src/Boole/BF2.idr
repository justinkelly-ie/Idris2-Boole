module Boole.BF2

import Math.BoxInt

%default total

-----------------------------------------------------------------------
-- MODULO-2 LOGIC FIELD
--
-- The two elements of BF_2 ∈ {0,1} as a strict modulo-2 type.
-- This is the coefficient field for the Boolean Ring (Row 1).
-- Addition is XOR (1 + 1 = 0); multiplication is AND (1 * 1 = 1).
-----------------------------------------------------------------------

public export
data BF2 = Z | O

public export
Eq BF2 where
  Z == Z = True
  O == O = True
  _ == _ = False

public export
Show BF2 where
  show Z = "0"
  show O = "1"

||| BOOLEAN RING EVALUATION: XOR Addition (1 + 1 = 0)
public export
addBF2 : BF2 -> BF2 -> BF2
addBF2 Z x = x
addBF2 x Z = x
addBF2 O O = Z

||| AND Multiplication (1 * 1 = 1)
public export
mulBF2 : BF2 -> BF2 -> BF2
mulBF2 O O = O
mulBF2 _ _ = Z

public export
Num BF2 where
  (+) = addBF2
  (*) = mulBF2
  fromInteger 0 = Z
  fromInteger 1 = O
  fromInteger _ = Z

||| Lift a BF2 element to a natural number (0 or 1)
public export
bf2ToNat : BF2 -> Nat
bf2ToNat Z = 0
bf2ToNat O = 1

||| Lift a BF2 element to a BoxInt weight for Row 2 transition.
||| Maps the bi-field {Z,O} into algebraic integer space without raw casting.
public export
bf2ToBoxInt : BF2 -> BoxInt
bf2ToBoxInt Z = intToBoxInt 0
bf2ToBoxInt O = intToBoxInt 1
