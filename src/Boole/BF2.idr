module Boole.BF2

import Math.BoxInt
import Math.Sing

%default total

-----------------------------------------------------------------------
-- MODULO-2 LOGIC FIELD
--
-- Redefined using Wildberger's recursive mset/singleton model.
-- The two elements of BF_2 ∈ {0,1} are represented as:
--   Z = Sing 0 = [] = ZeroS
--   O = Sing 1 = [[]] = OneS () 1
-----------------------------------------------------------------------

public export
record BF2 where
  constructor MkBF2
  content : Sing Integer ()

public export
Z : BF2
Z = MkBF2 ZeroS

public export
O : BF2
O = MkBF2 (OneS () 1)

public export
normalize : BF2 -> BF2
normalize (MkBF2 ZeroS) = Z
normalize (MkBF2 (OneS () c)) =
  if mod c 2 == 0
    then Z
    else O

public export
Eq BF2 where
  (MkBF2 s1) == (MkBF2 s2) =
    let count1 = case s1 of
                   ZeroS => 0
                   OneS () c => mod c 2
        count2 = case s2 of
                   ZeroS => 0
                   OneS () c => mod c 2
    in (count1 == 0 && count2 == 0) || (count1 == 1 && count2 == 1)

public export
Show BF2 where
  show x = if x == Z then "0" else "1"

||| BOOLEAN RING EVALUATION: XOR Addition (1 + 1 = 0)
public export
addBF2 : BF2 -> BF2 -> BF2
addBF2 x y =
  let c1 = case content x of
             ZeroS => 0
             OneS () c => c
      c2 = case content y of
             ZeroS => 0
             OneS () c => c
  in normalize (MkBF2 (OneS () (c1 + c2)))

||| AND Multiplication (1 * 1 = 1)
public export
mulBF2 : BF2 -> BF2 -> BF2
mulBF2 x y =
  let c1 = case content x of
             ZeroS => 0
             OneS () c => c
      c2 = case content y of
             ZeroS => 0
             OneS () c => c
  in normalize (MkBF2 (OneS () (c1 * c2)))

public export
Num BF2 where
  (+) = addBF2
  (*) = mulBF2
  fromInteger 0 = Z
  fromInteger 1 = O
  fromInteger n = if mod n 2 == 0 then Z else O

||| Lift a BF2 element to a natural number (0 or 1)
public export
bf2ToNat : BF2 -> Nat
bf2ToNat x = if x == Z then 0 else 1

||| Lift a BF2 element to a BoxInt weight for Row 2 transition.
||| Maps the bi-field {Z,O} into algebraic integer space without raw casting.
public export
bf2ToBoxInt : BF2 -> BoxInt
bf2ToBoxInt x = if x == Z then intToBoxInt 0 else intToBoxInt 1
