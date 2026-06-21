module Boole.MobiusTransform

import Data.List
import Data.Nat
import Math.Multiset
import Boole.Bit
import Boole.Polynumber

%default covering

-----------------------------------------------------------------------
-- THE BOOLE-MÖBIUS TRANSFORM
--
-- Source: Wildberger Lectures 270, 271, 272.
--
-- T(i,j) = 1 iff i ⊆ j (subset inclusion via binary encoding).
-- Self-inverse over B₂: T² = I.
-----------------------------------------------------------------------

||| Apply the Boole-Möbius transform.
||| Self-inverse: mobiusTransform (mobiusTransform v) = v.
public export
mobiusTransform : List BVal -> List BVal
mobiusTransform xs =
  let size = length xs
  in map (\i => foldRow i 0 xs) [0 .. minus size 1]
  where
    foldRow : Nat -> Nat -> List BVal -> BVal
    foldRow _ _ [] = Zero
    foldRow i j (x :: rest) =
      let contrib = if isSubsetNat i j then x else Zero
      in addBVal contrib (foldRow i (S j) rest)

||| Convert a Boolean function (dense truth table) to Boole polynumber.
public export
boolFuncToBoole : List BVal -> BoolePolynumber
boolFuncToBoole truthTable = denseToSparse (mobiusTransform truthTable)

||| Convert a Boole polynumber to Boolean function (dense truth table).
public export
booleToBoolFunc : (numVars : Nat) -> BoolePolynumber -> List BVal
booleToBoolFunc n poly =
  let dense = sparseToDense (power 2 n) poly
  in mobiusTransform dense
