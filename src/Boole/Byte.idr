module Boole.Byte

import Data.Vect
import Boole.Bit

%default total

-----------------------------------------------------------------------
-- BOOLE ALGEBRA B₂ⁿ
--
-- An N-dimensional vector over the by-field B₂.
-- Represents a property assignment over a population of N objects.
-- Operations are pointwise by-field arithmetic.
-----------------------------------------------------------------------

||| An N-dimensional Boole vector. Each component is a BVal.
public export
Byte : Nat -> Type
Byte n = Vect n BVal

-----------------------------------------------------------------------
-- VECTOR ARITHMETIC
-----------------------------------------------------------------------

||| Pointwise addition (XOR) of two Boole vectors.
public export
addByte : Byte n -> Byte n -> Byte n
addByte [] [] = []
addByte (x :: xs) (y :: ys) = addBVal x y :: addByte xs ys

||| Pointwise multiplication (AND) of two Boole vectors.
public export
mulByte : Byte n -> Byte n -> Byte n
mulByte [] [] = []
mulByte (x :: xs) (y :: ys) = mulBVal x y :: mulByte xs ys

||| Scalar multiplication: multiply every component by a BVal.
public export
scaleByte : BVal -> Byte n -> Byte n
scaleByte _ [] = []
scaleByte s (x :: xs) = mulBVal s x :: scaleByte s xs

||| The zero vector in B₂ⁿ.
public export
zeroByte : {n : Nat} -> Byte n
zeroByte {n = Z} = []
zeroByte {n = S k} = Zero :: zeroByte

||| The one vector in B₂ⁿ (all components One).
public export
oneByte : {n : Nat} -> Byte n
oneByte {n = Z} = []
oneByte {n = S k} = One :: oneByte

-----------------------------------------------------------------------
-- PREDICATES
-----------------------------------------------------------------------

||| Test whether a Boole vector is the zero vector.
public export
isZeroByte : Byte n -> Bool
isZeroByte [] = True
isZeroByte (Zero :: xs) = isZeroByte xs
isZeroByte (One :: _) = False

||| Test whether a Boole vector is nonzero.
public export
isNonZeroByte : Byte n -> Bool
isNonZeroByte v = not (isZeroByte v)

-----------------------------------------------------------------------
-- ARISTOTLE'S FOUR SYLLOGISTIC FORMS
--
-- NOT P = 1 + P  (derived from addition, not a primitive)
-----------------------------------------------------------------------

||| Every Q is a P: Q·(1+P) = 0.
public export
everyQisP : {n : Nat} -> Byte n -> Byte n -> Bool
everyQisP q p = isZeroByte (mulByte q (addByte oneByte p))

||| No Q is a P: Q·P = 0.
public export
noQisP : Byte n -> Byte n -> Bool
noQisP q p = isZeroByte (mulByte q p)

||| Some Q is a P: Q·P ≠ 0.
public export
someQisP : Byte n -> Byte n -> Bool
someQisP q p = isNonZeroByte (mulByte q p)

||| Some Q is not a P: Q·(1+P) ≠ 0.
public export
someQnotP : {n : Nat} -> Byte n -> Byte n -> Bool
someQnotP q p = isNonZeroByte (mulByte q (addByte oneByte p))

-----------------------------------------------------------------------
-- DISPLAY
-----------------------------------------------------------------------

export
Show (Byte n) where
  show v = "(" ++ showInner v ++ ")"
    where
      showInner : Byte m -> String
      showInner [] = ""
      showInner [x] = show x
      showInner (x :: xs) = show x ++ "," ++ showInner xs
