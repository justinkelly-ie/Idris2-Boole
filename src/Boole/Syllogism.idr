module Boole.Syllogism

import Data.Vect
import Boole.Bit
import Boole.Byte

%default total

-----------------------------------------------------------------------
-- ARISTOTELIAN SYLLOGISMS VIA THE ALGEBRA OF BOOLE
--
-- Source: Wildberger Lectures 255–257, 275, 280.
-----------------------------------------------------------------------

public export
data Predication : Type where
  EveryQisP  : Predication
  NoQisP     : Predication
  SomeQisP   : Predication
  SomeQnotP  : Predication

public export
Show Predication where
  show EveryQisP  = "Every Q is a P"
  show NoQisP     = "No Q is a P"
  show SomeQisP   = "Some Q is a P"
  show SomeQnotP  = "Some Q is not a P"

public export
checkPredication : {n : Nat} -> Predication -> Byte n -> Byte n -> Bool
checkPredication EveryQisP  q p = everyQisP q p
checkPredication NoQisP     q p = noQisP q p
checkPredication SomeQisP   q p = someQisP q p
checkPredication SomeQnotP  q p = someQnotP q p

-----------------------------------------------------------------------
-- FIRST FIGURE
-----------------------------------------------------------------------

||| Barbara: Every B is A, Every C is B ⊢ Every C is A.
public export
barbara : {n : Nat} -> (a, b, c : Byte n) -> Bool
barbara a b c =
  if everyQisP b a && everyQisP c b
  then everyQisP c a
  else True

||| Celarent: No B is A, Every C is B ⊢ No C is A.
public export
celarent : {n : Nat} -> (a, b, c : Byte n) -> Bool
celarent a b c =
  if noQisP b a && everyQisP c b
  then noQisP c a
  else True

||| Darii: Every B is A, Some C is B ⊢ Some C is A.
public export
darii : {n : Nat} -> (a, b, c : Byte n) -> Bool
darii a b c =
  if everyQisP b a && someQisP c b
  then someQisP c a
  else True

||| Ferio: No B is A, Some C is B ⊢ Some C is not A.
public export
ferio : {n : Nat} -> (a, b, c : Byte n) -> Bool
ferio a b c =
  if noQisP b a && someQisP c b
  then someQnotP c a
  else True

-----------------------------------------------------------------------
-- SECOND FIGURE
-----------------------------------------------------------------------

public export
cesare : {n : Nat} -> (p, m, s : Byte n) -> Bool
cesare p m s =
  if noQisP p m && everyQisP s m
  then noQisP s p
  else True

public export
camestres : {n : Nat} -> (p, m, s : Byte n) -> Bool
camestres p m s =
  if everyQisP p m && noQisP s m
  then noQisP s p
  else True

-----------------------------------------------------------------------
-- STOIC LOGIC
-----------------------------------------------------------------------

||| Modus Ponens: P, P→Q ⊢ Q.
||| P→Q = 1 + P + PQ. Premise P·(1+P+PQ) = PQ.
public export
modusPonens : BVal -> BVal -> BVal
modusPonens p q =
  let premise = mulBVal p (One + p + mulBVal p q)
  in case premise of
       Zero => One
       One  => q

||| Modus Tollens: P→Q, ¬Q ⊢ ¬P.
public export
modusTollens : BVal -> BVal -> BVal
modusTollens p q =
  let implication = One + p + mulBVal p q
      notQ = One + q
      premise = mulBVal implication notQ
      notP = One + p
  in case premise of
       Zero => One
       One  => notP

-----------------------------------------------------------------------
-- GENERIC VERIFICATION
-----------------------------------------------------------------------

public export
verifySyllogism : {n : Nat}
              -> (Predication, Byte n, Byte n)
              -> (Predication, Byte n, Byte n)
              -> (Predication, Byte n, Byte n)
              -> Bool
verifySyllogism (pred1, q1, p1) (pred2, q2, p2) (conc, qc, pc) =
  if checkPredication pred1 q1 p1 && checkPredication pred2 q2 p2
  then checkPredication conc qc pc
  else True
