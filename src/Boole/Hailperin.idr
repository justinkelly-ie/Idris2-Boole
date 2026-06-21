module Boole.Hailperin

import Data.List
import Math.Multiset
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Boole.Bit
import Boole.Polynumber
import Boole.Bridge

%default covering

-----------------------------------------------------------------------
-- HAILPERIN PROBABILITY BOUNDS (Row 4)
--
-- Source: Theodore Hailperin, "Boole's Logic and Probability" (1986).
--
-- When given incomplete data (fragmentary probabilities), a single
-- exact probability cannot be determined.  Instead, Hailperin showed
-- that Boole's method produces tight interval bounds [min, max]
-- via the inclusion-exclusion principle.
--
-- In our framework, the Möbius inversion signs (from Bridge.idr)
-- drive the bound extraction.  No LP solver needed — the
-- Boole-Möbius polynomial structure yields the bounds directly
-- by enforcing non-negativity of truth-table weights.
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- 1. PROBABILITY INTERVAL
-----------------------------------------------------------------------

||| A closed interval [lo, hi] of MSetFractions.
||| Represents the tightest possible bounds on an unknown probability.
public export
record ProbBounds where
  constructor MkBounds
  lo : MSetFraction
  hi : MSetFraction

public export
Show ProbBounds where
  show (MkBounds l h) = "[" ++ show l ++ ", " ++ show h ++ "]"

public export
Eq ProbBounds where
  (MkBounds l1 h1) == (MkBounds l2 h2) = l1 == l2 && h1 == h2

-----------------------------------------------------------------------
-- 2. TRIVIAL BOUNDS
-----------------------------------------------------------------------

||| The trivial bounds [0/1, 1/1] — no information.
public export
trivialBounds : ProbBounds
trivialBounds = MkBounds zeroMSF oneMSF

||| An exact probability (degenerate interval where lo == hi).
public export
exactBounds : MSetFraction -> ProbBounds
exactBounds p = MkBounds p p

-----------------------------------------------------------------------
-- 3. INTERSECTION OF BOUNDS
-----------------------------------------------------------------------

||| Tighten two intervals by taking the intersection.
||| max(lo₁, lo₂) and min(hi₁, hi₂).
||| Returns Nothing if the intersection is empty (contradiction).
public export
intersectBounds : ProbBounds -> ProbBounds -> Maybe ProbBounds
intersectBounds (MkBounds l1 h1) (MkBounds l2 h2) =
  let newLo = if gtProbability l1 l2 then l1 else l2
      newHi = if gtProbability h1 h2 then h2 else h1
  in if gtProbability newLo newHi
     then Nothing
     else Just (MkBounds newLo newHi)
  where
    gtProbability : MSetFraction -> MSetFraction -> Bool
    gtProbability (MkMSF a b) (MkMSF c d) =
      (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

-----------------------------------------------------------------------
-- 4. BOOLE-FRÉCHET BOUNDS (Two-Event Case)
-----------------------------------------------------------------------

||| Given P(A) = pA and P(B) = pB, compute the Boole-Fréchet bounds
||| on P(A ∧ B) using the inclusion-exclusion principle.
|||
||| Lower bound: max(0, P(A) + P(B) - 1)
||| Upper bound: min(P(A), P(B))
|||
||| These are the exact bounds Wildberger derives from the Boole-Möbius
||| polynomial by enforcing non-negativity of truth-table coefficients.
public export
booleFrechetBounds : (pA : MSetFraction) -> (pB : MSetFraction) -> ProbBounds
booleFrechetBounds pA pB =
  let -- Lower: max(0, pA + pB - 1)
      sumMinus1 = subMSF (addMSF pA pB) oneMSF
      lo = if gtProbMSF sumMinus1 zeroMSF then sumMinus1 else zeroMSF
      -- Upper: min(pA, pB)
      hi = if gtProbMSF pA pB then pB else pA
  in MkBounds lo hi
  where
    gtProbMSF : MSetFraction -> MSetFraction -> Bool
    gtProbMSF (MkMSF a b) (MkMSF c d) =
      (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))

-----------------------------------------------------------------------
-- 5. INCLUSION-EXCLUSION EXTRACTION FROM MÖBIUS COEFFICIENTS
-----------------------------------------------------------------------

||| Given a list of Möbius-inverted coefficients (from mobiusInverseZ),
||| extract the probability bounds by reading off the non-negativity
||| constraints on the truth-table weights.
|||
||| Each coefficient cᵢ multiplied by the unknown target probability P
||| must satisfy cᵢ ≥ 0.  This directly yields interval constraints.
public export
extractBoundsFromMobius : List BoxInt -> List ProbBounds
extractBoundsFromMobius [] = []
extractBoundsFromMobius coeffs =
  map toBound coeffs
  where
    toBound : BoxInt -> ProbBounds
    toBound c =
      let (MkUr val) = boxToInt c
      in if val > 0 then MkBounds zeroMSF (fromBoxInt c)
         else if val < 0 then MkBounds (fromBoxInt (negate c)) oneMSF
         else trivialBounds
