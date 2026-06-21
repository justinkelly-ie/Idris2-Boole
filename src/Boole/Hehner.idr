module Boole.Hehner

import Data.List
import Math.Multiset
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Boole.Bit
import Boole.Bridge

%default covering

-----------------------------------------------------------------------
-- HEHNER FUNCTIONAL PROBABILITY (Row 3)
--
-- Source: Eric Hehner, "a]Probability Theory".
--
-- Hehner replaces infinite quantifiers (∀, ∃) with calculational
-- min/max over closed finite spaces.  Probability is not an axiom
-- but a derived normalisation:
--
--   E̅ = E · (ΣE)⁻¹
--
-- In our MSetFraction framework, this becomes:
--   For each element e with weight w in a multiset of total mass T,
--   the probability is w/T — computed by cross-multiplication, no division.
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- 1. TOTAL MASS (Universe Sum)
-----------------------------------------------------------------------

||| Compute the total signed mass of a BoxInt multiset.
||| This is the denominator of Hehner normalisation: ΣE.
public export
totalMass : Multiset BoxInt a -> BoxInt
totalMass ZeroM = 0
totalMass (AddM _ c rest) = c + totalMass rest

||| Compute the total unsigned mass (absolute values).
public export
totalAbsMass : Multiset BoxInt a -> BoxInt
totalAbsMass ZeroM = 0
totalAbsMass (AddM _ c rest) = abs c + totalAbsMass rest

-----------------------------------------------------------------------
-- 2. HEHNER NORMALISATION
-----------------------------------------------------------------------

||| Normalise a multiset into a list of MSetFractions.
||| Each element's weight becomes the numerator; the total mass
||| becomes the shared denominator.
|||
||| E̅ᵢ = wᵢ / ΣE
|||
||| Returns the empty list if total mass is zero (degenerate space).
public export
hehnerNormalize : Multiset BoxInt a -> List (a, MSetFraction)
hehnerNormalize m =
  let mass = totalMass m
      (MkUr massVal) = boxToInt mass
      absDen = Math.Interfaces.integerToNat (abs massVal)
  in if absDen == 0
     then []
     else go m absDen
  where
    go : Multiset BoxInt a -> Nat -> List (a, MSetFraction)
    go ZeroM _ = []
    go (AddM elem wt rest) d =
      (elem, MkMSF wt d) :: go rest d

-----------------------------------------------------------------------
-- 3. CALCULATIONAL QUANTIFIERS (min / max)
-----------------------------------------------------------------------

||| Minimum weight in a BoxInt multiset (Hehner's ∀ replacement).
public export
minWeight : Multiset BoxInt a -> BoxInt
minWeight ZeroM = 0
minWeight (AddM _ c ZeroM) = c
minWeight (AddM _ c rest) =
  let restMin = minWeight rest
  in if c < restMin then c else restMin

||| Maximum weight in a BoxInt multiset (Hehner's ∃ replacement).
public export
maxWeight : Multiset BoxInt a -> BoxInt
maxWeight ZeroM = 0
maxWeight (AddM _ c ZeroM) = c
maxWeight (AddM _ c rest) =
  let restMax = maxWeight rest
  in if c > restMax then c else restMax

-----------------------------------------------------------------------
-- 4. PROPORTIONAL COMPARISON
-----------------------------------------------------------------------

||| Check whether two elements have equal probability in a normalised space.
||| Uses cross-multiplication: w₁ * T == w₂ * T (trivially true if same
||| denominator, but this generalises to comparing across different spaces).
public export
eqProbability : MSetFraction -> MSetFraction -> Bool
eqProbability = eqMSF

||| Check whether one probability dominates another.
||| a/b > c/d ⟺ a*d > c*b (for positive denominators).
public export
gtProbability : MSetFraction -> MSetFraction -> Bool
gtProbability (MkMSF a b) (MkMSF c d) =
  (a * fromInteger (natToInteger d)) > (c * fromInteger (natToInteger b))
