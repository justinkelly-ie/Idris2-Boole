module Boole.FunctionalProbability

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
-- 2. HEHNER FRACTION DEFINITION (Row 3 Complete Type)
-----------------------------------------------------------------------

||| Row 3 complete fraction type.
||| Pairs a quantified multiset (numerator box) with its total universe sum (denominator box).
||| The dependent type constraint `isNormalized` proves the denominator is exactly the total mass.
public export
record HehnerFraction (v : Type) where
  constructor OverHehnerSpace
  numeratorMset  : Multiset BoxInt v
  denominatorSum : BoxInt
  isNormalized   : denominatorSum = totalMass numeratorMset

||| Smart constructor for HehnerFraction.
||| Automatically constructs the normalization proof.
public export
mkHehnerFraction : (m : Multiset BoxInt v) -> HehnerFraction v
mkHehnerFraction m = OverHehnerSpace m (totalMass m) Refl

||| Extract the probability of a specific state in the normalised space.
||| Returns the probability as an MSetFraction.
||| If the total mass is zero (degenerate space), returns 0/1.
public export
stateProbability : Eq v => HehnerFraction v -> v -> MSetFraction
stateProbability (OverHehnerSpace m den prf) s =
  let (MkUr denVal) = boxToInt den
      absDen = Math.Interfaces.integerToNat (abs denVal)
  in if absDen == 0
     then zeroMSF
     else
       let wt = lookupWeight s m
       in MkMSF wt absDen
  where
    lookupWeight : v -> Multiset BoxInt v -> BoxInt
    lookupWeight _ ZeroM = 0
    lookupWeight x (AddM y w rest) =
      if x == y then w + lookupWeight x rest
      else lookupWeight x rest

||| Normalize a HehnerFraction into a list of states and their corresponding probabilities.
public export
normalizeFraction : HehnerFraction v -> List (v, MSetFraction)
normalizeFraction (OverHehnerSpace m den prf) =
  let (MkUr denVal) = boxToInt den
      absDen = Math.Interfaces.integerToNat (abs denVal)
  in if absDen == 0
     then []
     else go m absDen
  where
    go : Multiset BoxInt v -> Nat -> List (v, MSetFraction)
    go ZeroM _ = []
    go (AddM elem wt rest) d =
      (elem, MkMSF wt d) :: go rest d

-----------------------------------------------------------------------
-- 3. HEHNER NORMALISATION (Legacy API)
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

-----------------------------------------------------------------------
-- 5. VERIFIED EXAMPLES FROM HEHNER'S PAPER
-----------------------------------------------------------------------

-- === Example 1: The Two Children Paradox ===
-- "I have two children. At least one child is a girl. What is the probability that the other child is also a girl?"

public export
data Gender = Boy | Girl

public export
Eq Gender where
  Boy == Boy = True
  Girl == Girl = True
  _ == _ = False

public export
Show Gender where
  show Boy = "Boy"
  show Girl = "Girl"

||| Unnormalized state space for families with 2 children.
||| Each outcome has a weight of 1.
public export
twoChildrenSpace : Multiset BoxInt (Gender, Gender)
twoChildrenSpace = fromList
  [ ((Boy, Boy), 1)
  , ((Boy, Girl), 1)
  , ((Girl, Boy), 1)
  , ((Girl, Girl), 1)
  ]

||| Case A: "At least one child is a girl"
||| Filters the space, leaving 3 outcomes.
public export
atLeastOneGirl : HehnerFraction (Gender, Gender)
atLeastOneGirl = mkHehnerFraction $ fromList
  [ ((Boy, Girl), 1)
  , ((Girl, Boy), 1)
  , ((Girl, Girl), 1)
  ]

||| The probability that both are girls given at least one is a girl (evaluates to 1/3).
public export
probBothGirlsGivenAtLeastOne : MSetFraction
probBothGirlsGivenAtLeastOne = stateProbability atLeastOneGirl (Girl, Girl)

||| Case B: "The older child (first) is a girl"
||| Filters the space, leaving 2 outcomes.
public export
olderChildGirl : HehnerFraction (Gender, Gender)
olderChildGirl = mkHehnerFraction $ fromList
  [ ((Girl, Boy), 1)
  , ((Girl, Girl), 1)
  ]

||| The probability that both are girls given the older is a girl (evaluates to 1/2).
public export
probBothGirlsGivenOlderGirl : MSetFraction
probBothGirlsGivenOlderGirl = stateProbability olderChildGirl (Girl, Girl)


-- === Example 2: The Three Cards Paradox ===
-- Three cards: R (red/red), W (white/white), M (mixed red/white). 
-- You look at one side, it is red. Probability the other side is also red?

public export
data Card = CardRR | CardWW | CardMR

public export
Eq Card where
  CardRR == CardRR = True
  CardWW == CardWW = True
  CardMR == CardMR = True
  _ == _ = False

public export
Show Card where
  show CardRR = "CardRR"
  show CardWW = "CardWW"
  show CardMR = "CardMR"

public export
data Side = RedSide | WhiteSide

public export
Eq Side where
  RedSide == RedSide = True
  WhiteSide == WhiteSide = True
  _ == _ = False

public export
Show Side where
  show RedSide = "Red"
  show WhiteSide = "White"

||| Total unnormalized space of card choices and observed sides (6 outcomes).
public export
threeCardsSpace : Multiset BoxInt (Card, Side)
threeCardsSpace = fromList
  [ ((CardRR, RedSide), 1)
  , ((CardRR, RedSide), 1)
  , ((CardWW, WhiteSide), 1)
  , ((CardWW, WhiteSide), 1)
  , ((CardMR, RedSide), 1)
  , ((CardMR, WhiteSide), 1)
  ]

||| Filtered space where the observed side is Red (3 outcomes).
public export
observedRedSide : HehnerFraction (Card, Side)
observedRedSide = mkHehnerFraction $ fromList
  [ ((CardRR, RedSide), 1)
  , ((CardRR, RedSide), 1)
  , ((CardMR, RedSide), 1)
  ]

||| The probability that the other side is also red.
||| This is equivalent to checking if the card is CardRR (evaluates to 2/3).
public export
probOtherSideRed : MSetFraction
probOtherSideRed = stateProbability observedRedSide (CardRR, RedSide)
