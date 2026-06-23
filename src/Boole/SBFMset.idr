module Boole.SBFMset

import Math.Multiset
import Math.Sing
import Boole.BF2
import Boole.SingFraction
import Boole.Transformation

%default total

||| The Symmetric Bilinear Form MSet (SBFMset):
||| A multiset of logical relations mapping inputs to gate inputs.
public export
SBFMset : (state : Type) -> Type
SBFMset state = Multiset BF2 (SingRelation (LogicState state))
