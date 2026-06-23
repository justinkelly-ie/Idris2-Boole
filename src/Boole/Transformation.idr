module Boole.Transformation

import Math.Multiset
import Math.Sing
import Boole.BF2
import Boole.BooleFraction

%default total

||| Unified state type for logic gates, combining variables and constants.
public export
data LogicState state = VarState state | ConstState TrivialBase

public export
Eq state => Eq (LogicState state) where
  (VarState x) == (VarState y) = x == y
  (ConstState BaseAnchor) == (ConstState BaseAnchor) = True
  _ == _ = False

public export
Show state => Show (LogicState state) where
  show (VarState x) = show x
  show (ConstState BaseAnchor) = "1"

||| The Transformation MSet (Logic Gate Operator):
||| A multiset of logical relations.
||| Natively mirrors the Maxel (multiset of Pixels) in spatial geometry.
public export
TransformationMSet : (state : Type) -> Type
TransformationMSet state = Multiset BF2 (SingRelation (LogicState state))

||| A wire connection (buffer gate) mapping an input state to an output state.
public export
bufferGate : state -> state -> TransformationMSet state
bufferGate input output = AddM (MkSingRelation (MkSing (VarState input)) (MkSing (VarState output))) O ZeroM

||| A NOT gate mapping an input state to a complement output state.
||| Implements XOR-inversion by adding the unit constant as an active source.
public export
notGate : state -> state -> TransformationMSet state
notGate input output =
  let wire = MkSingRelation (MkSing (VarState input)) (MkSing (VarState output))
      bias = MkSingRelation (MkSing (ConstState BaseAnchor)) (MkSing (VarState output))
  in AddM wire O (AddM bias O ZeroM)

||| An XOR gate mapping two input states to a single output state.
public export
xorGate : state -> state -> state -> TransformationMSet state
xorGate in1 in2 output =
  let w1 = MkSingRelation (MkSing (VarState in1)) (MkSing (VarState output))
      w2 = MkSingRelation (MkSing (VarState in2)) (MkSing (VarState output))
  in AddM w1 O (AddM w2 O ZeroM)
