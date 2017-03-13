module Group

import public BinaryOperation
import Algebra.Monoid

%access public export

||| Group is monoid where every element has inverse
record Group where
    constructor MkGroup
    setoid: Setoid
    op: ClosedBinaryOperation setoid

    isAssociative: IsAssociative op
    hasNeutral: HasNeutral op
    hasInverse: HasInverse op

||| Proof that group is monoid
groupIsMonoid: Group -> Monoid
groupIsMonoid (MkGroup s op assoc neutral _) = MkMonoid s op assoc neutral
