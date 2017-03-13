module Monoid

import public BinaryOperation
import Algebra.Semigroup

%access public export

||| Monoid is semigroup with neutral element
record Monoid where
    constructor MkMonoid
    setoid: Setoid
    op: ClosedBinaryOperation setoid
    isAssociative: IsAssociative op
    hasNeutral: HasNeutral op

||| Proof that monoid is semigroo
monoidIsSemigroup: Monoid -> Semigroup
monoidIsSemigroup (MkMonoid s op assoc _) = MkSemigroup s op assoc
