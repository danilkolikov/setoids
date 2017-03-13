module CommutativeMonoid

import public BinaryOperation
import Algebra.Monoid

%access public export

||| Commutative monoid is monoid with commutative operation
record CommutativeMonoid where
    constructor MkCommutativeMonoid
    setoid: Setoid
    op: ClosedBinaryOperation setoid

    isAssociative: IsAssociative op
    hasNeutral: HasNeutral op
    isCommutative: IsCommutative op

||| Proof that commutative monoid is still monoid
commutativeMonoidIsMonoid: CommutativeMonoid -> Monoid
commutativeMonoidIsMonoid (MkCommutativeMonoid s op assoc neutral _) = MkMonoid s op assoc neutral
