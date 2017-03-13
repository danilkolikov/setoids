module AbelianGroup

import public BinaryOperation
import Algebra.Group
import Algebra.CommutativeMonoid

%access public export

||| Abelian group is group where operation is commutative
record AbelianGroup where
    constructor MkAbelianGroup
    setoid: Setoid
    op: ClosedBinaryOperation setoid

    isAssociative: IsAssociative op
    hasNeutral: HasNeutral op
    hasInverse: HasInverse op
    isCommutative: IsCommutative op

||| Proof that abelian group is still group
abelianGroupIsGroup: AbelianGroup -> Group
abelianGroupIsGroup (MkAbelianGroup s op assoc neutral inverse _) =
    MkGroup s op assoc neutral inverse

||| Proof that abelian group is commutative monoid
abelianGroupIsCommutativeMonoid: AbelianGroup -> CommutativeMonoid
abelianGroupIsCommutativeMonoid (MkAbelianGroup s op assoc neutral _ commut) =
    MkCommutativeMonoid s op assoc neutral commut
