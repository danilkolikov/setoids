module Semiring

import public BinaryOperation
import Algebra.CommutativeMonoid
import Algebra.Monoid

%access public export

||| Semiring is a set with two operations - addition and multiplication.
|||
||| Semiring is a commutative monoid over addition and monoid over multiplication
||| and is ditributive over this operations
record Semiring where
    constructor MkSemiring
    setoid: Setoid
    plus: ClosedBinaryOperation setoid
    mult: ClosedBinaryOperation setoid

    plusIsAssociative: IsAssociative plus
    plusHasNeutral: HasNeutral plus
    plusIsCommutative: IsCommutative plus

    multIsAssociative: IsAssociative mult
    multHasNeutral: HasNeutral mult

    isDistributive: IsDistributive plus mult

||| Proof that semiring is commutative monoid over addition
semiringIsCommutativeMonoidOverPlus: Semiring -> CommutativeMonoid
semiringIsCommutativeMonoidOverPlus (MkSemiring s plus mult assoc neutral commut _ _ _) =
    MkCommutativeMonoid s plus assoc neutral commut

||| Proof that semiring is monoid over multiplication
semiringIsMonoidOverMult: Semiring -> Monoid
semiringIsMonoidOverMult (MkSemiring s plus mult _ _ _ assoc neutral _) =
    MkMonoid s mult assoc neutral
