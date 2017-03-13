module CommutativeSemiring

import public BinaryOperation
import Algebra.Semiring
import Algebra.CommutativeMonoid

%access public export

||| Commutative semiring is semiring with commutative multiplication
record CommutativeSemiring where
    constructor MkCommutativeSemiring
    setoid: Setoid
    plus: ClosedBinaryOperation setoid
    mult: ClosedBinaryOperation setoid

    plusIsAssociative: IsAssociative plus
    plusHasNeutral: HasNeutral plus
    plusIsCommutative: IsCommutative plus

    multIsAssociative: IsAssociative mult
    multHasNeutral: HasNeutral mult
    multIsCommutative: IsCommutative mult

    isDistributive: IsDistributive plus mult

||| Proof that commutative semiring is semiring
commutativeSemiringIsSemiring: CommutativeSemiring -> Semiring
commutativeSemiringIsSemiring
    (MkCommutativeSemiring s plus mult plusAssoc plusNeutral plusCommut multAssoc multNeutral _ distribute) =
    (MkSemiring s plus mult plusAssoc plusNeutral plusCommut multAssoc multNeutral distribute)

||| Proof that commutative semiring is commutative monoid over multiplication
commutativeSemiringIsCommutativeMonoidOverMult: CommutativeSemiring -> CommutativeMonoid
commutativeSemiringIsCommutativeMonoidOverMult
    (MkCommutativeSemiring s _ mult _ _ _ multAssoc multNeutral multCommut _) =
    (MkCommutativeMonoid s mult multAssoc multNeutral multCommut)
