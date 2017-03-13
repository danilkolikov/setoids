||| Example of setoid definition
module Natural

import Setoid
import Setoid.Identical
import Algebra.CommutativeSemiring
import Isomorphism
import Relation

%access public export
%auto_implicits off

||| Extenstional equivalence relation for natural numbers
public export data NatEqual: Nat -> Nat -> Type where
    NatRefl: {x: Nat} -> {y: Nat} -> (x = y) -> NatEqual x y

||| Proof that custom equalty for natural numbers is equality
natEqualIsEquality: IsEquality NatEqual
natEqualIsEquality = MkIsEquality
    (MkIsReflexive $ NatRefl Refl)
    (MkIsSymmetric $ \(NatRefl left) => NatRefl $ sym left)
    (MkIsTransittive $ \(NatRefl left), (NatRefl center) => NatRefl $ trans left center)

||| Setoid for natural numbers (Example of usage of custom equality)
Natural: Setoid
Natural = MkSetoid Nat NatEqual natEqualIsEquality

||| Identical setoid for Natural
identicalNaturalSetoid: Setoid
identicalNaturalSetoid = identicalSetoid Nat

||| Factorizes Natural by defined equality
naturalFactorization: Factorization Natural Nat
naturalFactorization = MkIsomorphism
    (MkFunction id (\(NatRefl prf) => prf))
    (MkFunction id (\prf => NatRefl prf))
    (MkFunctionEquality $ NatRefl Refl)
    (MkFunctionEquality Refl)

--- Plus part ---

||| Plus for natural is default `plus` and proof of bi-congruence
plus: ClosedBinaryOperation Natural
plus = MkBinaryOperation
    Nat.plus
    (\(NatRefl xs), (NatRefl ys) => NatRefl $ rewrite xs in rewrite ys in Refl)

naturalPlusIsAssociative: IsAssociative plus
naturalPlusIsAssociative = MkIsAssociative $ NatRefl $ plusAssociative _ _ _

naturalPlusHasNeutral: HasNeutral plus
naturalPlusHasNeutral = MkHasNeutral
    0
    (NatRefl $ plusZeroLeftNeutral _)
    (NatRefl $ plusZeroRightNeutral _)

naturalPlusIsCommutative: IsCommutative plus
naturalPlusIsCommutative = MkIsCommutative $ NatRefl $ plusCommutative _ _

--- Mult part ---

||| Mult for natural is default `mult` and proof of bi-congruence
mult: ClosedBinaryOperation Natural
mult = MkBinaryOperation
    Nat.mult
    (\(NatRefl xs), (NatRefl ys) => NatRefl $ rewrite xs in rewrite ys in Refl)

naturalMultIsAssociative: IsAssociative mult
naturalMultIsAssociative = MkIsAssociative $ NatRefl $ multAssociative _ _ _

naturalMultIsCommutative: IsCommutative mult
naturalMultIsCommutative = MkIsCommutative $ NatRefl $ multCommutative _ _

naturalMultHasNeutral: HasNeutral mult
naturalMultHasNeutral = MkHasNeutral
    1
    (NatRefl $ multOneLeftNeutral _)
    (NatRefl $ multOneRightNeutral _)

naturalMultIsDistributiveOverPlus: IsDistributive plus mult
naturalMultIsDistributiveOverPlus = MkIsDistributive
    (NatRefl $ multDistributesOverPlusLeft _ _ _)
    (NatRefl $ multDistributesOverPlusRight _ _ _)

--- Algebraic structure ---

||| Algebraic structure of natural numbers is commutative semiring
naturalIsCommutativeSemiring: CommutativeSemiring
naturalIsCommutativeSemiring = MkCommutativeSemiring
    Natural
    plus
    mult
    naturalPlusIsAssociative
    naturalPlusHasNeutral
    naturalPlusIsCommutative
    naturalMultIsAssociative
    naturalMultHasNeutral
    naturalMultIsCommutative
    naturalMultIsDistributiveOverPlus
