||| Module with definition and basic properties of extensional binary operations
module BinaryOperation

import public Setoid
import public Function

%access public export
%auto_implicits off

||| Extensional binary operation. It acts on two setoids and congruent
||| by each argument
||| @ A Setoid of first operand
||| @ B Setoid of second operand
||| @ C Setoid of result
data BinaryOperation: (A, B, C: Setoid) -> Type where
    ||| Constructs extensional binary operation
    ||| @ A Setoid of first operand
    ||| @ B Setoid of second operand
    ||| @ C Setoid of result
    ||| @ applyOp Application of operation
    ||| @ biCongruence Proof that defined application is congruent by it's arguments, i.e.
    |||   `x =(A) x', y =(B) y' => apply x y =(C) apply x' y'`
    MkBinaryOperation: {A, B, C: Setoid}
        -> (applyOp: Carrier A -> Carrier B -> Carrier C)
        -> (biCongruence: {x, x': Carrier A} -> {y, y': Carrier B}
                -> Equal A x x'
                -> Equal B y y'
                -> Equal C (applyOp x y) (applyOp x' y')
            )
        -> BinaryOperation A B C

||| Apply extensional binary operation
||| @ op ensional binary operation
||| @ x First operand
||| @ y Second operand
applyOp: {A, B, C: Setoid} -> (op: BinaryOperation A B C) -> (x: Carrier A) -> (y: Carrier B) -> Carrier C
applyOp (MkBinaryOperation ap _) = ap

||| Get proof that extensional binary operation is congruent by it's arguments
||| @ op ensional binary operation
biCongruence: {A, B, C: Setoid} -> (op: BinaryOperation A B C) ->
    ({x, x': Carrier A} -> {y, y': Carrier B} -> (Equal A x x')
        -> (Equal B y y')
        -> (Equal C (applyOp op x y) (applyOp op x' y'))
    )
biCongruence (MkBinaryOperation _ biCong) = biCong

||| Closed extensional binary operation, i.e. such operation which
||| operands and result belongs to same setoid
||| @ A Setoid
ClosedBinaryOperation: (A: Setoid) -> Type
ClosedBinaryOperation A = BinaryOperation A A A

||| Proof that closed extensional binary operation is associative
||| @ op Operation
data IsAssociative: {A: Setoid} -> (op: ClosedBinaryOperation A) -> Type where
    ||| Shows that operation is associative
    ||| @ op Operation
    ||| @ assoc Proof that
    ||| ```idris
    |||     (a * (b * c)) =(A) ((a * b) * c)
    ||| ```
    MkIsAssociative: {A: Setoid} -> {op: ClosedBinaryOperation A}
        -> (assoc: {a, b, c: Carrier A}
            -> Equal A (applyOp op a (applyOp op b c)) (applyOp op (applyOp op a b) c)
            )
        -> IsAssociative op

||| Get proof that operation is associative
||| @ op Operation
assoc: {A: Setoid} -> {op: ClosedBinaryOperation A} -> IsAssociative op ->
    {a, b, c: Carrier A} -> Equal A (applyOp op a (applyOp op b c)) (applyOp op (applyOp op a b) c)
assoc (MkIsAssociative as) = as

||| Proof that closed extensional binary operation has neutral element
||| @ op Operation
data HasNeutral: {A: Setoid} -> (op: ClosedBinaryOperation A) -> Type where
    ||| Shows that operation has neutral element
    ||| @ getNeutral Neutral element
    ||| @ leftNeutral Proof that neutral element is left neutral
    ||| @ rightNeutral Proof that neutral element is right neutral
    MkHasNeutral: {A: Setoid} -> {op: ClosedBinaryOperation A}
        -> (getNeutral: Carrier A)
        -> (leftNeutral: {x: Carrier A} -> Equal A (applyOp op getNeutral x) x)
        -> (rightNeutral: {x: Carrier A} -> Equal A (applyOp op x getNeutral) x)
        -> HasNeutral op

||| Get neutral element for closed extensional binary operation
||| @ prf Proof that operation has neutral element
getNeutral: {A: Setoid} -> {op: ClosedBinaryOperation A}
    -> (prf: HasNeutral op)
    -> Carrier A
getNeutral (MkHasNeutral neutral _ _) = neutral

||| Get proof that neutral element for closed extensional binary operation
||| is left neutral element
||| @ prf Proof that operation has neutral element
leftNeutral: {A: Setoid} -> {op: ClosedBinaryOperation A}
    -> (prf: HasNeutral op)
    -> {x: Carrier A} -> Equal A (applyOp op (getNeutral prf) x) x
leftNeutral (MkHasNeutral _ left _) = left

||| Get proof that neutral element for closed extensional binary operation
||| is right neutral element
||| @ prf Proof that operation has neutral element
rightNeutral: {A: Setoid} -> {op: ClosedBinaryOperation A}
    -> (prf: HasNeutral op)
    -> {x: Carrier A} -> Equal A (applyOp op x (getNeutral prf)) x
rightNeutral (MkHasNeutral _ _ right) = right

||| Proof that closed extensional binary operation has inverse
||| @ op Operation
data HasInverse: {A: Setoid} -> (op: ClosedBinaryOperation A) -> Type where
    ||| Shows that operation has inverse
    ||| @ hasNeutral Proof that operation has neutral element
    ||| @ inverse Inverse specified element
    ||| @ leftInverse Proof that (inverse x) is left inverse element to x
    ||| @ rightInverse Proof that (inverse x) is right inverse element to x
    MkHasInverse: {A: Setoid} -> {op: ClosedBinaryOperation A}
        -> {hasNeutral: HasNeutral op}
        -> (inverse: Function A A)
        -> (leftInverse: {x: Carrier A}
            -> Equal A (applyOp op (apply inverse x) x) (getNeutral hasNeutral)
            )
        -> (rightInverse: {x: Carrier A}
            -> Equal A (applyOp op x (apply inverse x)) (getNeutral hasNeutral)
            )
        -> HasInverse op

||| Proof that if operation has inverse then it has neutral element
||| @ prf Proof that operaion has inverse
hasInverseThenHasNeutral: {A: Setoid} -> {op: ClosedBinaryOperation A}
    -> (prf: HasInverse op) -> HasNeutral op
hasInverseThenHasNeutral (MkHasInverse {hasNeutral} _ _ _) = hasNeutral

||| Get inverse function
||| @ prf Proof that operaion has inverse
inverse: {A: Setoid} -> {op: ClosedBinaryOperation A}
    -> (prf: HasInverse op)
    -> Function A A
inverse (MkHasInverse inverse _ _) = inverse

||| Get proof that (inverse x) is left inverse element to x
||| @ prf Proof that operaion has inverse
leftInverse: {A: Setoid} -> {op: ClosedBinaryOperation A}
    -> (prf: HasInverse op)
    -> {x: Carrier A}
        -> Equal A (applyOp op (apply (inverse prf) x) x) (getNeutral (hasInverseThenHasNeutral prf))
leftInverse (MkHasInverse _ left _) = left

||| Get proof that (inverse x) is left inverse element to x
||| @ prf Proof that operaion has inverse
rightInverse: {A: Setoid} -> {op: ClosedBinaryOperation A}
    -> (prf: HasInverse op)
    -> {x: Carrier A}
        -> Equal A (applyOp op x (apply (inverse prf) x)) (getNeutral (hasInverseThenHasNeutral prf))
rightInverse (MkHasInverse _ _ right) = right

||| Proof that closed extensional binary operation is commutative
||| @ op Operation
data IsCommutative: {A: Setoid} -> (op: ClosedBinaryOperation A) -> Type where
    ||| Shows that operation is commutative
    ||| @ commut Proof that operation is `x * y =(A) y * x`
    MkIsCommutative: {A: Setoid} -> {op: ClosedBinaryOperation A}
        -> (commut: {x, y: Carrier A} -> Equal A (applyOp op x y) (applyOp op y x))
        -> IsCommutative op

||| Get proof that operation is `x * y =(A) y * x`
||| @ prf Proof that operation is commutative
commut: {A: Setoid} -> {op: ClosedBinaryOperation A}
    -> (prf: IsCommutative op)
    -> {x, y: Carrier A} -> Equal A (applyOp op x y) (applyOp op y x)
commut (MkIsCommutative prf) = prf

||| Proof that two closed extensional binary operation are distributive
||| @ plus Summation
||| @ mult Multiplication
data IsDistributive: {A: Setoid} -> (plus, mult: ClosedBinaryOperation A) -> Type where
    ||| Shows that two operations are distributive
    ||| @ distributeLeft Proof that mult distributes over plus left
    ||| @ distributeRight Proof that mult distributes over plus right
    MkIsDistributive: {A: Setoid} -> {plus, mult: ClosedBinaryOperation A}
        -> (distributeLeft: {x, y, z: Carrier A}
            -> Equal A (applyOp mult (applyOp plus x y) z) (applyOp plus (applyOp mult x z) (applyOp mult y z))
            )
        -> (distributeRight: {x, y, z: Carrier A}
            -> Equal A (applyOp mult x (applyOp plus y z)) (applyOp plus (applyOp mult x y) (applyOp mult x z))
            )
        -> IsDistributive plus mult

||| Get proof that mult distributes over plus left
||| @ prf Proof that plus and mult are distributive
distributeLeft: {A: Setoid} -> {plus, mult: ClosedBinaryOperation A}
    -> (prf: IsDistributive plus mult)
    -> {x, y, z: Carrier A}
    -> Equal A (applyOp mult (applyOp plus x y) z) (applyOp plus (applyOp mult x z) (applyOp mult y z))
distributeLeft (MkIsDistributive left _) = left

||| Get proof that mult distributes over plus right
||| @ prf Proof that plus and mult are distributive
distributeRight: {A: Setoid} -> {plus, mult: ClosedBinaryOperation A}
    -> (prf: IsDistributive plus mult)
    -> {x, y, z: Carrier A}
    -> Equal A (applyOp mult x (applyOp plus y z)) (applyOp plus (applyOp mult x y) (applyOp mult x z))
distributeRight (MkIsDistributive _ right) = right
