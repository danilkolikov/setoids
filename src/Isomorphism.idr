module Isomorphism

import public Setoid
import public Setoid.Identical
import public Function

%access public export

%auto_implicits off

||| Setoids A and B are ismorphic when A is part of B and B is part of A
|||
||| It means that there is such functions (A -> B) and (B -> A) that
||| their composition is identity function
record Isomorphism (A: Setoid) (B: Setoid) where
    ||| Constructor
    constructor MkIsomorphism

    ||| Transform A to B
    to: Function A B

    ||| Get A from B
    from: Function B A

    ||| Proof that `to . from === id`
    toFrom: (to `compose` from) `FunctionEquality` identity

    ||| Proof that `from . to === id`
    fromTo: (from `compose` to) `FunctionEquality` identity

||| Factorization of Setoid is isomorphism between setoid and factor-set
||| by Setoid's equivalence relation, equiped with Identical relation
Factorization: (A: Setoid) -> (B: Type) -> Type
Factorization A B = Isomorphism A (identicalSetoid B)
