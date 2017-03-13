module Setoid

import public Relation.Equality

%access public export

||| Setoid is a set with existential equality predicate on it
||| and proof that this predicate in equaivalence
record Setoid where
    constructor MkSetoid
    Carrier: Type
    Equal: Carrier -> Carrier -> Type
    isEquality: IsEquality Equal
