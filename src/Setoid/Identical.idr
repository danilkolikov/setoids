module Identical

import public Setoid
import public Relation.Equality.Identical

%access public export

||| Identical Setoid uses `identical` relation
||| Two objects here are equal is they are identical
identicalSetoid: Type -> Setoid
identicalSetoid a = MkSetoid
    a
    (=)
    identicalIsEquality
