module Identical

import public Relation.Equality

%access export

||| Proof that built-in equality is equality
identicalIsEquality: IsEquality (=)
identicalIsEquality = MkIsEquality
    (MkIsReflexive Refl)
    (MkIsSymmetric sym)
    (MkIsTransittive trans)
