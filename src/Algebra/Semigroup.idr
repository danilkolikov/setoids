module Semigroup

import BinaryOperation

%access public export

||| Semigroup is setoid with associative closed binary operation
record Semigroup where
    constructor MkSemigroup
    setoid: Setoid
    op: ClosedBinaryOperation setoid
    isAssociative: IsAssociative op
