module Equality

import public Relation.Preorder
import public Relation

%access public export
%auto_implicits on

||| Equality is reflexive, symmetric and transittive relation
data IsEquality: Relation rel -> Type where
    MkIsEquality:  IsReflexive rel ->
                    IsSymmetric rel ->
                    IsTransittive rel -> IsEquality rel

||| Proof that equality is preorder
equalityIsPreOrder: IsEquality rel -> IsPreOrder rel
equalityIsPreOrder (MkIsEquality refl _ trans) = MkIsPreOrder refl trans
