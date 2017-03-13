module Preorder

import public Relation

%access public export
%auto_implicits on

||| Preorder is reflexive and transittive relation
data IsPreOrder: Relation rel -> Type where
    MkIsPreOrder: IsReflexive rel -> IsTransittive rel -> IsPreOrder rel
