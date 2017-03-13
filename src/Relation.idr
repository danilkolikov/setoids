||| Properties of relations
module Relation

%access public export
%auto_implicits on

||| Type of relation between objects in one set
Relation: Type -> Type
Relation a = a -> a -> Type

||| Shows that relation is reflexive
data IsReflexive: Relation a -> Type where
    MkIsReflexive: (prf: {x: a} -> x `rel` x) -> IsReflexive rel

||| Get proof of reflexy
reflexy: IsReflexive rel -> {x: a} -> x `rel` x
reflexy (MkIsReflexive refl) = refl

||| Shows that relation is antireflexive
data IsAntiReflexive: Relation a -> Type where
    MkIsAntiReflexive: ({x: a} -> Not (x `rel` x)) -> IsAntiReflexive rel

||| Get proof of antireflexy
antiReflexy: IsAntiReflexive rel -> {x: a} -> Not (x `rel` x)
antiReflexy (MkIsAntiReflexive anti) = anti

||| Shows tath relation is symmetric
data IsSymmetric: Relation a -> Type where
    MkIsSymmetric: ({x, y: a} -> x `rel` y -> y `rel` x) -> IsSymmetric rel

||| Get proof of symmetry
symmetry: IsSymmetric rel -> ({x, y: a} -> x `rel` y -> y `rel` x)
symmetry (MkIsSymmetric symm) = symm

||| Shows that relation is transittive
data IsTransittive: Relation a -> Type where
    MkIsTransittive: ({x, y, z: a} -> x `rel` y -> y `rel` z -> x `rel` z) -> IsTransittive rel

||| Get proof of transittivity
transit: IsTransittive rel -> {x, y, z: a} -> x `rel` y -> y `rel` z -> x `rel` z
transit (MkIsTransittive prf) = prf
