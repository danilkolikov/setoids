||| Module with definition and basic properties of extensional n-ary operations
module Operation

import public Data.Fun
import public Data.Vect
import public Setoid

%access public export
%default total

using (arity : Nat)
    ConstructCongruenceTy : (argsTys : Vect arity Setoid) -> (resTy : Setoid) -> Fun (map Carrier argsTys) (Carrier resTy) -> Type
    ConstructCongruenceTy argsTys resTy f = go argsTys f f where
        go : (argsTys : Vect arity Setoid) -> (f, g : Fun (map Carrier argsTys) (Carrier resTy)) -> Type
        go [] v u = Equal resTy v u
        go (ty :: tys) f g = {x, y : Carrier ty} -> Equal ty x y -> go tys (f x) (g y)

    record Operation (argsTys : Vect arity Setoid) (resTy : Setoid) where
        constructor MkOperation
        ApplyOp : Fun (map Carrier argsTys) (Carrier resTy)
        Congruence : ConstructCongruenceTy argsTys resTy ApplyOp

ClosedOperation : (arity : Nat) -> (ty : Setoid) -> Type
ClosedOperation arity ty = Operation (replicate arity ty) ty
