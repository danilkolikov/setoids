||| Module with definition of extensional function
module Function

import public Setoid

%access public export

||| Extensional function. It's domain and codomain are setoids, and it
||| preserves congruence
||| @ A Domain setoid
||| @ B Codomain setoid
data Function: (A, B: Setoid) -> Type where
    ||| Constructs extensional function
    ||| @ apply Application of function
    ||| @ congruence Proof that if `x =(A) y` then `apply(x) =(B) apply(y)`
    MkFunction: {A, B: Setoid}
        -> (apply: Carrier A -> Carrier B)
        -> (congruence: {x, y: Carrier A}
            -> Equal A x y
            -> Equal B (apply x) (apply y)
            )
        -> Function A B

||| Apply extensional function
||| @ f Extensional function
||| @ x Argument
apply: {A, B: Setoid} -> (f: Function A B) -> (x: Carrier A) -> Carrier B
apply (MkFunction ap _) = ap

||| Get proof that extensional function is congruent
||| @ f Extensional function
congruence: {A, B: Setoid} -> (f: Function A B) ->
    ({x, y: Carrier A} -> Equal A x y -> Equal B (apply f x) (apply f y))
congruence (MkFunction _ cong) = cong

||| Composition of setoid functions is setoid function
||| @ left Left operand
||| @ right Right operand
compose: {A, B, C: Setoid} -> (left: Function A B) -> (right: Function B C) -> Function A C
compose (MkFunction f congF) (MkFunction g congG) = MkFunction
    (g . f)
    (congG . congF)

||| Identity setoid function
||| @ A domain and codomain of Identity function
identity: {A: Setoid} -> Function A A
identity = MkFunction id (\prf => prf)

||| Equality between two extensonal functions of same domain and codomain.
||| Such functions are equal if they are equal for any argument
||| @ A Domain setoid
||| @ B Codomain setoid
||| @ f Left side of equality
||| @ g Right side of equality
data FunctionEquality: {A, B: Setoid} -> (f, g: Function A B) -> Type where
    ||| Constructs equality of two setoid functions
    ||| @ prf Proof of the fact that for any x `f(x) =(B) g(x)`
    MkFunctionEquality: {A, B: Setoid} -> {f, g: Function A B}
                    -> (prf: {x: Carrier A} -> Equal B (apply f x) (apply g x))
                    -> FunctionEquality f g

||| Proof that defined equality of extensional functions is indeed equality
functionEqualityIsEquality: {a, b: Setoid} -> IsEquality (FunctionEquality {A = a} {B = b})
functionEqualityIsEquality {a} {b} with (b)
    | (MkSetoid _ _ (MkIsEquality (MkIsReflexive reflB) (MkIsSymmetric symB) (MkIsTransittive transB)))
    = MkIsEquality
        (MkIsReflexive $ MkFunctionEquality $ reflB)
        (MkIsSymmetric $ \(MkFunctionEquality prf)
            => MkFunctionEquality $ symB prf)
        (MkIsTransittive $ \ (MkFunctionEquality left), (MkFunctionEquality right)
            => MkFunctionEquality $ transB left right)

||| Setoid of extensional functions between two setoids
||| @ A Domain of functions
||| @ B Codomain of functions
FunctionSetoid: (A, B: Setoid) -> Setoid
FunctionSetoid a b = MkSetoid
    (Function a b)
    FunctionEquality
    functionEqualityIsEquality

--- Proofs ---

||| Proof that composition of SetoidFunctions is application of corresponding functions
compositionIsApplication: {A, B, C: Setoid}
    -> (F: Function A B)
    -> (G: Function B C)
    -> {x: Carrier A}
    -> Equal C (apply (F `compose` G) x) (apply G $ apply F x)
compositionIsApplication
    {C=(MkSetoid _ _ (MkIsEquality refl _ _))}
    (MkFunction f _)
    (MkFunction g _)
    {x} = reflexy refl {x=g $ f x}

||| Proof that composition of SetoidFunctions is associative
composeIsAssociative: {a, b, c, d: Setoid} ->
    {f: Function a b} -> {g: Function b c} -> {h: Function c d} ->
    FunctionEquality (f `compose` (g `compose` h)) ((f `compose` g) `compose` h)
composeIsAssociative
    {a} {b} {c} {d=d@(MkSetoid t eq (MkIsEquality r isSymm isTrans))}
    {f} {g} {h} = MkFunctionEquality qed
    where
        D: Setoid
        D = (MkSetoid t eq (MkIsEquality r isSymm isTrans))

        -- It can be done in smaller amount of steps, but it's easier to
        -- understand proof if it has many steps

        step_1: {x: Carrier a}
            -> Equal c (apply (f `compose` g) x) (apply g (apply f x))
        step_1 = compositionIsApplication f g

        step_2: {x: Carrier a}
            -> Equal D (apply h (apply (f `compose` g) x)) (apply h (apply g (apply f x)))
        step_2 = congruence h step_1

        step_3: {x: Carrier a}
            -> Equal D (apply ((f `compose` g) `compose` h) x) (apply h (apply (f `compose` g) x))
        step_3 = compositionIsApplication (f `compose` g) h

        step_4: {x: Carrier a}
            -> Equal D (apply ((f `compose` g) `compose` h) x) (apply h (apply g (apply f x)))
        step_4 = transit isTrans step_3 step_2

        step_5: {x: Carrier a}
            -> Equal D (apply (g `compose` h) (apply f x)) (apply h (apply g (apply f x)))
        step_5 = compositionIsApplication g h

        step_6: {x: Carrier a}
            -> Equal D (apply (f `compose` (g `compose` h)) x) (apply (g `compose` h) (apply f x))
        step_6 = compositionIsApplication f (g `compose` h)

        step_7: {x: Carrier a}
            -> Equal D (apply (f `compose` (g `compose` h)) x) (apply h (apply g (apply f x)))
        step_7 = transit isTrans step_6 step_5

        qed: {x: Carrier a}
            -> Equal D (apply (f `compose` (g `compose` h)) x) (apply ((f `compose` g) `compose` h) x)
        qed = transit isTrans step_7 $ symmetry isSymm step_4

%auto_implicits off

||| Proof that identityFun is left identity for composition
identityIsLeftIdentity: {a, b: Setoid} -> {f: Function a b}
    -> FunctionEquality (compose identity f) f
identityIsLeftIdentity
    {a=(MkSetoid _ _ (MkIsEquality (MkIsReflexive refl) _ _))}
    {b}
    {f=f@(MkFunction _ _)} =
        MkFunctionEquality $ congruence f refl

||| Proof that identityFun is right identity for composition
identityIsRightIdentity: {a, b: Setoid} -> {f: Function a b}
    -> FunctionEquality (f `compose` identity) f
identityIsRightIdentity
    {a}
    {b=(MkSetoid _ _ (MkIsEquality (MkIsReflexive refl) _ _))}
    {f=(MkFunction _ _)}
    = MkFunctionEquality refl

%auto_implicits on
