# Setoids - Idris proofs for extensional equalities

Motivation of these proofs is next - only two identical objects can be equal in Idris, and it usually complicates other proofs.
For example, we can think about Integer numbers as about pairs of two natural numbers `(a, b)`:
```idris
X = a - b
```
Then two integer numbers `(a, b)` and `(c, d)` will be equal when
```idris
a + d = c + b
```
Such representation simplifies proofs of theorems for integer numbers, but two pairs can be not identical when corresponding integers are equal.
And for overcome that difficulty we can use Setoids - sets with extensionally defined equality.  

## Contents

- Algebraic structures - Semigroup, Monoid, Semiring, ...
- Setoids - Natural numbers, built-in setoid
- Extensional functions
- Properties of relations and binary operations

## Installation & Usage

To install `setoids` package, you should:

1. Clone repository to folder
2. Run `idris --install setoids.ipkg`

To use proofs and types from `setoids` in files import them as default modules and start Idris with command
```
idris -p setoids %FILE_NAME%
```
To use modules from  `setoids` in REPL, import them using `:module` command
