# Comonad Duality Guide

Comonads are the categorical dual of Monads: every Comonad on **C** is a Monad on **C^op**.

## Core typeclass (defined in `Comonad/Core.v`)

| Comonad operation | Type | Dual Monad operation |
|---|---|---|
| `extract` | `W a → a` | `return : a → M a` |
| `extend` | `(W a → b) → W a → W b` | `bind : M a → (a → M b) → M b` |
| `duplicate` | `W a → W (W a)` | `join : M (M a) → M a` |

## Comonad laws

```
extend extract        = id
extract ∘ extend f    = f
extend f ∘ extend g   = extend (f ∘ extend g)
```

These are the mirror images of the three monad laws under reversal of morphisms.

## Formal duality

`Comonad/Duality.v` proves `ComonadToDualMonad : Comonad W → Monad (op W)` where `op W` lifts `W` to the opposite category **C^op**.

## Example: Stream comonad

```coq
CoInductive Stream A := Cons : A → Stream A → Stream A.

(* extract = head, duplicate = stream of all tails *)
Instance Stream_Comonad : Comonad Stream := { ... }.
```

## Navigation

- `Core.v` — typeclass definition
- `Duality.v` — formal proof that every Comonad is a Monad on C^op
- `CoKleisli.v` — co-Kleisli category
- `Coalgebra.v` — Coalgebras for a Comonad
- `../Monad/Core.v` — the Monad dual
