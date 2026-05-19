# Axiom audit

A complete enumeration of every `Axiom`, `Parameter`, and
`Conjecture` declaration in the library — what each is, where it
lives, and why it is acceptable in a library that otherwise aims to be
axiom-free.

## Summary

The library's CORE definitions — `Category`, `Functor`, `Monoidal`,
`Symmetric`, `Hypergraph`, `CompactClosed`, `Cospan_Hypergraph`,
`PROP`, and everything they transitively depend on — are CLOSED UNDER
THE GLOBAL CONTEXT.  They use no axioms whatsoever.  This can be
verified by

```coq
Require Import Category.Structure.Monoidal.Hypergraph.
Print Assumptions Hypergraph.
(* prints:  Closed under the global context *)
```

and similarly for `PROP`, `Cospan_Hypergraph`,
`DecoratedCospan_Hypergraph`, etc.

The ONLY axioms in the library are the `Phase` parameterisation in
the ZX-calculus instance, where they are explicit "you supply the
phase semiring" declarations that any concrete user would
realise concretely (e.g. as `R / 2π` for the standard ZX calculus or
as `bool` for the Clifford fragment).

## Complete list

All declared in `Instance/ZX.v`:

| Declaration             | Kind       | Type                              | Purpose                                                 |
|-------------------------|------------|-----------------------------------|---------------------------------------------------------|
| `Phase`                 | `Parameter` | `Type`                            | The phase type used to label ZX spiders                 |
| `phase_zero`            | `Parameter` | `Phase`                           | Neutral phase                                           |
| `phase_add`             | `Parameter` | `Phase -> Phase -> Phase`         | Phase addition (used by spider fusion)                  |

That's 3 declarations total: 3 `Parameter`, 0 `Axiom`.  All three say
"you supply the phase type and a binary phase-addition operation" —
they are the algebraic interface that ZX-calculus is generic over.
Note that [zx_eq] currently compares phases by syntactic equality
only; the standard real-number-mod-2π equivalence and the
corresponding congruence rules are a deliberate omission (see the
header of `Instance/ZX.v` for the full list of missing rules).

A concrete instantiation discharging these (e.g. `Phase := R`,
`phase_add := Rplus`, `phase_zero := 0`) reduces them all to standard
Coq stdlib facts.

## How to audit

Run

```bash
make print-assumptions
```

This (re-)builds the library and prints the assumption-set of every
top-level definition in
`Category.Structure.Monoidal.Hypergraph`,
`Category.Construction.PROP`,
`Category.Construction.Cospan.HypergraphInstance`,
`Category.Construction.DecoratedCospan.Hypergraph`,
`Category.Structure.Monoidal.Hypergraph.Spider`.

Expected output: "Closed under the global context" for each, except
ZX-instance definitions (which list the 3 phase parameters above).

## Stdlib axioms

The library does NOT depend on any of the following stdlib axioms:

- `proof_irrelevance`
- `functional_extensionality` (in any form)
- `propositional_extensionality`
- `JMeq_eq`
- `classic` (excluded middle)
- `dependent_choice`
- `unique_choice`

If you `Require Import` files from `Coq.Logic.*` (most commonly to
get `eq_rect_eq`), those axioms become available to YOUR code but the
library itself never invokes them.

## Adding new axioms

The library's design intent is to remain axiom-free apart from the
ZX `Phase` semiring.  If you add a new `Axiom` or `Parameter` in a
contribution:

1. Document it in this file under a clearly-marked new heading.
2. Justify why it's acceptable (e.g. "interface to user-supplied
   semantic primitive") or why it can't be eliminated.
3. Add a corresponding `Print Assumptions` invocation to the
   `print-assumptions` make target so the addition shows up in audit
   output.
