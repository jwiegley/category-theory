# Axiom audit

A complete enumeration of every `Axiom`, `Parameter`, and
`Conjecture` declaration in the library — what each is, where it
lives, and why it is acceptable in a library that otherwise aims to be
axiom-free.

## Summary

The headline definitions checked by the `print-assumptions` make
target — `Hypergraph`, `PROP`, `Cospan_Hypergraph`,
`DecoratedCospan_Hypergraph`, `spider_collapse`, `spider_frobenius`,
`Hypergraph_CompactClosed`, and `ZX_Cat` — together with the phase
5-17 flagship theorems added to the target and listed under
[How to audit](#how-to-audit) — are reported as CLOSED UNDER THE
GLOBAL CONTEXT (with the sole exception of `ZX_Cat`, which lists the
three `Phase` parameters described below).  This can be verified by

```coq
Require Import Category.Structure.Monoidal.Hypergraph.
Print Assumptions Hypergraph.
(* prints:  Closed under the global context *)
```

and similarly for the other audited definitions.

Read this scope precisely.  "Closed under the global context" is a
statement about a *particular* definition's assumption set; it is NOT
a claim that the library as a whole — every instance, every
construction — is free of stdlib axioms.  It is not.  Several concrete
instance layers do invoke stdlib axioms; these are enumerated in the
[Stdlib axioms](#stdlib-axioms) section below.  See also the
[Caveats](#caveats-what-closed-under-the-global-context-does-and-does-not-establish)
section for what the audit does and does not certify.

The only `Axiom`/`Parameter` declarations in the library are the
`Phase` parameterisation in the ZX-calculus instance — a bare phase
type, a distinguished zero, and a binary addition — which a concrete
user would realise concretely (e.g. as `R / 2π` for the standard ZX
calculus or as `bool` for the Clifford fragment).

## Complete list

All declared in `Instance/ZX.v`:

| Declaration             | Kind       | Type                              | Purpose                                                 |
|-------------------------|------------|-----------------------------------|---------------------------------------------------------|
| `Phase`                 | `Parameter` | `Type`                            | The phase type used to label ZX spiders                 |
| `phase_zero`            | `Parameter` | `Phase`                           | Neutral phase                                           |
| `phase_add`             | `Parameter` | `Phase -> Phase -> Phase`         | Phase addition (used by spider fusion)                  |

That's 3 declarations total: 3 `Parameter`, 0 `Axiom`.  They provide a
bare phase type, a distinguished zero element, and a binary addition
operation.  No algebraic laws are declared on them: there is no
monoid, group, or semiring structure asserted — `phase_add` is not
even claimed to be associative or to have `phase_zero` as a unit.
They are simply the data interface that ZX-calculus is generic over.
Note that [zx_eq] currently compares phases by syntactic equality
only; the standard real-number-mod-2π equivalence and the
corresponding congruence rules are a deliberate omission (see the
header of `Instance/ZX.v` for the full list of missing rules).

A concrete instantiation supplying these (e.g. `Phase := R`,
`phase_add := Rplus`, `phase_zero := 0`) reduces them all to standard
Coq stdlib facts.

## Caveats: what "Closed under the global context" does and does not establish

The audit conflates two genuinely different situations, and it is
important to keep them apart.

1. **Axiom-free AND inhabited by a concrete model.**  Here a "Closed
   under the global context" report certifies a result about something
   the library actually contains.  The genuine example is
   `classifier_classifies`: it is proven for any `ElementaryTopos`, and
   the library exhibits one — `FinSet_Topos : ElementaryTopos FinSet`
   in `Instance/FinSet/Topos.v` — whose sanity examples compute by
   `eq_refl` (for instance `Pow 2 = 4`).  A full ledger of which
   headline results carry an in-tree witness and which are
   conditional-only is kept in [INHABITATION.md](INHABITATION.md).

   Note that `Cospan_Hypergraph` is **not** such an example, despite
   earlier editions of this file presenting it as one.  Feeding it the
   only `HasPushouts` instance in the tree, `Sets_HasPushouts`, does
   not type-check: a cospan's hom carries an apex object, so `CospanCat`
   requires objects to sit at or below homs, whereas `Sets` places its
   objects one universe above its homs, and `CospanCat Sets HP` reports
   a universe inconsistency for any `HP`.  The route that fits is
   skeletal `FinSet`; see the cospan note in
   [INHABITATION.md](INHABITATION.md).

2. **Axiom-free *as written*, but not yet instantiated.**  `Hypergraph`
   is a `Class : Type` declaration, and `DecoratedCospan_Hypergraph`
   is a `Program Definition` living under a section `Context`
   `{DCHGC : DecCospan_Hypergraph_Coherent}` whose coherence class is
   NEVER instantiated anywhere in the library (there is no inhabitant
   of `DecCospan_Hypergraph_Coherent` or of `HypergraphPROP`).  For
   these, "Closed under the global context" is trivially or vacuously
   true and certifies no concrete result.  (`PROP` itself, by contrast,
   IS inhabited — by `FreePROP`, `PresentedPROP`, `Lawvere_PROP`, and
   `RepeatPROP` — so it is not in this list.)

   Running `Print Assumptions` on a `Class` *type* reports the
   assumptions of the type expression, not of any inhabitant — a type
   has no proof content to depend on axioms.  Likewise, a definition
   quantified over an uninstantiated section hypothesis reports
   "Closed" only because that hypothesis is lambda-bound: the
   assumption is discharged into the definition's own signature rather
   than satisfied.  In neither case does the audit establish that any
   inhabitant exists.

## How to audit

Run

```bash
make print-assumptions
```

This (re-)builds the library and prints the assumption set of the
following specific definitions:

- `Hypergraph`
- `PROP`
- `Cospan_Hypergraph`
- `DecoratedCospan_Hypergraph`
- `spider_collapse`
- `spider_frobenius`
- `Hypergraph_CompactClosed`
- `ZX_Cat`

The audit target was extended to also cover the phase 5-17 flagship
theorems, each stated parametrically over abstract structure and
each reported "Closed under the global context":

- `lambek` (`Theory/Lambek.v`) — Lambek's lemma
- `GAFT` (`Adjunction/GAFT.v`) — the general adjoint functor theorem
- `beck_monadicity` and `monadic_creates`
  (`Monad/Monadicity/Beck.v`) — Beck's precise monadicity theorem
- `RoundTrip_Equivalence` (`Construction/Grothendieck/RoundTrip.v`) —
  the fibred/indexed round-trip equivalence
- `markov_all_deterministic_iff_cartesian`
  (`Structure/Monoidal/Markov/Fox.v`) — Fox's theorem
- `classifier_classifies` (`Structure/SubobjectClassifier.v`) — the
  subobject classification theorem
- `relations_iso` (`Structure/Topos.v`) — the power-object relations
  isomorphism
- `mate_iso` (`Theory/Bicategory/Mates.v`) — the mates bijection
- `image_mediator_epic` (`Structure/Abelian.v`) — the abelian
  epi-mono factorization mediator

Expected output: "Closed under the global context" for each, except
`ZX_Cat`, which lists the 3 `Phase` parameters above.  This is the
assumption set of these specific headline definitions only — it is not
a claim about every definition in the library.  Read it together with
the [Caveats](#caveats-what-closed-under-the-global-context-does-and-does-not-establish)
above: several of these definitions are class types or conditional
constructions that are axiom-free without yet being inhabited.

## Stdlib axioms

The audited core definitions listed under [How to audit](#how-to-audit)
— the ones the `print-assumptions` make target checks — are "Closed
under the global context" and invoke none of the following stdlib
axioms:

- `proof_irrelevance`
- `functional_extensionality` (in any form)
- `propositional_extensionality`
- `JMeq_eq`
- `classic` (excluded middle)
- `dependent_choice`
- `unique_choice`

This freedom is scoped to those audited definitions; it is NOT a
library-wide guarantee.  Several concrete instance layers DO invoke
some of these stdlib axioms, and a `Print Assumptions` on a definition
that depends on them will report the axiom rather than "Closed under
the global context".  Known live uses:

- **`functional_extensionality_dep`** — the cartesian-closed /
  exponential structure on `Instance/Coq` depends on it (verify:
  `Print Assumptions Coq_Closed` lists
  `FunctionalExtensionality.functional_extensionality_dep`).  The
  `Instance/Lambda.*` development depends on it as well (verify:
  `Print Assumptions Category.Instance.Lambda.Lambda`).
  `Instance/Comp.v` also applies `functional_extensionality` /
  `functional_extensionality_dep` directly, and
  `Theory/Coq/Functor/Proofs.v` uses the `extensionality` tactic.
- **UIP / `Eqdep` (`inj_pair2`, `eq_rect_eq`)** — `Instance/Lambda.v`
  and its tactic support `Instance/Lambda/Ltac.v` rely on UIP for
  index types (injectivity of `existT` via `Coq.Logic.Eqdep`).
  `Instance/Shapes.v` likewise depends on `eq_rect_eq` (verify:
  `Print Assumptions Category.Instance.Shapes.Tries_Cartesian`).

Two entries that earlier editions of this table listed are *not* live
uses, and are corrected here:

- `proof_irrelevance` is invoked **nowhere** in the compiled library.
  Its only textual occurrences are in `Instance/Rel.v` (around lines
  137–156), and that whole region sits inside a comment block, so
  `Print Assumptions Category.Instance.Rel.Rel` reports "Closed under
  the global context".
- `Instance/Sets/Par.v` uses the `extensionality` tactic only inside
  proofs that end in `Abort.`, so those uses never enter the
  environment; the file introduces no axiom on that account.

So if you `Require Import` and build on these instance layers — or on
files from `Coq.Logic.*` more generally — those axioms become part of
your development's assumption set.  The point is that the audited core
definitions above stay free of them; the library as a whole does not.

## Adding new axioms

The design intent is to keep the audited core definitions free of
`Axiom`/`Parameter` declarations apart from the ZX `Phase`
parameters (the bare phase type, zero, and addition above).  If you
add a new `Axiom` or `Parameter` in a contribution:

1. Document it in this file under a clearly-marked new heading.
2. Justify why it's acceptable (e.g. "interface to user-supplied
   semantic primitive") or why it can't be eliminated.
3. Add a corresponding `Print Assumptions` invocation to the
   `print-assumptions` make target so the addition shows up in audit
   output.

## Note: the former version-conditional obligation

`Structure/UniversalProperty/Universal/Arrow.v` (in
`UniversalArrowIsUniversalProperty`) once carried a single obligation
discharged only by a version-conditional tactic, with a trailing
`admit` reached on Coq versions below 8.16.  That obligation is now
proven directly, so the file contains no proof hole on any supported
version; `Print Assumptions UniversalArrowIsUniversalProperty` reports
"Closed under the global context".  The module remains an orphan — no
other file in the library depends on it — so it stands outside the
audited core in any case.
