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
5-17 flagship theorems and the further definitions added to the target,
all listed under [How to audit](#how-to-audit) — are reported as CLOSED UNDER THE
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

   Note that feeding `Cospan_Hypergraph` the `Sets` pushout instance
   `Sets_HasPushouts`, as earlier editions of this file suggested, does
   not type-check: a cospan's hom carries an apex object, so `CospanCat`
   requires objects to sit at or below homs, whereas `Sets` places its
   objects one universe above its homs, and `CospanCat Sets HP` reports
   a universe inconsistency for any `HP`.  The route that fits is
   skeletal `FinSet`, and `FinSet_HasPushouts`
   (`Instance/FinSet/Pushout.v`) supplies it: over `FinSet` the cospan
   hypergraph and both spider results are inhabited and axiom-free.  See
   the cospan note in [INHABITATION.md](INHABITATION.md).

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

   `CreatesLimit` is likewise a `Class` type, so its entry in the audit
   certifies nothing on its own; the inhabitant to read alongside it is
   `em_forget_CreatesAllLimits`, which is audited here too, and the
   fully concrete instantiation at `Id_Monad` over `Coq` recorded in
   [INHABITATION.md](INHABITATION.md).

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
- `CreatesLimit`, `creation_preserves_limit` and
  `creates_limits_Complete` (`Structure/Limit/Creation.v`) — creation
  of limits and Mac Lane's §V.4 Theorem 2
- `em_forget_CreatesAllLimits` and `EM_Complete`
  (`Monad/Eilenberg/Moore/Limit.v`) — limits of algebras are
  computed on carriers

The skeleton development (Mac Lane §IV.4) adds:

- `skeleton_inclusion_is_equivalence`, `skeletons_are_isomorphic`,
  `skeletons_isomorphic_iff_equivalent`, `skeletal_equivalence_is_isomorphism`,
  `skeleton0_skeletal_forces_UIP` (`Theory/Skeleton.v`)
- `skeletality_is_not_equivalence_invariant` (`Theory/Skeleton/Separation.v`)
- `FinSet_Skeletal` (`Instance/FinSet/Skeleton.v`)
- `Proset_Skeletal_iff_Antisymmetric` (`Instance/Proset/Skeletal.v`)

The target further covers the Mac Lane exercise layer — the category of
groups, and the fixed-factor product functor built over it.  These sit
outside the `Theory/`/`Structure/`/`Construction/` scope in which the
library's zero-axiom claim holds: `Instance/Grp.v` is squarely in the
instance layer, which *is* permitted stdlib axioms, and
`Functor/Product/Fixed.v` is a `Functor/` file that depends on it.  The
definitions below are audited precisely because, permission
notwithstanding, each of them turns out to need no axiom at all.  This
is a claim about these named definitions, not about every definition in
either file:

- `Grp`, `Grp_Forget`, `Grp_Zero` (`Instance/Grp.v`) — the category of
  groups, its underlying-set functor, and its zero object
- `fixed_product_functor`, `fixed_product_transform`,
  `fixed_product_transform_faithful`, `alt_transform`,
  `alt_is_inj_left` (`Functor/Product/Fixed.v`) — the fixed-factor
  product functor `H × −`, the induced transformation `H × − ⟹ K × −`,
  its faithfulness in `f`, the `split f id` spelling of the component,
  and its agreement on the nose with the binoidal composite the tree
  already reaches
- `Grp_fixed_product`, `Grp_fixed_product_transform`,
  `Grp_fixed_product_transform_not_id`, `Grp_Z2_zero_not_iso`
  (`Functor/Product/Fixed.v`) — the same two constructions instantiated
  at `Grp`, together with the two non-vacuity witnesses at `Z/2`
- `Exp_Functor`, `eval_natural`, `Curry_Adjunction`,
  `Curry_Representable` (`Structure/Cartesian/Closed/Adjunction.v`) —
  the currying adjunction `(− × S) ⊣ (−)^S` with `eval` as counit, and
  the representation of `C(− × S, B)` by `B^S`
- `Conjugate`, `conjugate_characterizations` and `conjugate_bijection`
  (`Adjunction/Conjugate.v`) — Mac Lane §IV.7 conjugate natural
  transformations: the hom-set square, its four equivalent
  characterizations, and the conjugation bijection

The target also covers the Mac Lane I.3 witnesses — two functors with
the same object function and different arrow functions — each likewise
"Closed under the global context":

- `S3_two_functors_distinct` and `S3_two_functors_weakly_equal`
  (`Instance/Grp/TwoFunctors.v`) — the strict separation, and the weak
  (natural-isomorphism) identification, of the conjugation-twisted pair
  over the full subcategory of `Grp` on the symmetric group S3
- `Grp_op_twist_is_Id` (`Instance/Grp/TwoFunctors.v`) — the collapse of
  the inversion twist of the whole of `Grp`, which is why that uniform
  candidate does not separate anything
- `free_two_functors_distinct` (`Construction/Free/TwoFunctors.v`) —
  the group-free witness of Fong and Spivak's Exercise 3.40

The target additionally audits three CONCRETE results (not parametric
over abstract structure, and belonging to no numbered phase), because
they are the headline statements of the preorder-transformation
development:

- `proset_transform_iff` and `proset_transform_unique`
  (`Instance/Proset/Transform.v`) — existence and uniqueness of a
  natural transformation into a preorder (Mac Lane §I.4, exercise 4)
- `proset_out_not_unique` (`Instance/Proset/Transform.v`) — the
  refutation of the dual: two distinct transformations *out of* a
  preorder

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
- **The standard-library reals (`ClassicalDedekindReals.sig_forall_dec`,
  `ClassicalDedekindReals.sig_not_dec`,
  `FunctionalExtensionality.functional_extensionality_dep`)** —
  `Instance/Top/Interval.v` builds the unit interval `[0,1]` and the
  unit square out of `Coq.Reals`,
  `Instance/Top/FundamentalGroupoid.v` builds the fundamental groupoid
  on them, and `Instance/Top/Presheaf.v` builds the real line `R_Top`
  and the presheaf of continuous real-valued functions on it.  These
  are the only three files in the tree that import the reals (verify:
  `rg -l 'Coq.Reals' --glob '*.v' .`), and none declares an axiom of
  its own; what they inherit is the axiom set of the standard
  library's own construction of `R`.  The cost splits in two, and both
  halves are measured rather than estimated:

  - `π(X)` itself, its groupoid structure and the base-point
    corollary carry **two** axioms — `sig_forall_dec` and
    `functional_extensionality_dep` (verify:
    `Print Assumptions Category.Instance.Top.FundamentalGroupoid.FundamentalGroupoid`,
    and likewise for `fundamental_groupoid_is_groupoid` and
    `fundamental_group_basepoint_independent`).
  - The results that go through the least-upper-bound property
    (`Raxioms.completeness`) carry a **third**, `sig_not_dec`.
    `Print Assumptions` was run over every constant of both files,
    and this third axiom is carried by exactly **eight** of them, all
    in `Instance/Top/FundamentalGroupoid.v` and none in
    `Instance/Top/Interval.v`:

    | constant | role |
    |---|---|
    | `gval_endpoints` | the least-upper-bound argument itself |
    | `f_endpoints` | its endpoint corollary |
    | `interval_to_discrete_constant_dec` | the theorem they establish: every continuous map from `[0,1]` into a discrete space with decidable equality is constant |
    | `interval_to_discrete_constant` | that theorem at the two-point discrete space |
    | `no_path_true_false` | non-vacuity: the discrete witness |
    | `Bool_Discrete_not_pathconnected` | " |
    | `Bool_Discrete_pi_not_connected` | " |
    | `Bool_Discrete_loops_trivial` | " |

    Verify any of them with, e.g.,
    `Print Assumptions Category.Instance.Top.FundamentalGroupoid.interval_to_discrete_constant`.

  **The per-file split, measured per constant.**  Each constant of all
  three files of that development was measured individually — no class
  was inferred from a headline, and nothing was sampled.

  `Instance/Top/FundamentalGroupoid.v` has **113** constants: the 108
  recorded in its `.glob` file, together with the five Program
  obligations `FundamentalGroupoid_obligation_1` .. `_5` that the
  `Program Definition` of π(X) generates and that no `.glob` sweep
  sees.  They split

  | count | assumption set | which |
  |---|---|---|
  | 1 | closed under the global context | `bool_carriers_agree` |
  | 1 | `sig_forall_dec` only | `const_arrow_eval` |
  | 103 | the two | 98 glob-recorded constants and all five obligations |
  | 8 | the three | the table above |

  `Instance/Top/Interval.v` has **160** constants and no Program
  obligations.  They split

  | count | assumption set | which |
  |---|---|---|
  | 1 | closed under the global context | `rf_id` |
  | 34 | `sig_forall_dec` only | the 34 named below |
  | 125 | the two | all the rest |
  | 0 | the three | — |

  The 34 that carry `sig_forall_dec` alone, in full, are
  `BallSpace`, `ball_carrier`, `bdist`, `bdist_zero`, `bdist_sym`,
  `bdist_tri`, `ball_open`, `ball_respects`, `ball_proper`,
  `ball_union`, `bs_fst`, `bs_snd`, `BSprod_Object`, `BSprod_Setoid`,
  `BSprod_equiv`, `BSprod_equiv_Equivalence`, `BSprod_pt`, `hfun`,
  `Ipt`, `Ipt_Object`, `Ipt_Setoid`, `Ipt_equiv`,
  `Ipt_equiv_Equivalence`, `ipt_lo`, `ipt_hi`, `ival`, `ival_I_zero`,
  `ival_I_one`, `I_point`, `I_rev_eval`, `rf_zero`, `rf_rev`,
  `sq_pt_s` and `sq_pt_t`.

  `Instance/Top/Presheaf.v` has **54** constants: the 36 recorded in
  its `.glob` file together with the 18 Program obligations of its six
  `Program` definitions.  They split

  | count | assumption set | which |
  |---|---|---|
  | 33 | closed under the global context | the open-subspace machinery — `SubCar` through `sub_map`, the subspace-topology correspondence (`sub_ext_contained`, `sub_ext_recovers`, `sub_open_of_open`, `sub_ext_of_open`), `whole_open` and `OpenSub_whole_iso`, obligations included — and the setoid packaging of `R` (`R_equiv`, `R_equiv_Equivalence`, `R_Setoid`, `R_Object`), which names the type but computes nothing with it |
  | 21 | the two | everything that computes with `R`: `BS_R_zero`, `BS_R_sym`, `BS_R_tri`, `BS_R`, `R_Top`, `SectionsOb`, `ContinuousPresheaf`, `const_section`, `const_restrict`, `Maps_to_R`, `global_sections_iso`, obligations included |
  | 0 | `sig_forall_dec` alone, or the three | — |

  In particular nothing in the file goes through the least-upper-bound
  property, so `sig_not_dec` is not incurred, and the open-subspace
  topology (design note 1 of the file's header) is axiom-free — it is
  the 21 real-computing constants, not the subspace machinery, that
  price Mac Lane's example.

  An earlier edition of this section said the remaining constants of
  each file carried "exactly the two"; for the 34 above and for
  `const_arrow_eval` that is false.  The direction of the error was to
  over-report the cost, so nothing that rested on it was unsound, but
  it was a figure inferred rather than measured and it is corrected
  here.

  The purely categorical part of that development, the base-point
  independence theorem for connected groupoids in
  `Structure/Groupoid/Basepoint.v`, imports no reals: all **27** of its
  constants report "Closed under the global context" (verify:
  `Print Assumptions Category.Structure.Groupoid.Basepoint.connected_vertex_moniso`),
  and because they do, that file *is* wired into the
  `print-assumptions` make target, alongside its `Structure/Groupoid`
  siblings.  The three files that import the reals are not: that target
  permits only the three ZX `Phase` parameters, and the instance-layer
  stdlib axioms listed in this section are documented here instead,
  exactly as the `Instance/Coq` and `Instance/Lambda` entries above
  are.

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
