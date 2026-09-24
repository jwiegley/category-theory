Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.Representability.

Generalizable All Variables.

(** * The representability theorem

    Mac Lane §V.6 Theorem 3 and Definition 3 (book p. 122,
    `maclane:V.6:thm3`, `maclane:V.6:def3`) with §V.8 Exercise 1 (book
    p. 131) and Riehl's 4.7.14, over `Sets`-valued functors: a functor
    [K : C ⟶ Sets] on a complete category that preserves limits and
    satisfies the solution set condition is REPRESENTABLE, and conversely.
    A satellite of Adjunction/Representability.v (#348) rather than an
    extension of it: the ingredients here are GAFT's and the hom-functor
    continuity of #428, and requiring them in the parent would take the
    closure every downstream consumer of #348's biconditional pays from 40
    modules to about 95.

    DEFINITION 3, and why the tree already had half of it.
    [ElementSolutionSet K] is the book's element-wise form — a [Type] of
    indices, an object and an ELEMENT of [K] at each, and a factorization
    of every element of every [K c] through one of them.  Adjunction/GAFT.v
    's [SolutionSet U d] is the hom-shaped form, and the two agree at the
    singleton: [sols_of_esols] and [esols_of_sols] pass between them,
    keeping index, objects and elements on the nose (four [eq_refl]
    readbacks).  The passage rests on elements being global points, which
    is Theory/Universal/Element.v's [global_elements_iso] — the issue
    asks for that bridge to be proved as a "reusable lemma"; it has existed
    since #318 and nothing here re-proves it.  The two records are NOT
    convertible, only inter-derivable (probe N1).

    THEOREM 3.  A representation is a universal element, hence an initial
    object of the category of elements, which Construction/Elements.v
    presents as the comma category [=(1) ↓ K]; GAFT's own machinery turns a
    solution set there into that initial object.  That step was sealed
    inside [GAFT]'s [Qed], so this issue exports it as
    Adjunction/GAFT.v's [comma_initial_of_sols] (appended at that file's
    end — every line above it stays put, eleven external citations pointing
    into it — with [GAFT_via_comma_initial] re-deriving GAFT from
    it as a cross-check that it IS the same step; the theorem itself is not
    rewritten to use it).  [representability_theorem] is then four existing
    constants composed with no tactic, and [representability_iff] adds the
    converse: a representable functor preserves limits
    ([continuous_of_representable], through Functor/Hom/Continuous.v's
    [representable_iso_ContinuousFunctor] — the #428 leg the issue does not
    name) and supplies its own element-wise solution set, the single object
    being the representing one and the single element the identity read
    across the isomorphism.

    §V.8 EXERCISE 1.  Forward: [HomAfter K 1] IS [Hom(1,−) ◯ K] on the nose
    (readback), global points make it [K] up to [homafter_one_iso] — NOT on
    the nose (probe N2) — so #348's [adj_representable] at the singleton
    transports onto [K], and [representable_of_left_adjoint] returns the
    left adjoint at the singleton as its representing object ([eq_refl]).
    Riehl 4.7.14 is the same passage after SAFT: [saft_representable].
    (CORRECTION, #451: the same passage over Adjunction/SAFT.v's premises,
    which are not Riehl's.  Its [cover] premise is refutable at
    [K := Id[Sets]] -- Adjunction/SAFT/Sets.v's
    [SubobjectCover_Id_Sets_absurd], at every [Sets@{o _}] with
    [Set < o] -- a functor that Riehl's hypotheses cover and that
    [Sets_Id_repr] below represents, so [saft_representable] never
    applies there.)  (Since #453: superseded, and kept.
    Adjunction/SAFT/Characterization/Corollaries.v's
    [continuous_Set_functor_representable] is the same passage over the
    hypotheses of Mac Lane's §V.8 Corollary -- [Complete],
    [PreservesImageLimit], a [Cogenerator] and #451's [WellPowered], with
    no covering datum -- and its [continuous_Set_functor_representable_iff]
    is the criterion as a biconditional;
    Adjunction/SAFT/Characterization/Examples.v applies it at [Id[Sets]]
    and at [HomFrom A] under [Untruncate].  [saft_representable] and its
    statement are unchanged.)
    CONVERSE: it CANNOT be run with the tree's copowers.  Every copower in
    tree (Structure/Limit/Power.v, which came from #321; #366 added
    Structure/Limit/Power/Adjunction.v) is indexed by a bare [Type] and so
    yields plain functions out of the index, where a [Sets]-valued
    adjunction needs setoid morphisms respecting [≈]; a setoid-indexed
    copower does not exist in tree (probe N5 pins the mismatch).  So the
    converse is delivered as an axiom-free CONDITIONAL over
    [HasSetsCopowers], stated exactly as #348's
    [adjunction_iff_pointwise_representable] consumes it — which makes the
    hypothesis, by that same biconditional, "the represented functor has a
    left adjoint".  That is disclosed rather than hidden: the conditional
    is honest, not deep.  Two further disclosures: the hypothesis is
    STRONGER than what is used ([cop] is applied only at the representing
    object), and no inhabitant of it is built by any route — none is shown
    impossible either.

    WITNESSES.  Two, both with every premise discharged in tree.  The
    points functor [Sets_points := Hom(1,−)] on [Sets]: its element-wise
    solution set is the singleton at [1] with the identity as its element,
    its limit preservation is Functor/Hom/Limit.v's [hom_ContinuousFunctor],
    and [Sets_points_repr] is Theorem 3 applied; [Sets_points_iso] compares
    the object the theorem produces with [1] through
    [repr_unique_iso].  And the identity functor on [Sets], twice over:
    [Sets_Id_repr] by Theorem 3 from Adjunction/GAFT/Sets.v's own solution
    set, and [Sets_Id_repr_of_adjoint] by Exercise 1 from [GAFT_at_Sets_Id]
    's adjunction, whose representing object reads back at [eq_refl] as
    that adjoint at the singleton.

    STALE PREMISES — the issue's "Current state" is wrong in five
    substantive claims and six line numbers.  FALSE: "no
    [(1 ~{Sets}~> X) ≅ carrier X] lemma" (it is [global_elements_iso],
    Theory/Universal/Element.v, with the natural form);
    "the library never performs that instantiation" (Element.v does
    relate [AUniversalArrow SetsOne H r] and [AUniversalElement H r] with
    [eq_refl] and [≈] round trips); "nothing produces a [Representable]
    from anything, and in particular not from an adjunction; no file even
    imports it" (at the parent commit 26 constants across 19 files conclude
    [Representable] — counted by taking each [Definition]/[Theorem]/[Lemma]/
    [Corollary]/[Instance] head with comments stripped and testing whether
    the conclusion begins with [Representable] — and 33 files [Require] it;
    one of the 26 is Adjunction/Representability.v's [adj_representable],
    an adjunction-sourced instance); "no category
    of elements for a [Sets]-valued functor" (Construction/Elements.v has
    [Elements], [ElementsComma] and the proved comparison
    [Elements_Comma]); and "#366 is the filed obligation" for copowers
    (#366 landed).  STALE LINE NUMBERS: the issue's citation for
    [Representable] misses its declaration in Functor/Representable.v,
    and that same miss is repeated five times;
    [representability_by_yoneda] is in Structure/UniversalProperty.v,
    over a narrower range than cited; the Instance/Sets.v citation is
    off, and the object wanted there is
    Construction/Elements.v's [SetsOne]; the Adjunction/Continuity.v
    citation lands on header prose rather than on any of the four
    constants there, which are [right_adjoint_PreservesLimitCone],
    [right_adjoint_Continuous], [right_adjoint_preserves_limit] and
    [right_adjoint_preserves_limits]; and the citations for
    Construction/Comma/Limit.v and
    Theory/WeaklyInitial.v are each off by a few lines.
    Correct as cited: GAFT.v, SAFT.v, Theory/Profunctor/Adjunction.v.  The
    [Sets_global_points] named in the issue's Verification block exists
    nowhere in tree, and is not created here — the bridge it seems to want
    is [global_elements_iso].

    UNIVERSES ([About] under `Set Printing Universes`).  Definition 3 is
    UNPINNED: [ElementSolutionSet@{u u0 u1 i}] is over
    [C : Category@{u u0 u0}] with one strict constraint ([u0 < u1], the
    functor's) and no [Set].

    RECORDED CORRECTION.  An earlier revision continued: "Everything
    downstream of the comma-initial step inherits GAFT's pin instead —
    [representability_theorem] and [representability_iff] are over
    [C : Category@{_ Set Set}], hom AND proof at [Set], with [Set < u] —
    which is why the theorem is stated at TOP LEVEL … The witnesses land
    at [Sets@{Set u}], the same place Adjunction/GAFT/Sets.v's header
    records for [GAFT_at_Sets_Id]."  GAFT has no such pin any more:
    Instance/Discrete.v's [DiscreteCat_Functor] was annotated in place at
    its declaration in the PR "algebraic carriers are sets" (2026-09-17), and
    measured after it

      representability_theorem@{cobj h su +} :
        ∀ {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su}),
        Complete@{h h h cobj} → PreservesImageLimit
        → ElementSolutionSet@{cobj h su h} K → Representable K

      representability_iff@{… u11 … u15 u16} :
        ∀ {C : Category@{u15 u11 u11}} …, Complete@{u11 u11 u11 u15} → …

    -- no literal [Set] in either, and [GAFT_at_Sets_Id] likewise stands
    at the polymorphic [Sets].  What SURVIVES is the reason for stating
    the theorem at TOP LEVEL, because that was never the [Set]: both
    constants identify [C]'s hom and proof universes, so inside a section
    that has already elaborated a category with those levels APART the
    ascription is refused, and probe N4 pins exactly that ("universe
    inconsistency: Cannot enforce sp = sh because sh < sp") -- an
    identification, with no [Set] in the message.  Stdlib
    caps ([JMeq], [eq], [Logic_lemmas.equality], [Projections],
    [projections], [Basics.compose], [ID]) all arrive with the GAFT and
    [Sets] donors; none is introduced here.

    MEASURED.  38 `.glob` heads (32 `def`, 1 `prf`, 4 `proj`, 1 `rec`) and
    14 [Program] obligations (6 of [homafter_one_iso], discharged by its
    local tactic; 8 of [homafter_whisker], closed by hand under [idtac]),
    plus Adjunction/GAFT.v's 2 new heads — 54 constants, all "Closed under
    the global context", zero `Axioms:` lines; the `make print-assumptions`
    gate carries the 38 and the 2.  Four `Defined` in this file, each
    LOAD-BEARING (flipped to `Qed` one at a time in a copy of the whole
    file, compilation halting at the first readback that reads the flipped
    constant's components back: [sols_of_esols] stops [sols_of_esols_index],
    [esols_of_sols] stops [esols_of_sols_index], [representability_iff] stops
    [representability_iff_fst] and [Sets_points_esol] stops
    [Sets_points_esol_obj]); eight `Qed`, all of them [homafter_whisker]'s
    obligations.  GAFT.v's [comma_initial_of_sols] is [Defined] because it
    produces DATA, matching [wif_of_sols] beside it, but the flip is NOT
    load-bearing — nothing in tree reads its components back, and it is
    disclosed here rather than claimed.  Closure 99 excluding self
    (Functor/Hom/Continuous.v 10 at the margin, Adjunction/GAFT/Sets.v 2,
    Adjunction/Representability.v 2, Construction/Comma/Creation.v 2,
    Adjunction/SAFT.v 1, and 22 of the 27 `Require`s at margin 0; none is
    droppable).  Adjunction/Representability.v's own closure is 39 excluding
    self, and requiring this file's imports there would take it to 98 — the
    reason this is a satellite.  (CORRECTION, #451: Adjunction/SAFT.v now
    requires Theory/Subobject.v, which no other import here reaches, and
    the same count over .Makefile.coq.d -- which reproduces 99, 98, 39 and
    the five margins above when that edge is left out -- gives a closure
    of 100 excluding self, Adjunction/SAFT.v 2 at the margin (the other
    four margins unchanged), and 99 for Adjunction/Representability.v with
    this file's imports; its own 39 is unchanged.)  Zero name collisions
    for the 38 names (`grep -rlw --include='*.v'`).
    Test/ProbeRepresentability437.v mirrors this file's `Require` list and
    carries 6 refutation commands = 1
    instrument + N1-N2
    CONVERSION (the two solution-set records are not the same type;
    [HomAfter K 1] is not [K]) + N3, N5 TYPING (the apex-only
    [PreservesAllLimits] does not ascribe where the cone-level
    [PreservesImageLimit] is asked; a [Type]-indexed copower family is not
    a [HasSetsCopowers] — "The term "X" has type "Type" while it is
    expected to have type "obj[Sets]"") + N4 UNIVERSE, each stripped one at
    a time in a copy of the whole file beside its accepted control; seven
    `eq_refl` readbacks; guard coverage 34/24 with ten exhaustive
    exceptions (identifier tokens inside the six refutation commands /
    also named outside them, comments stripped: three keywords ([Definition],
    the refutation keyword, [Type]), three bound variables ([X], [b], [cop])
    and the four refuted names); rename-simulated 14 library
    names — [ElementSolutionSet], [SolutionSet], [SetsOne], [HomAfter],
    [Curried_Hom], [Compose], [representability_theorem],
    [PreservesAllLimits], [PreservesImageLimit], [Complete],
    [HasSetsCopowers], [Representable], [eq_refl], [Category] — every
    first break on a positive line.  `make todo` grows by the 6 refutation
    lines only (2283 → 2289 over #435's tip), so the issue's "adds no new
    hits" box is not met as written (disclosed, as in #430-#435); Coq 8.19
    and 8.20 are checked by nix source builds of the committed revision,
    which the PR records.

    NOT DELIVERED.  A setoid-indexed copower, hence no unconditional
    converse to Exercise 1 (above); any inhabitant of [HasSetsCopowers];
    the rewriting of [GAFT] itself to use the exported step (its lines must
    not move); GAFT as a biconditional; the [Sets_global_points] of the
    issue's Verification block, which names nothing that exists;
    representability at any target but [Sets]; a witness at any category
    but [Sets] in this file (an earlier revision said "a witness at any
    category but [Sets]" without the qualifier; since #449
    Instance/Mod/TensorAFT.v's [tensor_via_AFT_of_esols] and
    [bal_tensor_via_AFT_of_esols] apply the theorem at [RMod R] and at
    [Ab], and since #454 Instance/Mod/Watts/Unconditional.v's
    [RModop_continuous_representable] applies it at [(RMod R)^op] with
    its completeness and solution-set premises discharged for every
    continuous K, and at K := the hom functor by
    [RModop_hom_representable_obj]); naturality of [homafter_one_iso] in
    [K], or functoriality of any construction here; no edit to
    Functor/Representable.v, Theory/Universal/Element.v,
    Construction/Elements.v, Functor/Hom/Continuous.v, Adjunction/SAFT.v,
    Adjunction/Representability.v, and none to Adjunction/GAFT.v above its
    last line.  Instance/Sets/Complete.v and Adjunction/GAFT/Sets.v ARE
    edited, one sentence each and line-count-preserving: both said [SAFT]
    was never applied, which [saft_representable] makes false, and the
    citations into those files (all at lines below the corrections) still
    land. *)

Section Definition3.

Context {C : Category}.
Context (K : C ⟶ Sets).

(** ** Mac Lane §V.6 Definition 3: the solution set condition, element-wise

    A set of objects and ELEMENTS through which every element factors.  This
    is Definition 3 as the book states it; [SolutionSet] of Adjunction/GAFT.v
    is the hom-shaped form, and the two agree at the singleton set. *)

(* The INDEX universe is named [i], and it is free of it: the constraint
   block relates it to nothing, exactly as in [SolutionSet].  It is the
   LAST binder, because the three the enclosing section discharges (the
   ambient's object and hom-and-proof levels, and [Sets]' object level)
   come first and print with generic names.  Measured readback:

     ElementSolutionSet@{u u0 u1 i} :
     ∀ {C : Category@{u u0 u0}}, (C ⟶ Sets@{u0 u1}) → Type@{max(u,u0,i+1)}
     (* u u0 u1 i |= u0 < u1 / u0 <= ID.u0 *)

   [representability_theorem] below is where [i] is pinned, to the ambient
   hom universe, exactly as in [GAFT]: see its own binders. *)
Record ElementSolutionSet@{i} := {
  esol_index : Type@{i};
  esol_obj : esol_index → C;
  esol_elem : ∀ i, K (esol_obj i);
  esol_covers {c : C} (x : K c) :
    { i : esol_index & { t : esol_obj i ~{C}~> c
                       & fmap[K] t (esol_elem i) ≈ x } }
}.

(** ** The two forms agree at the singleton

    Elements of [K c] are global points [1 ~> K c] — Theory/Universal/
    Element.v's [global_element] and [global_elements_iso], which already
    exist; nothing here re-proves that bridge. *)

(* Both passages carry the index TYPE across on the nose — the four
   [eq_refl] readbacks below say so.  At the level of the index UNIVERSE
   the two directions differ, and the difference is measured rather than
   assumed:

     sols_of_esols@{u u0 u1 i u2 u3 u4} :
       … ElementSolutionSet@{u u0 u1 i} K
         → SolutionSet@{i u1 u u0} K SetsOne
     (* u u0 u1 i u2 u3 u4 |= u0 < u1 / u3 <= ID.u0 *)

   -- [i] on the nose in this direction, the index universe reappearing
   verbatim in [SolutionSet]'s first slot; and

     esols_of_sols@{u u0 u1 i u2 u3 u4 u5} :
       … SolutionSet@{u5 u1 u u0} K SetsOne
         → ElementSolutionSet@{u u0 u1 i} K
     (* u u0 u1 i u2 u3 u4 u5 |= u0 < u1 / u5 <= i *)

   -- a BOUND, [u5 <= i], in the other, since the record is built rather
   than projected.  Stated because "the same index" is true of the types
   and only up to [<=] of the levels. *)
Definition sols_of_esols@{i +} (E : ElementSolutionSet@{i})
  : SolutionSet K SetsOne.
Proof.
  unshelve refine
    {| sol_index := esol_index E
     ; sol_obj := esol_obj E
     ; sol_arr := fun i => global_element (esol_elem E i) |}.
  intros c h.
  destruct (esol_covers E (h ttt)) as [i [t e]].
  exists i, t.
  intro u; destruct u; exact e.
Defined.

Definition esols_of_sols@{i +} (S : SolutionSet K SetsOne)
  : ElementSolutionSet@{i}.
Proof.
  unshelve refine
    {| esol_index := sol_index S
     ; esol_obj := sol_obj S
     ; esol_elem := fun i => sol_arr S i ttt |}.
  intros c x.
  destruct (sol_covers S (global_element x)) as [i [t e]].
  exists i, t.
  exact (e ttt).
Defined.

(* Both passages keep the index and the objects on the nose. *)
Example sols_of_esols_index (E : ElementSolutionSet) :
  sol_index (sols_of_esols E) = esol_index E := eq_refl.

Example sols_of_esols_obj (E : ElementSolutionSet) (i : esol_index E) :
  sol_obj (sols_of_esols E) i = esol_obj E i := eq_refl.

Example esols_of_sols_index (S : SolutionSet K SetsOne) :
  esol_index (esols_of_sols S) = sol_index S := eq_refl.

Example esols_of_sols_elem (S : SolutionSet K SetsOne) (i : sol_index S) :
  esol_elem (esols_of_sols S) i = sol_arr S i ttt := eq_refl.

(** ** A representation out of an initial object of the elements comma *)

Definition representable_of_comma_initial (I : @Initial (=(SetsOne) ↓ K)) :
  Representable K :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement
       (AUniversalElement_of_AUniversalArrow K _
          (aua_of_ua (Build_UniversalArrow SetsOne K I)))).

End Definition3.

Arguments ElementSolutionSet {C} K.
Arguments esol_index {C K} _.
Arguments esol_obj {C K} _ _.
Arguments esol_elem {C K} _ _.

(** ** Mac Lane §V.6 Theorem 3

    Stated at top level, and the binders carry the SAME size condition as
    [GAFT], which is where it comes from ([comma_initial_of_sols]):

      (i)  [ElementSolutionSet@{cobj h su h} K] -- the element-solution-set
           INDEX universe (the last slot) is the ambient hom universe [h].
           The record leaves it free; this theorem pins it.
      (ii) [@Complete@{h h h cobj} C] -- [Complete]'s shape-object universe
           is [h] too, for the reason Adjunction/GAFT.v spells out: the
           equalizer of all endomorphisms of the product is a limit over a
           shape whose objects are a hom-set.

    RECORDED CORRECTION.  An earlier revision of this comment read
    "[comma_initial_of_sols] pins the hom AND proof universes of both
    categories to [Set] (GAFT's own pin), and inside a section that has
    already elaborated [Sets] the ascription is refused."  That [Set] was
    a universe-minimization artifact of Instance/Discrete.v's unannotated
    [DiscreteCat_Functor] and is gone (PR "algebraic carriers are sets",
    2026-09-17); the theorem is still stated at top level, and (i)+(ii)
    are why.  The refusals that Instance/Mod/TensorAFT.v records against
    this theorem survive the repair, re-measured there: they are (i)
    meeting an index one universe above the ring's carrier, with no [Set]
    in the message.

    Measured readback:

      representability_theorem@{cobj h su u u0 u1 u2 u3 u4 u5 u6 u7 u8} :
      ∀ {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su}),
        Complete@{h h h cobj}
        → PreservesImageLimit@{cobj h su h u h su h}
          → ElementSolutionSet@{cobj h su h} K
            → Representable@{u u0 su cobj h} K
      (* cobj h su … |= h < su / u6 <= u4 *) *)

Definition representability_theorem@{cobj h su +}
  {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C Sets K)
  (E : ElementSolutionSet@{cobj h su h} K) : Representable K :=
  representable_of_comma_initial K
    (comma_initial_of_sols K SetsOne comp cont (sols_of_esols K E)).

(** ** Transport of a representation along a natural isomorphism *)

Definition Representable_transport {C : Category} {F G : C ⟶ Sets}
  (i : F ≅[[C, Sets]] G) (R : Representable F) : Representable G :=
  {| repr_obj := @repr_obj C F R
   ; represented := iso_compose i (@represented C F R) |}.

Example Representable_transport_obj {C : Category} {F G : C ⟶ Sets}
  (i : F ≅[[C, Sets]] G) (R : Representable F) :
  @repr_obj C G (Representable_transport i R) = @repr_obj C F R := eq_refl.

(** ** §V.8 Exercise 1, forward: a left adjoint makes the functor representable

    [HomAfter K 1] IS [Hom(1,−) ◯ K] on the nose, and global points make it
    [K] itself, so #348's [adj_representable] at the singleton transports
    onto [K]. *)

Section Ex81.

Context {C : Category}.
Context (K : C ⟶ Sets).

Example homafter_one_is_composite :
  HomAfter K SetsOne = Compose (fobj[Curried_Hom Sets] SetsOne) K := eq_refl.

#[local] Obligation Tactic :=
  simpl; intros;
  repeat match goal with [ H : poly_unit |- _ ] => destruct H end;
  try (srewrite (@fmap_id _ _ K); reflexivity); try reflexivity.

Program Definition homafter_one_iso : HomAfter K SetsOne ≅[[C, Sets]] K := {|
  to   := {| transform := fun c => global_elements_to (K c) |};
  from := {| transform := fun c => global_elements_from (K c) |}
|}.

Definition representable_of_left_adjoint {L : Sets ⟶ C} (A : L ⊣ K) :
  Representable K :=
  Representable_transport homafter_one_iso (adj_representable A SetsOne).

(* The representing object is the left adjoint at the singleton. *)
Example representable_of_left_adjoint_obj {L : Sets ⟶ C} (A : L ⊣ K) :
  @repr_obj C K (representable_of_left_adjoint A) = L SetsOne := eq_refl.

End Ex81.

(** ** The converse leg: a representable functor is continuous *)

Definition continuous_of_representable {C : Category} {K : C ⟶ Sets}
  (R : Representable K) : ContinuousFunctor K :=
  representable_iso_ContinuousFunctor (@repr_obj C K R)
    (iso_equiv (@represented C K R)).

Definition preserves_image_of_representable {C : Category} {K : C ⟶ Sets}
  (R : Representable K) : @PreservesImageLimit C Sets K :=
  Continuous_PreservesImageLimit (continuous_of_representable R).

(** ** Theorem 3 as a biconditional

    A representation supplies its own element-wise solution set: the single
    object is the representing one and the single element is the identity
    read across the isomorphism. *)

Theorem representability_iff {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) :
  (@PreservesImageLimit C Sets K * ElementSolutionSet K)%type
    ↔ Representable K.
Proof.
  split.
  - intros [cont E]; exact (representability_theorem K comp cont E).
  - intro R.
    split.
    + exact (preserves_image_of_representable R).
    + unshelve refine {| esol_index := poly_unit
                       ; esol_obj := fun _ => @repr_obj C K R
                       ; esol_elem := fun _ =>
                           transform[to (@represented C K R)]
                             (@repr_obj C K R) id |}.
      intros c x.
      exists ttt.
      exists (transform[from (@represented C K R)] c x).
      pose proof (@naturality _ _ _ _ (to (@represented C K R))
                    (@repr_obj C K R) c
                    (transform[from (@represented C K R)] c x) id) as N.
      simpl in N.
      rewrite id_right in N.
      rewrite N.
      pose proof (iso_to_from (@represented C K R) c x) as HH;
        simpl in HH; rewrite HH; srewrite (@fmap_id _ _ K c); reflexivity.
Defined.

Example representability_iff_fst {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) (cont : @PreservesImageLimit C Sets K)
  (E : ElementSolutionSet K) :
  fst (representability_iff K comp) (cont, E)
    = representability_theorem K comp cont E := eq_refl.

(** ** Riehl 4.7.14: SAFT's hypotheses give representability *)

(* CORRECTION, #453: "SAFT's hypotheses" here are Adjunction/SAFT.v's,
   whose covering datum [cover] is refutable (the header).  The passage
   over the book's hypotheses is Adjunction/SAFT/Characterization/
   Corollaries.v's [continuous_Set_functor_representable]; this
   constant is kept as it was. *)

Definition saft_representable {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) (cont : @PreservesImageLimit C Sets K)
  (G : Cogenerator C) (WP : ∀ x : C, SubobjectIndex x)
  (cover : SubobjectCover K comp G WP) : Representable K :=
  representable_of_left_adjoint K (projT2 (SAFT K comp cont G WP cover)).

(** ** §V.8 Exercise 1, converse: copowers give the left adjoint

    The tree's copowers (Structure/Limit/Power.v from #321, with #366's
    Structure/Limit/Power/Adjunction.v) are indexed by a
    bare [Type] and so yield plain functions out of the index, where a
    [Sets]-valued adjunction needs setoid morphisms respecting [≈]; a
    setoid-indexed copower is not in the tree.  [HasSetsCopowers] is that
    missing structure, stated exactly as the representability #348's
    biconditional consumes it — so the converse lands as an axiom-free
    CONDITIONAL, and the condition is, by that same biconditional, "the
    represented functor has a left adjoint". *)

Definition HasSetsCopowers (C : Category) : Type :=
  ∀ (b : C) (X : Sets),
    Representable (HomAfter (fobj[@Curried_Hom C] b) X).

Section Ex81Converse.

Context {C : Category}.
Context {K : C ⟶ Sets}.
Context (R : Representable K).

#[local] Notation r := (@repr_obj C K R).

(* Whiskering [K ≅ [Hom r,−)] by [Hom_Sets(X,−)]. *)
#[local] Obligation Tactic := idtac.

Program Definition homafter_whisker (X : Sets) :
  HomAfter K X ≅[[C, Sets]] HomAfter (fobj[@Curried_Hom C] r) X := {|
  to   := {| transform := fun c =>
    {| morphism := fun f => transform[from (@represented C K R)] c ∘ f |} |};
  from := {| transform := fun c =>
    {| morphism := fun f => transform[to (@represented C K R)] c ∘ f |} |}
|}.
Next Obligation. intros X c u v Huv z; simpl; now rewrite (Huv z). Qed.
Next Obligation.
  intros X x y f u z; simpl.
  exact (@naturality _ _ _ _ (from (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X x y f u z; simpl.
  symmetry.
  exact (@naturality _ _ _ _ (from (@represented C K R)) x y f (u z)).
Qed.
Next Obligation. intros X c u v Huv z; simpl; now rewrite (Huv z). Qed.
Next Obligation.
  intros X x y f u z; simpl.
  exact (@naturality _ _ _ _ (to (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X x y f u z; simpl.
  symmetry.
  exact (@naturality _ _ _ _ (to (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X c u z; simpl.
  pose proof (iso_from_to (@represented C K R) c (u z)) as HH;
    simpl in HH; rewrite HH; now rewrite id_left.
Qed.
Next Obligation.
  intros X c u z; simpl.
  pose proof (iso_to_from (@represented C K R) c (u z)) as HH;
    simpl in HH; rewrite HH; srewrite (@fmap_id _ _ K c); reflexivity.
Qed.

Definition left_adjoint_of_representable_Sets (cop : HasSetsCopowers C) :
  { L : Sets ⟶ C & L ⊣ K } :=
  fst (adjunction_iff_pointwise_representable K)
      (fun X => Representable_transport
                  (iso_sym (homafter_whisker X)) (cop r X)).

End Ex81Converse.

(** ** Witnesses at Sets

    Two functors, each with every premise discharged in tree. *)

(** *** The points functor [Hom(1,−)] on Sets *)

Definition Sets_points : Sets ⟶ Sets := @HomFrom Sets SetsOne.

Definition Sets_points_esol : ElementSolutionSet Sets_points.
Proof.
  unshelve refine
    {| esol_index := poly_unit
     ; esol_obj := fun _ => SetsOne
     ; esol_elem := fun _ =>
         (@id Sets SetsOne : carrier (fobj[Sets_points] SetsOne)) |}.
  intros c x.
  exists ttt, x.
  simpl; intro u; destruct u; simpl.
  reflexivity.
Defined.

(* The single member is the singleton itself, and the single element is its
   identity — which is what keeps [Sets_points_esol] transparent. *)
Example Sets_points_esol_obj (u : esol_index Sets_points_esol) :
  esol_obj Sets_points_esol u = SetsOne := eq_refl.

Definition Sets_points_cont : @PreservesImageLimit Sets Sets Sets_points :=
  Continuous_PreservesImageLimit (hom_ContinuousFunctor SetsOne).

Definition Sets_points_repr : Representable Sets_points :=
  representability_theorem Sets_points Sets_Complete Sets_points_cont
    Sets_points_esol.

(* The object the theorem produces represents the same functor as the
   singleton does, so the two agree up to the canonical isomorphism. *)
Definition Sets_points_iso :
  @repr_obj Sets Sets_points Sets_points_repr ≅ SetsOne :=
  repr_unique_iso (Hom_Representable SetsOne) Sets_points_repr.

(** *** The identity functor on Sets, both routes *)

Definition Sets_Id_esol : ElementSolutionSet (@Id Sets) :=
  esols_of_sols (@Id Sets) (Sets_Id_SolutionSet SetsOne).

Definition Sets_Id_repr : Representable (@Id Sets) :=
  representability_theorem (@Id Sets) Sets_Complete
    Sets_Id_PreservesImageLimit Sets_Id_esol.

Definition Sets_Id_repr_iso :
  @repr_obj Sets (@Id Sets) Sets_Id_repr ≅ SetsOne :=
  repr_unique_iso (Representable_transport global_elements_natural
                     (Hom_Representable SetsOne)) Sets_Id_repr.

(* And by Exercise V.8.1's forward direction, from GAFT's own adjunction. *)
Definition Sets_Id_repr_of_adjoint : Representable (@Id Sets) :=
  representable_of_left_adjoint (@Id Sets) (projT2 GAFT_at_Sets_Id).

Example Sets_Id_repr_of_adjoint_obj :
  @repr_obj Sets (@Id Sets) Sets_Id_repr_of_adjoint
    = projT1 GAFT_at_Sets_Id SetsOne := eq_refl.
