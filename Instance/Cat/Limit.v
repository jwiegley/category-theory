(** * Cat has set-indexed products; StrictCat is small-complete under UIP

    Mac Lane, CWM 2nd ed., §V.1 Exercise 5 (book p. 112, [maclane:V.1:ex5]):
    the category of small categories has all small limits — products
    componentwise on objects and arrows, equalizers the evident
    subcategories, the general limit by products and equalizers.  Also
    Awodey §7.1 ([awodey:7.1:construction-cat-equalizer], the equalizer of
    two parallel functors as the subcategory on which they agree, and
    [awodey:7.1:remark-cat-complete]), Riehl §3.1 Exercise 3.1.x
    ([riehl:3.1:exx], the product of an indexed family of categories),
    §3.6 Proposition 3.6.6 ([riehl:3.6:prop6]) and §4.6 Corollary 4.6.15
    ([riehl:4.6:cor15]).

    WHAT IS DELIVERED, AND IN WHICH CATEGORY OF CATEGORIES.

    (A) [Cat_HasIndexedProducts : HasIndexedProducts Cat], UNCONDITIONAL.
        Its object field IS [PiCat], its projections ARE [PiCat_Proj] and
        its universal property IS [PiCat_ump] (Construction/Product/
        Indexed.v), consumed and not rebuilt; [PiCat_IsIndexedProduct] is
        the apex-pinned record beneath it.  The probe reads the class's
        object and projections back at [eq_refl].  This is Riehl's indexed
        clause and Awodey's "all small products", in the tree's [Cat].

    (B) The equalizer of [F G : C ⟶ D] as a SUBCATEGORY, Awodey's and
        Riehl's construction verbatim: [EqSub F G : Subcategory C] has
        objects [{c & F c = G c}] (a LEIBNIZ equation of objects) and arrows
        those [f] with [hom_cast p p' (fmap[F] f) ≈ fmap[G] f] — the two
        images agree after transport along the two object equations —
        [EqCat F G := Sub C (EqSub F G)] and [EqIncl := Incl C (EqSub F G)].
        Its universal property is [Eq_IsEqualizer (uip : ObjUIP D) :
        @IsEqualizer StrictCat C D F G (EqCat F G) (EqIncl F G)] in
        Structure/Equalizer/Fork.v's apex-pinned record, and
        [StrictCat_HasEqualizers : (∀ C, ObjUIP C) → HasEqualizers
        StrictCat] its packaging in that file's class (the issue's
        "[HasEqualizers] form").  [Eq_commutes] is a [:=] with no tactic —
        the fork equation's object component IS the equation each object
        carries and its arrow component IS the equation each arrow carries.

    (C) [StrictCat_HasIndexedProducts : (∀ C, ObjUIP C) → DepFunext →
        HasIndexedProducts StrictCat], on the SAME [PiCat]/[PiCat_Proj]/
        [PiCat_Pair], and [StrictCat_Complete := Complete_from_products_
        equalizers (StrictCat_HasIndexedProducts uip fe)
        (StrictCat_HasEqualizers uip)] — Mac Lane's "the general limit
        follows by the products-and-equalizers construction" is exactly one
        application of Structure/Limit/FromProducts.v's theorem (#416),
        consumed and not re-derived.

    THE ISSUE'S PINNED NAMES [Cat_HasEqualizers] AND [Cat_Complete] ARE NOT
    DELIVERED, AND THE REASON IS RIEHL'S OWN SHARPENING ON THE ISSUE.
    Instance/Cat.v:142-145 gives [Cat] the hom-setoid [Functor_Setoid],
    natural isomorphism of functors, so this [Cat] is Ho(Cat) and an
    isomorphism in it is an EQUIVALENCE of categories.  The on-the-nose
    subcategory (B) is then not merely unproven but WRONG as an equalizer
    in [Cat], and that is a THEOREM here rather than a remark:
    [EqCat_not_Cat_equalizer] takes the parallel pair [1 ⇉ Chaotic bool]
    picking [true] and [false] — two functors that are EQUIVALENT in [Cat]
    ([ChaoticBool_points_equiv], every hom-set of the chaotic category
    being a singleton) — whose strict equalizer has NO objects
    ([EqCat_ChaoticBool_empty], by [discriminate]), while [Id[1]] is a
    competing fork in [Cat]; a mediator would be a functor out of [1] into
    the empty category.  Read it at its width: it refutes THIS apex at THIS
    pair.  Whether Ho(Cat) has equalizers, or is complete, is NEITHER
    PROVED NOR REFUTED here, and the iso-comma ("inserter") replacement is
    UNATTEMPTED.  The issue's sharpening offers two ways out — "build it in
    Instance/StrictCat, or adopt the inserter and disclose" — and (B)-(C)
    take the first.  Instance/StrictCat.v's hom-setoid
    [Functor_StrictEq_Setoid] is Leibniz equality of the object actions
    together with transported agreement of the arrow actions, which is what
    a subcategory cut by [F c = G c] can satisfy.  So the answer to Mac
    Lane's exercise as this library can state it is: [StrictCat] is
    small-complete under two hypotheses, and [Cat] has small products
    outright.

    THE TWO HYPOTHESES, WHERE EACH IS SPENT, AND THAT BOTH ARE NECESSARY.
    [ObjUIP D] (Theory/Category/Monoid.v) enters the equalizer side at ONE
    lemma, [Eq_obj_eq]: two objects of [EqCat F G] over one object of [C]
    carry two proofs of [F c = G c], and the uniqueness clause
    [Eq_med_unique] must identify a competing mediator's object [(c; p)]
    with the canonical [(c; q)].  [Eq_commutes], [Eq_med] and [Eq_med_incl]
    take no hypothesis, and the five [Program] obligations of [EqSub]
    (two) and [Eq_med] (three) take none.  On the product side [DepFunext]
    (dependent function extensionality at the index and small object
    universes, declared here as a bare [Type]) and [ObjUIP] enter at ONE
    lemma, [pi_obj_eq]: two
    objects of [PiCat C] that agree pointwise must be identified, and the
    identification's projections must be the given pointwise equations;
    [PiCat_Pair_Proj_strict] takes neither.  Both hypotheses are NECESSARY
    for the uniqueness clauses as STATED — uniformly, for every parallel
    pair or family, with no hypothesis on the target:
    [Eq_uniqueness_forces_UIP] derives UIP for every type at the small
    object universe (the loops [p : x = x] at a point [x] of [Chaotic X]
    each name a functor [1 ⟶ EqCat (ChaoticPt x) (ChaoticPt x)] satisfying
    the triangle, so uniqueness identifies them; axiom-free through
    [inj_pair2_eq_dec] at the decidable index [poly_unit]) — this is
    Instance/Cat/Pullback.v's [FP_uniqueness_forces_UIP] one shape over —
    and [PiCat_uniqueness_forces_funext] derives dependent function
    extensionality (two pointwise-equal families [f g : ∀ i, P i] name two
    mediators [1 ⟶ PiCat (fun i => Chaotic (P i))] for one cone).  Scope
    both precisely: each is about the uniqueness clause OF THIS APEX, so
    neither refutes [HasEqualizers StrictCat] or [HasIndexedProducts
    StrictCat] with some other apex, and no such refutation is offered.
    The blanket [∀ C, ObjUIP C] is free for decidable object equality by
    Hedberg (Instance/Cat/Pullback.v's [ObjUIP_of_ObjDecEq]), and
    [DepFunext] has no axiom-free inhabitant in the tree; neither is
    registered as an [Instance].

    RELATION TO #337 (Instance/Cat/Pullback.v).  Same design decisions for
    the same reason: the universal property in [StrictCat], [ObjUIP] as the
    hypothesis, its necessity proved by a loop-space countermodel.  Pullbacks
    ARE a special case of (C) in principle (an equalizer of two composites
    out of a binary product), but no derivation of that file's
    [StrictCat_HasPullbacks] from [StrictCat_Complete] is built — it would
    go through [Structure/Pullback/Reduction.v]'s reduction, which wants a
    [Cartesian StrictCat] that does not exist — so the relation is recorded
    in prose only.  That module is NOT required — its own closure is 38
    modules excluding itself, and requiring it would take this file's from
    52 to 58 (measured with [coqdep -sort] over both files: 59 modules
    counting both) — and its [fmap_hom_cast] is RESTATED as
    [eq_fmap_hom_cast].

    RIEHL'S [ob]/[mor] LEAD-IN IS NOT TAKEN, AND WHY.  Riehl computes
    limits in [Cat] by representing objects and morphisms through [1] and
    [2].  Instance/Cat/Objects.v proves that over THIS [Cat] no objects
    functor into a target comparing object maps by Leibniz equality exists
    ([objects_not_functorial_over_Cat]), the same fact that blocks the
    on-the-nose equalizer; its [StrictCat_Objects] is the strict version.
    The limits here are computed DIRECTLY from the product and subcategory
    constructions and nothing goes through an [ob] or [mor] functor.

    AWODEY'S CAVEAT.  Coequalizers of categories are much harder to
    describe (already for posets), so the COLIMIT side is scoped out
    explicitly: nothing here is about coequalizers, coproducts (#338's
    [Cat_HasIndexedCoproducts]) or cocompleteness, and no colimit
    construction is attempted.

    UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK OVER ALL 58 CONSTANTS.
    [Cat_HasIndexedProducts@{i so sh u u0} : HasIndexedProducts@{i i i so u
    so} Cat@{u so u0 so sh}] — index universe [i], small categories at
    [Category@{so sh sh}] — with, among ten constraints, the bounds
    [i <= sh], [i <= so], [sh <= so], three strict bounds into the ambient
    levels ([so < u], [sh < u], [sh < u0]), four stdlib [Projections] caps,
    and NO equation.  The explicit binders are LOAD-BEARING: with the
    universe binders removed and the lambda binders left untyped, the two
    definitions minimize [i], [so] and [sh] to ONE level, [Cat]'s ambient
    level staying separate (measured; that form reads
    [Cat_HasIndexedProducts@{u u0} : HasIndexedProducts@{u u u u u0 u}
    Cat@{u0 u u0 u u}]).  The bound
    [sh <= so] — the small categories' hom universe at or below their
    object universe — is [PiCat_Proj]'s, MEASURED AND NOT ATTRIBUTED BY
    READING: at levels declared [so < sh], [PiCat C : Category@{so sh sh}],
    [PiCat C : obj[Cat@{_ sh _ so sh}]], the class applied up to the
    projections, and the BARE [PiCat_Proj C a] and [PiCat_ump R] are all
    accepted, while [PiCat_Proj C a : PiCat@{i so sh so sh} C ⟶ C a] is
    refused — the projection's declared [PiCat] instance identifies the
    index universe with the small hom universe and bounds the product's
    OBJECT universe below by it, so the projection's product cannot sit at
    object universe [so]; [PiCat_IsIndexedProduct] (at its argument) and the
    instance inherit it.  Annotating [Cat]'s hom universe separately, in
    the instance alone and in both the record and the instance, was tried
    and does not lift it (the first re-derives [so = m], the second keeps
    [sh <= so]); the donor is Construction/Product/Indexed.v's unannotated
    declaration, the same one Construction/Product/Limit.v records, and
    the bound is not claimed unavoidable.  Every constant of the equalizer
    development is over [C : Category@{u u0 u0}], [D : Category@{u1 u2
    u2}] — hom identified with proof IN THE BINDER, [Subcategory]'s and
    [Functor_StrictEq_Setoid]'s doing; [EqCat] carries NO block equation,
    [EqIncl] carries [u0 = u2] ([Sub]'s hom universe is [C]'s), and every
    constant stating a [StrictCat] equation ([Eq_commutes], [Eq_IsEqualizer],
    the whole Mediator section) carries [u = u1] and [u0 = u2] — [StrictCat]
    identifies the object AND hom universes of [C] and [D], its objects being
    [Category@{u u0 u0}] at ONE instance — the Mediator section adding
    [u = u3], [u0 = u4] for the competitor's category [Z].
    [StrictCat_HasEqualizers@{u u0 u1 u2 u3 u4}] carries no equation.
    [PiCat_ump_unique_strict] and [PiCat_IsIndexedProduct_strict] carry
    [u = u1] (index = small hom, [PiCat_Proj] again), and
    [StrictCat_HasIndexedProducts@{u u0 u1} : (∀ C : Category@{u u u},
    ObjUIP C) → DepFunext@{u u} → HasIndexedProducts@{u u u u u0 u}
    StrictCat@{u0 u u0 u u}] collapses index, object and hom to one level.
    THE SMALLNESS SIDE CONDITION is carried by [StrictCat_Complete@{u u0
    u1} : … → Complete@{u0 u0 u0 u}]: the diagram shapes range over
    [Category@{u0 u0 u0}], the same universe instance as the small
    categories, the collapse forced by [Complete_from_products_equalizers],
    whose index universe IS the ambient hom universe (the discipline of
    Instance/Sets/Complete.v:196's [Sets_Complete@{u u0} : Complete@{u u u
    u0}], and Structure/Complete.v:27-38's note).  The necessity theorems
    match the sufficiency statements' shapes: [Eq_uniqueness_forces_UIP@{o h
    u u0 u1 u2}] carries no equation, [PiCat_uniqueness_forces_funext@{i o h
    u u0}] carries [h = i].  [Chaotic@{o h p}] is free in all three levels
    (its homs are [poly_unit]; Instance/Discrete/Reconstruct.v's
    [Indiscrete] pins its homs to the stdlib [unit : Set] and would have
    confined the product half to [Set]-indexed families) and [DepFunext@{i
    o} : Type@{max(i+1,o+1)}] carries none.  ZERO word-bounded [Set] in
    the binder or block of any of the 58.

    COUNTS.  58/58 constants closed under the global context with ZERO
    [Axioms:] lines — 40 declaration heads (19 [Definition], 6 [Program
    Definition], 11 [Lemma], 3 [Theorem], 1 [Instance]) plus the 18
    [Program] obligations [Print Module] lists and a source sweep cannot
    see (5 [Next Obligation]s are written; [EqSub], [Eq_med], [ChaoticPt],
    [eq_loop_functor], [pi_point] and [ChaoticBool_points_equiv] generate
    18), all in the [make print-assumptions] gate FULLY QUALIFIED.  Ten
    [Defined] tokens, exactly THREE load-bearing by flipping each alone to
    [Qed] with both this file and the probe recompiled: [Chaotic], whose
    flip stops [ChaoticPt]'s [fobj] field in this file (an opaque
    [Chaotic X] no longer unfolds to [X]: "x has type X while it is
    expected to have type obj[Chaotic X]"); [Eq_IsEqualizer],
    whose flip stops the probe's readback of the mediator; and
    [StrictCat_HasEqualizers], whose flip stops the probe's readbacks of
    the chosen equalizer and its inclusion — the other seven flip with both
    files green and are kept [Defined] by the data convention.  Closure 52
    modules excluding self.
    Zero collisions over the 58 names after THREE were renamed before
    landing: [punit_eq] is Instance/Cat/Pullback.v:578's (same statement,
    a module deliberately not required), and [CB] matched the section
    variables of two files and a section-local [Notation CB]
    (Structure/Limit/Power/Adjunction.v:1717) — not global collisions,
    but a two-letter global name in a gate that loads many modules into
    one scope is a hazard, hence [ChaoticBool]; [CBtrue]/[CBfalse]
    matched nothing and were renamed with it ([ChaoticBool_true]/
    [ChaoticBool_false]).  The [Program] obligations of the Necessity sections
    are closed by a LOCAL obligation tactic that must open [Proper] with
    [repeat intro] — with [intros] the [fmap_respects] obligation stays
    folded and [ChaoticPt] never enters the environment (measured, and the
    cause of one lost compile).

    Test/ProbeCatLimit414.v mirrors this file's [Require] list and carries
    10 refutation commands = 1 instrument check + 9 negatives of THREE
    kinds told apart by the error TEXT: 6 FORMABILITY (the [PiCat_Proj]
    donor with its five accepted controls, the two inheriting constants,
    [StrictCat_HasIndexedProducts] and [StrictCat_Complete] at an index
    universe strictly below the hom universe, and their donor
    [Complete_from_products_equalizers] at the same levels), 1 TYPING
    ([Eq_IsEqualizer] ascribed at [@IsEqualizer Cat …], a plain has-type
    mismatch with no "cannot unify" and no universe clause) and 2
    CONVERSION (the equalizer and product triangles as WHOLE functor
    records, each beside its two [eq_refl] data controls) — each stripped
    ONE AT A TIME in a copy of the whole file and compiled alone with its
    error read; guard coverage measured mechanically (48 identifiers inside
    a refutation command, 41 also outside, the seven exceptions
    exhaustively the refutation keyword itself, the three bound variables
    [Cu]/[HP]/[HE], the two names the refuted [Example]s declare and the
    instrument's absent name); rename-simulated 9/9 over the target
    constants the negatives name, each rename applied in THIS file only and
    every break landing on a [Check] or control line of the probe, none
    inside a refutation command.  [make todo] grows by 16 lines, ALL in the
    probe — its 10 refutation commands and 6 header lines that name the
    refutation keyword — and this file contributes ZERO.

    NOT DELIVERED.  [Cat_HasEqualizers], [Cat_Complete] and any equalizer
    or completeness statement about Ho(Cat), neither proved nor refuted; the
    inserter; any colimit; the pullback special case as a theorem; a
    [Cartesian StrictCat]; the [ob]/[mor] functors on [Cat]; an axiom-free
    inhabitant of [DepFunext] or of the blanket [ObjUIP]; naturality of any
    identification in the diagram; a comparison of [StrictCat_Complete]'s
    chosen limits with [Instance/Cat/Cartesian.v]'s binary products or
    [Instance/One.v]'s terminal category; and nothing registered as an
    [Instance] except [Cat_HasIndexedProducts], which carries no hypothesis
    and so may safely resolve. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.One.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** ** Cat has set-indexed products *)

(* The explicit universe binders are load-bearing: written bare, the two
   definitions minimize the index universe, the small categories' object
   universe and their hom universe to ONE level (measured; see the header). *)
Definition PiCat_IsIndexedProduct@{i so sh +} {I : Type@{i}}
  (C : I → Category@{so sh sh}) :
  @IsIndexedProduct Cat I C (PiCat C) (PiCat_Proj C) :=
  @Build_IsIndexedProduct Cat I C (PiCat C) (PiCat_Proj C)
    (fun D R => PiCat_ump R).

#[export]
Instance Cat_HasIndexedProducts@{i so sh +} : @HasIndexedProducts Cat :=
  @Build_HasIndexedProducts Cat
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) => PiCat C)
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) a => PiCat_Proj C a)
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) =>
       PiCat_IsIndexedProduct C).

(** ** A small cast kit *)

(* Functors commute with [hom_cast], the endpoints being relabelled by
   [f_equal] of the object map.  Restated from Instance/Cat/Pullback.v's
   [fmap_hom_cast] rather than requiring that module. *)
Lemma eq_fmap_hom_cast {X Y : Category} (P : X ⟶ Y) {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) :
  fmap[P] (hom_cast ea eb f)
    ≈ hom_cast (f_equal (fobj[P]) ea) (f_equal (fobj[P]) eb) (fmap[P] f).
Proof. destruct ea, eb; reflexivity. Qed.

(* A [hom_cast] in a product category, read at one index. *)
Lemma hom_cast_pi {I : Type} (C : I → Category) {a b a' b' : PiCat C}
      (ea : a = a') (eb : b = b') (η : a ~> b) (i : I) :
  hom_cast ea eb η i
    = hom_cast (f_equal (fun g => g i) ea) (f_equal (fun g => g i) eb) (η i).
Proof. destruct ea, eb; reflexivity. Qed.

(* A Leibniz equality of morphisms followed by a setoid equation. *)
Definition eq_then_equiv {X : Category} {a b : X} {p q r : a ~> b}
  (e : p = q) (h : q ≈ r) : p ≈ r :=
  match e in _ = q' return q' ≈ r → p ≈ r with eq_refl => fun h => h end h.

(** ** Equalizers in StrictCat *)

Section Equalizer.

Context {C D : Category}.
Context (F G : C ⟶ D).

#[local] Obligation Tactic := idtac.

(* The subcategory of C on the objects where F and G agree, and the arrows
   on which they agree up to the cast along those object agreements. *)
Program Definition EqSub : Subcategory C := {|
  sobj := fun c => F c = G c;
  shom := fun c c' (p : F c = G c) (p' : F c' = G c') (f : c ~> c') =>
            hom_cast p p' (fmap[F] f) ≈ fmap[G] f
|}.
Next Obligation.
  intros x y z ox oy oz f g Hf Hg; simpl in *.
  rewrite !fmap_comp.
  rewrite <- (hom_cast_comp ox oy oz).
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  intros x ox; simpl.
  rewrite !fmap_id.
  apply hom_cast_id.
Qed.

Definition EqCat : Category := Sub C EqSub.
Definition EqIncl : EqCat ⟶ C := Incl C EqSub.

(* The inclusion equalizes F and G, strictly: the object component IS the
   membership equality each object carries, the morphism component IS the
   equation each morphism carries. *)
Definition Eq_commutes :
  F ∘[StrictCat] EqIncl ≈[StrictCat] G ∘[StrictCat] EqIncl :=
  @Build_strict_eq EqCat D (F ◯ EqIncl) (G ◯ EqIncl)
                   (fun x : EqCat => `2 x)
                   (fun (x y : EqCat) (f : x ~> y) => `2 f).

(* Two objects of the equalizer with the same underlying object are equal --
   PROVIDED the two membership proofs can be identified, which is [ObjUIP D]. *)
Lemma Eq_obj_eq (uip : ObjUIP D) (x y : EqCat) (e : `1 x = `1 y) :
  { E : x = y & f_equal (fobj[EqIncl]) E = e }.
Proof.
  destruct x as [a p], y as [a' p']; simpl in *.
  destruct e, (uip _ _ p p').
  exists eq_refl; reflexivity.
Defined.

Section Mediator.

Context {Z : Category} (h : Z ⟶ C).
Context (Hh : F ∘[StrictCat] h ≈[StrictCat] G ∘[StrictCat] h).

Program Definition Eq_med : Z ⟶ EqCat := {|
  fobj := fun z => (h z; `1 Hh z);
  fmap := fun x y f => (fmap[h] f; strict_fmap_cast Hh f)
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; simpl; apply fmap_comp. Qed.

Definition Eq_med_incl : EqIncl ∘[StrictCat] Eq_med ≈[StrictCat] h.
Proof.
  refine (@Build_strict_eq Z C (EqIncl ◯ Eq_med) h (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(* [EqCat]'s hom-setoid compares underlying morphisms, so an equation between
   the inclusion's images IS an equation in [EqCat]; the proof is the
   identity. *)
Definition EqCat_equiv_of_incl {x y : EqCat} (f g : x ~> y)
  (H : fmap[EqIncl] f ≈ fmap[EqIncl] g) : f ≈ g := H.

Lemma Eq_med_unique (uip : ObjUIP D) (v : Z ⟶ EqCat)
      (Hv : EqIncl ∘[StrictCat] v ≈[StrictCat] h) :
  v ≈[StrictCat] Eq_med.
Proof.
  refine (@Build_strict_eq Z EqCat v Eq_med
            (fun x => `1 (Eq_obj_eq uip (v x) (Eq_med x) (`1 Hv x))) _).
  intros x y f.
  pose proof (`2 (Eq_obj_eq uip (v x) (Eq_med x) (`1 Hv x))) as Px.
  pose proof (`2 (Eq_obj_eq uip (v y) (Eq_med y) (`1 Hv y))) as Py.
  apply EqCat_equiv_of_incl.
  etransitivity; [ exact (eq_fmap_hom_cast EqIncl _ _ (fmap[v] f)) | ].
  rewrite Px, Py.
  exact (strict_fmap_cast Hv f).
Qed.

End Mediator.

Definition Eq_IsEqualizer (uip : ObjUIP D) :
  @IsEqualizer StrictCat C D F G EqCat EqIncl.
Proof.
  unshelve refine {| fork_eq := Eq_commutes |}.
  intros Z h Hh.
  unshelve refine {| unique_obj := Eq_med h Hh |}.
  - exact (Eq_med_incl h Hh).
  - intros v Hv; symmetry.
    exact (Eq_med_unique h Hh uip v Hv).
Defined.

End Equalizer.

Definition StrictCat_HasEqualizers (uip : ∀ C : Category, ObjUIP C) :
  HasEqualizers StrictCat.
Proof.
  constructor; intros C D F G.
  exists (EqCat F G), (EqIncl F G).
  exact (Eq_IsEqualizer F G (uip D)).
Defined.

(** ** Indexed products in StrictCat *)

(* Dependent function extensionality, at one pair of universes. *)
Definition DepFunext@{i o} : Type@{max(i+1,o+1)} :=
  ∀ (I : Type@{i}) (P : I → Type@{o}) (f g : ∀ i : I, P i),
    (∀ i : I, f i = g i) → f = g.

Section StrictProduct.

Context {I : Type} (C : I → Category).

(* The triangle holds on the nose: projecting the pairing IS the component,
   on objects and on arrows. *)
Definition PiCat_Pair_Proj_strict {D : Category} (R : ∀ i : I, D ⟶ C i)
  (i : I) : PiCat_Proj C i ∘[StrictCat] PiCat_Pair R ≈[StrictCat] R i.
Proof.
  refine (@Build_strict_eq D (C i) (PiCat_Proj C i ◯ PiCat_Pair R) (R i)
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(* Two objects of the product agreeing at every index are equal -- PROVIDED
   object families are compared extensionally -- and the equality returns its
   component projections, so that a cast along it can be rewritten into the
   component casts, which is where UIP on each component's objects enters. *)
Lemma pi_obj_eq
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g)
  (a b : PiCat C) (e : ∀ i : I, a i = b i) :
  { E : a = b & ∀ i : I, f_equal (fun g => g i) E = e i }.
Proof.
  exists (fe a b e).
  intro i; apply uip.
Defined.

(* A cast in the product, read at one index, once the two whole-family
   equalities are known to project to given component equalities. *)
Lemma hom_cast_pi_ext {a b a' b' : PiCat C} (ea : a = a') (eb : b = b')
  (e1 : ∀ i : I, a i = a' i) (e2 : ∀ i : I, b i = b' i)
  (H1 : ∀ i : I, f_equal (fun g => g i) ea = e1 i)
  (H2 : ∀ i : I, f_equal (fun g => g i) eb = e2 i)
  (η : a ~> b) (i : I) :
  hom_cast ea eb η i = hom_cast (e1 i) (e2 i) (η i).
Proof. rewrite hom_cast_pi, H1, H2; reflexivity. Qed.

(* Uniqueness needs two principles a set-theoretic Cat has for free: the
   object families must be compared extensionally, and the two proofs of each
   component equation must be identified.  The proof is one [exact]: the cast
   along the family equality is rewritten into the component casts by
   [hom_cast_pi_ext] and the component agreement is [HP i]'s. *)
Lemma PiCat_ump_unique_strict
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g)
  {D : Category} (R : ∀ i : I, D ⟶ C i) (H : D ⟶ PiCat C)
  (HP : ∀ i : I, PiCat_Proj C i ∘[StrictCat] H ≈[StrictCat] R i) :
  H ≈[StrictCat] PiCat_Pair R.
Proof.
  refine (@Build_strict_eq D (PiCat C) H (PiCat_Pair R)
            (fun d => `1 (pi_obj_eq uip fe (H d) (fun i => R i d)
                                    (fun i => `1 (HP i) d))) _).
  intros x y f i.
  exact (eq_then_equiv
           (hom_cast_pi_ext _ _ _ _
              (`2 (pi_obj_eq uip fe (H x) (fun i => R i x)
                              (fun i => `1 (HP i) x)))
              (`2 (pi_obj_eq uip fe (H y) (fun i => R i y)
                              (fun i => `1 (HP i) y)))
              (fmap[H] f) i)
           (strict_fmap_cast (HP i) f)).
Qed.

Definition PiCat_IsIndexedProduct_strict
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g) :
  @IsIndexedProduct StrictCat I C (PiCat C) (PiCat_Proj C).
Proof.
  constructor; intros D R.
  unshelve refine {| unique_obj := PiCat_Pair R |}.
  - exact (PiCat_Pair_Proj_strict R).
  - intros H HP; symmetry.
    exact (PiCat_ump_unique_strict uip fe R H HP).
Defined.

End StrictProduct.

Definition StrictCat_HasIndexedProducts
  (uip : ∀ C : Category, ObjUIP C) (fe : DepFunext) :
  HasIndexedProducts StrictCat :=
  @Build_HasIndexedProducts StrictCat
    (fun A C => PiCat C)
    (fun A C a => PiCat_Proj C a)
    (fun A C => PiCat_IsIndexedProduct_strict C (fun i => uip (C i))
                  (fe A (fun i => obj[C i]))).

(** ** StrictCat is small-complete *)

Definition StrictCat_Complete
  (uip : ∀ C : Category, ObjUIP C) (fe : DepFunext) : @Complete StrictCat :=
  Complete_from_products_equalizers
    (StrictCat_HasIndexedProducts uip fe) (StrictCat_HasEqualizers uip).

(** ** The two hypotheses are necessary *)

(* The chaotic category on a type: every hom-set is the polymorphic unit.
   Instance/Discrete/Reconstruct.v's [Indiscrete] pins its homs to the stdlib
   [unit : Set], which would confine the product half below to [Set]-indexed
   families; this one is [_1] with an arbitrary object type. *)
Definition Chaotic@{o h p} (X : Type@{o}) : Category@{o h p}.
Proof.
  unshelve refine {|
    obj     := X;
    hom     := fun _ _ => poly_unit@{h};
    homset  := Morphism_equality@{o h p};
    id      := fun _ => ttt;
    compose := fun _ _ _ _ _ => ttt
  |}.
  all: repeat intro; simpl;
    first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].
Defined.

Lemma chaotic_unit_eq (u : poly_unit) : ttt = u.
Proof. now destruct u. Defined.

Definition chaotic_unit_dec (a b : poly_unit) : {a = b} + {a <> b}.
Proof. destruct a, b; now left. Defined.

Section NecessityUIP.

(* One ambient [StrictCat]: its small categories are [Category@{o h h}]. *)
Universe o h.

#[local] Obligation Tactic :=
  repeat intro; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

(* The functor out of the terminal category picking a point. *)
Program Definition ChaoticPt {X : Type@{o}} (x : X) :
  _1@{o h h} ⟶ Chaotic@{o h h} X := {|
  fobj := fun _ => x;
  fmap := fun _ _ _ => ttt
|}.

(* Each loop [p : x = x] names a functor into the equalizer of [ChaoticPt x]
   with itself, and every such functor satisfies the triangle. *)
Program Definition eq_loop_functor {X : Type@{o}} {x : X} (p : x = x) :
  _1@{o h h} ⟶ EqCat (ChaoticPt x) (ChaoticPt x) := {|
  fobj := fun _ => (ttt; p);
  fmap := fun _ _ _ => (ttt; _)
|}.

Lemma eq_loop_functor_incl {X : Type@{o}} {x : X} (p : x = x) :
  EqIncl (ChaoticPt x) (ChaoticPt x) ∘[StrictCat] eq_loop_functor p
    ≈[StrictCat] Id[_1@{o h h}].
Proof.
  refine (@Build_strict_eq _1 _1
            (EqIncl (ChaoticPt x) (ChaoticPt x) ◯ eq_loop_functor p) Id[_1]
            (fun o => chaotic_unit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

(* Deriving the uniqueness clause of the strict equalizer UNIFORMLY -- for
   every parallel pair, with no hypothesis on the target -- entails UIP for
   every type at the small object universe.  So [ObjUIP D] in
   [Eq_IsEqualizer] is what the statement costs; this is
   Instance/Cat/Pullback.v's [FP_uniqueness_forces_UIP] one shape over. *)
Theorem Eq_uniqueness_forces_UIP
  (K : ∀ (C D : Category@{o h h}) (F G : C ⟶ D),
         @IsEqualizer StrictCat C D F G (EqCat F G) (EqIncl F G)) :
  ∀ (X : Type@{o}) (x y : X) (p q : x = y), p = q.
Proof.
  assert (loops : ∀ (X : Type@{o}) (x : X) (p : x = x), p = eq_refl).
  { intros X x p.
    pose proof (eq_desc (K _1 (Chaotic X) (ChaoticPt x) (ChaoticPt x))
                  Id[_1] (reflexivity _)) as U.
    pose proof (uniqueness U (eq_loop_functor p) (eq_loop_functor_incl p))
      as Up.
    pose proof (uniqueness U (eq_loop_functor (@eq_refl _ x))
                  (eq_loop_functor_incl eq_refl)) as Ur.
    assert (Hpq : eq_loop_functor p ≈[StrictCat] eq_loop_functor (@eq_refl _ x))
      by (rewrite <- Up; exact Ur).
    exact (inj_pair2_eq_dec _ chaotic_unit_dec _ _ _ _ (`1 Hpq ttt)). }
  intros X x y p q; destruct p; symmetry; apply loops.
Qed.

End NecessityUIP.

Section NecessityFunext.

(* The same ambient, with the index types of its products at [i]. *)
Universe i o h.
Constraint i <= o.
Constraint i <= h.

#[local] Obligation Tactic :=
  repeat intro; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

(* A family [f : ∀ i, P i] names a functor from the terminal category into
   the product of the chaotic categories on the [P i]. *)
Program Definition pi_point {I : Type@{i}} {P : I → Type@{o}} (f : ∀ i, P i) :
  _1@{o h h} ⟶ PiCat (fun i => Chaotic@{o h h} (P i)) := {|
  fobj := fun _ => f;
  fmap := fun _ _ _ i => ttt
|}.

Lemma pi_point_proj {I : Type@{i}} {P : I → Type@{o}} (f g : ∀ i, P i)
  (e : ∀ i, f i = g i) (i : I) :
  PiCat_Proj (fun i => Chaotic@{o h h} (P i)) i ∘[StrictCat] pi_point f
    ≈[StrictCat] ChaoticPt (g i).
Proof.
  refine (@Build_strict_eq _1 (Chaotic (P i))
            (PiCat_Proj (fun i => Chaotic (P i)) i ◯ pi_point f)
            (ChaoticPt (g i)) (fun _ => e i) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

(* Deriving the uniqueness clause of the strict indexed product UNIFORMLY
   entails dependent function extensionality at the index and small object
   universes: two pointwise-equal families name two mediators for one cone,
   and uniqueness identifies them. *)
Theorem PiCat_uniqueness_forces_funext
  (K : ∀ (I : Type@{i}) (C : I → Category@{o h h}),
         @IsIndexedProduct StrictCat I C (PiCat C) (PiCat_Proj C)) :
  ∀ (I : Type@{i}) (P : I → Type@{o}) (f g : ∀ i, P i),
    (∀ i, f i = g i) → f = g.
Proof.
  intros I P f g e.
  pose proof (iprod_desc (K I (fun i => Chaotic (P i)))
                (fun i => ChaoticPt (g i))) as U.
  pose proof (uniqueness U (pi_point f) (pi_point_proj f g e)) as Uf.
  pose proof (uniqueness U (pi_point g) (pi_point_proj g g (fun _ => eq_refl)))
    as Ug.
  assert (Hfg : pi_point f ≈[StrictCat] pi_point g)
    by (rewrite <- Uf; exact Ug).
  exact (`1 Hfg ttt).
Qed.

End NecessityFunext.

(** ** The weak ambient: the strict equalizer is not an equalizer in Cat *)

Section WeakAmbient.

#[local] Obligation Tactic :=
  intros; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

Definition ChaoticBool : Category := Chaotic bool.
Definition ChaoticBool_true  : _1 ⟶ ChaoticBool := ChaoticPt true.
Definition ChaoticBool_false : _1 ⟶ ChaoticBool := ChaoticPt false.

(* In Ho(Cat) the two points are the SAME morphism: every hom-set of the
   chaotic category is a singleton, so the family of its unique arrows is a
   natural isomorphism. *)
Program Definition ChaoticBool_points_equiv :
  ChaoticBool_true ≈[Cat] ChaoticBool_false :=
  (fun _ => {| to := ttt; from := ttt |}; _).

Lemma EqCat_ChaoticBool_empty :
  obj[EqCat ChaoticBool_true ChaoticBool_false] → False.
Proof. intros [o e]; simpl in e; discriminate e. Qed.

(* The strict equalizer of two functors that are equivalent in [Cat] is
   empty, while the identity of [1] is a competing fork there; so it is not
   an equalizer in [Cat].  Read narrowly: this refutes THIS apex at THIS pair,
   and says nothing about whether [Cat] has equalizers. *)
Theorem EqCat_not_Cat_equalizer :
  @IsEqualizer Cat _1 ChaoticBool ChaoticBool_true ChaoticBool_false
    (EqCat ChaoticBool_true ChaoticBool_false)
    (EqIncl ChaoticBool_true ChaoticBool_false)
  → False.
Proof.
  intros K.
  assert (Hc : ChaoticBool_true ∘[Cat] Id[_1]
                 ≈[Cat] ChaoticBool_false ∘[Cat] Id[_1])
    by (rewrite ChaoticBool_points_equiv; reflexivity).
  exact (EqCat_ChaoticBool_empty (fobj[unique_obj (eq_desc K Id[_1] Hc)] ttt)).
Qed.

End WeakAmbient.
