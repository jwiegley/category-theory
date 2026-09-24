Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Pullback.Wide.Complete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(** * Well-powered and co-well-powered categories *)

(* nLab:      https://ncatlab.org/nlab/show/well-powered+category
   nLab:      https://ncatlab.org/nlab/show/subobject
   Wikipedia: https://en.wikipedia.org/wiki/Subobject

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   book p. 130 (PDF p. 139): a category is WELL-POWERED when the subobjects
   of each object form a small set, and CO-WELL-POWERED when the quotient
   objects of each object do.  The notion is the size hypothesis of the
   special adjoint functor theorem: with it, a small-complete category has
   the intersection of any collection of subobjects of an object, because
   the collection can be reindexed by a small set before the wide pullback
   is taken.  mathlib states the same thing as the class [WellPowered.{w}],
   asking that [Subobject X] be [w]-small, and names [w] = the hom
   universe as the common case.

   ** The definition, and where its content lies

   A subobject of x is Theory/Subobject.v's [SubObj x], a mono into x, and
   two subobjects are the same when the setoid [SubObj_Setoid] relates
   them (an isomorphism of domains over x).  "The subobjects of x form a
   small set" is read here as a small INDEX together with maps both ways
   that EXHAUST the subobjects: [WellPoweredAt x] carries [wp_index],
   [wp_to : wp_index → SubObj x], [wp_from : SubObj x → wp_index] and the
   exhaustiveness clause [wp_to_from : wp_to (wp_from u) ≈ u].  That is a
   bijection onto the setoid of ALL subobjects: pulling [SubObj_Setoid]
   back along [wp_to] ([wp_index_setoid]) makes [wp_to] respect and
   reflect the equivalence by definition, [wp_from] respect it
   ([wp_from_resp]) and [wp_from ∘ wp_to] the identity up to it
   ([wp_from_to]).  No second record repeats those fields: the one clause
   that cannot be derived is exhaustiveness.

   Adjunction/SAFT.v's [SubobjectIndex] is the family of monos WITHOUT the
   exhaustiveness clause, and so is strictly weaker: the empty family
   inhabits it at every object (that file's [empty_SubobjectIndex] and
   [SubobjectIndex_not_exhaustive]).  The bridge from [WellPowered] to it
   is the satellite Adjunction/SAFT/WellPowered.v's
   [WellPowered_SubobjectIndex], with [SAFT_of_WellPowered] beside it.

   The content of the definition is its UNIVERSE.  Left free, the index can
   be [SubObj x] itself with [wp_to] and [wp_from] the identity
   ([wp_trivial] below), and every category is "well-powered".
   [WellPowered] therefore pins the index at or below the hom universe,
   [w <= h]: the book's small sets are the size of its hom-sets,
   mathlib's common case is the same, and Adjunction/SAFT.v's statement
   of [SAFT] already puts the bound [u3 <= h] on its [SubobjectIndex]
   datum.  The
   per-object record [WellPoweredAt] is left unpinned so that a witness
   one universe up can still be STATED, and compared with the pinned
   notion.

   "Small" is therefore relative to the category's OWN hom universe, as in
   mathlib's [WellPowered.{v}].  A category whose hom universe is a free
   parameter, as a thin category's is, can be instantiated with its homs
   raised, and then passes the pin: Structure/WellPowered/
   Counterexample.v's [AntichainTop] is refuted at the pin when its homs
   sit at or below the types its objects name, and its top object has a
   pinned datum when they sit above ([AntichainTop_WellPoweredAt_up]); the
   powerset lattices of Instance/Powerset/WellPowered.v are well-powered
   through [trivial_small] once the homs are raised to the objects.  The
   pin excludes something only where the hom universe is tied to the
   objects' carriers, as in [Sets] and the algebraic categories, or where
   a free one is instantiated low.

   [CoWellPowered C] is [WellPowered (C^op)], and its subobjects are
   Theory/Subobject/Quotient.v's quotient objects on the nose:
   [quot_obj_is_sub_op] and [quot_setoid_is_sub_setoid_op] hold by
   [eq_refl].

   ** The consequence: intersections

   The consequence named at the head of this essay -- a well-powered
   small-complete category has the intersection of any collection of
   subobjects of an object -- is proved below in two forms, and the
   difference between them is the content of well-poweredness.

   SMALL FAMILIES NEED NO WELL-POWEREDNESS.  [complete_intersection] and
   [complete_intersection_IsIntersection] intersect EVERY family
   [S : J → SubObj x] whose index lies at or below [Complete]'s
   shape-object universe, from completeness alone: the wide pullback of
   the monos comes from Structure/Pullback/Wide/Complete.v's
   [complete_wide_pullback], and Theory/Subobject/Lattice.v's
   [sub_wide_intersection] reads it as a subobject.  That reading needs a
   point of the index, so the family is first extended by [sub_top] over
   [option J] ([sub_opt_top]); adding the top changes no lower bound
   ([IsIntersection_drop_top]), so the empty family is covered too, with
   no nonemptiness hypothesis.  A statement about families indexed at
   [Complete]'s own shape universe is therefore NOT the §V.8 consequence.

   CLASSES OF SUBOBJECTS NEED IT.  A "collection of subobjects" is a
   collection of equivalence classes; in setoid discipline it is a
   predicate [P] on the large type [SubObj x] closed under ≈ ([HP]).  Its
   members form a
   family indexed by [{ m : SubObj x & P m }], which lives at the OBJECT
   universe, above the shape universe whenever objects sit above homs.
   [wellpowered_complete_has_intersections] intersects it by reindexing
   over the small [wp_class_index] = [{ i : wp_index W & P (wp_to W i) }]:
   [IsIntersection_reindex] carries membership along [wp_to (wp_from m) ≈
   m] with [HP] and the bound back with [sub_le_of_equiv].  Only the four
   fields of [WellPoweredAt] are consumed; the derived bijection is not
   needed.  The [Prop]-valued form ([_prop]) puts no size condition on
   [P]; [wellpowered_complete_intersection_all] is the class of ALL
   subobjects, indexed by [SubObj x] itself, and
   [wellpowered_complete_least_subobject] reads it as the least subobject.
   Necessity is measured, in scratch files at the regime the adjoint
   functor theorems use ([C : Category@{o h h}], [h < o],
   [comp : Complete@{h h h o}]): [complete_intersection_IsIntersection
   comp (fun k : { m : SubObj x & P m } => `1 k)] is refused with "cannot
   ensure that Type@{max(o,h)} is a subtype of Type@{...}", and so is the
   identity family on [SubObj x], while [wellpowered_complete_has_
   intersections] and [wellpowered_complete_intersection_all] are
   accepted at the same regime given [WellPowered C]; at [Sets@{o so}]
   with [Sets_Complete], the identity family on [SubObj X] is refused
   with "Cannot enforce o = ... because o < so <= ..." (the chain as
   printed with [X : Sets@{o so}] a [Section] [Context]; with [X] a
   binder of the definition, Rocq 9.1.1 prints an unnamed universe in
   the place of [so], as Test/ProbeWellPowered451.v's N7 records), and
   accepted through [wellpowered_complete_intersection_all] given
   [WellPowered Sets].

   WHY CLASSES AND NOT ARBITRARY LARGE FAMILIES.  For [S : J → SubObj x]
   with [J : Type@{o}], two readings suggest themselves, and both are
   refused (measured at the same regime).  The typed image [fun m => { j
   : J & S j ≈ m }] is as large as [J]: "Cannot enforce o <= ... because
   ... < o".  The [Prop]-truncated image [fun m => ex (fun j => inhabited
   (S j ≈ m))] is ≈-closed and IS accepted, and its intersection is a
   lower bound of every [S j]; but showing a lower bound of [S] to be below
   it needs a member of [S] out of the truncated witness, and that step is
   refused with "Incorrect elimination ... in the inductive type ex ...
   the return type has sort Type@{h} while it should be SProp or Prop"
   (as printed under [Set Printing Universes] with [h] a named universe;
   the default printing gives "Type" in place of "Type@{h}").
   That route needs unique choice to eliminate the truncated witness into
   the [Type]-valued [sub_le]; no other route was measured, and nothing
   here shows that every route needs it.  The class form is both the
   faithful reading of the book and the strongest form proved here.

   THE DUAL.  [cowellpowered_cocomplete_has_cointersections] is the
   theorem read at [C^op] through Construction/Product/Limit.v's
   [Complete_op_of_Cocomplete], in one line; [cointersection_quot_le]
   reads its lower bound in Theory/Subobject/Quotient.v's [quot_le] with no
   conversion step.  The result is called a cointersection here;
   Quotient.v calls the same greatest lower bound in [quot_le]
   [quot_wide_meet].

   STRENGTHS, measured.  The intersection is data: [IsIntersection]
   carries the [sub_le] factorizations, and every constant of this file
   that builds them is [Defined].  Not all of it computes.  The
   criterion is [eq_refl] at a category where the answer is known,
   [Indiscrete bool] completed by [Indiscrete_Complete true], every hom
   being [unit]:

     - the lower-bound half computes.  The product mediators of
       Structure/Pullback/Wide/Complete.v ([unique_obj (iprod_ump ...)])
       and the legs [wide_pullback_proj (complete_wide_pullback comp f) j]
       reduce to [tt] by [eq_refl].  Every [inter_le] of
       [complete_intersection] is such a leg, and the class form composes
       it with the isomorphism of [wp_to_from], which computes as far as
       the witness's own exhaustiveness proof does;
     - the greatest-lower-bound half does not.  The wide pullback's
       mediator [unique_obj (ump_wide_pullbacks (complete_wide_pullback
       comp f) q Hq)], from which every [inter_greatest] factorization is
       built, is refused at [eq_refl] by conversion ("cannot unify ...
       and ()"), and [Eval cbv] stops at [unique_obj (eq_desc
       (equalizer_of_pullback_awodey ...))].  Structure/Pullback/
       Reduction.v's [equalizer_of_pullback_awodey] is [Qed] and returns
       an [IsEqualizer], whose [eq_desc] is the equalizer's mediator: the
       factorization is data that reduces only up to that opaque
       constant.  Adjunction/GAFT.v's [Complete_HasEqualizers] would not
       help: at the same category its mediator stops at Structure/
       Equalizer/Fork.v's [limit_equalizer_desc], also [Qed].

   [Print Opaque Dependencies wellpowered_complete_has_intersections]
   lists 63 constants.  Besides [equalizer_of_pullback_awodey], two more
   carry data: Theory/Subobject.v's [SubObj_Setoid_obligation_1], the
   equivalence on subobjects, whose members are isomorphisms, and
   Structure/Pullback/Limit.v's [Pullback_to_Universal_obligation_2], an
   [∃!] mediator; reading the statements of the rest, they are
   ≈-equations, monicity, [Program] obligations of the shapes, and
   setoid-rewriting lemmas.  Making the factorizations compute would
   start with flipping [equalizer_of_pullback_awodey] to [Defined]; that
   is not attempted here.  The subobject that
   [wellpowered_complete_has_intersections] returns IS, by [eq_refl], the
   [complete_intersection] of the small reindexed family
   ([wellpowered_intersection_is_small]).  Uniqueness is Lattice.v's
   [IsIntersection_unique], up to ≈ and not re-proved here.

   UNIVERSES, measured with [Set Printing Universes. About ...], stdlib
   bounds omitted.  In the first, unannotated elaboration minimization
   collapsed universes the statements keep apart: the index [w] onto the
   hom universe and [r] onto [so] in [wellpowered_complete_has_
   intersections] and in [cointersection_quot_le], the family index [q]
   onto [s] in [wellpowered_complete_intersection_all], and the index [j]
   onto [so] in [complete_intersection_IsIntersection].  The binders are
   therefore load-bearing:

     wellpowered_complete_has_intersections@{o h w s t r so p q u u0 u1 u2} :
       ∀ {C : Category@{o h h}}, WellPowered@{o h w s t} C →
       Complete@{r so h o} → ∀ (x : obj[C]) (P : SubObj@{o h} x → Type@{p}),
       (∀ m m', m ≈ m' → P m → P m') →
       ∃ w, IsIntersection@{o h q} (λ k : ∃ m, P m, `1 k) w
     (* w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
        o <= q, h <= q, p <= q, and internal ones *)

   The two bounds that matter are [w <= so] and [p <= so]: the index and
   the class's universe must fit [Complete]'s shape objects.  Nothing ties
   [h] to [so], and at the adjoint-functor regime ([so = h]) the pin
   [w <= h] is exactly what is asked.  [complete_intersection@{o h r so j
   ...}] carries [j <= so] for the family's index [j], and nothing else of
   note.

   ** Witnesses

   [trivial_small]: a category whose objects sit at or below its homs is
   well-powered ([o <= h]), with the trivial index.  [wp_groupoid] and
   [Groupoid_WellPowered]: a category in which every arrow is invertible
   (Structure/Groupoid.v's [IsGroupoid]) is well-powered with the
   one-point index, at EVERY object universe; its opposite is again one
   ([IsGroupoid_op] of Structure/Groupoid.v), so [Groupoid_CoWellPowered] too.  Instances:
   [DiscreteCat_WellPowered], [Indiscrete_WellPowered] and their
   co-well-powered twins, and [DiscreteCat_types_WellPowered] at
   [DiscreteCat@{o j j} Type@{j}], objects strictly above homs with the
   index at [Set].  [wp_of_classifier] and [Classifier_WellPowered]: a
   subobject classifier over pullbacks indexes the subobjects of x by
   [x ~> Ω], at the hom universe with no bound between objects and homs;
   Instance/FinSet/WellPowered.v instantiates it at FinSet.  The
   refutation side is Structure/WellPowered/Counterexample.v: a thin
   category, [AntichainTop], built without axioms, that is provably not
   well-powered at the pin.

   Elsewhere in tree: Instance/Sets/WellPowered.v ([Sets] well-powered
   and co-well-powered one universe up, well-powered at the pin under
   [Untruncate], and the consequence at [Sets] under the same
   hypothesis), Instance/Grp/WellPowered.v ([Grp] well-powered one
   universe up), Instance/Powerset/WellPowered.v (the consequence at the
   powerset lattice of a setoid, unconditionally), Adjunction/SAFT/
   WellPowered.v (the bridge to Adjunction/SAFT.v's [SubobjectIndex]),
   and, since #452, Adjunction/SAFT/InitialObject.v (the special
   initial-object theorem's well-powered corollary) with its witnesses
   Adjunction/SAFT/InitialObject/Examples.v and Instance/Sets/
   SpecialInitial.v; and, since #454, Instance/Mod/WellPowered.v ([RMod R]
   well-powered and co-well-powered one universe up unconditionally, and
   both at the pin under [Untruncate]).

   ** Non-vacuity of the consequence

   The tree's [Complete] instances were searched (every definition of a
   constant named [*Complete*] with type [@Complete ...] under Instance/,
   Structure/ and Construction/) for one that is well-powered at the pin
   in a form the theorem accepts, as written.  [Sets] and [Grp] are
   shown well-powered constructively only one universe up (Instance/Sets/
   WellPowered.v's [Sets_WellPoweredAt_up], Instance/Grp/WellPowered.v's
   [Grp_WellPoweredAt_up]; this parenthesis said "the other algebraic
   categories were not measured", which is corrected here: since #454
   Instance/Mod/WellPowered.v shows [RMod R] well-powered one universe up
   unconditionally ([RMod_WellPoweredAt_up]) and at the pin under
   [Untruncate] ([RMod_WellPowered_untruncate]), and co-well-powered the
   same two ways ([RMod_CoWellPoweredAt_up],
   [RMod_CoWellPowered_untruncate]), and the remaining algebraic
   categories are still unmeasured), and [Sets] is well-powered
   at the pin only under [Untruncate] ([Sets_WellPowered_untruncate]);
   the presheaf categories of [Presheaf_Complete] have a classifier only
   under a hypothesis:
   Instance/Fun/Classifier.v's [Fun_Classifier] takes [Untruncate] and
   its [Fun_Classifier_IEM] takes [IEM].  [SmallOrd_op_Complete]
   (Instance/Ordinal/Large.v) is thin and [trivial_small] applies to it
   with the homs raised to the objects, but its shape-object universe
   lies strictly below its objects, and feeding that witness to
   [wellpowered_complete_intersection_all] is refused with "Cannot
   enforce ... = ... because ... < ..." (measured).  [Subsets_Complete]
   (Instance/Powerset.v) is written with its homs at [Set] and its
   objects above; restated at a free hom level it is Instance/Powerset/
   WellPowered.v's [Subsets_Complete_free], and that satellite applies
   the theorem at the powerset lattice of any setoid, unconditionally and
   non-degenerately ([Subsets_intersection_all_not_top]), with the
   objects at or below the homs so that [trivial_small] is the witness.
   This file supplies the instance with objects strictly above homs:
   [Indiscrete_Complete] makes every inhabited indiscrete category
   complete, and [Indiscrete_types_has_intersections] applies the theorem
   at [Indiscrete@{o j j} Type@{j}] ([j < o]), where [trivial_small] is
   out of reach.  That instance is degenerate (every subobject there is
   the top one).  Of the instances of the consequence in tree, none has
   both objects strictly above homs and a non-degenerate subobject
   lattice unconditionally; Instance/Sets/WellPowered.v's
   [Sets_wellpowered_intersection] has both under [Untruncate].

   ** Not delivered

   No well-poweredness witness for [Sets], [Grp] or any algebraic
   category in this file (they are the satellites named under Witnesses).
   No intersection theorem over [FinitelyComplete] or over a
   [HasWidePullbacks] that is not derived from [Complete];
   Theory/Subobject/Lattice.v's [sub_intersection] already covers the
   latter for small NONEMPTY families (it takes a point of the index;
   [sub_opt_top] is how this file avoids needing one).  No statement that
   a well-powered category has intersections of ARBITRARY large families,
   for the reason given above.  No wide-pushout
   vocabulary: the dual runs through [C^op], exactly as Quotient.v's
   [quot_wide_meet] does. *)

Record WellPoweredAt {C : Category} (x : C) := {
  wp_index   : Type;
  wp_to      : wp_index → SubObj x;
  wp_from    : SubObj x → wp_index;
  wp_to_from : ∀ u : SubObj x, wp_to (wp_from u) ≈ u
}.

Arguments wp_index {C x} _.
Arguments wp_to {C x} _ _.
Arguments wp_from {C x} _ _.
Arguments wp_to_from {C x} _ _.

(** ** The bijection onto all subobjects *)

Section Bijection.

Context {C : Category} {x : C} (W : WellPoweredAt x).

(* The index setoid: two indices are equal when the subobjects they name
   are. *)
Definition wp_rel : crelation (wp_index W) :=
  fun i j => wp_to W i ≈ wp_to W j.

Lemma wp_rel_equiv : Equivalence wp_rel.
Proof.
  unfold wp_rel; constructor.
  - intro i; reflexivity.
  - intros i j H; symmetry; exact H.
  - intros i j k H1 H2; etransitivity; [exact H1 | exact H2].
Defined.

Definition wp_index_setoid : Setoid (wp_index W) :=
  {| equiv := wp_rel; setoid_equiv := wp_rel_equiv |}.

Lemma wp_to_resp (i j : wp_index W) :
  @equiv _ wp_index_setoid i j → wp_to W i ≈ wp_to W j.
Proof. intro H; exact H. Qed.

Lemma wp_from_resp (u v : SubObj x) :
  u ≈ v → @equiv _ wp_index_setoid (wp_from W u) (wp_from W v).
Proof.
  intro H; simpl; unfold wp_rel.
  etransitivity; [exact (wp_to_from W u)|].
  etransitivity; [exact H|].
  symmetry; exact (wp_to_from W v).
Qed.

Lemma wp_from_to (i : wp_index W) :
  @equiv _ wp_index_setoid (wp_from W (wp_to W i)) i.
Proof. exact (wp_to_from W (wp_to W i)). Qed.

End Bijection.

(** ** The pinned notion *)

(* [w] is the index universe, pinned at or below the hom universe [h];
   [s] and [t] are the two universes of [SubObj_Setoid].  The trailing
   [+] in both constraint lists is load-bearing on Coq 8.19 and 8.20,
   where [sigT] and [eq] carry global universes: without it both
   toolchains refuse the declaration with "Universe constraints are not
   implied by the ones declared: h <= sigT.u0, h <= sigT.u1, h <= eq.u0"
   (measured).  On Rocq 9.1 the block read back is the same four
   constraints with or without it. *)

Definition WellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) :=
  ∀ x : C, WellPoweredAt@{w o s h t} x.

Definition CoWellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) :=
  WellPowered@{o h w s t} (C^op).

(** ** Co-well-powered is well-powered over the quotient objects *)

Section Quotients.

Context {C : Category} {x : C}.

Example quot_obj_is_sub_op : @QuotObj C x = @SubObj (C^op) x := eq_refl.

Example quot_setoid_is_sub_setoid_op :
  @QuotObj_Setoid C x = @SubObj_Setoid (C^op) x := eq_refl.

(* Exhaustiveness read in the quotient setoid, with no conversion step. *)
Lemma cowp_to_from (W : @WellPoweredAt (C^op) x) (q : QuotObj x) :
  @equiv _ (@QuotObj_Setoid C x) (wp_to W (wp_from W q)) q.
Proof. exact (wp_to_from W q). Qed.

End Quotients.

(** ** Intersections of small families need no well-poweredness *)

(* Adjoining the top subobject to a family changes none of its lower
   bounds, and it gives the index a point ([None]), which Theory/Subobject/
   Lattice.v's [sub_wide_intersection] needs to read a wide pullback as a
   subobject. *)

Section SmallIntersections.

Context {C : Category} {x : C}.

Definition sub_opt_top {J : Type} (S : J → SubObj x) : option J → SubObj x :=
  fun o => match o with Some j => S j | None => sub_top end.

Lemma IsIntersection_drop_top {J : Type} (S : J → SubObj x) (w : SubObj x) :
  IsIntersection (sub_opt_top S) w → IsIntersection S w.
Proof.
  intros H; constructor.
  - intro j; exact (inter_le _ _ H (Some j)).
  - intros v Hv; apply (inter_greatest _ _ H).
    intros [j|]; [exact (Hv j) | exact (sub_top_greatest v)].
Defined.

End SmallIntersections.

(* The intersection of ANY family indexed at or below [Complete]'s
   shape-object universe, empty or not, from completeness alone. *)
Definition complete_intersection@{o h r so j +| so <= r, h <= r, j <= so +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C) {x : C}
  {J : Type@{j}} (S : J → SubObj x) : SubObj x :=
  sub_wide_intersection (sub_opt_top S) None
    (complete_wide_pullback comp
       (fun o => Subobject.sub_mono (sub_opt_top S o))).

Definition complete_intersection_IsIntersection@{o h r so j +|
    so <= r, h <= r, j <= so +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C) {x : C}
  {J : Type@{j}} (S : J → SubObj x) :
  IsIntersection@{o h j} S (complete_intersection comp S) :=
  IsIntersection_drop_top S _
    (sub_wide_intersection_IsIntersection (sub_opt_top S) None
       (complete_wide_pullback comp
          (fun o => Subobject.sub_mono (sub_opt_top S o)))).

(** ** The consequence: intersections of classes of subobjects *)

(* A collection of subobjects is a collection of equivalence classes; in
   setoid discipline, a predicate [P] on the large type [SubObj x] that is
   closed under ≈.  Its members are intersected by reindexing them over the
   SMALL index [{ i : wp_index W & P (wp_to W i) }] and taking the wide
   pullback there. *)

Section ClassIntersection.

Context {C : Category} {x : C}.
Context (W : WellPoweredAt x).
Context (P : SubObj x → Type).
Context (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m').

Definition wp_class_index : Type := { i : wp_index W & P (wp_to W i) }.

Definition wp_class_family (k : wp_class_index) : SubObj x := wp_to W (`1 k).

(* A lower bound of the representatives is a lower bound of the class:
   [HP] carries membership along [wp_to (wp_from m) ≈ m] to the
   representative, and [sub_le_of_equiv] carries the bound back. *)
Lemma IsIntersection_reindex (w : SubObj x) :
  IsIntersection wp_class_family w →
  IsIntersection (fun k : { m : SubObj x & P m } => `1 k) w.
Proof using HP.
  intros H; constructor.
  - intros [m p]; simpl.
    exact (sub_le_trans _ _ _
             (inter_le _ _ H
                (wp_from W m; HP m (wp_to W (wp_from W m))
                                (symmetry (wp_to_from W m)) p))
             (sub_le_of_equiv _ _ (wp_to_from W m))).
  - intros v Hv; apply (inter_greatest _ _ H).
    intros [i p]; exact (Hv (wp_to W i; p)).
Defined.

End ClassIntersection.

(* The per-object form: one object's well-poweredness datum suffices. *)
Definition wp_complete_class_intersection@{o h w s t r so p q +|
    h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= q, h <= q, p <= q +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  {x : C} (W : WellPoweredAt@{w o s h t} x) (P : SubObj x → Type@{p})
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w }.
Proof.
  exists (complete_intersection comp (wp_class_family W P)).
  exact (IsIntersection_reindex W P HP _
           (complete_intersection_IsIntersection comp _)).
Defined.

(* §V.8, as #451 reads it: a well-powered complete category has the
   intersection of every class of subobjects of every object. *)
Definition wellpowered_complete_has_intersections@{o h w s t r so p q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= q, h <= q, p <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C)
  (P : SubObj x → Type@{p}) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wp_complete_class_intersection comp (WP x) P HP.

(* The intersection IS the wide pullback over the small index. *)
Example wellpowered_intersection_is_small {C : Category}
  (WP : WellPowered C) (comp : @Complete C) (x : C)
  (P : SubObj x → Type) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  `1 (wellpowered_complete_has_intersections WP comp x P HP)
    = complete_intersection comp (wp_class_family (WP x) P) := eq_refl.

(* The same for a [Prop]-valued class, which carries no size condition. *)
Definition wellpowered_complete_has_intersections_prop@{o h w s t r so q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so,
    o <= q, h <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C)
  (P : SubObj x → Prop) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections WP comp x P HP.

(* The intersection of ALL subobjects, indexed by the large type [SubObj x]
   itself: the class [fun _ => True]. *)
Definition wellpowered_complete_intersection_all@{o h w s t r so q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so,
    o <= q, h <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C) :
  { w : SubObj x & IsIntersection@{o h q} (fun m : SubObj x => m) w }.
Proof.
  pose (R := wellpowered_complete_has_intersections_prop
               WP comp x (fun _ => True) (fun _ _ _ t => t)).
  exists (`1 R); constructor.
  - intro m; exact (inter_le _ _ (`2 R) (m; I)).
  - intros v Hv; apply (inter_greatest _ _ (`2 R)).
    intros [m t]; exact (Hv m).
Defined.

(* ... which is the least subobject. *)
Definition wellpowered_complete_least_subobject@{o h w s t r so +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C) :
  { w : SubObj x & ∀ v : SubObj x, sub_le w v }.
Proof.
  exists (`1 (wellpowered_complete_intersection_all
                WP comp x)).
  exact (inter_le _ _
           (`2 (wellpowered_complete_intersection_all
                  WP comp x))).
Defined.

(** ** The dual: cointersections of classes of quotient objects *)

Definition cowellpowered_cocomplete_has_cointersections@{o h w s t r so qo p q
    +| w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= qo, h <= qo, qo <= q, p <= q +}
  {C : Category@{o h h}}
  (CWP : CoWellPowered@{o h w s t} C) (cocomp : @Cocomplete@{r so h o} C)
  (x : C) (P : QuotObj@{qo o h} x → Type@{p})
  (HP : ∀ q q' : QuotObj x, q ≈ q' → P q → P q') :
  { w : QuotObj@{qo o h} x &
    @IsIntersection@{o h q} (C^op) x _
      (fun k : { q : QuotObj x & P q } => `1 k) w } :=
  wellpowered_complete_has_intersections CWP
    (Complete_op_of_Cocomplete cocomp) x P HP.

(* Read in the order of quotients, with no conversion step: the
   cointersection lies below every member of the class in [quot_le]. *)
Lemma cointersection_quot_le@{o h w s t r so qo p q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= qo, h <= qo, qo <= q, p <= q +}
  {C : Category@{o h h}}
  (CWP : CoWellPowered@{o h w s t} C) (cocomp : @Cocomplete@{r so h o} C)
  (x : C) (P : QuotObj@{qo o h} x → Type@{p})
  (HP : ∀ q q' : QuotObj x, q ≈ q' → P q → P q')
  (q : QuotObj x) (p : P q) :
  quot_le (`1 (cowellpowered_cocomplete_has_cointersections CWP cocomp x P HP))
    q.
Proof.
  exact (inter_le _ _
           (`2 (cowellpowered_cocomplete_has_cointersections CWP cocomp x P HP))
           (q; p)).
Defined.

(** ** Witnesses *)

(* The trivial datum: the index is [SubObj x] itself.  It exists at every
   object of every category, one universe too high to be [WellPowered] in
   general; [trivial_small] is the case where it is not too high. *)
Definition wp_trivial@{o h w s t | o <= w, h <= w, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} (x : C) : WellPoweredAt@{w o s h t} x :=
  {| wp_index   := SubObj x;
     wp_to      := fun u => u;
     wp_from    := fun u => u;
     wp_to_from := fun u => Equivalence_Reflexive u |}.

(* A category whose objects sit at or below its homs is well-powered. *)
Definition trivial_small@{o h t | o <= h, h < t +}
  (C : Category@{o h h}) : WellPowered@{o h h h t} C :=
  fun x => wp_trivial x.

(* A category in which every arrow is invertible (Structure/Groupoid.v's
   [IsGroupoid]) is well-powered with the one-point index: every subobject
   is the top one. *)
Section Groupoid.

Context {C : Category}.
Context (G : IsGroupoid C).

Definition wp_groupoid (x : C) : WellPoweredAt x.
Proof using G.
  unshelve refine {| wp_index := Datatypes.unit;
                     wp_to    := fun _ => sub_top;
                     wp_from  := fun _ => tt |}.
  intro u.
  unshelve eexists.
  - exact (iso_sym (IsIsoToIso (Subobject.sub_mono u)
                                (G _ _ (Subobject.sub_mono u)))).
  - simpl; exact is_right_inverse.
Defined.

End Groupoid.

(* The pinned forms.  The one-point index sits at [Set], below every hom
   universe, so no bound relates the objects to the homs. *)
Definition Groupoid_WellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) (G : IsGroupoid C) :
  WellPowered@{o h w s t} C :=
  fun x => wp_groupoid G x.

(* A groupoid's opposite is a groupoid, with the same inverses:
   Structure/Groupoid.v's [IsGroupoid_op]. *)
Definition Groupoid_CoWellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) (G : IsGroupoid C) :
  CoWellPowered@{o h w s t} C :=
  Groupoid_WellPowered@{o h w s t} (C^op) (IsGroupoid_op G).

(* Discrete categories: every arrow is an equality proof, inverted by
   [eq_sym]. *)
Definition DiscreteCat_isos@{o h} (A : Type@{o})
  (a b : DiscreteCat@{o h h} A) (f : a ~> b) : IsIsomorphism f.
Proof.
  exists (eq_sym f); destruct f; reflexivity.
Defined.

Definition DiscreteCat_WellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : WellPowered@{o h w s t} (DiscreteCat@{o h h} A) :=
  Groupoid_WellPowered@{o h w s t} (DiscreteCat@{o h h} A) (DiscreteCat_isos A).

Definition DiscreteCat_CoWellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : CoWellPowered@{o h w s t} (DiscreteCat@{o h h} A) :=
  Groupoid_CoWellPowered@{o h w s t} (DiscreteCat@{o h h} A)
    (DiscreteCat_isos A).

(* The objects are the types of [Type@{j}], one universe above the homs,
   which sit at [j]; the index is at [Set]. *)
Definition DiscreteCat_types_WellPowered@{j o t | j < o, j < t +} :
  WellPowered@{o j Set o t} (DiscreteCat@{o j j} Type@{j}) :=
  DiscreteCat_WellPowered@{o j Set o t} Type@{j}.

(* Indiscrete categories: every arrow is [tt], inverted by [tt]. *)
Definition Indiscrete_isos@{o h} (A : Type@{o})
  (a b : Indiscrete@{o h h} A) (f : a ~> b) : IsIsomorphism f.
Proof.
  exists (tt : @hom (Indiscrete@{o h h} A) b a); destruct f; reflexivity.
Defined.

Definition Indiscrete_WellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : WellPowered@{o h w s t} (Indiscrete@{o h h} A) :=
  Groupoid_WellPowered@{o h w s t} (Indiscrete@{o h h} A) (Indiscrete_isos A).

Definition Indiscrete_CoWellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : CoWellPowered@{o h w s t} (Indiscrete@{o h h} A) :=
  Groupoid_CoWellPowered@{o h w s t} (Indiscrete@{o h h} A)
    (Indiscrete_isos A).

(* A subobject classifier over pullbacks indexes the subobjects of x by the
   arrows [x ~> Ω]: [wp_to] pulls [truth_subobject] back along the arrow,
   [wp_from] takes the characteristic map, and exhaustiveness is
   Structure/SubobjectClassifier.v's [classifier_pullback_roundtrip].  The
   index is a hom-set, so it sits at the hom universe with no bound between
   objects and homs. *)
Definition wp_of_classifier {C : Category} `{T : @Terminal C}
  `{PB : @HasPullbacks C} `{S : @SubobjectClassifier C T} (x : C) :
  WellPoweredAt x :=
  {| wp_index   := x ~> Ω;
     wp_to      := fun f => sub_reindex f truth_subobject;
     wp_from    := fun u => char (Subobject.sub_mono u) (sub_is_monic u);
     wp_to_from := fun u => classifier_pullback_roundtrip u |}.

Definition Classifier_WellPowered@{o h s t | o <= s, h <= s, h < t +}
  (C : Category@{o h h}) `{T : @Terminal C} `{PB : @HasPullbacks C}
  `{S : @SubobjectClassifier C T} : WellPowered@{o h h s t} C :=
  fun x => wp_of_classifier x.

(** ** Non-vacuity of the consequence *)

(* An inhabited indiscrete category is complete: the limit of every diagram
   is any object, with the only possible legs. *)
Definition Indiscrete_Complete@{r so h o +| so <= r, h <= r +}
  {A : Type@{o}} (a : A) : @Complete@{r so h o} (Indiscrete@{o h h} A).
Proof.
  intros D F.
  unshelve refine {| limit_cone :=
    @Build_Cone D (Indiscrete A) F a
      (@Build_ACone D (Indiscrete A) a F (fun _ => tt) _) |}.
  - intros; reflexivity.
  - intro N.
    unshelve eapply Build_Unique.
    + exact tt.
    + intro y.
      destruct (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) y); reflexivity.
    + intros v _; destruct v; reflexivity.
Defined.

(* Both hypotheses of [wellpowered_complete_has_intersections] at once, at a
   category whose objects, the types of [Type@{j}], sit one universe above
   its homs; the trivial witness is out of reach there. *)
Definition Indiscrete_types_has_intersections@{j o t q +|
    j < o, j < t, o <= q +}
  (x : Indiscrete@{o j j} Type@{j}) (P : SubObj x → Type@{j})
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o j q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections
    (Indiscrete_WellPowered@{o j Set o t} Type@{j})
    (Indiscrete_Complete@{j j j o} (Datatypes.unit : Type@{j})) x P HP.
