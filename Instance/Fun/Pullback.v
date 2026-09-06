Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Fun.

Generalizable All Variables.

Set Default Proof Using "All".

(** * Pointwise pullbacks in a functor category *)

(* Item 3 of the work list of Mac Lane §IV.9 construction 2 and remark 1
   (book pp. 105-106, [maclane:IV.9:construction2],
   [maclane:IV.9:remark1]) asks for the prerequisites a subobject
   classifier needs on a functor category, "terminal object and
   pullbacks, both pointwise".  The terminal object was already in tree
   as Instance/Fun/Terminal.v's [Functor_Category_Terminal] (#339); the
   pullbacks are here, and they were genuinely absent — before this file
   no [HasPullbacks], [Pullback] or [IsPullback] for ANY functor category
   existed anywhere, and Instance/Fun/Morphisms.v's own NOT DELIVERED
   paragraph said so at the base commit (it is amended in the same
   change that adds this file).  The refusal
   [Definition x : HasPullbacks ([_2, Sets]) := _.] is a RESOLUTION
   error, pinned in Test/ProbeFunClassifier403.v with
   [Fun_HasPullbacks Sets_HasPullbacks] as the accepted control.

   A NOTE ON WHO NEEDS THIS.  The subobject classifier of
   Instance/Fun/Classifier.v does NOT consume it: [SubobjectClassifier]
   takes only a category and a [Terminal], and the [HasPullbacks] of its
   declaring section is used by the theorems BELOW the class, not by the
   class.  What this file is for is those theorems — the two round trips
   of Structure/SubobjectClassifier.v, which Instance/Fun/Classifier.v
   states over [Fun_HasPullbacks Sets_HasPullbacks] — and
   Theory/Subobject/Functor.v's subobject presheaf, which takes a
   [HasPullbacks] of the ambient category.

   WHAT IS DELIVERED, AND IN WHICH ORDER.  The apex-pinned form comes
   FIRST and is the general one: [Fun_IsPullback] says that a square of
   natural transformations whose COMPONENTS are pullbacks in D is a
   pullback in [C, D], for an arbitrary D and with no [HasPullbacks]
   anywhere in its type (Theory/Morphisms/Stability.v's [IsPullback] is
   the predicate).  Only then is the chosen pointwise pullback built:
   [Fun_Pullback_Functor] with its two natural projections
   [Fun_Pullback_fst] / [Fun_Pullback_snd], the bundled
   [Fun_Pullback], and [Fun_HasPullbacks].  The bundled record is
   [is_pullback_pullback] of [Fun_IsPullback] applied to the componentwise
   [pullback_is_pullback], so the mediator is constructed ONCE, in
   [Fun_IsPullback], and not twice.

   REGISTRATION.  [Fun_HasPullbacks] is deliberately a plain
   [Definition] rather than an [Instance], following
   Instance/Fun/Terminal.v's [Fun_HasIndexedProducts] — and that file's
   own header is careful that the reason is an UNTESTED PRECAUTION rather
   than a measurement: registering a premise-carrying instance whose
   conclusion is headed by [Fun] could let resolution unify an unknown
   category with [Fun ?C ?D] and recurse, while its own neighbours
   [Functor_Category_Cartesian] and [Functor_Category_Terminal] are
   premise-carrying [#[export]] instances with [Fun]-headed conclusions
   and no divergence has been exhibited either way.  The same sentence
   applies here unchanged, and flipping it is a one-word change.  The
   consequence is visible: the RESOLUTION refusal pinned in the probe
   stays refused even with this file loaded, and the control names
   [Fun_HasPullbacks] explicitly.

   READBACKS.  Five [:= eq_refl] Examples pin that the construction is
   pointwise on the nose rather than up to an isomorphism: the pullback
   object's value at c IS D's chosen pullback of the components, each
   projection's component at c IS D's corresponding projection, and
   [pullback] of [Fun_HasPullbacks HP] IS [Fun_Pullback HP].  A FIFTH
   readback, [fun_pullback_med_strict], says the same of the MEDIATOR:
   its component at c IS D's mediator, at [eq_refl].  That was NOT
   expected — the prediction was a [≈]-only identification, on the ground
   that the bundled record reaches its universal property through
   [is_pullback_pullback] of [Fun_IsPullback] — and measurement refuted
   it: [is_pullback_pullback] is a field repackaging and
   [Build_Transform'] is transparent, so the whole chain reduces.  The
   [≈] form [fun_pullback_med_at] is kept beside it, being the shape a
   consumer rewrites with, and the probe carries the strict statement as
   a POSITIVE rather than as a refutation.

   UNIVERSES, off BOTH binder and block, and the two disagree — which is
   the point worth carrying.  [Fun_HasPullbacks@{u u0 u1 u2 u3 u4}] is
   over [C : Category@{u1 u4 u4}] and [D : Category@{u3 u4 u4}] — ONE
   level [u4] filling four slots, so C's hom, C's proof, D's hom and D's
   proof are all identified IN THE BINDER — while its constraint block
   carries NO equation at all, only bounds.  Reading the block alone
   reports no identification and is wrong.  The section constants
   [Fun_IsPullback], [Fun_Pullback_Functor], [Fun_Pullback] read the
   other way: their binders keep C and D at [Category@{u u0 u0}] and
   [Category@{u1 u2 u2}] while their BLOCKS carry the equation
   [u0 = u2], identifying the two categories' hom-and-proof levels.  That
   equation is [Fun]'s: [Fun@{...}]'s own block carries [u0 = u2], and
   the probe rejects [[Cu, Du]] under [Constraint ch < dh] while
   [@Functor Cu Du] is ACCEPTED at those very levels, so [Functor] is not
   a donor of it.  No constant of this file carries a word-bounded [Set]
   in any binder or block.

   COUNTS, WITH THEIR CRITERIA.  Constants closed under the global
   context: 24/24 with zero [Axioms:] lines, counted as the entries
   [Print Module] emits at five-space indent (the [Program] obligations,
   invisible to the [.glob], among them); this file declares no record,
   so there is no unlisted [Build_*]; every one queried FULLY QUALIFIED,
   and all 24 are in the [print-assumptions] gate.  [Defined]
   tokens: 4, and ALL FOUR are load-bearing — measured by flipping each
   ALONE to [Qed] and compiling the result alone: [Fun_IsPullback]'s flip
   stops the mediator readback [fun_pullback_med_strict] first and
   [fun_pullback_med_at] behind it; the functor's flip stops
   [Fun_Pullback_fst], and each projection's flip stops
   [Fun_Pullback_IsPullback].  Statements closed by
   [:= eq_refl]: 5.  Transitive in-project closure excluding this file:
   22 modules.  This file contributes ZERO [make todo] hits.

   NOT DELIVERED.  No CONVERSE: nothing says that an [IsPullback] in
   [C, D] has pullback components in D, and no separating example refutes
   it either — the honest form would take [HasPullbacks D] and compare
   with the pointwise pullback through the unique isomorphism, and
   nothing here does that.  No pushouts, no equalizers, no coequalizers.
   No [Complete] or [Cocomplete] for [C, D], and no general "limits in
   [C, D] are pointwise" theorem.  No [Cartesian_of_HasPullbacks_Terminal]
   instantiation.  No stability or pasting results for [C, D] beyond what
   Theory/Morphisms/Stability.v already gives generically.  No witness at
   a named pair of categories in this file: the concrete uses are
   Instance/Fun/Classifier.v's round trips at [[C^op, Sets]] and the
   probe's controls. *)

(* ------------------------------------------------------------------ *)
(** ** (A) Pointwise pullbacks give a pullback in [C, D] *)

Section FunIsPullback.

Context {C D : Category}.
Context {F G H P : C ⟶ D}.
Context (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H).
Context (p1 : P ~{[C, D]}~> F) (p2 : P ~{[C, D]}~> G).
Context (Hpt : ∀ x : C, IsPullback (transform[alpha] x) (transform[beta] x)
                          (P x) (transform[p1] x) (transform[p2] x)).

(* Two arrows into the apex agreeing on both legs agree: the standard
   consequence of the universal property, used to prove naturality of the
   mediator. *)
Lemma fpb_jointly_monic (x : C) {Z : D} (u v : Z ~> P x) :
  transform[p1] x ∘ u ≈ transform[p1] x ∘ v →
  transform[p2] x ∘ u ≈ transform[p2] x ∘ v → u ≈ v.
Proof.
  intros Hu Hv.
  assert (Hs : transform[alpha] x ∘ (transform[p1] x ∘ u)
                 ≈ transform[beta] x ∘ (transform[p2] x ∘ u)).
  { rewrite !comp_assoc. now rewrite (is_pullback_commutes (Hpt x)). }
  pose proof (is_pullback_ump (Hpt x) Z
                (transform[p1] x ∘ u) (transform[p2] x ∘ u) Hs) as U.
  transitivity (unique_obj U).
  - symmetry; apply (uniqueness U); split; reflexivity.
  - apply (uniqueness U); split; [ now rewrite <- Hu | now rewrite <- Hv ].
Qed.

Definition Fun_IsPullback : IsPullback alpha beta P p1 p2.
Proof.
  unshelve refine (Build_IsPullback ([C, D]) F G H alpha beta P p1 p2 _ _).
  - intro x; exact (is_pullback_commutes (Hpt x)).
  - intros Q q1 q2 Hq.
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine (@Build_Transform' C D Q P
        (fun x => unique_obj (is_pullback_ump (Hpt x) (Q x)
                    (transform[q1] x) (transform[q2] x) (Hq x))) _).
      intros x y h.
      set (mx := unique_obj (is_pullback_ump (Hpt x) (Q x)
                   (transform[q1] x) (transform[q2] x) (Hq x))).
      set (my := unique_obj (is_pullback_ump (Hpt y) (Q y)
                   (transform[q1] y) (transform[q2] y) (Hq y))).
      assert (Hmx1 : transform[p1] x ∘ mx ≈ transform[q1] x)
        by (unfold mx; now destruct (unique_property (is_pullback_ump (Hpt x)
              (Q x) (transform[q1] x) (transform[q2] x) (Hq x)))).
      assert (Hmx2 : transform[p2] x ∘ mx ≈ transform[q2] x)
        by (unfold mx; now destruct (unique_property (is_pullback_ump (Hpt x)
              (Q x) (transform[q1] x) (transform[q2] x) (Hq x)))).
      assert (Hmy1 : transform[p1] y ∘ my ≈ transform[q1] y)
        by (unfold my; now destruct (unique_property (is_pullback_ump (Hpt y)
              (Q y) (transform[q1] y) (transform[q2] y) (Hq y)))).
      assert (Hmy2 : transform[p2] y ∘ my ≈ transform[q2] y)
        by (unfold my; now destruct (unique_property (is_pullback_ump (Hpt y)
              (Q y) (transform[q1] y) (transform[q2] y) (Hq y)))).
      apply (fpb_jointly_monic y).
      * rewrite !comp_assoc.
        rewrite <- (@naturality _ _ _ _ p1 _ _ h).
        rewrite Hmy1, <- comp_assoc, Hmx1.
        apply (@naturality _ _ _ _ q1).
      * rewrite !comp_assoc.
        rewrite <- (@naturality _ _ _ _ p2 _ _ h).
        rewrite Hmy2, <- comp_assoc, Hmx2.
        apply (@naturality _ _ _ _ q2).
    + split; intro x; simpl;
        now destruct (unique_property (is_pullback_ump (Hpt x) (Q x)
                        (transform[q1] x) (transform[q2] x) (Hq x))).
    + intros v [Hv1 Hv2] x; simpl in *.
      apply (uniqueness (is_pullback_ump (Hpt x) (Q x)
               (transform[q1] x) (transform[q2] x) (Hq x))).
      split; [ apply Hv1 | apply Hv2 ].
Defined.

End FunIsPullback.

(* ------------------------------------------------------------------ *)
(** ** (B) The chosen pointwise pullback *)

Section FunPullback.

Context {C D : Category}.
Context (HP : @HasPullbacks D).
Context {F G H : C ⟶ D}.
Context (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H).

Definition fpb_at (x : C) :
  Pullback (transform[alpha] x) (transform[beta] x)
  := pullback (transform[alpha] x) (transform[beta] x).

Definition fpb_obj (x : C) : D := Pull _ _ (fpb_at x).
Definition fpb_fst (x : C) : fpb_obj x ~> F x := pullback_fst _ _ (fpb_at x).
Definition fpb_snd (x : C) : fpb_obj x ~> G x := pullback_snd _ _ (fpb_at x).

Lemma fpb_commutes (x : C) :
  transform[alpha] x ∘ fpb_fst x ≈ transform[beta] x ∘ fpb_snd x.
Proof. exact (pullback_commutes _ _ (fpb_at x)). Qed.

(* The square the arrow action factors through: the two naturality
   squares of alpha and beta plus the pointwise commuting square. *)
Lemma fpb_arr_sq {x y : C} (h : x ~> y) :
  transform[alpha] y ∘ (fmap[F] h ∘ fpb_fst x)
    ≈ transform[beta] y ∘ (fmap[G] h ∘ fpb_snd x).
Proof.
  rewrite !comp_assoc.
  rewrite <- (@naturality _ _ _ _ alpha _ _ h).
  rewrite <- (@naturality _ _ _ _ beta _ _ h).
  rewrite <- !comp_assoc.
  now rewrite fpb_commutes.
Qed.

Definition fpb_arr {x y : C} (h : x ~> y) : fpb_obj x ~> fpb_obj y :=
  unique_obj (ump_pullbacks _ _ (fpb_at y) (fpb_obj x)
                (fmap[F] h ∘ fpb_fst x) (fmap[G] h ∘ fpb_snd x)
                (fpb_arr_sq h)).

Lemma fpb_arr_fst {x y : C} (h : x ~> y) :
  fpb_fst y ∘ fpb_arr h ≈ fmap[F] h ∘ fpb_fst x.
Proof.
  unfold fpb_arr.
  now destruct (unique_property (ump_pullbacks _ _ (fpb_at y) (fpb_obj x)
                  (fmap[F] h ∘ fpb_fst x) (fmap[G] h ∘ fpb_snd x)
                  (fpb_arr_sq h))).
Qed.

Lemma fpb_arr_snd {x y : C} (h : x ~> y) :
  fpb_snd y ∘ fpb_arr h ≈ fmap[G] h ∘ fpb_snd x.
Proof.
  unfold fpb_arr.
  now destruct (unique_property (ump_pullbacks _ _ (fpb_at y) (fpb_obj x)
                  (fmap[F] h ∘ fpb_fst x) (fmap[G] h ∘ fpb_snd x)
                  (fpb_arr_sq h))).
Qed.

Lemma fpb_arr_uniq {x y : C} (h : x ~> y) (u : fpb_obj x ~> fpb_obj y) :
  fpb_fst y ∘ u ≈ fmap[F] h ∘ fpb_fst x →
  fpb_snd y ∘ u ≈ fmap[G] h ∘ fpb_snd x → u ≈ fpb_arr h.
Proof.
  intros H1 H2. unfold fpb_arr. symmetry.
  apply (uniqueness (ump_pullbacks _ _ (fpb_at y) (fpb_obj x)
           (fmap[F] h ∘ fpb_fst x) (fmap[G] h ∘ fpb_snd x) (fpb_arr_sq h))).
  now split.
Qed.

(* All three functor laws are the uniqueness clause of the pullback
   applied to the two legs. *)
Definition Fun_Pullback_Functor : C ⟶ D.
Proof.
  unshelve refine (@Build_Functor C D fpb_obj (@fpb_arr) _ _ _).
  - intros x y h1 h2 Hh.
    apply fpb_arr_uniq.
    + rewrite fpb_arr_fst. now rewrite Hh.
    + rewrite fpb_arr_snd. now rewrite Hh.
  - intros x. symmetry. apply fpb_arr_uniq.
    + rewrite fmap_id, id_left, id_right; reflexivity.
    + rewrite fmap_id, id_left, id_right; reflexivity.
  - intros x y z h1 h2. symmetry. apply fpb_arr_uniq.
    + rewrite comp_assoc, fpb_arr_fst, <- comp_assoc, fpb_arr_fst, comp_assoc.
      now rewrite fmap_comp.
    + rewrite comp_assoc, fpb_arr_snd, <- comp_assoc, fpb_arr_snd, comp_assoc.
      now rewrite fmap_comp.
Defined.

(* Naturality of each projection IS the defining equation of the arrow
   action, read backwards. *)
Definition Fun_Pullback_fst : Fun_Pullback_Functor ~{[C, D]}~> F.
Proof.
  unshelve refine (@Build_Transform' C D Fun_Pullback_Functor F fpb_fst _).
  intros x y h. simpl. symmetry. apply fpb_arr_fst.
Defined.

Definition Fun_Pullback_snd : Fun_Pullback_Functor ~{[C, D]}~> G.
Proof.
  unshelve refine (@Build_Transform' C D Fun_Pullback_Functor G fpb_snd _).
  intros x y h. simpl. symmetry. apply fpb_arr_snd.
Defined.

Definition Fun_Pullback_IsPullback :
  IsPullback alpha beta Fun_Pullback_Functor Fun_Pullback_fst Fun_Pullback_snd
  := Fun_IsPullback alpha beta Fun_Pullback_fst Fun_Pullback_snd
       (fun x => pullback_is_pullback _ _ (fpb_at x)).

Definition Fun_Pullback : @Pullback ([C, D]) F G H alpha beta
  := is_pullback_pullback Fun_Pullback_IsPullback.

End FunPullback.

Definition Fun_HasPullbacks {C D : Category} (HP : @HasPullbacks D) :
  @HasPullbacks ([C, D]) :=
  {| pullback := fun F G H alpha beta => Fun_Pullback HP alpha beta |}.

(* ------------------------------------------------------------------ *)
(** ** (C) Readbacks *)

Example fun_pullback_obj_at {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H) (x : C) :
  fobj[Pull _ _ (Fun_Pullback HP alpha beta)] x
    = Pull _ _ (pullback (transform[alpha] x) (transform[beta] x)) := eq_refl.

Example fun_pullback_fst_at {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H) (x : C) :
  transform[pullback_fst _ _ (Fun_Pullback HP alpha beta)] x
    = pullback_fst _ _ (pullback (transform[alpha] x) (transform[beta] x))
  := eq_refl.

Example fun_pullback_snd_at {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H) (x : C) :
  transform[pullback_snd _ _ (Fun_Pullback HP alpha beta)] x
    = pullback_snd _ _ (pullback (transform[alpha] x) (transform[beta] x))
  := eq_refl.

Example fun_haspullbacks_readback {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H) :
  @pullback ([C, D]) (Fun_HasPullbacks HP) F G H alpha beta
    = Fun_Pullback HP alpha beta := eq_refl.

(* The mediator is D's mediator at every component, ON THE NOSE
   ([fun_pullback_med_strict]); the [≈] form below is the weakening a
   consumer rewrites with. *)
Example fun_pullback_med_strict {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H)
  {Q : C ⟶ D} (q1 : Q ~{[C, D]}~> F) (q2 : Q ~{[C, D]}~> G)
  (Hq : alpha ∘ q1 ≈ beta ∘ q2) (x : C) :
  transform[unique_obj (ump_pullbacks _ _ (Fun_Pullback HP alpha beta) Q
                          q1 q2 Hq)] x
    = unique_obj (ump_pullbacks _ _ (fpb_at HP alpha beta x) (Q x)
                    (transform[q1] x) (transform[q2] x) (Hq x))
  := eq_refl.

Lemma fun_pullback_med_at {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H)
  {Q : C ⟶ D} (q1 : Q ~{[C, D]}~> F) (q2 : Q ~{[C, D]}~> G)
  (Hq : alpha ∘ q1 ≈ beta ∘ q2) (x : C) :
  transform[unique_obj (ump_pullbacks _ _ (Fun_Pullback HP alpha beta) Q
                          q1 q2 Hq)] x
    ≈ unique_obj (ump_pullbacks _ _ (fpb_at HP alpha beta x) (Q x)
                    (transform[q1] x) (transform[q2] x) (Hq x)).
Proof.
  apply (uniqueness (ump_pullbacks _ _ (fpb_at HP alpha beta x) (Q x)
           (transform[q1] x) (transform[q2] x) (Hq x))).
  destruct (unique_property (ump_pullbacks _ _ (Fun_Pullback HP alpha beta) Q
                               q1 q2 Hq)) as [Hu1 Hu2].
  split; [ exact (Hu1 x) | exact (Hu2 x) ].
Qed.
