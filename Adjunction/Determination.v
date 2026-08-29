Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Universal.Arrow.Dual.

Generalizable All Variables.

(** * Determination of an adjunction by its counit and by couniversal
      arrows

    nLab:      https://ncatlab.org/nlab/show/adjoint+functor
    nLab:      https://ncatlab.org/nlab/show/universal+morphism
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, §IV.1 Theorem 2 -- maclane:IV.1:thm2.
    Book: Awodey, "Category Theory", 2nd ed., §9.2 Corollary 9.5,
          printed pp. 222-223 -- awodey:9.2:cor5.

    WHAT WAS ALREADY THERE, AND THE ISSUE'S OWN ACCOUNT OF IT IS STALE.
    #347's "Current state" says a whole-tree search for couniversal
    arrows "returns nothing" and that Theory/Universal/Arrow.v "has no
    dual".  Both are false: Theory/Universal/Arrow/Dual.v supplies
    [CouniversalArrow] (:199), [coarrow] (:222),
    [ump_couniversal_arrows] (:237),
    [RightAdjointFunctorFromCouniversalArrows] (:421) and
    [AdjunctionFromCouniversalArrows] (:439).  Every one of those is
    CONSUMED here and none re-derived, which is what that issue's own QA
    correction directs.

    THE DISTINCTION THAT DEFINES THIS FILE IS A DIRECTION, AND IT IS EASY
    TO MISS.  Dual.v:452 already carries a lemma named
    [counit_couniversal].  It takes a couniversal family as DATA and
    describes the adjunction that file BUILDS -- every adjunction named
    there is [AdjunctionFromCouniversalArrows] of that family -- so it
    never starts from an arbitrary adjunction.  What was open, and is
    delivered here, is the CONVERSE: from an ARBITRARY [F ⊣ U],
    [adj_counit_couniversal] exhibits each counit component as a
    [CouniversalArrow] PACKAGED AS THE CLASS, which is the bar the issue
    sets ("not merely that the equational form [adj_univ_impl] holds").
    Neither Theory/Universal/Arrow.v nor its dual contains any passage
    from an adjunction to a (co)universal arrow.

    STRENGTHS, MEASURED STRICT-FIRST -- AND ONLY ONE OF THEM
    DISCRIMINATES.  The arrow readback [coarrow (adj_counit_couniversal
    c) = counit] is [eq_refl], where the donor's [counit_couniversal]
    reaches only [≈]; building the couniversal arrow FROM the counit
    makes the counit definitionally its arrow, whereas recovering the
    counit from a given family leaves an [fmap[F] id] residue.  **The
    OBJECT readback is NOT evidence of that**: it is [eq_refl] on both
    sides (Dual.v:429's [right_adjoint_obj] is [reflexivity]) and also on
    this file's own other direction ([couniversal_of_counit_obj]), so it
    is parity, not superiority.  Only the arrow half separates them.

    The [eq_refl] object readbacks are nonetheless load-bearing rather
    than decorative: [couniversal_of_counit_med] and
    [adjunction_of_counit_unit] only TYPECHECK because the object
    readback is definitional.

    THE ONE [≈]-ONLY STEP IS THE MEDIATOR, and the honest statement of
    its cause is narrower than "donor opacity" alone.  What the contrast
    below establishes is that the failure is not a property of the
    couniversal arrow in general: [coarrow] and [coarrow_obj] of the SAME
    arrow do reduce.  That does NOT by itself isolate the [Qed] on
    [ump_universal_arrows] (Theory/Universal/Arrow.v:139), since those
    two never route through [ump_*] at all and so would reduce under any
    competing hypothesis.  An isolating experiment -- the same statement
    against a transparent clone of that donor -- was run during review
    and DOES confirm the attribution, and it further shows the [≈] could
    be strengthened by making the donor transparent; that experiment is
    NOT shipped here, and changing Theory/Universal/Arrow.v is out of
    scope for this issue.

    WHAT THE UNIT SIDE DOES AND DOES NOT DELIVER.  [UnitPresentation]
    gives Mac Lane's FIRST presentation its own record -- a left adjoint,
    a right adjoint, and a unit whose every component is universal --
    with passages BOTH ways ([unit_presentation_of_adjunction],
    [adjunction_of_unit_presentation]).  That is a DICTIONARY, not a
    separation in this tree's usual sense: nothing here proves the two
    presentations differ.  And unlike the counit side, **no round trip is
    proved**: there is no statement that
    [adjunction_of_unit_presentation (unit_presentation_of_adjunction A)]
    agrees with [A], nor any relating the recovered [up_unit] to
    [unit A].  [unit_presentation_transpose] and its untransposed sibling
    are [eq_refl] BY CONSTRUCTION -- [adjunction_of_unit_presentation]
    defines its transposes as exactly those terms -- so they pin a
    definition rather than recovering anything, and neither passes
    through [unit_presentation_of_adjunction].

    NOT DELIVERED: the unit-side round trip just described; no dual of
    the [UnitPresentation] packaging (a counit presentation as its own
    record); no naturality of the couniversal family in [c]; no
    comparison with Theory/Universal/Element.v's universal-element
    route; and no change to the transparency of
    [ump_universal_arrows]. *)


Section CounitCouniversal.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

#[local] Existing Instance A.

(* Mac Lane §IV.1 Theorem 2, the converse leg: each counit component is a
   couniversal arrow, PACKAGED as one. *)
Definition adj_counit_couniversal (c : C) : CouniversalArrow c F.
Proof using A U.
  unshelve eapply (couniversal_arrow_from_UMP c F (U c) counit).
  intros d' f.
  unshelve eexists ((to adj[A] f)).
  - exact (snd (adj_univ_impl f (to adj[A] f)) (reflexivity _)).
  - intros v Hv.
    exact (fst (adj_univ_impl f v) Hv).
Defined.

Example adj_counit_couniversal_obj (c : C) :
  coarrow_obj (adj_counit_couniversal c) = U c := eq_refl.

Example adj_counit_couniversal_arrow (c : C) :
  coarrow (adj_counit_couniversal c) = @counit C D F U A c := eq_refl.

(* The mediator of that couniversal arrow is the forward transpose -- up to
   `≈` only, and the cause is DONOR OPACITY that DISCRIMINATES: [coarrow] and
   [coarrow_obj] above reduce because they are transparent projections of the
   transparent [couniversal_arrow_from_UMP], whereas the mediator is read out
   of [ump_couniversal_arrows], whose primal donor [ump_universal_arrows]
   (Theory/Universal/Arrow.v:139) is closed with [Qed]. *)
Lemma adj_counit_couniversal_med (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal c) f)
    ≈ to adj[A] f.
Proof using A U.
  symmetry.
  exact (fst (adj_univ_impl f _)
             (unique_property
                (ump_couniversal_arrows (adj_counit_couniversal c) f))).
Qed.

Lemma adj_counit_factor_unique {x y : C} (f : x ~{C}~> y)
      (g : U x ~{D}~> U y) :
  f ∘ @counit C D F U A x ≈ @counit C D F U A y ∘ fmap[F] g →
  g ≈ fmap[U] f.
Proof using A U.
  intro Hg.
  rewrite <- (fst (adj_univ_impl (f ∘ counit) g) Hg).
  symmetry.
  apply fmap_to_adj_counit.
Qed.

End CounitCouniversal.

Section CounitRoundTrip.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition counit_couniversal_family : ∀ c : C, CouniversalArrow c F :=
  adj_counit_couniversal A.

Definition right_adjoint_of_counit : C ⟶ D :=
  RightAdjointFunctorFromCouniversalArrows F counit_couniversal_family.

Definition adjunction_of_counit : F ⊣ right_adjoint_of_counit :=
  AdjunctionFromCouniversalArrows F counit_couniversal_family.

Example right_adjoint_of_counit_obj (c : C) :
  fobj[right_adjoint_of_counit] c = fobj[U] c := eq_refl.

Lemma adjunction_of_counit_counit (c : C) :
  @counit C D F right_adjoint_of_counit adjunction_of_counit c
    ≈ @counit C D F U A c.
Proof using A U.
  exact (counit_couniversal F counit_couniversal_family c).
Qed.

Lemma right_adjoint_of_counit_fmap {x y : C} (f : x ~{C}~> y) :
  fmap[right_adjoint_of_counit] f ≈ fmap[U] f.
Proof using A U.
  apply (adj_counit_factor_unique A).
  rewrite <- (adjunction_of_counit_counit x).
  rewrite <- (adjunction_of_counit_counit y).
  symmetry.
  exact (adj_counit_naturality adjunction_of_counit f).
Qed.

Lemma right_adjoint_of_counit_iso : right_adjoint_of_counit ≈ U.
Proof using A U.
  exists (fun c => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  apply right_adjoint_of_counit_fmap.
Qed.

Lemma adjunction_of_counit_to {x : D} {y : C} (g : F x ~{C}~> y) :
  to adj[adjunction_of_counit] g ≈ to adj[A] g.
Proof using A U.
  symmetry.
  apply (fst (@adj_univ_impl C D F U A x y g _)).
  rewrite <- (adjunction_of_counit_counit y).
  exact (snd (@adj_univ_impl C D F right_adjoint_of_counit
                adjunction_of_counit x y g _) (reflexivity _)).
Qed.

Lemma adjunction_of_counit_from {x : D} {y : C} (h : x ~{D}~> U y) :
  from adj[adjunction_of_counit] h ≈ from adj[A] h.
Proof using A U.
  rewrite (@from_adj_counit C D F right_adjoint_of_counit
             adjunction_of_counit x y h).
  rewrite (@from_adj_counit C D F U A x y h).
  now rewrite (adjunction_of_counit_counit y).
Qed.

Lemma adjunction_of_counit_unit (d : D) :
  @unit C D F right_adjoint_of_counit adjunction_of_counit d
    ≈ @unit C D F U A d.
Proof using A U. exact (adjunction_of_counit_to id). Qed.

End CounitRoundTrip.

(** ** The other composite: couniversal arrows, adjunction, counit *)

Section CouniversalRoundTrip.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context (H : ∀ c : C, CouniversalArrow c F).

Example couniversal_of_counit_obj (c : C) :
  coarrow_obj (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
    = coarrow_obj (H c) := eq_refl.

Lemma couniversal_of_counit_arrow (c : C) :
  coarrow (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
    ≈ coarrow (H c).
Proof using H. exact (counit_couniversal F H c). Qed.

Lemma couniversal_of_counit_med (c : C) :
  cua_med (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
          (H c) ≈ id.
Proof using H.
  apply cua_med_unique.
  rewrite fmap_id, id_right.
  symmetry.
  apply couniversal_of_counit_arrow.
Qed.

Lemma couniversal_of_counit_iso (c : C) :
  couniversal_arrow_iso
    (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c) (H c)
    ≈ iso_id.
Proof using H.
  apply to_equiv_implies_iso_equiv; simpl.
  apply couniversal_of_counit_med.
Qed.

End CouniversalRoundTrip.

(** ** Mac Lane's first presentation: a natural unit whose every component
       is universal *)

Section UnitSide.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Class UnitPresentation := {
  up_unit : Id[D] ⟹ U ◯ F;
  up_universal {d : D} {c : C} (f : d ~{D}~> U c) :
    ∃! g : F d ~{C}~> c, f ≈ fmap[U] g ∘ transform[up_unit] d
}.

Definition unit_presentation_of_adjunction (A : F ⊣ U) : UnitPresentation.
Proof.
  unshelve eapply Build_UnitPresentation.
  - unshelve eapply Build_Transform.
    + exact (fun d => @unit C D F U A d).
    + exact (fun x y f => adj_unit_naturality A f).
    + exact (fun x y f => symmetry (adj_unit_naturality A f)).
  - intros d c f; simpl.
    unshelve eexists (from adj[A] f).
    + rewrite <- (@to_adj_unit C D F U A d c (from adj[A] f)).
      symmetry.
      exact (@from_adj_comp_law C D F U A d c f).
    + intros v Hv.
      symmetry.
      apply (snd (@adj_univ C D F U A d c v f)).
      rewrite (@to_adj_unit C D F U A d c v).
      now symmetry.
Defined.

Definition adjunction_of_unit_presentation (P : UnitPresentation) : F ⊣ U.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros d c.
    unshelve eapply Isomorphism.Build_Isomorphism.
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun g => fmap[U] g ∘ transform[up_unit] d).
      * abstract (intros g1 g2 Hg; apply compose_respects;
                  [ exact (fmap_respects _ _ g1 g2 Hg) | reflexivity ]).
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun f => unique_obj (up_universal f)).
      * abstract (intros f1 f2 Hf; apply uniqueness;
                  etransitivity; [ exact Hf
                                 | exact (unique_property (up_universal f2)) ]).
    + abstract (intro f; symmetry; exact (unique_property (up_universal f))).
    + abstract (intro g; apply uniqueness; reflexivity).
  - abstract (intros x y z f g; simpl;
              rewrite fmap_comp, <- comp_assoc;
              rewrite (@naturality _ _ _ _ up_unit _ _ g);
              now rewrite comp_assoc).
  - abstract (intros x y z f g; simpl;
              now rewrite fmap_comp, <- comp_assoc).
Defined.

(* Mac Lane's transpose formula, on the nose. *)
Example unit_presentation_transpose (P : UnitPresentation)
        {d : D} {c : C} (g : F d ~{C}~> c) :
  to adj[adjunction_of_unit_presentation P] g
    = fmap[U] g ∘ transform[up_unit] d := eq_refl.

Example unit_presentation_untranspose (P : UnitPresentation)
        {d : D} {c : C} (f : d ~{D}~> U c) :
  from adj[adjunction_of_unit_presentation P] f
    = unique_obj (up_universal f) := eq_refl.

End UnitSide.
