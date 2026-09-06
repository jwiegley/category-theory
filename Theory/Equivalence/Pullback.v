Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(* Pullbacks transport along an equivalence of categories.

   nLab:      https://ncatlab.org/nlab/show/equivalence+of+categories
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   Theory/Equivalence/Terminal.v carries [Terminal_transport] and
   [Initial_transport], their two object readbacks and four lower-case helpers,
   and nothing else of this NAME shape.  MEASURED, with the five files of this
   change excluded (this one, the three Structure/Topos/ files and the probe): a
   whole-tree search for [Terminal_transport], [Cartesian_transport],
   [HasEqualizers_transport], [HasPullbacks_transport], [Initial_transport] or
   [Cocartesian_transport] returns 8 lines, ALL in
   Theory/Equivalence/Terminal.v, naming [Terminal_transport],
   [Initial_transport], [Terminal_transport_obj] and [Initial_transport_obj];
   the case-sensitive search does not reach [terminal_transport_unique],
   [terminal_transport_arrow], [initial_transport_unique] or
   [initial_transport_arrow], and none of those eight is a transport of a binary
   universal property.  Read it as a NAME search: other structures ARE carried
   across an equivalence under other names -- Instance/Proset/Limit.v's
   [Complete_equivalence_invariant] and [Cocomplete_equivalence_invariant],
   Theory/Equivalence/Monoidal.v's [Transported_Monoidal] and
   Theory/Equivalence/Adjunction.v's [Transported_Adjunction] -- so what is new
   here is the pullback case, not the pattern.  This is the
   binary-universal-property companion, built to the same recipe -- take the
   quasi-inverse image of the data, use the structure downstairs, push the
   answer back with F -- and, like it, with no limit machinery anywhere: no
   [Cone], no [Limit], no RAPL.

   WHY THAT MATTERS BEYOND ECONOMY.  The [Limit]-shaped route is not merely more
   expensive here, it is STRICTLY WEAKER, and the measurement is pinned in
   Test/ProbeToposColimits405.v: [Terminal_Limit] (Structure/Limit/Terminal.v)
   and [Cartesian_Limit] (Structure/Limit/Cartesian.v) are stated over
   [Category@{u Set Set}] -- they pin the ambient category's hom AND proof
   universes to the literal [Set] -- while nothing in this file pins any
   universe to [Set].  Read off BOTH binder and block, every constant here is
   over [C : Category@{u u0 u0}] -- hom identified with proof in the BINDER,
   inherited from [IsPullback] and [HasPullbacks], each refused alone at hom and
   proof levels declared strictly apart with the hom-set and the identity
   accepted, pinned in the probe -- and five of the six carry the block equation
   [u0 = u2] identifying the two categories' hom levels, while
   [is_pullback_jointly_monic]'s block is LITERALLY EMPTY over that same binder:
   the binder/block trap in miniature.

   THE HONEST CORE is [IsPullback_transport], which is apex-pinned: a
   pullback IN C of the quasi-inverse image of a cospan of D is, after
   applying F and correcting both legs by the counit isomorphisms, a
   pullback IN D of the original cospan.  [HasPullbacks_transport] merely
   chooses the pullback downstairs and packages the record.

   WHAT THE PROOF SPENDS.  Existence needs only naturality of the COUNIT
   ([equivalence_counit_to_natural]) and its invertibility.  Uniqueness needs,
   in addition, naturality of the UNIT in its conjugated form
   ([equivalence_unit_conjugate]), invertibility of both cells, and faithfulness
   of the quasi-inverse ([Equivalence_Inverse_Faithful]).  NO triangle identity
   is used -- an [EquivalenceOfCategories] carries two natural isomorphisms and
   no coherence between them, so no such identity is available, and the argument
   is arranged to avoid needing one.

   NOT DELIVERED: no statement that F PRESERVES pullbacks (an
   [IsPullback f g P p1 p2] in C carried to one in D at the F-images of
   f and g); no equalizer, product or general limit transport; no
   uniqueness of the transported pullback beyond what the universal
   property itself gives; and no dual (pushouts along an equivalence). *)

(** ** Joint monicity of a pullback's projections *)

(* The standard consequence of the universal property: two maps into the
   apex agreeing after both projections are equal.  Stated separately
   because the transport's uniqueness clause consumes it in C while
   working in D. *)
Lemma is_pullback_jointly_monic {C : Category} {x y z : C}
      {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
      (HP : IsPullback f g P p1 p2) (Q : C) (a b : Q ~> P) :
  p1 ∘ a ≈ p1 ∘ b → p2 ∘ a ≈ p2 ∘ b → a ≈ b.
Proof.
  intros H1 H2.
  assert (Hc : f ∘ (p1 ∘ a) ≈ g ∘ (p2 ∘ a)).
  { rewrite !comp_assoc.
    now rewrite (is_pullback_commutes HP). }
  pose proof (is_pullback_ump HP Q (p1 ∘ a) (p2 ∘ a) Hc) as U.
  transitivity (unique_obj U).
  - symmetry.
    apply (uniqueness U); split; reflexivity.
  - apply (uniqueness U); split.
    + now symmetry.
    + now symmetry.
Qed.

Section PullbackTransport.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(* The two corrected legs of the transported square. *)
Definition pullback_transport_leg {d : D} {P : C}
           (p : P ~> @quasi_inverse C D F E d) : F P ~> d :=
  to (@equivalence_counit_at C D F E d) ∘ fmap[F] p.

(* Any two maps into F P that agree after both corrected legs agree, when
   the two uncorrected legs are jointly monic downstairs.  This is the
   whole content of the uniqueness clause below. *)
Lemma pullback_transport_jointly_monic {x y : D} {P : C}
      {p1 : P ~> @quasi_inverse C D F E x}
      {p2 : P ~> @quasi_inverse C D F E y}
      (JM : ∀ (Z : C) (a b : Z ~> P),
              p1 ∘ a ≈ p1 ∘ b → p2 ∘ a ≈ p2 ∘ b → a ≈ b)
      {Q : D} (v w : Q ~> F P) :
  pullback_transport_leg p1 ∘ v ≈ pullback_transport_leg p1 ∘ w →
  pullback_transport_leg p2 ∘ v ≈ pullback_transport_leg p2 ∘ w →
  v ≈ w.
Proof.
  intros H1 H2.
  (* Cancel the counit isomorphisms, then apply the faithful
     quasi-inverse. *)
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  (* The unit at P is invertible, so it suffices to compare after
     [from (unit at P)]. *)
  apply (monic (Monic := iso_from_monic
                  (@equivalence_unit_at C D F E P))).
  (* Reduce to the two projections downstairs. *)
  apply JM.
  - apply (monic (Monic := iso_to_monic
                    (@equivalence_unit_at C D F E
                       (@quasi_inverse C D F E x)))).
    rewrite !comp_assoc.
    rewrite <- !(equivalence_unit_conjugate p1).
    rewrite <- !fmap_comp.
    apply fmap_respects.
    unfold pullback_transport_leg in H1.
    apply (monic (Monic := iso_to_monic
                    (@equivalence_counit_at C D F E x))).
    rewrite !comp_assoc.
    exact H1.
  - apply (monic (Monic := iso_to_monic
                    (@equivalence_unit_at C D F E
                       (@quasi_inverse C D F E y)))).
    rewrite !comp_assoc.
    rewrite <- !(equivalence_unit_conjugate p2).
    rewrite <- !fmap_comp.
    apply fmap_respects.
    unfold pullback_transport_leg in H2.
    apply (monic (Monic := iso_to_monic
                    (@equivalence_counit_at C D F E y))).
    rewrite !comp_assoc.
    exact H2.
Qed.

(** ** The apex-pinned transport *)

Lemma IsPullback_transport {x y z : D} {f : x ~> z} {g : y ~> z}
      {P : C}
      {p1 : P ~> @quasi_inverse C D F E x}
      {p2 : P ~> @quasi_inverse C D F E y}
      (HP : IsPullback (fmap[@quasi_inverse C D F E] f)
                       (fmap[@quasi_inverse C D F E] g) P p1 p2) :
  IsPullback f g (F P)
    (pullback_transport_leg p1) (pullback_transport_leg p2).
Proof.
  constructor.
  - (* the corrected square commutes: counit naturality on both sides *)
    unfold pullback_transport_leg.
    rewrite !comp_assoc.
    rewrite <- (equivalence_counit_to_natural f).
    rewrite <- (equivalence_counit_to_natural g).
    rewrite <- !comp_assoc, <- !fmap_comp.
    apply compose_respects; [reflexivity|].
    apply fmap_respects.
    exact (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    (* transport the competing cone into C with the quasi-inverse *)
    assert (Hq' : fmap[@quasi_inverse C D F E] f
                    ∘ fmap[@quasi_inverse C D F E] q1
                  ≈ fmap[@quasi_inverse C D F E] g
                    ∘ fmap[@quasi_inverse C D F E] q2).
    { rewrite <- !fmap_comp.
      now apply fmap_respects. }
    destruct (is_pullback_ump HP (@quasi_inverse C D F E Q)
                (fmap[@quasi_inverse C D F E] q1)
                (fmap[@quasi_inverse C D F E] q2) Hq') as [u [U1 U2] Uu].
    unshelve refine {| unique_obj :=
      fmap[F] u ∘ from (@equivalence_counit_at C D F E Q) |}.
    + split; unfold pullback_transport_leg.
      * rewrite <- !comp_assoc, (comp_assoc (fmap[F] p1)), <- fmap_comp.
        rewrite U1, comp_assoc.
        rewrite (equivalence_counit_to_natural q1).
        rewrite <- comp_assoc, iso_to_from.
        apply id_right.
      * rewrite <- !comp_assoc, (comp_assoc (fmap[F] p2)), <- fmap_comp.
        rewrite U2, comp_assoc.
        rewrite (equivalence_counit_to_natural q2).
        rewrite <- comp_assoc, iso_to_from.
        apply id_right.
    + intros v [V1 V2].
      apply (pullback_transport_jointly_monic
               (is_pullback_jointly_monic HP)).
      * rewrite V1.
        unfold pullback_transport_leg.
        rewrite <- !comp_assoc, (comp_assoc (fmap[F] p1)), <- fmap_comp.
        rewrite U1, comp_assoc.
        rewrite (equivalence_counit_to_natural q1).
        rewrite <- comp_assoc, iso_to_from.
        now rewrite id_right.
      * rewrite V2.
        unfold pullback_transport_leg.
        rewrite <- !comp_assoc, (comp_assoc (fmap[F] p2)), <- fmap_comp.
        rewrite U2, comp_assoc.
        rewrite (equivalence_counit_to_natural q2).
        rewrite <- comp_assoc, iso_to_from.
        now rewrite id_right.
Qed.

(** ** The packaged transport *)

Definition HasPullbacks_transport (HP : @HasPullbacks C) :
  @HasPullbacks D :=
  {| pullback := fun x y z f g =>
       is_pullback_pullback
         (IsPullback_transport
            (pullback_is_pullback _ _
               (@pullback C HP _ _ _
                  (fmap[@quasi_inverse C D F E] f)
                  (fmap[@quasi_inverse C D F E] g)))) |}.

(* The transported pullback object is the image of the one chosen
   downstairs, on the nose. *)
Example HasPullbacks_transport_obj (HP : @HasPullbacks C)
        {x y z : D} (f : x ~> z) (g : y ~> z) :
  Pull f g (@pullback D (HasPullbacks_transport HP) x y z f g)
    = F (Pull _ _ (@pullback C HP _ _ _
                     (fmap[@quasi_inverse C D F E] f)
                     (fmap[@quasi_inverse C D F E] g)))
  := eq_refl.

End PullbackTransport.
