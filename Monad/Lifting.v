Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.

Generalizable All Variables.

(** * Adjoint lifting along monadic functors, crude case

    nLab:      https://ncatlab.org/nlab/show/adjoint+lifting+theorem
    nLab:      https://ncatlab.org/nlab/show/adjoint+triangle+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

    This file delivers the adjoint lifting theorem in its adjoint-triangle
    form (Dubuc, "Adjoint triangles", 1968), scoped to the crude
    monadicity hypotheses of Monad/Monadicity/Crude.v.

    Fix an adjunction F ⊣ U with F : D ⟶ C, and write T = U ◯ F for the
    induced monad on D and K = [EM_Comparison A] : C ⟶ D^T for the
    Eilenberg–Moore comparison (Monad/Comparison.v).  The core statement
    ([adjoint_triangle]) assumes only that K is fully faithful — that U is
    "of descent type" — supplied as [Full K] and [Faithful K] hypotheses:

      given R : B ⟶ C together with a left adjoint L0 ⊣ U ◯ R of the
      composite, if B has coequalizers of reflexive pairs, then R itself
      has a left adjoint ([Lifted_Left_Adjoint], adjoint to R by
      [adjoint_triangle]).

    The construction is the classical one.  For c : C, the parallel pair

        L0 (U ε_c),  ⌈U ε ∘ U F η0⌉  :  L0 (U (F (U c))) ⇉ L0 (U c)

    — the L0-transport of the canonical presentation of the comparison
    algebra K c, with the second leg the A0-inverse-transpose of the free
    algebra action on the A0-unit η0 — is reflexive with common section
    L0 η_{U c} ([lift_reflexive]; the retraction laws are the two zig-zag
    identities).  The value of the left adjoint at c is its chosen
    reflexive coequalizer e : L0 (U c) ~> q ([lift_obj]/[lift_e]).  The
    A0-transpose of e is an algebra homomorphism K c ~> K (R q) — its
    commuting square is the transposed cofork law ([lift_w_commutes]) —
    and pulling it back through the full comparison K produces the unit
    c ~> R q ([lift_unit]).  Every f : c ~> R b factors through the unit:
    the A0-inverse-transpose of U f coforks the pair ([lift_desc_cofork])
    and so descends through e, faithfulness of K (hence of U,
    [lift_faithful]) yields the factorization ([lift_factor_property]),
    and descent uniqueness read back through the transposition gives its
    uniqueness ([lift_factor_unique]).  The universal arrows so obtained
    assemble into a left adjoint via Theory/Universal/Arrow.v
    ([LeftAdjointFunctorFromUniversalArrows]).

    The principal theorem [adjoint_lifting] is the crude case: when the
    adjunction satisfies the crude hypotheses — C has reflexive
    coequalizers, U preserves them and reflects isomorphisms — the
    comparison is an equivalence ([crude_monadicity]), hence full and
    faithful (Theory/Equivalence/FullFaithful.v), and the triangle
    theorem applies: every R : B ⟶ C whose composite U ◯ R has a left
    adjoint has a left adjoint, provided B has reflexive coequalizers.
    [adjoint_lifting_monadic] states the same with the monadicity data
    packaged as [Monadic U] (Monad/Comparison.v).

    The classical square form of the adjoint lifting theorem — monads S
    on B' and T on D, a functor Q̄ between the algebra categories lifting
    Q : B' ⟶ D through the forgetful functors, and a left adjoint of Q —
    is the instance R := Q̄ of the triangle form: the composite of Q̄ with
    the (monadic) forgetful functor is Q ◯ U^S, whose left adjoint is
    F^S composed with the left adjoint of Q ([Adjunction_Compose]).

    Alongside, [EM_Adjunction_Transport] records the transport piece: an
    adjunction L ⊣ J whose right adjoint lands in the Eilenberg–Moore
    category composes with the adjoint equivalence K ⊣ K⁻¹ carried by the
    comparison (Theory/Equivalence/Adjoint.v) to the adjunction
    L ◯ K ⊣ K⁻¹ ◯ J, whose right adjoint lands in C. *)

(** ** The adjoint triangle theorem, for U of descent type *)

Section AdjointTriangle.

Context {C : Category}.
Context {D : Category}.
Context {B : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (fullK : Full (EM_Comparison A)).
Context (faithK : Faithful (EM_Comparison A)).
Context {R : B ⟶ C}.
Context {L0 : D ⟶ B}.
Context (A0 : L0 ⊣ U ◯ R).
Context (RCB : HasReflexiveCoequalizers B).

Local Notation HM := (Adjunction_Induced_Monad A).
Local Notation EM := (@EilenbergMoore D (U ◯ F) HM).
Local Notation K := (EM_Comparison A).

(** The A0-transposition laws, restated with the composite right
    adjoint's action split into fmap[U] (fmap[R] -), so that later
    rewrites are syntactic. *)

Lemma lift_transpose_unit {x : D} {b : B} (f : L0 x ~{B}~> b) :
  to (@adj _ _ _ _ A0 x b) f
    ≈ fmap[U] (fmap[R] f) ∘ @unit _ _ _ _ A0 x.
Proof. exact (@to_adj_unit _ _ _ _ A0 x b f). Qed.

Lemma lift_transpose_nat_r {x : D} {b b' : B}
  (f : b ~{B}~> b') (g : L0 x ~{B}~> b) :
  to (@adj _ _ _ _ A0 x b') (f ∘ g)
    ≈ fmap[U] (fmap[R] f) ∘ to (@adj _ _ _ _ A0 x b) g.
Proof. exact (@to_adj_nat_r _ _ _ _ A0 x b b' f g). Qed.

Lemma lift_untranspose_nat_r {x : D} {b b' : B}
  (f : b ~{B}~> b') (g : x ~{D}~> U (R b)) :
  from (@adj _ _ _ _ A0 x b') (fmap[U] (fmap[R] f) ∘ g)
    ≈ f ∘ from (@adj _ _ _ _ A0 x b) g.
Proof. exact (@from_adj_nat_r _ _ _ _ A0 x b b' f g). Qed.

(* Transposition is injective: both transposes are the two legs of the
   hom-setoid isomorphism of A0. *)
Lemma lift_transpose_inj {x : D} {b : B} (g h : L0 x ~{B}~> b) :
  to (@adj _ _ _ _ A0 x b) g ≈ to (@adj _ _ _ _ A0 x b) h → g ≈ h.
Proof.
  intros Hgh.
  transitivity (from (@adj _ _ _ _ A0 x b) (to (@adj _ _ _ _ A0 x b) g)).
  - symmetry.
    exact (@to_adj_comp_law _ _ _ _ A0 x b g).
  - transitivity (from (@adj _ _ _ _ A0 x b) (to (@adj _ _ _ _ A0 x b) h)).
    + exact (@from_adj_respects _ _ _ _ A0 x b _ _ Hgh).
    + exact (@to_adj_comp_law _ _ _ _ A0 x b h).
Qed.

(** ** The presentation pair, transported along L0

    The canonical presentation of the comparison algebra K c is the pair
    U ε_c, U F (η0) followed by the free action; transported through the
    adjunction L0 ⊣ U ◯ R it becomes a reflexive pair in B. *)

Definition lift_pair_l (c : C) :
  L0 (U (F (U c))) ~{B}~> L0 (U c) :=
  fmap[L0] (fmap[U] (@counit _ _ _ _ A c)).

(* The algebra action of K (R (L0 (U c))) precomposed with the T-image of
   the A0-unit: the D-level second leg of the presentation. *)
Definition lift_action (c : C) :
  U (F (U c)) ~{D}~> U (R (L0 (U c))) :=
  fmap[U] (@counit _ _ _ _ A (R (L0 (U c))))
    ∘ fmap[U] (fmap[F] (@unit _ _ _ _ A0 (U c))).

Definition lift_pair_r (c : C) :
  L0 (U (F (U c))) ~{B}~> L0 (U c) :=
  from (@adj _ _ _ _ A0 (U (F (U c))) (L0 (U c))) (lift_action c).

(* L0 (U ε_c) retracts L0 η_{U c}: the L0-image of the zig-zag identity
   of A. *)
Lemma lift_section_l (c : C) :
  lift_pair_l c ∘ fmap[L0] (@unit _ _ _ _ A (U c)) ≈ id.
Proof.
  unfold lift_pair_l.
  rewrite <- fmap_comp.
  rewrite (@fmap_counit_unit _ _ _ _ A c).
  apply fmap_id.
Qed.

(* Restricting the action leg along the unit of A recovers the unit of
   A0: slide η across η0 by naturality, and close with the zig-zag
   identity of A. *)
Lemma lift_action_unit (c : C) :
  lift_action c ∘ @unit _ _ _ _ A (U c) ≈ @unit _ _ _ _ A0 (U c).
Proof.
  unfold lift_action.
  rewrite <- comp_assoc.
  rewrite <- (adj_unit_natural A (@unit _ _ _ _ A0 (U c))).
  rewrite comp_assoc.
  rewrite (@fmap_counit_unit _ _ _ _ A (R (L0 (U c)))).
  apply id_left.
Qed.

(* The transposed action leg retracts L0 η_{U c} as well: transpose the
   previous triangle and close with the zig-zag identity of A0. *)
Lemma lift_section_r (c : C) :
  lift_pair_r c ∘ fmap[L0] (@unit _ _ _ _ A (U c)) ≈ id.
Proof.
  unfold lift_pair_r.
  rewrite <- (@from_adj_nat_l _ _ _ _ A0 _ _ _
                (lift_action c) (@unit _ _ _ _ A (U c))).
  transitivity (from (@adj _ _ _ _ A0 (U c) (L0 (U c)))
                  (@unit _ _ _ _ A0 (U c))).
  - exact (@from_adj_respects _ _ _ _ A0 _ _ _ _ (lift_action_unit c)).
  - exact (@from_adj_unit _ _ _ _ A0 (U c)).
Qed.

Definition lift_reflexive (c : C) :
  ReflexivePair (lift_pair_l c) (lift_pair_r c) :=
  common_section_reflexive (lift_pair_l c) (lift_pair_r c)
    (fmap[L0] (@unit _ _ _ _ A (U c)))
    (lift_section_l c) (lift_section_r c).

(** ** The candidate adjoint values: chosen reflexive coequalizers *)

Definition lift_coeq (c : C) :
  ∃ (q : B) (e : L0 (U c) ~{B}~> q),
    IsCoequalizer (lift_pair_l c) (lift_pair_r c) q e :=
  @reflexive_coeq B RCB (L0 (U (F (U c)))) (L0 (U c))
    (lift_pair_l c) (lift_pair_r c) (lift_reflexive c).

Definition lift_obj (c : C) : B := `1 (lift_coeq c).

Definition lift_e (c : C) : L0 (U c) ~{B}~> lift_obj c :=
  `1 (`2 (lift_coeq c)).

Definition lift_is_coeq (c : C) :
  IsCoequalizer (lift_pair_l c) (lift_pair_r c) (lift_obj c) (lift_e c) :=
  `2 (`2 (lift_coeq c)).

Lemma lift_cofork (c : C) :
  lift_e c ∘ lift_pair_l c ≈ lift_e c ∘ lift_pair_r c.
Proof. exact (cofork (lift_is_coeq c)). Qed.

(** ** The unit carrier: the A0-transpose of the coequalizing map *)

Definition lift_w (c : C) : U c ~{D}~> U (R (lift_obj c)) :=
  to (@adj _ _ _ _ A0 (U c) (lift_obj c)) (lift_e c).

(* Pushing the coequalizing map under the algebra action: counit
   naturality at fmap[R] e, after expanding the transpose through the
   unit of A0. *)
Lemma lift_action_square (c : C) :
  fmap[U] (@counit _ _ _ _ A (R (lift_obj c)))
      ∘ fmap[U] (fmap[F] (lift_w c))
    ≈ fmap[U] (fmap[R] (lift_e c)) ∘ lift_action c.
Proof.
  unfold lift_w.
  rewrite (lift_transpose_unit (lift_e c)).
  rewrite (@fmap_comp D C F _ _ _
             (fmap[U] (fmap[R] (lift_e c))) (@unit _ _ _ _ A0 (U c))).
  rewrite (@fmap_comp C D U _ _ _
             (fmap[F] (fmap[U] (fmap[R] (lift_e c))))
             (fmap[F] (@unit _ _ _ _ A0 (U c)))).
  rewrite comp_assoc.
  rewrite <- (@fmap_comp C D U _ _ _
                (@counit _ _ _ _ A (R (lift_obj c)))
                (fmap[F] (fmap[U] (fmap[R] (lift_e c))))).
  rewrite (adj_counit_natural A (fmap[R] (lift_e c))).
  rewrite (@fmap_comp C D U _ _ _
             (fmap[R] (lift_e c)) (@counit _ _ _ _ A (R (L0 (U c))))).
  unfold lift_action.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

(* The commuting square of the transposed coequalizing map: it is an
   algebra homomorphism K c ~> K (R (lift_obj c)).  Transpose the cofork
   law of the coequalizer and contract with [lift_action_square]. *)
Lemma lift_w_commutes (c : C) :
  lift_w c ∘ fmap[U] (@counit _ _ _ _ A c)
    ≈ fmap[U] (@counit _ _ _ _ A (R (lift_obj c)))
        ∘ fmap[U] (fmap[F] (lift_w c)).
Proof.
  rewrite (lift_action_square c).
  transitivity (to (@adj _ _ _ _ A0 (U (F (U c))) (lift_obj c))
                  (lift_e c ∘ lift_pair_l c)).
  - symmetry.
    exact (@to_adj_nat_l _ _ _ _ A0 _ _ _
             (lift_e c) (fmap[U] (@counit _ _ _ _ A c))).
  - transitivity (to (@adj _ _ _ _ A0 (U (F (U c))) (lift_obj c))
                    (lift_e c ∘ lift_pair_r c)).
    + exact (@to_adj_respects _ _ _ _ A0 _ _ _ _ (lift_cofork c)).
    + rewrite (lift_transpose_nat_r (lift_e c) (lift_pair_r c)).
      apply compose_respects.
      * reflexivity.
      * unfold lift_pair_r.
        exact (@from_adj_comp_law _ _ _ _ A0 _ _ (lift_action c)).
Qed.

(* The algebra homomorphism K c ~> K (R (lift_obj c)) carried by the
   transpose of e. *)
Definition lift_unit_hom (c : C) :
  K c ~{EM}~> K (R (lift_obj c)) :=
  @Build_TAlgebraHom D (U ◯ F) HM (U c) (U (R (lift_obj c)))
    (EM_Comparison_Algebra A c)
    (EM_Comparison_Algebra A (R (lift_obj c)))
    (lift_w c) (lift_w_commutes c).

(** ** The unit, through the fully faithful comparison *)

Definition lift_unit (c : C) : c ~{C}~> R (lift_obj c) :=
  @prefmap C EM K fullK c (R (lift_obj c)) (lift_unit_hom c).

(* The section law of fullness, read on carriers: hom-equivalence in the
   Eilenberg-Moore category is carrier equivalence, and the carrier of
   fmap[K] is fmap[U]. *)
Lemma lift_unit_w (c : C) : fmap[U] (lift_unit c) ≈ lift_w c.
Proof.
  exact (@fmap_sur C EM K fullK c (R (lift_obj c)) (lift_unit_hom c)).
Qed.

(* Faithfulness of K, read on carriers, is faithfulness of U. *)
Lemma lift_faithful {x y : C} (f g : x ~{C}~> y) :
  fmap[U] f ≈ fmap[U] g → f ≈ g.
Proof using A C D F U faithK.
  intros Hfg.
  apply (@fmap_inj C EM K faithK x y f g).
  exact Hfg.
Qed.

(** ** Descent: every f : c ~> R b factors through the unit *)

(* The A0-inverse-transpose of U f, the map to be descended. *)
Definition lift_desc_arg {c : C} {b : B} (f : c ~{C}~> R b) :
  L0 (U c) ~{B}~> b :=
  from (@adj _ _ _ _ A0 (U c) b) (fmap[U] f).

(* Its own transposition triangle: restricting along the A0-unit
   recovers U f. *)
Lemma lift_desc_transpose {c : C} {b : B} (f : c ~{C}~> R b) :
  fmap[U] (fmap[R] (lift_desc_arg f)) ∘ @unit _ _ _ _ A0 (U c)
    ≈ fmap[U] f.
Proof.
  transitivity (to (@adj _ _ _ _ A0 (U c) b) (lift_desc_arg f)).
  - symmetry.
    exact (lift_transpose_unit (lift_desc_arg f)).
  - exact (@from_adj_comp_law _ _ _ _ A0 (U c) b (fmap[U] f)).
Qed.

(* The D-level cofork of the descent: U f absorbs the presentation pair,
   by counit naturality at fmap[R] (lift_desc_arg f) and at f. *)
Lemma lift_desc_square {c : C} {b : B} (f : c ~{C}~> R b) :
  fmap[U] f ∘ fmap[U] (@counit _ _ _ _ A c)
    ≈ fmap[U] (fmap[R] (lift_desc_arg f)) ∘ lift_action c.
Proof.
  symmetry.
  unfold lift_action.
  rewrite comp_assoc.
  rewrite <- (@fmap_comp C D U _ _ _
                (fmap[R] (lift_desc_arg f))
                (@counit _ _ _ _ A (R (L0 (U c))))).
  rewrite <- (adj_counit_natural A (fmap[R] (lift_desc_arg f))).
  rewrite (@fmap_comp C D U _ _ _
             (@counit _ _ _ _ A (R b))
             (fmap[F] (fmap[U] (fmap[R] (lift_desc_arg f))))).
  rewrite <- comp_assoc.
  rewrite <- (@fmap_comp C D U _ _ _
                (fmap[F] (fmap[U] (fmap[R] (lift_desc_arg f))))
                (fmap[F] (@unit _ _ _ _ A0 (U c)))).
  rewrite <- (@fmap_comp D C F _ _ _
                (fmap[U] (fmap[R] (lift_desc_arg f)))
                (@unit _ _ _ _ A0 (U c))).
  rewrite (lift_desc_transpose f).
  rewrite <- (@fmap_comp C D U _ _ _
                (@counit _ _ _ _ A (R b)) (fmap[F] (fmap[U] f))).
  rewrite (adj_counit_natural A f).
  exact (@fmap_comp C D U _ _ _ f (@counit _ _ _ _ A c)).
Qed.

Lemma lift_desc_cofork {c : C} {b : B} (f : c ~{C}~> R b) :
  lift_desc_arg f ∘ lift_pair_l c ≈ lift_desc_arg f ∘ lift_pair_r c.
Proof.
  transitivity (from (@adj _ _ _ _ A0 (U (F (U c))) b)
                  (fmap[U] f ∘ fmap[U] (@counit _ _ _ _ A c))).
  - symmetry.
    exact (@from_adj_nat_l _ _ _ _ A0 _ _ _
             (fmap[U] f) (fmap[U] (@counit _ _ _ _ A c))).
  - transitivity (from (@adj _ _ _ _ A0 (U (F (U c))) b)
                    (fmap[U] (fmap[R] (lift_desc_arg f)) ∘ lift_action c)).
    + exact (@from_adj_respects _ _ _ _ A0 _ _ _ _ (lift_desc_square f)).
    + exact (lift_untranspose_nat_r (lift_desc_arg f) (lift_action c)).
Qed.

Definition lift_desc {c : C} {b : B} (f : c ~{C}~> R b) :
  ∃! u : lift_obj c ~{B}~> b, u ∘ lift_e c ≈ lift_desc_arg f :=
  coeq_desc (lift_is_coeq c) (lift_desc_arg f) (lift_desc_cofork f).

Definition lift_factor {c : C} {b : B} (f : c ~{C}~> R b) :
  lift_obj c ~{B}~> b :=
  unique_obj (lift_desc f).

Definition lift_factor_e {c : C} {b : B} (f : c ~{C}~> R b) :
  lift_factor f ∘ lift_e c ≈ lift_desc_arg f :=
  unique_property (lift_desc f).

(* The factorization law: both sides have the same U-image, and U is
   faithful. *)
Lemma lift_factor_property {c : C} {b : B} (f : c ~{C}~> R b) :
  f ≈ fmap[R] (lift_factor f) ∘ lift_unit c.
Proof using A A0 B C D F L0 R RCB U faithK fullK.
  apply lift_faithful.
  rewrite (@fmap_comp C D U _ _ _ (fmap[R] (lift_factor f)) (lift_unit c)).
  rewrite (lift_unit_w c).
  transitivity (to (@adj _ _ _ _ A0 (U c) b) (lift_desc_arg f)).
  - symmetry.
    exact (@from_adj_comp_law _ _ _ _ A0 (U c) b (fmap[U] f)).
  - transitivity (to (@adj _ _ _ _ A0 (U c) b)
                    (lift_factor f ∘ lift_e c)).
    + symmetry.
      exact (@to_adj_respects _ _ _ _ A0 _ _ _ _ (lift_factor_e f)).
    + exact (lift_transpose_nat_r (lift_factor f) (lift_e c)).
Qed.

(* Uniqueness of the factorization: any other mediator descends the same
   map (compare transposes), so descent uniqueness identifies them. *)
Lemma lift_factor_unique {c : C} {b : B} (f : c ~{C}~> R b)
  (v : lift_obj c ~{B}~> b) (Hv : f ≈ fmap[R] v ∘ lift_unit c) :
  lift_factor f ≈ v.
Proof.
  apply (uniqueness (lift_desc f)).
  apply lift_transpose_inj.
  transitivity (fmap[U] (fmap[R] v) ∘ lift_w c).
  - exact (lift_transpose_nat_r v (lift_e c)).
  - transitivity (fmap[U] (fmap[R] v ∘ lift_unit c)).
    + rewrite (@fmap_comp C D U _ _ _ (fmap[R] v) (lift_unit c)).
      apply compose_respects.
      * reflexivity.
      * symmetry.
        exact (lift_unit_w c).
    + transitivity (fmap[U] f).
      * now rewrite Hv.
      * symmetry.
        exact (@from_adj_comp_law _ _ _ _ A0 (U c) b (fmap[U] f)).
Qed.

(** ** The universal arrows, and the lifted left adjoint *)

Definition lift_ump (c : C) (b : B) (f : c ~{C}~> R b) :
  ∃! g : lift_obj c ~{B}~> b, f ≈ fmap[R] g ∘ lift_unit c :=
  {| unique_obj      := lift_factor f
   ; unique_property := lift_factor_property f
   ; uniqueness      := fun v Hv => lift_factor_unique f v Hv |}.

Definition lift_universal_arrow (c : C) : UniversalArrow c R :=
  universal_arrow_from_UMP c R (lift_obj c) (lift_unit c)
    (fun b f => lift_ump c b f).

(** The adjoint triangle theorem (Dubuc): with U of descent type, a left
    adjoint of U ◯ R and reflexive coequalizers in B induce a left
    adjoint of R. *)

Definition Lifted_Left_Adjoint : C ⟶ B :=
  LeftAdjointFunctorFromUniversalArrows R lift_universal_arrow.

Definition adjoint_triangle : Lifted_Left_Adjoint ⊣ R :=
  AdjunctionFromUniversalArrows R lift_universal_arrow.

End AdjointTriangle.

(** ** Transport: adjunctions into the Eilenberg–Moore category descend *)

Section TransportEM.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (E : EquivalenceOfCategories (EM_Comparison A)).
Context {B : Category}.
Context {L : @EilenbergMoore D (U ◯ F) (Adjunction_Induced_Monad A) ⟶ B}.
Context {J : B ⟶ @EilenbergMoore D (U ◯ F) (Adjunction_Induced_Monad A)}.
Context (AJ : L ⊣ J).

(* An adjunction whose right adjoint lands in the Eilenberg-Moore
   category composes with the adjoint equivalence K ⊣ K⁻¹ of the
   comparison to one whose right adjoint lands in C. *)
Definition EM_Adjunction_Transport :
  (L ◯ EM_Comparison A) ⊣ (@quasi_inverse _ _ _ E ◯ J) :=
  Adjunction_Compose (equiv_adjunction E) AJ.

End TransportEM.

(** ** The crude-case adjoint lifting theorem *)

Section AdjointLiftingCrude.

Context {C : Category}.
Context {D : Category}.
Context {B : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (RC : HasReflexiveCoequalizers C).
Context (pres : PreservesReflexiveCoequalizers U).
Context (refl : ReflectsIsos U).
Context {R : B ⟶ C}.
Context {L0 : D ⟶ B}.
Context (A0 : L0 ⊣ U ◯ R).
Context (RCB : HasReflexiveCoequalizers B).

(* The crude monadicity equivalence makes the comparison full and
   faithful. *)
Definition adjoint_lifting_full : Full (EM_Comparison A) :=
  Equivalence_Full (crude_monadicity A RC pres refl).

Definition adjoint_lifting_faithful : Faithful (EM_Comparison A) :=
  Equivalence_Faithful (crude_monadicity A RC pres refl).

(** The adjoint lifting theorem, crude case: if F ⊣ U satisfies the
    crude monadicity hypotheses, then any functor R into C whose
    composite with U has a left adjoint itself has a left adjoint,
    provided the domain of R has reflexive coequalizers. *)

Theorem adjoint_lifting : ∃ L : C ⟶ B, L ⊣ R.
Proof using A A0 B C D F L0 R RC RCB U pres refl.
  exists (Lifted_Left_Adjoint A
            adjoint_lifting_full adjoint_lifting_faithful A0 RCB).
  exact (adjoint_triangle A
           adjoint_lifting_full adjoint_lifting_faithful A0 RCB).
Defined.

End AdjointLiftingCrude.

(** The same statement with the monadicity data packaged as [Monadic]. *)

Theorem adjoint_lifting_monadic {C D B : Category} {U : C ⟶ D}
  (M : Monadic U) {R : B ⟶ C} {L0 : D ⟶ B}
  (A0 : L0 ⊣ U ◯ R) (RCB : HasReflexiveCoequalizers B) :
  ∃ L : C ⟶ B, L ⊣ R.
Proof.
  exists (Lifted_Left_Adjoint (`1 (`2 M))
            (Equivalence_Full (`2 (`2 M)))
            (Equivalence_Faithful (`2 (`2 M))) A0 RCB).
  exact (adjoint_triangle (`1 (`2 M))
           (Equivalence_Full (`2 (`2 M)))
           (Equivalence_Faithful (`2 (`2 M))) A0 RCB).
Defined.
