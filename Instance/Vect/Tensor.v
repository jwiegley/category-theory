(* [Coq.QArith.QArith] is imported FIRST, before [Category.Lib]: it exports
   an [equiv] that shadows [Setoid]'s otherwise.  This is the import-order
   discipline Instance/FdVect.v records at its own head. *)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The tensor product of vector spaces, as a universal element

    nLab:      https://ncatlab.org/nlab/show/tensor+product
    nLab:      https://ncatlab.org/nlab/show/universal+element
    Wikipedia: https://en.wikipedia.org/wiki/Tensor_product
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          GTM 5, §III.1, printed p. 58 — maclane:III.1:construction6
    Book: Riehl, Category Theory in Context, Dover 2016, §2.3, printed
          p. 58 — riehl:2.3:example8

    THE HEADLINE.  Mac Lane's §III.1 and Riehl's §2.3 both state the
    tensor product for VECTOR SPACES: the functor carrying a space W to
    the set of bilinear maps V × V' → W is represented by V ⊗ V', with
    universal element the canonical bilinear map ⊗.  That statement is
    [vct_tensor_universal_element] below.

    WHERE THE WORK IS.  Instance/FdVect.v:223 defines
    [Vct_F F := RMod (field_ring F)]: a vector space over F IS an
    F-module, by DEFINITION and not by an isomorphism of categories.  So
    the construction uses nothing about fields and is carried out over an
    arbitrary [RingObject] in Instance/Mod/Tensor.v — the formal-
    expression carrier, the bilinear-maps functor, the mediator, the
    universal element and the non-degeneracy results all live there.
    This file is the vector-space reading, and because the two categories
    are the same term, every specialization below is a CONVERSION: each
    definition is stated with its [Vct_F]-level type and inhabited by the
    [RMod]-level term, so the kernel checks the identification rather
    than a transport doing it.  Nothing here reproves anything.

    WHAT THE FIELD LAYER BUYS, EXACTLY.  Not the universal property:
    Instance/Mod/Tensor.v proves that over an arbitrary ring, and
    commutativity is a hypothesis of none of the construction, the
    functor or the universal element there (that file's GENERALITY
    section states it exactly, including the one general lemma that DOES
    assume it).  What commutativity buys is that
    the tensor product does not collapse further than the classical
    construction does.  The engine file's [rbl_commutator] shows that
    every commutator of the scalar ring annihilates the image of every
    bilinear map, so over a non-commutative ring V ⊗ V' is smaller than a
    reader of the commutative case expects; [vct_commutator_vacuous]
    below is the record that over a field that identity is empty,
    obtained from [field_comm] alone.  Read the direction carefully: the
    hypothesis is absent upstream because the conclusion degenerates
    without it, NOT because the theorem is stronger than the classical
    one.

    Nothing below spends [finv] or [field_one_neq_zero].  A proper
    fraction does appear in both argument positions — as a VECTOR in
    [q_tensor_half_distinct] (½ ⊗ 1 is not 1 ⊗ 1) and as a SCALAR in
    [q_tensor_smul_half] and [q_tensor_smul_half_moves] (the action of ½
    moves 1 ⊗ 1) — so the witnesses do exercise ℚ rather than its prime
    subring; but nothing is ever inverted, and no claim is made here that
    the multiplicative-inverse structure is exercised.

    WHAT THE ℚ WITNESSES ADD OVER THE ℤ ONES.  Instance/Mod/Tensor.v
    already measures the construction at ℤ.  The point of repeating the
    measurement here is that ℤ's setoid equality is Leibniz [=], so the
    ℤ witnesses exercise no quotient at the SCALAR level; ℚ's is [Qeq],
    a genuine quotient (the terms [4#2] and [2#1] are distinct and
    [Qeq]-equal), so [Q_tensor_iso] is the only place in these two files
    where the tensor product is pinned over a scalar setoid that
    identifies distinct terms.  Test/ProbeModTensor.v guards the
    consequence: over ℤ the mediator's value at a closed generator is a
    numeral by [eq_refl], over ℚ it is not.

    WHAT IS NOT DELIVERED.  Everything the engine file's own
    WHAT IS NOT DELIVERED section lists — no bifunctoriality, no monoidal
    structure on [Vct_F F], no coefficient uniqueness, no comparison with
    Instance/Ab/Tensor.v — plus two readings specific to this level: no
    dimension theory (nothing here says dim(V ⊗ V') = dim V · dim V',
    and no connection to Instance/FdVect.v's based spaces or to
    Instance/FdVect/Tensor.v's [TensorSq], which is the diagonal square
    endofunctor of Riehl Ex 1.4.4(vii) and not a tensor product of two
    spaces at all), and no bilinear-forms specialization. *)

Section VectTensor.

Context (F : FieldObject).

(** ** Bilinear maps of vector spaces *)

(** The bilinear maps V × V' → W, at the vector-space level.  This is
    Instance/Mod/Tensor.v's [RBilinear] read through
    [Vct_F F = RMod (field_ring F)]. *)
Definition VctBilinear (V V' W : Vct_F F) : Type := RBilinear V V' W.

Example VctBilinear_is_RBilinear (V V' W : Vct_F F) :
  VctBilinear V V' W = RBilinear V V' W := eq_refl.

(** The bilinear-maps FUNCTOR Bilin(V, V'; −) : Vct_F F ⟶ Sets. *)
Definition VctBilin (V V' : Vct_F F) : Vct_F F ⟶ Sets := Bilin V V'.

(** ** The tensor product, and its canonical bilinear map *)

Definition VctTensor (V V' : Vct_F F) : Vct_F F := TensorMod V V'.

Definition vct_tensor_gen (V V' : Vct_F F) :
  VctBilinear V V' (VctTensor V V') := tensor_gen.

(** ** Mac Lane §III.1 / Riehl §2.3: ⟨V ⊗ V', ⊗⟩ is a universal element

    For every vector space W and every bilinear map β : V × V' → W there
    is one and only one linear map V ⊗ V' ⟶ W carrying ⊗ to β. *)
Definition vct_tensor_universal_element (V V' : Vct_F F) :
  AUniversalElement (VctBilin V V') (VctTensor V V') :=
  tensor_universal_element V V'.

(** The same data as Mac Lane's pair ⟨r, e⟩. *)
Definition vct_tensor_UniversalElement (V V' : Vct_F F) :
  UniversalElement (VctBilin V V') := tensor_UniversalElement V V'.

Example vct_tensor_UniversalElement_obj (V V' : Vct_F F) :
  @ue_obj (Vct_F F) (VctBilin V V') (vct_tensor_UniversalElement V V')
    = VctTensor V V' := eq_refl.

(** ** Unique factorization, elementwise *)

Definition vct_tensor_factor {V V' W : Vct_F F} (β : VctBilinear V V' W) :
  VctTensor V V' ~{Vct_F F}~> W := tensor_factor β.

Lemma vct_tensor_factor_commutes {V V' W : Vct_F F} (β : VctBilinear V V' W)
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom (vct_tensor_factor β)) (mt_gen v w) ≈ rbl_map β v w.
Proof. exact (tensor_factor_commutes β v w). Qed.

Lemma vct_tensor_factor_unique {V V' W : Vct_F F} (β : VctBilinear V V' W)
  (k : VctTensor V V' ~{Vct_F F}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom k) (mt_gen v w) ≈ rbl_map β v w) →
  vct_tensor_factor β ≈ k.
Proof. exact (tensor_factor_unique β k). Qed.

(** ** What commutativity buys

    The engine file's collapse identity, at a field: its conclusion
    already follows from [field_comm], with no bilinear map in sight, so
    over a field it says nothing.  That is the precise sense in which the
    construction above is the classical tensor product of vector
    spaces. *)
Lemma vct_commutator_vacuous (W : Vct_F F)
  (r s : carrier (rig_setoid (ring_rig (field_ring F))))
  (x : carrier (cmon_setoid W)) :
  rm_smul W (rig_mul (ring_rig (field_ring F)) r s) x
    ≈ rm_smul W (rig_mul (ring_rig (field_ring F)) s r) x.
Proof.
  exact (rbl_commutator_from_commutativity (field_comm F) W r s x).
Qed.

End VectTensor.

Arguments VctBilinear {F} V V' W.
Arguments VctBilin {F} V V'.
Arguments VctTensor {F} V V'.
Arguments vct_tensor_gen {F} V V'.
Arguments vct_tensor_universal_element {F} V V'.
Arguments vct_tensor_UniversalElement {F} V V'.
Arguments vct_tensor_factor {F V V' W} β.

(** ** Non-degeneracy over ℚ

    The field as a one-dimensional space over itself, with multiplication
    as the archetypal bilinear map — the ℤ measurements of
    Instance/Mod/Tensor.v repeated over a scalar setoid whose [≈] is a
    genuine quotient. *)

Definition Q_Vct : Vct_F Q_Field := Ring_RMod (field_ring Q_Field).

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses. *)
Local Notation qgen  := (@mt_gen (field_ring Q_Field) Q_Vct Q_Vct).
Local Notation qzero := (@mt_zero (field_ring Q_Field) Q_Vct Q_Vct).
Local Notation qsmul := (@mt_smul (field_ring Q_Field) Q_Vct Q_Vct).

Definition Q_mul_bilinear : VctBilinear Q_Vct Q_Vct Q_Vct.
Proof.
  unshelve notypeclasses refine
    (@Build_RBilinear (field_ring Q_Field) Q_Vct Q_Vct Q_Vct Qmult
       _ _ _ _ _).
  - (* rbl_respects *)
    intros a b Hab c d Hcd; simpl in *.
    now rewrite Hab, Hcd.
  - (* rbl_add_l *)
    intros v v' w; simpl; ring.
  - (* rbl_add_r *)
    intros v w w'; simpl; ring.
  - (* rbl_smul_l *)
    intros r v w; simpl; ring.
  - (* rbl_smul_r: the clause that spends commutativity of ℚ *)
    intros r v w; simpl; ring.
Defined.

(** The factorization computes: the mediator is a fixpoint, so its value
    on a closed generator reduces — up to [≈], which here is [Qeq] and so
    is a genuine quotient step rather than a syntactic identity. *)
Example q_tensor_med_computes :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. reflexivity. Qed.

Example q_tensor_factor_computes :
  cmon_map (rm_hom (vct_tensor_factor Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. reflexivity. Qed.

(** The quotient does not collapse, proved by mapping OUT through
    [tensor_med_respects]. *)
Lemma q_tensor_gen_nonzero : mt_eq (qgen 1 1) qzero → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(** The scalars really are ℚ: a proper fraction gives a generator
    distinct from the one at 1 — the counterpart of
    Instance/Vect/Free.v's [free_vect_half_not_one], and the one place
    below where a non-integer scalar does work. *)
Lemma q_tensor_half_distinct : mt_eq (qgen (1#2) 1) (qgen 1 1) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(** The same fraction in SCALAR position.  The first is the action rule
    at r = ½ (the product ½·1 reducing to the term [1#2], so the
    statement typechecks by conversion); the second says the action of ½
    genuinely moves the generator, which is what makes the scalar side of
    the module structure non-degenerate over a field rather than merely
    over its prime subring. *)
Lemma q_tensor_smul_half : mt_eq (qsmul (1#2) (qgen 1 1)) (qgen (1#2) 1).
Proof.
  exact (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct (1#2) 1 1).
Qed.

Lemma q_tensor_smul_half_moves : mt_eq (qsmul (1#2) (qgen 1 1)) (qgen 1 1) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(** ℚ ⊗_ℚ ℚ ≅ ℚ in [Vct_F Q_Field], by the same two legs as the ℤ case:
    multiplication one way, q ↦ q ⊗ 1 the other. *)
Program Definition q_tensor_unit :
  Q_Vct ~{Vct_F Q_Field}~> VctTensor Q_Vct Q_Vct := {|
  rm_hom := {| cmon_map := {|
    morphism        := fun q => qgen q 1;
    proper_morphism := fun a b Hab => mte_gen Hab (reflexivity 1) |} |}
|}.
Next Obligation.
  exact (@tensor_zero_l (field_ring Q_Field) Q_Vct Q_Vct 1).
Qed.
Next Obligation.
  intros a b; exact (@mte_add_l (field_ring Q_Field) Q_Vct Q_Vct a b 1).
Qed.
Next Obligation.
  intros r q;
    exact (mte_sym (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct r q 1)).
Qed.

Program Definition Q_tensor_iso :
  @Isomorphism (Vct_F Q_Field) (VctTensor Q_Vct Q_Vct) Q_Vct := {|
  to   := tensor_med Q_mul_bilinear;
  from := q_tensor_unit
|}.
Next Obligation.
  intro q; simpl; apply Qmult_1_r.
Qed.
Next Obligation.
  refine (tensor_hom_ext
            (q_tensor_unit ∘ tensor_med Q_mul_bilinear)
            (@id (Vct_F Q_Field) (VctTensor Q_Vct Q_Vct)) _).
  intros v w; simpl.
  (* (v·w) ⊗ 1 ≈ (w·v) ⊗ 1 ≈ w·(v ⊗ 1) ≈ v ⊗ (w·1) ≈ v ⊗ w. *)
  refine (mte_trans (@mte_gen (field_ring Q_Field) Q_Vct Q_Vct _ _ _ _
                       (Qmult_comm v w) (reflexivity 1)) _).
  refine (mte_trans
            (mte_sym (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct w v 1)) _).
  refine (mte_trans (@mte_act_r (field_ring Q_Field) Q_Vct Q_Vct w v 1) _).
  exact (@mte_gen (field_ring Q_Field) Q_Vct Q_Vct _ _ _ _
           (reflexivity v) (Qmult_1_r w)).
Qed.
