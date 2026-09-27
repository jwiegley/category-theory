(** * The commutator-ideal reflection is not trivial: upper-triangular UT2

    Riehl, "Category Theory in Context", §4.6, Example 4.6.13 (ii),
    printed p. 170 (PDF p. 190), read from the page image: "A similar
    construction defines a left adjoint to the inclusion CRing ↪ Ring
    of commutative rings into the category of all rings."  The
    reflection is Instance/Rng/Commutativize.v; this satellite shows at
    one ring that it does something.
    nLab: https://ncatlab.org/nlab/show/reflective+subcategory

    BACKGROUND.  A reflection is visibly non-trivial at an object outside
    the subcategory whose unit is not invertible and whose reflection is
    not the terminal object.  The witness is [UT2], the ring of
    upper-triangular 2×2 integer matrices [[a, b], [0, c]] carried as
    triples (a, b, c), built in Instance/Rng/Algebras/Associative.v
    together with the matrix units [ut2_e11] = E11 and
    [ut2_e12] = E12 and [UT2_not_commutative] (E11·E12 = E12 while
    E12·E11 = 0).  Instance/Rng/Quotient/OneSided.v uses the same ring
    for its one-sided ideals, and isolates it in a satellite for the
    same reason: [UT2]'s file brings modules the reflection does not
    need (Commutativize.v's header gives the closure counts).

    WHAT IS SHOWN.
      - UT2 is not an object of the subcategory
        ([UT2_not_commutative_ring]).
      - E12 is itself a commutator, E11·E12 − E12·E11, on the nose
        ([ut2_e12_commutator], [eq_refl]), so it lies in the commutator
        ideal ([ut2_e12_in_CommIdeal]) and the unit at UT2 identifies it
        with zero ([crng_unit_UT2_merges]).  E12 is not zero in UT2
        ([ut2_e12_nonzero]), so the unit is not invertible
        ([crng_unit_UT2_not_iso]).
      - The reflection is not the zero ring: the top-left entry
        (a, b, c) ↦ a is a ring map into ℤ ([ut2_diag1_hom]); exercising
        [crng_universal] on it, the mediator sends one to 1
        ([crng_UT2_med_one], [eq_refl]) and zero to 0, so one and zero
        stay apart in the quotient ([Commutativize_UT2_nonzero]).

    UNIVERSES, read by [About] under [Set Printing Universes] on all
    eleven named constants.  The binders name [a c p] where the
    statement is about the ring [UT2 : RingObject@{a c p}], [u p] where
    it is about [Rng@{u p}], [c] for [ut2_diag1 : ut2@{c} → Z], and
    nothing ([@{+}]) for the respectfulness witness [ut2_diag1_proper],
    whose levels are the setoids'.  THE BINDERS LIFT A [Set] PIN,
    measured: in an unannotated draft of this file [crng_unit_UT2_not_iso]
    read [IsIsomorphism@{u Set Set} (crng_unit@{…} UT2@{Set Set Set}) →
    False], [ut2_diag1_hom] was a map [UT2@{Set Set Set} →
    Int_Ring@{Set Set Set}], and [crng_UT2_med_one] and
    [Commutativize_UT2_nonzero] were at [Set] too.  The bare statement
    [IsIsomorphism (crng_unit UT2) → False], elaborated alone as a
    [Definition], is general, and the same proof under [@{p +}] is
    accepted, so the pin was an artefact of elaborating the unannotated
    theorem.  Here all four read [UT2@{p p p}] at a general [p]; no
    constant of this file prints [Set] in an instance.  No block carries
    an equation.  Five blocks carry [Set < u] on [Rng]'s object level,
    [Rng]'s own bound; the six ring-level constants carry none.  [UT2]'s
    carrier level is capped by the standard library's monomorphic
    [Logic_lemmas.equality.u0] in [UT2]'s own block ([About UT2]), and
    that cap, like every global universe here, is an upper bound.

    AXIOMS.  All fifteen constants of this module, the eleven above and
    the four [Program] obligations of [ut2_diag1_hom], are closed under
    the global context.

    NOT DELIVERED.
      - No computation of the whole quotient: that UT2/[UT2, UT2] is
        ℤ × ℤ through the two diagonal entries is not proved here; only
        E12 ↦ 0 and 1 ≉ 0 are.
      - No second witness, and no statement at a ring whose reflection
        collapses. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Commutativize.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** ** UT2 is not an object of the subcategory *)

Lemma UT2_not_commutative_ring@{a c p +} :
  IsCommutative (UT2 : RingObject@{a c p}) → False.
Proof. intro H; exact (UT2_not_commutative (H ut2_e11 ut2_e12)). Qed.

(** ** The unit at UT2 merges E12 with zero *)

(* E12 = E11·E12 − E12·E11 is itself a commutator. *)
Example ut2_e12_commutator@{a c p +} :
  rcomm (UT2 : RingObject@{a c p}) ut2_e11 ut2_e12 = ut2_e12 := eq_refl.

Lemma ut2_e12_in_CommIdeal@{a c p +} :
  InCommIdeal (UT2 : RingObject@{a c p}) ut2_e12.
Proof. exact (@ici_gen UT2 ut2_e11 ut2_e12). Defined.

Lemma crng_unit_UT2_merges@{u p +} :
  rig_map (crng_unit (UT2 : Rng@{u p})) ut2_e12
    ≈ rig_map (crng_unit (UT2 : Rng@{u p})) ut2_zero.
Proof.
  simpl; unfold rquot_rel; constructor.
  exact (@ici_resp UT2 ut2_e12 _ eq_refl ut2_e12_in_CommIdeal).
Qed.

Lemma ut2_e12_nonzero@{a c p +} :
  @equiv (carrier (rig_setoid (UT2 : RingObject@{a c p}))) _ ut2_e12 ut2_zero
    → False.
Proof. unfold ut2_e12, ut2_zero; simpl; unfold ut2_eqT; discriminate. Qed.

(* So the unit at UT2 is not invertible: the reflection is a proper
   quotient there. *)
Theorem crng_unit_UT2_not_iso@{u p +} :
  IsIsomorphism (crng_unit (UT2 : Rng@{u p})) → False.
Proof.
  intros [g _ Hgf].
  apply ut2_e12_nonzero.
  refine (transitivity (symmetry (Hgf ut2_e12)) _).
  refine (transitivity _ (Hgf ut2_zero)).
  exact (proper_morphism (rig_map g) _ _ crng_unit_UT2_merges).
Qed.

(** ** The reflection of UT2 is not the zero ring *)

(* The top-left entry is a ring map into ℤ, which is commutative. *)
Definition ut2_diag1@{c +} (x : ut2@{c}) : Z := fst (fst x).

#[local] Obligation Tactic := idtac.

(* The respectfulness witness is written out rather than left to
   instance resolution, as Associative.v does for [ut2_scal_proper]. *)
Definition ut2_diag1_proper@{+}
  : Proper (@equiv _ (is_setoid ut2_setoid_object)
              ==> @equiv _ (is_setoid Z_setoid_object)) ut2_diag1 :=
  fun x y H => f_equal ut2_diag1 H.

Program Definition ut2_diag1_hom@{u p +} :
  (UT2 : Rng@{u p}) ~{Rng@{u p}}~> Int_Ring := {|
  rig_map := {| morphism := ut2_diag1; proper_morphism := ut2_diag1_proper |}
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros [[a b] c] [[a' b'] c']; reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros [[a b] c] [[a' b'] c']; reflexivity. Qed.

(* Exercising the universal property on it separates one from zero in
   the quotient. *)
Example crng_UT2_med_one@{u p +} :
  rig_map `1 (unique_obj (crng_universal (UT2 : Rng@{u p}) Int_CRng
                            ut2_diag1_hom))
    (rig_one UT2) = 1%Z := eq_refl.

Theorem Commutativize_UT2_nonzero@{u p +} :
  @equiv (carrier (rig_setoid (Commutativize (UT2 : Rng@{u p})))) _
    (rig_one UT2) (rig_zero UT2) → False.
Proof.
  intro H.
  pose proof (proper_morphism
                (rig_map `1 (unique_obj
                               (crng_universal UT2 Int_CRng ut2_diag1_hom)))
                _ _ H) as E.
  simpl in E; discriminate E.
Qed.
