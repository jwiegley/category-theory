(** * Character groups and the double-dual evaluation *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qreduction.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §I.4, printed p. 17 (PDF 27) — maclane:I.4:construction3
              (the finite-iso and non-naturality halves are
              Instance/Ab/Character/Finite.v's and NonNatural.v's)
   nLab:      https://ncatlab.org/nlab/show/Pontryagin+duality
   Wikipedia: https://en.wikipedia.org/wiki/Pontryagin_duality

   Mac Lane's §I.4 example: the character group D(G) = hom(G, ℚ/ℤ) is
   contravariant in G, its square DD is a covariant endofunctor of Ab,
   and the evaluation family τ_G : G → DD(G), a ↦ (χ ↦ χ a), is
   natural in G — his second worked example of a natural
   transformation.  This file delivers the dualizing group, both
   functors, and the natural evaluation; the finite-iso theorem and
   the non-naturality remark live in the sibling files.

     - [QZ]: the circle group ℚ/ℤ as an [AbObject] — carrier ℚ,
       identified up to integer difference, with decidable ≈
     - [D_ob]/[D]: the character group and the contravariant functor
       [D : Ab^op ⟶ Ab], acting by precomposition
     - [DD]: the covariant double dual, defined directly (its action
       Ξ ↦ (χ ↦ Ξ (χ ∘ f)) makes the two flips visible)
     - [tau]/[tau_natural]/[tau_Transform]: the evaluation family and
       its naturality square, packaged as [Id ⟹ DD]

   Design:

   1. ℚ/ℤ, NOT ℝ/ℤ, AND WHY THAT IS FAITHFUL.  The book's dualizing
      group is the circle ℝ/ℤ; every character of a FINITE group
      lands in its torsion subgroup, which is exactly ℚ/ℤ, so on the
      finite abelian groups of the example the two dualizing choices
      agree.  ℚ/ℤ is chosen because the stdlib rationals are
      axiom-free while the reals import classical axioms
      (docs/AXIOMS.md) — the issue's disclosed restriction.

   2. THE QUOTIENT IS A SETOID, AND IT IS DECIDABLE.  A point of ℚ/ℤ
      is a rational; two are identified when they differ by an
      integer.  No quotient construction is needed — the setoid
      discipline IS the quotient — and the relation is decidable
      ([qz_dec]): x − y is an integer exactly when its [Qred]
      canonical form has denominator 1, by [Qred]'s completeness.
      Decidability is not consumed here, but the finite half of the
      development counts characters, and counting needs it.

   3. CHARACTERS FORM AN ABELIAN GROUP POINTWISE.  D(G) carries the
      hom-set [AbHom G QZ] with pointwise addition, zero, and
      negation; the hom-setoid is [CMonHom_Setoid]'s pointwise
      equality, reused rather than rebuilt.  [D] acts by
      precomposition; [DD] is defined directly rather than as a
      composite through [Ab^op], so its object and arrow actions
      unfold definitionally in the evaluation's naturality square. *)

(** ** The circle group ℚ/ℤ *)

(* x and y are identified when they differ by an integer. *)
Definition qz_eq (x y : Q) : Type := { z : Z & x - y == inject_Z z }.

Lemma qz_eq_refl (x : Q) : qz_eq x x.
Proof. exists 0%Z; ring. Qed.

Lemma qz_eq_sym (x y : Q) : qz_eq x y → qz_eq y x.
Proof.
  intros [z Hz]; exists (- z)%Z.
  rewrite inject_Z_opp.
  rewrite <- Hz; ring.
Qed.

Lemma qz_eq_trans (x y w : Q) : qz_eq x y → qz_eq y w → qz_eq x w.
Proof.
  intros [z1 H1] [z2 H2]; exists (z1 + z2)%Z.
  rewrite inject_Z_plus.
  rewrite <- H1, <- H2; ring.
Qed.

(* Qeq is a special case (difference zero). *)
Lemma qz_of_Qeq (x y : Q) : x == y → qz_eq x y.
Proof.
  intro H; exists 0%Z.
  rewrite H; ring.
Qed.

(* The canonical form of an integer has denominator 1, by the ggcd
   specification (gcd with 1 is 1). *)
Lemma Qred_inject_Z_den (z : Z) : Qden (Qred (inject_Z z)) = 1%positive.
Proof.
  unfold Qred, inject_Z; simpl.
  pose proof (Z.ggcd_gcd z 1) as Hg.
  pose proof (Z.ggcd_correct_divisors z 1) as Hd.
  destruct (Z.ggcd z 1) as [g [aa bb]]; simpl in *.
  destruct Hd as [Ha Hb].
  rewrite Z.gcd_1_r in Hg; subst g.
  rewrite Z.mul_1_l in Hb; subst bb.
  reflexivity.
Qed.

(* Decidability: the canonical form of an integer has denominator 1. *)
Lemma qz_eq_dec (x y : Q) : qz_eq x y + (qz_eq x y → False).
Proof.
  destruct (Pos.eq_dec (Qden (Qred (x - y))) 1%positive) as [He|He].
  - left.
    destruct (Qred (x - y)) as [n d] eqn:Er.
    simpl in He; subst d.
    exists n.
    pose proof (Qred_correct (x - y)) as Hc.
    rewrite Er in Hc.
    unfold inject_Z.
    apply Qeq_sym; exact Hc.
  - right.
    intros [z Hz].
    apply He.
    rewrite (Qred_complete _ _ Hz).
    apply Qred_inject_Z_den.
Qed.

(* The circle as an abelian group object: ℚ with the integer-difference
   setoid, addition, and negation. *)
Program Definition QZ : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := Q;
                      is_setoid := {| equiv := qz_eq |} |};
    cmon_zero := 0;
    cmon_plus := Qplus
  |};
  ab_neg := Qopp
|}.
Next Obligation.
  constructor.
  - exact qz_eq_refl.
  - exact qz_eq_sym.
  - exact qz_eq_trans.
Qed.
Next Obligation.
  intros x x' [z1 H1] y y' [z2 H2].
  exists (z1 + z2)%Z.
  rewrite inject_Z_plus.
  rewrite <- H1, <- H2; ring.
Qed.
Next Obligation.
  intros a b c; apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros a b; apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intro a; apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros x y [z Hz].
  exists (- z)%Z.
  rewrite inject_Z_opp.
  rewrite <- Hz; ring.
Qed.
Next Obligation.
  intro a; apply qz_of_Qeq; cbn; ring.
Qed.

(** ** The character group *)

(* The zero character. *)
Program Definition char_zero (G : AbObject) : AbHom G QZ := {|
  cmon_map := {| morphism := fun _ => 0 |}
|}.
Next Obligation.
  intros G x y H; apply qz_eq_refl.
Qed.
Next Obligation.
  intros G; apply qz_eq_refl.
Qed.
Next Obligation.
  intros G a b; apply qz_of_Qeq; cbn; ring.
Qed.

(* Pointwise sum of characters. *)
Program Definition char_plus (G : AbObject) (χ ψ : AbHom G QZ) :
  AbHom G QZ := {|
  cmon_map := {| morphism := fun a => cmon_map χ a + cmon_map ψ a |}
|}.
Next Obligation.
  intros G χ ψ x y H.
  apply QZ.(ab_cmon).(cmon_plus_respects);
    apply (proper_morphism (cmon_map _)); exact H.
Qed.
Next Obligation.
  intros G χ ψ.
  eapply qz_eq_trans.
  - apply QZ.(ab_cmon).(cmon_plus_respects);
      [ apply (cmon_map_zero χ) | apply (cmon_map_zero ψ) ].
  - apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ ψ a b.
  eapply qz_eq_trans.
  - apply QZ.(ab_cmon).(cmon_plus_respects);
      [ apply (cmon_map_plus χ) | apply (cmon_map_plus ψ) ].
  - apply qz_of_Qeq; cbn; ring.
Qed.

(* Pointwise negation of a character (a homomorphism because negation
   in ℚ/ℤ is additive). *)
Program Definition char_neg (G : AbObject) (χ : AbHom G QZ) :
  AbHom G QZ := {|
  cmon_map := {| morphism := fun a => - cmon_map χ a |}
|}.
Next Obligation.
  intros G χ x y H.
  apply QZ.(ab_neg_respects).
  apply (proper_morphism (cmon_map _)); exact H.
Qed.
Next Obligation.
  intros G χ.
  eapply qz_eq_trans.
  - apply QZ.(ab_neg_respects), (cmon_map_zero χ).
  - apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ a b.
  eapply qz_eq_trans.
  - apply QZ.(ab_neg_respects), (cmon_map_plus χ).
  - apply qz_of_Qeq; cbn; ring.
Qed.

(* The character group D(G) = hom(G, ℚ/ℤ), pointwise. *)
Program Definition D_ob (G : AbObject) : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := AbHom G QZ;
                      is_setoid := @CMonHom_Setoid G QZ |};
    cmon_zero := char_zero G;
    cmon_plus := char_plus G
  |};
  ab_neg := char_neg G
|}.
Next Obligation.
  intros G χ χ' Hχ ψ ψ' Hψ a; simpl.
  apply QZ.(ab_cmon).(cmon_plus_respects); [ exact (Hχ a) | exact (Hψ a) ].
Qed.
Next Obligation.
  intros G χ ψ ρ a; simpl.
  apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ ψ a; simpl.
  apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ a; simpl.
  apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ χ' Hχ a; simpl.
  apply QZ.(ab_neg_respects); exact (Hχ a).
Qed.
Next Obligation.
  intros G χ a; simpl.
  apply qz_of_Qeq; cbn; ring.
Qed.

(** ** The contravariant character functor *)

(* Precomposition: a homomorphism f : H → G pulls characters of G back
   to characters of H. *)
Program Definition char_precomp {G H : AbObject} (f : AbHom H G)
        (χ : AbHom G QZ) : AbHom H QZ := {|
  cmon_map := {| morphism := fun a => cmon_map χ (cmon_map f a) |}
|}.
Next Obligation.
  intros G H f χ x y Hxy.
  apply (proper_morphism (cmon_map χ)).
  apply (proper_morphism (cmon_map f)); exact Hxy.
Qed.
Next Obligation.
  intros G H f χ.
  eapply qz_eq_trans.
  - apply (proper_morphism (cmon_map χ)), (cmon_map_zero f).
  - apply (cmon_map_zero χ).
Qed.
Next Obligation.
  intros G H f χ a b.
  eapply qz_eq_trans.
  - apply (proper_morphism (cmon_map χ)), (cmon_map_plus f).
  - apply (cmon_map_plus χ).
Qed.

(* D : Ab^op ⟶ Ab, the contravariant character functor. *)
Program Definition D : Ab^op ⟶ Ab := {|
  fobj := fun G => D_ob G;
  fmap := fun G H (f : G ~{Ab^op}~> H) =>
    {| cmon_map := {| morphism := fun χ => char_precomp f χ |} |}
|}.
Next Obligation.
  intros G H f χ ψ Hχψ a; simpl.
  exact (Hχψ (cmon_map f a)).
Qed.
Next Obligation.
  intros G H f a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f χ ψ a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f g Hfg χ a; simpl.
  apply (proper_morphism (cmon_map χ)).
  exact (Hfg a).
Qed.
Next Obligation.
  intros G χ a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H K f g χ a; simpl.
  apply qz_eq_refl.
Qed.

(** ** The covariant double dual *)

(* Evaluation-style action: Ξ ↦ (χ ↦ Ξ (χ ∘ f)).  Defined directly so
   both flips are visible and everything unfolds in the naturality
   square. *)
Program Definition DD : Ab ⟶ Ab := {|
  fobj := fun G => D_ob (D_ob G);
  fmap := fun G H (f : G ~{Ab}~> H) =>
    {| cmon_map := {| morphism := fun Ξ =>
      {| cmon_map := {| morphism := fun χ : AbHom H QZ =>
           cmon_map Ξ (char_precomp f χ) |} |} |} |}
|}.
Next Obligation.
  intros G H f Ξ χ ψ Hχψ; simpl.
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  exact (Hχψ (cmon_map f a)).
Qed.
Next Obligation.
  intros G H f Ξ; simpl.
  eapply qz_eq_trans; [ | apply (cmon_map_zero Ξ) ].
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f Ξ χ ψ; simpl.
  eapply qz_eq_trans; [ | apply (cmon_map_plus Ξ) ].
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f Ξ Θ HΞΘ χ; simpl.
  exact (HΞΘ (char_precomp f χ)).
Qed.
Next Obligation.
  intros G H f χ; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f Ξ Θ χ; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f g Hfg Ξ χ; simpl.
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply (proper_morphism (cmon_map χ)).
  exact (Hfg a).
Qed.
Next Obligation.
  intros G Ξ χ; simpl.
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H K f g Ξ χ; simpl.
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply qz_eq_refl.
Qed.

(** ** The natural evaluation *)

(* The evaluation character of an element: χ ↦ χ a. *)
Program Definition tau_component {G : AbObject} (a : carrier (cmon_setoid G)) :
  AbHom (D_ob G) QZ := {|
  cmon_map := {| morphism := fun χ : AbHom G QZ => cmon_map χ a |}
|}.
Next Obligation.
  intros G a χ ψ Hχψ.
  exact (Hχψ a).
Qed.
Next Obligation.
  intros G a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G a χ ψ; simpl.
  apply qz_eq_refl.
Qed.

(* τ_G : G → DD(G), a ↦ (χ ↦ χ a). *)
Program Definition tau (G : AbObject) : G ~{Ab}~> DD G := {|
  cmon_map := {| morphism := fun a => tau_component a |}
|}.
Next Obligation.
  intros G x y Hxy χ; simpl.
  apply (proper_morphism (cmon_map χ)); exact Hxy.
Qed.
Next Obligation.
  intros G χ; simpl.
  apply (cmon_map_zero χ).
Qed.
Next Obligation.
  intros G a b χ; simpl.
  apply (cmon_map_plus χ).
Qed.

(* Mac Lane's naturality square: DD f ∘ τ_G ≈ τ_H ∘ f. *)
Lemma tau_natural {G H : AbObject} (f : G ~{Ab}~> H) :
  fmap[DD] f ∘ tau G ≈ tau H ∘ f.
Proof.
  intros a χ; simpl.
  apply qz_eq_refl.
Qed.

(* The evaluation family packaged as a natural transformation
   Id ⟹ DD. *)
Program Definition tau_Transform : Id[Ab] ⟹ DD := {|
  transform := tau
|}.
Next Obligation.
  intros G H f a χ; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f a χ; simpl.
  apply qz_eq_refl.
Qed.
