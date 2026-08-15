(** * No natural isomorphism G ≅ D(G): Mac Lane's remark *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Character.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §I.4, printed p. 17 (PDF 27) — maclane:I.4:remark1
   nLab:      https://ncatlab.org/nlab/show/natural+isomorphism

   Mac Lane's remark: although each finite abelian group is isomorphic
   to its own character group, no such family of isomorphisms is
   natural — in the only sense in which the question is well posed,
   naturality over the ISO-ONLY category, where the character functor
   becomes covariant by D' f := D (f⁻¹).  This file makes the negative
   half precise and proves it by one concrete violation.

     - [AbIso]: the groupoid core of Ab (Construction/Groupoid.v's
       [Groupoid], cited not rebuilt)
     - [D']: the covariant character functor on the core,
       D' f := D (f⁻¹)
     - [Z5]: ℤ/5 as an [AbObject] (carrier ℤ, identified modulo 5 —
       the same setoid-as-quotient discipline as [QZ])
     - [alpha]: the automorphism x ↦ 2·x of ℤ/5, with inverse
       x ↦ 3·x
     - [sigma_not_natural]: no isomorphism ℤ/5 ≅ D(ℤ/5) satisfies
       even the single naturality square at [alpha] (strong form;
       [sigma_family_not_natural] instantiates it for families, and
       [no_such_sigma_family] shows the family premise is itself
       uninhabited — ℤ has no nonzero 2-torsion while D(ℤ) does)

   Design:

   1. ONE AUTOMORPHISM SUFFICES.  The issue allows "a concrete
      two-object violation"; the violation here is at the two equal
      endpoints of one automorphism, which is stronger and simpler.
      The arithmetic: naturality of σ at α : x ↦ 2x demands
      σ ∘ α ≈ D(α⁻¹) ∘ σ.  Writing q := σ(1)(1) ∈ ℚ/ℤ, the left side
      evaluates σ(2)(1) = 2q by additivity of σ, and the right
      evaluates σ(1)(3) = 3q by additivity of characters (α⁻¹ is
      x ↦ 3x, since 2·3 = 6 ≡ 1 mod 5).  So 2q ≈ 3q in ℚ/ℤ, hence
      q ≈ 0, hence σ(1) is the zero character; but then
      σ(1) ≈ σ(0) while 1 ≉ 0 in ℤ/5, so σ is not injective —
      contradicting that it is an isomorphism.  This is Mac Lane's
      m² ≡ 1 obstruction in its smallest working clothes: for ℤ/p
      the argument needs an automorphism m with m ≢ m⁻¹, so p = 5
      with m = 2 is the first prime that works (p = 2, 3 have only
      m ≡ ±1, and every additive map already commutes with those).

   2. WHY THE STATEMENT LIVES AT ℤ/5 ALONE.  [sigma_not_natural]
      takes ONE isomorphism ℤ/5 ≅ D(ℤ/5) and the single square at
      [alpha] — not full naturality over [AbIso] (refuting the
      weaker hypothesis is the stronger theorem), and not a family
      over all of Ab (a family premise would make the statement
      vacuous: [no_such_sigma_family] below proves no such family
      exists at all, ℤ against D(ℤ) — an audit catch).  [D'] is
      nonetheless constructed in full, so the covariant reading the
      book names is in the tree, and the square hypothesis is
      literally the to-component of [D']-naturality at [alpha]. *)

(** ** The groupoid core and the covariant character functor *)

Definition AbIso : Category := Groupoid Ab.

(* D' f := D (f⁻¹): contravariance twisted through inversion makes the
   character functor covariant on the core. *)
Program Definition D' : AbIso ⟶ AbIso := {|
  fobj := fun G => D_ob G;
  fmap := fun G H (f : @Isomorphism Ab G H) =>
    {| to   := fmap[D] (from f)
     ; from := fmap[D] (to f) |}
|}.
Next Obligation.
  intros G H f χ a; simpl.
  apply (proper_morphism (cmon_map χ)).
  exact (iso_to_from f a).
Qed.
Next Obligation.
  intros G H f χ a; simpl.
  apply (proper_morphism (cmon_map χ)).
  exact (iso_from_to f a).
Qed.
Next Obligation.
  intros G H f g Hfg; split.
  - intros χ a; simpl.
    apply (proper_morphism (cmon_map χ)).
    exact (snd Hfg a).
  - intros χ a; simpl.
    apply (proper_morphism (cmon_map χ)).
    exact (fst Hfg a).
Qed.
Next Obligation.
  intros G; split; intros χ a; simpl; apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H K f g; split; intros χ a; simpl; apply qz_eq_refl.
Qed.

(** ** ℤ/5 *)

Definition z5_eq (x y : Z) : Type := { k : Z & (x - y = 5 * k)%Z }.

Lemma z5_eq_refl (x : Z) : z5_eq x x.
Proof. exists 0%Z; lia. Qed.

Lemma z5_eq_sym (x y : Z) : z5_eq x y → z5_eq y x.
Proof. intros [k Hk]; exists (- k)%Z; lia. Qed.

Lemma z5_eq_trans (x y w : Z) : z5_eq x y → z5_eq y w → z5_eq x w.
Proof. intros [k1 H1] [k2 H2]; exists (k1 + k2)%Z; lia. Qed.

Program Definition Z5 : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := Z;
                      is_setoid := {| equiv := z5_eq |} |};
    cmon_zero := 0%Z;
    cmon_plus := Z.add
  |};
  ab_neg := Z.opp
|}.
Next Obligation.
  constructor.
  - exact z5_eq_refl.
  - exact z5_eq_sym.
  - exact z5_eq_trans.
Qed.
Next Obligation.
  intros x x' [k1 H1] y y' [k2 H2].
  exists (k1 + k2)%Z; lia.
Qed.
Next Obligation.
  intros a b c; exists 0%Z; lia.
Qed.
Next Obligation.
  intros a b; exists 0%Z; lia.
Qed.
Next Obligation.
  intro a; exists 0%Z; lia.
Qed.
Next Obligation.
  intros x y [k Hk]; exists (- k)%Z; lia.
Qed.
Next Obligation.
  intro a; exists 0%Z; cbn; lia.
Qed.

(* 1 and 0 are distinct in ℤ/5. *)
Lemma z5_one_neq_zero : z5_eq 1 0 → False.
Proof. intros [k Hk]; lia. Qed.

(** ** The automorphism x ↦ 2x and the generator character *)

Program Definition z5_mul (m : Z) : Z5 ~{Ab}~> Z5 := {|
  cmon_map := {| morphism := fun x => (m * x)%Z |}
|}.
Next Obligation.
  intros m x y [k Hk]; exists (m * k)%Z; nia.
Qed.
Next Obligation.
  intro m; exists 0%Z; cbn; lia.
Qed.
Next Obligation.
  intros m a b; exists 0%Z; cbn; lia.
Qed.

(* x ↦ 2x is an isomorphism, with inverse x ↦ 3x (2·3 = 6 ≡ 1). *)
Program Definition alpha : @Isomorphism Ab Z5 Z5 := {|
  to   := z5_mul 2;
  from := z5_mul 3
|}.
Next Obligation.
  intro x; exists x.
  change ((2 * (3 * x) - x)%Z = (5 * x)%Z).
  lia.
Qed.
Next Obligation.
  intro x; exists x.
  change ((3 * (2 * x) - x)%Z = (5 * x)%Z).
  lia.
Qed.

(* The generator character of ℤ/5: x ↦ x/5 in ℚ/ℤ. *)
Program Definition chi1 : AbHom Z5 QZ := {|
  cmon_map := {| morphism := fun x : Z => (inject_Z x / 5)%Q |}
|}.
Next Obligation.
  intros x y [k Hk].
  exists k.
  assert (Hx : x = (y + 5 * k)%Z) by lia.
  subst x.
  rewrite inject_Z_plus.
  rewrite inject_Z_mult.
  field.
Qed.
Next Obligation.
  apply qz_of_Qeq; cbn; field.
Qed.
Next Obligation.
  intros a b.
  apply qz_of_Qeq; cbn.
  rewrite inject_Z_plus.
  field.
Qed.

(** ** The violation *)

(* The arithmetic heart: 2q ≈ 3q in ℚ/ℤ forces q ≈ 0 (subtract). *)
Lemma qz_two_three_zero (q : Q) :
  qz_eq (q + q) (q + (q + q)) → qz_eq q 0.
Proof.
  intros [z Hz].
  exists (- z)%Z.
  rewrite inject_Z_opp.
  rewrite <- Hz; ring.
Qed.

Section Violation.

Context (s0 : @Isomorphism Ab Z5 (D_ob Z5)).
Context (Hnat : ∀ x : Z,
  cmon_map (to s0) ((2 * x)%Z)
    ≈ char_precomp (z5_mul 3) (cmon_map (to s0) x)).

Set Default Proof Using "All".

Let s : Z5 ~{Ab}~> D_ob Z5 := to s0.
Let q : Q := cmon_map (cmon_map s 1%Z) 1%Z.

(* Doubling on the argument side: σ(2)(1) ≈ q + q. *)
Lemma sigma_two : cmon_map (cmon_map s 2%Z) 1%Z ≈ (q + q)%Q.
Proof.
  exact (cmon_map_plus s 1%Z 1%Z 1%Z).
Qed.

(* Tripling on the value side: σ(1)(3) ≈ q + (q + q). *)
Lemma sigma_three : cmon_map (cmon_map s 1%Z) 3%Z ≈ (q + (q + q))%Q.
Proof.
  eapply qz_eq_trans.
  - exact (cmon_map_plus (cmon_map s 1%Z) 1%Z 2%Z).
  - apply QZ.(ab_cmon).(cmon_plus_respects); [ apply qz_eq_refl | ].
    exact (cmon_map_plus (cmon_map s 1%Z) 1%Z 1%Z).
Qed.

(* The square at x := 1, evaluated at the group element 1, plus
   additivity on both sides: 2q ≈ 3q, so q ≈ 0. *)
Lemma q_zero : qz_eq q 0.
Proof.
  apply qz_two_three_zero.
  eapply qz_eq_trans; [ apply qz_eq_sym, sigma_two | ].
  eapply qz_eq_trans; [ exact (Hnat 1%Z 1%Z) | ].
  exact sigma_three.
Qed.

(* Multiples of a vanishing value vanish: σ(1)(n) ≈ 0 for the five
   residues, hence — through the mod-5 setoid — for every argument. *)
Lemma sigma_one_zero : ∀ x : Z, qz_eq (cmon_map (cmon_map s 1%Z) x) 0.
Proof.
  assert (Hstep : ∀ n : Z,
    qz_eq (cmon_map (cmon_map s 1%Z) n) 0 →
    qz_eq (cmon_map (cmon_map s 1%Z) (1 + n)%Z) 0).
  { intros n Hn.
    eapply qz_eq_trans.
    - exact (cmon_map_plus (cmon_map s 1%Z) 1%Z n).
    - eapply qz_eq_trans.
      + apply QZ.(ab_cmon).(cmon_plus_respects); [ exact q_zero | exact Hn ].
      + apply qz_of_Qeq; cbn; ring.
  }
  assert (H0 : qz_eq (cmon_map (cmon_map s 1%Z) 0%Z) 0)
    by exact (cmon_map_zero (cmon_map s 1%Z)).
  pose proof (Hstep _ H0) as H1.
  pose proof (Hstep _ H1) as H2.
  pose proof (Hstep _ H2) as H3.
  pose proof (Hstep _ H3) as H4.
  intro x.
  (* x is congruent mod 5 to its remainder r ∈ {0,1,2,3,4} *)
  pose proof (Z.mod_pos_bound x 5 ltac:(lia)) as Hb.
  assert (Hx : z5_eq x (x mod 5)).
  { exists (x / 5)%Z.
    pose proof (Z.div_mod x 5 ltac:(lia)); lia. }
  eapply qz_eq_trans.
  - apply (proper_morphism (cmon_map (cmon_map s 1%Z))), Hx.
  - destruct (Z.eq_dec (x mod 5) 0) as [E|n0]; [ rewrite E; exact H0 |].
    destruct (Z.eq_dec (x mod 5) 1) as [E|n1]; [ rewrite E; exact H1 |].
    destruct (Z.eq_dec (x mod 5) (1 + 1)) as [E|n2]; [ rewrite E; exact H2 |].
    destruct (Z.eq_dec (x mod 5) (1 + (1 + 1))) as [E|n3];
      [ rewrite E; exact H3 |].
    assert (E : (x mod 5 = 1 + (1 + (1 + 1)))%Z) by lia.
    rewrite E; exact H4.
Qed.

(* σ identifies 1 and 0, so — being an isomorphism — 1 ≈ 0 in ℤ/5:
   contradiction. *)
Theorem sigma_square_violation : False.
Proof.
  apply z5_one_neq_zero.
  (* 1 ≈ from(σ)(σ(1)) ≈ from(σ)(σ(0)) ≈ 0 *)
  pose proof (iso_from_to s0) as Hfi.
  eapply z5_eq_trans; [ apply z5_eq_sym, (Hfi 1%Z) | ].
  eapply z5_eq_trans; [ | apply (Hfi 0%Z) ].
  apply (proper_morphism (cmon_map (from s0))).
  intro x.
  eapply qz_eq_trans; [ apply (sigma_one_zero x) | ].
  apply qz_eq_sym.
  exact ((cmon_map_zero s) x).
Qed.

End Violation.

(* The packaged negative half, in its STRONG form: no isomorphism
   ℤ/5 ≅ D(ℤ/5) satisfies even the single naturality square at the
   automorphism x ↦ 2x — a fortiori, no natural family over the
   iso-only category [AbIso] with respect to [D'] exists. *)
Theorem sigma_not_natural (s0 : @Isomorphism Ab Z5 (D_ob Z5)) :
  (∀ x : Z,
     cmon_map (to s0) ((2 * x)%Z)
       ≈ char_precomp (z5_mul 3) (cmon_map (to s0) x)) →
  False.
Proof.
  intros Hnat.
  exact (sigma_square_violation s0 Hnat).
Qed.

(* The family form, for the record: any family σ_G : G ≅ D(G) over
   all abelian groups instantiates at ℤ/5.  This corollary's premise
   is in fact ITSELF uninhabited ([no_such_sigma_family] below), which
   is why the single-object statement above is the headline: it is the
   one with applicable content. *)
Corollary sigma_family_not_natural
          (σ : ∀ G : AbObject, @Isomorphism Ab G (D_ob G)) :
  (∀ x : Z,
     cmon_map (to (σ Z5)) ((2 * x)%Z)
       ≈ char_precomp (z5_mul 3) (cmon_map (to (σ Z5)) x)) →
  False.
Proof.
  intros Hnat.
  exact (sigma_not_natural (σ Z5) Hnat).
Qed.

(** ** Not even the objects match up globally *)

(* Away from finite groups the single-dual identification is already impossible
   already at the level of bare isomorphism: ℤ has no nonzero
   2-torsion, while D(ℤ) does — the half-character n ↦ n/2.  So a
   family σ_G : G ≅ D(G) over ALL abelian groups does not exist,
   independently of any naturality demand. *)

Definition ZZ : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := {| cmon_setoid := {| carrier := Z;
                                    is_setoid := eq_Setoid Z |};
                  cmon_zero := 0%Z;
                  cmon_plus := Z.add |};
    ab_neg := Z.opp |}.
  - intros x x' Hx y y' Hy.
    assert (Hx' : x = x') by exact Hx.
    assert (Hy' : y = y') by exact Hy.
    rewrite Hx', Hy'; reflexivity.
  - intros x y z; simpl; lia.
  - intros x y; simpl; lia.
  - intros x; simpl; lia.
  - intros x y Hxy.
    assert (Hxy2 : x = y) by exact Hxy.
    rewrite Hxy2; reflexivity.
  - intros x; simpl; lia.
Defined.

(* The half-character n ↦ n/2 of ℤ. *)
Definition chi_half : AbHom ZZ QZ.
Proof.
  unshelve notypeclasses refine
    (@Build_CMonHom ZZ QZ
       (@Build_SetoidMorphism
          (carrier (cmon_setoid ZZ)) _ (carrier (cmon_setoid QZ)) _
          (fun n : Z => (inject_Z n / 2)%Q) _) _ _).
  - intros x y Hxy.
    assert (Hxy' : x = y) by exact Hxy.
    rewrite Hxy'; apply qz_eq_refl.
  - apply qz_of_Qeq; reflexivity.
  - intros x y; apply qz_of_Qeq; simpl.
    rewrite inject_Z_plus; field.
Defined.

(* It is 2-torsion in D(ℤ)… *)
Lemma chi_half_double_zero :
  cmon_plus (D_ob ZZ) chi_half chi_half ≈ cmon_zero (D_ob ZZ).
Proof.
  intro n; simpl.
  apply (fun H => qz_eq_trans _ _ _ H (qz_eq_refl 0)).
  exists n; field.
Qed.

(* …but not itself zero… *)
Lemma chi_half_nonzero : (chi_half ≈ cmon_zero (D_ob ZZ)) → False.
Proof.
  intro H; destruct (H 1%Z) as [z Hz].
  unfold Qeq in Hz; simpl in Hz; lia.
Qed.

(* …while ℤ itself has no nonzero 2-torsion. *)
Lemma ZZ_no_2_torsion (m : carrier (cmon_setoid ZZ)) :
  cmon_plus ZZ m m ≈ cmon_zero ZZ → m ≈ cmon_zero ZZ.
Proof.
  intro H.
  change ((m + m)%Z = 0%Z) in H.
  change (m = 0%Z).
  lia.
Qed.

(* Hence no family of isomorphisms σ_G : G ≅ D(G) exists over all of
   Ab — the family corollary's premise is uninhabited, which is
   exactly why [sigma_not_natural] is stated at ℤ/5. *)
Theorem no_such_sigma_family :
  (∀ G : AbObject, @Isomorphism Ab G (D_ob G)) → False.
Proof.
  intro sigma.
  pose (f := to (sigma ZZ)).
  pose (g := from (sigma ZZ)).
  pose (m := cmon_map g chi_half).
  assert (Hfm : cmon_map f m ≈ chi_half)
    by exact (iso_to_from (sigma ZZ) chi_half).
  assert (Hd : cmon_map f (cmon_plus ZZ m m) ≈ cmon_zero (D_ob ZZ)).
  { transitivity (cmon_plus (D_ob ZZ) (cmon_map f m) (cmon_map f m)).
    - exact (cmon_map_plus f m m).
    - transitivity (cmon_plus (D_ob ZZ) chi_half chi_half).
      + exact (cmon_plus_respects (D_ob ZZ) _ _ Hfm _ _ Hfm).
      + exact chi_half_double_zero. }
  assert (Hm0 : m ≈ cmon_zero ZZ).
  { apply ZZ_no_2_torsion.
    transitivity (cmon_map g (cmon_map f (cmon_plus ZZ m m))).
    - symmetry; exact (iso_from_to (sigma ZZ) (cmon_plus ZZ m m)).
    - transitivity (cmon_map g (cmon_zero (D_ob ZZ))).
      + apply (proper_morphism (cmon_map g)); exact Hd.
      + exact (cmon_map_zero g). }
  apply chi_half_nonzero.
  transitivity (cmon_map f m).
  - symmetry; exact Hfm.
  - transitivity (cmon_map f (cmon_zero ZZ)).
    + apply (proper_morphism (cmon_map f)); exact Hm0.
    + exact (cmon_map_zero f).
Qed.
