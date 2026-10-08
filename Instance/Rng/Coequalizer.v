Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Quotient rings as coequalizers, split under the forgetful functor *)

(* Book:   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
           §VI.6 "Split Coequalizers", Exercise 1, book p. 150 (PDF
           p. 159), item maclane:VI.6:ex1, read from the page image; the
           group example it refers to is Instance/Grp/Coequalizer.v
   nLab:   https://ncatlab.org/nlab/show/split+coequalizer
   nLab:   https://ncatlab.org/nlab/show/quotient+ring
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_ring

   WHAT THE BOOK SAYS.  "In Rng give a similar construction to show that
   every quotient R/A of a ring R by an ideal A can be represented as a
   coequalizer, and show that the resulting fork is split after the
   application of the forgetful functors to sets."  Mac Lane's Rng is the
   category of rings with identity, as is the tree's [Rng]
   (Instance/Rng.v).

   THE CONSTRUCTION.  The book leaves it to the reader.  Here it is the
   group example's, additively: R ×₀ A has elements the pairs (r, a) with
   a ∈ A carrying its membership witness, added componentwise and
   multiplied by (r, a)(r', a') = (rr', (ra' + ar') + aa'), with unit
   (1, 0); ∂₀(r, a) = r and ∂₁(r, a) = r + a, the latter multiplicative
   because (r + a)(r' + a') expands to rr' + ((ra' + ar') + aa').  The
   ideal's two absorption laws put ra' and ar' in A, which is where
   two-sidedness is spent.  The ring laws of R ×₀ A are not expanded:
   (∂₀, ∂₁) is jointly injective ([rsdp_ext], cancelling r from r + a)
   and carries every operation to R's ([rsdp_d1_add], [rsdp_d1_mul] and
   the rest), so each law is R's, read twice.

   WHAT IS HERE, in the group file's order and with its names prefixed
   by r where they would collide.
     - [SemidirectRing A], [rsemidirect_d0], [rsemidirect_d1].
       [rsdp_d1_add] is Instance/CMon/Biproduct.v's middle-four
       interchange [cmon_plus_interchange] at R's additive monoid.
     - With no hypothesis: [rsemidirect_cofork],
       [rsemidirect_cofork_iff_kills] (a ring map coforks the pair
       exactly when it kills A), [rquot_proj_IsCoequalizer] (the descent
       being Instance/Rng/Quotient.v's mediator [rquot_med]) and
       [rsemidirect_U_cofork].
     - [RTransversal A] (a representative in each class, with the
       untruncated witness that s a - a ∈ A) and
       [Rng_U_split_iff_transversal]: the U-image pair has a split
       coequalizer if and only if A has a transversal; the splitting is
       [rtransversal_split], with t r = (r, s(p r) - r)
       ([rtransversal_t]), and [rsplit_transversal] reads a transversal
       off any splitting; then [rtransversal_U_IsCoequalizer] and
       [rtransversal_U_AbsoluteCoequalizer].
     - [Rng_U_IsCoequalizer_iff_untruncates]: U p is a coequalizer in
       Sets if and only if the class relation untruncates
       ([RCosetUntruncates]); [rtransversal_untruncates].
     - UNCONDITIONAL ALTERNATIVE, attempted and delivered: U corestricted
       to PropSets carries p to a coequalizer (not a split one):
       [Rng_ForgetP] factors [Rng_Forget] through Instance/Sets/
       Propositional/Full.v's [PropSets] by [rig_prop], and
       [PropSets_rquot_IsCoequalizer] holds with no hypothesis.  In
       [Sets] the coequalizer of the U-image pair is, with no
       hypothesis, the untruncated quotient [rquot_mem_object]
       ([rquot_mem_IsCoequalizer]), Instance/Sets/Quotient.v's
       [SetsQuotient] with [sets_quot_proj], its descent [sets_quot_med].
     - [Rng_split_iff_hom_rtransversal]: the pair splits in Rng itself
       exactly when p has a ring-homomorphic section with untruncated
       witnesses ([HomRTransversal]); t is then a ring map
       ([hom_rtransversal_t], again by joint injectivity).
     - Witnesses.  Transversals at A = R ([TotalIdeal_transversal], 0),
       at A trivial ([TrivialIdeal_transversal], the identity, a ring
       map, so the fork splits in Rng: [TrivialIdeal_Rng_split]) and at
       2Z ⊂ Z ([EvenIdeal_transversal], a ↦ a mod 2, over
       Instance/Rng/Quotient.v's [EvenIdeal]).  At 2Z the fork does not
       split in Rng ([EvenIdeal_not_split_in_Rng]): a ring map
       s : Z/2Z → Z has s(1 + 1) = 1 + 1 = 2, while 1 + 1 ≡ 0 sends it
       to s 0 = 0.

   THE CONSTRUCTIVE QUESTION is the group file's, with the class of r
   for the coset, and its two taboos are proved here at A_P ◁ Z ([AP]:
   all of Z when P holds and zero when it does not, its membership the
   Prop [or P (a = 0)]).  A transversal of A_P decides P
   ([AP_rtransversal_decides]), so Exercise 1's "split after the
   application of the forgetful functors", asked of every ideal,
   decides every proposition ([Rng_U_split_taboo]); and the class
   relation untruncates at A_P outright ([AP_untruncates]), so
   untruncation does not give a transversal constructively
   ([runtruncation_transversal_taboo]).  The group file's third
   statement, untruncation for every N being the untruncation principle
   (its N_S), is not repeated for ideals.

   THE TWINS are deliberate, for the reasons the group file's THE RING
   TWIN gives; the generic parts are Instance/Sets/Quotient.v's and
   Lib/Setoid/Propositional.v's, stated once.  A candidate this file
   does not take: [rquot_mem] and its four lemmas ([rquot_mem_of_equiv],
   [rquot_mem_refl], [rquot_mem_sym], [rquot_mem_trans]) repeat
   Instance/Rng/Quotient.v's [rquot_rel] lemmas without the truncation,
   where Instance/Grp/Quotient.v keeps the untruncated [quot_rel] and its
   lemmas upstream; Rng/Quotient.v could do the same and derive its
   [rquot_rel] ones, a change to that file left to the maintainer.

   STRENGTHS.  At [eq_refl]: the multiplication's two components
   ([rsdp_mul_fst], [rsdp_mul_snd]); ∂₀ and ∂₁ ([rsemidirect_d0_fun],
   [rsemidirect_d1_fun]); the descent IS [rquot_med]
   ([rquot_proj_IsCoequalizer_desc]); the splitting's e, s and t's
   second component s(p r) - r ([rtransversal_split_e],
   [rtransversal_split_s], [rtransversal_split_t_snd]); law 3 of each
   splitting, ∂₀ (t r) = r, pointwise ([rtransversal_split_law3],
   [hom_rtransversal_Rng_split_law3]); the round trip
   ([rtransversal_round_trip]); the transversal at 2Z
   ([EvenIdeal_transversal_fun]).  At ≈ only: the ring laws of R ×₀ A
   and laws 1, 2 and 4 of each splitting; law 4, ∂₁ (t r) =
   r + (s(p r) - r) against s(p r), is refused at [eq_refl]
   (Test/ProbeQuotient479.v, R4).

   UNIVERSES, by [About] on each of the 84 gated names (a script).  As
   in the group file: the construction binds R : RingObject@{u u0 u1}
   freely; the rest binds R : RingObject@{p p p} in the binder,
   [Rng@{u p}]'s object shape, and A : Ideal@{u p p p} R, the nine
   readbacks of the pair and its splittings outside the sections with
   the bound, @{p u + | u <= p +} (bare, their binders had u put at p
   by minimization, measured); no block carries an equation; every name
   generic in A that mentions the pair, a splitting of it, t or the
   untruncated quotient carries "u <= p", first at [rsemidirect_d0]
   (R6 refuses it at a membership level above the carrier, C15 and C16
   accept [rtransversal_untruncates] and [SemidirectRing] there, C18
   accepts [rtransversal_split_e] below it).  The witnesses
   at the total, trivial and even ideals, and [Rng_U_split_taboo] at
   A_P, take those ideals' membership level at the carrier level.
   [rquot_mem_object] is annotated at [SetoidObject@{p p}], and its
   equivalence is built from three lemmas in place, since a separate
   [Equivalence] lemma read "p = u" (measured).  [Rng_ForgetP] keeps the
   object levels of [Rng] and [PropSets] apart and
   [PropSets_rquot_IsCoequalizer] names them (go, so), through
   [Rng_ForgetP@{go p so}], the one explicit universe instance this file
   writes of a constant of its own, closed at three levels (three on
   Coq 8.19.2 and 8.20.1 as well).  No block mentions [Set] except as a
   bound "Set < _".  [rtransversal_U_AbsoluteCoequalizer] names its
   target levels.  On Coq 8.19.2 and 8.20.1 ([About] in a build of the
   files' closure and the probe under each) every one of the 84 names
   binds the same levels except [SemidirectRing], fifteen against Rocq
   9.1's ten, and its readbacks [rsdp_mul_fst] and [rsdp_mul_snd],
   eleven against nine; no explicit universe instance of them is
   written, and no block carries an equation.

   STALE PREMISES.  The group file's: Rng is stale since PR #1091
   (merged 2026-08-14, #257) and quotient rings since PR #1171 (merged
   2026-08-19, #314, Instance/Rng/Quotient.v).

   NOT DELIVERED.  A transversal for every ideal: the taboo above; R ×₀ A
   as the kernel pair of p; for ideals, the group file's N_S statement
   and its consequence for Monad/Monadicity/Crude.v (the pair's
   reflexivity is not built here); a ring isomorphism theorem
   (Instance/Rng/Quotient.v records why). *)

Section RngSemidirect.

Context {R : RingObject}.
Context (A : Ideal R).

(** ** The ideal as a setoid, compared on elements *)

Definition ideal_carrier : Type := { a : carrier (rig_setoid R) & idl_mem A a }.

Lemma ideal_equiv_Equivalence :
  Equivalence (fun p q : ideal_carrier => `1 p ≈ `1 q).
Proof.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; now symmetry.
  - intros p q r Hpq Hqr; now transitivity (`1 q).
Qed.

Definition ideal_setoid : Setoid ideal_carrier :=
  {| equiv := fun p q : ideal_carrier => `1 p ≈ `1 q
   ; setoid_equiv := ideal_equiv_Equivalence |}.

Definition ideal_PropEquiv : PropEquiv ideal_setoid.
Proof.
  unshelve refine (sigma_first_PropEquiv _ _ _ (rig_prop R)).
  - intros p q Hpq; exact Hpq.
  - intros p q Hpq; exact Hpq.
Defined.

(** ** R ×₀ A *)

Definition rsdp_carrier : Type := (carrier (rig_setoid R) * ideal_carrier)%type.

Definition rsdp_setoid : Setoid rsdp_carrier :=
  @prod_setoid _ _ (is_setoid (rig_setoid R)) ideal_setoid.

Definition rsdp_zero : rsdp_carrier :=
  (rig_zero R, @existT _ (idl_mem A) (rig_zero R) (idl_zero A)).

Definition rsdp_add (p q : rsdp_carrier) : rsdp_carrier :=
  (rig_add R (fst p) (fst q),
   @existT _ (idl_mem A) (rig_add R (`1 (snd p)) (`1 (snd q)))
     (idl_plus A _ _ (`2 (snd p)) (`2 (snd q)))).

Definition rsdp_one : rsdp_carrier :=
  (rig_one R, @existT _ (idl_mem A) (rig_zero R) (idl_zero A)).

(* (r, a)(r', a') = (rr', ra' + ar' + aa'). *)
Definition rsdp_mul (p q : rsdp_carrier) : rsdp_carrier :=
  (rig_mul R (fst p) (fst q),
   @existT _ (idl_mem A)
     (rig_add R (rig_add R (rig_mul R (fst p) (`1 (snd q)))
                           (rig_mul R (`1 (snd p)) (fst q)))
                (rig_mul R (`1 (snd p)) (`1 (snd q))))
     (idl_plus A _ _
        (idl_plus A _ _ (idl_absorb_l A (fst p) _ (`2 (snd q)))
                        (idl_absorb_r A _ (fst q) (`2 (snd p))))
        (idl_absorb_l A (`1 (snd p)) _ (`2 (snd q))))).

Definition rsdp_neg (p : rsdp_carrier) : rsdp_carrier :=
  (ring_neg R (fst p),
   @existT _ (idl_mem A) (ring_neg R (`1 (snd p))) (idl_neg A _ (`2 (snd p)))).

(* ∂₁(r, a) = r + a, on the raw carrier. *)
Definition rsdp_d1 (p : rsdp_carrier) : carrier (rig_setoid R) :=
  rig_add R (fst p) (`1 (snd p)).

(* The pair (∂₀, ∂₁) is jointly injective: the second component is
   recovered from r + a by cancelling r. *)
Lemma rsdp_ext (p q : rsdp_carrier) :
  fst p ≈ fst q → rsdp_d1 p ≈ rsdp_d1 q → @equiv _ rsdp_setoid p q.
Proof.
  intros H0 H1; split; [ exact H0 |].
  apply (ab_cancel_l (ring_ab R) (fst p)); simpl.
  unfold rsdp_d1 in H1.
  rewrite H1, H0; reflexivity.
Qed.

Lemma rsdp_d1_respects :
  Proper (@equiv _ rsdp_setoid ==> equiv) rsdp_d1.
Proof.
  intros [r [a Ha]] [r' [a' Ha']] [Hr Haa]; simpl in *.
  unfold rsdp_d1; simpl; now rewrite Hr, Haa.
Qed.

(* ∂₁ carries each operation of R ×₀ A to the one of R. *)
Lemma rsdp_d1_zero : rsdp_d1 rsdp_zero ≈ rig_zero R.
Proof. apply rig_add_zero_l. Qed.

Lemma rsdp_d1_one : rsdp_d1 rsdp_one ≈ rig_one R.
Proof. apply rig_add_zero_r. Qed.

(* The middle-four interchange of Instance/CMon/Biproduct.v, at R's
   additive monoid. *)
Lemma rsdp_d1_add (p q : rsdp_carrier) :
  rsdp_d1 (rsdp_add p q) ≈ rig_add R (rsdp_d1 p) (rsdp_d1 q).
Proof. unfold rsdp_d1; simpl; apply (cmon_plus_interchange (rig_cmon R)). Qed.

Lemma rsdp_d1_mul (p q : rsdp_carrier) :
  rsdp_d1 (rsdp_mul p q) ≈ rig_mul R (rsdp_d1 p) (rsdp_d1 q).
Proof.
  unfold rsdp_d1; simpl.
  rewrite rig_distr_r, !rig_distr_l.
  rewrite !rig_add_assoc.
  reflexivity.
Qed.

Lemma rsdp_d1_neg (p : rsdp_carrier) :
  rsdp_d1 (rsdp_neg p) ≈ ring_neg R (rsdp_d1 p).
Proof.
  unfold rsdp_d1; simpl.
  symmetry; exact (ab_neg_plus (ring_ab R) (fst p) (`1 (snd p))).
Qed.

Definition SemidirectRing : RingObject.
Proof using R A.
  unshelve notypeclasses refine {|
    ring_rig := {| rig_setoid := {| carrier := rsdp_carrier
                                  ; is_setoid := rsdp_setoid |}
                 ; rig_zero := rsdp_zero
                 ; rig_add := rsdp_add
                 ; rig_one := rsdp_one
                 ; rig_mul := rsdp_mul
                 ; rig_prop := prod_PropEquiv (rig_prop R) ideal_PropEquiv |};
    ring_neg := rsdp_neg
  |}.
  - (* rig_add_respects *)
    intros [r [a Ha]] [r' [a' Ha']] [Hr Haa] [s [b Hb]] [s' [b' Hb']] [Hs Hb0].
    simpl in *; split; simpl; now apply rig_add_respects.
  - (* rig_mul_respects *)
    intros [r [a Ha]] [r' [a' Ha']] [Hr Haa] [s [b Hb]] [s' [b' Hb']] [Hs Hb0].
    simpl in *; split; simpl.
    + now apply rig_mul_respects.
    + now rewrite Hr, Haa, Hs, Hb0.
  - (* rig_add_assoc *)
    intros p q s; apply rsdp_ext; simpl; [ apply rig_add_assoc |].
    rewrite !rsdp_d1_add; apply rig_add_assoc.
  - (* rig_add_comm *)
    intros p q; apply rsdp_ext; simpl; [ apply rig_add_comm |].
    rewrite !rsdp_d1_add; apply rig_add_comm.
  - (* rig_add_zero_l *)
    intros p; apply rsdp_ext; simpl; [ apply rig_add_zero_l |].
    rewrite rsdp_d1_add, rsdp_d1_zero; apply rig_add_zero_l.
  - (* rig_mul_assoc *)
    intros p q s; apply rsdp_ext; simpl; [ apply rig_mul_assoc |].
    rewrite !rsdp_d1_mul; apply rig_mul_assoc.
  - (* rig_mul_one_l *)
    intros p; apply rsdp_ext; simpl; [ apply rig_mul_one_l |].
    rewrite rsdp_d1_mul, rsdp_d1_one; apply rig_mul_one_l.
  - (* rig_mul_one_r *)
    intros p; apply rsdp_ext; simpl; [ apply rig_mul_one_r |].
    rewrite rsdp_d1_mul, rsdp_d1_one; apply rig_mul_one_r.
  - (* rig_distr_l *)
    intros p q s; apply rsdp_ext; simpl; [ apply rig_distr_l |].
    rewrite rsdp_d1_mul, !rsdp_d1_add, !rsdp_d1_mul; apply rig_distr_l.
  - (* rig_distr_r *)
    intros p q s; apply rsdp_ext; simpl; [ apply rig_distr_r |].
    rewrite rsdp_d1_mul, !rsdp_d1_add, !rsdp_d1_mul; apply rig_distr_r.
  - (* rig_mul_zero_l *)
    intros p; apply rsdp_ext; simpl; [ apply rig_mul_zero_l |].
    rewrite rsdp_d1_mul, rsdp_d1_zero; apply rig_mul_zero_l.
  - (* rig_mul_zero_r *)
    intros p; apply rsdp_ext; simpl; [ apply rig_mul_zero_r |].
    rewrite rsdp_d1_mul, rsdp_d1_zero; apply rig_mul_zero_r.
  - (* ring_neg_respects *)
    intros [r [a Ha]] [r' [a' Ha']] [Hr Haa]; simpl in *.
    split; simpl; now rewrite ?Hr, ?Haa.
  - (* ring_neg_l *)
    intros p; apply rsdp_ext; simpl; [ apply ring_neg_l |].
    rewrite rsdp_d1_add, rsdp_d1_neg, rsdp_d1_zero; apply ring_neg_l.
Defined.

End RngSemidirect.

(* U corestricted to the propositional setoids, by [rig_prop], as the
   group file's [Grp_ForgetP]. *)
Definition Rng_ForgetP@{u p so | p < so +} : Rng@{u p} ⟶ PropSets@{p so} :=
  PropSets_lift Rng_Forget (fun R => rig_prop R).

(* The pair, the coequalizer and the splitting live in [Rng], whose objects
   are [RingObject@{p p p}]; the binder says so. *)

Section RngSemidirectPair.

Universe p.

Context {R : RingObject@{p p p}}.
Context (A : Ideal R).

(** ** The parallel pair ∂₀, ∂₁ : R ×₀ A ⇉ R *)

(* ∂₀(r, a) = r. *)
Definition rsemidirect_d0 : SemidirectRing A ~{Rng}~> R.
Proof.
  unshelve refine
    (@Build_RigHom (SemidirectRing A) R
       {| morphism := fun p : rsdp_carrier A => fst p
        ; proper_morphism := fun p q (Hpq : @equiv _ (rsdp_setoid A) p q) =>
            fst Hpq |} _ _ _ _).
  - reflexivity.
  - intros p q; reflexivity.
  - reflexivity.
  - intros p q; reflexivity.
Defined.

(* ∂₁(r, a) = r + a. *)
Definition rsemidirect_d1 : SemidirectRing A ~{Rng}~> R.
Proof.
  unshelve refine
    (@Build_RigHom (SemidirectRing A) R
       {| morphism := rsdp_d1 A ; proper_morphism := rsdp_d1_respects A |}
       _ _ _ _).
  - exact (rsdp_d1_zero A).
  - exact (rsdp_d1_add A).
  - exact (rsdp_d1_one A).
  - exact (rsdp_d1_mul A).
Defined.

(** ** The projection coforks the pair, and is its coequalizer *)

Lemma rsemidirect_cofork :
  rquot_proj A ∘ rsemidirect_d0 ≈ rquot_proj A ∘ rsemidirect_d1.
Proof.
  intros [r [a Ha]]; simpl.
  constructor.
  apply (idl_at A (a := ring_neg R a)); [| exact (idl_neg A a Ha) ].
  transitivity (ab_neg (ring_ab R)
                  (ab_sub (ring_ab R) (rig_add R r a) r)).
  - apply ring_neg_respects.
    symmetry; exact (ab_sub_add_cancel (ring_ab R) r a).
  - exact (ab_sub_neg (ring_ab R) (rig_add R r a) r).
Qed.

Lemma rsemidirect_cofork_kills {K : RingObject} (h : R ~{Rng}~> K) :
  h ∘ rsemidirect_d0 ≈ h ∘ rsemidirect_d1 →
  ∀ a : carrier (rig_setoid R), idl_mem A a → rig_map h a ≈ rig_zero K.
Proof.
  intros Hh a Ha.
  pose proof (Hh (rig_zero R, @existT _ (idl_mem A) a Ha)) as E.
  simpl in E.
  transitivity (rig_map h (rig_add R (rig_zero R) a)).
  - apply (proper_morphism (rig_map h)).
    symmetry; apply rig_add_zero_l.
  - unfold rsdp_d1 in E; simpl in E.
    rewrite <- E.
    apply (rig_map_zero h).
Qed.

Lemma kills_rsemidirect_cofork {K : RingObject} (h : R ~{Rng}~> K) :
  (∀ a : carrier (rig_setoid R), idl_mem A a → rig_map h a ≈ rig_zero K) →
  h ∘ rsemidirect_d0 ≈ h ∘ rsemidirect_d1.
Proof.
  intros Hk [r [a Ha]]; simpl.
  unfold rsdp_d1; simpl.
  rewrite (rig_map_add h), (Hk a Ha).
  symmetry; apply rig_add_zero_r.
Qed.

Definition rsemidirect_cofork_iff_kills {K : RingObject} (h : R ~{Rng}~> K) :
  h ∘ rsemidirect_d0 ≈ h ∘ rsemidirect_d1
    ↔ (∀ a : carrier (rig_setoid R), idl_mem A a →
         rig_map h a ≈ rig_zero K) :=
  (rsemidirect_cofork_kills h, kills_rsemidirect_cofork h).

(* The descent is the quotient's own mediator [rquot_med]. *)
Definition rquot_proj_IsCoequalizer :
  IsCoequalizer rsemidirect_d0 rsemidirect_d1 (QuotientRing A) (rquot_proj A).
Proof.
  unshelve econstructor.
  - exact rsemidirect_cofork.
  - intros K h Hh.
    exact {| unique_obj :=
               rquot_med A (existT _ h (rsemidirect_cofork_kills h Hh));
             unique_property :=
               rquot_med_commutes A
                 (existT _ h (rsemidirect_cofork_kills h Hh));
             uniqueness :=
               rquot_med_unique A
                 (existT _ h (rsemidirect_cofork_kills h Hh)) |}.
Defined.

(* The U-image is a fork, with no hypothesis: the image of the cofork. *)
Lemma rsemidirect_U_cofork :
  fmap[Rng_Forget] (rquot_proj A) ∘ fmap[Rng_Forget] rsemidirect_d0
    ≈ fmap[Rng_Forget] (rquot_proj A) ∘ fmap[Rng_Forget] rsemidirect_d1.
Proof. intro p; exact (rsemidirect_cofork p). Qed.

(** ** Transversals, and the splitting after the forgetful functor *)

(* A transversal of A: a map of setoids out of U(R/A) choosing a
   representative of each coset, with the untruncated witness that the
   representative lies in the coset it represents. *)
Record RTransversal := {
  rtransversal_map :
    fobj[Rng_Forget] (QuotientRing A) ~{Sets}~> fobj[Rng_Forget] R;
  rtransversal_coset : ∀ a : carrier (rig_setoid R),
    idl_mem A (ab_sub (ring_ab R) (rtransversal_map a) a)
}.

(* The additive form of Mac Lane's t: t r = (r, s(p r) - r). *)
Definition rtransversal_t (T : RTransversal) :
  fobj[Rng_Forget] R ~{Sets}~> fobj[Rng_Forget] (SemidirectRing A).
Proof.
  unshelve refine {| morphism := fun r : carrier (rig_setoid R) =>
    (r, @existT _ (idl_mem A)
          (ab_sub (ring_ab R)
             (rtransversal_map T (rig_map (rquot_proj A) r)) r)
          (rtransversal_coset T r)) |}.
  intros r r' Hr; split; simpl.
  - exact Hr.
  - apply (ab_sub_respects (ring_ab R)); [| exact Hr ].
    apply (proper_morphism (rtransversal_map T)).
    exact (proper_morphism (rig_map (rquot_proj A)) _ _ Hr).
Defined.

Definition rtransversal_split (T : RTransversal) :
  SplitCoequalizer (fmap[Rng_Forget] rsemidirect_d0)
                   (fmap[Rng_Forget] rsemidirect_d1).
Proof.
  unshelve refine
    {| scoeq_obj := fobj[Rng_Forget] (QuotientRing A)
     ; scoeq_e   := fmap[Rng_Forget] (rquot_proj A)
     ; scoeq_s   := rtransversal_map T
     ; scoeq_t   := rtransversal_t T |}.
  - exact rsemidirect_U_cofork.
  - intro a; simpl.
    constructor; exact (rtransversal_coset T a).
  - intro r; simpl; reflexivity.
  - intro r; simpl; unfold rsdp_d1; simpl.
    exact (ab_add_sub_cancel (ring_ab R) (rtransversal_map T r) r).
Defined.

(* Any map out of U R that coforks the U-image pair is constant on cosets,
   given the coset witness untruncated: a ~ b is read off (b, a - b). *)
Lemma rU_cofork_descends {Z : obj[Sets]}
  (h : fobj[Rng_Forget] R ~{Sets}~> Z)
  (Hh : h ∘ fmap[Rng_Forget] rsemidirect_d0
          ≈ h ∘ fmap[Rng_Forget] rsemidirect_d1)
  (a b : carrier (rig_setoid R)) :
  idl_mem A (ab_sub (ring_ab R) a b) → h a ≈ h b.
Proof.
  intro Hab.
  pose proof (Hh (b, @existT _ (idl_mem A) _ Hab)) as E.
  simpl in E; unfold rsdp_d1 in E; simpl in E.
  transitivity (h (rig_add R b (ab_sub (ring_ab R) a b))).
  - apply (proper_morphism h).
    symmetry; exact (ab_add_sub_cancel (ring_ab R) a b).
  - symmetry; exact E.
Qed.

(* Conversely, ANY split coequalizer of the U-image pair yields a
   transversal. *)

Definition rsplit_transversal
  (S : SplitCoequalizer (fmap[Rng_Forget] rsemidirect_d0)
                        (fmap[Rng_Forget] rsemidirect_d1)) : RTransversal.
Proof.
  unshelve refine
    {| rtransversal_map :=
         {| morphism := fun a : carrier (rig_setoid R) =>
              scoeq_s S (scoeq_e S a) |} |}.
  - intros a b Hab.
    apply (@pequiv_to _ _ (rig_prop R)).
    change (inhabited (idl_mem A (ab_sub (ring_ab R) a b))) in Hab.
    destruct Hab as [Hab].
    apply (@pequiv_from _ _ (rig_prop R)).
    apply (proper_morphism (scoeq_s S)).
    exact (rU_cofork_descends (scoeq_e S) (scoeq_law1 S) a b Hab).
  - intro a; simpl.
    pose proof (scoeq_law3 S a) as E3.
    pose proof (scoeq_law4 S a) as E4.
    simpl in E3, E4.
    destruct (scoeq_t S a) as [x' [n Hn]]; simpl in E3, E4.
    unfold rsdp_d1 in E4; simpl in E4.
    apply (idl_at A (a := n)); [| exact Hn ].
    rewrite <- E4, E3.
    symmetry; exact (ab_sub_add_cancel (ring_ab R) a n).
Defined.

Definition Rng_U_split_iff_transversal :
  SplitCoequalizer (fmap[Rng_Forget] rsemidirect_d0)
                   (fmap[Rng_Forget] rsemidirect_d1) ↔ RTransversal :=
  (rsplit_transversal, rtransversal_split).

Definition rtransversal_U_IsCoequalizer (T : RTransversal) :
  IsCoequalizer (fmap[Rng_Forget] rsemidirect_d0)
    (fmap[Rng_Forget] rsemidirect_d1)
    (fobj[Rng_Forget] (QuotientRing A)) (fmap[Rng_Forget] (rquot_proj A)) :=
  split_coequalizer_is_coequalizer _ _ (rtransversal_split T).

Definition rtransversal_U_AbsoluteCoequalizer@{xo xh +} (T : RTransversal) :
  AbsoluteCoequalizer@{_ _ xo xh _} (fmap[Rng_Forget] rsemidirect_d0)
    (fmap[Rng_Forget] rsemidirect_d1)
    (fobj[Rng_Forget] (QuotientRing A)) (fmap[Rng_Forget] (rquot_proj A)) :=
  split_coequalizer_absolute (rtransversal_split T).

(** ** Whether U preserves the coequalizer: exactly when cosets untruncate *)

Definition rquot_mem (a b : carrier (rig_setoid R)) : Type :=
  idl_mem A (ab_sub (ring_ab R) a b).

Definition RCosetUntruncates : Type :=
  ∀ a b : carrier (rig_setoid R), rquot_rel A a b → rquot_mem a b.

Lemma rquot_mem_of_equiv (a b : carrier (rig_setoid R)) :
  a ≈ b → rquot_mem a b.
Proof.
  intro Hab; unfold rquot_mem.
  apply (idl_at A (a := rig_zero R)); [| exact (idl_zero A) ].
  change (rig_zero R) with (cmon_zero (ring_ab R)).
  rewrite <- Hab.
  symmetry; apply (ab_sub_self (ring_ab R)).
Qed.

Lemma rquot_mem_refl (a : carrier (rig_setoid R)) : rquot_mem a a.
Proof. apply rquot_mem_of_equiv; reflexivity. Qed.

Lemma rquot_mem_sym (a b : carrier (rig_setoid R)) :
  rquot_mem a b → rquot_mem b a.
Proof.
  intro K; unfold rquot_mem in *.
  apply (idl_at A (a := ring_neg R (ab_sub (ring_ab R) a b))).
  - apply (ab_sub_neg (ring_ab R)).
  - exact (idl_neg A _ K).
Qed.

Lemma rquot_mem_trans (a b c : carrier (rig_setoid R)) :
  rquot_mem a b → rquot_mem b c → rquot_mem a c.
Proof.
  intros K1 K2; unfold rquot_mem in *.
  apply (idl_at A (a := rig_add R (ab_sub (ring_ab R) a b)
                                 (ab_sub (ring_ab R) b c))).
  - apply (ab_sub_trans (ring_ab R)).
  - exact (idl_plus A _ _ K1 K2).
Qed.

(* The untruncated quotient, Instance/Sets/Quotient.v's [SetsQuotient], and
   its projection [sets_quot_proj], as in the group file. *)
Definition rquot_mem_object : SetoidObject@{p p} :=
  SetsQuotient (rig_setoid R) rquot_mem
    {| Equivalence_Reflexive := rquot_mem_refl
     ; Equivalence_Symmetric := rquot_mem_sym
     ; Equivalence_Transitive := rquot_mem_trans |}.

Definition rquot_mem_proj : fobj[Rng_Forget] R ~{Sets}~> rquot_mem_object :=
  sets_quot_proj (rig_setoid R) rquot_mem _ rquot_mem_of_equiv.

Lemma rquot_mem_proj_cofork :
  rquot_mem_proj ∘ fmap[Rng_Forget] rsemidirect_d0
    ≈ rquot_mem_proj ∘ fmap[Rng_Forget] rsemidirect_d1.
Proof.
  intros [r [a Ha]]; simpl; unfold rquot_mem, rsdp_d1; simpl.
  apply (idl_at A (a := ring_neg R a)); [| exact (idl_neg A a Ha) ].
  transitivity (ab_neg (ring_ab R)
                  (ab_sub (ring_ab R) (rig_add R r a) r)).
  - apply ring_neg_respects.
    symmetry; exact (ab_sub_add_cancel (ring_ab R) r a).
  - exact (ab_sub_neg (ring_ab R) (rig_add R r a) r).
Qed.

(* With no hypothesis, the coequalizer in Sets of the U-image pair is the
   untruncated quotient, by [sets_quot_med] at [rU_cofork_descends]. *)
Definition rquot_mem_IsCoequalizer :
  IsCoequalizer (fmap[Rng_Forget] rsemidirect_d0)
    (fmap[Rng_Forget] rsemidirect_d1) rquot_mem_object rquot_mem_proj.
Proof.
  unshelve econstructor.
  - exact rquot_mem_proj_cofork.
  - intros Z h Hh.
    exact {| unique_obj :=
               sets_quot_med rquot_mem _
                 (existT _ h (rU_cofork_descends h Hh));
             unique_property :=
               sets_quot_med_commutes rquot_mem _ rquot_mem_of_equiv
                 (existT _ h (rU_cofork_descends h Hh));
             uniqueness :=
               sets_quot_med_unique rquot_mem _ rquot_mem_of_equiv
                 (existT _ h (rU_cofork_descends h Hh)) |}.
Defined.

Lemma rU_IsCoequalizer_untruncates
  (E : IsCoequalizer (fmap[Rng_Forget] rsemidirect_d0)
         (fmap[Rng_Forget] rsemidirect_d1)
         (fobj[Rng_Forget] (QuotientRing A))
         (fmap[Rng_Forget] (rquot_proj A))) :
  RCosetUntruncates.
Proof.
  intros a b Hab.
  pose (D := coeq_desc E rquot_mem_proj rquot_mem_proj_cofork).
  pose proof (unique_property D) as Hu.
  pose proof (proper_morphism (unique_obj D) a b Hab) as Hab'.
  apply (rquot_mem_trans a (unique_obj D a)).
  - apply rquot_mem_sym; exact (Hu a).
  - apply (rquot_mem_trans _ (unique_obj D b)); [ exact Hab' | exact (Hu b) ].
Qed.

Definition untruncates_rU_IsCoequalizer (D : RCosetUntruncates) :
  IsCoequalizer (fmap[Rng_Forget] rsemidirect_d0)
    (fmap[Rng_Forget] rsemidirect_d1)
    (fobj[Rng_Forget] (QuotientRing A)) (fmap[Rng_Forget] (rquot_proj A)).
Proof.
  unshelve econstructor.
  - exact rsemidirect_U_cofork.
  - intros Z h Hh.
    unshelve eapply Build_Unique.
    + refine {| morphism := fun a : carrier (rig_setoid R) => h a |}.
      intros a b Hab.
      exact (rU_cofork_descends h Hh a b (D a b Hab)).
    + intro x; reflexivity.
    + intros v Hv x; symmetry; exact (Hv x).
Defined.

Definition Rng_U_IsCoequalizer_iff_untruncates :
  IsCoequalizer (fmap[Rng_Forget] rsemidirect_d0)
    (fmap[Rng_Forget] rsemidirect_d1)
    (fobj[Rng_Forget] (QuotientRing A)) (fmap[Rng_Forget] (rquot_proj A))
    ↔ RCosetUntruncates :=
  (rU_IsCoequalizer_untruncates, untruncates_rU_IsCoequalizer).

(* A transversal untruncates the cosets, directly: a ~ s a ≈ s b ~ b. *)
Lemma rtransversal_untruncates (T : RTransversal) : RCosetUntruncates.
Proof.
  intros a b Hab.
  assert (Hs : rtransversal_map T a ≈ rtransversal_map T b)
    by exact (proper_morphism (rtransversal_map T) a b Hab).
  apply (rquot_mem_trans a (rtransversal_map T a)).
  - apply rquot_mem_sym; exact (rtransversal_coset T a).
  - apply (rquot_mem_trans _ (rtransversal_map T b)).
    + exact (rquot_mem_of_equiv _ _ Hs).
    + exact (rtransversal_coset T b).
Qed.

(** ** Unconditionally: U into the propositional setoids preserves p *)

(* As the group file's [PropSets_quot_IsCoequalizer]: not a split one. *)
Definition PropSets_rquot_IsCoequalizer@{go so +} :
  IsCoequalizer (fmap[Rng_ForgetP@{go p so}] rsemidirect_d0)
    (fmap[Rng_ForgetP@{go p so}] rsemidirect_d1)
    (fobj[Rng_ForgetP@{go p so}] (QuotientRing A))
    (fmap[Rng_ForgetP@{go p so}] (rquot_proj A)).
Proof.
  unshelve econstructor.
  - exact rsemidirect_U_cofork.
  - intros Z h Hh.
    unshelve eapply Build_Unique.
    + unshelve eexists; [ | exact I ].
      unshelve refine (@Build_SetoidMorphism _ _ _ _
                         (fun a : carrier (rig_setoid R) => projT1 h a) _).
      intros a b Hab.
      apply (@pequiv_elim_inhabited _ _ (projT2 Z)).
      change (inhabited (idl_mem A (ab_sub (ring_ab R) a b))) in Hab.
      destruct Hab as [Hab].
      constructor.
      exact (rU_cofork_descends (projT1 h) Hh a b Hab).
    + intro x; reflexivity.
    + intros v Hv x; symmetry; exact (Hv x).
Defined.

(** ** Split in Rng itself: exactly when p has a ring-homomorphic section *)

Definition HomRTransversal : Type :=
  { s : QuotientRing A ~{Rng}~> R
  & ∀ a : carrier (rig_setoid R),
      idl_mem A (ab_sub (ring_ab R) (rig_map s a) a) }.

Definition hom_rtransversal_transversal (H : HomRTransversal) : RTransversal :=
  {| rtransversal_map := fmap[Rng_Forget] (`1 H)
   ; rtransversal_coset := `2 H |}.

(* t is a ring homomorphism as soon as s is: by the joint injectivity of
   (∂₀, ∂₁), since ∂₀ t = 1 and ∂₁ t = s p are. *)
Lemma hom_rtransversal_t_ext (H : HomRTransversal)
  (p : carrier (rig_setoid R)) (q : rsdp_carrier A) :
  p ≈ fst q → rig_map (`1 H) p ≈ rsdp_d1 A q →
  @equiv _ (rsdp_setoid A)
    (rtransversal_t (hom_rtransversal_transversal H) p) q.
Proof.
  intros H0 H1; apply rsdp_ext; simpl; [ exact H0 |].
  unfold rsdp_d1; simpl.
  rewrite (ab_add_sub_cancel (ring_ab R) (rig_map (`1 H) p) p).
  exact H1.
Qed.

Definition hom_rtransversal_t (H : HomRTransversal) :
  R ~{Rng}~> SemidirectRing A.
Proof.
  unshelve refine
    (@Build_RigHom R (SemidirectRing A)
       (rtransversal_t (hom_rtransversal_transversal H)) _ _ _ _).
  - apply hom_rtransversal_t_ext; simpl; [ reflexivity |].
    rewrite (rig_map_zero (`1 H)); symmetry; exact (rsdp_d1_zero A).
  - intros a b; apply hom_rtransversal_t_ext; simpl; [ reflexivity |].
    rewrite (rsdp_d1_add A), (rig_map_add (`1 H)).
    unfold rsdp_d1; simpl.
    rewrite !(ab_add_sub_cancel (ring_ab R)); reflexivity.
  - apply hom_rtransversal_t_ext; simpl; [ reflexivity |].
    rewrite (rig_map_one (`1 H)); symmetry; exact (rsdp_d1_one A).
  - intros a b; apply hom_rtransversal_t_ext; simpl; [ reflexivity |].
    rewrite (rsdp_d1_mul A), (rig_map_mul (`1 H)).
    unfold rsdp_d1; simpl.
    rewrite !(ab_add_sub_cancel (ring_ab R)); reflexivity.
Defined.

Definition hom_rtransversal_Rng_split (H : HomRTransversal) :
  SplitCoequalizer rsemidirect_d0 rsemidirect_d1.
Proof.
  unshelve refine
    (@Build_SplitCoequalizer Rng _ _ rsemidirect_d0 rsemidirect_d1
       (QuotientRing A) (rquot_proj A) (`1 H) (hom_rtransversal_t H)
       _ _ _ _).
  - exact rsemidirect_cofork.
  - intro a; simpl.
    constructor; exact (`2 H a).
  - intro r; simpl; reflexivity.
  - intro r; simpl; unfold rsdp_d1; simpl.
    exact (ab_add_sub_cancel (ring_ab R) (rig_map (`1 H) r) r).
Defined.

Definition Rng_split_hom_rtransversal
  (S : SplitCoequalizer rsemidirect_d0 rsemidirect_d1) : HomRTransversal.
Proof.
  pose (T := rsplit_transversal (functor_preserves_split Rng_Forget _ _ S)).
  unshelve eexists.
  - unshelve refine
      (@Build_RigHom (QuotientRing A) R (rtransversal_map T) _ _ _ _); simpl.
    + rewrite (rig_map_zero (scoeq_e S)); apply (rig_map_zero (scoeq_s S)).
    + intros a b.
      rewrite (rig_map_add (scoeq_e S)); apply (rig_map_add (scoeq_s S)).
    + rewrite (rig_map_one (scoeq_e S)); apply (rig_map_one (scoeq_s S)).
    + intros a b.
      rewrite (rig_map_mul (scoeq_e S)); apply (rig_map_mul (scoeq_s S)).
  - exact (rtransversal_coset T).
Defined.

Definition Rng_split_iff_hom_rtransversal :
  SplitCoequalizer rsemidirect_d0 rsemidirect_d1 ↔ HomRTransversal :=
  (Rng_split_hom_rtransversal, hom_rtransversal_Rng_split).

End RngSemidirectPair.

(* Its law 3 holds pointwise by conversion, t being the same map. *)
Example hom_rtransversal_Rng_split_law3@{p u + | u <= p +}
  {R : RingObject@{p p p}} {A : Ideal@{u p p p} R}
  (H : HomRTransversal A) (r : carrier (rig_setoid R)) :
  rig_map (rsemidirect_d0 A)
    (rig_map (scoeq_t (hom_rtransversal_Rng_split A H)) r) = r := eq_refl.

Arguments rtransversal_map {R A} _.
Arguments rtransversal_coset {R A} _ _.

(** ** Witnesses *)

(* A = R: every coset is R, represented by 0. *)
Definition TotalIdeal_transversal (R : RingObject) :
  RTransversal (TotalIdeal R).
Proof.
  unshelve refine
    (@Build_RTransversal R (TotalIdeal R)
       {| morphism := fun _ : carrier (rig_setoid R) => rig_zero R |} _).
  - intros a b _; reflexivity.
  - intro a; exact ttt.
Defined.

(* A trivial: every element represents its own coset, and the identity is
   a ring homomorphism, so the fork splits in Rng itself. *)
Definition TrivialIdeal_transversal (R : RingObject) :
  RTransversal (TrivialIdeal R).
Proof.
  unshelve refine
    (@Build_RTransversal R (TrivialIdeal R)
       {| morphism := fun a : carrier (rig_setoid R) => a |} _).
  - intros a b Hab.
    exact (fst (rquot_trivial_iff R a b) Hab).
  - intro a; exact (ab_sub_self (ring_ab R) a).
Defined.

Definition TrivialIdeal_hom_rtransversal (R : RingObject) :
  HomRTransversal (TrivialIdeal R).
Proof.
  unshelve eexists.
  - unshelve refine
      (@Build_RigHom (QuotientRing (TrivialIdeal R)) R
         (rtransversal_map (TrivialIdeal_transversal R)) _ _ _ _);
      simpl; intros; reflexivity.
  - exact (rtransversal_coset (TrivialIdeal_transversal R)).
Defined.

Definition TrivialIdeal_Rng_split (R : RingObject) :
  SplitCoequalizer (rsemidirect_d0 (TrivialIdeal R))
                   (rsemidirect_d1 (TrivialIdeal R)) :=
  hom_rtransversal_Rng_split (TrivialIdeal R) (TrivialIdeal_hom_rtransversal R).

(* Z/2Z: the remainder mod 2 represents each class. *)
Definition EvenIdeal_transversal : RTransversal EvenIdeal.
Proof.
  unshelve refine
    (@Build_RTransversal Int_Ring EvenIdeal
       {| morphism := fun a : Z => Z.modulo a 2 |} _).
  - intros a b Hab.
    change (inhabited (ZEven (a - b)%Z)) in Hab.
    change (Z.modulo a 2 = Z.modulo b 2).
    destruct Hab as [[k Hk]].
    replace a with (b + k * 2)%Z by lia.
    apply Z_mod_plus_full.
  - intro a.
    exists (- (a / 2))%Z.
    change ((a mod 2 - a)%Z = (2 * - (a / 2))%Z).
    pose proof (Z.div_mod a 2 ltac:(discriminate)) as E.
    lia.
Defined.

(* But no ring homomorphism Z/2Z → Z exists: s(1 + 1) = 1 + 1 = 2 while
   1 + 1 ≡ 0, so the fork at Z ⊇ 2Z does not split in Rng. *)
Theorem EvenIdeal_not_split_in_Rng :
  SplitCoequalizer (rsemidirect_d0 EvenIdeal) (rsemidirect_d1 EvenIdeal)
    → False.
Proof.
  intro S.
  destruct (Rng_split_hom_rtransversal EvenIdeal S) as [s _].
  pose proof (rig_map_one s) as H1.
  pose proof (rig_map_zero s) as H0.
  pose proof (rig_map_add s 1%Z 1%Z) as H11.
  assert (H20 : rig_map s 2%Z ≈ rig_map s 0%Z).
  { apply (proper_morphism (rig_map s)).
    constructor; exists 1%Z; reflexivity. }
  assert (E1 : rig_map s 1%Z = 1%Z) by exact H1.
  assert (E0 : rig_map s 0%Z = 0%Z) by exact H0.
  assert (E11 : rig_map s 2%Z = (rig_map s 1%Z + rig_map s 1%Z)%Z)
    by exact H11.
  assert (E20 : rig_map s 2%Z = rig_map s 0%Z) by exact H20.
  lia.
Qed.

(** ** The constructive taboo, at an ideal of Z *)

(* A_P ◁ Z: all of Z when P holds and zero when it does not, with the
   Prop-valued membership P or a = 0, as the group file's N_P. *)
Definition AP (P : Prop) : Ideal Int_Ring.
Proof.
  unshelve refine
    (@Build_Ideal Int_Ring (fun a : Z => or P (a = 0%Z)) _ _ _ _ _).
  - intros a b Hab Ha; simpl in *; unfold Z_eqT in Hab; subst; exact Ha.
  - right; reflexivity.
  - intros a b Ha Hb; simpl in *.
    destruct Ha as [Ha|Ha]; [ left; exact Ha |].
    destruct Hb as [Hb|Hb]; [ left; exact Hb |].
    right; subst; reflexivity.
  - intros r a Ha; simpl in *.
    destruct Ha as [Ha|Ha]; [ left; exact Ha |].
    right; subst; apply Z.mul_0_r.
  - intros a r Ha; simpl in *.
    destruct Ha as [Ha|Ha]; [ left; exact Ha |].
    right; subst; reflexivity.
Defined.

Lemma AP_untruncates (P : Prop) : RCosetUntruncates (AP P).
Proof. intros a b H; unfold rquot_mem; simpl; destruct H as [H]; exact H. Qed.

(* A transversal of A_P decides P: its values at 0 and 1 agree when P
   holds, and lie in the classes of 0 and 1. *)
Definition AP_rtransversal_decides (P : Prop) (T : RTransversal (AP P)) :
  (P + (P → False))%type.
Proof.
  pose proof (rtransversal_coset T 0%Z) as H0.
  pose proof (rtransversal_coset T 1%Z) as H1.
  assert (Hs : P → rtransversal_map T 0%Z = rtransversal_map T 1%Z).
  { intro p; apply (proper_morphism (rtransversal_map T) 0%Z 1%Z).
    constructor; left; exact p. }
  revert H0 H1 Hs.
  generalize (rtransversal_map T 0%Z) (rtransversal_map T 1%Z).
  intros v0 v1 H0 H1 Hs.
  destruct (Z.eq_dec v0 v1) as [E|E].
  - left.
    destruct H0 as [p|H0]; [ exact p |].
    destruct H1 as [p|H1]; [ exact p |].
    assert (Z0 : (v0 - 0 = 0)%Z) by exact H0.
    assert (Z1 : (v1 - 1 = 0)%Z) by exact H1.
    exfalso; lia.
  - right; intro p; exact (E (Hs p)).
Defined.

(* Exercise 1's "split after the application of the forgetful functors",
   asked of every ideal, decides every proposition. *)
Definition Rng_U_split_taboo :
  (∀ P : Prop, SplitCoequalizer (fmap[Rng_Forget] (rsemidirect_d0 (AP P)))
                                (fmap[Rng_Forget] (rsemidirect_d1 (AP P)))) →
  ∀ P : Prop, (P + (P → False))%type :=
  fun H P => AP_rtransversal_decides P (rsplit_transversal (AP P) (H P)).

(* Untruncation holds at A_P outright, while a transversal decides P. *)
Definition runtruncation_transversal_taboo :
  (∀ P : Prop, RCosetUntruncates (AP P) → RTransversal (AP P)) →
  ∀ P : Prop, (P + (P → False))%type :=
  fun H P => AP_rtransversal_decides P (H P (AP_untruncates P)).

(** ** Readbacks *)

Example rsdp_mul_fst {R : RingObject} (A : Ideal R)
  (p q : carrier (rig_setoid (SemidirectRing A))) :
  fst (rig_mul (SemidirectRing A) p q) = rig_mul R (fst p) (fst q) := eq_refl.

Example rsdp_mul_snd {R : RingObject} (A : Ideal R)
  (p q : carrier (rig_setoid (SemidirectRing A))) :
  `1 (snd (rig_mul (SemidirectRing A) p q))
    = rig_add R (rig_add R (rig_mul R (fst p) (`1 (snd q)))
                           (rig_mul R (`1 (snd p)) (fst q)))
                (rig_mul R (`1 (snd p)) (`1 (snd q))) := eq_refl.

(* The readbacks of the pair bind A's membership level u apart from the
   carrier level p, with the pair's own bound, as the section constants
   do; left to minimization, the bare binders identified the two. *)

Example rsemidirect_d0_fun@{p u + | u <= p +} {R : RingObject@{p p p}}
  (A : Ideal@{u p p p} R) (x : carrier (rig_setoid (SemidirectRing A))) :
  rig_map (rsemidirect_d0 A) x = fst x := eq_refl.

Example rsemidirect_d1_fun@{p u + | u <= p +} {R : RingObject@{p p p}}
  (A : Ideal@{u p p p} R) (x : carrier (rig_setoid (SemidirectRing A))) :
  rig_map (rsemidirect_d1 A) x = rig_add R (fst x) (`1 (snd x)) := eq_refl.

Example rquot_proj_IsCoequalizer_desc@{p u + | u <= p +}
  {R K : RingObject@{p p p}} (A : Ideal@{u p p p} R)
  (h : R ~{Rng}~> K)
  (Hh : h ∘ rsemidirect_d0 A ≈ h ∘ rsemidirect_d1 A) :
  unique_obj (coeq_desc (rquot_proj_IsCoequalizer A) h Hh)
    = rquot_med A (existT _ h (rsemidirect_cofork_kills A h Hh)) := eq_refl.

Example rtransversal_split_e@{p u + | u <= p +} {R : RingObject@{p p p}}
  {A : Ideal@{u p p p} R} (T : RTransversal A) :
  scoeq_e (rtransversal_split A T) = fmap[Rng_Forget] (rquot_proj A)
  := eq_refl.

Example rtransversal_split_s@{p u + | u <= p +} {R : RingObject@{p p p}}
  {A : Ideal@{u p p p} R} (T : RTransversal A) :
  scoeq_s (rtransversal_split A T) = rtransversal_map T := eq_refl.

Example rtransversal_split_t_snd@{p u + | u <= p +} {R : RingObject@{p p p}}
  {A : Ideal@{u p p p} R} (T : RTransversal A) (r : carrier (rig_setoid R)) :
  `1 (snd (scoeq_t (rtransversal_split A T) r))
    = ab_sub (ring_ab R) (rtransversal_map T (rig_map (rquot_proj A) r)) r
  := eq_refl.

(* Law 3 of the splitting, ∂₀ ∘ t = 1, holds pointwise by conversion. *)
Example rtransversal_split_law3@{p u + | u <= p +} {R : RingObject@{p p p}}
  {A : Ideal@{u p p p} R} (T : RTransversal A) (r : carrier (rig_setoid R)) :
  rig_map (rsemidirect_d0 A) (scoeq_t (rtransversal_split A T) r) = r
  := eq_refl.

Example rtransversal_round_trip@{p u + | u <= p +} {R : RingObject@{p p p}}
  {A : Ideal@{u p p p} R} (T : RTransversal A) (a : carrier (rig_setoid R)) :
  rtransversal_map (rsplit_transversal A (rtransversal_split A T)) a
    = rtransversal_map T a := eq_refl.

Example EvenIdeal_transversal_fun (a : Z) :
  rtransversal_map EvenIdeal_transversal a = Z.modulo a 2 := eq_refl.
