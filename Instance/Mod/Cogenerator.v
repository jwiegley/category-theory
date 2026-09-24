(** * Mac Lane V.8 Exercise 2(b): hom_Z(R, ℚ/ℤ) as an injective cogenerator
      of R-Mod, GIVEN that ℚ/ℤ is one of Ab *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed., §V.8 Exercise 2(b), printed p. 131, PDF p. 140 (ledger
              item `maclane:V.8:ex2`, issue #454), read from the printed
              page: "The additive group Q/Z of rational numbers modulo 1
              is known to be an injective cogenerator of Ab.  Use (a) to
              prove that hom_Z(R, Q/Z) is an injective cogenerator of
              R-Mod ("injective" object as defined in § 4)."  The book
              states the fact about Q/Z as known; taking it as a
              HYPOTHESIS is this formalisation's choice, and sections 6–8
              below show why it cannot be discharged in the axiom-free
              core.  (The in-repo catalogue, doc/plan/books/maclane/
              inventory/V.json, paraphrases the sentence as "Given that
              the additive group Q/Z ... is an injective cogenerator of
              Ab, use (a) to prove"; the quotation above is the printed
              page's.)
   Book:      Mac Lane, ibid., §V.8 Theorem 2 — SAFT, whose cogenerator
              hypothesis this file is written to feed (Adjunction/SAFT.v).
   nLab:      https://ncatlab.org/nlab/show/cogenerator
   nLab:      https://ncatlab.org/nlab/show/injective+object
   nLab:      https://ncatlab.org/nlab/show/divisible+group
   nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
              The nLab page "injective cogenerator" does not exist (an
              HTTP 404, measured with curl on 2026-09-24), as the issue
              recorded.

   WHAT IS CONSUMED.  Structure/Projective.v's [Injective] (the notation
   [@Projective (C^op)], whose lift is DATA), [inj_extend],
   [inj_extend_comm] and [cohom_epic_injective]; Adjunction/SAFT.v's
   [Cogenerator] record (the POSITIVE cancellation form [cog_separates])
   and [cogen_prod]; Instance/Mod/Coextension.v's [CoextObj] and
   [coex_adjunction : RMod_Forget_Ab R ⊣ Coextension R]; Exercise 2(a)
   at B := R from Instance/Mod/HomTensor.v ([homzl_ring_adjunction]);
   Instance/Ab/Character.v's [QZ] with its DECIDABLE equality
   [qz_eq_dec]; Instance/Ab/Monoidal.v's [zsmul] family and
   Adjunction/Unitalization.v's [zsmul_mul].

   WHAT IS BUILT.

     1. Transfer along an adjunction F ⊣ U, unconditional:
        [right_adjoint_injective] (if F preserves monos, U preserves
        injectives: transpose, extend along F m, transpose back) and
        [right_adjoint_cogenerator] (if F is faithful, U carries a
        cogenerating family to one, over the SAME index —
        [right_adjoint_cogenerator_obj] at [eq_refl]).  No decision
        procedure is used in either.
     2. [forget_ab_monic] and [forget_ab_faithful] for [RMod_Forget_Ab R].
     3. Exercise 2(b) on the book's premise.  [QZ_family_cogenerates] is
        "the one-member family {ℚ/ℤ} separates arrows of Ab" in
        [Cogenerator]'s positive form, [QZ_Cogenerator] packages it, and
        **[QZ_injective_cogenerator R HI HC]** — the name the issue's
        Verification block prints — takes [HI : Injective Ab QZ] and that
        separation hypothesis and returns [Injective (RMod R) (CoextObj R
        QZ)] together with a [Cogenerator (RMod R)] whose one member is
        [CoextObj R QZ] ([QZ_injective_cogenerator_member] at [eq_refl]).
        [QZ_injective_cogenerator_via_2a] is Mac Lane's own route
        verbatim: the same transfer along Exercise 2(a) at B := R, with
        [HomZL R_R QZ] as the member.  [QZ_injective_cogenerator_ML] is
        the exercise with the book's own DEFINITION of cogenerator
        (§V.7, p. 127: to every h ≠ h' : a → b some g : b → q with
        g h ≠ g h'), [ML_cogenerates], in premise and conclusion alike;
        its transfer [right_adjoint_ML] needs only a faithful left
        adjoint and no decision procedure.  [QZ_cogen_prod] shows the
        conditional cogenerator is ACCEPTED by SAFT's [cogen_prod] at
        [RMod R]'s own completeness witness [RMod_Complete R].
        [RMod_Cogenerator_large] is an UNCONDITIONAL cogenerator (every
        module, tested by the identity), and it is REFUSED by
        [cogen_prod] at [RMod_Complete R], exactly as
        Instance/Sets/Cogenerator.v's [Sets_Cogenerator_large] is at
        [Sets]; with the probe written out, the error ends "(universe
        inconsistency: Cannot enforce <c> = <o> because <c> < <o>)", its
        index universe being the object universe o of [RMod R] where
        [cogen_prod] demands the carrier universe c.
     4. What IS constructive about ℚ/ℤ.  [QZ_divisible] (every element is
        divisible by every positive n), [zchar_determined] (a character
        of ℤ is determined by its value at 1), [zchar], and
        [QZ_extends_along_mul] — Baer's condition AT ℤ: every character
        of nℤ ⊆ ℤ extends to ℤ, the extension computing as k ↦ k · (f(1)/n)
        ([QZ_extends_along_mul_is_zchar] at [eq_refl]).  Together with
        Instance/Ab/Character/Finite.v's axiom-free results for FINITE
        groups — [character_extend_at] (extension across one generator
        from a decidable subgroup) and [tau_injective_finite] (ℚ/ℤ
        separates the points of every finite abelian group) — this is the
        constructive content the tree has.  Baer's criterion itself (from
        ideals to arbitrary subgroups) is Zorn's lemma and is not here.
     5. [Ab_to_ZMod : Ab ⟶ RMod Int_Ring], every abelian group carrying
        ITS OWN ℤ-action [zsmul] ([Ab_to_ZMod_group], [Ab_to_ZMod_smul] and
        [Ab_to_ZMod_fmap] at [eq_refl]).  It exists here because section
        8 needs the gadgets as ℤ-modules.  Seven headers recorded it as
        absent or relied on its absence (Instance/Ab/Free.v,
        Instance/Mod/BaseChange.v, Instance/Mod/Closed.v,
        Instance/Mod/Coextension.v, Instance/Mod/Monoidal.v,
        Instance/Mod/Quotient.v, Instance/Mod/Tensor.v); each carries the
        #454 correction in place.  NOT proved: that every
        ℤ-module's action agrees with [zsmul], hence no equivalence
        [Ab ≃ RMod Int_Ring].
     6.–8. THE METATHEOREMS: THE PREMISES ARE CLASSICAL, NOT FALSE.

        - [QZ_cogenerates_Ab_DNE]: [QZ_family_cogenerates] implies
          ∀ P : Prop, ¬¬P → P.
        - [QZ_injective_WLEM]: [Injective Ab QZ] implies
          ∀ P : Prop, (¬P) + (¬¬P) — INFORMATIVE, because the injective
          lift is data.
        - [cogenerator_stable_DNE] (and [cogenerator_stable_DNE_Z] for
          [RMod Int_Ring]): ANY cogenerating family of Ab whose members'
          equality is stable under double negation implies DNE; every
          family with decidable equality qualifies, ℚ/ℤ among them
          ([qz_stable] from [qz_eq_dec]).
        - [coext_QZ_cogenerates_DNE] and [coext_QZ_injective_WLEM]: the
          CONCLUSION of Exercise 2(b) at R = ℤ carries the same two
          costs.

        The gadgets are [YP P], ℤ/2 with x ≈ y := (x = y ∨ P), and [BP P],
        ℤ/2 × ℤ/2 modulo a subgroup that kills the diagonal when P holds
        and the second axis when ¬P holds; both carry the [PropEquiv] field
        by [PropEquiv_of_relation].  Read these theorems precisely: they
        are closed theorems of the core, and they do NOT refute the
        premises.  They show that the premises are unprovable without
        axioms unless DNE (respectively informative WLEM) is, and both
        principles are independent of the core.  So
        [QZ_injective_cogenerator] is the faithful statement of the
        exercise, and no in-tree term inhabits its hypotheses.  Mac Lane's
        own ≠ form ([ML_cogenerates], "h ≠ h' implies some g with
        g h ≠ g h'") is not the shape [cog_separates] and [cogen_prod]
        consume; the [YP] argument does not apply to it; and no in-tree
        implication relates the two forms (positive to ≠ needs a step
        from ¬∀ to ∃¬, ≠ to positive needs ¬¬-stable hom equality).  Its
        own conditional, [QZ_injective_cogenerator_ML], is delivered, but
        the special adjoint functor theorem cannot consume it.
        Structure/Projective.v's [sets_all_projective_entails_LEM] is the
        tree's precedent for this kind of metatheorem.

   STRENGTHS.  At [eq_refl]: the member of every transferred cogenerator,
   [QZ_extends_along_mul_is_zchar], and the three [Ab_to_ZMod] readbacks.
   Everything else is ≈ in the relevant hom-setoid, or [qz_eq] in ℚ/ℤ.

   UNIVERSES, measured by [About] under [Set Printing Universes].
   [right_adjoint_injective@{co do h …}] and [right_adjoint_cogenerator]
   have C and D sharing the hom universe h, and that is not this file's
   choice: the bare type [F ⊣ U] over [Category@{co hc hc}] and
   [Category@{do hd hd}] with [hc < hd] declared is refused, at its
   argument [F : D ⟶ C], before the record is reached.  The two functors
   already force the equation: Theory/Functor.v's [Functor@{o1 h1 p1 o2
   h2 p2}] carries [h1 <= h2] by its [About], and a definition taking
   only [F : D ⟶ C] and [U : C ⟶ D], with a trivial body, reads back
   [hc = hd]; Theory/Adjunction.v's record, whose [About] carries
   [h1 = h2] as well, repeats it.  Test/ProbeWatts454.v pins the refusal
   as its N5, beside the control [p454_adj_one_hom] over one hom
   universe.  [coext_injective], [coext_cogenerator],
   [QZ_injective_cogenerator], its [_via_2a] form and its [_ML] form are at
   [RingObject@{r r r}] with [QZ : AbObject@{r r r}]: that is [CoextObj]'s
   own identification (its signature is over [RingObject@{u u0 u1}] with
   [u = u0], [u = u1]), coming from [hom_ab] out of [ring_ab R].
   [QZ_injective_cogenerator_ML@{r a +}] reads [ML_cogenerates@{a r a}]
   in premise and conclusion, with no universe equation.
   [QZ_cogen_prod@{r a +}] instantiates the separation hypothesis at
   index universe r, the ring carrier, which is what [cogen_prod] demands
   of an index at [RMod_Complete R].  [RMod_Cogenerator_large] reads
   [Cogenerator@{u u rc} (RMod@{u u0 ra rp rc} R)]: index = object
   universe, the reason [cogen_prod] refuses it.

   NOT DELIVERED.  ℚ/ℤ is NOT proved injective or cogenerating in Ab, and
   by sections 6–8 it cannot be without an axiom; no instance under [IEM],
   [Untruncate] or any other named principle is built either (the
   classical proof extends characters by Baer's criterion, i.e. Zorn).
   No small unconditional cogenerator of [RMod R] or of [Ab]: the class
   of families with double-negation-stable members is ruled out above,
   families with non-stable [Prop]-valued equality are NOT ruled out,
   and none is constructed.  No equivalence [Ab ≃ RMod Int_Ring].  No
   comparison of [Ab_to_ZMod] with Instance/Mod/BaseChange.v's
   [ZExt Int_Ring]. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Projective.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.Character.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.HomTensor.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(** ** 1. Transfer along an adjunction *)

Definition right_adjoint_injective@{co do h +}
  {C : Category@{co h h}} {D : Category@{do h h}} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U)
  (HF : ∀ (x y : D) (m : x ~> y), Monic m → Monic (fmap[F] m))
  (q : C) (Q : @Injective C q) : @Injective D (U q).
Proof.
  apply cohom_epic_injective.
  intros a b m Hm.
  apply (@surjective_implies_epic).
  intro f.
  pose (h := @inj_extend C q Q _ _ (fmap[F] m) (HF _ _ m Hm) (from adj f)).
  exists (to adj h).
  simpl.
  rewrite <- to_adj_nat_l.
  unfold h.
  rewrite (@inj_extend_comm C q Q _ _ (fmap[F] m) (HF _ _ m Hm) (from adj f)).
  exact (iso_to_from (@adj _ _ _ _ A a q) f).
Defined.

Definition right_adjoint_cogenerator@{co do h c +}
  {C : Category@{co h h}} {D : Category@{do h h}} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) (HF : Faithful F) (G : Cogenerator@{c co h} C) :
  Cogenerator@{c do h} D.
Proof.
  refine {| cog_index := cog_index G ;
            cog_obj := fun j => fobj[U] (cog_obj G j) |}.
  intros x y f g H.
  apply (@fmap_inj _ _ F HF).
  apply (cog_separates G).
  intros j k.
  rewrite <- (iso_from_to (@adj _ _ _ _ A y (cog_obj G j)) k).
  simpl.
  rewrite <- !from_adj_nat_l.
  apply from_adj_respects.
  exact (H j _).
Defined.

Example right_adjoint_cogenerator_obj@{co do h c +}
  {C : Category@{co h h}} {D : Category@{do h h}} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (HF : Faithful F) (G : Cogenerator@{c co h} C)
  (j : cog_index G) :
  cog_obj (right_adjoint_cogenerator A HF G) j = fobj[U] (cog_obj G j) :=
  eq_refl.

(** ** 2. The forgetful functor [RMod R ⟶ Ab] *)

Lemma forget_ab_monic@{ra rc rp +} (R : RingObject@{ra rc rp})
  (M N : RModObject R)
  (m : M ~{RMod R}~> N) : Monic m → Monic (fmap[RMod_Forget_Ab R] m).
Proof.
  intro Hm.
  apply ab_injective_monic.
  exact (rmod_monic_injective m Hm).
Qed.

Definition forget_ab_faithful@{ra rc rp +} (R : RingObject@{ra rc rp}) :
  Faithful (RMod_Forget_Ab R).
Proof.
  constructor.
  intros x y f g H a.
  exact (H a).
Defined.

(** ** 3. Mac Lane V.8 Exercise 2(b), on the book's own premise *)

Definition coext_injective@{r +} (R : RingObject@{r r r})
  (A : AbObject@{r r r}) (HA : @Injective Ab A) :
  @Injective (RMod R) (CoextObj R A) :=
  right_adjoint_injective (coex_adjunction R)
    (fun x y m Hm => forget_ab_monic R x y m Hm) A HA.

Definition coext_cogenerator@{r c +} (R : RingObject@{r r r})
  (G : Cogenerator@{c _ r} Ab) : Cogenerator@{c _ r} (RMod R) :=
  right_adjoint_cogenerator (coex_adjunction R) (forget_ab_faithful R) G.

(* The one-member family {Q/Z}, in [Cogenerator]'s positive form. *)
Definition QZ_family_cogenerates@{a h c +} : Type :=
  ∀ (x y : Ab@{a h}) (f g : x ~{Ab@{a h}}~> y),
    (∀ (u : poly_unit@{c}) (k : y ~{Ab@{a h}}~> QZ), k ∘ f ≈ k ∘ g) → f ≈ g.

Definition QZ_Cogenerator@{a h c +} (H : QZ_family_cogenerates@{a h c _ _}) :
  Cogenerator@{c a h} Ab@{a h} :=
  @Build_Cogenerator Ab@{a h} poly_unit@{c} (fun _ => QZ) H.

Definition QZ_injective_cogenerator@{r a c +} (R : RingObject@{r r r})
  (HI : @Injective Ab@{a r} QZ) (HC : QZ_family_cogenerates@{a r c _ _}) :
  (@Injective (RMod R) (CoextObj R QZ)) * Cogenerator@{c _ r} (RMod R) :=
  (coext_injective R QZ HI, coext_cogenerator R (QZ_Cogenerator HC)).

Example QZ_injective_cogenerator_member@{r a c +} (R : RingObject@{r r r})
  (HI : @Injective Ab@{a r} QZ) (HC : QZ_family_cogenerates@{a r c _ _})
  (u : poly_unit@{c}) :
  cog_obj (snd (QZ_injective_cogenerator R HI HC)) u = CoextObj R QZ :=
  eq_refl.

(* Mac Lane's own route: Exercise 2(a) at B := R, read along R ⊗_R A ≅ A. *)
Definition QZ_injective_cogenerator_via_2a@{r a c +} (R : RingObject@{r r r})
  (HI : @Injective Ab@{a r} QZ) (HC : QZ_family_cogenerates@{a r c _ _}) :
  (@Injective (RMod R) (HomZL (Ring_RMod (Ring_op R)) QZ))
    * Cogenerator@{c _ r} (RMod R) :=
  (right_adjoint_injective homzl_ring_adjunction
     (fun x y m Hm => forget_ab_monic R x y m Hm) QZ HI,
   right_adjoint_cogenerator homzl_ring_adjunction (forget_ab_faithful R)
     (QZ_Cogenerator HC)).

Example QZ_injective_cogenerator_via_2a_member@{r a c +}
  (R : RingObject@{r r r}) (HI : @Injective Ab@{a r} QZ)
  (HC : QZ_family_cogenerates@{a r c _ _}) (u : poly_unit@{c}) :
  cog_obj (snd (QZ_injective_cogenerator_via_2a R HI HC)) u
    = HomZL (Ring_RMod (Ring_op R)) QZ := eq_refl.

(* Mac Lane's own definition (§V.7, p. 127): q is a cogenerator when to
   every parallel pair h ≠ h' : a → b there is g : b → q with
   g h ≠ g h'.  "There is" is read as data, a Σ. *)
Definition ML_cogenerates@{o h +} {C : Category@{o h h}} (q : C) : Type :=
  ∀ (x y : C) (f g : x ~> y), (f ≈ g → False) →
    { k : y ~> q & (k ∘ f ≈ k ∘ g → False) }.

(* The ≠ form transfers along an adjunction with a faithful left adjoint:
   F keeps the pair apart, the given cogenerator separates their images,
   and transposing keeps them apart.  No decision procedure is used. *)
Definition right_adjoint_ML@{co do h +}
  {C : Category@{co h h}} {D : Category@{do h h}} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) (HF : Faithful F) (q : C) (H : ML_cogenerates q) :
  ML_cogenerates (fobj[U] q).
Proof.
  intros x y f g Hne.
  destruct (H _ _ (fmap[F] f) (fmap[F] g)
              (fun E => Hne (@fmap_inj _ _ F HF _ _ f g E))) as [k Hk].
  exists (to adj k).
  intro E. apply Hk.
  rewrite <- (iso_from_to (@adj _ _ _ _ A y q) k).
  simpl. rewrite <- !from_adj_nat_l.
  apply from_adj_respects. exact E.
Defined.

(* Exercise 2(b) with the book's own definition of cogenerator in both
   premise and conclusion. *)
Definition QZ_injective_cogenerator_ML@{r a +} (R : RingObject@{r r r})
  (HI : @Injective Ab@{a r} QZ) (HC : @ML_cogenerates Ab@{a r} QZ) :
  (@Injective (RMod R) (CoextObj R QZ))
    * @ML_cogenerates (RMod R) (CoextObj R QZ) :=
  (coext_injective R QZ HI,
   right_adjoint_ML (coex_adjunction R) (forget_ab_faithful R) QZ HC).

(* The conditional cogenerator is consumed by SAFT's product construction
   at [RMod R]'s own completeness witness. *)
Definition QZ_cogen_prod@{r a +} (R : RingObject@{r r r})
  (HC : QZ_family_cogenerates@{a r r _ _}) : RMod R :=
  cogen_prod (RMod_Complete R) (coext_cogenerator R (QZ_Cogenerator HC)).

(* The large cogenerator: every module, tested by the identity. *)
Definition RMod_Cogenerator_large@{ra rc rp +} (R : RingObject@{ra rc rp}) :
  Cogenerator (RMod R).
Proof.
  refine (@Build_Cogenerator (RMod R) (RModObject R) (fun M => M) _).
  intros x y f g H.
  pose proof (H y id) as Hid.
  intro a. exact (Hid a).
Defined.

(** ** 4. What is constructive about ℚ/ℤ *)

Notation Zab := (ring_ab Int_Ring).

Definition QZ_divisible@{q +} (q : Q) (n : positive) :
  { r : Q & qz_eq (inject_Z (Zpos n) * r) q }.
Proof.
  exists (q / inject_Z (Zpos n)).
  apply qz_of_Qeq. field. unfold Qeq; simpl; lia.
Defined.

Lemma qz_sum_cong@{q +} (x x' y y' : Q) :
  qz_eq x x' -> qz_eq y y' -> qz_eq (x + y) (x' + y').
Proof. intros H1 H2; exact (cmon_plus_respects QZ x x' H1 y y' H2). Qed.

Lemma q_add_mul (a b : Z) (c : Q) :
  inject_Z (a + b) * c == inject_Z a * c + inject_Z b * c.
Proof. rewrite inject_Z_plus; ring. Qed.

Lemma q_one_mul (c : Q) : c == 1 * c.
Proof. ring. Qed.

Lemma q_zero_mul (c : Q) : 0 == inject_Z 0 * c.
Proof. ring. Qed.

Lemma q_succ_mul (p : positive) (c : Q) :
  inject_Z (Zpos p) * c + c == inject_Z (Zpos p + 1) * c.
Proof. rewrite inject_Z_plus. ring. Qed.

Lemma q_neg_mul (p : positive) (c : Q) :
  - (inject_Z (Zpos p) * c) == inject_Z (Zneg p) * c.
Proof. rewrite <- (Pos2Z.opp_pos p), inject_Z_opp. ring. Qed.

Lemma zchar_pos@{a h +} (f : Zab ~{Ab@{a h}}~> QZ) (p : positive) :
  qz_eq (cmon_map f (Zpos p)) (inject_Z (Zpos p) * cmon_map f 1%Z).
Proof.
  induction p using Pos.peano_rect.
  - apply qz_of_Qeq. exact (q_one_mul (cmon_map f 1%Z)).
  - replace (Zpos (Pos.succ p)) with (Z.add (Zpos p) 1%Z) by lia.
    eapply qz_eq_trans; [exact (cmon_map_plus f (Zpos p) 1%Z)|].
    eapply qz_eq_trans.
    + apply qz_sum_cong; [exact IHp | apply qz_eq_refl].
    + apply qz_of_Qeq. exact (q_succ_mul p (cmon_map f 1%Z)).
Qed.

Lemma zchar_determined@{a h +} (f : Zab ~{Ab@{a h}}~> QZ) (k : Z) :
  qz_eq (cmon_map f k) (inject_Z k * cmon_map f 1%Z).
Proof.
  destruct k as [|p|p].
  - eapply qz_eq_trans; [exact (cmon_map_zero f)|].
    apply qz_of_Qeq. exact (q_zero_mul (cmon_map f 1%Z)).
  - exact (zchar_pos f p).
  - pose proof (ab_map_neg f (Zpos p)) as Hn. simpl in Hn.
    eapply qz_eq_trans; [exact Hn|].
    eapply qz_eq_trans; [exact (ab_neg_respects QZ _ _ (zchar_pos f p))|].
    apply qz_of_Qeq. exact (q_neg_mul p (cmon_map f 1%Z)).
Qed.

Lemma q_baer_step (n : positive) (k : Z) (r c : Q) (z : Z) :
  inject_Z (Zpos n) * r - c == inject_Z z ->
  inject_Z (Zpos n * k) * r - inject_Z k * c == inject_Z (k * z).
Proof.
  intro Hz. rewrite !inject_Z_mult.
  setoid_replace (inject_Z (Zpos n) * inject_Z k * r - inject_Z k * c)
    with (inject_Z k * (inject_Z (Zpos n) * r - c)) by ring.
  rewrite Hz. ring.
Qed.

#[local] Obligation Tactic := idtac.

Program Definition zchar@{a h +} (c : Q) : Zab ~{Ab@{a h}}~> QZ := {|
  cmon_map := {| morphism := fun k : Z => inject_Z k * c |}
|}.
Next Obligation. intros c k k' Hk; destruct Hk; apply qz_eq_refl. Qed.
Next Obligation. intros c; apply qz_of_Qeq; exact (q_zero_mul c). Qed.
Next Obligation. intros c a b; apply qz_of_Qeq; exact (q_add_mul a b c). Qed.

Definition QZ_extends_along_mul@{a h +} (n : positive)
  (f : Zab ~{Ab@{a h}}~> QZ) :
  { g : Zab ~{Ab@{a h}}~> QZ &
      ∀ k : Z, qz_eq (cmon_map g (Z.mul (Zpos n) k)) (cmon_map f k) }.
Proof.
  exists (zchar@{a h _} (projT1 (QZ_divisible (cmon_map f 1%Z) n))).
  intro k.
  destruct (QZ_divisible (cmon_map f 1%Z) n) as [r Hr]; simpl.
  eapply qz_eq_trans; [|exact (qz_eq_sym _ _ (zchar_determined f k))].
  destruct Hr as [z Hz].
  exists (Z.mul k z).
  exact (q_baer_step n k r (cmon_map f 1%Z) z Hz).
Defined.

(* The extension computes: it is k ↦ k · (f(1) / n). *)
Example QZ_extends_along_mul_is_zchar@{a h +} (n : positive)
  (f : Zab ~{Ab@{a h}}~> QZ) :
  projT1 (QZ_extends_along_mul n f)
    = zchar (cmon_map f 1%Z / inject_Z (Zpos n)) := eq_refl.

(** ** 5. Every abelian group is a ℤ-module *)

Definition AbZMod@{h +} (A : AbObject@{h h h}) : RModObject Int_Ring.
Proof.
  refine (@Build_RModObject Int_Ring A (zsmul A) _ _ _ _ _).
  - intros n n' Hn a a' Ha. destruct Hn.
    exact (zsmul_respects A n a a' Ha).
  - intros n a b; exact (zsmul_plus A n a b).
  - intros n m a; exact (zsmul_add A n m a).
  - intros n m a; exact (zsmul_mul A n m a).
  - intros a; exact (zsmul_one A a).
Defined.

Program Definition AbZModMap@{a h +} {A B : AbObject@{h h h}}
  (f : A ~{Ab@{a h}}~> B) :
  AbZMod A ~{RMod Int_Ring}~> AbZMod B := {| rm_hom := f |}.
Next Obligation. intros A B f n a; exact (zsmul_hom f n a). Qed.

Program Definition Ab_to_ZMod@{a h +} : Ab@{a h} ⟶ RMod Int_Ring := {|
  fobj := AbZMod;
  fmap := @AbZModMap
|}.
Next Obligation. intros A B f g H; exact H. Qed.
Next Obligation. intros A a; reflexivity. Qed.
Next Obligation. intros A B C f g a; reflexivity. Qed.

Example Ab_to_ZMod_group@{h +} (A : AbObject@{h h h}) :
  rm_ab (fobj[Ab_to_ZMod] A) = A := eq_refl.

Example Ab_to_ZMod_smul@{h +} (A : AbObject@{h h h}) :
  rm_smul (fobj[Ab_to_ZMod] A) = zsmul A := eq_refl.

Example Ab_to_ZMod_fmap@{a h +} {A B : AbObject@{h h h}}
  (f : A ~{Ab@{a h}}~> B) :
  rm_hom (fmap[Ab_to_ZMod] f) = f := eq_refl.

(** ** 6. The premises are classical: two gadgets *)

Section YP.

Context (P : Prop).

Definition yp_eq (x y : bool) : Prop := x = y \/ P.

Lemma yp_equiv@{s0 s1 +} : Equivalence@{s0 s1} yp_eq.
Proof.
  constructor.
  - intro x; left; reflexivity.
  - intros x y [H|H]; [left; symmetry; exact H | right; exact H].
  - intros x y z [H1|H1] [H2|H2];
      [left; congruence | right; exact H2 | right; exact H1 | right; exact H1].
Qed.

Definition yp_setoid@{s0 s1 +} : Setoid@{s0 s1} bool :=
  {| equiv := yp_eq; setoid_equiv := yp_equiv |}.

Definition yp_prop@{s0 s1 +} : PropEquiv yp_setoid@{s0 s1} :=
  @PropEquiv_of_relation _ yp_setoid yp_eq (fun _ _ h => h) (fun _ _ h => h).

Lemma yp_plus_respects_prop (x x' y y' : bool) :
  yp_eq x x' -> yp_eq y y' -> yp_eq (xorb x y) (xorb x' y').
Proof.
  intros [H1|H1] [H2|H2]; subst;
    [left; reflexivity | right; exact H2 | right; exact H1 | right; exact H1].
Qed.

Lemma yp_plus_respects@{s0 s1 +} :
  Proper (@equiv _ yp_setoid@{s0 s1} ==> @equiv _ yp_setoid@{s0 s1}
            ==> @equiv _ yp_setoid@{s0 s1}) xorb.
Proof.
  intros x x' H1 y y' H2; exact (yp_plus_respects_prop x x' y y' H1 H2).
Qed.

Definition YP@{g0 g1 g2 +} : AbObject@{g0 g1 g2} := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := bool; is_setoid := yp_setoid |};
    cmon_zero := false;
    cmon_plus := xorb;
    cmon_plus_respects := yp_plus_respects;
    cmon_plus_assoc := fun a b c => or_introl (Bool.xorb_assoc_reverse a b c);
    cmon_plus_comm := fun a b => or_introl (Bool.xorb_comm a b);
    cmon_plus_zero_l := fun a => or_introl (Bool.xorb_false_l a);
    cmon_prop := yp_prop
  |};
  ab_neg := fun b => b;
  ab_neg_respects := fun _ _ h => h;
  ab_neg_left := fun a => or_introl (Bool.xorb_nilpotent a)
|}.

Program Definition yp_zero@{a h +} : YP ~{Ab@{a h}}~> YP := {|
  cmon_map := {| morphism := fun _ => false |}
|}.
Next Obligation. intros; left; reflexivity. Qed.
Next Obligation. left; reflexivity. Qed.
Next Obligation. intros; left; reflexivity. Qed.

Lemma yp_true_false_prop : yp_eq true false -> P.
Proof. intros [H|H]; [discriminate | exact H]. Qed.

Lemma yp_true_false@{s0 s1 +} : @equiv _ yp_setoid@{s0 s1} true false -> P.
Proof. intro H; exact (yp_true_false_prop H). Qed.

End YP.

Section BP.

Context (P : Prop).

Definition bp_xor (x y : bool * bool) : bool * bool :=
  (xorb (fst x) (fst y), xorb (snd x) (snd y)).

Definition bp_kill (v : bool * bool) : Prop :=
  v = (false, false) \/ (P /\ v = (true, true)) \/ (~ P /\ v = (false, true)).

Lemma bp_kill_xor (v w : bool * bool) :
  bp_kill v -> bp_kill w -> bp_kill (bp_xor v w).
Proof.
  unfold bp_kill, bp_xor.
  intros [H1|[[p1 H1]|[p1 H1]]] [H2|[[p2 H2]|[p2 H2]]]; subst; simpl;
    first [ left; reflexivity
          | right; left; split; [assumption|reflexivity]
          | right; right; split; [assumption|reflexivity]
          | exfalso; auto ].
Qed.

Definition bp_eq (x y : bool * bool) : Prop := bp_kill (bp_xor x y).

Lemma bp_xor_self (x : bool * bool) : bp_xor x x = (false, false).
Proof. destruct x as [[|] [|]]; reflexivity. Qed.

Lemma bp_xor_comm (x y : bool * bool) : bp_xor x y = bp_xor y x.
Proof. destruct x as [[|] [|]], y as [[|] [|]]; reflexivity. Qed.

Lemma bp_xor_trans (x y z : bool * bool) :
  bp_xor x z = bp_xor (bp_xor x y) (bp_xor y z).
Proof.
  destruct x as [[|] [|]], y as [[|] [|]], z as [[|] [|]]; reflexivity.
Qed.

Lemma bp_equiv@{s0 s1 +} : Equivalence@{s0 s1} bp_eq.
Proof.
  constructor.
  - intro x; unfold bp_eq; rewrite bp_xor_self; left; reflexivity.
  - intros x y H; unfold bp_eq in *; rewrite bp_xor_comm; exact H.
  - intros x y z H1 H2; unfold bp_eq in *; rewrite (bp_xor_trans x y z).
    exact (bp_kill_xor _ _ H1 H2).
Qed.

Definition bp_setoid@{s0 s1 +} : Setoid@{s0 s1} (bool * bool) :=
  {| equiv := bp_eq; setoid_equiv := bp_equiv |}.

Definition bp_prop@{s0 s1 +} : PropEquiv bp_setoid@{s0 s1} :=
  @PropEquiv_of_relation _ bp_setoid bp_eq (fun _ _ h => h) (fun _ _ h => h).

Lemma bp_plus_respects_prop (x x' y y' : bool * bool) :
  bp_eq x x' -> bp_eq y y' -> bp_eq (bp_xor x y) (bp_xor x' y').
Proof.
  intros H1 H2; unfold bp_eq in *.
  replace (bp_xor (bp_xor x y) (bp_xor x' y'))
    with (bp_xor (bp_xor x x') (bp_xor y y')).
  - exact (bp_kill_xor _ _ H1 H2).
  - destruct x as [[|] [|]], y as [[|] [|]], x' as [[|] [|]], y' as [[|] [|]];
      reflexivity.
Qed.

Lemma bp_eq_of_eq (x y : bool * bool) : x = y -> bp_eq x y.
Proof. intro H; subst; unfold bp_eq; rewrite bp_xor_self; left; reflexivity. Qed.

Lemma bp_xor_assoc (a b c : bool * bool) :
  bp_xor (bp_xor a b) c = bp_xor a (bp_xor b c).
Proof.
  destruct a as [[|] [|]], b as [[|] [|]], c as [[|] [|]]; reflexivity.
Qed.

Lemma bp_xor_zero_l (a : bool * bool) : bp_xor (false, false) a = a.
Proof. destruct a as [[|] [|]]; reflexivity. Qed.

Definition BP@{g0 g1 g2 +} : AbObject@{g0 g1 g2} := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := bool * bool; is_setoid := bp_setoid |};
    cmon_zero := (false, false);
    cmon_plus := bp_xor;
    cmon_plus_respects :=
      fun x x' H1 y y' H2 => bp_plus_respects_prop x x' y y' H1 H2;
    cmon_plus_assoc := fun a b c => bp_eq_of_eq _ _ (bp_xor_assoc a b c);
    cmon_plus_comm := fun a b => bp_eq_of_eq _ _ (bp_xor_comm a b);
    cmon_plus_zero_l := fun a => bp_eq_of_eq _ _ (bp_xor_zero_l a);
    cmon_prop := bp_prop
  |};
  ab_neg := fun b => b;
  ab_neg_respects := fun _ _ h => h;
  ab_neg_left := fun a => bp_eq_of_eq _ _ (bp_xor_self a)
|}.

Lemma bp_incl_respects_prop (x y : bool) :
  yp_eq False x y -> bp_eq (x, false) (y, false).
Proof. intros [H|[]]; subst; apply bp_eq_of_eq; reflexivity. Qed.

Program Definition bp_incl@{a h +} : YP False ~{Ab@{a h}}~> BP := {|
  cmon_map := {| morphism := fun b => (b, false) |}
|}.
Next Obligation. intros x y H; exact (bp_incl_respects_prop x y H). Qed.
Next Obligation. exact (bp_eq_of_eq _ _ eq_refl). Qed.
Next Obligation. intros; exact (bp_eq_of_eq _ _ eq_refl). Qed.

Lemma bp_incl_injective_prop (x y : bool) :
  bp_eq (x, false) (y, false) -> x = y.
Proof.
  unfold bp_eq, bp_kill, bp_xor; simpl.
  destruct x, y; simpl; intros [H|[[_ H]|[_ H]]]; try discriminate; reflexivity.
Qed.

Lemma bp_incl_monic@{a h +} : Monic bp_incl@{a h}.
Proof.
  apply ab_injective_monic.
  intros x y H; left; exact (bp_incl_injective_prop x y H).
Qed.

End BP.

Definition qz_half : Q := 1 # 2.

Lemma qz_half_nonzero@{q +} : qz_eq@{q} qz_half 0 -> False.
Proof.
  intros [z Hz]. unfold Qeq, qz_half in Hz; simpl in Hz. lia.
Qed.

Lemma z2_eq_bool (x y : bool) : (x = y \/ False) -> x = y.
Proof. intros [H|[]]; exact H. Qed.

Program Definition z2_half@{a h +} : YP False ~{Ab@{a h}}~> QZ := {|
  cmon_map := {| morphism := fun b : bool => if b then qz_half else 0 |}
|}.
Next Obligation.
  intros x y H.
  pose proof (z2_eq_bool x y H) as E; subst; apply qz_eq_refl.
Qed.
Next Obligation. apply qz_eq_refl. Qed.
Next Obligation.
  intros a b; destruct a, b; simpl.
  - exists (-1)%Z; reflexivity.
  - apply qz_of_Qeq; reflexivity.
  - apply qz_of_Qeq; reflexivity.
  - apply qz_of_Qeq; reflexivity.
Qed.

(** ** 7. The metatheorems in Ab *)

Theorem cogenerator_stable_DNE@{c a h +} (G : Cogenerator@{c a h} Ab@{a h})
  (stable : ∀ j (a b : carrier (cmon_setoid (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P -> P.
Proof.
  intros P nnP.
  apply (yp_true_false P).
  pose proof (cog_separates G (x:=YP P) (y:=YP P) id (yp_zero P)) as Hsep.
  refine (Hsep _ true).
  intros j k b.
  apply stable; intro Hne.
  apply nnP; intro HP.
  apply Hne.
  simpl.
  transitivity (cmon_map k false).
  - apply (proper_morphism (cmon_map k)). right; exact HP.
  - reflexivity.
Qed.

Lemma qz_stable@{q +} (a b : Q) :
  ((qz_eq@{q} a b → False) → False) → qz_eq@{q} a b.
Proof.
  intro H.
  destruct (qz_eq_dec a b) as [Hd|Hd]; [exact Hd | exfalso; exact (H Hd)].
Qed.

Theorem QZ_cogenerates_Ab_DNE@{a h c +}
  (HC : QZ_family_cogenerates@{a h c _ _}) :
  ∀ P : Prop, ~~P -> P.
Proof.
  apply (cogenerator_stable_DNE (QZ_Cogenerator HC)).
  intros j a b; exact (qz_stable a b).
Qed.

Theorem QZ_injective_WLEM@{a h +} (HI : @Injective Ab@{a h} QZ) :
  ∀ P : Prop, (~ P) + (~~ P).
Proof.
  intro P.
  pose (g := @inj_extend Ab QZ HI _ _ (bp_incl P) (bp_incl_monic P) z2_half).
  pose proof (@inj_extend_comm Ab QZ HI _ _ (bp_incl P) (bp_incl_monic P)
                z2_half) as Hg.
  destruct (qz_eq_dec (cmon_map g (false, true)) 0) as [H0|H0].
  - left; intro HP.
    apply qz_half_nonzero.
    assert (E : @equiv _ (bp_setoid P) (false, true) (true, false)).
    { right; left; split; [exact HP | reflexivity]. }
    pose proof (proper_morphism (cmon_map g) _ _ E) as Hgt.
    pose proof (Hg true) as Hgt'. simpl in Hgt'.
    apply (qz_eq_trans _ _ _ (qz_eq_sym _ _ Hgt')).
    apply (qz_eq_trans _ _ _ (qz_eq_sym _ _ Hgt)).
    exact H0.
  - right; intro HnP.
    apply H0.
    assert (E : @equiv _ (bp_setoid P) (false, true) (false, false)).
    { right; right; split; [exact HnP | reflexivity]. }
    apply (qz_eq_trans _ _ _ (proper_morphism (cmon_map g) _ _ E)).
    exact (cmon_map_zero g).
Qed.

(** ** 8. The metatheorems at R = ℤ *)

Definition YPZ@{a h +} (P : Prop) : RModObject Int_Ring :=
  fobj[Ab_to_ZMod@{a h _ _ _ _}] (YP P).

Definition BPZ@{a h +} (P : Prop) : RModObject Int_Ring :=
  fobj[Ab_to_ZMod@{a h _ _ _ _}] (BP P).

Definition ypz_zero@{a h +} (P : Prop) :
  YPZ@{a h _ _ _ _} P ~{RMod Int_Ring}~> YPZ@{a h _ _ _ _} P :=
  fmap[Ab_to_ZMod@{a h _ _ _ _}] (yp_zero P).

Definition bpz_incl@{a h +} (P : Prop) :
  YPZ@{a h _ _ _ _} False ~{RMod Int_Ring}~> BPZ@{a h _ _ _ _} P :=
  fmap[Ab_to_ZMod@{a h _ _ _ _}] (bp_incl P).

Lemma bpz_incl_monic@{a h +} (P : Prop) : Monic (bpz_incl@{a h _ _ _ _} P).
Proof.
  apply rmod_injective_monic.
  intros x y H; left; exact (bp_incl_injective_prop P x y H).
Qed.

Theorem cogenerator_stable_DNE_Z@{c m h +}
  (G : Cogenerator@{c m h} (RMod Int_Ring))
  (stable : ∀ j (a b : carrier (cmon_setoid (rm_ab (cog_obj G j)))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P -> P.
Proof.
  intros P nnP.
  apply (yp_true_false P).
  pose proof (cog_separates G (x:=YPZ P) (y:=YPZ P) id (ypz_zero P)) as Hsep.
  refine (Hsep _ true).
  intros j k b.
  apply stable; intro Hne.
  apply nnP; intro HP.
  apply Hne.
  simpl.
  apply (proper_morphism (cmon_map (rm_hom k))). right; exact HP.
Qed.

Lemma coext_QZ_stable@{r +}
  (a b : carrier (cmon_setoid (rm_ab (CoextObj Int_Ring@{r r r} QZ)))) :
  ((a ≈ b → False) → False) → a ≈ b.
Proof.
  intros H s.
  destruct (qz_eq_dec (cmon_map a s) (cmon_map b s)) as [Hd|Hd]; [exact Hd|].
  exfalso; apply H; intro Hab; exact (Hd (Hab s)).
Qed.

Theorem coext_QZ_cogenerates_DNE@{r c +}
  (HC : ∀ (x y : RMod Int_Ring@{r r r}) (f g : x ~{RMod Int_Ring}~> y),
          (∀ (u : poly_unit@{c})
             (k : y ~{RMod Int_Ring}~> CoextObj Int_Ring@{r r r} QZ),
             k ∘ f ≈ k ∘ g) → f ≈ g) :
  ∀ P : Prop, ~~P -> P.
Proof.
  apply (cogenerator_stable_DNE_Z
           (@Build_Cogenerator (RMod Int_Ring) poly_unit
              (fun _ => CoextObj Int_Ring QZ) HC)).
  intros j a b; exact (coext_QZ_stable a b).
Qed.

Definition z2_half_Z@{r +} :
  YPZ False ~{RMod Int_Ring}~> CoextObj Int_Ring@{r r r} QZ :=
  coex_to Int_Ring (M:=YPZ False) z2_half.

Theorem coext_QZ_injective_WLEM@{r +}
  (HI : @Injective (RMod Int_Ring) (CoextObj Int_Ring@{r r r} QZ)) :
  ∀ P : Prop, (~ P) + (~~ P).
Proof.
  intro P.
  pose (h := @inj_extend (RMod Int_Ring) _ HI _ _ (bpz_incl P)
               (bpz_incl_monic P) z2_half_Z).
  pose proof (@inj_extend_comm (RMod Int_Ring) _ HI _ _ (bpz_incl P)
                (bpz_incl_monic P) z2_half_Z) as Hh.
  destruct (qz_eq_dec (cmon_map (cmon_map (rm_hom h) (false, true)) 1%Z) 0)
    as [H0|H0].
  - left; intro HP.
    apply qz_half_nonzero.
    assert (E : @equiv _ (bp_setoid P) (false, true) (true, false)).
    { right; left; split; [exact HP | reflexivity]. }
    pose proof (proper_morphism (cmon_map (rm_hom h)) _ _ E 1%Z) as Ht.
    pose proof (Hh true 1%Z) as Ht'. simpl in Ht'.
    apply (qz_eq_trans _ _ _ (qz_eq_sym _ _ Ht')).
    apply (qz_eq_trans _ _ _ (qz_eq_sym _ _ Ht)).
    exact H0.
  - right; intro HnP.
    apply H0.
    assert (E : @equiv _ (bp_setoid P) (false, true) (false, false)).
    { right; right; split; [exact HnP | reflexivity]. }
    apply (qz_eq_trans _ _ _ (proper_morphism (cmon_map (rm_hom h)) _ _ E 1%Z)).
    exact (cmon_map_zero (rm_hom h) 1%Z).
Qed.
