Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Rng.
Require Import Category.Instance.FdVect.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Generalizable All Variables.

(** * Field: the category of fields, and the determination of its monos

    Riehl, "Category Theory in Context", §1.2 Exercise 1.2.iii (printed
    p. 15): "show that every morphism in the category of fields is a
    monomorphism" [riehl:1.2:exiii], and §1.6 Example 1.6.15 (printed
    p. 38), the field half: the category of fields has NEITHER an
    initial NOR a terminal object [riehl:1.6:example15].  These are the
    one entry of the standard roster (Mac Lane §I.7, Awodey §1.4, Riehl
    1.1.3) that asks for mathematics rather than bookkeeping: the roster
    entries around it — Grp, Ab, Rng, RMod, Top — are constructions,
    whereas these are theorems about the category once built.
    nLab: https://ncatlab.org/nlab/show/field
    Wikipedia: https://en.wikipedia.org/wiki/Field_(mathematics)

    OBJECTS AND MORPHISMS.  [FieldObject] is Instance/FdVect.v's record —
    a [RingObject] with commutative multiplication, a separated unit
    (1 ≉ 0), and a TOTAL inverse operation [finv] whose defining law
    [finv_l] is asserted only away from zero.  Totality is forced by the
    setoid discipline (a partial operation is not a setoid map), so
    [finv (rig_zero F)] is a junk value, constrained by nothing except
    [finv_respects]; every statement below that mentions [finv] carries
    the nonzeroness hypothesis that makes it meaningful.

    Morphisms are the ring homomorphisms of Instance/Rng.v, i.e. the
    [RigHom]s of Theory/Algebra/Rig.v, which preserve 0, +, 1 and ·.  No
    further preservation is demanded, and none may be: preservation of
    negation is Rig.v's theorem [RigHom_neg], and preservation of
    inverses is the theorem [field_hom_finv] below, holding at every
    nonzero argument by uniqueness of two-sided inverses.  At zero it is
    NOT claimed — both sides are junk values of two unrelated [finv]s,
    and nothing relates them.

    THE DETERMINATION, and its exact constructive strength.  The
    classical argument is short: a homomorphism of fields carrying
    a and b to a common value carries a − b to 0; were a − b nonzero it
    would be invertible, and its image would be an invertible zero,
    forcing 1 ≈ 0 in the target.  That argument is available here
    verbatim and is [field_hom_distinct], stated in the form the
    argument actually produces:

        a ≉ b  →  f a ≉ f b

    — distinct elements have distinct images, unconditionally and
    axiom-free.  What the argument does NOT produce is the strict
    cancellation form [f a ≈ f b → a ≈ b].  Running it under the
    hypothesis [f a ≈ f b] yields ¬¬(a ≈ b), and no field axiom carries
    that back to a ≈ b: the record supplies [finv] together with a law
    holding away from zero, not a decision between "zero" and
    "invertible".  This is exactly the shape of Instance/Grp/Epi.v,
    where surjectivity of a group epimorphism is delivered as the
    unconditional density theorem [grp_epic_image_dense] and the
    classical biconditional is its double-negation elimination; the
    same discipline is followed here, and for the same reason.

    So the hypothesis is named rather than smuggled: [FieldStable F]
    says that ≈ on F is ¬¬-stable.  It is discharged by decidable
    equality ([field_dec_stable]), hence holds for both fields in the
    tree ([Q_Field_stable], [F2_Field_stable]).  Two results say where
    it sits.  [stability_is_the_conclusion] shows that under the
    premise [f a ≈ f b] the hypothesis INSTANCE at (a, b) and the
    conclusion a ≈ b inter-derive — a single-instance statement, not
    the quantified biconditional Instance/Grp/Epi.v proves, and it is
    labelled as such where it is stated.  [FieldStableAtZero], with
    [field_stable_at_zero_suffices] and the two inter-derivability
    lemmas, locates the obstruction: stability is ever used only at
    zero, which is precisely the guard on [finv_l], and the zero-only
    form is equivalent to the pairwise one.  With either,
    [field_monic] gives Riehl's conclusion per morphism and
    [field_every_monic] gives it in the blanket form the exercise
    states.  No countermodel is offered: whether some field has
    unstable equality is left open, not asserted either way.

    NO INITIAL AND NO TERMINAL OBJECT.  Riehl's Example 1.6.15 is
    delivered as [Field_no_initial] and [Field_no_terminal], with the
    object-level readings [Field_no_initial_obj] and
    [Field_no_terminal_obj] — no object of [Field] is initial, and none
    is terminal — obtained through Structure/Terminal.v's
    [IsTerminalObj]/[IsInitialObj] bundling.  The separating pair is ℚ
    against [F2_Field], the two-element field built here on [bool]:
    characteristic 0 against characteristic 2.  Both proofs are
    CONSTRUCTIVE and consult no decision procedure — the guard on
    [finv_l] is a negation, so the negative fact "1 + 1 is not zero
    here" is itself the licence to invert, and neither [FieldStable]
    nor decidability appears in either proof.  The same pair also gives
    [no_hom_Q_F2] and [no_hom_F2_Q]: there is no homomorphism in either
    direction, so [Field] is not even connected.

    THE CONVERSE IS NOT CLAIMED.  "Monic ⟺ injective" would need the
    monic ⇒ injective direction, and that needs a probe object — the
    free field on one generator, which does not exist in this tree.  The
    analogous probes elsewhere show what is missing rather than that the
    pattern is unavailable: Instance/Sets.v probes with the singleton,
    and Instance/Rng.v's own monic ⇒ injective — deferred there when this
    was written, pending the polynomial ring ℤ[x] — is now proved, as
    [rng_monic_injective] in Instance/Rng/Polynomial.v, using exactly
    that probe.  No such object is available for fields.  Riehl's
    exercise concludes that every morphism is monic, and that is what is
    delivered.

    WITNESSES.  ℚ is an object ([Q_Field], from FdVect.v) and F₂ is a
    second one, built here; the identity is a morphism; every
    homomorphism out of either is monic with no hypothesis at all
    ([Q_hom_monic], [F2_hom_monic]); and ℚ is rigid — its only ring
    endomorphism is the identity ([Q_endo_id]), by initiality of ℤ
    followed by cancellation of the denominator.

    AXIOMS.  Everything here is axiom-free, counted the way
    docs/AXIOMS.md counts: all 76 constants the module declares — the
    50 source-level definitions and theorems, the 2 [Faithful]
    instances, and the 24 [Program] obligations, which no [.glob] sweep
    sees — report "Closed under the global context".  The arithmetic is
    Theory/Algebra/Rig.v's, the concrete carriers are [bool] and stdlib
    [QArith], and neither needs an axiom.  In particular nothing in
    this file touches the reals. *)

#[local] Obligation Tactic := idtac.

(** ** The category *)

(* Objects are fields, morphisms are ring homomorphisms of the
   underlying rings, and the hom-setoid is Rig.v's — pointwise
   equivalence of the underlying setoid maps.  The shape mirrors
   Instance/Rng.v's [Ring] exactly, since a field homomorphism IS a ring
   homomorphism: see the header on why no inverse-preservation clause is
   demanded. *)
Program Definition Field : Category := {|
  obj     := FieldObject;
  hom     := fun F K => RigHom F K;
  homset  := fun F K => @RigHom_Setoid F K;
  id      := fun F => @rig_hom_id F;
  compose := fun _ _ _ f g => rig_hom_compose f g;

  compose_respects := fun _ _ _ => @rig_hom_compose_respects _ _ _
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** ** The evident forgetful functors *)

(* To rings: identity on morphisms, since the two hom notions coincide.
   This is the inclusion of the roster entry into its neighbour, and it
   is faithful for the same definitional reason [Rng_Forget] is. *)
Program Definition Field_Rng : Field ⟶ Rng := {|
  fobj := fun F : FieldObject => field_ring F;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Rng_Faithful : Faithful Field_Rng.
Proof. constructor; intros F K f g E; exact E. Qed.

(* To setoids: the underlying set, Mac Lane's roster column. *)
Program Definition Field_Forget : Field ⟶ Sets := {|
  fobj := fun F : FieldObject => rig_setoid F;
  fmap := fun F K f => rig_map f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Forget_Faithful : Faithful Field_Forget.
Proof. constructor; intros F K f g E; exact E. Qed.

(** ** Homomorphisms reflect nothing into zero *)

(* The engine of the whole file.  If x is nonzero it is invertible, so
   1 ≈ f (x⁻¹ · x) ≈ f (x⁻¹) · f x; were f x zero the right-hand side
   would be zero, and the target's [field_one_neq_zero] refutes 1 ≈ 0.
   Unconditional: no stability, no decidability, no choice. *)
Lemma field_hom_nonzero {F K : FieldObject} (f : RigHom F K)
  (x : carrier (rig_setoid F)) :
  (x ≈ rig_zero F → False) → (rig_map f x ≈ rig_zero K → False).
Proof.
  intros Hx Hfx.
  apply (field_one_neq_zero K).
  transitivity (rig_map f (rig_one F)).
  - symmetry; apply (rig_map_one f).
  - transitivity (rig_map f (rig_mul F (finv F x) x)).
    + apply (proper_morphism (rig_map f)).
      symmetry; now apply finv_l.
    + rewrite (rig_map_mul f).
      rewrite Hfx.
      apply rig_mul_zero_r.
Qed.

(* Preservation of inverses is a theorem, not a clause of the morphism
   notion: f (x⁻¹) left-inverts f x, and (f x)⁻¹ right-inverts it — the
   latter by [finv_r], which needs f x to be nonzero, which is the
   previous lemma — so Rng.v's [rig_inv_unique] identifies them.  At
   x ≈ 0 no claim is made; see the header. *)
Lemma field_hom_finv {F K : FieldObject} (f : RigHom F K)
  (x : carrier (rig_setoid F)) (Hx : x ≈ rig_zero F → False) :
  rig_map f (finv F x) ≈ finv K (rig_map f x).
Proof.
  apply (rig_inv_unique K (rig_map f x)).
  - rewrite <- (rig_map_mul f).
    transitivity (rig_map f (rig_one F)).
    + apply (proper_morphism (rig_map f)); now apply finv_l.
    + apply (rig_map_one f).
  - apply finv_r.
    now apply (field_hom_nonzero f x Hx).
Qed.

(** ** Riehl 1.2.iii: distinct elements have distinct images *)

(* A difference vanishing forces the two elements to agree — pure ring
   arithmetic, isolated so the field argument below reads cleanly. *)
Lemma ring_sub_zero (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_add R a (ring_neg R b) ≈ rig_zero R → a ≈ b.
Proof.
  intro H.
  transitivity (rig_add R (rig_add R a (ring_neg R b)) b).
  - rewrite rig_add_assoc.
    rewrite (ring_neg_l R b).
    symmetry; apply rig_add_zero_r.
  - rewrite H.
    apply rig_add_zero_l.
Qed.

(* ... and the converse, which the stability analysis below needs. *)
Lemma ring_zero_sub (R : RingObject) (a b : carrier (rig_setoid R)) :
  a ≈ b → rig_add R a (ring_neg R b) ≈ rig_zero R.
Proof.
  intro H.
  rewrite H.
  rewrite rig_add_comm.
  apply ring_neg_l.
Qed.

(* Agreement of the images sends the difference to zero.  Isolated
   because both [field_hom_distinct] and [field_stable_at_zero_suffices]
   consume exactly this step and nothing else. *)
Lemma field_hom_sub_zero {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b →
  rig_map f (rig_add F a (ring_neg F b)) ≈ rig_zero K.
Proof.
  intro Hab.
  rewrite (rig_map_add f).
  rewrite (RigHom_neg F K f b).
  rewrite Hab.
  rewrite rig_add_comm.
  apply (ring_neg_l K (rig_map f b)).
Qed.

(* The exercise's argument, in the form it actually produces.  Given
   a ≉ b, the difference a − b is nonzero, so by [field_hom_nonzero] its
   image is nonzero; but that image is f a − f b, which any agreement of
   f a with f b would send to zero. *)
Theorem field_hom_distinct {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  (a ≈ b → False) → (rig_map f a ≈ rig_map f b → False).
Proof.
  intros Hne Hab.
  (* the difference is nonzero, since a vanishing difference gives a ≈ b *)
  assert (Hd : rig_add F a (ring_neg F b) ≈ rig_zero F → False).
  { intro H; apply Hne; exact (ring_sub_zero F a b H). }
  (* yet its image vanishes *)
  exact (field_hom_nonzero f _ Hd (field_hom_sub_zero f a b Hab)).
Qed.

(* The same content stated positively: the double negation of
   injectivity holds outright.  This is the exact unconditional
   strength — cf. Instance/Grp/Epi.v's [grp_epic_image_dense]. *)
Corollary field_hom_injective_nn {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → ((a ≈ b → False) → False).
Proof.
  intros Hab Hne.
  exact (field_hom_distinct f a b Hne Hab).
Qed.

(** ** The named hypothesis, and that it is exactly the missing step *)

(* Stability of ≈ under double negation.  Named rather than assumed
   silently, and discharged below for every field with decidable
   equality. *)
Definition FieldStable (F : FieldObject) : Type :=
  ∀ a b : carrier (rig_setoid F), ((a ≈ b → False) → False) → a ≈ b.

Lemma field_dec_stable (F : FieldObject)
  (dec : ∀ a b : carrier (rig_setoid F), (a ≈ b) + (a ≈ b → False)) :
  FieldStable F.
Proof.
  intros a b Hnn.
  destruct (dec a b) as [H | H].
  - exact H.
  - destruct (Hnn H).
Qed.

(* Nothing weaker can serve, for a reason that needs no proof of
   independence: under the premise [f a ≈ f b] the hypothesis INSTANCE
   at (a, b) and the conclusion a ≈ b inter-derive — forward by feeding
   the instance the theorem above, backward by discarding its argument.
   Read it as exactly that, a single-instance inter-derivation under the
   premise, and not as the quantified biconditional Instance/Grp/Epi.v's
   [stability_is_the_conclusion] proves; no claim is made here about the
   quantified forms. *)
Theorem stability_is_the_conclusion {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) (Hab : rig_map f a ≈ rig_map f b) :
  ((((a ≈ b → False) → False) → a ≈ b) → a ≈ b) *
  ((a ≈ b) → (((a ≈ b → False) → False) → a ≈ b)).
Proof.
  split.
  - intro Hstab.
    apply Hstab.
    exact (field_hom_injective_nn f a b Hab).
  - intros H _; exact H.
Qed.

(** ** The hypothesis is only ever used at zero *)

(* [FieldStable] quantifies over pairs, but every use below reduces the
   pair (a, b) to the single element a − b through [ring_sub_zero].  So
   the weaker-looking hypothesis "≈ is ¬¬-stable AT ZERO" already
   suffices — and it is not in fact weaker, the two being
   inter-derivable ([field_stable_stable_at_zero] and
   [field_stable_at_zero_stable]).  This turns what the header would
   otherwise have to assert into a proved statement, and it locates the
   obstruction exactly: it is about deciding "is this element zero?",
   which is the guard on [finv_l], and about nothing else. *)
Definition FieldStableAtZero (F : FieldObject) : Type :=
  ∀ a : carrier (rig_setoid F),
    ((a ≈ rig_zero F → False) → False) → a ≈ rig_zero F.

Definition field_stable_stable_at_zero (F : FieldObject) :
  FieldStable F → FieldStableAtZero F :=
  fun HF a => HF a (rig_zero F).

Lemma field_stable_at_zero_stable (F : FieldObject) :
  FieldStableAtZero F → FieldStable F.
Proof.
  intros HF a b Hnn.
  apply (ring_sub_zero F a b).
  apply HF.
  intro Hd.
  apply Hnn.
  intro Hab.
  exact (Hd (ring_zero_sub F a b Hab)).
Qed.

(* Cancellation from the zero-only form directly, spending no more than
   [field_hom_sub_zero] and [field_hom_nonzero]. *)
Theorem field_stable_at_zero_suffices {F K : FieldObject} (f : RigHom F K)
  (HF : FieldStableAtZero F) (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intro Hab.
  apply (ring_sub_zero F a b).
  apply HF.
  intro Hd.
  exact (field_hom_nonzero f _ Hd (field_hom_sub_zero f a b Hab)).
Qed.

(** ** Injectivity and Riehl's conclusion *)

Theorem field_hom_injective {F K : FieldObject} (f : RigHom F K)
  (HF : FieldStable F) (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intro Hab.
  apply HF.
  exact (field_hom_injective_nn f a b Hab).
Qed.

(* Injective ⇒ monic, in the shape Instance/Rng.v's
   [rng_injective_monic] and Instance/Grp.v's [Grp_injectivity_is_monic]
   use: cancellation in the hom-setoid is pointwise, so left
   cancellation of f is injectivity of f evaluated at the two competing
   images. *)
Theorem field_monic {F K : FieldObject} (f : F ~{Field}~> K)
  (HF : FieldStable F) : Monic f.
Proof.
  constructor; intros T g1 g2 Hg a.
  exact (field_hom_injective f HF (rig_map g1 a) (rig_map g2 a) (Hg a)).
Qed.

(* Riehl's blanket statement, with its hypothesis in view. *)
Theorem field_every_monic :
  (∀ F : FieldObject, FieldStable F) →
  ∀ (F K : FieldObject) (f : F ~{Field}~> K), Monic f.
Proof.
  intros Hstab F K f.
  exact (field_monic f (Hstab F)).
Qed.

(** ** ℚ: the witness *)

(* [Qeq] is decidable, so ℚ's equality is stable and every homomorphism
   out of ℚ is monic with no hypothesis whatsoever. *)
Lemma Q_Field_dec (a b : carrier (rig_setoid Q_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct (Qeq_dec a b) as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

Definition Q_Field_stable : FieldStable Q_Field :=
  field_dec_stable Q_Field Q_Field_dec.

Theorem Q_hom_monic (K : FieldObject) (f : Q_Field ~{Field}~> K) : Monic f.
Proof. exact (field_monic f Q_Field_stable). Qed.

(* The identity is a morphism, and ℚ is an object: the category is
   inhabited.  A second object, F₂, is built below, and the two are
   shown to have no morphism between them in either direction. *)
Example Q_Field_object : obj[Field] := Q_Field.

Example Q_Field_id : Q_Field ~{Field}~> Q_Field := @id Field Q_Field.

Example Q_Field_id_monic : Monic (@id Field Q_Field) := Q_hom_monic _ _.

(** ** ℚ is rigid *)

(* Denominators are nonzero as rationals — the one arithmetic fact the
   cancellation below needs. *)
Lemma Q_den_nonzero (q : Q) : ~ (inject_Z (Z.pos (Qden q)) == 0)%Q.
Proof. unfold Qeq, inject_Z; simpl; discriminate. Qed.

Lemma Q_cancel_r (x y b : Q) :
  ~ (b == 0)%Q → (x * b == y * b)%Q → (x == y)%Q.
Proof.
  intros Hb H.
  rewrite <- (Qmult_1_r x), <- (Qmult_1_r y).
  rewrite <- (Qmult_inv_r b Hb).
  rewrite (Qmult_assoc x b (/ b)), (Qmult_assoc y b (/ b)).
  now rewrite H.
Qed.

(* Every ring endomorphism of ℚ is the identity.  On the image of ℤ this
   is initiality of ℤ in Rng ([rng_from_Z_unique], applied twice: once
   to the composite with the inclusion and once to the inclusion
   itself); a general rational is then pinned by multiplying through by
   its denominator, which the endomorphism fixes, and cancelling.  No
   fraction is ever chosen — the same discipline as Rng.v's
   [ZtoQ_epic]. *)
Theorem Q_endo_id (f : Q_Field ~{Field}~> Q_Field) (q : Q) :
  (rig_map f q == q)%Q.
Proof.
  (* f respects Qeq, and preserves products — both by conversion *)
  assert (Hresp : ∀ x y : Q, (x == y)%Q → (rig_map f x == rig_map f y)%Q).
  { intros x y H; exact (proper_morphism (rig_map f) x y H). }
  assert (Hmul : ∀ x y : Q,
             (rig_map f (x * y) == rig_map f x * rig_map f y)%Q).
  { intros x y; exact (rig_map_mul f x y). }
  (* f fixes every integer, by initiality of ℤ used on both sides *)
  assert (Hz : ∀ z : Z, (rig_map f (inject_Z z) == inject_Z z)%Q).
  { intro z.
    transitivity (zring Q_Ring z).
    - exact (rng_from_Z_unique Q_Ring (rig_hom_compose f ZtoQ) z).
    - symmetry; exact (rng_from_Z_unique Q_Ring ZtoQ z). }
  (* multiply through by the denominator and cancel *)
  apply (Q_cancel_r _ _ (inject_Z (Z.pos (Qden q))) (Q_den_nonzero q)).
  transitivity (rig_map f (q * inject_Z (Z.pos (Qden q)))%Q).
  - rewrite Hmul.
    now rewrite (Hz (Z.pos (Qden q))).
  - transitivity (inject_Z (Qnum q)).
    + transitivity (rig_map f (inject_Z (Qnum q))).
      * apply Hresp, Q_num_den.
      * apply Hz.
    + symmetry; apply Q_num_den.
Qed.

(* ...hence the identity is the only endomorphism, in the hom-setoid. *)
Corollary Q_endo_unique (f : Q_Field ~{Field}~> Q_Field) :
  f ≈ @id Field Q_Field.
Proof. intro q; exact (Q_endo_id f q). Qed.

(** ** F₂: the second object, and a second characteristic *)

(* The two-element field, on [bool] with Leibniz equality (Sets.v's
   [bool_setoid_object]): addition is exclusive or, multiplication is
   conjunction, negation and inversion are both the identity.  Every law
   is a case analysis over at most three booleans.  The point of the
   object is that its characteristic is 2 while ℚ's is 0, which is what
   separates the two below. *)
Program Definition F2_Rig : RigObject := {|
  rig_setoid := bool_setoid_object;
  rig_zero := false;
  rig_add := xorb;
  rig_one := true;
  rig_mul := andb
|}.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.

Program Definition F2_Ring : RingObject := {|
  ring_rig := F2_Rig;
  ring_neg := fun b => b
|}.
Next Obligation. intros [|]; reflexivity. Qed.

Program Definition F2_Field : FieldObject := {|
  field_ring := F2_Ring;
  finv := fun b => b
|}.
Next Obligation. intros [|] [|]; reflexivity. Qed.
Next Obligation. discriminate. Qed.
Next Obligation.
  (* the only nonzero boolean is [true], and true · true ≈ true *)
  intros [|] Hx; [ reflexivity | destruct (Hx eq_refl) ].
Qed.

(* Leibniz equality on [bool] is decidable, so F₂ is stable and every
   homomorphism out of it is monic with no hypothesis. *)
Lemma F2_Field_dec (a b : carrier (rig_setoid F2_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct a, b;
    solve [ left; reflexivity | right; discriminate ].
Qed.

Definition F2_Field_stable : FieldStable F2_Field :=
  field_dec_stable F2_Field F2_Field_dec.

Theorem F2_hom_monic (K : FieldObject) (f : F2_Field ~{Field}~> K) :
  Monic f.
Proof. exact (field_monic f F2_Field_stable). Qed.

(** ** The two fields are not connected, in either direction *)

(* 1 + 1 in an arbitrary field.  Named because both non-existence
   theorems below run through it: it is zero in F₂ and nonzero in ℚ,
   and a homomorphism must carry it to the corresponding element. *)
Definition ftwo (F : FieldObject) : carrier (rig_setoid F) :=
  rig_add F (rig_one F) (rig_one F).

Lemma ftwo_map {F K : FieldObject} (f : RigHom F K) :
  rig_map f (ftwo F) ≈ ftwo K.
Proof.
  unfold ftwo.
  rewrite (rig_map_add f).
  now rewrite (rig_map_one f).
Qed.

(* In ℚ, 2 ≉ 0 — the whole content of "characteristic zero" that is
   needed here. *)
Lemma Q_ftwo_nonzero : ftwo Q_Field ≈ rig_zero Q_Field → False.
Proof.
  intro H.
  assert (Hq : (2 # 1 == 0)%Q) by exact H.
  unfold Qeq in Hq; simpl in Hq; discriminate Hq.
Qed.

(* In F₂, 2 ≈ 0 — and definitionally so, since [xorb true true] computes
   to [false]. *)
Lemma F2_ftwo_zero : ftwo F2_Field ≈ rig_zero F2_Field.
Proof. reflexivity. Qed.

(* No homomorphism ℚ → F₂: it would have to carry the invertible 2 to
   the zero of F₂, which [field_hom_nonzero] refutes. *)
Theorem no_hom_Q_F2 (f : Q_Field ~{Field}~> F2_Field) : False.
Proof.
  apply (field_hom_nonzero f (ftwo Q_Field) Q_ftwo_nonzero).
  rewrite (ftwo_map f).
  exact F2_ftwo_zero.
Qed.

(* ...and none the other way: g would have to carry the zero of F₂,
   which is 1 + 1 there, to 1 + 1 = 2 in ℚ, forcing 2 ≈ 0. *)
Theorem no_hom_F2_Q (g : F2_Field ~{Field}~> Q_Field) : False.
Proof.
  apply Q_ftwo_nonzero.
  rewrite <- (ftwo_map g).
  (* [ftwo F2_Field] IS [rig_zero F2_Field], by computation *)
  apply (rig_map_zero g).
Qed.

(** ** riehl:1.6:example15: fields have neither an initial nor a
       terminal object *)

(* Both proofs are constructive and case-split-free.  They are the
   standard characteristic argument, and the only subtlety is that the
   guard on [finv_l] is a NEGATION, so the negative fact "2 is not zero
   here" is exactly what licenses inverting it — no decision procedure
   is consulted, and neither [FieldStable] nor decidability is used.

   An initial field I would map to both ℚ and F₂.  The ℚ-map shows
   1 + 1 is nonzero in I, since a zero there would be carried to a zero
   in ℚ; the F₂-map then carries that nonzero element to
   1 + 1 = 0 in F₂, which [field_hom_nonzero] refutes. *)
Theorem Field_no_initial (I : @Initial Field) : False.
Proof.
  pose (f := @zero Field I Q_Field).
  pose (g := @zero Field I F2_Field).
  (* 1 + 1 is nonzero in the initial field, because its ℚ-image is 2 *)
  assert (Hnz : ftwo (@initial_obj Field I)
                  ≈ rig_zero (@initial_obj Field I) → False).
  { intro H.
    apply Q_ftwo_nonzero.
    transitivity (rig_map f (ftwo (@initial_obj Field I))).
    - symmetry; apply (ftwo_map f).
    - transitivity (rig_map f (rig_zero (@initial_obj Field I))).
      + apply (proper_morphism (rig_map f)); exact H.
      + apply (rig_map_zero f). }
  (* yet its F₂-image is zero *)
  apply (field_hom_nonzero g _ Hnz).
  rewrite (ftwo_map g).
  exact F2_ftwo_zero.
Qed.

(* Dually, a terminal field T receives both.  The F₂-map forces
   1 + 1 ≈ 0 in T, because 1 + 1 already is 0 in F₂; the ℚ-map then
   carries the nonzero 2 of ℚ onto that same zero. *)
Theorem Field_no_terminal (T : @Terminal Field) : False.
Proof.
  pose (f := @one Field T Q_Field).
  pose (g := @one Field T F2_Field).
  (* 1 + 1 vanishes in the terminal field, being the g-image of 0 *)
  assert (H0 : ftwo (@terminal_obj Field T)
                 ≈ rig_zero (@terminal_obj Field T)).
  { transitivity (rig_map g (ftwo F2_Field)).
    - symmetry; apply (ftwo_map g).
    - apply (rig_map_zero g). }
  (* yet it is the f-image of the invertible 2 of ℚ *)
  apply (field_hom_nonzero f (ftwo Q_Field) Q_ftwo_nonzero).
  rewrite (ftwo_map f).
  exact H0.
Qed.

(* The object-level readings, which are what "the category has no
   initial object" says without choosing one: NO object of [Field] is
   initial, and none is terminal. *)
Corollary Field_no_initial_obj (c : Field) (H : IsInitialObj c) : False.
Proof. exact (Field_no_initial (Initial_from_IsInitialObj H)). Qed.

Corollary Field_no_terminal_obj (c : Field) (H : IsTerminalObj c) : False.
Proof. exact (Field_no_terminal (Terminal_from_IsTerminalObj H)). Qed.

(** ** Acceptance tests *)

(* The forgetful functors return the underlying data on the nose. *)
Example field_forget_carrier (F : FieldObject) :
  Field_Forget F = rig_setoid F := eq_refl.

Example field_rng_object (F : FieldObject) :
  Field_Rng F = field_ring F := eq_refl.

(* ℚ's inverse computes, and its unit is separated from its zero. *)
Example q_inv_three : finv Q_Field (3 # 1) = (1 # 3)%Q := eq_refl.

Example q_one_neq_zero : (1 # 1) == 0 → False := field_one_neq_zero Q_Field.
