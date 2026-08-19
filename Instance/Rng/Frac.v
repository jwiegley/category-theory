Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The field of quotients, as a functor

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.3
    (printed p. 15), Exercise 1 [maclane:I.3:ex1]: exhibit the field of
    quotients of an integral domain as a functor, choosing the right
    domain category.
    nLab: https://ncatlab.org/nlab/show/field+of+fractions

    THE CHOICE OF MORPHISMS is the exercise's actual content.  A ring
    homomorphism f that sends some nonzero d to zero supports no
    induced map on fractions — n/d would need image f n / 0 — so the fraction
    construction is functorial only on homomorphisms that reflect zero,
    i.e. the INJECTIVE ones, and the standard fix is to take the
    category of integral domains with MONOMORPHISMS.  Here that
    category is [IntDom]: objects are [DomObject]s, morphisms are ring
    homomorphisms carrying an injectivity field ([DomHom]).  In-tree
    the identification "monomorphism = injection" is available in the
    direction that matters — [rng_injective_monic] (Instance/Rng.v)
    shows every [DomHom]'s underlying map is monic in [Rng].  The
    converse (monic ⇒ injective) was deferred when this was written,
    pending the free ring ℤ[x]; it is now proved, as
    [rng_monic_injective] in Instance/Rng/Polynomial.v.  Injectivity
    remains carried as DATA in [DomHom] rather than reconstructed from
    the categorical property, and that is now a choice rather than a
    necessity: the construction below consumes the injectivity witness
    directly at several sites here and downstream in
    Instance/Field/Frac.v, so recovering it from a [Monic] hypothesis at
    each use would buy nothing.

    CONSTRUCTIVE CHOICE, disclosed.  An integral domain is presented
    with CANCELLATION as the defining field ([dom_cancel]: c ≉ 0 and
    a·c ≈ b·c give a ≈ b), together with commutativity and 1 ≉ 0.
    Cancellation is the only INTEGRALITY property the construction
    consumes — the transitivity of the fraction relation and the ring
    laws below use it and the plain ring laws, nothing more — and it
    follows constructively from the no-zero-divisors disjunction in
    its Type-valued form ([DomObject_of_no_zero_divisors]; the
    Type-valued sum is constructively stronger than the classical
    Prop-valued statement), while the converse direction — recovering
    a chosen disjunct from cancellation — would need a classical,
    indeed Type-valued, case split on the setoid equality.  No
    decidability and no choice principle appears anywhere.

    THE CONSTRUCTION.  [FracObj D] is the setoid of pairs (n, d) with
    d ≉ 0, compared by cross-multiplication: (n₁, d₁) ≈ (n₂, d₂) iff
    n₁·d₂ ≈ n₂·d₁.  Fraction arithmetic makes it a commutative ring
    ([FracRing], [FracRing_comm]), the functor [Frac : IntDom ⟶ CRng]
    acts componentwise on morphisms, and the FIELD property is the
    lemma [frac_recip]: every fraction whose numerator is apart from
    zero has a reciprocal ([frac_nonzero_recip] packages it against
    apartness from the zero fraction).  The embedding n ↦ n/1 is
    [frac_embed], itself injective ([frac_embed_inj]) — the unit of
    the universal-arrow reading of the construction
    (Theory/Universal/Arrow.v's essay lists this very example); the
    full universal property needs a category of fields to land in and
    is left to the future fields development.

    THE LIE HALF of Mac Lane's exercise — the Lie algebra of a Lie
    group as a functor — needs smooth manifolds and is out of scope
    for this library for the foreseeable future; the catalog item is
    covered with that descope made explicit here.

    Witness: ℤ ([Int_Dom], cancellation from [Z.mul_cancel_r]), where
    1/2 + 1/3 ≈ 5/6 computes by [eq_refl]. *)

(** ** Negation moves through products *)

(* (−a)·b ≈ −(a·b), from [rig_mul_neg_one] by reassociation; needed
   for the fraction ring's negation to respect the cross-multiplication
   equivalence. *)
Lemma mul_neg_l (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R a) b ≈ ring_neg R (rig_mul R a b).
Proof.
  rewrite <- (rig_mul_neg_one R (rig_mul R a b)).
  rewrite <- (rig_mul_assoc R).
  rewrite (rig_mul_neg_one R a).
  reflexivity.
Qed.

(** ** Integral domains, constructively *)

Record DomObject := {
  dom_ring :> RingObject;
  dom_comm : ∀ a b, rig_mul dom_ring a b ≈ rig_mul dom_ring b a;
  dom_nontrivial : rig_one dom_ring ≈ rig_zero dom_ring → False;
  dom_cancel : ∀ a b c,
    (c ≈ rig_zero dom_ring → False) →
    rig_mul dom_ring a c ≈ rig_mul dom_ring b c →
    a ≈ b
}.

(* The classical presentation implies this one: a commutative nontrivial
   ring whose zero products split as a (Type-valued) disjunction
   cancels.  The two branches: c ≈ 0 contradicts the hypothesis, and
   a − b ≈ 0 gives a ≈ b by the group laws. *)
Program Definition DomObject_of_no_zero_divisors
  (R : RingObject)
  (comm : ∀ a b, rig_mul R a b ≈ rig_mul R b a)
  (nontriv : rig_one R ≈ rig_zero R → False)
  (nzd : ∀ a b, rig_mul R a b ≈ rig_zero R →
           (a ≈ rig_zero R) + (b ≈ rig_zero R)) : DomObject := {|
  dom_ring := R;
  dom_comm := comm;
  dom_nontrivial := nontriv
|}.
Next Obligation.
  intros R comm nontriv nzd a b c Hc Habc.
  destruct (nzd (rig_add R a (ring_neg R b)) c) as [Hab | H0]; [| |].
  - rewrite rig_distr_r.
    rewrite mul_neg_l.
    rewrite Habc.
    apply (ring_neg_r R).
  - symmetry.
    rewrite <- (rig_add_zero_l R b).
    rewrite <- Hab.
    rewrite rig_add_assoc.
    rewrite (ring_neg_l R b).
    apply (rig_add_zero_r R).
  - destruct (Hc H0).
Qed.

(* Products of elements apart from zero stay apart from zero — the
   contrapositive form of "no zero divisors", derived from
   cancellation alone. *)
Lemma dom_mul_nonzero (D : DomObject) (a b : carrier (rig_setoid D)) :
  (a ≈ rig_zero D → False) → (b ≈ rig_zero D → False) →
  rig_mul D a b ≈ rig_zero D → False.
Proof.
  intros Ha Hb Hab.
  apply Ha.
  apply (dom_cancel D a (rig_zero D) b Hb).
  rewrite Hab.
  symmetry.
  apply rig_mul_zero_l.
Qed.

(** ** The category of integral domains with monomorphisms *)

Record DomHom (D E : DomObject) := {
  dom_map :> RigHom D E;
  dom_map_inj : ∀ a b, dom_map a ≈ dom_map b → a ≈ b
}.

Arguments dom_map {D E} _.
Arguments dom_map_inj {D E} _ _ _ _.

Program Definition dom_id {D : DomObject} : DomHom D D := {|
  dom_map := @rig_hom_id (dom_ring D)
|}.
Next Obligation. intros D a b H; exact H. Qed.

Program Definition dom_compose {D E F : DomObject}
  (f : DomHom E F) (g : DomHom D E) : DomHom D F := {|
  dom_map := rig_hom_compose (dom_map f) (dom_map g)
|}.
Next Obligation.
  intros D E F f g a b H.
  exact (dom_map_inj g a b (dom_map_inj f _ _ H)).
Qed.

(* The design justification, machine-checked: every [DomHom]'s
   underlying map is a monomorphism of [Rng]. *)
Lemma DomHom_monic {D E : DomObject} (f : DomHom D E) :
  Monic (dom_map f : dom_ring D ~{Rng}~> dom_ring E).
Proof. exact (rng_injective_monic (dom_map f) (dom_map_inj f)). Qed.

Program Definition IntDom : Category := {|
  obj     := DomObject;
  hom     := DomHom;
  homset  := fun D E =>
    {| Setoid.equiv := fun f g => ∀ x, dom_map f x ≈ dom_map g x |};
  id      := fun D => @dom_id D;
  compose := fun _ _ _ f g => dom_compose f g
|}.
Next Obligation.
  intros D E; constructor.
  - intros f x; reflexivity.
  - intros f g H x; symmetry; apply H.
  - intros f g h H1 H2 x.
    transitivity (dom_map g x); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros D E F f f' Hf g g' Hg x; simpl.
  rewrite (Hg x).
  exact (Hf (dom_map g' x)).
Qed.
Next Obligation. intros D E f x; simpl; reflexivity. Qed.
Next Obligation. intros D E f x; simpl; reflexivity. Qed.
Next Obligation. intros D E F G f g h x; simpl; reflexivity. Qed.
Next Obligation. intros D E F G f g h x; simpl; reflexivity. Qed.

(* The inclusion into commutative rings: on objects, forget the domain
   fields; on morphisms, forget injectivity.  Faithfulness is proved
   below ([IntDom_Incl_Faithful]): both hom-setoids compare underlying
   maps pointwise.  Fullness is expected to be REFUTABLE — a
   non-injective homomorphism between domains, such as ℤ → ℤ/2ℤ, has
   no preimage — but the tree has no quotient rings yet, so no
   counterexample object is available and non-fullness is left
   unstated rather than asserted.

   ERRATUM, appended rather than rewritten so that
   Instance/Field/Frac.v's QUOTATION of the sentence above stays an
   accurate quotation.  Both clauses have since been overtaken.  (1) The
   deferral itself was DISCHARGED in Instance/Field/Frac.v by
   [IntDom_Incl_not_Full], which needed no quotient ring at all: F₂ is a
   field, hence a domain, and [ZtoF2] is a homomorphism into it with no
   [IntDom] preimage.  (2) The tree DOES now have quotient rings —
   Instance/Rng/Quotient.v builds R/I for a two-sided ideal I with its
   universal property, and ℤ/2ℤ is its worked witness — so the
   counterexample object the sentence above wished for is available too,
   though it is no longer needed. *)
Program Definition IntDom_Incl : IntDom ⟶ CRng := {|
  fobj := fun D => (dom_ring D; dom_comm D);
  fmap := fun _ _ f => (dom_map f; I)
|}.
Next Obligation.
  intros D E f g Hfg; simpl.
  exact Hfg.
Qed.
Next Obligation. intros D x; simpl; reflexivity. Qed.
Next Obligation. intros D E F f g x; simpl; reflexivity. Qed.

#[export] Program Instance IntDom_Incl_Faithful : Faithful IntDom_Incl.
Next Obligation. intros D E f g H x; exact (H x). Qed.

(** ** The fraction construction *)

Section FracConstruction.

Context (D : DomObject).

Local Notation z0 := (rig_zero D).
Local Notation e1 := (rig_one D).
Local Infix "+" := (rig_add D).
Local Infix "*" := (rig_mul D).

(* A small shuffle kit for the commutative multiplication; every
   cross-multiplication identity below is a chain of these. *)
Lemma mulC (a b : carrier (rig_setoid D)) : a * b ≈ b * a.
Proof. apply dom_comm. Qed.

Lemma mulA (a b c : carrier (rig_setoid D)) :
  (a * b) * c ≈ a * (b * c).
Proof. apply rig_mul_assoc. Qed.

Lemma mul_swap_r (a b c : carrier (rig_setoid D)) :
  (a * b) * c ≈ (a * c) * b.
Proof.
  rewrite mulA.
  rewrite (mulC b c).
  rewrite <- mulA.
  reflexivity.
Qed.

Lemma mul4_shuffle1 (a b c d : carrier (rig_setoid D)) :
  (a * b) * (c * d) ≈ (a * c) * (b * d).
Proof.
  rewrite mulA.
  rewrite <- (mulA b c d).
  rewrite (mulC b c).
  rewrite (mulA c b d).
  rewrite <- mulA.
  reflexivity.
Qed.

Lemma mul4_shuffle2 (a b c d : carrier (rig_setoid D)) :
  (a * b) * (c * d) ≈ (a * d) * (c * b).
Proof.
  rewrite (mulC c d).
  rewrite mul4_shuffle1.
  rewrite (mulC b c).
  reflexivity.
Qed.

(* Congruence in a form [apply] accepts without unfolding [Proper]. *)
Lemma addf (a a' b b' : carrier (rig_setoid D)) :
  a ≈ a' → b ≈ b' → a + b ≈ a' + b'.
Proof. intros Ha Hb; now rewrite Ha, Hb. Qed.

Lemma mulf (a a' b b' : carrier (rig_setoid D)) :
  a ≈ a' → b ≈ b' → a * b ≈ a' * b'.
Proof. intros Ha Hb; now rewrite Ha, Hb. Qed.

(* Pairs with denominator apart from zero.  The family of the sigma is
   explicit throughout ([mk_frac]), the 8.19/8.20-safe form. *)
Definition frac_carrier : Type :=
  { nd : carrier (rig_setoid D) * carrier (rig_setoid D)
       & snd nd ≈ z0 → False }.

Definition mk_frac (n d : carrier (rig_setoid D))
  (Hd : d ≈ z0 → False) : frac_carrier :=
  existT (fun nd : carrier (rig_setoid D) * carrier (rig_setoid D) =>
            snd nd ≈ z0 → False)
    (n, d) Hd.

Definition num (x : frac_carrier) : carrier (rig_setoid D) := fst (`1 x).
Definition den (x : frac_carrier) : carrier (rig_setoid D) := snd (`1 x).
Definition den_nonzero (x : frac_carrier) : den x ≈ z0 → False := `2 x.

(* Cross-multiplication comparison. *)
Definition frac_eq (x y : frac_carrier) : Type :=
  num x * den y ≈ num y * den x.

Lemma frac_eq_refl (x : frac_carrier) : frac_eq x x.
Proof. unfold frac_eq; reflexivity. Qed.

Lemma frac_eq_sym (x y : frac_carrier) : frac_eq x y → frac_eq y x.
Proof. unfold frac_eq; intros H; symmetry; exact H. Qed.

(* Transitivity is where the domain earns its keep: cancel the shared
   denominator. *)
Lemma frac_eq_trans (x y z : frac_carrier) :
  frac_eq x y → frac_eq y z → frac_eq x z.
Proof.
  unfold frac_eq; intros H1 H2.
  apply (dom_cancel D _ _ (den y) (den_nonzero y)).
  rewrite mul_swap_r.
  rewrite H1.
  rewrite mul_swap_r.
  rewrite H2.
  rewrite mul_swap_r.
  reflexivity.
Qed.

Program Definition FracObj : SetoidObject := {|
  carrier := frac_carrier;
  is_setoid := {| Setoid.equiv := frac_eq |}
|}.
Next Obligation.
  equivalence.
  - apply frac_eq_refl.
  - apply frac_eq_sym; assumption.
  - eapply frac_eq_trans; eassumption.
Qed.

(* Equal parts give equal fractions; most ring laws below reduce to
   this. *)
Lemma frac_eq_of_parts (x y : frac_carrier) :
  num x ≈ num y → den x ≈ den y → frac_eq x y.
Proof.
  intros Hn Hd; unfold frac_eq.
  now rewrite Hn, <- Hd.
Qed.

(** *** Fraction arithmetic *)

Definition frac_zero : frac_carrier := mk_frac z0 e1 (dom_nontrivial D).
Definition frac_one : frac_carrier := mk_frac e1 e1 (dom_nontrivial D).

Definition frac_add (x y : frac_carrier) : frac_carrier :=
  mk_frac (num x * den y + num y * den x) (den x * den y)
    (dom_mul_nonzero D _ _ (den_nonzero x) (den_nonzero y)).

Definition frac_mul (x y : frac_carrier) : frac_carrier :=
  mk_frac (num x * num y) (den x * den y)
    (dom_mul_nonzero D _ _ (den_nonzero x) (den_nonzero y)).

Definition frac_neg (x : frac_carrier) : frac_carrier :=
  mk_frac (ring_neg D (num x)) (den x) (den_nonzero x).

Lemma frac_add_respects (x x' y y' : frac_carrier) :
  frac_eq x x' → frac_eq y y' → frac_eq (frac_add x y) (frac_add x' y').
Proof.
  unfold frac_eq; intros H1 H2; unfold frac_add, num, den in *; simpl.
  rewrite !rig_distr_r.
  apply addf.
  - transitivity ((fst `1 x * snd `1 x') * (snd `1 y * snd `1 y')).
    { apply mul4_shuffle1. }
    transitivity ((fst `1 x' * snd `1 x) * (snd `1 y * snd `1 y')).
    { now rewrite H1. }
    transitivity ((fst `1 x' * snd `1 y) * (snd `1 x * snd `1 y')).
    { apply mul4_shuffle1. }
    apply mul4_shuffle2.
  - transitivity ((fst `1 y * snd `1 y') * (snd `1 x' * snd `1 x)).
    { apply mul4_shuffle2. }
    transitivity ((fst `1 y' * snd `1 y) * (snd `1 x' * snd `1 x)).
    { now rewrite H2. }
    transitivity ((fst `1 y' * snd `1 x') * (snd `1 y * snd `1 x)).
    { apply mul4_shuffle1. }
    apply mulf; [ reflexivity | apply mulC ].
Qed.

Lemma frac_mul_respects (x x' y y' : frac_carrier) :
  frac_eq x x' → frac_eq y y' → frac_eq (frac_mul x y) (frac_mul x' y').
Proof.
  unfold frac_eq; intros H1 H2; unfold frac_mul, num, den in *; simpl.
  transitivity ((fst `1 x * snd `1 x') * (fst `1 y * snd `1 y')).
  { apply mul4_shuffle1. }
  transitivity ((fst `1 x' * snd `1 x) * (fst `1 y' * snd `1 y)).
  { now rewrite H1, H2. }
  apply mul4_shuffle1.
Qed.

Lemma frac_neg_respects (x y : frac_carrier) :
  frac_eq x y → frac_eq (frac_neg x) (frac_neg y).
Proof.
  unfold frac_eq; simpl; intros H; unfold num, den in *; simpl.
  rewrite !mul_neg_l.
  rewrite H.
  reflexivity.
Qed.

(** *** The ring laws *)

Lemma frac_add_assoc (x y z : frac_carrier) :
  frac_eq (frac_add (frac_add x y) z) (frac_add x (frac_add y z)).
Proof.
  apply frac_eq_of_parts; unfold frac_add, num, den; simpl.
  - rewrite !rig_distr_r.
    rewrite !rig_add_assoc.
    apply addf; [ apply mulA |].
    apply addf.
    + apply mul_swap_r.
    + transitivity (fst `1 z * (snd `1 y * snd `1 x)).
      { apply mulf; [ reflexivity | apply mulC ]. }
      symmetry; apply mulA.
  - apply mulA.
Qed.

Lemma frac_add_comm (x y : frac_carrier) :
  frac_eq (frac_add x y) (frac_add y x).
Proof.
  apply frac_eq_of_parts; simpl; unfold num, den; simpl.
  - apply rig_add_comm.
  - apply mulC.
Qed.

Lemma frac_add_zero_l (x : frac_carrier) :
  frac_eq (frac_add frac_zero x) x.
Proof.
  apply frac_eq_of_parts; simpl; unfold num, den; simpl.
  - rewrite rig_mul_zero_l.
    rewrite rig_add_zero_l.
    apply rig_mul_one_r.
  - apply rig_mul_one_l.
Qed.

Lemma frac_neg_l (x : frac_carrier) :
  frac_eq (frac_add (frac_neg x) x) frac_zero.
Proof.
  unfold frac_eq; simpl; unfold num, den; simpl.
  rewrite rig_mul_one_r.
  rewrite <- rig_distr_r.
  rewrite (rig_add_comm D).
  rewrite (ring_neg_r D).
  rewrite !rig_mul_zero_l.
  reflexivity.
Qed.

Lemma frac_mul_assoc (x y z : frac_carrier) :
  frac_eq (frac_mul (frac_mul x y) z) (frac_mul x (frac_mul y z)).
Proof.
  apply frac_eq_of_parts; simpl; unfold num, den; simpl; apply mulA.
Qed.

Lemma frac_mul_comm (x y : frac_carrier) :
  frac_eq (frac_mul x y) (frac_mul y x).
Proof.
  apply frac_eq_of_parts; simpl; unfold num, den; simpl; apply mulC.
Qed.

Lemma frac_mul_one_l (x : frac_carrier) :
  frac_eq (frac_mul frac_one x) x.
Proof.
  apply frac_eq_of_parts; simpl; unfold num, den; simpl;
    apply rig_mul_one_l.
Qed.

Lemma frac_mul_zero_l (x : frac_carrier) :
  frac_eq (frac_mul frac_zero x) frac_zero.
Proof.
  unfold frac_eq, frac_mul, frac_zero, num, den; simpl.
  now rewrite !rig_mul_zero_l.
Qed.

(* Distribution is the one law that does not split into equal parts:
   the two sides carry different (but associate) denominators, and the
   cross-multiplication identity is a genuine six-factor shuffle. *)
Lemma frac_distr_l (x y z : frac_carrier) :
  frac_eq (frac_mul x (frac_add y z))
          (frac_add (frac_mul x y) (frac_mul x z)).
Proof.
  unfold frac_eq, frac_mul, frac_add, num, den; simpl.
  rewrite rig_distr_l.
  rewrite !rig_distr_r.
  apply addf.
  - transitivity (((fst `1 x * fst `1 y) * snd `1 z)
                    * ((snd `1 x * snd `1 y) * (snd `1 x * snd `1 z))).
    { apply mulf; [ symmetry; apply mulA | reflexivity ]. }
    transitivity (((fst `1 x * fst `1 y) * (snd `1 x * snd `1 z))
                    * ((snd `1 x * snd `1 y) * snd `1 z)).
    { apply mul4_shuffle2. }
    apply mulf; [ reflexivity | apply mulA ].
  - transitivity (((fst `1 x * fst `1 z) * snd `1 y)
                    * ((snd `1 x * snd `1 y) * (snd `1 x * snd `1 z))).
    { apply mulf; [ symmetry; apply mulA | reflexivity ]. }
    transitivity (((fst `1 x * fst `1 z) * (snd `1 x * snd `1 y))
                    * (snd `1 y * (snd `1 x * snd `1 z))).
    { apply mul4_shuffle1. }
    apply mulf; [ reflexivity |].
    transitivity ((snd `1 y * snd `1 x) * snd `1 z).
    { symmetry; apply mulA. }
    transitivity ((snd `1 x * snd `1 y) * snd `1 z).
    { apply mulf; [ apply mulC | reflexivity ]. }
    apply mulA.
Qed.

(** *** The fraction ring *)

Program Definition FracRig : RigObject := {|
  rig_setoid := FracObj;
  rig_zero := frac_zero;
  rig_add := frac_add;
  rig_one := frac_one;
  rig_mul := frac_mul
|}.
Next Obligation.
  intros x x' Hx y y' Hy; apply frac_add_respects; assumption.
Qed.
Next Obligation.
  intros x x' Hx y y' Hy; apply frac_mul_respects; assumption.
Qed.
Next Obligation. intros x y z; apply frac_add_assoc. Qed.
Next Obligation. intros x y; apply frac_add_comm. Qed.
Next Obligation. intros x; apply frac_add_zero_l. Qed.
Next Obligation. intros x y z; apply frac_mul_assoc. Qed.
Next Obligation. intros x; apply frac_mul_one_l. Qed.
Next Obligation.
  intros x.
  apply frac_eq_trans with (frac_mul frac_one x).
  - apply frac_mul_comm.
  - apply frac_mul_one_l.
Qed.
Next Obligation. intros x y z; apply frac_distr_l. Qed.
Next Obligation.
  intros x y z.
  apply frac_eq_trans with (frac_mul z (frac_add x y)).
  - apply frac_mul_comm.
  - apply frac_eq_trans with
      (frac_add (frac_mul z x) (frac_mul z y)).
    + apply frac_distr_l.
    + apply frac_add_respects; apply frac_mul_comm.
Qed.
Next Obligation. intros x; apply frac_mul_zero_l. Qed.
Next Obligation.
  intros x.
  apply frac_eq_trans with (frac_mul frac_zero x).
  - apply frac_mul_comm.
  - apply frac_mul_zero_l.
Qed.

Program Definition FracRing : RingObject := {|
  ring_rig := FracRig;
  ring_neg := frac_neg
|}.
Next Obligation. intros x y Hxy; apply frac_neg_respects; assumption. Qed.
Next Obligation. intros x; apply frac_neg_l. Qed.

Lemma FracRing_comm : ∀ a b,
  rig_mul FracRing a b ≈ rig_mul FracRing b a.
Proof. intros x y; apply frac_mul_comm. Qed.

(** *** Field of quotients: reciprocals and the embedding *)

(* The FIELD property, constructively scoped: a fraction whose
   numerator is apart from zero has a reciprocal — the flipped pair. *)
Lemma frac_recip (x : frac_carrier) (Hn : num x ≈ z0 → False) :
  frac_eq (frac_mul x (mk_frac (den x) (num x) Hn)) frac_one.
Proof.
  unfold frac_eq; simpl; unfold num, den; simpl.
  rewrite rig_mul_one_r.
  rewrite rig_mul_one_l.
  apply mulC.
Qed.

(* Apartness from the zero fraction is exactly apartness of the
   numerator, so reciprocals exist for every fraction apart from 0. *)
Lemma frac_nonzero_num (x : frac_carrier)
  (Hx : frac_eq x frac_zero → False) : num x ≈ z0 → False.
Proof.
  intros Hn; apply Hx.
  unfold frac_eq; simpl; unfold num, den in *; simpl.
  rewrite rig_mul_one_r.
  rewrite rig_mul_zero_l.
  exact Hn.
Qed.

Definition frac_nonzero_recip (x : frac_carrier)
  (Hx : frac_eq x frac_zero → False) :
  { y : frac_carrier & frac_eq (frac_mul x y) frac_one } :=
  existT (fun y : frac_carrier => frac_eq (frac_mul x y) frac_one)
    (mk_frac (den x) (num x) (frac_nonzero_num x Hx))
    (frac_recip x (frac_nonzero_num x Hx)).

(* The embedding n ↦ n/1: a homomorphism of rings, injective — the
   universal-arrow unit of the construction. *)
Program Definition frac_embed : RigHom (dom_ring D) FracRing := {|
  rig_map := {| morphism := fun n : carrier (rig_setoid D) =>
                  mk_frac n e1 (dom_nontrivial D) |}
|}.
Next Obligation.
  intros a b Hab.
  apply frac_eq_of_parts; [ exact Hab | reflexivity ].
Qed.
Next Obligation. apply frac_eq_refl. Qed.
Next Obligation.
  intros a b; apply frac_eq_of_parts; unfold num, den; simpl.
  - now rewrite !rig_mul_one_r.
  - symmetry; apply rig_mul_one_l.
Qed.
Next Obligation. apply frac_eq_refl. Qed.
Next Obligation.
  intros a b; apply frac_eq_of_parts; simpl; unfold num, den; simpl.
  - reflexivity.
  - symmetry; apply rig_mul_one_l.
Qed.

Lemma frac_embed_inj (a b : carrier (rig_setoid D)) :
  frac_embed a ≈ frac_embed b → a ≈ b.
Proof.
  simpl; unfold frac_eq; simpl; unfold num, den; simpl; intros H.
  rewrite <- (rig_mul_one_r D a).
  rewrite <- (rig_mul_one_r D b).
  exact H.
Qed.

End FracConstruction.

(** ** Functoriality on monomorphisms *)

Program Definition Frac_map {D E : DomObject} (f : DomHom D E) :
  RigHom (FracRing D) (FracRing E) := {|
  rig_map := {| morphism := fun x =>
    mk_frac E (dom_map f (num D x)) (dom_map f (den D x)) _ |}
|}.
Next Obligation.
  intros D E f x H.
  apply (den_nonzero D x).
  apply (dom_map_inj f).
  rewrite H.
  symmetry.
  apply (rig_map_zero (dom_map f)).
Qed.
Next Obligation.
  intros D E f x y H; simpl; unfold frac_eq, num, den; simpl.
  transitivity (dom_map f (rig_mul D (fst `1 x) (snd `1 y))).
  { symmetry; apply (rig_map_mul (dom_map f)). }
  transitivity (dom_map f (rig_mul D (fst `1 y) (snd `1 x))).
  { exact (proper_morphism (rig_map (dom_map f)) _ _ H). }
  apply (rig_map_mul (dom_map f)).
Qed.
Next Obligation.
  intros D E f; apply frac_eq_of_parts; simpl; unfold num, den; simpl.
  - apply (rig_map_zero (dom_map f)).
  - apply (rig_map_one (dom_map f)).
Qed.
Next Obligation.
  intros D E f x y; apply frac_eq_of_parts; simpl; unfold num, den; simpl.
  - rewrite (rig_map_add (dom_map f)).
    apply rig_add_respects; apply (rig_map_mul (dom_map f)).
  - apply (rig_map_mul (dom_map f)).
Qed.
Next Obligation.
  intros D E f; apply frac_eq_of_parts; simpl; unfold num, den; simpl.
  - apply (rig_map_one (dom_map f)).
  - apply (rig_map_one (dom_map f)).
Qed.
Next Obligation.
  intros D E f x y; apply frac_eq_of_parts; simpl; unfold num, den; simpl;
    apply (rig_map_mul (dom_map f)).
Qed.

Program Definition Frac : IntDom ⟶ CRng := {|
  fobj := fun D => (FracRing D; FracRing_comm D);
  fmap := fun D E f => (Frac_map f; I)
|}.
Next Obligation.
  intros D E f g Hfg x; simpl.
  unfold frac_eq; simpl; unfold num, den; simpl.
  rewrite (Hfg (fst `1 x)).
  rewrite (Hfg (snd `1 x)).
  reflexivity.
Qed.
Next Obligation.
  intros D x; simpl; unfold frac_eq, num, den; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros D E F f g x; simpl; unfold frac_eq, num, den; simpl.
  reflexivity.
Qed.

(** ** The integers are an integral domain; 1/2 + 1/3 computes *)

Program Definition Int_Dom : DomObject := {|
  dom_ring := Int_Ring;
  dom_comm := Int_Ring_commutative
|}.
Next Obligation. simpl; intros H; discriminate H. Qed.
Next Obligation.
  intros a b c Hc H; simpl in *.
  apply (Z.mul_cancel_r a b c); [ exact Hc | exact H ].
Qed.

Lemma two_nonzero : (2%Z : carrier (rig_setoid Int_Dom)) ≈ rig_zero Int_Dom → False.
Proof. simpl; intros H; discriminate H. Qed.

Lemma three_nonzero : (3%Z : carrier (rig_setoid Int_Dom)) ≈ rig_zero Int_Dom → False.
Proof. simpl; intros H; discriminate H. Qed.

Lemma six_nonzero : (6%Z : carrier (rig_setoid Int_Dom)) ≈ rig_zero Int_Dom → False.
Proof. simpl; intros H; discriminate H. Qed.

(* The arithmetic of fractions of integers computes: 1/2 + 1/3 ≈ 5/6,
   the cross-multiplication (1·3 + 1·2)·6 = 5·(2·3) reducing to
   30 = 30. *)
Example frac_int_half_plus_third :
  frac_eq Int_Dom
    (frac_add Int_Dom
       (mk_frac Int_Dom 1%Z 2%Z two_nonzero)
       (mk_frac Int_Dom 1%Z 3%Z three_nonzero))
    (mk_frac Int_Dom 5%Z 6%Z six_nonzero) := eq_refl.

(* The embedding of ℤ into its fraction field, with 3 ↦ 3/1. *)
Example frac_embed_Z_3 :
  num Int_Dom (frac_embed Int_Dom 3%Z) = 3%Z := eq_refl.
