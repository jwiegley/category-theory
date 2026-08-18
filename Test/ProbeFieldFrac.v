Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Frac.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Instance.Field.Frac.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

(** * Boundary probe: what is and is not definitional in the field of
      quotients as a universal arrow

    Companion to Instance/Field/Frac.v (Mac Lane §III.1).  That file
    makes several strength claims — some things hold at Leibniz [=] by
    [eq_refl], one deliberately holds only up to [≈] — and a strength
    claim that lives only in a header is a claim nothing in the build
    would notice losing.  This file pins the boundary in the manner of
    Test/ProbeModTensor.v: **if the [Fail] commands here stop failing,
    this file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very
    little — it passes just as happily when the term is ill-typed for
    some unrelated reason, or when a name has been renamed out from
    under it.  So each negative probe is paired with a positive control
    which must SUCCEED, and the controls are the claims themselves.

    The instrument was checked before being trusted: wrapping [Fail]
    around a command that succeeds reports "The command has not
    failed!" and aborts compilation, so [Fail] here is not a no-op.
    Each negative below was also run with the [Fail] stripped and the
    error confirmed to be a genuine unification or typing error rather
    than a syntax, scope or coercion error; the diagnoses are recorded
    beside each probe.  That check earned its keep: the first two
    negatives, run in a file that did not import Instance/Sets, aborted
    with "Illegal application (Non-functional construction)" — the
    [SetoidMorphism]-to-function coercion was simply absent — which
    would have been a FALSE PASS under [Fail].  The import list above
    is therefore the one Instance/Field/Frac.v itself uses.

    The four negatives and their causes:

      - THE EXTENSION'S COMPUTED VALUE IS PINNED.  The extension of
        ℤ ↪ ℚ carries the fraction 1/2 to the rational [1 # 2] at
        Leibniz equality.  The first negative replaces the value with
        [1 # 3], which is simply wrong, and confirms that the [eq_refl]
        in the positive control discriminates at all rather than being
        absorbed by some coercion.

      - AND IT IS PINNED AT LEIBNIZ STRENGTH, NOT UP TO [Qeq].  The
        second negative replaces the value with [2 # 4], which IS [Qeq]
        -equal to the true answer — [q_probe_qeq] proves it, by
        [eq_refl] no less — and is NOT Leibniz-equal to it
        ([q_probe_not_leibniz]).  So this negative is a genuine
        strength boundary and not a second wrong-value probe: it is
        exactly the difference between "the extension computes to the
        rational one half" and "it computes to something equivalent to
        one half", and Instance/Field/Frac.v claims the former.

      - THE TWO FORGETFUL FUNCTORS AGREE ONLY UP TO [≈] ON MORPHISMS.
        [Field_IntDom stab] and [StableField_IntDom] send a morphism of
        [StableField] to [DomHom]s with the SAME underlying map but
        DIFFERENT injectivity proofs — [stab F] against the object's
        own stability datum — and [DomHom] carries that proof as a
        record field, so the two records are distinct terms.  The
        positive control is the [≈] statement, which holds because
        [IntDom]'s hom-setoid compares underlying maps pointwise and
        ignores the proof.  This is the one place in that file where
        strictness was attempted and rejected.

      - ...WHICH IS NOT A GENERIC FACT ABOUT [DomHom] RECORDS.  The
        third positive control is the SAME SHAPE of comparison for
        [IntDom_Dom ◯ StableField_IntDom] against [StableField_Dom],
        and that one IS strict, by [eq_refl]: [IntDom_Dom] forgets
        exactly the injectivity field that was just supplied, so the
        composite reduces to the underlying map on the nose.  Without
        this control the previous negative would say only "records with
        proof fields are rarely convertible"; with it, it says the
        proofs genuinely differ in that one case and not in this one.

      - THE TWO DOMAIN CATEGORIES DIFFER AT THE LEVEL OF TYPES.
        Reduction mod 2 is a morphism of [Dom] (positive control) and
        is not even well-typed as a morphism of [IntDom] (fourth
        negative), [IntDom]'s homs being [DomHom]s, which bundle an
        injectivity datum, and not bare [RigHom]s.  The probe records
        the TYPING half only; the mathematical half — that no [DomHom]
        from ℤ to F₂ exists at all, so the hom-set is empty rather than
        merely differently packaged — is PROVED in
        Instance/Field/Frac.v as [no_DomHom_Z_F2], and a probe would be
        the weaker statement. *)

(** ** The extension's computed value *)

(* Positive control: the claim itself. *)
Example frac_extend_half_control :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 2)%Q := eq_refl.

(* Negative 1 — a wrong value.  Stripped of [Fail] this reports
   "cannot unify" between the extension's value and [1 # 3]. *)
Fail Example frac_extend_half_wrong :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 3)%Q := eq_refl.

(* The two controls that make the next negative a strength boundary
   rather than a second wrong value: [2 # 4] is [Qeq]-equal to the true
   answer and is not Leibniz-equal to it. *)
Example q_probe_qeq : ((2 # 4) == (1 # 2))%Q := eq_refl.

Example q_probe_not_leibniz : (2 # 4)%Q = (1 # 2)%Q → False.
Proof. discriminate. Qed.

(* Negative 2 — a [Qeq]-equal but not Leibniz-equal value.  Stripped of
   [Fail] this reports "cannot unify" between the extension's value and
   [2 # 4]. *)
Fail Example frac_extend_half_only_up_to_Qeq :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (2 # 4)%Q := eq_refl.

(** ** The two forgetful functors into [IntDom] *)

(* Positive control: agreement up to ≈ on morphisms. *)
Example field_intdom_agrees_up_to_equiv
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    ≈ fmap[StableField_IntDom] f.
Proof. intro a; simpl; reflexivity. Qed.

(* Negative 3 — the same agreement at Leibniz equality.  Stripped of
   [Fail] this reports "cannot unify" between the two [DomHom]s, whose
   [dom_map_inj] fields are built from different stability data. *)
Fail Example field_intdom_agrees_strictly
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    = fmap[StableField_IntDom] f := eq_refl.

(* Positive control: the SAME shape of comparison, one functor along,
   IS strict — so the negative above is not a generic fact about
   proof-carrying records. *)
Example intdom_dom_agrees_strictly (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[IntDom_Dom] (fmap[StableField_IntDom] f) = fmap[StableField_Dom] f
  := eq_refl.

(** ** Reduction mod 2 lives in [Dom] and not in [IntDom] *)

(* Positive control. *)
Example ZtoF2_is_a_Dom_morphism :
  Int_Dom ~{Dom}~> Field_Dom F2_Field := ZtoF2.

(* Negative 4 — the same term as a morphism of [IntDom].  Stripped of
   [Fail] this reports that [ZtoF2] has type [Int_Ring ~{Rng}~> F2_Ring]
   while a [DomHom] is expected: a typing error, not a proof obligation.
   That no [DomHom] exists there AT ALL is the theorem
   [no_DomHom_Z_F2]. *)
Fail Definition ZtoF2_is_not_an_IntDom_morphism :
  Int_Dom ~{IntDom}~> field_dom F2_Field := ZtoF2.
