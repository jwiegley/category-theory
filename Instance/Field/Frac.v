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
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* NAME COLLISION, recorded because it is silent and the error it
   produces names neither culprit.  [Coq.QArith.QArith] transitively
   exports [Stdlib.setoid_ring.Field_theory.num] — the numerator of the
   [linear] datatype of the [field] tactic — which SHADOWS
   Instance/Rng/Frac.v's [num].  Its [den] is not shadowed, so the
   symptom is a type error mentioning [linear] on the numerator alone.
   Rather than depend on the order of two [Require Import]s, the
   fraction numerator is bound here explicitly; the same family as the
   [equiv] shadowing recorded in Instance/FdVect.v. *)
#[local] Notation num := Frac.num.

(** * The field of quotients as a universal arrow, and Mac Lane's
      non-example

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §III.1 (Universal Arrows), printed pp. 55-56
    [maclane:III.1:construction2]: for an integral domain D, the field
    of quotients Q(D) together with the embedding n ↦ n/1 is a
    universal arrow from D to the forgetful functor from fields to
    integral domains — PROVIDED the domain category is taken to have
    monomorphisms as its arrows.  Mac Lane's accompanying remark is the
    half with the content: over the category of integral domains and
    ALL homomorphisms there is no universal arrow from ℤ at all,
    because the reductions ℤ → ℤ/pℤ cannot be routed through one fixed
    field.
    nLab: https://ncatlab.org/nlab/show/field+of+fractions
    nLab: https://ncatlab.org/nlab/show/universal+construction

    The construction is the oldest universal property in algebra —
    Grassmann and Hamilton built ℚ from ℤ this way long before anyone
    called it universal — and it is the example by which the notion is
    usually first motivated, precisely because the wrong choice of
    morphisms destroys it.  That sensitivity is the point: the
    extension of f : D → K to Q(D) sends n/d to f(n)·(f d)⁻¹, so it
    needs f d invertible for every d ≉ 0, i.e. it needs f to REFLECT
    zero, which for a ring homomorphism is injectivity.  A homomorphism
    that collapses a nonzero denominator supports no such map, and the
    standard repair — restrict the domain category to monomorphisms —
    is what Mac Lane's Dom_m records.  Both halves are
    delivered here, against the SAME category of fields, so that the
    contrast is a theorem and not a change of subject
    ([frac_universal_over_monos_not_over_all]).

    WHAT IS ALREADY IN TREE, and a CORRECTION.  The issue's "Current
    state" paragraph says of this material "Absent … No category of
    fields or integral domains exists, and no ℤ-as-initial-ring
    machinery for the non-existence example."  That is false on every
    count, as the issue's own trailing QA-audit block records, and the
    correction is repeated here because a header is where a reader
    looks.  Already present and REUSED rather than rebuilt:
    Instance/Rng/Frac.v's [IntDom] — integral domains with injective
    ring homomorphisms, which is Mac Lane's Dom_m modulo the
    monic-implies-injective converse that Instance/Rng/Frac.v defers
    pending the free ring ℤ[x] (injective-implies-monic IS proved
    there, as [DomHom_monic]) — with [DomObject],
    [DomHom], the fraction ring [FracRing], the embedding [frac_embed]
    and its injectivity [frac_embed_inj]; Instance/Field.v's [Field]
    with [Field_Rng], [Field_Forget], the ¬¬-stability analysis, ℚ and
    F₂; and Instance/Rng.v's [ZtoQ].  Nothing of that is re-derived
    below.  Instance/Rng.v's [Rng_Initial_Z] refutes the issue's
    "no ℤ-as-initial-ring machinery" clause by existing, but it is not
    used: the non-existence proof names the two homomorphisms out of ℤ
    concretely rather than obtaining them from initiality.

    WHAT IS NEW HERE.  The forgetful functor from fields into a
    category of integral domains — no such functor existed, into either
    [IntDom] or the [Dom] built below; the universal property and its
    packaging as a [UniversalArrow]; and the whole non-existence half,
    including [Dom] itself and the reduction ℤ → F₂ that lives in it.

    THE FORGETFUL FUNCTOR, and the first hypothesis.  A field is an
    integral domain unconditionally ([field_dom]): cancellation follows
    from invertibility, and the guard on [finv_l] is a NEGATION, which
    is exactly the hypothesis [dom_cancel] already carries, so no
    decision procedure is consulted.  Morphisms are where the price is
    paid.  [DomHom] carries injectivity as DATA in the strict form
    f a ≈ f b → a ≈ b, and Instance/Field.v has already measured how
    much of that is constructively available: the unconditional
    strength is [field_hom_distinct], a ≉ b → f a ≉ f b, whose
    contrapositive yields only ¬¬(a ≈ b), and the strict form is
    [field_stable_at_zero_suffices], which consumes ¬¬-stability of the
    SOURCE at zero.  So the functor is delivered in two shapes:
    [StableField_IntDom], hypothesis-free, on the full subcategory
    [StableField] of fields carrying [FieldStableAtZero] as an object
    datum; and [Field_IntDom], on all of [Field], taking the blanket
    stability assumption as an explicit argument in the shape
    Instance/Field.v's [field_every_monic] uses.  Whether some other
    construction gives an unconditional functor on all of [Field] is
    NOT settled here and is not asserted either way — the same
    discipline Instance/Field.v follows in declining to claim that some
    field has unstable equality.  This is ARGUED from what the tree
    proves, not proved to be necessary.  What IS proved is that no such
    hypothesis is needed on the [Dom] side: [Field_Dom] is
    unconditional, since a plain ring homomorphism is asked for nothing.

    THE UNIVERSAL PROPERTY IS UNCONDITIONAL.  [frac_ump] states, for an
    ARBITRARY integral domain D and an ARBITRARY field K, that every
    [IntDom]-morphism D → K extends uniquely along the embedding to a
    ring homomorphism Q(D) → K.  No stability, no decidability, no
    choice, and no field structure on the fractions appears in it.  The
    extension is [frac_extend], its triangle [frac_extend_embed], and
    the uniqueness [frac_extend_unique] — the latter through
    [frac_embed_den], the identity saying that d/1 · n/d ≈ n/1, so that
    the extension is forced without ever asking a competitor to
    preserve inverses.  Injectivity is spent in EXACTLY ONE PLACE,
    [frac_hom_den_nonzero]: a denominator is apart from zero, and its
    image must be too, or it could not be inverted.  That single lemma
    is Mac Lane's whole reason for taking monomorphisms.

    THE SECOND HYPOTHESIS, and it is not Mac Lane's either.  Naming
    Q(D) as an OBJECT of the field category requires a [FieldObject],
    whose inverse operation [finv] is TOTAL — totality being forced by
    the setoid discipline, since a partial operation is not a setoid
    map (Instance/FdVect.v's own header says so).  A total reciprocal
    on fractions must decide what to return at zero, and that decision
    is [DomZeroDec]: ≈-comparison with zero is decidable in D.  It is
    stated at zero rather than pairwise, following [FieldStableAtZero]
    in locating the obstruction, and the two are inter-derivable
    ([dom_zero_dec_eq_dec] and [dom_eq_dec_zero_dec]).  It subsumes the
    first hypothesis on the fractions: decidability gives stability, so
    [FracField] lands in [StableField] with nothing further to check.
    Classically neither hypothesis is visible; both are disclosed here
    rather than absorbed, and ℤ discharges the second by [Z.eq_dec].

    THE NON-EXAMPLE, and how far it reaches.  [Dom] is built here with
    all ring homomorphisms as arrows, and [IntDom_Dom] includes [IntDom]
    into it as a wide, faithful, NOT full subcategory —
    [IntDom_Dom_not_Full] proves the non-fullness that
    Instance/Rng/Frac.v left unstated for want of a counterexample
    object.  The witness is reduction mod 2, which needs NO
    quotient-ring theory: F₂ is already an object, and the reduction is
    [Z.odd], whose stdlib laws [Z.odd_add] and [Z.odd_mul] ARE the two
    homomorphism clauses against F₂'s [xorb] and [andb].  It is not
    injective ([ZtoF2_not_injective]), and more sharply [IntDom] has NO
    morphism from ℤ to F₂ whatsoever ([no_DomHom_Z_F2]) — so the arrow
    that breaks the universal property is invisible to the category in
    which the universal property holds.  ONE PRIME SUFFICES, and no
    case split on the characteristic is needed: [no_field_over_Q_and_F2]
    observes that a homomorphism to ℚ forces 1 + 1 to be apart from
    zero (a NEGATIVE fact, delivered outright), whereupon
    [field_hom_nonzero] refutes a homomorphism to F₂, where 1 + 1
    vanishes.  Mac Lane's ℤ/pℤ family is therefore not needed and
    neither is a second prime; the separating pair is ℚ against F₂,
    already Instance/Field.v's pair for the absence of initial and
    terminal objects.  The refutation consumes only the EXISTENCE of
    the factorizations — uniqueness is never used, and neither is the
    universal arrow ℤ → K itself, which is why it also holds in the
    weaker form [no_field_maps_to_all_fields].  It is stated in both
    encodings ([UniversalArrow] and [AUniversalArrow]) and over BOTH
    field categories, so the obstruction is not an artifact of [Field]
    being larger than [StableField]: ℚ and F₂ are both stable, so both
    survive the restriction.

    STRENGTHS, measured.  At Leibniz equality by [eq_refl] — the
    convertibility exception, exhibited where it holds: the object and
    morphism components of [StableField_IntDom_Dom_obj] and
    [StableField_IntDom_Dom_map]; the object component of
    [Field_IntDom_agrees_obj]; and the two computations
    [frac_extend_Z_half] and [frac_extend_Z_three], where the extension
    of ℤ ↪ ℚ carries 1/2 to the rational 1#2 ON THE NOSE.  Strictness
    was attempted first and REJECTED in one place:
    [Field_IntDom_agrees_map] holds only up to ≈, because the two
    [DomHom]s carry the same underlying map but different injectivity
    proofs, and [DomHom] carries that proof as a field.  Both
    boundaries are guarded, not merely measured, by negative probes in
    Test/ProbeFieldFrac.v, each paired with a positive control.

    NON-VACUITY.  Q(ℤ) is an actual object ([Frac_Z]), ℤ ↪ ℚ an actual
    [IntDom]-morphism ([ZtoQ_Dom]), the extension computes as above,
    and the embedding is NOT onto — [frac_embed_Z_not_surjective] shows
    1/2 is not n/1 for any integer n, so the fraction field is strictly
    larger than the image of D and the universal arrow is not a
    degenerate one.

    WHAT IS NOT DELIVERED.  No isomorphism Q(ℤ) ≅ ℚ is proved; the
    computations above relate the two through the extension, not by an
    equivalence of objects.  [Dom] is defined here rather than beside
    [IntDom] in Instance/Rng/Frac.v, since it exists only to state the
    non-example.  Fullness of [IntDom_Incl] into [CRng] — a DIFFERENT
    functor from [IntDom_Dom], and the one Instance/Rng/Frac.v actually
    left open — is refuted separately as [IntDom_Incl_not_Full], on the
    same F₂ witness; the two statements are about different functors
    and neither implies the other here.  And no quotient rings are
    built: F₂ is used as the positive-characteristic witness precisely
    so that none are needed, which is exactly what makes the
    [IntDom_Incl] deferral discharge-able, since that deferral was
    conditioned on there being no counterexample OBJECT and a field is
    a domain.

    AXIOMS.  Everything here is axiom-free, counted the way
    docs/AXIOMS.md counts: all 99 constants the module declares — the
    69 source-level definitions and theorems and the 30 [Program]
    obligations, which no [.glob] sweep sees — report "Closed under the
    global context", including both principal artifacts,
    [frac_universal] and [no_universal_arrow_Z_Dom].  The
    arithmetic is Theory/Algebra/Rig.v's, the concrete carriers are
    stdlib [Z], [bool] and [QArith], and nothing here touches the
    reals. *)

(** ** Every field is an integral domain *)

(* Cancellation is where the field structure is spent, and it is spent
   unconditionally: the guard on [finv_l] is exactly the hypothesis
   [dom_cancel] already carries, so c ≉ 0 licenses inverting c with no
   decision procedure consulted.  Commutativity and 1 ≉ 0 transfer
   verbatim. *)
Program Definition field_dom (F : FieldObject) : DomObject := {|
  dom_ring       := field_ring F;
  dom_comm       := field_comm F;
  dom_nontrivial := field_one_neq_zero F
|}.
Next Obligation.
  intros F a b c Hc H.
  transitivity (rig_mul F (rig_mul F a c) (finv F c)).
  - rewrite rig_mul_assoc.
    rewrite (finv_r F c Hc).
    symmetry; apply rig_mul_one_r.
  - rewrite H.
    rewrite rig_mul_assoc.
    rewrite (finv_r F c Hc).
    apply rig_mul_one_r.
Qed.

(** ** The category of integral domains and ALL homomorphisms *)

(* Mac Lane's [Dom], as against Instance/Rng/Frac.v's [IntDom], which is
   his [Dom_m].  Same objects; the morphisms here are the plain ring
   homomorphisms, with no injectivity clause.  The two categories are
   what the whole file is about: the universal arrow exists over
   [IntDom] and does not exist over [Dom]. *)
Program Definition Dom : Category := {|
  obj     := DomObject;
  hom     := fun D E => RigHom (dom_ring D) (dom_ring E);
  homset  := fun D E => @RigHom_Setoid (dom_ring D) (dom_ring E);
  id      := fun D => @rig_hom_id (dom_ring D);
  compose := fun _ _ _ f g => rig_hom_compose f g;

  compose_respects := fun _ _ _ => @rig_hom_compose_respects _ _ _
|}.
Next Obligation. intros D E f a; simpl; reflexivity. Qed.
Next Obligation. intros D E f a; simpl; reflexivity. Qed.
Next Obligation. intros D E F G f g h a; simpl; reflexivity. Qed.
Next Obligation. intros D E F G f g h a; simpl; reflexivity. Qed.

(* [IntDom] sits inside [Dom] as a WIDE subcategory: identical on
   objects, forgetting the injectivity datum on morphisms.  It is not
   full — proved below as [IntDom_Dom_not_Full], on the witness
   [no_DomHom_Z_F2]: the reduction ℤ → F₂ is a morphism of [Dom]
   between two objects of [IntDom] that no morphism of [IntDom] can
   carry. *)
Program Definition IntDom_Dom : IntDom ⟶ Dom := {|
  fobj := fun D => D;
  fmap := fun _ _ f => dom_map f
|}.
Next Obligation. intros D E f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros D a; simpl; reflexivity. Qed.
Next Obligation. intros D E F f g a; simpl; reflexivity. Qed.

#[export] Instance IntDom_Dom_Faithful : Faithful IntDom_Dom.
Proof. constructor; intros D E f g H x; exact (H x). Qed.

(** ** The forgetful functor into ALL homomorphisms, unconditionally *)

(* Every field is a domain and every ring homomorphism is a ring
   homomorphism, so this functor costs nothing.  Contrast
   [StableField_IntDom] below, which is the same assignment on objects
   and needs a hypothesis on morphisms; the difference between the two
   is exactly the injectivity clause of [DomHom]. *)
Program Definition Field_Dom : Field ⟶ Dom := {|
  fobj := field_dom;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Dom_Faithful : Faithful Field_Dom.
Proof. constructor; intros F K f g H x; exact (H x). Qed.

(** ** Fields whose equality is ¬¬-stable *)

(* The selection predicate is Instance/Field.v's [FieldStableAtZero],
   the LOCATED form of stability: ≈ is ¬¬-stable at zero.  That file
   proves it inter-derivable with the pairwise [FieldStable]
   ([field_stable_stable_at_zero], [field_stable_at_zero_stable]), so
   nothing is lost by selecting on the weaker-looking one, and it is
   what [field_stable_at_zero_suffices] consumes directly. *)
Definition StableField_Sub : Subcategory Field :=
  @Build_Subcategory Field
    (fun F : FieldObject => FieldStableAtZero F)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition StableField : Category := Sub Field StableField_Sub.

(* Full: every field homomorphism between selected objects is selected. *)
Lemma StableField_Full :
  Category.Construction.Subcategory.Full Field StableField_Sub.
Proof. intros F K oF oK g; exact I. Qed.

(* Decidable equality gives stability, so both fields of the tree are
   objects.  ℚ and F₂ are the two witnesses Instance/Field.v uses to
   separate characteristics, and they are the two witnesses the
   non-existence theorem below uses as well. *)
Definition StableField_of_dec (F : FieldObject)
  (dec : ∀ a b : carrier (rig_setoid F), (a ≈ b) + (a ≈ b → False)) :
  StableField :=
  (F; field_stable_stable_at_zero F (field_dec_stable F dec)).

Definition Q_StableField : StableField := StableField_of_dec _ Q_Field_dec.

Definition F2_StableField : StableField := StableField_of_dec _ F2_Field_dec.

(** ** The forgetful functor into the category of MONOMORPHISMS *)

(* Deliverable one, and the reason the objects carry a stability datum.
   To land in [IntDom] a field homomorphism must supply [DomHom]'s
   [dom_map_inj], the STRICT cancellation form f a ≈ f b → a ≈ b.
   Instance/Field.v measures exactly how much of that is available: the
   unconditional strength is [field_hom_distinct], a ≉ b → f a ≉ f b,
   whose contrapositive gives only ¬¬(a ≈ b); the strict form is
   [field_stable_at_zero_suffices] and it consumes ¬¬-stability of the
   SOURCE at zero.  So the injectivity datum comes from the object's own
   stability field, and no classical ideal argument and no [frac]-style
   cancellation can replace it — see the header. *)
Program Definition StableField_IntDom : StableField ⟶ IntDom := {|
  fobj := fun F => field_dom `1 F;
  fmap := fun F K f =>
    {| dom_map     := `1 f;
       dom_map_inj := field_stable_at_zero_suffices `1 f `2 F |}
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance StableField_IntDom_Faithful : Faithful StableField_IntDom.
Proof. constructor; intros F K f g H x; exact (H x). Qed.

(* What a forgetful functor on ALL of [Field] costs, in the shape
   Instance/Field.v's [field_every_monic] uses: the blanket stability
   assumption, taken as an explicit argument rather than smuggled.
   Restricting to [StableField] instead is what makes
   [StableField_IntDom] hypothesis-free.  The two agree on the selected
   objects, and the strengths of the two agreements DIFFER: the object
   component is [eq_refl], the morphism component only ≈ — the two
   [DomHom]s carry the same underlying map but different injectivity
   proofs ([stab F] against F's own datum), and [DomHom] carries that
   proof as a field, so they are distinct records. *)
Program Definition Field_IntDom
  (stab : ∀ F : FieldObject, FieldStableAtZero F) : Field ⟶ IntDom := {|
  fobj := field_dom;
  fmap := fun F K f =>
    Build_DomHom (field_dom F) (field_dom K) f
      (field_stable_at_zero_suffices f (stab F))
|}.
Next Obligation. intros stab F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros stab F a; simpl; reflexivity. Qed.
Next Obligation. intros stab F K T f g a; simpl; reflexivity. Qed.

Example Field_IntDom_agrees_obj
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F : StableField) :
  Field_IntDom stab (Incl Field StableField_Sub F) = StableField_IntDom F
  := eq_refl.

Example Field_IntDom_agrees_map
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    ≈ fmap[StableField_IntDom] f.
Proof. intro a; simpl; reflexivity. Qed.

(* The same assignment read into [Dom] instead, where no hypothesis is
   needed; the two agree, in that composing with the wide inclusion
   recovers [Field_Dom] on the selected objects.  BOTH components hold
   at Leibniz equality by [eq_refl] — the convertibility exception,
   measured rather than assumed: [IntDom_Dom] forgets exactly the
   injectivity field that [StableField_IntDom] supplied, so the
   composite's morphism component reduces to `1 f on the nose.
   Contrast [Field_IntDom_agrees_map] below, where the same shape of
   comparison is NOT strict. *)
Definition StableField_Dom : StableField ⟶ Dom :=
  Field_Dom ◯ Incl Field StableField_Sub.

Example StableField_IntDom_Dom_obj (F : StableField) :
  IntDom_Dom (StableField_IntDom F) = StableField_Dom F := eq_refl.

Example StableField_IntDom_Dom_map (F K : StableField) (f : F ~{StableField}~> K) :
  fmap[IntDom_Dom] (fmap[StableField_IntDom] f) = fmap[StableField_Dom] f
  := eq_refl.

(** ** Division in a field *)

(* A small kit, mirroring Instance/Rng/Frac.v's shuffle kit one layer
   up: everything below is "clear the denominator and shuffle".  Every
   lemma carries the nonzeroness hypotheses that make [finv] meaningful,
   and none consults a decision procedure — the hypotheses are
   NEGATIONS, which is exactly what [finv_l] asks for. *)

Section FieldArith.

Context (K : FieldObject).

Local Notation k0 := (rig_zero K).
Local Notation k1 := (rig_one K).
Local Infix "*" := (rig_mul K).
Local Infix "+" := (rig_add K).
Local Notation "/ x" := (finv K x).

Lemma kmulC (a b : carrier (rig_setoid K)) : a * b ≈ b * a.
Proof. apply field_comm. Qed.

Lemma kmulA (a b c : carrier (rig_setoid K)) : (a * b) * c ≈ a * (b * c).
Proof. apply rig_mul_assoc. Qed.

Lemma kmul_swap_r (a b c : carrier (rig_setoid K)) :
  (a * b) * c ≈ (a * c) * b.
Proof.
  rewrite kmulA, (kmulC b c), <- kmulA; reflexivity.
Qed.

Lemma kmul4_shuffle1 (a b c d : carrier (rig_setoid K)) :
  (a * b) * (c * d) ≈ (a * c) * (b * d).
Proof.
  rewrite kmulA, <- (kmulA b c d), (kmulC b c), (kmulA c b d), <- kmulA.
  reflexivity.
Qed.

(* Read off the domain structure of K rather than reproved: a field is
   an integral domain, and [dom_mul_nonzero] is that domain's. *)
Lemma field_mul_nonzero (a b : carrier (rig_setoid K)) :
  (a ≈ k0 → False) → (b ≈ k0 → False) → a * b ≈ k0 → False.
Proof. exact (dom_mul_nonzero (field_dom K) a b). Qed.

Lemma finv_one : / k1 ≈ k1.
Proof.
  rewrite <- (rig_mul_one_r K (/ k1)).
  apply finv_l, (field_one_neq_zero K).
Qed.

(* (a/b)·b ≈ a. *)
Lemma field_div_elim (a b : carrier (rig_setoid K)) (Hb : b ≈ k0 → False) :
  (a * / b) * b ≈ a.
Proof.
  rewrite kmulA.
  rewrite (kmulC (/ b) b).
  rewrite (finv_r K b Hb).
  apply rig_mul_one_r.
Qed.

(* To prove q ≈ a/b it is enough to clear the denominator. *)
Lemma field_div_intro (q a b : carrier (rig_setoid K)) (Hb : b ≈ k0 → False) :
  q * b ≈ a → q ≈ a * / b.
Proof.
  intro H.
  transitivity ((q * b) * / b).
  - rewrite kmulA, (finv_r K b Hb).
    symmetry; apply rig_mul_one_r.
  - now rewrite H.
Qed.

(* Cross-multiplication decides equality of quotients. *)
Lemma field_div_eq (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  a * d ≈ c * b → a * / b ≈ c * / d.
Proof.
  intro H.
  apply (field_div_intro _ _ _ Hd).
  rewrite kmul_swap_r.
  rewrite H.
  rewrite kmulA.
  rewrite (finv_r K b Hb).
  apply rig_mul_one_r.
Qed.

Lemma field_div_add (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  a * / b + c * / d ≈ (a * d + c * b) * / (b * d).
Proof.
  apply (field_div_intro _ _ _ (field_mul_nonzero b d Hb Hd)).
  rewrite rig_distr_r.
  apply rig_add_respects.
  - rewrite <- kmulA.
    rewrite (field_div_elim a b Hb).
    reflexivity.
  - rewrite (kmulC b d), <- kmulA.
    rewrite (field_div_elim c d Hd).
    reflexivity.
Qed.

Lemma field_div_mul (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  (a * / b) * (c * / d) ≈ (a * c) * / (b * d).
Proof.
  apply (field_div_intro _ _ _ (field_mul_nonzero b d Hb Hd)).
  rewrite kmul4_shuffle1.
  rewrite (field_div_elim a b Hb).
  rewrite (field_div_elim c d Hd).
  reflexivity.
Qed.

End FieldArith.

(** ** The extension of an injective homomorphism to the fractions *)

(* This section is UNCONDITIONAL: [D] is an arbitrary integral domain,
   [K] an arbitrary field, and the only datum is an [IntDom]-morphism
   from D into K, i.e. an injective ring homomorphism.  No stability,
   no decidability, no choice, and no field structure on the fractions
   is needed to state or prove any of it. *)

Section FracExtension.

Context (D : DomObject).
Context (K : FieldObject).
Context (f : DomHom D (field_dom K)).

(* THE ONE PLACE INJECTIVITY IS SPENT.  A denominator is apart from
   zero; its image has to be apart from zero too, or it could not be
   inverted — and that step is exactly the reflection of zero, which is
   what [dom_map_inj] supplies and what a general ring homomorphism does
   not.  This is why the domain category has monomorphisms only. *)
Lemma frac_hom_den_nonzero (x : frac_carrier D) :
  dom_map f (den D x) ≈ rig_zero K → False.
Proof.
  intro H.
  apply (den_nonzero D x).
  apply (dom_map_inj f).
  rewrite H.
  symmetry.
  apply (rig_map_zero (dom_map f)).
Qed.

(* n/d ↦ f n · (f d)⁻¹. *)
Definition frac_extend_map (x : frac_carrier D) : carrier (rig_setoid K) :=
  rig_mul K (dom_map f (num D x)) (finv K (dom_map f (den D x))).

Program Definition frac_extend : RigHom (FracRing D) (field_ring K) := {|
  rig_map := {| morphism := frac_extend_map |}
|}.
Next Obligation.
  intros x y Hxy; unfold frac_extend_map.
  apply (field_div_eq K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
  rewrite <- !(rig_map_mul (dom_map f)).
  exact (proper_morphism (rig_map (dom_map f)) _ _ Hxy).
Qed.
Next Obligation.
  unfold frac_extend_map, frac_zero, Frac.num, Frac.den, mk_frac; simpl.
  rewrite (rig_map_zero (dom_map f)).
  apply rig_mul_zero_l.
Qed.
Next Obligation.
  intros x y.
  unfold frac_extend_map, frac_add, Frac.num, Frac.den, mk_frac; simpl.
  rewrite (rig_map_add (dom_map f)).
  rewrite !(rig_map_mul (dom_map f)).
  symmetry.
  apply (field_div_add K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
Qed.
Next Obligation.
  unfold frac_extend_map, frac_one, Frac.num, Frac.den, mk_frac; simpl.
  rewrite !(rig_map_one (dom_map f)).
  apply finv_r, (field_one_neq_zero K).
Qed.
Next Obligation.
  intros x y.
  unfold frac_extend_map, frac_mul, Frac.num, Frac.den, mk_frac; simpl.
  rewrite !(rig_map_mul (dom_map f)).
  symmetry.
  apply (field_div_mul K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
Qed.

(* The triangle: the extension restricts along the embedding to f. *)
Lemma frac_extend_embed (a : carrier (rig_setoid D)) :
  frac_extend (frac_embed D a) ≈ dom_map f a.
Proof.
  unfold frac_extend, frac_extend_map, frac_embed, Frac.num, Frac.den, mk_frac;
    simpl.
  rewrite (rig_map_one (dom_map f)).
  rewrite (finv_one K).

  apply rig_mul_one_r.
Qed.

(* Every fraction is its numerator divided by its denominator, said
   inside the fraction ring: multiplying n/d by the image of d gives the
   image of n.  This is what forces the extension to be what it is, and
   it needs nothing of g beyond being a ring homomorphism — in
   particular no preservation of inverses. *)
Lemma frac_embed_den (x : frac_carrier D) :
  rig_mul (FracRing D) (frac_embed D (den D x)) x ≈ frac_embed D (num D x).
Proof.
  simpl; unfold frac_eq, frac_mul, Frac.num, Frac.den, mk_frac; simpl.
  rewrite rig_mul_one_r.
  rewrite rig_mul_one_l.
  apply dom_comm.
Qed.

Lemma frac_extend_unique (g : RigHom (FracRing D) (field_ring K))
  (Hg : ∀ a, rig_map g (frac_embed D a) ≈ dom_map f a) (x : frac_carrier D) :
  rig_map g x ≈ frac_extend x.
Proof.
  (* g of the identity above, with the embedding legs replaced by f *)
  assert (Hgx : rig_mul K (dom_map f (den D x)) (rig_map g x)
                  ≈ dom_map f (num D x)).
  { transitivity (rig_map g (rig_mul (FracRing D) (frac_embed D (den D x)) x)).
    - rewrite (rig_map_mul g).
      rewrite (Hg (den D x)).
      reflexivity.
    - rewrite (proper_morphism (rig_map g) _ _ (frac_embed_den x)).
      apply Hg. }
  unfold frac_extend, frac_extend_map; simpl.
  apply (field_div_intro K _ _ _ (frac_hom_den_nonzero x)).
  rewrite (field_comm K).
  exact Hgx.
Qed.

End FracExtension.

(** ** The universal mapping property, over EVERY field *)

(* The mathematical content of Mac Lane's construction, and it is
   unconditional: no stability of K, no decidability of D, no field
   structure on the fractions.  Everything the packaging below adds is
   bookkeeping needed to name [FracRing D] as an OBJECT of a category of
   fields; the property itself is this. *)
Theorem frac_ump (D : DomObject) (K : FieldObject) (f : DomHom D (field_dom K)) :
  ∃! g : RigHom (FracRing D) (field_ring K),
    ∀ a : carrier (rig_setoid D), rig_map g (frac_embed D a) ≈ dom_map f a.
Proof.
  unshelve esplit.
  - exact (frac_extend D K f).
  - exact (frac_extend_embed D K f).
  - intros g Hg x; symmetry; exact (frac_extend_unique D K f g Hg x).
Qed.

(** ** Apartness from the zero fraction *)

Lemma frac_eq_zero (D : DomObject) (x : frac_carrier D) :
  frac_eq D x (frac_zero D) → num D x ≈ rig_zero D.
Proof.
  unfold frac_eq, frac_zero, Frac.num, Frac.den, mk_frac; simpl; intro H.
  rewrite <- (rig_mul_one_r D (fst `1 x)).
  rewrite H.
  apply rig_mul_zero_l.
Qed.

Lemma frac_zero_eq (D : DomObject) (x : frac_carrier D) :
  num D x ≈ rig_zero D → frac_eq D x (frac_zero D).
Proof.
  unfold frac_eq, frac_zero, Frac.num, Frac.den, mk_frac; simpl; intro H.
  rewrite rig_mul_one_r.
  rewrite H.
  symmetry; apply rig_mul_zero_l.
Qed.

(** ** Testing for zero, and the fractions as an OBJECT of [Field] *)

(* THE ONE HYPOTHESIS OF THIS PACKAGING STEP — the file's second, the
   first being the ¬¬-stability carried by [StableField]'s objects —
   and it is not Mac Lane's either: it is
   the price of Instance/FdVect.v's [FieldObject], whose inverse
   operation [finv] is TOTAL.  Totality is forced by the setoid
   discipline (a partial operation is not a setoid map), and a total
   reciprocal on fractions has to decide which value to return at zero;
   that decision is exactly this.  Stated at zero, following
   Instance/Field.v's [FieldStableAtZero] in locating the obstruction
   rather than assuming the pairwise form — and, as there, the two are
   inter-derivable ([dom_zero_dec_eq_dec] and its converse), the passage
   through a − b being the whole argument. *)
Definition DomZeroDec (D : DomObject) : Type :=
  ∀ a : carrier (rig_setoid D),
    (a ≈ rig_zero D) + (a ≈ rig_zero D → False).

Definition DomEqDec (D : DomObject) : Type :=
  ∀ a b : carrier (rig_setoid D), (a ≈ b) + (a ≈ b → False).

Definition dom_eq_dec_zero_dec (D : DomObject) (dec : DomEqDec D) :
  DomZeroDec D := fun a => dec a (rig_zero D).

Lemma dom_zero_dec_eq_dec (D : DomObject) (dec : DomZeroDec D) : DomEqDec D.
Proof.
  intros a b.
  destruct (dec (rig_add D a (ring_neg D b))) as [H | H].
  - left; exact (ring_sub_zero (dom_ring D) a b H).
  - right; intro Hab; apply H; exact (ring_zero_sub (dom_ring D) a b Hab).
Qed.

Section FracField.

Context (D : DomObject).
Context (dec : DomZeroDec D).

Definition frac_zero_dec (x : frac_carrier D) :
  (frac_eq D x (frac_zero D)) + (frac_eq D x (frac_zero D) → False) :=
  match dec (num D x) with
  | inl H => inl (frac_zero_eq D x H)
  | inr H => inr (fun Heq => H (frac_eq_zero D x Heq))
  end.

(* The reciprocal: flip the pair when the numerator is apart from zero,
   and return the junk value 0 otherwise — which is precisely the junk
   [FieldObject] allows, constrained by nothing but [finv_respects]. *)
Definition frac_finv (x : frac_carrier D) : frac_carrier D :=
  match dec (num D x) with
  | inl _  => frac_zero D
  | inr Hn => mk_frac D (den D x) (num D x) Hn
  end.

Program Definition FracField : FieldObject := {|
  field_ring         := FracRing D;
  field_comm         := FracRing_comm D;
  finv               := frac_finv
|}.
Next Obligation.
  (* 1 ≉ 0 in the fractions, since 1 ≉ 0 in D.  The hypothesis is a
     cross-multiplication equation by conversion, and is read as one. *)
  intro H.
  assert (H' : rig_mul D (rig_one D) (rig_one D)
                 ≈ rig_mul D (rig_zero D) (rig_one D)) by exact H.
  apply (dom_nontrivial D).
  rewrite <- (rig_mul_one_r D (rig_one D)).
  rewrite H'.
  apply rig_mul_zero_l.
Qed.
Next Obligation.
  (* [finv] respects ≈.  The two mixed cases are impossible — a fraction
     with vanishing numerator cannot be equivalent to one whose
     numerator is apart from zero — and the surviving case is a
     commutation.  Each goal is read as its cross-multiplication
     equation by conversion. *)
  intros x y Hxy.
  assert (Hxy' : rig_mul D (num D x) (den D y) ≈ rig_mul D (num D y) (den D x))
    by exact Hxy.
  unfold frac_finv.
  destruct (dec (num D x)) as [Hx | Hx]; destruct (dec (num D y)) as [Hy | Hy].
  - reflexivity.
  - exfalso; apply Hy.
    apply (dom_cancel D _ _ (den D x) (den_nonzero D x)).
    rewrite rig_mul_zero_l.
    rewrite <- Hxy'.
    rewrite Hx.
    apply rig_mul_zero_l.
  - exfalso; apply Hx.
    apply (dom_cancel D _ _ (den D y) (den_nonzero D y)).
    rewrite rig_mul_zero_l.
    rewrite Hxy'.
    rewrite Hy.
    apply rig_mul_zero_l.
  - assert (Hres : rig_mul D (den D x) (num D y)
                     ≈ rig_mul D (den D y) (num D x)).
    { rewrite (dom_comm D (den D x) (num D y)).
      rewrite <- Hxy'.
      apply dom_comm. }
    exact Hres.
Qed.
Next Obligation.
  (* [finv_l] away from zero: the numerator cannot vanish there, and
     flipping the pair back gives 1/1. *)
  intros x Hx; unfold frac_finv.
  destruct (dec (num D x)) as [Hn | Hn].
  - destruct (Hx (frac_zero_eq D x Hn)).
  - assert (Hres : rig_mul D (rig_mul D (den D x) (num D x)) (rig_one D)
                     ≈ rig_mul D (rig_one D) (rig_mul D (num D x) (den D x))).
    { rewrite rig_mul_one_r, rig_mul_one_l; apply dom_comm. }
    exact Hres.
Qed.

(* Decidability at zero passes to the fractions, hence so does
   ¬¬-stability, so [FracField] is an object of [StableField]. *)
Definition FracField_stable : FieldStableAtZero FracField :=
  fun a Hnn =>
    match frac_zero_dec a with
    | inl H => H
    | inr H => match Hnn H with end
    end.

Definition FracStableField : StableField := (FracField; FracField_stable).

(* The unit: n ↦ n/1, with the injectivity datum [IntDom] demands. *)
Definition frac_unit : D ~{IntDom}~> StableField_IntDom FracStableField :=
  Build_DomHom D (field_dom FracField) (frac_embed D) (frac_embed_inj D).

(** ** ⟨Q(D), n ↦ n/1⟩ is a universal arrow *)

Program Instance frac_universal_arrow :
  AUniversalArrow (D : IntDom) StableField_IntDom FracStableField := {|
  universal_arrow := frac_unit
|}.
Next Obligation.
  intros K f.
  unshelve esplit.
  - exact (frac_extend D `1 K f; I).
  - exact (frac_extend_embed D `1 K f).
  - intros g Hg x; symmetry; exact (frac_extend_unique D `1 K f `1 g Hg x).
Qed.

(* The same, in the comma-category packaging: an initial object of
   =(D) ↓ U.  Note the reversed orientation of the factorization
   equation in [universal_arrow_from_UMP], whence the [symmetry]s. *)
Definition frac_universal : UniversalArrow (D : IntDom) StableField_IntDom.
Proof using D dec.
  unshelve eapply (universal_arrow_from_UMP (D : IntDom) StableField_IntDom
                     FracStableField frac_unit).
  intros K f.
  unshelve esplit.
  - exact (frac_extend D `1 K f; I).
  - intro x; symmetry; exact (frac_extend_embed D `1 K f x).
  - intros g Hg x.
    assert (Hg' : ∀ a : carrier (rig_setoid D),
               rig_map `1 g (frac_embed D a) ≈ dom_map f a).
    { intro a; symmetry; exact (Hg a). }
    symmetry; exact (frac_extend_unique D `1 K f `1 g Hg' x).
Defined.

End FracField.

(** ** Reduction mod 2, the morphism [IntDom] does not have *)

(* No quotient-ring theory is needed to name ℤ → ℤ/2ℤ: F₂ is already an
   object (Instance/Field.v), and reduction mod 2 is [Z.odd], whose
   stdlib laws [Z.odd_add] and [Z.odd_mul] ARE the two homomorphism
   clauses against F₂'s [xorb] and [andb].  Preservation of 0 and 1
   holds by computation. *)
(* Only FOUR obligations are generated: both setoids here carry Leibniz
   equality, so [Proper (equiv ==> equiv) Z.odd] is discharged by
   instance resolution during elaboration and never becomes one. *)
Program Definition ZtoF2 : Int_Ring ~{Rng}~> F2_Ring := {|
  rig_map := {| morphism := Z.odd |}
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; apply Z.odd_add. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; apply Z.odd_mul. Qed.

(* It is not injective — 0 and 2 collide — which is exactly why it is a
   morphism of [Dom] and not of [IntDom]. *)
Theorem ZtoF2_not_injective :
  (∀ a b : carrier (rig_setoid Int_Ring),
     rig_map ZtoF2 a ≈ rig_map ZtoF2 b → a ≈ b) → False.
Proof.
  intro Hinj.
  assert (H : (0%Z : carrier (rig_setoid Int_Ring)) ≈ 2%Z)
    by (apply Hinj; reflexivity).
  discriminate H.
Qed.

(* Stronger, and this is the load-bearing statement: [IntDom] has NO
   morphism from ℤ to F₂ whatsoever, not merely that this one is
   excluded.  An injective ring homomorphism would identify 0 with 2,
   since 1 + 1 vanishes in F₂.  So the wide inclusion [IntDom_Dom] is
   not full, and the arrow the non-existence proof below uses is
   invisible to the category the universal arrow lives in. *)
Theorem no_DomHom_Z_F2 : DomHom Int_Dom (field_dom F2_Field) → False.
Proof.
  intro f.
  assert (H : (0%Z : carrier (rig_setoid Int_Dom)) ≈ 2%Z).
  { apply (dom_map_inj f).
    transitivity (rig_zero F2_Field).
    - apply (rig_map_zero (dom_map f)).
    - symmetry.
      transitivity (rig_add F2_Field (rig_map (dom_map f) (rig_one Int_Dom))
                      (rig_map (dom_map f) (rig_one Int_Dom))).
      + apply (rig_map_add (dom_map f) 1%Z 1%Z).
      + rewrite (rig_map_one (dom_map f)).
        exact F2_ftwo_zero. }
  discriminate H.
Qed.

(** ** No field lies over both ℚ and F₂ *)

(* The engine of the non-existence half, and it needs NO case split on
   the characteristic of K: the ℚ-side delivers the NEGATIVE fact
   "1 + 1 is apart from zero in K" outright, and [field_hom_nonzero]
   then refutes the F₂-side.  Same shape as Instance/Field.v's
   [Field_no_initial], and constructive for the same reason — the guard
   on [finv_l] is a negation, so a negative fact is a licence to
   invert. *)
Theorem no_field_over_Q_and_F2 (K : FieldObject)
  (u : RigHom K Q_Field) (v : RigHom K F2_Field) : False.
Proof.
  assert (Hnz : ftwo K ≈ rig_zero K → False).
  { intro H.
    apply Q_ftwo_nonzero.
    rewrite <- (ftwo_map u).
    rewrite H.
    apply (rig_map_zero u). }
  apply (field_hom_nonzero v _ Hnz).
  rewrite (ftwo_map v).
  exact F2_ftwo_zero.
Qed.

(* Restated for the strength the theorems below actually consume: no
   field receives a homomorphism into every field.  Neither the arrow
   out of ℤ nor uniqueness of any factorization plays a part. *)
Corollary no_field_maps_to_all_fields (K : FieldObject)
  (h : ∀ L : FieldObject, RigHom K L) : False.
Proof. exact (no_field_over_Q_and_F2 K (h Q_Field) (h F2_Field)). Qed.

(* The two domain categories are genuinely different, as a theorem
   rather than as an expectation: the inclusion of [IntDom] into [Dom]
   is wide, faithful and NOT full, [ZtoF2] being a [Dom]-morphism
   between two objects of [IntDom] whose [IntDom]-hom-set is empty.
   Instance/Rng/Frac.v left non-fullness of [IntDom_Incl] unstated for
   want of a counterexample object; F₂ supplies one, and that statement
   is discharged below as [IntDom_Incl_not_Full] rather than merely
   gestured at here.  ([Full] is qualified because Construction/Subcategory.v
   exports a different, category-indexed [Full] that shadows the
   functor one — the same collision family as [num] above.) *)
Theorem IntDom_Dom_not_Full :
  Category.Theory.Functor.Full IntDom_Dom → False.
Proof.
  intros [pre _].
  exact (no_DomHom_Z_F2 (@pre Int_Dom (field_dom F2_Field) ZtoF2)).
Qed.

(** And the same witness settles a question Instance/Rng/Frac.v left
    open about a DIFFERENT functor.  That file expects fullness of
    [IntDom_Incl : IntDom ⟶ CRng] to be refutable — a non-injective
    homomorphism between domains has no preimage — but leaves it
    unstated rather than asserted, on the ground that "the tree has no
    quotient rings yet, so no counterexample object is available"
    (Instance/Rng/Frac.v, the comment above [IntDom_Incl]).  The
    counterexample object does not have to be a quotient ring: F₂ is a
    FIELD, hence a domain, and [ZtoF2] is a homomorphism into it that
    [no_DomHom_Z_F2] shows has no [IntDom] preimage.  [CRng]'s
    morphism predicate is trivially [True], so the [CRng] arrow is
    [ZtoF2] paired with [I]. *)
Theorem IntDom_Incl_not_Full :
  Category.Theory.Functor.Full IntDom_Incl → False.
Proof.
  intros [pre _].
  exact (no_DomHom_Z_F2 (@pre Int_Dom (field_dom F2_Field) (existT _ ZtoF2 I))).
Qed.

(** ** maclane:III.1: no universal arrow from ℤ over ALL homomorphisms *)

(* Mac Lane's non-example.  Over [Dom] the reduction ℤ → F₂ is a legal
   arrow, so a universal arrow at ℤ would have to factor it through one
   fixed field K — and K would then lie over both ℚ and F₂.  The
   factorizations are the ONLY thing used; their uniqueness is not, nor
   is the universal arrow ℤ → K itself. *)
Theorem no_universal_arrow_Z_Dom
  (U : UniversalArrow (Int_Dom : Dom) Field_Dom) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact (unique_obj (ump_universal_arrows U
             (ZtoQ : Int_Dom ~{Dom}~> Field_Dom Q_Field))).
  - exact (unique_obj (ump_universal_arrows U
             (ZtoF2 : Int_Dom ~{Dom}~> Field_Dom F2_Field))).
Qed.

Theorem no_auniversal_arrow_Z_Dom (K : Field)
  (U : AUniversalArrow (Int_Dom : Dom) Field_Dom K) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact (unique_obj (@universal_arrow_universal _ _ _ _ _ U Q_Field
             (ZtoQ : Int_Dom ~{Dom}~> Field_Dom Q_Field))).
  - exact (unique_obj (@universal_arrow_universal _ _ _ _ _ U F2_Field
             (ZtoF2 : Int_Dom ~{Dom}~> Field_Dom F2_Field))).
Qed.

(* And the same over the SMALLER field category the positive half uses,
   so the obstruction is not an artifact of [Field] being too large:
   both ℚ and F₂ are stable, so both remain available as targets. *)
Theorem no_universal_arrow_Z_Dom_stable
  (U : UniversalArrow (Int_Dom : Dom) StableField_Dom) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact `1 (unique_obj (ump_universal_arrows U
             (ZtoQ : Int_Dom ~{Dom}~> StableField_Dom Q_StableField))).
  - exact `1 (unique_obj (ump_universal_arrows U
             (ZtoF2 : Int_Dom ~{Dom}~> StableField_Dom F2_StableField))).
Qed.

Theorem no_auniversal_arrow_Z_Dom_stable (K : StableField)
  (U : AUniversalArrow (Int_Dom : Dom) StableField_Dom K) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact `1 (unique_obj (@universal_arrow_universal _ _ _ _ _ U Q_StableField
             (ZtoQ : Int_Dom ~{Dom}~> StableField_Dom Q_StableField))).
  - exact `1 (unique_obj (@universal_arrow_universal _ _ _ _ _ U F2_StableField
             (ZtoF2 : Int_Dom ~{Dom}~> StableField_Dom F2_StableField))).
Qed.

(** ** ℤ: the witness, and the two halves side by side *)

Definition Int_zero_dec : DomZeroDec Int_Dom :=
  fun a => match Z.eq_dec a 0%Z with
           | left H  => inl H
           | right H => inr H
           end.

(* Q(ℤ), as an object of the field category. *)
Definition Frac_Z : StableField := FracStableField Int_Dom Int_zero_dec.

(* The inclusion ℤ ↪ ℚ as a morphism of [IntDom]: [inject_Z] is
   injective because a · 1 ≈ b · 1 in ℤ. *)
Definition ZtoQ_Dom : DomHom Int_Dom (field_dom Q_Field).
Proof.
  refine (Build_DomHom Int_Dom (field_dom Q_Field) ZtoQ _).
  intros a b H.
  assert (H' : (inject_Z a == inject_Z b)%Q) by exact H.
  unfold Qeq, inject_Z in H'; simpl in H'.
  now rewrite !Z.mul_1_r in H'.
Defined.

(* THE CONTRAST, at one object and one field category.  Left: over
   [IntDom], whose morphisms are the monomorphisms, ℤ has a universal
   arrow.  Right: over [Dom], whose morphisms are ALL homomorphisms, NO
   object of the same field category carries one.  The categories of
   fields agree; the objects agree; only the domain-side morphisms
   differ, and that decides the question — which is what Mac Lane's
   remark says. *)
Theorem frac_universal_over_monos_not_over_all :
  AUniversalArrow (Int_Dom : IntDom) StableField_IntDom Frac_Z
  * (∀ K : StableField,
       AUniversalArrow (Int_Dom : Dom) StableField_Dom K → False).
Proof.
  split.
  - exact (frac_universal_arrow Int_Dom Int_zero_dec).
  - exact no_auniversal_arrow_Z_Dom_stable.
Qed.

(** ** The extension computes, and the embedding is not onto *)

(* 1/2 goes to the rational 1/2: the extension is 1 · (2)⁻¹ in ℚ, which
   reduces on the nose.  Leibniz equality, not [Qeq] — the convertibility
   exception, and it is exhibited because it holds. *)
Example frac_extend_Z_half :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 2)%Q := eq_refl.

Example frac_extend_Z_three :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (frac_embed Int_Dom 3%Z) = (3 # 1)%Q := eq_refl.

(* The embedding is not onto: 1/2 is not n/1 for any integer n, since
   that would need 2n = 1.  So the fraction field is strictly larger
   than the image of D and the universal arrow is not a degenerate one. *)
Theorem frac_embed_Z_not_surjective (n : carrier (rig_setoid Int_Dom)) :
  frac_eq Int_Dom (frac_embed Int_Dom n)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) → False.
Proof.
  intro H.
  assert (H' : (n * 2)%Z = (1 * 1)%Z) by exact H.
  assert (Hodd : Z.odd (n * 2) = Z.odd (1 * 1)) by (now rewrite H').
  rewrite Z.odd_mul in Hodd; simpl in Hodd.
  destruct (Z.odd n); discriminate Hodd.
Qed.
