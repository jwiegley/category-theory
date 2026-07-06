Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Compose.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.
Require Import Category.Construction.PROP.Presentation.

From Coq Require Import Arith.

Generalizable All Variables.

(** * The universal property of a presented PROP *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/generators+and+relations
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Presentation_of_a_monoid

   [Construction/PROP/Universal.v] packages the interpretation of free
   terms into the strict symmetric monoidal functor [InterpF] and
   proves it unique: the free PROP is initial among PROPs with an
   [S]-valuation.  This file extends that universal property through a
   PRESENTATION: given a symmetric monoidal theory [E : SMT] and a
   valuation [v] of its generators in a PROP [P] that is SOUND for the
   axioms of [E] ([ESound] — axiom-related terms have equivalent
   interpretations), the interpretation factors through the presented
   PROP of [Construction/PROP/Presentation.v], uniquely among strict
   symmetric monoidal functors.

   In one sentence: an [E]-sound valuation extends uniquely through
   the presented PROP.  This is the rule-soundness interface by which
   an equational theory is installed into a semantic target once, and
   every [TermEqW]-derivable equation then holds there for free.

   Contents:

   - [interpW_sound]: soundness of [interp] for the theory congruence
     [TermEqW E] — a six-constructor induction whose [TEW_termeq] case
     is [Interp.v]'s whole nineteen-case [interp_sound_heq], reused;
     as there, [TermEqW] is [Prop]-valued while the hom equivalence of
     the abstract target is [Type]-valued, so the induction lands in
     the [Prop]-reflection [heq] and round-trips through
     [heq_intro]/[heq_elim];

   - [PresentedInterp]: the interpretation functor on [PresentedCat E],
     obtained by the quotient lifting of [Construction/Quotient.v]; it
     factors [InterpF] through [PresentedProj E] DEFINITIONALLY
     ([PresentedInterp_proj] is a Leibniz equality by [eq_refl], and
     [Presented_factor] is its [≈]-level restatement);

   - the strict symmetric monoidal structure on [PresentedInterp]: the
     comparison DATA are the same [prop_unit_zero]/[prop_tensor_plus]
     casts as [InterpF]'s, and every proof field is one of
     [Universal.v]'s named coherence lemmas ([interp_ap_natural],
     [interp_monoidal_unit_left]/[interp_monoidal_unit_right],
     [interp_monoidal_assoc], [interp_braid_ap]) — their statements
     are purely target-side, which is exactly why they were factored
     out there;

   - [Presented_unique]: any strict symmetric competitor
     [G : PresentedCat E ⟶ P] agreeing with [v] on generators agrees
     with [interp] on EVERY morphism of the presented category, up to
     the [hom_cast] conjugation along an object-agreement family
     [Hobj].  Proved by PRECOMPOSITION with the projection: the
     composite [G ◯ PresentedProj E] is strict monoidal by
     [Compose_StrictMonoidalFunctor], its comparisons collapse onto
     [G]'s own because the projection's comparisons are identities
     with [eq_refl] object equalities, so [Universal.v]'s
     [interp_unique] applies to the composite and transfers back
     definitionally — every hom of [PresentedCat E] IS a term;

   - [Presented_unique_from_one]: the object agreement synthesised
     from the single datum [G 1 = ⟦1⟧] by the [PresentedG_obj]
     fixpoint, exactly as [interp_unique_from_one] does on the free
     side ([strict_pure_obj] against [prop_unit_zero] at arity 0,
     [strict_ap_obj] against [prop_tensor_plus] peeling one wire at a
     time).

   As in [Universal.v], "strict symmetric monoidal functor" is one
   [StrictMonoidalFunctor] over the strict-path monoidals plus the
   braid-compatibility square [SymmetricStrictW] over that SAME tensor
   comparison, with the target braiding re-indexed to the strict path
   by [strict_braid]; see the design note there for why the hypothesis
   pack is phrased against this bundle rather than against the two
   independent [StrictMonoidalFunctor]/[BraidedMonoidalFunctor]
   classes of [Functor/Structure/Monoidal/Strict.v] and
   [Functor/Structure/Monoidal/Braided.v]. *)

Section PresentedUniversal.

Context (E : SMT).
Context (P : PROP).
Context {HP : HomEqProp P}.
Context {OD : @ObjDecEq P}.

Notation Σ := (smt_sig E).

Context (v : Valuation P Σ).

Open Scope nat_scope.

Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(** ** 1. Soundness for the theory congruence

    A valuation is [E]-SOUND when the two sides of every axiom of the
    theory have equivalent interpretations.  This is the semantic
    entry fee of the presentation: the free equations hold in any
    PROP ([interp_sound]), and the axioms hold by hypothesis. *)

Definition ESound : Type :=
  ∀ m n (s t : Term Σ m n),
    smt_eqs E m n s t → interp P Σ v s ≈ interp P Σ v t.

Context (Hv : ESound).

(** Soundness of [interp] for [TermEqW E], in the [Prop]-reflection.
    Six cases: the embedded free equations are [Interp.v]'s
    [interp_sound_heq] wholesale; the axioms are [Hv]; symmetry,
    transitivity and the two composition congruences round-trip
    through [heq_intro]/[heq_elim] as in the donor induction. *)
Lemma interpW_sound_heq {m n : nat} {s t : Term Σ m n} :
  TermEqW E s t → heq (interp P Σ v s) (interp P Σ v t).
Proof using E HP Hv OD P v.
  intros HT.
  induction HT as
    [ m n s t Hst
    | m n s t Hax
    | m n s t Hst IH
    | m n s t u Hst IH1 Htu IH2
    | m n p f f' g g' Hf IHf Hg IHg
    | m1 n1 m2 n2 f f' g g' Hf IHf Hg IHg ].
  - (* TEW_termeq: a free equation *)
    exact (interp_sound_heq P Σ v Hst).
  - (* TEW_ax: an axiom of the theory *)
    exact (heq_intro (Hv _ _ s t Hax)).
  - (* TEW_sym *)
    apply heq_intro; symmetry; exact (heq_elim IH).
  - (* TEW_trans *)
    apply heq_intro.
    rewrite (heq_elim IH1).
    exact (heq_elim IH2).
  - (* TEW_comp *)
    apply heq_intro; cbn [interp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
  - (* TEW_tens *)
    apply heq_intro; cbn [interp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
Qed.

(** Soundness, in the target's own hom equivalence. *)
Theorem interpW_sound {m n : nat} {s t : Term Σ m n} :
  TermEqW E s t → interp P Σ v s ≈ interp P Σ v t.
Proof using E HP Hv OD P v.
  intros HT.
  exact (heq_elim (interpW_sound_heq HT)).
Qed.

(** ** 2. The interpretation functor on the presented category

    [InterpF] identifies [TermEqW]-related morphisms (that is
    [interpW_sound]), so it lifts through the quotient by the
    universal property of [Construction/Quotient.v].  The lift acts
    on objects and morphisms exactly as [InterpF] does. *)

Definition PresentedInterp : PresentedCat E ⟶ P :=
  @QuotientLift (FreeCat Σ) (fun m n : nat => @TermEqW E m n)
    (TermEqW_Congruence E) P (InterpF Σ P v)
    (fun (m n : nat) (s t : Term Σ m n) (H : TermEqW E s t) =>
       interpW_sound H).

(** The factorisation through the projection is DEFINITIONAL: both
    sides are the very same interpretation of the very same term. *)
Lemma PresentedInterp_proj {m n : nat} (t : Term Σ m n) :
  fmap[PresentedInterp] (fmap[PresentedProj E] t) = fmap[InterpF Σ P v] t.
Proof. reflexivity. Qed.

(** ** 3. The strong and strict monoidal structure

    Same component data as [InterpF]'s in [Universal.v] §3: the tensor
    comparison is the [prop_tensor_plus] cast, packaged as a natural
    isomorphism in the functor category, and every proof field is a
    named target-side lemma of [Universal.v] — the source category
    changed, the target goals did not. *)

Definition PresentedInterp_ap_dom :
  PresentedCat E ∏ PresentedCat E ⟶ P :=
  @tensor P (MP P) ◯ PresentedInterp ∏⟶ PresentedInterp.

Definition PresentedInterp_ap_cod :
  PresentedCat E ∏ PresentedCat E ⟶ P :=
  PresentedInterp ◯ @tensor (PresentedCat E) (Presented_Monoidal E).

Definition PresentedInterp_ap_to :
  PresentedInterp_ap_dom ⟹ PresentedInterp_ap_cod :=
  @Build_Transform' (PresentedCat E ∏ PresentedCat E) P
    PresentedInterp_ap_dom PresentedInterp_ap_cod
    (fun mn => id_cast (prop_tensor_plus (fst mn) (snd mn)))
    (fun x y f => interp_ap_natural Σ P v (fst f) (snd f)).

Definition PresentedInterp_ap_from :
  PresentedInterp_ap_cod ⟹ PresentedInterp_ap_dom :=
  @Build_Transform' (PresentedCat E ∏ PresentedCat E) P
    PresentedInterp_ap_cod PresentedInterp_ap_dom
    (fun mn => id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn))))
    (fun x y f => interp_ap_natural_from Σ P v (fst f) (snd f)).

(** The two composites are the identity transformation, componentwise
    (in the functor category the identity's component at [mn] is
    [fmap id], which on each side reduces to a tensor of identities);
    proof text as in the donor. *)
Lemma PresentedInterp_ap_to_from (mn : PresentedCat E ∏ PresentedCat E) :
  id_cast (prop_tensor_plus (fst mn) (snd mn))
      ∘ id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
    ≈ interp P Σ v (T_tens (T_id (fst mn)) (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [interp].
  apply tensor_hom_id.
Qed.

Lemma PresentedInterp_ap_from_to (mn : PresentedCat E ∏ PresentedCat E) :
  id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
      ∘ id_cast (prop_tensor_plus (fst mn) (snd mn))
    ≈ (interp P Σ v (T_id (fst mn)) ⨂[MP P] interp P Σ v (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [interp].
  apply bimap_id_id.
Qed.

Program Definition PresentedInterp_ap_iso :
  PresentedInterp_ap_dom
    ≅[[PresentedCat E ∏ PresentedCat E, P]] PresentedInterp_ap_cod := {|
  to := PresentedInterp_ap_to;
  from := PresentedInterp_ap_from;
  iso_to_from := PresentedInterp_ap_to_from;
  iso_from_to := PresentedInterp_ap_from_to
|}.

(** The strong monoidal structure.  All data fields are casts and all
    proof fields are the named lemmas of [Universal.v] §2. *)
Program Definition PresentedInterp_Monoidal :
  @MonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P)
    PresentedInterp := {|
  pure_iso := id_cast_iso (@prop_unit_zero P);
  ap_functor_iso := PresentedInterp_ap_iso;
  pure_iso_left := fun x : nat => @unit_left P (MP P) ⟦x⟧;
  pure_iso_right := fun x : nat =>
    iso_compose
      (id_cast_iso (f_equal (@prop_of_nat P) (eq_sym (Nat.add_0_r x))))
      (@unit_right P (MP P) ⟦x⟧);
  ap_iso_assoc := fun x y z : nat =>
    id_cast_iso
      (eq_trans
         (f_equal (fun u : P => (u ⨂[MP P] ⟦z⟧)%object)
                  (prop_tensor_plus x y))
         (eq_trans (prop_tensor_plus (x + y) z)
                   (f_equal (@prop_of_nat P)
                            (eq_sym (Nat.add_assoc x y z)))));
  monoidal_unit_left := interp_monoidal_unit_left Σ P v;
  monoidal_unit_right := interp_monoidal_unit_right Σ P v;
  monoidal_assoc := interp_monoidal_assoc Σ P v
|}.

(** The comparisons ARE the PROP's strictness equalities, verbatim —
    [strict_pure_obj] is [prop_unit_zero] and [strict_ap_obj] is
    [prop_tensor_plus], as the universal property demands.  The two
    reflexivity-grade comparison fields are in-situ Program
    obligations (the [Presented_Strict] discipline of
    [Presentation.v]), which the ambient obligation tactic discharges
    on its own: both comparisons are the transported identities the
    class asks for, definitionally. *)
Program Definition PresentedInterp_Strict :
  @StrictMonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P)
    PresentedInterp := {|
  strict_functor_is_monoidal := PresentedInterp_Monoidal;
  strict_pure_obj := @prop_unit_zero P;               (* the PROP field *)
  strict_ap_obj := fun x y : nat => @prop_tensor_plus P x y      (* ditto *)
|}.

(** ** 4. Symmetry

    The braid-compatibility square of a monoidal functor out of the
    presented category, over its own tensor comparison, with the
    target braiding re-indexed to the strict path by [strict_braid] —
    the presented-source sibling of [Universal.v]'s
    [SymmetricStrict]. *)

Definition SymmetricStrictW (G : PresentedCat E ⟶ P)
  (MG : @MonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P) G) :
  Type :=
  ∀ m n : nat,
    fmap[G] (quot E (T_braid m n)) ∘ to (@ap_iso _ _ _ _ G MG m n)
      ≈ to (@ap_iso _ _ _ _ G MG n m) ∘ strict_braid P (G m) (G n).

Lemma PresentedInterp_SymmetricStrict :
  SymmetricStrictW PresentedInterp PresentedInterp_Monoidal.
Proof.
  intros m n.
  exact (interp_braid_ap Σ P v m n).
Qed.

(** ** 5. Factorisation

    The [≈]-level statement of the (definitional) factorisation of
    the interpretation through the projection: [PresentedInterp]
    extends [v]'s interpretation along [PresentedProj E]. *)

Theorem Presented_factor : ∀ m n (t : Term Σ m n),
  fmap[PresentedInterp] (fmap[PresentedProj E] t) ≈ interp P Σ v t.
Proof.
  intros; reflexivity.
Qed.

(** ** 6. Uniqueness

    Any strict symmetric competitor agreeing with [v] on generators
    agrees with [interp] on every morphism of [PresentedCat E], up to
    the [hom_cast] conjugation along the object family [Hobj].  As on
    the free side, the theorem holds for an ARBITRARY such family —
    axiom-free UIP on [obj P] (the [ObjDecEq] class) makes any two
    proofs of the same object equality interchangeable. *)

Section PresentedUniqueness.

Context (G : PresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (PresentedCat E) P
                (Presented_Monoidal E) (MP P) G).
Context (HBW : SymmetricStrictW G SG).
Context (Hobj : ∀ n : nat, G n = ⟦n⟧).
Context (Hgen : ∀ m n (g : Σ m n),
  fmap[G] (quot E (T_gen g))
    ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (v m n g)).

(** The competitor, precomposed with the projection: a functor from
    the FREE category, to which [Universal.v]'s uniqueness applies.
    Its action on objects and morphisms is definitionally [G]'s own,
    because the projection is the identity on both. *)
Definition PresentedComposite : FreeCat Σ ⟶ P := G ◯ PresentedProj E.

(** The composite is strict monoidal: [Compose_StrictMonoidalFunctor]
    of [SG] after [PresentedProj_Strict].  Because the projection's
    strict object equalities are [eq_refl], the composite's strict
    object data reduce to [SG]'s own ([eq_trans e eq_refl ≡ e]). *)
Definition PresentedComposite_Strict :
  @StrictMonoidalFunctor (FreeCat Σ) P (FreeCat_Monoidal Σ) (MP P)
    PresentedComposite :=
  @Compose_StrictMonoidalFunctor (FreeCat Σ) (PresentedCat E) P
    (FreeCat_Monoidal Σ) (Presented_Monoidal E) (MP P)
    G (PresentedProj E) SG (PresentedProj_Strict E).

(** Machine-checked: the composite's strict object comparisons ARE
    [SG]'s, definitionally.  This is the cast-fusing content of the
    precomposition route. *)
Example PresentedComposite_ap_obj_is_SG (x y : nat) :
  @strict_ap_obj _ _ _ _ PresentedComposite PresentedComposite_Strict x y
  = @strict_ap_obj _ _ _ _ G SG x y := eq_refl.

Example PresentedComposite_pure_obj_is_SG :
  @strict_pure_obj _ _ _ _ PresentedComposite PresentedComposite_Strict
  = @strict_pure_obj _ _ _ _ G SG := eq_refl.

(** Both tensor comparisons, spelled as the cast along [SG]'s object
    equality (the composite's comparison converts to the same cast,
    by the [Example]s above). *)
Lemma PresentedComposite_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ PresentedComposite
        (@strict_functor_is_monoidal _ _ _ _ PresentedComposite
           PresentedComposite_Strict) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ PresentedComposite
           PresentedComposite_Strict x y).
Qed.

Lemma Presented_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ G SG x y).
Qed.

(** The composite inherits the braid-compatibility square from [HBW]:
    rewriting all four comparisons to the SAME cast aligns the two
    squares, and the remaining sides agree definitionally. *)
Lemma PresentedComposite_SymmetricStrict :
  SymmetricStrict Σ P PresentedComposite
    (@strict_functor_is_monoidal _ _ _ _ PresentedComposite
       PresentedComposite_Strict).
Proof using E G HBW P SG.
  intros x y.
  rewrite (PresentedComposite_ap_cast x y).
  rewrite (PresentedComposite_ap_cast y x).
  pose proof (HBW x y) as HB.
  rewrite (Presented_ap_cast x y) in HB.
  rewrite (Presented_ap_cast y x) in HB.
  exact HB.
Qed.

(** Main uniqueness.  [interp_unique] pins the composite on every
    term; since the projection is the identity on objects and
    morphisms — every hom of [PresentedCat E] IS a term — the
    conclusion transfers back to [G] definitionally. *)
Theorem Presented_unique :
  ∀ m n (f : m ~{PresentedCat E}~> n),
    fmap[G] f ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n))
                         (interp P Σ v f).
Proof using E G HBW Hgen Hobj OD P SG v.
  intros m n f.
  exact (interp_unique Σ P v PresentedComposite PresentedComposite_Strict
           PresentedComposite_SymmetricStrict Hobj Hgen m n f).
Qed.

End PresentedUniqueness.

(** *** Uniqueness from a single object datum

    As on the free side, the object family [Hobj] can be synthesised
    from the single equality [G 1 = ⟦1⟧]: zero-arity agreement is
    [strict_pure_obj] against [prop_unit_zero], and successor
    agreement peels one wire off with [strict_ap_obj] against
    [prop_tensor_plus]. *)

Section PresentedUniquenessFromOne.

Context (G : PresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (PresentedCat E) P
                (Presented_Monoidal E) (MP P) G).
Context (HBW : SymmetricStrictW G SG).
Context (H1 : G 1 = ⟦1⟧).

Fixpoint PresentedG_obj (n : nat) : G n = ⟦n⟧ :=
  match n with
  | O => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                  (@prop_unit_zero P)
  | Datatypes.S k =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG 1 k))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MP P] b)%object) H1
                     (PresentedG_obj k))
           (@prop_tensor_plus P 1 k))
  end.

Corollary Presented_unique_from_one
  (Hgen : ∀ m n (g : Σ m n),
     fmap[G] (quot E (T_gen g))
       ≈ hom_cast (eq_sym (PresentedG_obj m)) (eq_sym (PresentedG_obj n))
                  (v m n g)) :
  ∀ m n (f : m ~{PresentedCat E}~> n),
    fmap[G] f ≈ hom_cast (eq_sym (PresentedG_obj m))
                         (eq_sym (PresentedG_obj n))
                         (interp P Σ v f).
Proof using E G H1 HBW OD P SG v.
  exact (Presented_unique G SG HBW PresentedG_obj Hgen).
Qed.

End PresentedUniquenessFromOne.

(** ** Machine-checked sanity

    Each [Example] pins a definitional behaviour, so any regression in
    the quotient-lifting or shared-record wiring is caught here rather
    than at a distant use site. *)

(** The lifted functor acts as the interpretation on terms. *)
Example PresentedInterp_fmap_on_terms {m n : nat} (t : Term Σ m n) :
  fmap[PresentedInterp] (quot E t) = interp P Σ v t := eq_refl.

(** The strict object comparisons of [PresentedInterp_Strict] are the
    PROP class fields themselves. *)
Example PresentedInterp_strict_pure_obj_is_prop_unit_zero :
  @strict_pure_obj _ _ _ _ PresentedInterp PresentedInterp_Strict
  = @prop_unit_zero P := eq_refl.

Example PresentedInterp_strict_ap_obj_is_prop_tensor_plus (x y : nat) :
  @strict_ap_obj _ _ _ _ PresentedInterp PresentedInterp_Strict x y
  = @prop_tensor_plus P x y := eq_refl.

(** Every axiom of the theory holds under the lifted interpretation —
    the end-to-end form of [ESound]. *)
Example PresentedInterp_respects_axioms {m n : nat} (s t : Term Σ m n)
  (Hax : smt_eqs E m n s t) :
  fmap[PresentedInterp] (quot E s) ≈ fmap[PresentedInterp] (quot E t) :=
  interpW_sound (TEW_ax E s t Hax).

End PresentedUniversal.

Arguments ESound E P v : assert.
Arguments PresentedInterp E P {HP OD} v Hv : assert.
Arguments SymmetricStrictW E P G MG : assert.
