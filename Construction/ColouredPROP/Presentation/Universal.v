Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
(* [Category.Instance.Fun] is Required transitively (its [Fun] category
   hosts the tensor-comparison isomorphism below) but deliberately NOT
   Imported: its bracket notation [C, D] is grammatically incompatible
   with the singleton list notation [c] of [ListNotations], which the
   wire-datum corollary needs.  The use sites write the qualified
   [@Category.Instance.Fun.Fun] instead — the same discipline as
   [Construction/ColouredPROP/Universal.v]. *)
Require Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.
Require Import Category.Construction.ColouredPROP.Presentation.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * The universal property of a presented coloured PROP *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/generators+and+relations
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Presentation_of_a_monoid

   [Construction/ColouredPROP/Universal.v] packages the interpretation
   of free coloured terms into the strict symmetric monoidal functor
   [CInterpF] and proves it unique: the free coloured PROP is initial
   among coloured PROPs with an [S]-valuation.  This file extends that
   universal property through a PRESENTATION: given a coloured
   symmetric monoidal theory [E : CSMT Colour] and a valuation [v] of
   its generators in a coloured PROP [P] that is SOUND for the axioms
   of [E] ([CESound] — axiom-related terms have equivalent
   interpretations), the interpretation factors through the presented
   coloured PROP of [Construction/ColouredPROP/Presentation.v],
   uniquely among strict symmetric monoidal functors.

   In one sentence: an [E]-sound valuation extends uniquely through
   the presented coloured PROP.  This is the rule-soundness interface
   by which a many-sorted equational theory is installed into a
   semantic target once, and every [CTermEqW]-derivable equation then
   holds there for free.

   This file is the many-sorted mirror of
   [Construction/PROP/Presentation/Universal.v] (the one-sorted
   donor), with [list Colour] replacing [nat], [++] replacing
   [Nat.add], and the boundary equations [app_nil_l] / [app_nil_r] /
   [app_assoc] replacing [Nat.add_0_l] / [Nat.add_0_r] /
   [Nat.add_assoc].  Contents:

   - [cinterpW_sound]: soundness of [cinterp] for the theory
     congruence [CTermEqW E] — a six-constructor induction whose
     [CTEW_termeq] case is [Interp.v]'s whole nineteen-case
     [cinterp_sound_heq], reused; as there, [CTermEqW] is
     [Prop]-valued while the hom equivalence of the abstract target is
     [Type]-valued, so the induction lands in the [Prop]-reflection
     [heq] and round-trips through [heq_intro]/[heq_elim];

   - [CPresentedInterp]: the interpretation functor on
     [CPresentedCat E], obtained by the quotient lifting of
     [Construction/Quotient.v]; it factors [CInterpF] through
     [CPresentedProj E] DEFINITIONALLY ([CPresentedInterp_proj] is a
     Leibniz equality by [eq_refl], and [CPresented_factor] is its
     [≈]-level restatement);

   - the strict symmetric monoidal structure on [CPresentedInterp]:
     the comparison DATA are the same [cprop_unit_nil] /
     [cprop_tensor_app] casts as [CInterpF]'s, and every proof field
     is one of [Universal.v]'s named coherence lemmas
     ([cinterp_ap_natural], [cinterp_monoidal_unit_left] /
     [cinterp_monoidal_unit_right], [cinterp_monoidal_assoc],
     [cinterp_braid_ap]) — their statements are purely target-side,
     which is exactly why they were factored out there;

   - [CPresented_unique]: any strict symmetric competitor
     [G : CPresentedCat E ⟶ P] agreeing with [v] on generators agrees
     with [cinterp] on EVERY morphism of the presented category, up to
     the [hom_cast] conjugation along an object-agreement family
     [Hobj].  Proved by PRECOMPOSITION with the projection: the
     composite [G ◯ CPresentedProj E] is strict monoidal by
     [Compose_StrictMonoidalFunctor], its comparisons collapse onto
     [G]'s own because the projection's comparisons are identities
     with [eq_refl] object equalities, so [Universal.v]'s
     [cinterp_unique] applies to the composite and transfers back
     definitionally — every hom of [CPresentedCat E] IS a term;

   - [CPresented_unique_from_wires]: the object agreement synthesised
     from the single-wire data [∀ c, G [c] = ⟦[c]⟧] by the
     [CPresentedG_obj] fixpoint, exactly as [cinterp_unique_from_wires]
     does on the free side ([strict_pure_obj] against
     [cprop_unit_nil] at the empty word, [strict_ap_obj] against
     [cprop_tensor_app] peeling one typed wire at a time).

   As in [Universal.v], "strict symmetric monoidal functor" is one
   [StrictMonoidalFunctor] over the strict-path monoidals plus the
   braid-compatibility square [CSymmetricStrictW] over that SAME
   tensor comparison, with the target braiding re-indexed to the
   strict path by [cstrict_braid]; see the design note there for why
   the hypothesis pack is phrased against this bundle rather than
   against the two independent Phase-1 functor classes. *)

Section CPresentedUniversal.

Context {Colour : Type}.
Context (E : CSMT Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (P : ColouredPROP Colour).
Context {HP : @HomEqProp P}.
Context {OD : @ObjDecEq P}.

Notation Σ := (csmt_sig E).

Context (v : CValuation P Σ).

Notation "⟦ cs ⟧" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧").

(** ** 1. Soundness for the theory congruence

    A valuation is [E]-SOUND when the two sides of every axiom of the
    theory have equivalent interpretations.  This is the semantic
    entry fee of the presentation: the free equations hold in any
    coloured PROP ([cinterp_sound]), and the axioms hold by
    hypothesis. *)

Definition CESound : Type :=
  ∀ (cs ds : list Colour) (s t : CTerm Σ cs ds),
    csmt_eqs E cs ds s t → cinterp P Σ v s ≈ cinterp P Σ v t.

Context (HE : CESound).

(** Soundness of [cinterp] for [CTermEqW E], in the [Prop]-reflection.
    Six cases: the embedded free equations are [Interp.v]'s
    [cinterp_sound_heq] wholesale; the axioms are [HE]; symmetry,
    transitivity and the two composition congruences round-trip
    through [heq_intro]/[heq_elim] as in the donor induction. *)
Lemma cinterpW_sound_heq {cs ds : list Colour} {s t : CTerm Σ cs ds} :
  CTermEqW E s t → heq (cinterp P Σ v s) (cinterp P Σ v t).
Proof using E HE HP OD P v.
  intros HT.
  induction HT as
    [ cs ds s t Hst
    | cs ds s t Hax
    | cs ds s t Hst IH
    | cs ds s t u Hst IH1 Htu IH2
    | cs ds es f f' g g' Hf IHf Hg IHg
    | cs1 ds1 cs2 ds2 f f' g g' Hf IHf Hg IHg ].
  - (* CTEW_termeq: a free equation *)
    exact (cinterp_sound_heq P Σ v Hst).
  - (* CTEW_ax: an axiom of the theory *)
    exact (heq_intro (HE _ _ s t Hax)).
  - (* CTEW_sym *)
    apply heq_intro; symmetry; exact (heq_elim IH).
  - (* CTEW_trans *)
    apply heq_intro.
    rewrite (heq_elim IH1).
    exact (heq_elim IH2).
  - (* CTEW_comp *)
    apply heq_intro; cbn [cinterp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
  - (* CTEW_tens *)
    apply heq_intro; cbn [cinterp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
Qed.

(** Soundness, in the target's own hom equivalence. *)
Theorem cinterpW_sound {cs ds : list Colour} {s t : CTerm Σ cs ds} :
  CTermEqW E s t → cinterp P Σ v s ≈ cinterp P Σ v t.
Proof using E HE HP OD P v.
  intros HT.
  exact (heq_elim (cinterpW_sound_heq HT)).
Qed.

(** ** 2. The interpretation functor on the presented category

    [CInterpF] identifies [CTermEqW]-related morphisms (that is
    [cinterpW_sound]), so it lifts through the quotient by the
    universal property of [Construction/Quotient.v].  The lift acts
    on objects and morphisms exactly as [CInterpF] does. *)

Definition CPresentedInterp : CPresentedCat E ⟶ P :=
  @QuotientLift (CFreeCat Σ)
    (fun cs ds : list Colour => @CTermEqW Colour E cs ds)
    (CTermEqW_Congruence E) P (CInterpF Σ P v)
    (fun (cs ds : list Colour) (s t : CTerm Σ cs ds)
         (H : CTermEqW E s t) => cinterpW_sound H).

(** The factorisation through the projection is DEFINITIONAL: both
    sides are the very same interpretation of the very same term. *)
Lemma CPresentedInterp_proj {cs ds : list Colour} (t : CTerm Σ cs ds) :
  fmap[CPresentedInterp] (fmap[CPresentedProj E] t)
  = fmap[CInterpF Σ P v] t.
Proof. reflexivity. Qed.

(** ** 3. The strong and strict monoidal structure

    Same component data as [CInterpF]'s in [Universal.v] §3: the
    tensor comparison is the [cprop_tensor_app] cast, packaged as a
    natural isomorphism in the functor category, and every proof field
    is a named target-side lemma of [Universal.v] — the source
    category changed, the target goals did not. *)

Definition CPresentedInterp_ap_dom :
  CPresentedCat E ∏ CPresentedCat E ⟶ P :=
  @tensor P (MPc P) ◯ CPresentedInterp ∏⟶ CPresentedInterp.

Definition CPresentedInterp_ap_cod :
  CPresentedCat E ∏ CPresentedCat E ⟶ P :=
  CPresentedInterp ◯ @tensor (CPresentedCat E) (CPresented_Monoidal E Cdec).

Definition CPresentedInterp_ap_to :
  CPresentedInterp_ap_dom ⟹ CPresentedInterp_ap_cod :=
  @Build_Transform' (CPresentedCat E ∏ CPresentedCat E) P
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod
    (fun mn => id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn)))
    (fun x y f => cinterp_ap_natural Σ P v (fst f) (snd f)).

Definition CPresentedInterp_ap_from :
  CPresentedInterp_ap_cod ⟹ CPresentedInterp_ap_dom :=
  @Build_Transform' (CPresentedCat E ∏ CPresentedCat E) P
    CPresentedInterp_ap_cod CPresentedInterp_ap_dom
    (fun mn =>
       id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn))))
    (fun x y f => cinterp_ap_natural_from Σ P v (fst f) (snd f)).

(** The two composites are the identity transformation, componentwise
    (in the functor category the identity's component at [mn] is
    [fmap id], which on each side reduces to a tensor of identities);
    proof text as in the free-source donor. *)
Lemma CPresentedInterp_ap_to_from
  (mn : CPresentedCat E ∏ CPresentedCat E) :
  id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn))
      ∘ id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn)))
    ≈ cinterp P Σ v (CT_tens (CT_id (fst mn)) (CT_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [cinterp].
  apply ctensor_hom_id.
Qed.

Lemma CPresentedInterp_ap_from_to
  (mn : CPresentedCat E ∏ CPresentedCat E) :
  id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn)))
      ∘ id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn))
    ≈ (cinterp P Σ v (CT_id (fst mn))
         ⨂[MPc P] cinterp P Σ v (CT_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [cinterp].
  apply bimap_id_id.
Qed.

(* The functor-category isomorphism is an explicit [Build_Isomorphism]
   application, pinning the ambient category to the functor category
   [Fun (CPresentedCat E ∏ CPresentedCat E) P] (a record literal would
   leave it to inference; see the import note at the top for why the
   category is written in qualified form rather than bracket
   notation). *)
Definition CPresentedInterp_ap_iso :
  @Isomorphism
    (@Category.Instance.Fun.Fun (CPresentedCat E ∏ CPresentedCat E) P)
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod :=
  @Build_Isomorphism
    (@Category.Instance.Fun.Fun (CPresentedCat E ∏ CPresentedCat E) P)
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod
    CPresentedInterp_ap_to CPresentedInterp_ap_from
    CPresentedInterp_ap_to_from CPresentedInterp_ap_from_to.

(** The strong monoidal structure.  All data fields are casts and all
    proof fields are the named lemmas of [Universal.v] §2. *)
Definition CPresentedInterp_Monoidal :
  @MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp :=
  @Build_MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp
    (id_cast_iso (@cprop_unit_nil Colour P))
    CPresentedInterp_ap_iso
    (fun x : list Colour => @unit_left P (MPc P) ⟦x⟧)
    (fun x : list Colour =>
       iso_compose
         (id_cast_iso (f_equal (@cprop_of_list Colour P)
                               (eq_sym (app_nil_r x))))
         (@unit_right P (MPc P) ⟦x⟧))
    (fun x y z : list Colour =>
       id_cast_iso
         (eq_trans
            (f_equal (fun u : P => (u ⨂[MPc P] ⟦z⟧)%object)
                     (@cprop_tensor_app Colour P x y))
            (eq_trans (@cprop_tensor_app Colour P (x ++ y) z)
                      (f_equal (@cprop_of_list Colour P)
                               (eq_sym (app_assoc x y z))))))
    (fun x : list Colour => cinterp_monoidal_unit_left Σ P v x)
    (fun x : list Colour => cinterp_monoidal_unit_right Σ P v x)
    (fun x y z : list Colour => cinterp_monoidal_assoc Σ P v x y z).

(** The comparisons ARE the coloured PROP's strictness equalities,
    verbatim — [strict_pure_obj] is [cprop_unit_nil] and
    [strict_ap_obj] is [cprop_tensor_app], as the universal property
    demands.  The two reflexivity-grade comparison fields are in-situ
    Program obligations (the [CPresented_Strict] discipline of
    [Presentation.v]): a separately-declared comparison lemma carries
    its own universe instance of the polymorphic [CPresentedCat], and
    the record-field unifier stops at the instance mismatch inside the
    transported-identity [match] before it would reduce both sides;
    proving the field in situ keeps the whole comparison at the
    record's single instance. *)
Program Definition CPresentedInterp_Strict :
  @StrictMonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp := {|
  strict_functor_is_monoidal := CPresentedInterp_Monoidal;
  strict_pure_obj := @cprop_unit_nil Colour P;         (* the class field *)
  strict_ap_obj := fun x y : list Colour =>
    @cprop_tensor_app Colour P x y                     (* ditto *)
|}.

(** ** 4. Symmetry

    The braid-compatibility square of a monoidal functor out of the
    presented category, over its own tensor comparison, with the
    target braiding re-indexed to the strict path by [cstrict_braid] —
    the presented-source sibling of [Universal.v]'s
    [CSymmetricStrict]. *)

Definition CSymmetricStrictW (G : CPresentedCat E ⟶ P)
  (MG : @MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
          (MPc P) G) : Type :=
  ∀ cs ds : list Colour,
    fmap[G] (cquot E (CT_braid cs ds)) ∘ to (@ap_iso _ _ _ _ G MG cs ds)
      ≈ to (@ap_iso _ _ _ _ G MG ds cs) ∘ cstrict_braid P (G cs) (G ds).

Lemma CPresentedInterp_SymmetricStrict :
  CSymmetricStrictW CPresentedInterp CPresentedInterp_Monoidal.
Proof.
  intros cs ds.
  exact (cinterp_braid_ap Σ P v cs ds).
Qed.

(** ** 5. Factorisation

    The [≈]-level statement of the (definitional) factorisation of
    the interpretation through the projection: [CPresentedInterp]
    extends [v]'s interpretation along [CPresentedProj E]. *)

Theorem CPresented_factor : ∀ cs ds (t : CTerm Σ cs ds),
  fmap[CPresentedInterp] (fmap[CPresentedProj E] t) ≈ cinterp P Σ v t.
Proof.
  intros; reflexivity.
Qed.

(** ** 6. Uniqueness

    Any strict symmetric competitor agreeing with [v] on generators
    agrees with [cinterp] on every morphism of [CPresentedCat E], up
    to the [hom_cast] conjugation along the object family [Hobj].  As
    on the free side, the theorem holds for an ARBITRARY such family —
    axiom-free UIP on [obj P] (the [ObjDecEq] class) makes any two
    proofs of the same object equality interchangeable. *)

Section CPresentedUniqueness.

Context (G : CPresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (CPresentedCat E) P
                (CPresented_Monoidal E Cdec) (MPc P) G).
Context (HBW : CSymmetricStrictW G SG).
Context (Hobj : ∀ cs : list Colour, G cs = ⟦cs⟧).
Context (Hgen : ∀ cs ds (g : Σ cs ds),
  fmap[G] (cquot E (CT_gen g))
    ≈ hom_cast (eq_sym (Hobj cs)) (eq_sym (Hobj ds)) (v cs ds g)).

(** The competitor, precomposed with the projection: a functor from
    the FREE category, to which [Universal.v]'s uniqueness applies.
    Its action on objects and morphisms is definitionally [G]'s own,
    because the projection is the identity on both. *)
Definition CPresentedComposite : CFreeCat Σ ⟶ P := G ◯ CPresentedProj E.

(** The composite is strict monoidal: [Compose_StrictMonoidalFunctor]
    of [SG] after [CPresentedProj_Strict].  Because the projection's
    strict object equalities are [eq_refl], the composite's strict
    object data reduce to [SG]'s own ([eq_trans e eq_refl ≡ e]). *)
Definition CPresentedComposite_Strict :
  @StrictMonoidalFunctor (CFreeCat Σ) P (CFreeCat_Monoidal Σ Cdec)
    (MPc P) CPresentedComposite :=
  @Compose_StrictMonoidalFunctor (CFreeCat Σ) (CPresentedCat E) P
    (CFreeCat_Monoidal Σ Cdec) (CPresented_Monoidal E Cdec) (MPc P)
    G (CPresentedProj E) SG (CPresentedProj_Strict E Cdec).

(** Machine-checked: the composite's strict object comparisons ARE
    [SG]'s, definitionally.  This is the cast-fusing content of the
    precomposition route. *)
Example CPresentedComposite_ap_obj_is_SG (x y : list Colour) :
  @strict_ap_obj _ _ _ _ CPresentedComposite CPresentedComposite_Strict x y
  = @strict_ap_obj _ _ _ _ G SG x y := eq_refl.

Example CPresentedComposite_pure_obj_is_SG :
  @strict_pure_obj _ _ _ _ CPresentedComposite CPresentedComposite_Strict
  = @strict_pure_obj _ _ _ _ G SG := eq_refl.

(** Both tensor comparisons, spelled as the cast along [SG]'s object
    equality (the composite's comparison converts to the same cast,
    by the [Example]s above). *)
Lemma CPresentedComposite_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ CPresentedComposite
        (@strict_functor_is_monoidal _ _ _ _ CPresentedComposite
           CPresentedComposite_Strict) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ CPresentedComposite
           CPresentedComposite_Strict x y).
Qed.

Lemma CPresented_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ G SG x y).
Qed.

(** The composite inherits the braid-compatibility square from [HBW]:
    rewriting all four comparisons to the SAME cast aligns the two
    squares, and the remaining sides agree definitionally. *)
Lemma CPresentedComposite_SymmetricStrict :
  CSymmetricStrict Σ Cdec P CPresentedComposite
    (@strict_functor_is_monoidal _ _ _ _ CPresentedComposite
       CPresentedComposite_Strict).
Proof using Cdec E G HBW P SG.
  intros x y.
  rewrite (CPresentedComposite_ap_cast x y).
  rewrite (CPresentedComposite_ap_cast y x).
  pose proof (HBW x y) as HB.
  rewrite (CPresented_ap_cast x y) in HB.
  rewrite (CPresented_ap_cast y x) in HB.
  exact HB.
Qed.

(** Main uniqueness.  [cinterp_unique] pins the composite on every
    term; since the projection is the identity on objects and
    morphisms — every hom of [CPresentedCat E] IS a term — the
    conclusion transfers back to [G] definitionally. *)
Theorem CPresented_unique :
  ∀ cs ds (f : cs ~{CPresentedCat E}~> ds),
    fmap[G] f ≈ hom_cast (eq_sym (Hobj cs)) (eq_sym (Hobj ds))
                         (cinterp P Σ v f).
Proof using Cdec E G HBW Hgen Hobj OD P SG v.
  intros cs ds f.
  exact (cinterp_unique Σ Cdec P v CPresentedComposite
           CPresentedComposite_Strict CPresentedComposite_SymmetricStrict
           Hobj Hgen cs ds f).
Qed.

End CPresentedUniqueness.

(** *** Uniqueness from single-wire object data

    As on the free side, the object family [Hobj] can be synthesised
    from the single-wire data [∀ c, G [c] = ⟦[c]⟧]: empty-word
    agreement is [strict_pure_obj] against [cprop_unit_nil], and cons
    agreement peels one typed wire off with [strict_ap_obj] against
    [cprop_tensor_app], using the definitional fact
    [[c] ⨂ cs' = [c] ++ cs' = c :: cs'] on the presented side. *)

Section CPresentedUniquenessFromWires.

Context (G : CPresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (CPresentedCat E) P
                (CPresented_Monoidal E Cdec) (MPc P) G).
Context (HBW : CSymmetricStrictW G SG).
Context (H1 : ∀ c : Colour, G [c] = ⟦[c]⟧).

Fixpoint CPresentedG_obj (cs : list Colour) : G cs = ⟦cs⟧ :=
  match cs with
  | [] => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                   (@cprop_unit_nil Colour P)
  | c :: cs' =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG [c] cs'))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MPc P] b)%object)
                     (H1 c) (CPresentedG_obj cs'))
           (@cprop_tensor_app Colour P [c] cs'))
  end.

Corollary CPresented_unique_from_wires
  (Hgen : ∀ cs ds (g : Σ cs ds),
     fmap[G] (cquot E (CT_gen g))
       ≈ hom_cast (eq_sym (CPresentedG_obj cs))
                  (eq_sym (CPresentedG_obj ds)) (v cs ds g)) :
  ∀ cs ds (f : cs ~{CPresentedCat E}~> ds),
    fmap[G] f ≈ hom_cast (eq_sym (CPresentedG_obj cs))
                         (eq_sym (CPresentedG_obj ds))
                         (cinterp P Σ v f).
Proof using Cdec E G H1 HBW OD P SG v.
  exact (CPresented_unique G SG HBW CPresentedG_obj Hgen).
Qed.

End CPresentedUniquenessFromWires.

(** ** Machine-checked sanity

    Each [Example] pins a definitional behaviour, so any regression in
    the quotient-lifting or shared-record wiring is caught here rather
    than at a distant use site. *)

(** The lifted functor acts as the interpretation on terms. *)
Example CPresentedInterp_fmap_on_terms {cs ds : list Colour}
  (t : CTerm Σ cs ds) :
  fmap[CPresentedInterp] (cquot E t) = cinterp P Σ v t := eq_refl.

(** The strict object comparisons of [CPresentedInterp_Strict] are the
    coloured-PROP class fields themselves. *)
Example CPresentedInterp_strict_pure_obj_is_cprop_unit_nil :
  @strict_pure_obj _ _ _ _ CPresentedInterp CPresentedInterp_Strict
  = @cprop_unit_nil Colour P := eq_refl.

Example CPresentedInterp_strict_ap_obj_is_cprop_tensor_app
  (x y : list Colour) :
  @strict_ap_obj _ _ _ _ CPresentedInterp CPresentedInterp_Strict x y
  = @cprop_tensor_app Colour P x y := eq_refl.

(** Every axiom of the theory holds under the lifted interpretation —
    the end-to-end form of [CESound]. *)
Example CPresentedInterp_respects_axioms {cs ds : list Colour}
  (s t : CTerm Σ cs ds) (Hax : csmt_eqs E cs ds s t) :
  fmap[CPresentedInterp] (cquot E s) ≈ fmap[CPresentedInterp] (cquot E t) :=
  cinterpW_sound (CTEW_ax E s t Hax).

End CPresentedUniversal.

Arguments CESound {Colour} E P v : assert.
Arguments CPresentedInterp {Colour} E P {HP OD} v HE : assert.
Arguments CSymmetricStrictW {Colour} E Cdec P G MG : assert.
