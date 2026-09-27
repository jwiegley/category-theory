(** * Torsion groups are coreflective in Ab, stated covariantly

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    Springer GTM 5, §IV.3, printed p. 92 (PDF p. 101), read from the
    page image, catalog item maclane:IV.3:construction1: "A coreflective
    subcategory of Ab is the full subcategory of all torsion abelian
    groups (a group is torsion if all elements have finite order); the
    coreflector sends each abelian group A to the subgroup TA of all
    elements of finite order in A."  The definition is on printed p. 91
    (PDF p. 100): "Dually, A ⊂ B is coreflective in B when the inclusion
    functor A → B has a right adjoint."
    Riehl, "Category Theory in Context", §4.6, Example 4.6.13 (iii),
    printed p. 170 (PDF p. 190), read from the page image, for the other
    half of the pair: "The inclusion Ab_tf ↪ Ab of torsion-free abelian
    groups is reflective.  The reflector sends an abelian group A to the
    quotient A/TA by its torsion subgroup."  That half is #371's
    Instance/Ab/TorsionFree.v; Riehl does not list the coreflection.
    Riehl, §5.3, Exercise 5.3.ii, printed p. 197 (PDF p. 217), catalog
    item riehl:5.3:exii, is carried through at that reflection below.
    nLab: https://ncatlab.org/nlab/show/torsion+subgroup
    nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

    BACKGROUND.  nLab's torsion-subgroup page defines the torsion
    subgroup of an abelian group as the subgroup of its elements of
    finite order, calls a group "pure torsion" when it coincides with it
    and "torsion-free" when it is trivial, and records that torsion and
    torsion-free classes of objects in an abelian category "were
    introduced axiomatically as a torsion theory (or torsion pair) in
    (Dickson 1963)".  The two halves of Mac Lane's page and exercise
    are the two sides of that pair in Ab: the torsion groups
    coreflective with coreflector A ↦ TA, the torsion-free groups
    reflective with reflector A ↦ A/TA.  This file is the first half;
    Instance/Ab/TorsionFree.v, whose header quotes the same paragraph,
    is the second.  That header was written before this file and lists
    this coreflection among what it does not deliver; its CORRECTION
    (#370) note there points here.

    WHAT IS DELIVERED, COVARIANTLY.  The reviewer's check for this item
    is that the coreflective example be stated covariantly, and it is:

      [torsion_coreflection : Incl Ab Torsion_Sub ⊣ torsion_coreflector]

    the inclusion LEFT adjoint to [torsion_coreflector : Ab ⟶
    TorsionCat], with no opposite category in its type.  It is built as
    a couniversal arrow per object: [torsion_couniversal] states the
    ∃!, whose arrow is the inclusion of TA ([torsion_incl], TorsionFree.v)
    and whose mediator [torsion_lift] corestricts a map out of a torsion
    group through TA, using that homomorphisms carry elements of finite
    order to elements of finite order with the same exponent
    ([torsion_map]); Theory/Universal/Arrow/Dual.v's
    [couniversal_arrow_from_UMP], [RightAdjointFunctorFromCouniversalArrows]
    and [AdjunctionFromCouniversalArrows] do the rest.  The record of
    Construction/Reflective.v, [Torsion_Coreflective : Coreflective
    Torsion_Sub], is then built from those covariant data by
    Construction/Reflective/Coreflective.v's [Coreflective_of_adjunction],
    and reading it back returns them on the nose (below).  The torsion
    predicate is #371's [torsion_mem], whose exponent is data; the
    subgroup is TorsionFree.v's [TorsionAb]; no choice principle is used.

    STRENGTHS, measured strict first.  Six [Example]s hold at
    [eq_refl]: the coreflection of A is TA ([torsion_coreflector_obj]);
    the couniversal arrow IS [torsion_incl A] ([torsion_coarrow_is_incl]);
    the counit applied to an element IS the inclusion applied to it
    ([torsion_counit_pointwise]); the record read back covariantly IS
    the covariant functor and adjunction ([torsion_record_coreflector],
    [torsion_record_adj], whole functor and whole adjunction); and the
    torsion-free monad at A is A/TA ([torsionfree_monad_obj]).  Falling
    back, each refusal pinned in Test/ProbeReflective370.v, whose import
    list carries this file's:
      - the counit as a morphism is only [≈] the inclusion
        ([torsion_counit_is_incl], from Dual.v's [counit_couniversal]).
        It is [torsion_incl A ∘ fmap[Incl] id] on the nose (accepted at
        [eq_refl]); against [torsion_incl A] its setoid-morphism
        component is refused at [eq_refl], and so is the whole record,
        with "cannot unify";
      - the coreflector's arrow part is not [torsion_lift] on the nose:
        stating [fmap[torsion_coreflector] f] equal to the corestriction
        of [f ∘ torsion_incl A] is refused, the arrow part being the
        [unique_obj] of Theory/Universal/Arrow.v's [Qed]-closed
        [ump_universal_arrows] read in the opposite categories.

    NON-VACUITY.  ℤ/2 (Instance/Ab/Character/Finite.v's [ZMod2]) is
    torsion, so it is an object of the subcategory ([ZMod2_Torsion]) and
    the unit there is invertible ([ZMod2_coreflect_iso], Coreflective.v's
    [coreflective_unit_iso]).  ℤ × ℤ/2 (TorsionFree.v's [MixedAb]) is not
    torsion ([MixedAb_not_torsion]); its torsion part is not trivial
    ([mixed_tors_in_TA], [mixed_tors_in_TA_nonzero]); and the counit
    there is not invertible ([torsion_counit_MixedAb_not_iso]): an
    inverse would carry the generator (1, 0) into TA and make it torsion.
    At ℤ the torsion part is trivial ([ZAb_TA_trivial]).

    RIEHL 5.3.ii, AT THE TORSION-FREE REFLECTION.  #371's
    [TorsionFree_Reflective] is fed to Construction/Reflective/
    Idempotent.v: [TorsionFree_Monad], [TorsionFree_IdempotentMonad],
    and [TorsionFree_EM_MLocal], which is [Idempotent_EM_Equivalence]
    verbatim, the algebras equivalent to the monad's M-LOCAL objects.
    Riehl's Proposition 5.3.3 (ii) asks for the subcategory itself, and
    Construction/Reflective/Monadic.v supplies it:
    [TorsionFree_EM_Equivalence] (the comparison functor from
    [TorsionFree_Sub] is an equivalence) and [TorsionFree_Incl_Monadic].

    UNIVERSES, read by [About] under [Set Printing Universes] on all
    thirty-four named constants.  Each binder names the levels its
    statement fixes, then [+]: [u p] for [Ab@{u p}]; [a c p] for
    [IsTorsion] over [AbObject@{a c p}] (a fourth level, the result
    sort, is left to [+]); [p] for [TorsionAb_IsTorsion] over
    [AbObject@{p p p}], the only shape at which TorsionFree.v states
    the inclusion [torsion_incl] its proof uses; [a] for
    [ZMod2_IsTorsion]; [u] for the two ℤ/2 statements and the counit
    statement over [Ab@{u Set}]; and none, [@{+}], for
    [MixedAb_not_torsion], [mixed_tors_in_TA], its lemma and
    [ZAb_TA_trivial], whose levels are all their donors'.  No
    block carries an equation.  Thirty-one blocks carry an own [Set]
    bound: twenty-seven [Set < u] on [Ab]'s object level, which is
    [Ab]'s own bound ([About Ab]: [Set < u]; the [PropEquiv] field puts
    [Set+1] in [AbObject]'s sort), and four on a level only a donor
    names -- [TorsionAb_IsTorsion] through the [Ab] instance of
    [torsion_incl] in its proof, and [MixedAb_not_torsion],
    [mixed_tors_in_TA] and its lemma through [MixedAb]'s own
    [Set < u2] ([MixedAb_not_torsion@{u}] reads [¬ IsTorsion
    MixedAb@{Set u u u Set Set Set}] with [Set < u], and never mentions
    [Ab]).  Seven witnesses print [Set] in their instances --
    [ZMod2_IsTorsion], [ZMod2_Torsion], [ZMod2_coreflect_iso],
    [MixedAb_not_torsion], [mixed_tors_in_TA], its lemma and
    [torsion_counit_MixedAb_not_iso] -- because
    [ZMod2@{u} : AbObject@{u Set Set}] ([About ZMod2]; its carrier is
    [bool]).  Six blocks read [Set < Projections.u0], which in each
    follows from an own [Set] bound and the block's caps, and every
    global universe in every block is an upper bound.  Against a copy
    with every binder removed, compared under [Set Printing All], no
    constant lost a universe or gained an identification.

    AXIOMS.  All thirty-seven constants of this module, the thirty-four
    above and three [Program] obligations of [torsion_lift], are closed
    under the global context.

    NOT DELIVERED.
      - Nothing about torsion theories in general, and no statement
        that the torsion and torsion-free classes form one.
      - No idempotent comonad of the coreflection beyond what
        Construction/Reflective/FixedPoints.v's op-form
        [Coreflective_IdempotentMonad_op] gives when applied to
        [Torsion_Coreflective]; that application is not made here.
      - The coreflector's arrow part and the unit are not read back on
        the nose; only the counit is, pointwise.
      - No [Grp] analogue, and no p-primary refinement. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Monad.Comparison.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.Coreflective.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Instance.Ab.TorsionFree.

Generalizable All Variables.

(** ** The full subcategory of torsion groups *)

Definition IsTorsion@{a c p +} (A : AbObject@{a c p}) : Type :=
  ∀ x : carrier A, torsion_mem A x.

Definition Torsion_Sub@{u p +} : Subcategory Ab@{u p} :=
  @Build_Subcategory Ab@{u p} IsTorsion
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TorsionCat@{u p +} : Category := Sub Ab@{u p} Torsion_Sub.

Definition Torsion_Full@{u p +} :
  Category.Construction.Subcategory.Full Ab@{u p} Torsion_Sub :=
  fun _ _ _ _ _ => I.

(* TA is torsion.  Equality in the subgroup compares first projections,
   so the exponent of a member is the exponent it was built with. *)
Definition TorsionAb_IsTorsion@{p +} (A : AbObject@{p p p}) :
  IsTorsion (TorsionAb A).
Proof.
  intros [a [k [Hk Hka]]].
  exists k; split; [ exact Hk | ].
  pose proof (nat_smul_hom (torsion_incl A) k
                (existT _ a (existT _ k (Hk, Hka)))) as E.
  simpl in E |- *.
  exact (transitivity E Hka).
Defined.

(* Mac Lane's TA, as an object of the subcategory. *)
Definition TorsionPart@{u p +} (A : Ab@{u p}) : TorsionCat :=
  (TorsionAb A; TorsionAb_IsTorsion A).

(** ** The couniversal property of the torsion subgroup *)

(* A homomorphism carries an element of finite order to one of finite
   order, with the same exponent. *)
Definition torsion_map@{u p +} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (a : carrier A) :
  torsion_mem A a → torsion_mem B (cmon_map f a).
Proof.
  intros [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite <- nat_smul_hom, Hka.
  apply cmon_map_zero.
Defined.

(* The mediator: a homomorphism out of a torsion group lands in TA. *)
Program Definition torsion_lift@{u p +} {T A : Ab@{u p}} (HT : IsTorsion T)
  (f : T ~{Ab@{u p}}~> A) : T ~{Ab@{u p}}~> TorsionAb A :=
  {| cmon_map := {| morphism := fun t : carrier T =>
       existT _ (cmon_map f t) (torsion_map f t (HT t)) |} |}.
Next Obligation. intros x y Hxy; simpl; now rewrite Hxy. Qed.
Next Obligation. simpl; apply cmon_map_zero. Qed.
Next Obligation. simpl; apply cmon_map_plus. Qed.

Theorem torsion_couniversal@{u p +} (A : Ab@{u p}) :
  ∀ (d : TorsionCat) (f : Incl Ab@{u p} Torsion_Sub d ~{Ab@{u p}}~> A),
    ∃! g : d ~{TorsionCat}~> TorsionPart A,
      f ≈ torsion_incl A ∘ fmap[Incl Ab@{u p} Torsion_Sub] g.
Proof.
  intros d f.
  unshelve eexists.
  - exact (torsion_lift `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition torsion_couniversal_arrow@{u p +} (A : Ab@{u p})
  : @CouniversalArrow Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub) :=
  @couniversal_arrow_from_UMP Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub)
    (TorsionPart A) (torsion_incl A) (torsion_couniversal A).

(** ** The coreflection, stated covariantly *)

Definition torsion_coreflector@{u p +} : Ab@{u p} ⟶ TorsionCat :=
  RightAdjointFunctorFromCouniversalArrows (Incl Ab@{u p} Torsion_Sub)
    torsion_couniversal_arrow.

(* Mac Lane's "coreflective": the inclusion has a RIGHT adjoint. *)
Definition torsion_coreflection@{u p +} :
  Incl Ab@{u p} Torsion_Sub ⊣ torsion_coreflector :=
  AdjunctionFromCouniversalArrows (Incl Ab@{u p} Torsion_Sub)
    torsion_couniversal_arrow.

(* The packaged record of Construction/Reflective.v, built from the
   covariant data through Construction/Reflective/Coreflective.v. *)
Definition Torsion_Coreflective@{u p +} : @Coreflective Ab@{u p} Torsion_Sub :=
  Coreflective_of_adjunction Torsion_Full torsion_coreflector
    torsion_coreflection.

(** ** Readbacks: the counit is the inclusion of TA *)

Example torsion_coreflector_obj@{u p +} (A : Ab@{u p}) :
  `1 (fobj[torsion_coreflector] A) = TorsionAb A := eq_refl.

Example torsion_coarrow_is_incl@{u p +} (A : Ab@{u p}) :
  @coarrow Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub)
    (torsion_couniversal_arrow A)
    = torsion_incl A := eq_refl.

Definition torsion_counit@{u p +} (A : Ab@{u p})
  : Incl Ab@{u p} Torsion_Sub (fobj[torsion_coreflector] A) ~{Ab@{u p}}~> A :=
  @counit _ _ _ _ torsion_coreflection A.

Example torsion_counit_pointwise@{u p +} (A : Ab@{u p})
  (x : carrier (TorsionAb A)) :
  cmon_map (torsion_counit A) x = cmon_map (torsion_incl A) x := eq_refl.

Lemma torsion_counit_is_incl@{u p +} (A : Ab@{u p}) :
  torsion_counit A ≈ torsion_incl A.
Proof.
  exact (counit_couniversal (Incl Ab Torsion_Sub)
           torsion_couniversal_arrow A).
Qed.

(* Read back from the record, the coreflector and the adjunction are the
   covariant ones on the nose. *)
Example torsion_record_coreflector@{u p +} :
  @coreflector Ab@{u p} Torsion_Sub Torsion_Coreflective
    = torsion_coreflector := eq_refl.

Example torsion_record_adj@{u p +} :
  @coreflective_adj Ab@{u p} Torsion_Sub Torsion_Coreflective
    = torsion_coreflection := eq_refl.

(** ** Non-vacuity *)

(* ℤ/2 is torsion, so it is an object of the subcategory, and the unit of
   the coreflection there is invertible. *)
Definition ZMod2_IsTorsion@{a +} : IsTorsion (ZMod2 : AbObject@{a Set Set}) :=
  ZMod2_all_torsion.

Definition ZMod2_Torsion@{u +} : Sub Ab@{u Set} Torsion_Sub :=
  (ZMod2; ZMod2_IsTorsion).

Definition ZMod2_coreflect_iso@{u +} :
  ZMod2_Torsion ≅[Sub Ab@{u Set} Torsion_Sub]
    fobj[coreflector Torsion_Coreflective]
      (fobj[Incl Ab@{u Set} Torsion_Sub] ZMod2_Torsion) :=
  coreflective_unit_iso Torsion_Coreflective ZMod2_Torsion.

(* ℤ × ℤ/2 is not torsion... *)
Lemma MixedAb_not_torsion@{+} : IsTorsion MixedAb → False.
Proof. intro H; exact (mixed_gen_not_torsion (H mixed_gen)). Qed.

(* ...its torsion part is not trivial... *)
Definition mixed_tors_in_TA@{+} : carrier (TorsionAb MixedAb) :=
  existT _ mixed_tors mixed_tors_torsion.

Lemma mixed_tors_in_TA_nonzero@{+} :
  @equiv (carrier (TorsionAb MixedAb)) _ mixed_tors_in_TA
    (cmon_zero (TorsionAb MixedAb)) → False.
Proof. exact mixed_tors_not_zero. Qed.

(* ...and the counit there is not invertible: an inverse would carry the
   generator (1, 0) into TA and back, making it torsion. *)
Theorem torsion_counit_MixedAb_not_iso@{u +} :
  IsIsomorphism (torsion_counit (MixedAb : Ab@{u Set})) → False.
Proof.
  intros [g Hfg _].
  apply mixed_gen_not_torsion.
  apply (torsion_resp MixedAb (projT1 (cmon_map g mixed_gen)) mixed_gen).
  - exact (Hfg mixed_gen).
  - exact (projT2 (cmon_map g mixed_gen)).
Qed.

(* The same at ℤ: its torsion part is trivial. *)
Lemma ZAb_TA_trivial@{+} (x : carrier (TorsionAb ZAb)) :
  @equiv (carrier (TorsionAb ZAb)) _ x (cmon_zero (TorsionAb ZAb)).
Proof. exact (ZAb_torsion_trivial (projT1 x) (projT2 x)). Qed.

(** ** Riehl 5.3.ii at the torsion-free reflection (Mac Lane §IV.3 Ex. 2) *)

Definition TorsionFree_Monad@{u p +} :
  @Monad Ab@{u p} (Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector) :=
  Reflective_Monad TorsionFree_Reflective.

Definition TorsionFree_IdempotentMonad@{u p +} :
  @IdempotentMonad Ab@{u p}
    (Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector)
    TorsionFree_Monad :=
  Reflective_IdempotentMonad TorsionFree_Reflective.

Example torsionfree_monad_obj@{u p +} (A : Ab@{u p}) :
  fobj[Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector] A
    = AbModTorsion A
  := eq_refl.

(* Idempotent.v's correspondence, fed a concrete record: the algebras of
   the induced monad are equivalent to its M-local objects... *)
Definition TorsionFree_EM_MLocal@{u p +} :
  EquivalenceOfCategories
    (@idem_G Ab@{u p} _ TorsionFree_Monad TorsionFree_IdempotentMonad) :=
  @Idempotent_EM_Equivalence Ab@{u p} _ TorsionFree_Monad
    TorsionFree_IdempotentMonad.

(* ...and, Riehl's Proposition 5.3.3 (ii), to the subcategory itself. *)
Definition TorsionFree_EM_Equivalence@{u p +} :
  EquivalenceOfCategories
    (@reflective_comparison Ab@{u p} _ TorsionFree_Reflective) :=
  Reflective_EM_Equivalence TorsionFree_Reflective.

Definition TorsionFree_Incl_Monadic@{u p +} :
  Monadic (Incl Ab@{u p} TorsionFree_Sub) :=
  Reflective_Monadic TorsionFree_Reflective.
