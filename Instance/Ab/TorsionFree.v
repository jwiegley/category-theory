(** * Torsion-free abelian groups are a full reflective subcategory of Ab

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer GTM 5, §IV.3, printed p. 92, Exercise 2.  Verbatim
          from the page: "2. Show that the torsion-free abelian groups
          form a full reflective subcategory of Ab."  The paragraph just
          above the exercises on that page supplies the vocabulary and
          is NOT this item's scope: "A coreflective subcategory of Ab is
          the full subcategory of all torsion abelian groups (a group is
          torsion if all elements have finite order); the coreflector
          sends each abelian group A to the subgroup TA of all elements
          of finite order in A."  Catalog id: maclane:IV.3:ex2.

    ** What is delivered

    [TorsionFree_Reflective : Reflective TorsionFree_Sub] -- the record
    of Construction/Reflective.v:60, whose three fields are exactly the
    three things Mac Lane's phrase names: FULLNESS of the subcategory
    ([TorsionFree_Full]), a REFLECTOR ([TorsionFree_reflector]), and the
    ADJUNCTION ([TorsionFree_adj]) making it left adjoint to the
    inclusion.  Read the packaging precisely: the adjunction ALONE is
    strictly less than the record, and the mismatch is pinned as this
    development's typing negative.

    Around it: the torsion predicate [torsion_mem] with its five closure
    lemmas, the torsion subgroup [TorsionSub]/[TorsionAb] and its
    inclusion [torsion_incl], the torsion-free predicate [TorsionFree],
    the full subcategory [TorsionFree_Sub]/[TorsionFreeAb] with the
    inclusion proved Full AND Faithful, the quotient [AbModTorsion] with
    [AbModTorsion_TorsionFree], the universal property
    [torsion_universal] and its packaging [torsion_universal_arrow], and
    the counit corollary [torsionfree_reflect_iso] -- for a torsion-free
    B, B/T(B) ≅ B -- instantiated at ℤ as [ZAb_reflect_iso].

    ** The route

    Universal arrows, exactly the path Instance/Grp/Abelianize.v takes
    for §III.1 Exercise 3: state the ∃! ([torsion_universal],
    Abelianize.v:305's shape), package it with
    Theory/Universal/Arrow.v:158's [universal_arrow_from_UMP]
    ([torsion_universal_arrow], Abelianize.v:328), then read the functor
    and the adjunction off :295's
    [LeftAdjointFunctorFromUniversalArrows] and :324's
    [AdjunctionFromUniversalArrows] with no further proof.  Nothing in
    that chain is re-derived here.

    ** Reused, and what that saves

    - Instance/Ab.v: [AbObject] (:115), [AbHom] (:184), [Ab] (:201),
      [ab_map_neg] (:186), and -- the load-bearing one -- the image
      quotient [AbQuotient] (:472) with [ab_coset_eq] (:427) and
      [ab_quot_proj] (:520).  A/T(A) is that PRE-EXISTING quotient
      applied to the subgroup inclusion; NO new quotient machinery is
      built here, and no coset object is formed anywhere in this file.
    - Instance/Ab/DirectedColimit.v: [AbSubgroup] (:273),
      [AbSubgroupAb] (:309), [absub_incl] (:333).  The torsion subgroup
      is that record, not a third subgroup record; the other two in tree
      are this one and Instance/Ab/Character/Finite.v:624's [Subgroup],
      which additionally demands DECIDABLE membership and so cannot host
      a torsion predicate whose exponent is found rather than decided.
    - Instance/Ab/Monoidal.v: the ℕ-action [nat_smul] (:179) with
      [nat_smul_respects] (:185), [_add] (:194), [_plus] (:204),
      [_zero] (:218), [_neg] (:226), [_hom] (:235); [ZAb] (:416),
      [ZAb_one] (:422), [nat_smul_int_one] (:428).
    - Adjunction/Unitalization.v:448's [nat_smul_mul] -- see the closure
      note below for why it is required rather than restated.
    - Construction/Subcategory.v: [Subcategory] (:36), [Sub] (:55),
      [Incl] (:64), [Incl_Faithful] (:89), [Full] (:99),
      [Full_Implies_Full_Functor] (:104).  The trivially-true [shom] is
      Instance/Rng.v:403's [CRng_Sub] pattern, and [Full] is written
      qualified for the same reason that file writes it so:
      Construction/Subcategory.v exports its OWN [Full], whose first
      argument is a Category, shadowing Theory/Functor.v's.
    - Construction/Reflective.v: [Reflective] (:60) and
      [reflective_counit_iso].

    NEW here: the torsion predicate and its five closure lemmas,
    torsion-freeness of the quotient, the mediator and the universal
    property, and the three witnesses.

    ** Exponent as data, and no choice principle

    [torsion_mem A a] is [{ k : nat & (0 < k) * (nat_smul A k a ≈ 0) }]
    -- a sigma, so the exponent is DATA and can be READ BACK, which is
    what [AbModTorsion_TorsionFree] does when it multiplies the two
    exponents.  Nothing anywhere in this file extracts a witness from a
    [Prop]-valued existential, so no choice principle appears; the same
    design note Instance/Ab.v:417-420 makes about [ab_coset_eq] being
    [Type]-valued applies verbatim, and it is what lets the coset
    witness be taken apart.  All 58 constants are closed under the
    global context.

    ** Prior art, measured at 9a1fe0f2 (the issue's "Current state" is
       stale and is corrected rather than repeated)

    The issue says the ambient category is missing ("there is no Ab, Grp
    or AbGrp instance") and that "a whole-tree search for 'torsion'
    returns nothing".  Both are false: [Ab] is Instance/Ab.v:201 and
    Instance/Grp.v exists.  A case-insensitive search for 'torsion' over
    the .v files, excluding this file and its probe, returns SEVEN
    lines, in Instance/Ab/Character.v:48 and
    Instance/Ab/Character/NonNatural.v:45,:358,:399,:415,:416,:444; five
    are prose, the sixth is [ZZ_no_2_torsion] (:416), a lemma that
    ℤ has no nonzero 2-torsion -- a statement about one group at one
    exponent, not a torsion predicate -- and the seventh (:444) is that
    lemma's one use.  What IS absent, and is supplied
    here, is a torsion predicate, a torsion subgroup and a torsion-free
    predicate.

    Sharper, and this is the claim worth carrying: [rg -n
    'Build_Reflective'] over the .v files, excluding these two, returns
    exactly ONE hit, Construction/Reflective/Idempotent.v:346 --
    inside [Idempotent_Reflective] (declared at :345), which is over an
    ABSTRACT category with an idempotent monad; every other
    [Reflective]-typed term in tree is a HYPOTHESIS ([Context (R :
    Reflective S)] and the like, in Adjunction/FullFaithful.v,
    Adjunction/Fullness.v,
    Construction/Localization/Universal.v and Idempotent.v itself).  So
    under the criterion "a [Reflective] built at a NAMED concrete
    category" this is the tree's first inhabitant.

    ** The [nat_smul_mul] closure decision, with numbers

    Scalar multiplicativity of the action, [nat_smul (j*k) a ≈ nat_smul
    j (nat_smul k a)], is needed twice: for closure of torsion under
    addition (exponents k and l give k*l) and for torsion-freeness of
    the quotient.  It exists in tree exactly once, at
    Adjunction/Unitalization.v:448.  Criterion for the numbers below:
    transitive in-project .vo dependencies via [coqdep -R . Category],
    excluding the file itself.  This file's closure is 61 modules.
    Dropping [Category.Adjunction.Unitalization] gives 59 -- a delta of
    exactly TWO, [Adjunction/Unitalization.vo] and [Instance/Rg.vo],
    because the remaining 51 modules of Unitalization's own closure (52
    by the same criterion) are already inside this one.  Two is not a
    handful, so the lemma is REQUIRED rather than restated, and no
    duplicate of it is declared here.  Dropping
    [Category.Instance.Ab.Character.Finite] likewise gives 59 (delta
    two: [Instance/Ab/Character.vo] and Finite.v itself), which is why
    [ZMod2] (Finite.v:1813) is reused as the torsion witness rather
    than a local bool group being built; dropping both gives 57, so the
    two deltas are independent.  (A first count read 62/60/60/58: it
    counted the queried module itself, which the stated criterion
    excludes.)

    ** ℤ has five names in tree

    [ring_ab Int_Ring] is named five times: [ZAb]
    (Instance/Ab/Monoidal.v:416), [ab_Z] (Instance/Ab/Coproduct.v:264),
    [Zgroup] (Instance/Ab/Graded.v:281), [Ab_Z]
    (Structure/Kernel/Universal/Examples.v:260) and [ab_int]
    (Instance/Ab/Free.v:865).  This file uses [ZAb] throughout and only
    [ZAb], because [nat_smul_int_one] is stated at it.

    ** Strengths, measured strict-first

    Holding at [eq_refl] (seven occurrences outside comments, all
    outside any rejection):
    the reflector's object part is the quotient
    ([torsion_reflector_obj]); the universal arrow IS [ab_quot_proj] and
    its object IS [TorsionFreeMod] ([torsion_arrow_is_proj],
    [torsion_arrow_obj] -- the Abelianize.v:351 precedent, since
    [universal_arrow_from_UMP] stores the supplied morphism as the
    second projection of the comma object it builds); the quotient's
    zero and addition ARE the base group's ([quot_zero_strict],
    [quot_plus_strict]); the scalar action agrees at every CLOSED scalar
    ([nat_smul_quot_two]); and -- the exercise's second reviewer check
    -- the adjunction's UNIT is the quotient projection applied to any
    element ([torsion_unit_is_proj]).

    Falling back, with the cause diagnosed in each case:

    - The unit as a MORPHISM RECORD is only `≈` the projection
      ([torsion_unit_is_proj_hom]).  Cause:
      [AdjunctionFromUniversalArrows] builds ⌊−⌋ as [fun g => fmap[U] g
      ∘ arrow], so the class unit is a COMPOSITE record, [fmap[Incl] id
      ∘ ab_quot_proj …]; applied to an element that composite reduces,
      as a record it does not.  Note the precedent this development was
      pointed at, Instance/Mod/Free.v:542's [free_module_unit_is_insert],
      is likewise stated POINTWISE and not as a morphism equality.
    - [nat_smul] at a VARIABLE scalar is only Leibniz-equal by induction
      ([nat_smul_quot]).  Cause: the [Fixpoint] is stuck on [k], so
      conversion is left comparing the two [AbObject]s themselves, which
      are not convertible: they differ in their setoid field -- that
      difference being the entire content of the quotient -- and, being
      separately built records, in every law field as well.  The setoid
      field is NOT the discriminating cause, and an audit measured that:
      a variant of [A] agreeing with it on [cmon_setoid], [cmon_zero],
      [cmon_plus] and [ab_neg] and differing in ONE law field alone is
      rejected the same way, while it still agrees at every closed
      scalar.  This is measured rather than predicted: the expectation
      that it would hold on the nose is exactly what the closed-scalar
      case does and the variable case does not.
    - ℤ/T(ℤ) is isomorphic to ℤ but not equal to it: [ZAb_reflect_iso]
      is a pure instantiation of [reflective_counit_iso] with no tactic,
      while [AbModTorsion ZAb = ZAb] is refused.
    - The COUNIT is not read back at all.  It is the other transpose,
      i.e. [unique_obj (ump_universal_arrows …)], and
      [ump_universal_arrows] (Theory/Universal/Arrow.v:139) is closed
      with [Qed], so nothing on that side reduces and no [eq_refl] is
      claimed for it.

    The first THREE fallbacks above are pinned as conversion
    rejections in Test/ProbeTorsionFree371.v, together with the
    record-versus-adjunction mismatch (typing) and two universe
    rejections (formability): six negatives of three kinds, plus one
    scope-free instrument check.  The COUNIT is NOT among them --
    nothing is claimed about it in either direction, and no rejection
    naming it is stated.  This file itself carries no rejection at all,
    so it contributes nothing to [make todo].

    ** Universes

    Measured with [Set Printing Universes] on all 58 constants, reading
    BOTH the binder and the constraint block.  NO constraint block of
    any constant carries a universe EQUATION -- every entry is [<] or
    [<=].  Two identifications nevertheless sit in BINDERS, where a
    reader of the blocks alone would miss them, and both are the
    DONORS'.  First, TWENTY-FOUR of the 58 -- exactly the constants that
    mention a hom-set of [Ab] or the quotient, from [AbModTorsion] and
    [torsion_incl] through [torsion_universal_arrow] and the three
    [torsion_med] obligations, and NONE of the torsion predicate's own
    ([torsion_mem] and its five closure lemmas, [TorsionSub],
    [TorsionFree]; the witness [MixedAb] binds no group at all) -- bind
    the group at [AbObject@{u u u}], carrier, relation and proof
    universes identified: [Print Ab] with universes shows
    [obj := AbObject@{u0 u0 u0}], so an [AbObject] whose three levels
    are declared strictly apart is not an object of [Ab] (probed), and
    [AbQuotient] and [absub_incl] carry universe equations of their own
    ([u = u0 ... u = u4], and [u = u0], [u = u1]).  Second,
    the hom-with-proof identification that [Subcategory] and
    [Reflective] carry ([Category@{u u0 u0}], [Category@{u3 u5 u5}]).
    Neither is introduced here and neither is claimed unavoidable.  The
    second is guarded by the probe's two formability rejections, where
    naming a hom-set and an identity at hom-strictly-below-proof levels
    succeeds while [Subcategory] is refused; read the second rejection
    at its strength -- it names [Reflective] but fires at its
    [Subcategory] ARGUMENT with the identical message, since
    [Reflective] takes a [Subcategory] and cannot be tested apart from
    it (the trap Test/ProbeRingLattice340.v records for
    [MonoidObject]), so whether [Reflective] identifies anything OF ITS
    OWN is not measured here.

    ELEVEN of the 58 constants carry a [Set] token: [MixedAb],
    [ZMod2_all_torsion], [ZMod2_not_TorsionFree], [ZMod2_quot_collapses],
    [mixed_gen], [mixed_gen_not_quot_zero], [mixed_gen_not_torsion],
    [mixed_quot_merges], [mixed_tors], [mixed_tors_not_zero],
    [mixed_tors_torsion] -- exactly the ℤ/2 and mixed witness block,
    from [ZMod2]'s [bool] carrier, and always as a BOUND ([Set < u]),
    never an equation.  The general theory, the reflector, the
    adjunction, [TorsionFree_Reflective] and the whole ℤ block are
    [Set]-free; in particular the ℤ results route through [ZAb_one]
    rather than a bare literal at a [carrier ZAb] position, which is
    Instance/Ab/Monoidal.v:418-421's own design note.

    ** NOT delivered

    - The COREFLECTION of the page's preceding paragraph -- torsion
      groups as a coreflective subcategory, with TA as coreflector.
      [Coreflective] is Construction/Reflective.v:85 and the torsion
      subgroup built here is its object part, but that is a different
      catalog item and nothing here states or proves it.
    - Functoriality of [TorsionSub] or of [TorsionAb] in A; no
      naturality of the torsion inclusion.
    - The idempotent monad of the reflection.
      Construction/Reflective/Idempotent.v gives it by instantiation
      from [TorsionFree_Reflective]; that instantiation is not made.
    - The [Grp] analogue, divisible groups, p-primary or p-torsion
      refinements, and any decision procedure for torsion.
    - No claim that [AbModTorsion] is the categorical cokernel of
      [torsion_incl], and no [HasCokernels]/[HasCoequalizers] instance.
    - No uniqueness statement for the reflector beyond what
      [torsion_universal] and [reflective_counit_iso] give.

    ** Corrections to the brief that guided this file

    Each is a measurement, not an opinion.  (1) The brief expected
    [nat_smul (AbModTorsion A) k x = nat_smul A k x] to hold at
    [eq_refl]; it does not at a variable [k], for the reason above --
    the brief anticipated the possibility and asked for it to be pinned,
    which is what happened.  (2) It warned that requiring
    Adjunction/Unitalization pulls "the whole Rg/Dorroh development";
    the measured delta is two modules, so the lemma is required.  (3) It
    cited Instance/Mod/Free.v's unit readback as a MORPHISM-level
    precedent for a strict unit; that constant is pointwise, and so is
    the one here.  (4) It suggested [nat_smul_int_one] might suffice for
    torsion-freeness of ℤ; it does not, being about the generator only,
    so [nat_smul_ZAb] is proved for an arbitrary integer -- but
    [nat_smul_int_one] IS reused, in [mixed_gen_not_torsion].  Every
    other donor line number the brief gave was re-grepped here and is
    correct. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Torsion elements *)

Definition torsion_mem (A : AbObject) (a : carrier A) : Type :=
  { k : nat & ((0 < k)%nat * (nat_smul A k a ≈ cmon_zero A))%type }.

Definition torsion_resp (A : AbObject) (a b : carrier A) :
  a ≈ b → torsion_mem A a → torsion_mem A b.
Proof.
  intros Hab [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite <- (nat_smul_respects A k a b Hab).
  exact Hka.
Defined.

Definition torsion_zero (A : AbObject) : torsion_mem A (cmon_zero A).
Proof.
  exists 1%nat; split; [ lia | ].
  apply nat_smul_zero.
Defined.

Lemma torsion_scale (A : AbObject) (j k : nat) (a : carrier A) :
  nat_smul A k a ≈ cmon_zero A →
  nat_smul A (j * k) a ≈ cmon_zero A.
Proof.
  intro Hk.
  rewrite nat_smul_mul, Hk.
  apply nat_smul_zero.
Defined.

Definition torsion_plus (A : AbObject) (a b : carrier A) :
  torsion_mem A a → torsion_mem A b →
  torsion_mem A (cmon_plus A a b).
Proof.
  intros [k [Hk Hka]] [l [Hl Hlb]].
  exists (k * l)%nat; split; [ lia | ].
  assert (Ha : nat_smul A (k * l) a ≈ cmon_zero A).
  { rewrite (Nat.mul_comm k l).
    exact (torsion_scale A l k a Hka). }
  assert (Hb : nat_smul A (k * l) b ≈ cmon_zero A).
  { exact (torsion_scale A k l b Hlb). }
  rewrite nat_smul_plus, Ha, Hb.
  apply cmon_plus_zero_l.
Defined.

Definition torsion_neg (A : AbObject) (a : carrier A) :
  torsion_mem A a → torsion_mem A (ab_neg A a).
Proof.
  intros [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite nat_smul_neg, Hka.
  apply ab_neg_zero.
Defined.

Definition TorsionSub (A : AbObject) : AbSubgroup A := {|
  absub_mem   := torsion_mem A;
  absub_resp  := torsion_resp A;
  absub_zero  := torsion_zero A;
  absub_plus  := torsion_plus A;
  absub_neg   := torsion_neg A
|}.

Definition TorsionAb (A : AbObject) : AbObject :=
  AbSubgroupAb (TorsionSub A).

Definition torsion_incl (A : AbObject) : TorsionAb A ~{Ab}~> A :=
  absub_incl (TorsionSub A).

(** * Torsion-free groups *)

Definition TorsionFree (A : AbObject) : Type :=
  ∀ (a : carrier A) (k : nat),
    (0 < k)%nat → nat_smul A k a ≈ cmon_zero A → a ≈ cmon_zero A.

Definition TorsionFree_Sub : Subcategory Ab :=
  @Build_Subcategory Ab
    TorsionFree
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TorsionFreeAb : Category := Sub Ab TorsionFree_Sub.

Lemma TorsionFree_Full :
  Category.Construction.Subcategory.Full Ab TorsionFree_Sub.
Proof. intros x y ox oy g; exact I. Defined.

Lemma TorsionFree_Incl_Full :
  Functor.Full (Incl Ab TorsionFree_Sub).
Proof. exact (Full_Implies_Full_Functor Ab TorsionFree_Sub
                TorsionFree_Full). Defined.

Lemma TorsionFree_Incl_Faithful :
  Functor.Faithful (Incl Ab TorsionFree_Sub).
Proof. exact (Incl_Faithful Ab TorsionFree_Sub). Defined.

(** * The quotient by the torsion subgroup *)

Definition AbModTorsion (A : AbObject) : AbObject :=
  AbQuotient (torsion_incl A).

(* The quotient reuses [A]'s own zero and addition, so those two fields
   agree with [A]'s ON THE NOSE ([quot_zero_strict], [quot_plus_strict])
   and the scalar action agrees at every CLOSED scalar
   ([nat_smul_quot_two]).  At a VARIABLE scalar it does not: [nat_smul]
   is a [Fixpoint] stuck on [k], so conversion is left comparing the two
   [AbObject]s themselves, which differ in their setoid field and in
   every law field (one differing law field already suffices, measured
   in the header).  The agreement is therefore a one-line induction
   rather than [eq_refl] --
   measured, and the [eq_refl] form is pinned in
   Test/ProbeTorsionFree371.v. *)

Example quot_zero_strict (A : AbObject) :
  cmon_zero (AbModTorsion A) = cmon_zero A := eq_refl.

Example quot_plus_strict (A : AbObject) (x y : carrier A) :
  cmon_plus (AbModTorsion A) x y = cmon_plus A x y := eq_refl.

Example nat_smul_quot_two (A : AbObject) (x : carrier A) :
  nat_smul (AbModTorsion A) 2 x = nat_smul A 2 x := eq_refl.

Lemma nat_smul_quot (A : AbObject) (k : nat) (x : carrier A) :
  nat_smul (AbModTorsion A) k x = nat_smul A k x.
Proof.
  induction k as [|j IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

Definition quot_eq_intro (A : AbObject) (x y t : carrier A)
    (Ht : torsion_mem A t) (H : x ≈ cmon_plus A y t) :
  @equiv (carrier (AbModTorsion A)) _ x y.
Proof. exists (existT _ t Ht); exact H. Defined.

Definition quot_eq_elim (A : AbObject) (x y : carrier A) :
  @equiv (carrier (AbModTorsion A)) _ x y →
  { t : carrier A & (torsion_mem A t * (x ≈ cmon_plus A y t))%type }.
Proof. intros [[t Ht] H]; exists t; split; assumption. Defined.

Definition AbModTorsion_TorsionFree (A : AbObject) :
  TorsionFree (AbModTorsion A).
Proof.
  intros x k Hk Hx.
  rewrite nat_smul_quot in Hx.
  destruct (quot_eq_elim A _ _ Hx) as [t [[l [Hl Hlt]] Hxt]].
  apply (quot_eq_intro A x (cmon_zero A) x).
  - exists (l * k)%nat; split; [ lia | ].
    rewrite nat_smul_mul.
    assert (Hkx : nat_smul A k x ≈ t).
    { transitivity (cmon_plus A (cmon_zero A) t).
      - exact Hxt.
      - apply cmon_plus_zero_l. }
    rewrite Hkx, Hlt.
    reflexivity.
  - symmetry; apply cmon_plus_zero_l.
Defined.

Definition TorsionFreeMod (A : AbObject) : TorsionFreeAb :=
  (AbModTorsion A; AbModTorsion_TorsionFree A).

(** * The universal property *)

Definition torsion_kills {A B : AbObject} (HB : TorsionFree B)
    (f : A ~{Ab}~> B) (t : carrier A) :
  torsion_mem A t → cmon_map f t ≈ cmon_zero B.
Proof.
  intros [k [Hk Hkt]].
  apply (HB _ k Hk).
  rewrite <- nat_smul_hom, Hkt.
  apply cmon_map_zero.
Defined.

Program Definition torsion_med {A B : AbObject} (HB : TorsionFree B)
    (f : A ~{Ab}~> B) : AbModTorsion A ~{Ab}~> B :=
  {| cmon_map := {| morphism := fun x : carrier A => cmon_map f x |} |}.
Next Obligation.
  intros x y Hxy.
  destruct (quot_eq_elim A x y Hxy) as [t [Ht Hxt]].
  rewrite Hxt, cmon_map_plus, (torsion_kills HB f t Ht).
  apply cmon_plus_zero_r.
Qed.
Next Obligation. apply cmon_map_zero. Qed.
Next Obligation. apply cmon_map_plus. Qed.

Theorem torsion_universal (A : AbObject) :
  ∀ (d : TorsionFreeAb) (f : A ~{Ab}~> Incl Ab TorsionFree_Sub d),
    ∃! g : TorsionFreeMod A ~{TorsionFreeAb}~> d,
      f ≈ fmap[Incl Ab TorsionFree_Sub] g
             ∘ ab_quot_proj (torsion_incl A).
Proof.
  intros d f.
  unshelve eexists.
  - exact (torsion_med `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition torsion_universal_arrow (A : AbObject)
  : @UniversalArrow Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub) :=
  @universal_arrow_from_UMP Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (TorsionFreeMod A) (ab_quot_proj (torsion_incl A))
    (torsion_universal A).

Definition TorsionFree_reflector : Ab ⟶ TorsionFreeAb :=
  LeftAdjointFunctorFromUniversalArrows (Incl Ab TorsionFree_Sub)
    torsion_universal_arrow.

Definition TorsionFree_adj
  : TorsionFree_reflector ⊣ Incl Ab TorsionFree_Sub :=
  AdjunctionFromUniversalArrows (Incl Ab TorsionFree_Sub)
    torsion_universal_arrow.

Definition TorsionFree_Reflective : Reflective TorsionFree_Sub :=
  @Build_Reflective Ab TorsionFree_Sub TorsionFree_Full
    TorsionFree_reflector TorsionFree_adj.

(** * Strict readbacks *)

Example torsion_reflector_obj (A : AbObject) :
  `1 (fobj[TorsionFree_reflector] A) = AbModTorsion A := eq_refl.

Example torsion_arrow_is_proj (A : AbObject) :
  @arrow Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (torsion_universal_arrow A)
    = ab_quot_proj (torsion_incl A) := eq_refl.

Example torsion_arrow_obj (A : AbObject) :
  @arrow_obj Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (torsion_universal_arrow A)
    = TorsionFreeMod A := eq_refl.

Definition torsion_unit (A : AbObject)
  : A ~{Ab}~> Incl Ab TorsionFree_Sub (fobj[TorsionFree_reflector] A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ TorsionFree_adj A.

Example torsion_unit_is_proj (A : AbObject) (a : carrier A) :
  cmon_map (torsion_unit A) a = cmon_map (ab_quot_proj (torsion_incl A)) a
  := eq_refl.

Lemma torsion_unit_is_proj_hom (A : AbObject) :
  torsion_unit A ≈ ab_quot_proj (torsion_incl A).
Proof. intro a; reflexivity. Defined.

(** * The counit at a torsion-free group *)

Definition torsionfree_reflect_iso (x : TorsionFreeAb) :
  fobj[TorsionFree_reflector] (Incl Ab TorsionFree_Sub x)
    ≅[TorsionFreeAb] x :=
  reflective_counit_iso TorsionFree_Reflective x.

(** * Non-vacuity: the integers *)

Lemma nat_smul_ZAb (k : nat) (n : carrier ZAb) :
  nat_smul ZAb k n = Z.mul (Z.of_nat k) n.
Proof.
  induction k as [|j IH].
  - reflexivity.
  - change (nat_smul ZAb (S j) n) with (Z.add n (nat_smul ZAb j n)).
    rewrite IH; lia.
Qed.

(* The case split on [Z.mul_eq_0] lands in [or], which is [Prop] and
   cannot be eliminated into the [Type]-sorted [≈]; it is therefore made
   inside this [Prop]-valued lemma and consumed by [exact] below. *)
Lemma ZAb_torsionfree_elt (n : carrier ZAb) (k : nat) :
  (0 < k)%nat → Z.mul (Z.of_nat k) n = 0%Z → n = 0%Z.
Proof.
  intros Hk H.
  apply Z.mul_eq_0 in H.
  destruct H as [Hz|Hz]; [ lia | exact Hz ].
Qed.

Definition ZAb_TorsionFree : TorsionFree ZAb.
Proof.
  intros n k Hk H.
  assert (H' : Z.mul (Z.of_nat k) n = 0%Z).
  { rewrite <- nat_smul_ZAb; exact H. }
  exact (ZAb_torsionfree_elt n k Hk H').
Defined.

Lemma ZAb_torsion_trivial (n : carrier ZAb) :
  torsion_mem ZAb n → n = 0%Z.
Proof.
  intros [k [Hk Hkn]].
  exact (ZAb_TorsionFree n k Hk Hkn).
Qed.

Definition ZAb_TF : TorsionFreeAb := (ZAb; ZAb_TorsionFree).

(* ℤ/T(ℤ) ≅ ℤ, by pure instantiation of the counit isomorphism -- no
   tactic, and no fact about ℤ beyond [ZAb_TorsionFree].  The two are NOT
   equal: [AbModTorsion ZAb] carries the coarsened setoid, and the
   [eq_refl] form is pinned in Test/ProbeTorsionFree371.v. *)
Definition ZAb_reflect_iso :
  fobj[TorsionFree_reflector] (Incl Ab TorsionFree_Sub ZAb_TF)
    ≅[TorsionFreeAb] ZAb_TF :=
  torsionfree_reflect_iso ZAb_TF.

(** * Non-vacuity: ℤ/2 is all torsion *)

Definition ZMod2_all_torsion (b : carrier ZMod2) : torsion_mem ZMod2 b.
Proof.
  exists 2%nat; split; [ lia | ].
  destruct b; reflexivity.
Defined.

Lemma ZMod2_not_TorsionFree : TorsionFree ZMod2 → False.
Proof.
  intro H.
  destruct (ZMod2_all_torsion true) as [k [Hk Hkt]].
  assert (Hb : true = false) by exact (H true k Hk Hkt).
  discriminate.
Qed.

Example ZMod2_quot_collapses :
  @equiv (carrier (AbModTorsion ZMod2)) _ true false.
Proof.
  apply (quot_eq_intro ZMod2 true false true).
  - exact (ZMod2_all_torsion true).
  - reflexivity.
Defined.

(** * Non-vacuity: a mixed group *)

Definition MixedAb : AbObject := Ab_product ZAb ZMod2.

Definition mixed_tors : carrier MixedAb := (cmon_zero ZAb, true).
Definition mixed_gen : carrier MixedAb := (ZAb_one, false).

Definition mixed_tors_torsion : torsion_mem MixedAb mixed_tors.
Proof.
  exists 2%nat; split; [ lia | ].
  split; reflexivity.
Defined.

(* [mixed_tors] is a torsion element that is not zero, so [TorsionSub] is
   NONTRIVIAL at [MixedAb]; [mixed_gen_not_torsion] makes it PROPER. *)
Lemma mixed_tors_not_zero :
  @equiv (carrier MixedAb) _ mixed_tors (cmon_zero MixedAb) → False.
Proof.
  intros [_ H]; simpl in H; discriminate.
Qed.

Lemma mixed_gen_not_torsion : torsion_mem MixedAb mixed_gen → False.
Proof.
  intros [k [Hk Hkg]].
  assert (Hz : nat_smul ZAb k ZAb_one ≈ cmon_zero ZAb).
  { rewrite <- (nat_smul_hom (Ab_exl ZAb ZMod2) k mixed_gen).
    exact (fst Hkg). }
  rewrite nat_smul_int_one in Hz.
  assert (Hz' : Z.of_nat k = 0%Z) by exact Hz.
  lia.
Qed.

Example mixed_quot_merges :
  @equiv (carrier (AbModTorsion MixedAb)) _ mixed_tors
    (cmon_zero MixedAb).
Proof.
  apply (quot_eq_intro MixedAb mixed_tors (cmon_zero MixedAb) mixed_tors).
  - exact mixed_tors_torsion.
  - split; reflexivity.
Defined.

Lemma mixed_gen_not_quot_zero :
  @equiv (carrier (AbModTorsion MixedAb)) _ mixed_gen
    (cmon_zero MixedAb) → False.
Proof.
  intro H.
  destruct (quot_eq_elim MixedAb _ _ H) as [t [Ht Hgt]].
  apply mixed_gen_not_torsion.
  apply (torsion_resp MixedAb t mixed_gen).
  - rewrite Hgt; symmetry; apply cmon_plus_zero_l.
  - exact Ht.
Qed.
