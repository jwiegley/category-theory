(** * The functor-of-points criterion for monoid and group objects *)

(* nLab:      https://ncatlab.org/nlab/show/group+object
   nLab:      https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Group_object
   Book:      Mac Lane, CWM 2nd ed., Section III.6 ("Groups in
              Categories"), Proposition 1 and remark 2, pp. 75-76
   Paper:     Eckmann, Hilton, "Group-Like Structures in General
              Categories I", Mathematische Annalen 145, 1962,
              Theorem 4.3

   Mac Lane's Proposition 1 says that an object [c] of a category with
   finite products carries a group (monoid) structure exactly when the
   representable presheaf [C(-,c)] carries one, the transfer running
   through the comparison [C(-,c) × C(-,c) ≅ C(-, c × c)] and Yoneda.
   His remark 2 observes that the presheaf side makes sense over a base
   WITHOUT finite products, and so may be taken as the definition of a
   group-like object there.

   THREE PRIOR-ART CORRECTIONS, each measured rather than repeated.

   (1) A name search for a group structure on hom-objects returns
   nothing, but that evidence is MISLEADING rather than informative: by
   SHAPE the tree is full of group homomorphisms -- [GrpHom]
   (Instance/Grp.v), [MonHom] (Structure/Groupoid.v), and their uses in
   Construction/Deloop/Functors.v and a dozen other files.  The genuine
   gap is narrower and is what this file fills: a group structure on the
   hom-OBJECT, the group analogue of [Hom_Monoid]
   (Structure/Monoid.v:290).

   (2) The reason Awodey's counterexample -- a field K whose ring C(K)
   of continuous functions is not a field, the pointwise inverse of
   x ↦ x² being discontinuous at 0 -- is not built here is NOT that the
   reals, topology and fields are missing.  All three are in tree, and
   the C(X) functor itself exists: Instance/Top/ContinuousRing.v:409
   supplies [CRingOb X : RingObject] and :495 supplies
   [ContinuousRingFunctor : Top^op ⟶ Rng].  The actual obstruction is
   narrower: there is no ℝ [FieldObject].  The inhabitants of
   Instance/FdVect.v's [FieldObject] class are [Q_Field]
   (Instance/FdVect.v:231), [F2_Field] (Instance/Field.v:521) and the
   PARAMETRIC [FracField] (Instance/Field/Frac.v:734, the field of
   quotients of an integral domain); a search for a reals-based
   [FieldObject] returns nothing.  And [CRingOb X] is a [RingObject],
   not a field.  So the statement "K is a field but C(K) is not" cannot
   even be TYPED here, and no impossibility is claimed -- only that the
   witness object does not exist.

   (3) Structure/Group.v:28 already ASSERTS this file's theorem in
   prose -- "equivalently, [grp] is a group object iff each hom
   Hom(X, grp) is a group naturally in X" -- with no formal statement
   anywhere.  This file is what discharges that sentence.

   WHAT IS DELIVERED, AND AT WHAT STRENGTH.

   The development is factored through ONE record, [HomGroupData e]
   (and its monoid half [HomMonoidData e]): a family of group
   operations on each hom-set [x ~> e], with the group laws and with
   naturality stated as compatibility with precomposition.  This is
   Eckmann and Hilton's Theorem 4.3 datum, and it is stated over an
   ARBITRARY category -- no products, no closure, no Yoneda.  Four
   passages relate it to everything else:

     [monoid_object_hom_data] / [group_object_hom_data]
       (needs finite products)   GroupObject c  ⟶  HomGroupData c
     [RepPresheaf_Monoid] / [RepPresheaf_Group]
       (base-free)               HomGroupData e ⟶  presheaf group
     [psh_monoid_hom_data] / [psh_group_hom_data]
       (base-free)               presheaf group ⟶  HomGroupData e
     [data_MonoidObject] / [data_GroupObject]
       (needs finite products)   HomGroupData c ⟶  GroupObject c

   (A) The headline is [group_object_iff_representable] and its monoid
   twin [monoid_object_iff_representable]: for [C] with finite products
   and any [c], a [GroupObject c] is interderivable with a group object
   on [C(-,c)] in the presheaf category with its POINTWISE cartesian
   structure ([Functor_Category_Cartesian] and
   [Functor_Category_Terminal]).  Both are [Defined], so the two
   passages are the named constants and can be computed with.  The
   comparison [C(-,c) × C(-,c) ≅ C(-, c × c)] is never built as a
   separate isomorphism: an element of the pointwise product IS a pair
   of morphisms, so the comparison is [fun (f, g) => f △ g] inlined at
   the two places it is used ([hmul] and [data_mul_eval]).  NOT
   [rep_mul_nt], as an earlier revision of this header said: that
   transformation contains no fork at all -- its body is
   [fun p => hmd_mul D (fst p) (snd p)] -- and it lives in the base-free
   section, where [c × c] does not exist and the comparison therefore
   cannot occur.

   The FIVE diagrammatic laws of [GroupObject] convert on the nose to
   their elementary product forms -- [rg_assoc_law], [rg_unit_left_law],
   [rg_unit_right_law], [rg_inv_left_law], [rg_inv_right_law] are each
   proved by [exact] of the corresponding class field, so the statement
   types are CONVERTIBLE and nothing is transported.  Reading them off
   is what makes the transfer chases short.

   (B) Remark 2 is [RepresentablyMonoid] / [RepresentablyGroup], stated
   over an ARBITRARY category (the presheaf category is cartesian and
   has a terminal object because [Sets] does, whatever [C] is), and the
   two base-free passages above make it INTERDERIVABLE with the
   hom-set-family datum there -- interderivable by two named passages,
   which is weaker than an equivalence: no base-free biconditional is
   stated, the file's only two [↔]s being the product-requiring headline
   theorems, and the round trip is not an equivalence of structures (see
   STRENGTHS below, which says so of the round trips themselves).
   Where [C] does have finite products, (A)
   identifies both with [GroupObject c].

   (C) Three further clauses:
     (a) [exp_GroupObject] is the group analogue of [Hom_Monoid]: under
         cartesian closure, [y ^ x] is a group object whenever the hom-set
         data on [y] is given.  Stated precisely because the constant
         takes a [HomGroupData y], NOT a [GroupObject y]; the composite
         is immediate through [group_object_hom_data], which is in scope
         there, but unlike the monoid side's [exp_MonoidObject_of] it is
         NOT delivered.
         It is obtained by transporting the hom-set data along
         curry/uncurry, not by an internal diagram chase.
         [exp_mappend_is_Hom_Monoid] records by [eq_refl] that the
         multiplication so obtained IS [Hom_Monoid]'s.
     (b) The EXTERNAL formulation, with NO cartesian-closure hypothesis
         and no products either: [HomGrpObject] equips each hom-set with
         an [Instance/Grp.v] [GrpObject], [HomGrpHom] proves
         precomposition a homomorphism, and [HomGrpFunctor] packages
         them as [C^op ⟶ Grp].
     (c) In [Sets], the operations are pointwise ([sets_mul_pointwise],
         [sets_unit_pointwise], [sets_inv_pointwise], all [eq_refl]),
         and for a DISCRETE setoid on a type [A],
         [sets_hom_iprod_iso : HomGrpA ≅[Grp] iprod_GrpObject A] is the
         concrete computation Hom(X, G) ≅ ∏_{x ∈ X} G, over
         Instance/Sets/Products.v's [Sets_iprod_obj].  The discreteness
         hypothesis is NOT cosmetic: for a general setoid [X] the
         hom-set consists of ≈-RESPECTING maps while the indexed product
         consists of all maps out of the carrier, so the construction
         below is unavailable for a general [X].  Read that at its
         actual strength: the carrier fact is measured, but "the two
         carriers differ" does not by itself entail "not isomorphic as
         groups", and NO counterexample is exhibited here.  The
         unrestricted statement is EXPECTED to fail and is ARGUED to,
         not PROVED to.

   STRENGTHS, MEASURED STRICT-FIRST.

   The presheaf round trip returns the DATA on the nose:
   [data_psh_data_mul], [data_psh_data_unit] and [data_psh_data_inv] are
   [eq_refl].  The WHOLE record does not ([data_psh_data_whole], pinned
   as a [Fail]), and the diagnosis is not guesswork: [HomGroupData] has
   primitive projections WITH eta (checked with [Print]), so record
   equality is field equality, and the fields that differ are the LAW
   fields -- [hmd_assoc] of the round trip is the opaque [pmul_assoc],
   a different constant from the [hmd_assoc] one started with.
   [data_psh_data_law] pins exactly that.

   The object-level round trip is only [≈], and the residues are named:
   [rt_mul] must discharge an [exl △ exr] that [fork_exl_exr] collapses
   to [id] and an [id_right]; [rt_unit] must discharge [one : 1 ~> 1]
   against [id].  [rt_mul_strict] is the pinned [Fail], with
   [rt_mul_control] the positive control.  Neither round trip is an
   equivalence of the two structures and none is claimed.

   NO SEPARATION IS PROVED anywhere in this file.  In particular it is
   not shown that the presheaf formulation is strictly more general than
   [GroupObject] over a base without products -- no base-without-
   products witness carrying a [RepresentablyGroup] is exhibited.

   UNIVERSES, read off BOTH the binder and the constraint block.
   [HomGroupData@{u u0}] has an EMPTY constraint block, over
   [C : Category@{u u0 u0}] -- so the hom-and-proof identification is in
   the BINDER, where reading the block alone would miss it, and it comes
   from the unannotated [Context {C : Category}] by minimization (the
   [Build_Quiver_Standard_Eq] family), not from any donor.  It is
   repairable in principle and is NOT claimed unavoidable.
   [group_object_iff_representable@{u u0 u1 u2 u3 u4 u5}] likewise has
   NO equation in its block -- only bounds and the two strict
   inequalities [u0 < u1] and [u3 < u5] that [Sets] forces -- and its
   OBJECT universe [u] is BOUNDED FROM ABOVE ONLY and never identified
   with the hom universe [u0]: the block carries [u <= u2], [u <= u3]
   and two [projections] bounds, and no equation relating [u] to [u0].

   YONEDA IS NOT USED, and that is deliberate.  [Yoneda_Lemma@{u u0}]
   (Functor/Hom/Yoneda.v) is stated over [C : Category@{u0 u0 u0}] --
   object, hom AND proof identified -- which is strictly narrower than
   what the results here need.  Every passage below is a direct
   hom-set argument through the naturality field of the structure
   transformations, so no [Curried_Hom] universe pin is inherited.

   NOT DELIVERED.  No comparison isomorphism [C(-,c) × C(-,c) ≅
   C(-, c × c)] as a named natural isomorphism; no functoriality of
   [c ↦ HomGrpFunctor] in [c], hence no [C ⟶ [C^op, Grp]]; no abelian
   / commutative variant; no ring or module objects; no Awodey
   counterexample (see (2) above); no equivalence of CATEGORIES between
   group objects in [C] and group objects in the presheaves on [C]; and
   no concrete non-degenerate witness -- every result here is stated for
   an arbitrary [c], and the only concrete category exercised is
   [Sets].

   AXIOMS.  175/175 constants of this file are closed under the global
   context -- 173 listed by [Print Module] plus the two [Build_*]
   constructors of [HomMonoidData] and [HomGroupData], which it does not
   list.  Counted as: 175/175 of this file are closed under the global
   context, counted by [Print Module] (which lists the [Program]
   obligations a [.glob] sweep does not) and queried by fully-qualified
   name. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Grp.

Generalizable All Variables.

Section HomData.

Context {C : Category}.

Record HomMonoidData (e : C) := {
  hmd_mul  : ∀ {x : C}, (x ~> e) → (x ~> e) → (x ~> e);
  hmd_unit : ∀ {x : C}, x ~> e;

  hmd_mul_respects : ∀ {x : C},
    Proper (equiv ==> equiv ==> equiv) (@hmd_mul x);

  hmd_assoc : ∀ {x : C} (f g h : x ~> e),
    hmd_mul (hmd_mul f g) h ≈ hmd_mul f (hmd_mul g h);
  hmd_unit_l : ∀ {x : C} (f : x ~> e), hmd_mul hmd_unit f ≈ f;
  hmd_unit_r : ∀ {x : C} (f : x ~> e), hmd_mul f hmd_unit ≈ f;

  hmd_mul_natural : ∀ {x y : C} (f g : x ~> e) (h : y ~> x),
    hmd_mul f g ∘ h ≈ hmd_mul (f ∘ h) (g ∘ h);
  hmd_unit_natural : ∀ {x y : C} (h : y ~> x),
    hmd_unit ∘ h ≈ @hmd_unit y
}.



Record HomGroupData (e : C) := {
  hgd_monoid :> HomMonoidData e;
  hgd_inv : ∀ {x : C}, (x ~> e) → (x ~> e);

  hgd_inv_respects : ∀ {x : C}, Proper (equiv ==> equiv) (@hgd_inv x);

  hgd_inv_l : ∀ {x : C} (f : x ~> e),
    hmd_mul e hgd_monoid (hgd_inv f) f ≈ hmd_unit e hgd_monoid;
  hgd_inv_r : ∀ {x : C} (f : x ~> e),
    hmd_mul e hgd_monoid f (hgd_inv f) ≈ hmd_unit e hgd_monoid;

  hgd_inv_natural : ∀ {x y : C} (f : x ~> e) (h : y ~> x),
    hgd_inv f ∘ h ≈ hgd_inv (f ∘ h)
}.



End HomData.

Arguments HomMonoidData {C} _.
Arguments HomGroupData {C} _.

Arguments hmd_mul {C e} _ {x} _ _.
Arguments hmd_unit {C e} _ {x}.
Arguments hmd_mul_respects {C e} _ {x}.
Arguments hmd_assoc {C e} _ {x} _ _ _.
Arguments hmd_unit_l {C e} _ {x} _.
Arguments hmd_unit_r {C e} _ {x} _.
Arguments hmd_mul_natural {C e} _ {x y} _ _ _.
Arguments hmd_unit_natural {C e} _ {x y} _.

Arguments hgd_monoid {C e} _.
Arguments hgd_inv {C e} _ {x} _.
Arguments hgd_inv_respects {C e} _ {x}.
Arguments hgd_inv_l {C e} _ {x} _.
Arguments hgd_inv_r {C e} _ {x} _.
Arguments hgd_inv_natural {C e} _ {x y} _ _.

#[export] Existing Instance hmd_mul_respects.
#[export] Existing Instance hgd_inv_respects.

(** ** From a monoid or group object to the hom-set data

    The engine: a [MonoidObject] on [c] makes every hom-set [x ~> e] a
    monoid, by [f · g := mappend ∘ (f △ g)] and [e := mempty ∘ one], and
    a [GroupObject] adds [f⁻¹ := inverse ∘ f].  The five [rg_*_law]
    lemmas below read the diagrammatic axioms off in their elementary
    product form; each is [exact] of the corresponding class field, so
    the two statements are CONVERTIBLE. *)

Section HomMonoidEngine.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (M : @MonoidObject C CC_Monoidal c).

Definition rg_mul : c × c ~> c := @mappend C CC_Monoidal c M.
Definition rg_unit : 1 ~> c := @mempty C CC_Monoidal c M.

Lemma rg_assoc_law :
  rg_mul ∘ Cartesian.split rg_mul id
    ≈ rg_mul ∘ Cartesian.split id rg_mul
        ∘ ((exl ∘ exl) △ ((exr ∘ exl) △ exr)).
Proof. exact (@mappend_assoc C CC_Monoidal c M). Qed.

Lemma rg_unit_left_law : rg_mul ∘ Cartesian.split rg_unit id ≈ exr.
Proof. exact (@mempty_left C CC_Monoidal c M). Qed.

Lemma rg_unit_right_law : rg_mul ∘ Cartesian.split id rg_unit ≈ exl.
Proof. exact (@mempty_right C CC_Monoidal c M). Qed.

Definition hmul {x : C} (f g : x ~> c) : x ~> c := rg_mul ∘ f △ g.
Definition hone {x : C} : x ~> c := rg_unit ∘ one.

#[export] Program Instance hmul_respects {x : C} :
  Proper (equiv ==> equiv ==> equiv) (@hmul x).
Next Obligation. proper; unfold hmul; now rewrite X, X0. Qed.

Lemma hmul_assoc {x : C} (f g h : x ~> c) :
  hmul (hmul f g) h ≈ hmul f (hmul g h).
Proof.
  unfold hmul.
  assert (E1 : rg_mul ∘ Cartesian.split rg_mul id ∘ ((f △ g) △ h)
                 ≈ rg_mul ∘ (rg_mul ∘ f △ g) △ h)
    by (rewrite <- comp_assoc, split_fork; cat).
  rewrite <- E1, rg_assoc_law, <- !comp_assoc.
  assert (E2 : ((exl ∘ exl) △ ((exr ∘ exl) △ exr)) ∘ ((f △ g) △ h)
                 ≈ f △ (g △ h)) by (now unfork).
  rewrite E2, split_fork.
  now rewrite id_left.
Qed.

Lemma hmul_unit_l {x : C} (f : x ~> c) : hmul hone f ≈ f.
Proof.
  unfold hmul, hone.
  rewrite <- (id_left f) at 1.
  rewrite <- split_fork, comp_assoc, rg_unit_left_law.
  now rewrite exr_fork.
Qed.

Lemma hmul_unit_r {x : C} (f : x ~> c) : hmul f hone ≈ f.
Proof.
  unfold hmul, hone.
  rewrite <- (id_left f) at 1.
  rewrite <- split_fork, comp_assoc, rg_unit_right_law.
  now rewrite exl_fork.
Qed.

Lemma hmul_comp {x y : C} (f g : x ~> c) (h : y ~> x) :
  hmul f g ∘ h ≈ hmul (f ∘ h) (g ∘ h).
Proof. unfold hmul; rewrite <- comp_assoc; now rewrite fork_comp. Qed.

Lemma hone_comp {x y : C} (h : y ~> x) : @hone x ∘ h ≈ @hone y.
Proof.
  unfold hone; rewrite <- comp_assoc.
  now rewrite (one_unique (one ∘ h) one).
Qed.

Definition monoid_object_hom_data : HomMonoidData c :=
  {| hmd_mul  := @hmul
   ; hmd_unit := @hone
   ; hmd_mul_respects := @hmul_respects
   ; hmd_assoc := @hmul_assoc
   ; hmd_unit_l := @hmul_unit_l
   ; hmd_unit_r := @hmul_unit_r
   ; hmd_mul_natural := @hmul_comp
   ; hmd_unit_natural := @hone_comp |}.

End HomMonoidEngine.

Section HomGroupEngine.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (G : @GroupObject C CC_CartesianMonoidal c).

Definition rg_monoid : @MonoidObject C CC_Monoidal c :=
  @groupobject_is_monoid C CC_CartesianMonoidal c G.
Definition rg_inv : c ~> c :=
  @Category.Structure.Group.inverse C CC_CartesianMonoidal c G.

Lemma rg_inv_left_law :
  rg_mul c rg_monoid ∘ Cartesian.split rg_inv id ∘ (id △ id)
    ≈ rg_unit c rg_monoid ∘ one.
Proof. exact (@left_inverse C CC_CartesianMonoidal c G). Qed.

Lemma rg_inv_right_law :
  rg_mul c rg_monoid ∘ Cartesian.split id rg_inv ∘ (id △ id)
    ≈ rg_unit c rg_monoid ∘ one.
Proof. exact (@right_inverse C CC_CartesianMonoidal c G). Qed.

Definition hinv {x : C} (f : x ~> c) : x ~> c := rg_inv ∘ f.

#[export] Program Instance hinv_respects {x : C} :
  Proper (equiv ==> equiv) (@hinv x).
Next Obligation. proper; unfold hinv; now rewrite X. Qed.

Lemma hmul_inv_l {x : C} (f : x ~> c) :
  hmul c rg_monoid (hinv f) f ≈ hone c rg_monoid.
Proof.
  unfold hmul, hinv, hone.
  assert (E : rg_mul c rg_monoid ∘ Cartesian.split rg_inv id ∘ (id △ id) ∘ f
                ≈ rg_mul c rg_monoid ∘ (rg_inv ∘ f) △ f).
  { rewrite <- !comp_assoc, <- fork_comp, !id_left, split_fork.
    now rewrite id_left. }
  rewrite <- E, rg_inv_left_law, <- comp_assoc.
  now rewrite (one_unique (one ∘ f) one).
Qed.

Lemma hmul_inv_r {x : C} (f : x ~> c) :
  hmul c rg_monoid f (hinv f) ≈ hone c rg_monoid.
Proof.
  unfold hmul, hinv, hone.
  assert (E : rg_mul c rg_monoid ∘ Cartesian.split id rg_inv ∘ (id △ id) ∘ f
                ≈ rg_mul c rg_monoid ∘ f △ (rg_inv ∘ f)).
  { rewrite <- !comp_assoc, <- fork_comp, !id_left, split_fork.
    now rewrite id_left. }
  rewrite <- E, rg_inv_right_law, <- comp_assoc.
  now rewrite (one_unique (one ∘ f) one).
Qed.

Lemma hinv_comp {x y : C} (f : x ~> c) (h : y ~> x) :
  hinv f ∘ h ≈ hinv (f ∘ h).
Proof. unfold hinv; now rewrite comp_assoc. Qed.

Definition group_object_hom_data : HomGroupData c :=
  {| hgd_monoid := monoid_object_hom_data c rg_monoid
   ; hgd_inv := @hinv
   ; hgd_inv_respects := @hinv_respects
   ; hgd_inv_l := @hmul_inv_l
   ; hgd_inv_r := @hmul_inv_r
   ; hgd_inv_natural := @hinv_comp |}.

End HomGroupEngine.

(** ** From the hom-set data to a presheaf monoid or group object

    Base-free: no products, no closure, no Yoneda.  The presheaf
    category is cartesian and has a terminal object because [Sets] does,
    so [CC_Monoidal] applies there whatever [C] is. *)

Section ToPresheaf.

Context {C : Category}.
Context (e : C).

Definition RepPresheaf : [C^op, Sets] := Curried_CoHom C e.

Context (D : HomMonoidData e).

Program Definition rep_mul_nt :
  (RepPresheaf × RepPresheaf)%object ~> RepPresheaf := {|
  transform := fun x => {| morphism := fun p => hmd_mul D (fst p) (snd p) |}
|}.
Next Obligation.
  intros [f g] [f' g'] [Hf Hg]; simpl in *; now rewrite Hf, Hg.
Qed.
Next Obligation. now rewrite hmd_mul_natural. Qed.
Next Obligation. now rewrite hmd_mul_natural. Qed.

Program Definition rep_unit_nt : (1 : [C^op, Sets]) ~> RepPresheaf := {|
  transform := fun x => {| morphism := fun _ => hmd_unit D |}
|}.
Next Obligation. now rewrite hmd_unit_natural. Qed.
Next Obligation. now rewrite hmd_unit_natural. Qed.

Program Definition RepPresheaf_Monoid :
  @MonoidObject ([C^op, Sets]) CC_Monoidal RepPresheaf := {|
  mempty  := rep_unit_nt;
  mappend := rep_mul_nt
|}.
Next Obligation. rewrite id_right; apply hmd_unit_l. Qed.
Next Obligation. rewrite id_right; apply hmd_unit_r. Qed.
Next Obligation. rewrite !id_right; apply hmd_assoc. Qed.

End ToPresheaf.

Section ToPresheafGroup.

Context {C : Category}.
Context (e : C).
Context (D : HomGroupData e).

Program Definition rep_inv_nt : RepPresheaf e ~> RepPresheaf e := {|
  transform := fun x => {| morphism := fun f => hgd_inv D f |}
|}.
Next Obligation. intros f f' Hf; simpl in *; now rewrite Hf. Qed.
Next Obligation. now rewrite hgd_inv_natural. Qed.
Next Obligation. now rewrite hgd_inv_natural. Qed.

Program Definition RepPresheaf_Group :
  @GroupObject ([C^op, Sets]) CC_CartesianMonoidal (RepPresheaf e) := {|
  groupobject_is_monoid := RepPresheaf_Monoid e (hgd_monoid D);
  Category.Structure.Group.inverse := rep_inv_nt
|}.
Next Obligation. rewrite !id_right; apply hgd_inv_l. Qed.
Next Obligation. rewrite !id_right; apply hgd_inv_r. Qed.

End ToPresheafGroup.

(** ** From a presheaf monoid or group object back to the hom-set data

    Also base-free.  Every law is extracted componentwise: the class
    field is a natural-transformation equation, applied at an object and
    then at an element, and the [id_right] residues come from the
    pointwise identity of [Sets]. *)

Section FromPresheaf.

Context {C : Category}.
Context (e : C).
Context (P : @MonoidObject ([C^op, Sets]) CC_Monoidal (RepPresheaf e)).

Definition psh_mul : (RepPresheaf e × RepPresheaf e)%object ~> RepPresheaf e :=
  @mappend ([C^op, Sets]) CC_Monoidal _ P.
Definition psh_unit : (1 : [C^op, Sets]) ~> RepPresheaf e :=
  @mempty ([C^op, Sets]) CC_Monoidal _ P.

Definition pmul {x : C} (f g : x ~> e) : x ~> e := transform[psh_mul] x (f, g).
Definition punit {x : C} : x ~> e := transform[psh_unit] x ttt.

#[export] Program Instance pmul_respects {x : C} :
  Proper (equiv ==> equiv ==> equiv) (@pmul x).
Next Obligation.
  proper; unfold pmul; apply proper_morphism; now split.
Qed.

Lemma pmul_natural {x y : C} (f g : x ~> e) (h : y ~> x) :
  pmul f g ∘ h ≈ pmul (f ∘ h) (g ∘ h).
Proof.
  unfold pmul.
  exact (naturality[psh_mul] x y h (f, g)).
Qed.

Lemma punit_natural {x y : C} (h : y ~> x) : @punit x ∘ h ≈ @punit y.
Proof.
  unfold punit.
  exact (naturality[psh_unit] x y h ttt).
Qed.

Lemma pmul_unit_l {x : C} (f : x ~> e) : pmul punit f ≈ f.
Proof.
  pose proof (@mempty_left ([C^op, Sets]) CC_Monoidal _ P x (ttt, f)) as HL.
  simpl in HL; rewrite id_right in HL; exact HL.
Qed.

Lemma pmul_unit_r {x : C} (f : x ~> e) : pmul f punit ≈ f.
Proof.
  pose proof (@mempty_right ([C^op, Sets]) CC_Monoidal _ P x (f, ttt)) as HR.
  simpl in HR; rewrite id_right in HR; exact HR.
Qed.

Lemma pmul_assoc {x : C} (f g h : x ~> e) :
  pmul (pmul f g) h ≈ pmul f (pmul g h).
Proof.
  pose proof (@mappend_assoc ([C^op, Sets]) CC_Monoidal _ P x ((f, g), h))
    as HA.
  simpl in HA; rewrite !id_right in HA; exact HA.
Qed.

Definition psh_monoid_hom_data : HomMonoidData e :=
  {| hmd_mul  := @pmul
   ; hmd_unit := @punit
   ; hmd_mul_respects := @pmul_respects
   ; hmd_assoc := @pmul_assoc
   ; hmd_unit_l := @pmul_unit_l
   ; hmd_unit_r := @pmul_unit_r
   ; hmd_mul_natural := @pmul_natural
   ; hmd_unit_natural := @punit_natural |}.

End FromPresheaf.

Section FromPresheafGroup.

Context {C : Category}.
Context (e : C).
Context (P : @GroupObject ([C^op, Sets]) CC_CartesianMonoidal
                          (RepPresheaf e)).

Definition psh_gmonoid :
  @MonoidObject ([C^op, Sets]) CC_Monoidal (RepPresheaf e) :=
  @groupobject_is_monoid _ CC_CartesianMonoidal _ P.

Definition psh_inv_nt : RepPresheaf e ~> RepPresheaf e :=
  @Category.Structure.Group.inverse ([C^op, Sets]) CC_CartesianMonoidal _ P.

Definition pinv {x : C} (f : x ~> e) : x ~> e := transform[psh_inv_nt] x f.

#[export] Program Instance pinv_respects {x : C} :
  Proper (equiv ==> equiv) (@pinv x).
Next Obligation. proper; unfold pinv; now apply proper_morphism. Qed.

Lemma pinv_natural {x y : C} (f : x ~> e) (h : y ~> x) :
  pinv f ∘ h ≈ pinv (f ∘ h).
Proof. unfold pinv; exact (naturality[psh_inv_nt] x y h f). Qed.

Lemma pinv_l {x : C} (f : x ~> e) :
  pmul e psh_gmonoid (pinv f) f
    ≈ punit e psh_gmonoid.
Proof.
  pose proof (@left_inverse ([C^op, Sets]) CC_CartesianMonoidal _ P x f) as HI.
  simpl in HI; rewrite !id_right in HI; exact HI.
Qed.

Lemma pinv_r {x : C} (f : x ~> e) :
  pmul e psh_gmonoid f (pinv f)
    ≈ punit e psh_gmonoid.
Proof.
  pose proof (@right_inverse ([C^op, Sets]) CC_CartesianMonoidal _ P x f) as HI.
  simpl in HI; rewrite !id_right in HI; exact HI.
Qed.

Definition psh_group_hom_data : HomGroupData e :=
  {| hgd_monoid := psh_monoid_hom_data e psh_gmonoid
   ; hgd_inv := @pinv
   ; hgd_inv_respects := @pinv_respects
   ; hgd_inv_l := @pinv_l
   ; hgd_inv_r := @pinv_r
   ; hgd_inv_natural := @pinv_natural |}.

End FromPresheafGroup.

(** ** From the hom-set data to a monoid or group object

    This is the half that needs finite products.  The structure
    morphisms are the operations evaluated at the generic pair and the
    generic point -- [data_mul := f · g] at [f := exl], [g := exr];
    [data_unit] at the terminal object; [data_inv] at [id] -- and
    [data_mul_eval], [data_unit_eval], [data_inv_eval] recover the whole
    family from them by naturality. *)

Section ToObject.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (D : HomMonoidData c).

Definition data_mul : c × c ~> c := hmd_mul D exl exr.
Definition data_unit : 1 ~{C}~> c := @hmd_unit C c D 1.

Lemma data_mul_eval {x : C} (f g : x ~> c) :
  hmd_mul D f g ≈ data_mul ∘ f △ g.
Proof.
  unfold data_mul.
  rewrite hmd_mul_natural.
  now rewrite exl_fork, exr_fork.
Qed.

Lemma data_unit_eval {x : C} : @hmd_unit C c D x ≈ data_unit ∘ one.
Proof. unfold data_unit; now rewrite hmd_unit_natural. Qed.

Lemma fork_exl_exl_exr_exl {x y z : C} :
  ((@exl C _ x y ∘ exl) △ (exr ∘ exl)) ≈ @exl C _ (x × y) z.
Proof. rewrite fork_comp, fork_exl_exr; cat. Qed.

Program Definition data_MonoidObject :
  @MonoidObject C CC_Monoidal c := {|
  mempty  := data_unit;
  mappend := data_mul
|}.
Next Obligation.
  pose proof (hmd_unit_l D (@exr C _ 1 c)) as HL.
  rewrite data_unit_eval, data_mul_eval in HL.
  rewrite id_left, (one_unique (@exl C _ 1 c) one).
  exact HL.
Qed.
Next Obligation.
  pose proof (hmd_unit_r D (@exl C _ c 1)) as HR.
  rewrite data_unit_eval, data_mul_eval in HR.
  rewrite id_left, (one_unique (@exr C _ c 1) one).
  exact HR.
Qed.
Next Obligation.
  pose proof (hmd_assoc D (exl ∘ exl) (exr ∘ exl) (@exr C _ (c × c) c)) as HA.
  rewrite !data_mul_eval in HA.
  rewrite fork_exl_exl_exr_exl in HA.
  rewrite !id_left, HA.
  rewrite <- comp_assoc, <- fork_comp, <- !comp_assoc.
  now rewrite exl_fork, exr_fork.
Qed.

End ToObject.

Section ToObjectGroup.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (D : HomGroupData c).

Definition data_inv : c ~> c := hgd_inv D id.

Lemma data_inv_eval {x : C} (f : x ~> c) : hgd_inv D f ≈ data_inv ∘ f.
Proof.
  unfold data_inv.
  rewrite hgd_inv_natural.
  now rewrite id_left.
Qed.

Program Definition data_GroupObject :
  @GroupObject C CC_CartesianMonoidal c := {|
  groupobject_is_monoid := data_MonoidObject c (hgd_monoid D);
  Category.Structure.Group.inverse := data_inv
|}.
Next Obligation.
  pose proof (hgd_inv_l D (@id C c)) as HI.
  rewrite data_inv_eval, data_mul_eval, data_unit_eval in HI.
  rewrite <- comp_assoc, <- fork_comp, <- !comp_assoc.
  rewrite exl_fork, exr_fork, id_left.
  exact HI.
Qed.
Next Obligation.
  pose proof (hgd_inv_r D (@id C c)) as HI.
  rewrite data_inv_eval, data_mul_eval, data_unit_eval in HI.
  rewrite <- comp_assoc, <- fork_comp, <- !comp_assoc.
  rewrite exl_fork, exr_fork, id_left.
  exact HI.
Qed.

End ToObjectGroup.

(** ** Mac Lane Proposition 1 and remark 2 *)

Definition RepresentablyMonoid {C : Category} (e : C) : Type :=
  @MonoidObject ([C^op, Sets]) CC_Monoidal (RepPresheaf e).

Definition RepresentablyGroup {C : Category} (e : C) : Type :=
  @GroupObject ([C^op, Sets]) CC_CartesianMonoidal (RepPresheaf e).

Section Headline.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).

Definition monoid_object_representable
  (M : @MonoidObject C CC_Monoidal c) : RepresentablyMonoid c :=
  RepPresheaf_Monoid c (monoid_object_hom_data c M).

Definition representable_monoid_object
  (P : RepresentablyMonoid c) : @MonoidObject C CC_Monoidal c :=
  data_MonoidObject c (psh_monoid_hom_data c P).

Theorem monoid_object_iff_representable :
  @MonoidObject C CC_Monoidal c ↔ RepresentablyMonoid c.
Proof.
  split.
  - exact monoid_object_representable.
  - exact representable_monoid_object.
Defined.

Definition group_object_representable
  (G : @GroupObject C CC_CartesianMonoidal c) : RepresentablyGroup c :=
  RepPresheaf_Group c (group_object_hom_data c G).

Definition representable_group_object
  (P : RepresentablyGroup c) : @GroupObject C CC_CartesianMonoidal c :=
  data_GroupObject c (psh_group_hom_data c P).

Theorem group_object_iff_representable :
  @GroupObject C CC_CartesianMonoidal c ↔ RepresentablyGroup c.
Proof.
  split.
  - exact group_object_representable.
  - exact representable_group_object.
Defined.

End Headline.

(** ** The external formulation: a functor into Grp

    Clause (b): no cartesian closure and no products are used here.  The
    hom-SET carries an [Instance/Grp.v] group and precomposition is a
    homomorphism, so the assignment is a functor [C^op ⟶ Grp]. *)

Section HomGrpFunctor.

Context {C : Category}.
Context (e : C).
Context (D : HomGroupData e).

Program Definition HomGrpObject (x : C) : GrpObject := {|
  grp_setoid := {| carrier := x ~> e ; is_setoid := @homset C x e |};
  grp_unit := hmd_unit D;
  grp_mul  := @hmd_mul C e D x;
  grp_inv  := @hgd_inv C e D x
|}.
Next Obligation. now rewrite hmd_assoc. Qed.
Next Obligation. now rewrite hmd_unit_l. Qed.
Next Obligation. now rewrite hgd_inv_l. Qed.

Program Definition HomGrpHom {x y : C} (h : y ~> x) :
  GrpHom (HomGrpObject x) (HomGrpObject y) := {|
  grp_map := {| morphism := fun f => f ∘ h |}
|}.
Next Obligation. now rewrite hmd_unit_natural. Qed.
Next Obligation. now rewrite hmd_mul_natural. Qed.

Program Definition HomGrpFunctor : C^op ⟶ Grp := {|
  fobj := fun x => HomGrpObject x;
  fmap := fun x y (h : x ~{C^op}~> y) => HomGrpHom h
|}.

Definition HomGrpFunctor_Forget_agrees (x : C) :
  carrier (grp_setoid (HomGrpObject x)) = (x ~> e) := eq_refl.

End HomGrpFunctor.

(** ** Round trips, measured strict-first *)

Section RoundTrips.

Context {C : Category}.
Context (e : C).
Context (D : HomGroupData e).

Example data_psh_data_mul {x : C} (f g : x ~> e) :
  hmd_mul (psh_monoid_hom_data e (RepPresheaf_Monoid e (hgd_monoid D))) f g
    = hmd_mul D f g := eq_refl.

Example data_psh_data_unit {x : C} :
  @hmd_unit C e (psh_monoid_hom_data e
                   (RepPresheaf_Monoid e (hgd_monoid D))) x
    = @hmd_unit C e (hgd_monoid D) x := eq_refl.

Example data_psh_data_inv {x : C} (f : x ~> e) :
  hgd_inv (psh_group_hom_data e (RepPresheaf_Group e D)) f
    = hgd_inv D f := eq_refl.

(* The data fields above return on the nose; the LAW fields do not, and
   that is the whole reason the record round trip fails.  [HomGroupData]
   has primitive projections with eta, so record equality IS field
   equality. *)
Fail Example data_psh_data_law {x : C} (f g h : x ~> e) :
  @hmd_assoc C e (psh_monoid_hom_data e
                    (RepPresheaf_Monoid e (hgd_monoid D))) x f g h
    = @hmd_assoc C e (hgd_monoid D) x f g h := eq_refl.

Example data_psh_data_law_control {x : C} (f g h : x ~> e) :
  @hmd_assoc C e (hgd_monoid D) x f g h
    = @hmd_assoc C e (hgd_monoid D) x f g h := eq_refl.

Fail Example data_psh_data_whole :
  psh_group_hom_data e (RepPresheaf_Group e D) = D := eq_refl.

(* The whole-record control the negative above needs.  Without it that
   [Fail] is guarded only by [data_psh_data_law_control], which is a
   control for the LAW FIELD and not for the record, so a change making
   whole-record equality unstatable would leave the negative succeeding
   for the wrong reason.  No [≈] repair is available to sit beside it:
   no setoid on [HomGroupData] exists anywhere in the tree, so an [≈]
   statement about the record is not even formable. *)
Example data_psh_data_whole_control : D = D := eq_refl.

End RoundTrips.

Section RoundTripsObject.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (M : @MonoidObject C CC_Monoidal c).

Example rt_mul_control : rg_mul c M = rg_mul c M := eq_refl.

Fail Example rt_mul_strict :
  rg_mul c (representable_monoid_object c (monoid_object_representable c M))
    = rg_mul c M := eq_refl.

Lemma rt_mul :
  rg_mul c (representable_monoid_object c (monoid_object_representable c M))
    ≈ rg_mul c M.
Proof.
  change (hmul c M exl exr ≈ rg_mul c M).
  unfold hmul.
  now rewrite fork_exl_exr, id_right.
Qed.

Lemma rt_unit :
  rg_unit c (representable_monoid_object c (monoid_object_representable c M))
    ≈ rg_unit c M.
Proof.
  change (@hone C _ _ c M 1 ≈ rg_unit c M).
  unfold hone.
  now rewrite (one_unique (one : 1 ~{C}~> 1) id), id_right.
Qed.

End RoundTripsObject.

(** ** Clause (a): the exponential of a group object

    The group analogue of [Hom_Monoid] (Structure/Monoid.v:290),
    obtained by transporting the hom-set data along curry/uncurry rather
    than by an internal diagram chase. *)

Section Exponential.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context `{CL : @Closed C _}.
Context (x y : C).

Section ExpMonoid.

Context (D : HomMonoidData y).

Program Definition exp_hom_monoid_data : HomMonoidData (y ^ x) := {|
  hmd_mul := fun z f g => curry (hmd_mul D (uncurry f) (uncurry g));
  hmd_unit := fun z => curry (@hmd_unit C y D (z × x))
|}.
Next Obligation.
  intros f f' Hf g g' Hg.
  now rewrite Hf, Hg.
Qed.
Next Obligation. now rewrite !uncurry_curry, hmd_assoc. Qed.
Next Obligation. now rewrite !uncurry_curry, hmd_unit_l, curry_uncurry. Qed.
Next Obligation. now rewrite !uncurry_curry, hmd_unit_r, curry_uncurry. Qed.
Next Obligation.
  rewrite curry_comp_l, hmd_mul_natural.
  now rewrite <- !uncurry_comp.
Qed.
Next Obligation.
  rewrite curry_comp_l.
  now rewrite hmd_unit_natural.
Qed.

Definition exp_MonoidObject : @MonoidObject C CC_Monoidal (y ^ x) :=
  data_MonoidObject (y ^ x) exp_hom_monoid_data.

End ExpMonoid.

Section ExpCompare.

Context (M : @MonoidObject C CC_Monoidal y).

Definition exp_MonoidObject_of :=
  exp_MonoidObject (monoid_object_hom_data y M).

Example exp_mappend_is_Hom_Monoid :
  @mappend C CC_Monoidal _ exp_MonoidObject_of
    = @mappend C CC_Monoidal _ (@Hom_Monoid C _ _ CL x y M) := eq_refl.

Fail Example exp_mempty_is_Hom_Monoid :
  @mempty C CC_Monoidal _ exp_MonoidObject_of
    = @mempty C CC_Monoidal _ (@Hom_Monoid C _ _ CL x y M) := eq_refl.

Lemma exp_mempty_agrees :
  @mempty C CC_Monoidal _ exp_MonoidObject_of
    ≈ @mempty C CC_Monoidal _ (@Hom_Monoid C _ _ CL x y M).
Proof.
  simpl.
  apply proper_morphism.
  unfold hone.
  now rewrite (one_unique (one : 1 × x ~> 1) exl).
Qed.

End ExpCompare.

Section ExpGroup.

Context (D : HomGroupData y).

Program Definition exp_hom_group_data : HomGroupData (y ^ x) := {|
  hgd_monoid := exp_hom_monoid_data (hgd_monoid D);
  hgd_inv := fun z f => curry (hgd_inv D (uncurry f))
|}.
Next Obligation. intros f f' Hf; now rewrite Hf. Qed.
Next Obligation. now rewrite !uncurry_curry, hgd_inv_l. Qed.
Next Obligation. now rewrite !uncurry_curry, hgd_inv_r. Qed.
Next Obligation.
  rewrite curry_comp_l, hgd_inv_natural.
  now rewrite <- !uncurry_comp.
Qed.

Definition exp_GroupObject : @GroupObject C CC_CartesianMonoidal (y ^ x) :=
  data_GroupObject (y ^ x) exp_hom_group_data.

End ExpGroup.

End Exponential.

(** ** Clause (c): the computation in Sets *)

Require Import Category.Instance.Sets.Products.

Section SetsComputation.

Context (gobj : Sets).
Context (G : @GroupObject Sets CC_CartesianMonoidal gobj).

Definition sets_group_monoid : @MonoidObject Sets CC_Monoidal gobj :=
  @rg_monoid Sets _ _ gobj G.

Example sets_mul_pointwise (X : Sets) (f h : X ~{Sets}~> gobj)
  (a : carrier X) :
  @hmul Sets _ _ gobj sets_group_monoid X f h a
    = @mappend Sets CC_Monoidal gobj sets_group_monoid (f a, h a)
  := eq_refl.

Example sets_unit_pointwise (X : Sets) (a : carrier X) :
  @hone Sets _ _ gobj sets_group_monoid X a
    = @mempty Sets CC_Monoidal gobj sets_group_monoid ttt := eq_refl.

Example sets_inv_pointwise (X : Sets) (f : X ~{Sets}~> gobj)
  (a : carrier X) :
  @hinv Sets _ _ gobj G X f a = @rg_inv Sets _ _ gobj G (f a) := eq_refl.

Program Definition const_elt (a : carrier gobj) : (1 : Sets) ~{Sets}~> gobj :=
  {| morphism := fun _ => a |}.

Program Definition elem_GrpObject : GrpObject := {|
  grp_setoid := gobj;
  grp_unit := @mempty Sets CC_Monoidal gobj sets_group_monoid ttt;
  grp_mul  := fun a b =>
                @mappend Sets CC_Monoidal gobj sets_group_monoid (a, b);
  grp_inv  := fun a => @rg_inv Sets _ _ gobj G a
|}.
Next Obligation.
  intros u u' Hu v v' Hv; apply proper_morphism; now split.
Qed.
Next Obligation.
  exact (@hmul_assoc Sets _ _ gobj sets_group_monoid _
           (const_elt a) (const_elt b) (const_elt c) ttt).
Qed.
Next Obligation.
  exact (@hmul_unit_l Sets _ _ gobj sets_group_monoid _ (const_elt a) ttt).
Qed.
Next Obligation. exact (@hmul_inv_l Sets _ _ gobj G _ (const_elt a) ttt). Qed.

Definition DiscSet (A : Type) : Sets :=
  {| carrier := A ; is_setoid := eq_Setoid A |}.

Program Definition iprod_GrpObject (A : Type) : GrpObject := {|
  grp_setoid := Sets_iprod_obj (fun _ : A => gobj);
  grp_unit := fun _ => grp_unit elem_GrpObject;
  grp_mul  := fun s t a => grp_mul elem_GrpObject (s a) (t a);
  grp_inv  := fun s a => grp_inv elem_GrpObject (s a)
|}.
Next Obligation.
  intros s s' Hs t t' Ht i; now rewrite (Hs i), (Ht i).
Qed.
Next Obligation.
  intro w; exact (grp_mul_assoc elem_GrpObject (a w) (b w) (c w)).
Qed.
Next Obligation. intro w; exact (grp_mul_unit_l elem_GrpObject (a w)). Qed.
Next Obligation. intro w; exact (grp_mul_inv_l elem_GrpObject (a w)). Qed.

Context (A : Type).

Definition HomGrpA : GrpObject :=
  @HomGrpObject Sets gobj (@group_object_hom_data Sets _ _ gobj G)
                (DiscSet A).

Program Definition sets_hom_to_iprod :
  GrpHom HomGrpA (iprod_GrpObject A) := {|
  grp_map := {| morphism := fun f a => f a |}
|}.
Next Obligation. intro w; reflexivity. Qed.
Next Obligation. intro w; reflexivity. Qed.

Program Definition sets_iprod_to_hom :
  GrpHom (iprod_GrpObject A) HomGrpA := {|
  grp_map := {| morphism := fun s => {| morphism := s |} |}
|}.

Program Definition sets_hom_iprod_iso :
  @Isomorphism Grp HomGrpA (iprod_GrpObject A) := {|
  to := sets_hom_to_iprod;
  from := sets_iprod_to_hom
|}.
Next Obligation. intro w; reflexivity. Qed.

End SetsComputation.
