(** * Partial orders are a full reflective subcategory of all preorders

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer GTM 5, §IV.3, printed p. 92, Exercise 4.  Read from the
          page image: "4. Show the following subcategories to be
          reflective: (a) The full subcategory of all partial orders in
          the category Preord of all preorders, with arrows all monotone
          functions.  (b) The full subcategory of T_0-spaces in Top."
          Catalog id: maclane:IV.3:ex4.  This file is half (a); half (b)
          is Instance/Top/Kolmogorov.v, written in parallel.

    ** What is delivered

    [Poset_Reflective_in_Ord : Reflective Pos_Sub] -- the record of
    Construction/Reflective.v:60, whose three fields are exactly the three
    things Mac Lane's phrase names: FULLNESS of the subcategory
    ([Pos_Sub_Full], Instance/Ord.v), a REFLECTOR ([Poset_reflector]), and
    the ADJUNCTION ([Poset_adj]) making it left adjoint to the inclusion.
    Read the packaging precisely: the adjunction ALONE is strictly less
    than the record, and that mismatch is this development's typing
    rejection.

    Around it: the poset reflection [PosetReflection] with
    [PosetReflection_Antisymmetric], its packaging [PosetReflectionObj],
    the projection [reflection_proj], the mediator [poset_med], the
    universal property [poset_reflection_universal] and its arrow
    [poset_reflection_universal_arrow], the counit corollary
    [poset_reflect_iso] -- for a partial order P, the reflection of P is
    isomorphic to P -- instantiated at the naturals as
    [natle_reflect_iso], and three witnesses.

    ** The route

    Universal arrows, exactly the path Instance/Ab/TorsionFree.v takes for
    §IV.3 Exercise 2 and Instance/Grp/Abelianize.v for §III.1 Exercise 3:
    state the ∃! ([poset_reflection_universal]), package it with
    Theory/Universal/Arrow.v:158's [universal_arrow_from_UMP], then read
    the functor and the adjunction off :295's
    [LeftAdjointFunctorFromUniversalArrows] and :324's
    [AdjunctionFromUniversalArrows] with no further proof.  Nothing in
    that chain is re-derived here, and this file states no triangle
    identity and no naturality square of its own.

    ** Same carrier, coarser [≈], and no choice principle

    [PosetReflection P] has the SAME carrier TYPE as P and the SAME order
    relation -- both recorded by [eq_refl] as [poset_reflection_carrier]
    and [poset_reflection_order] -- and differs from P in ONE field, the
    setoid: [≈] is coarsened from P's own to [poset_refl_equiv P x y :=
    ord_le P x y /\ ord_le P y x].  So the quotient is a SETOID quotient,
    which is what the issue asks for: no new carrier is built, no
    equivalence class is ever formed, no quotient axiom or quotient type
    is used, and no witness is extracted from a [Prop]-valued existential,
    so no choice principle appears anywhere.  This is the design
    Instance/Ab/TorsionFree.v uses for A/T(A) and the one
    Instance/Grp/Abelianization.v uses for G/[G,G].

    Three things fall out of that choice rather than being proved:
    antisymmetry of the reflection is the DEFINITION of its [≈]
    ([PosetReflection_Antisymmetric] hands back the two order proofs it is
    given, as the pair the coarser equivalence asks for); the projection
    is the identity on points; and respectfulness of the coarser relation
    for the order ([PosetReflection]'s one obligation) is transitivity of
    P applied twice on each side.  The only genuinely new argument in the
    file is the mediator's respectfulness, [poset_med]'s first obligation:
    [x ≈ y] in the reflection gives [f x ≤ f y] and [f y ≤ f x] in the
    target by monotonicity, and the target's OWN antisymmetry then gives
    [f x ≈ f y].  That is the one place where being in the subcategory is
    spent, and it is spent exactly once.

    ** Strengths, measured strict-first

    Holding at [eq_refl] (six occurrences, all outside any rejection):
    the reflector's object part is the reflection
    ([poset_reflector_obj]); the universal arrow IS [reflection_proj] and
    its object IS [PosetReflectionObj] ([poset_arrow_is_proj],
    [poset_arrow_obj] -- the TorsionFree.v:533/:538 precedent, since
    [universal_arrow_from_UMP] stores the supplied morphism as the second
    projection of the comma object it builds); the carrier and the order
    are the base preorder's ([poset_reflection_carrier],
    [poset_reflection_order]); and -- the reviewer's check -- the
    adjunction's UNIT applied to any point IS the projection applied to it
    ([poset_unit_is_proj]).

    Falling back, with the cause diagnosed in each case:

    - The unit as a MORPHISM RECORD is only [≈] the projection
      ([poset_unit_is_proj_hom]).  Cause:
      [AdjunctionFromUniversalArrows] builds the transpose as
      [fun g => fmap[U] g ∘ arrow], so the class unit is a COMPOSITE
      record, [fmap[Incl] id ∘ reflection_proj P]; applied to a point that
      composite reduces, as a record it does not.  This is the same
      fallback, with the same cause, that TorsionFree.v:551 records.
    - The reflection of a partial order is isomorphic to it but not equal
      to it: [natle_reflect_iso] is a pure instantiation of
      [reflective_counit_iso] with no tactic, while
      [PosetReflection NatLe = NatLe] is refused -- the two [OrdObject]s
      agree in carrier and order (both pinned as controls) and differ in
      the setoid field, which is the entire content of the reflection.
    - The COUNIT is not read back at all.  It is the other transpose,
      [unique_obj (ump_universal_arrows ...)], and [ump_universal_arrows]
      (Theory/Universal/Arrow.v:139) is closed with [Qed], so nothing on
      that side reduces and no [eq_refl] is claimed for it.

    The first two fallbacks are pinned as conversion rejections in
    Test/ProbeOrd372.v, together with the record-versus-adjunction
    mismatch (typing), the [sigT]-eta rejection of the [Pos] comparison
    (conversion), the objects-of-[Ord] versus objects-of-a-thin-category
    refutation (conversion) and one universe rejection (formability): six
    negatives of three kinds, plus one scope-free instrument check.  The
    COUNIT is NOT among them -- nothing is claimed about it in either
    direction.  This file itself carries no rejection at all, so it
    contributes nothing to [make todo].

    ** Non-vacuity: three preorders, and what each refutation uses

    - [Chaos2]: [bool] under the TOTAL relation.  Not antisymmetric
      ([Chaos2_not_antisymmetric]) and its reflection identifies the two
      points ([chaos2_merges]).  Its carrier setoid is Instance/Sets.v:563's
      discrete [bool_setoid_object], so the refutation of antisymmetry is
      settled by [Bool.diff_true_false] on a Leibniz equality -- by
      DISCRIMINATION at the discrete carrier, not by mapping out.
    - [NatLe]: the naturals under [le].  Antisymmetric
      ([NatLe_antisymmetric]), so it is an object [NatLePos] of [Posets],
      the counit isomorphism applies to it, and its reflection is INERT
      ([natle_reflection_inert]: the coarser [≈] is still Leibniz
      equality).  It is the witness that the reflection does not collapse
      everything.
    - [MixOrd]: three points, two of them mutually related and one
      strictly above both.  The reflection merges EXACTLY the pair
      ([mix_merges], and at the projection [mix_proj_merges]) and keeps
      the top apart ([mix_top_stays_apart]).  The merge is by direct
      construction of the two order proofs; the separation is by direct
      COMPUTATION of the relation -- destructing the pair and reading
      [mix_le mtop mleft = False] off the [match] -- not by mapping out
      and not by discrimination.  [MixOrd_not_antisymmetric] does use
      discrimination, at the discrete carrier.

    ** Universes

    Measured with [Set Printing Universes] on all 56 constants of this
    module, reading BOTH binder and block.  NO constraint block carries a
    universe EQUATION; every entry is [<] or [<=].  The identifications
    are in the binders and are the donors': [Poset_reflector] is a
    [Functor@{u u0 u0 u u0 u0}] and [Poset_Reflective_in_Ord] a
    [Reflective@{u1 u u1 u0 u1 u2 u2}] over [Pos_Sub@{u1 u2 u2 ...}], all
    inheriting [Subcategory]'s hom-with-proof identification, which the
    probe guards.  [Set] appears as a BOUND on most constants, from the
    [Prop]-valued order; Instance/Ord.v's header carries the
    discriminating experiment that attributes it.  All 122 constants of
    the two files are closed under the global context, with no [Axioms:]
    line anywhere.

    ** NOT delivered

    - No functoriality of [PosetReflection] beyond what [Poset_reflector]
      gives, and no naturality of [reflection_proj] stated separately.
    - No comparison with Instance/Proset/Skeletal.v:95's [Proset_Skeleton]
      -- the thin-category shadow of this reflection -- and no [Cat]-level
      statement of any kind.
    - No uniqueness statement for the reflector beyond what
      [poset_reflection_universal] and [reflective_counit_iso] give.
    - No idempotent monad of the reflection.
      Construction/Reflective/Idempotent.v would give it by instantiation
      from [Poset_Reflective_in_Ord]; that instantiation is not made.
    - No coreflection, no [Coreflective] statement, and nothing about
      preorders inside [Cat].
    - No specialization preorder of a topological space, which would be
      the natural bridge to half (b); neither file builds it.
    - No decision procedure for the reflection's [≈] and no normal form,
      and no relation between [PosetReflection] and any quotient
      construction elsewhere in tree. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ord.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** ** The reflection: same carrier, coarser [≈] *)

Definition poset_refl_equiv (P : OrdObject)
    (x y : carrier (ord_setoid P)) : Prop :=
  ord_le P x y ∧ ord_le P y x.

#[local] Obligation Tactic := idtac.

Program Definition poset_refl_setoid (P : OrdObject)
  : Setoid (carrier (ord_setoid P)) := {|
  equiv := poset_refl_equiv P
|}.
Next Obligation.
  intro P; constructor.
  - intro x; split; apply ord_refl.
  - intros x y [Hxy Hyx]; split; assumption.
  - intros x y z [Hxy Hyx] [Hyz Hzy]; split.
    + exact (ord_trans P x y z Hxy Hyz).
    + exact (ord_trans P z y x Hzy Hyx).
Qed.

Definition poset_refl_carrier (P : OrdObject) : SetoidObject := {|
  carrier   := carrier (ord_setoid P);
  is_setoid := poset_refl_setoid P
|}.

Program Definition PosetReflection (P : OrdObject) : OrdObject := {|
  ord_setoid := poset_refl_carrier P;
  ord_le     := ord_le P;
  ord_refl   := ord_refl P;
  ord_trans  := ord_trans P
|}.
Next Obligation.
  intros P x x' [Hxx' Hx'x] y y' [Hyy' Hy'y]; split; intro H.
  - exact (ord_trans P x' x y' Hx'x (ord_trans P x y y' H Hyy')).
  - exact (ord_trans P x x' y Hxx' (ord_trans P x' y' y H Hy'y)).
Qed.

(** Antisymmetry of the reflection is the DEFINITION of its [≈]: the two
    order proofs handed in ARE the pair the coarser equivalence asks for. *)
Lemma PosetReflection_Antisymmetric (P : OrdObject)
  : OrdAntisymmetric (PosetReflection P).
Proof. intros x y Hxy Hyx; split; assumption. Defined.

Definition PosetReflectionObj (P : OrdObject) : Posets :=
  (PosetReflection P; PosetReflection_Antisymmetric P).

Program Definition reflection_proj (P : OrdObject)
  : P ~{Ord}~> PosetReflection P :=
  @Build_OrdHom P (PosetReflection P)
    {| morphism := fun x : carrier (ord_setoid P) => x |} _.
Next Obligation.
  intros P x y Hxy; split; apply ord_le_of_equiv.
  - exact Hxy.
  - symmetry; exact Hxy.
Qed.
Next Obligation. intros P x y H; exact H. Qed.

(** ** The universal property *)

Program Definition poset_med {P D : OrdObject} (HD : OrdAntisymmetric D)
    (f : P ~{Ord}~> D) : PosetReflection P ~{Ord}~> D :=
  @Build_OrdHom (PosetReflection P) D
    {| morphism := fun x : carrier (ord_setoid P) => ord_fn f x |} _.
Next Obligation.
  intros P D HD f x y [Hxy Hyx]; simpl.
  exact (HD _ _ (ord_mono f x y Hxy) (ord_mono f y x Hyx)).
Qed.
Next Obligation. intros P D HD f x y H; exact (ord_mono f x y H). Qed.

Theorem poset_reflection_universal (P : OrdObject) :
  ∀ (d : Posets) (f : P ~{Ord}~> Incl Ord Pos_Sub d),
    ∃! g : PosetReflectionObj P ~{Posets}~> d,
      f ≈ fmap[Incl Ord Pos_Sub] g ∘ reflection_proj P.
Proof.
  intros d f.
  unshelve eexists.
  - exact (poset_med `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition poset_reflection_universal_arrow (P : OrdObject)
  : @UniversalArrow Ord Posets P (Incl Ord Pos_Sub) :=
  @universal_arrow_from_UMP Ord Posets P (Incl Ord Pos_Sub)
    (PosetReflectionObj P) (reflection_proj P)
    (poset_reflection_universal P).

Definition Poset_reflector : Ord ⟶ Posets :=
  LeftAdjointFunctorFromUniversalArrows (Incl Ord Pos_Sub)
    poset_reflection_universal_arrow.

Definition Poset_adj : Poset_reflector ⊣ Incl Ord Pos_Sub :=
  AdjunctionFromUniversalArrows (Incl Ord Pos_Sub)
    poset_reflection_universal_arrow.

Definition Poset_Reflective_in_Ord : Reflective Pos_Sub :=
  @Build_Reflective Ord Pos_Sub Pos_Sub_Full
    Poset_reflector Poset_adj.

(** ** Strict readbacks *)

Example poset_reflector_obj (P : OrdObject) :
  `1 (fobj[Poset_reflector] P) = PosetReflection P := eq_refl.

Example poset_arrow_is_proj (P : OrdObject) :
  @arrow Ord Posets P (Incl Ord Pos_Sub)
    (poset_reflection_universal_arrow P)
    = reflection_proj P := eq_refl.

Example poset_arrow_obj (P : OrdObject) :
  @arrow_obj Ord Posets P (Incl Ord Pos_Sub)
    (poset_reflection_universal_arrow P)
    = PosetReflectionObj P := eq_refl.

Definition poset_unit (P : OrdObject)
  : P ~{Ord}~> Incl Ord Pos_Sub (fobj[Poset_reflector] P) :=
  @Category.Theory.Adjunction.unit _ _ _ _ Poset_adj P.

Example poset_unit_is_proj (P : OrdObject)
    (x : carrier (ord_setoid P)) :
  ord_fn (poset_unit P) x = ord_fn (reflection_proj P) x := eq_refl.

Lemma poset_unit_is_proj_hom (P : OrdObject) :
  poset_unit P ≈ reflection_proj P.
Proof. intro a; reflexivity. Defined.

Example poset_reflection_carrier (P : OrdObject) :
  carrier (ord_setoid (PosetReflection P)) = carrier (ord_setoid P)
  := eq_refl.

Example poset_reflection_order (P : OrdObject) :
  ord_le (PosetReflection P) = ord_le P := eq_refl.

(** ** The counit at a partial order *)

Definition poset_reflect_iso (x : Posets) :
  fobj[Poset_reflector] (Incl Ord Pos_Sub x) ≅[Posets] x :=
  reflective_counit_iso Poset_Reflective_in_Ord x.

(** ** Non-vacuity: three preorders *)

(** The two-element set under the TOTAL relation: a preorder that is as far
    from a partial order as possible.  Its carrier setoid is the discrete
    one (Instance/Sets.v's [bool_setoid_object]), so the refutation of
    antisymmetry is settled by [discriminate] rather than by mapping out. *)
Program Definition Chaos2 : OrdObject := {|
  ord_setoid := bool_setoid_object;
  ord_le     := fun _ _ => True
|}.
Next Obligation. intro x; exact I. Qed.
Next Obligation. intros x y z Hxy Hyz; exact I. Qed.

Lemma Chaos2_not_antisymmetric : OrdAntisymmetric Chaos2 → False.
Proof. intro H; exact (Bool.diff_true_false (H true false I I)). Qed.

Lemma chaos2_merges :
  (true : carrier (ord_setoid (PosetReflection Chaos2))) ≈ false.
Proof. split; exact I. Defined.

(** The naturals under [le]: already a partial order, so the reflection is
    inert on it and the counit isomorphism applies. *)
Program Definition NatLe : OrdObject := {|
  ord_setoid := {| carrier := nat ; is_setoid := eq_Setoid nat |};
  ord_le     := Nat.le
|}.
Next Obligation. intro x; apply Nat.le_refl. Qed.
Next Obligation. intros x y z Hxy Hyz; exact (Nat.le_trans _ _ _ Hxy Hyz). Qed.

Lemma NatLe_antisymmetric : OrdAntisymmetric NatLe.
Proof. intros x y Hxy Hyx; exact (Nat.le_antisymm x y Hxy Hyx). Qed.

Definition NatLePos : Posets := (NatLe; NatLe_antisymmetric).

Definition natle_reflect_iso :
  fobj[Poset_reflector] (Incl Ord Pos_Sub NatLePos) ≅[Posets] NatLePos :=
  poset_reflect_iso NatLePos.

Lemma natle_reflection_inert (x y : carrier (ord_setoid NatLe)) :
  (x : carrier (ord_setoid (PosetReflection NatLe))) ≈ y → x = y.
Proof. intros [Hxy Hyx]; exact (Nat.le_antisymm x y Hxy Hyx). Qed.

(** A MIXED preorder: two mutually related points and one strictly above
    them.  The reflection merges exactly the pair and keeps the top apart. *)
Inductive MixPt : Set := mleft | mright | mtop.

Definition mix_le (x y : MixPt) : Prop :=
  match x, y with
  | mtop, mtop => True
  | mtop, _    => False
  | _, _       => True
  end.

Program Definition MixOrd : OrdObject := {|
  ord_setoid := {| carrier := MixPt ; is_setoid := eq_Setoid MixPt |};
  ord_le     := mix_le
|}.
Next Obligation. intro x; destruct x; exact I. Qed.
Next Obligation. intros x y z; destruct x, y, z; simpl; tauto. Qed.

Lemma MixOrd_not_antisymmetric : OrdAntisymmetric MixOrd → False.
Proof. intro H; discriminate (H mleft mright I I). Qed.

Lemma mix_merges :
  (mleft : carrier (ord_setoid (PosetReflection MixOrd))) ≈ mright.
Proof. split; exact I. Defined.

Lemma mix_top_stays_apart :
  (mleft : carrier (ord_setoid (PosetReflection MixOrd))) ≈ mtop → False.
Proof. intros [_ H]; exact H. Qed.

Lemma mix_proj_merges :
  ord_fn (reflection_proj MixOrd) mleft
    ≈ ord_fn (reflection_proj MixOrd) mright.
Proof. exact mix_merges. Defined.
