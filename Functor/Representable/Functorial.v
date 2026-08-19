Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Iso.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(** * Taking the representing object, as a functor

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer 1998, §III.2, Exercise 1, printed p. 62.
    nLab: https://ncatlab.org/nlab/show/representable+functor

    Functor/Representable.v proves Mac Lane's exercise: a natural
    transformation τ : K ⟹ K' between represented functors is named by a
    unique arrow [repr_induced R R' τ : repr_obj R' ~> repr_obj R] compatible
    with the two representations.  This file collects the three things that
    statement makes available and that its own file cannot host.

    (1) THE COMPARISON WITH THE YONEDA EMBEDDING.  The issue this development
    answers suggests obtaining the arrow by transporting τ to ψ'⁻¹ ∘ τ ∘ ψ and
    inverting the hom-bijection [Yoneda_Embedding'] (Functor/Hom.v:109).
    Functor/Representable.v does the first half — that is [repr_transport] —
    and then names the arrow directly rather than through the packaged
    bijection, for the universe reason recorded in that file's header.  The
    two agree: [repr_induced_is_yoneda_transpose] is [eq_refl], so wherever
    both are formable they are the same TERM, not merely equivalent arrows.

    (2) THE CROSS-LINK WITH Structure/UniversalProperty.v.  That file's
    [univ_property_unique_up_to_unique_iso] (:138) is the τ = id case for
    objects satisfying a universal PREDICATE, and its [univ_property_unique]
    (:115) is the underlying uniqueness.  Before this file there was no
    passage in either direction between [IsUniversalProperty] and
    [Representable] anywhere in the tree — before this one the two names
    occurred together in only two files, Structure/UniversalProperty.v (where
    "representable" is a URL and a paragraph of prose) and
    Structure/Cartesian/Closed/Adjunction.v
    (a comment, at :341 now that it has been amended to point here) — so the
    cross-link is a construction and not a citation, and the absence claim is
    scoped to what was searched: the two class NAMES, over every [.v] file in
    the tree.  It is a short one: [Representable_of_UnivProperty] is a record
    literal, and [UnivProperty_of_Representable] takes the predicate
    "c represents F" and the identity isomorphism.  With it,
    [univ_property_iso_from_is_induced] identifies the backward leg of that
    proposition's isomorphism with [repr_induced] at the identity
    transformation.  The identification factors through [repr_pair_iso]
    (Functor/Hom/Yoneda/Iso.v:162), which is what [univ_property_unique]
    consumes: [up_unique_obj_is_repr_pair_iso] records by [eq_refl] that the
    proposition's [unique_obj] IS that isomorphism, and
    [repr_pair_iso_from_is_induced] compares it with the induced arrow.

    (3) THE FUNCTOR.  [repr_induced_id] and [repr_induced_comp] say that
    K ↦ repr_obj is functorial, contravariantly into C.  [ReprCat C] is the
    category of functors C ⟶ Sets equipped with a chosen representation — the
    full subcategory of [C, Sets] cut out by [Representable], built with
    Construction/Subcategory.v's [Sub], so its objects are pairs ⟨K, R⟩ and
    its morphisms are natural transformations of the underlying functors
    (formally, paired with a trivial membership witness that the hom-setoid
    ignores, [Sub] comparing morphisms by first projection) —
    and [ReprObjFunctor C : ReprCat C ⟶ C^op] is the assignment.  It is FULL
    ([ReprObj_Full]) and FAITHFUL ([ReprObj_Faithful]): fullness is Mac Lane's
    correspondence run backwards, an arrow h being carried to
    ψ' ∘ Hom(h, −) ∘ ψ⁻¹, and faithfulness is the compatibility condition
    probed through the surjectivity of ψ.  That is the Yoneda embedding read
    from the other side; the equivalence with C^op that the slogan suggests is
    NOT assembled here — see below.

    WHAT IS DELIVERED

    - [repr_induced_is_yoneda_transpose] ([eq_refl]).
    - [repr_of_representation], [Representable_of_UnivProperty],
      [UnivProperty_of_Representable]; [up_unique_obj_is_repr_pair_iso]
      ([eq_refl]); [repr_pair_iso_from_is_induced],
      [repr_pair_iso_to_is_induced], [univ_property_iso_from_is_induced].
    - [ReprSubcat], [ReprCat], [ReprObjFunctor], [ReprObj_Full],
      [ReprObj_Faithful].
    - Non-vacuity over the delooping of (ℕ, +): a non-identity τ whose induced
      arrow is a non-identity too, in two forms — against the tautological
      representations of Functor/Representable.v ([wit_tau], where the induced
      arrow COMPUTES, [wit_induced_computes] being [eq_refl]) and against the
      in-tree [YoEvalAt_Representable] (Functor/Hom/Yoneda/Natural.v:413),
      where it does not compute on the nose and the agreement is [≈].

    WHAT IS NOT DELIVERED

    - No claim that the passages of (2) are mutually inverse.  They are not
      even composable in general: [Representable_of_UnivProperty] needs a
      point of the predicate, and going the other way replaces the predicate
      by "c represents F", which is not the predicate one started with.  What
      is proved is that each passage exists and that the τ = id isomorphisms
      agree.
    - No essential-surjectivity or equivalence claim for [ReprObjFunctor].
      Full and faithful are proved, and [Hom_Representable] does exhibit, for
      every object c of C, an object of [ReprCat C] whose representing object
      is c on the nose — but the essential-surjectivity witness is not
      packaged, the equivalence is not assembled, and no
      [EquivalenceOfCategories] is claimed.
    - No repleteness or 2-categorical statement about [ReprCat], and no
      comparison with Construction/Elements.v or with
      Theory/Universal/Element.v's [UniversalElement].  [ReprObj_Full] and
      [ReprObj_Faithful] are plain definitions rather than registered
      instances, so a consumer wanting [FullyFaithful] must supply them by
      name; that follows the header's reason for [Hom_Representable] being a
      [Definition] and keeps resolution unperturbed.
    - The witness's category is one-object, so "the induced arrow is not an
      identity" is a statement about an ENDOmorphism.  No witness with two
      DISTINCT representing objects and a non-identity induced arrow is given
      here; at distinct objects "is not an identity" is not a well-typed
      claim, and what would replace it — that the correspondence separates
      transformations — is [ReprObj_Faithful], proved in general.

    A UNIVERSE NOTE, MEASURED PER CONSTANT

    Functor/Representable.v's constants leave the object universe
    unconstrained relative to the hom universe.  An audit corrected an
    earlier draft of this note, which blamed section (2) as a whole: the
    pin follows [repr_pair_iso], NOT the section boundary.  Measured per
    constant, the partition is

      - FREE (no [o = h], no [o <= h]): [repr_of_representation],
        [Representable_of_UnivProperty], [UnivProperty_of_Representable] —
        i.e. the passage between the two classes, which consumes
        [repr_pair_iso] nowhere — together with [ReprSubcat] and [ReprCat];
      - [o <= h] with no [o = h]: [ReprObjFunctor], [ReprObj_Full],
        [ReprObj_Faithful], the price of packaging the assignment as a
        functor into C^op;
      - PINNED at [o = h]: exactly the four constants that consume
        [repr_pair_iso] — [repr_pair_iso_from_is_induced],
        [repr_pair_iso_to_is_induced], [up_unique_obj_is_repr_pair_iso],
        [univ_property_iso_from_is_induced] — plus
        [repr_induced_is_yoneda_transpose], which NAMES [Yoneda_Embedding']
        in its own statement.

    The inherited pin is invisible in the printed BINDER —
    [repr_pair_iso_from_is_induced] displays as [∀ (C : Category@{u u0 u0})]
    — and appears only in the constraint block, as [u = u0].  Section (1) is pinned by
    construction and deliberately so — [repr_induced_is_yoneda_transpose]
    NAMES [Yoneda_Embedding'] in its own statement, so it can only be stated
    where that constant is formable, and its category is left unannotated for
    that reason.  Both the pins and the freedom are guarded in
    Test/ProbeRepresentableInduced.v. *)

(** ** The comparison with the Yoneda embedding *)

Section YonedaTranspose.

Context (C : Category).
Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(* The issue's suggested route — transport τ across the representations, then
   invert the hom-bijection — produces the same TERM as [repr_induced], not
   merely an equivalent arrow.  [eq_refl] is the convertibility exception:
   [Yoneda_Embedding']'s two-sided inverse is [Yoneda_Full]'s [prefmap],
   which is evaluation at the identity, which is what [repr_induced] is. *)
Definition repr_induced_is_yoneda_transpose (tau : K ⟹ K') :
  @two_sided_inverse _ _ _ _
    (Yoneda_Embedding' C (@repr_obj _ _ R) (@repr_obj _ _ R'))
    (repr_transport R R' tau)
  = repr_induced R R' tau := eq_refl.

End YonedaTranspose.

(** ** The passage between [IsUniversalProperty] and [Representable] *)

Section Bridge.

Universes o h.
Context (C : Category@{o h h}).

(* A representation, packaged.  Used below to name the two representations a
   [repr_pair_iso] is built from. *)
Definition repr_of_representation {F : C ⟶ Sets} (c : C)
  (b : [Hom c,─] ≅[Fun] F) : Representable F := {|
  repr_obj := c;
  represented := b
|}.

Context (P : C → Type) (eqP : ∀ c, Setoid (P c)).

(* An object satisfying a universal property represents the functor that
   property is the representability of.  [repr_equivalence] carries the proof
   of [P c] to the representation; nothing else is needed. *)
Definition Representable_of_UnivProperty (H : IsUniversalProperty C P eqP)
  (c : C) (t : P c) : Representable (@repr_functor C P eqP H) := {|
  repr_obj := c;
  represented := to (repr_equivalence c) t
|}.

End Bridge.

Arguments repr_of_representation {C F} c b.
Arguments Representable_of_UnivProperty {C P eqP} H c t.

Section BridgeBack.

Universes o h.
Context (C : Category@{o h h}).
Context (F : C ⟶ Sets).

(* ...and conversely, representability of a FIXED functor is itself a
   universal property, of the predicate "c represents F".  The equivalence
   between proofs of the predicate and representations is the identity, which
   is the honest content of the direction: the class [IsUniversalProperty] is
   representability with the predicate left free, so instantiating the
   predicate at representability is where it becomes a tautology. *)
Program Definition UnivProperty_of_Representable
  : IsUniversalProperty C (fun c => @Isomorphism ([C, Sets]) [Hom c,─] F)
      (fun c => iso_setoid) := {|
  repr_functor := F;
  repr_equivalence := fun c => iso_id
|}.

End BridgeBack.

Arguments UnivProperty_of_Representable {C} F.

(** ** The τ = id case, cross-linked *)

Section CrossLink.

Context (C : Category).
Context {F : C ⟶ Sets}.
Context {c v : C}.
Context (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F).

(* [repr_pair_iso] (Functor/Hom/Yoneda/Iso.v:162) is the isomorphism of
   representing objects that Structure/UniversalProperty.v consumes.  Its two
   legs are the two induced arrows at the identity transformation.  They are
   NOT the same term — [nat_id]'s component is [fmap[F] id] rather than [id],
   so the induced arrow carries one application of [fmap] that
   [repr_pair_iso]'s leg does not — and the [eq_refl] negative is pinned in
   Test/ProbeRepresentableInduced.v. *)
Lemma repr_pair_iso_from_is_induced :
  from (repr_pair_iso b1 b2)
    ≈ repr_induced (repr_of_representation c b1)
                   (repr_of_representation v b2) nat_id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  apply proper_morphism.
  symmetry; srewrite (@fmap_id _ _ F c); reflexivity.
Qed.

Lemma repr_pair_iso_to_is_induced :
  to (repr_pair_iso b1 b2)
    ≈ repr_induced (repr_of_representation v b2)
                   (repr_of_representation c b1) nat_id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  apply proper_morphism.
  symmetry; srewrite (@fmap_id _ _ F v); reflexivity.
Qed.

End CrossLink.

Section UnivPropertyCrossLink.

Context (C : Category).
Context (P : C → Type) (eqP : ∀ c, Setoid (P c)).
Context (H : IsUniversalProperty C P eqP).

(* The isomorphism [univ_property_unique_up_to_unique_iso] produces IS the
   [repr_pair_iso] of the two representations, on the nose: the underlying
   [univ_property_unique] is [Defined] and its [uniqueness] field reduces.
   [eq_refl] is the convertibility exception. *)
Definition up_unique_obj_is_repr_pair_iso (c d : C) (t : P c) (s : P d) :
  unique_obj (univ_property_unique_up_to_unique_iso C P eqP H c d t s)
  = repr_pair_iso (to (repr_equivalence c) t) (to (repr_equivalence d) s)
  := eq_refl.

(* ...so Mac Lane's τ = id case, read through the passage of this file, is
   that proposition's isomorphism: its backward leg is the arrow induced by
   the identity transformation between the two representations. *)
Corollary univ_property_iso_from_is_induced (c d : C) (t : P c) (s : P d) :
  from (unique_obj (univ_property_unique_up_to_unique_iso C P eqP H c d t s))
    ≈ repr_induced (Representable_of_UnivProperty H c t)
                   (Representable_of_UnivProperty H d s) nat_id.
Proof. apply repr_pair_iso_from_is_induced. Qed.

End UnivPropertyCrossLink.

(** ** The category of represented functors, and the representing-object
       functor *)

Section ReprFunctor.

Universes o h.
Context (C : Category@{o h h}).

(* The full subcategory of [C, Sets] on the functors carrying a chosen
   representation.  [shom := True] is the full-subcategory idiom of
   Theory/Skeleton.v:553 and Construction/Localization.v. *)
Program Definition ReprSubcat : Subcategory ([C, Sets]) := {|
  sobj := fun K => Representable K;
  shom := fun _ _ _ _ _ => True
|}.

Definition ReprCat : Category := @Sub ([C, Sets]) ReprSubcat.

(* ...and the assignment ⟨K, R⟩ ↦ repr_obj R, τ ↦ the arrow τ names.  It
   lands in C^op because [repr_induced_comp] reverses composition. *)
Program Definition ReprObjFunctor : ReprCat ⟶ C^op := {|
  fobj := fun X => @repr_obj _ _ (`2 X);
  fmap := fun X Y f => repr_induced (`2 X) (`2 Y) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply repr_induced_respects. Qed.
Next Obligation. now apply repr_induced_id. Qed.
Next Obligation. now apply repr_induced_comp. Qed.

(* Fullness: Mac Lane's correspondence run backwards.  An arrow h between the
   representing objects is carried to ψ' ∘ Hom(h, −) ∘ ψ⁻¹, and that
   transformation names h again — by uniqueness, once ψ⁻¹ ∘ ψ has been
   cancelled. *)
Program Definition ReprObj_Full : Functor.Full ReprObjFunctor := {|
  prefmap := fun X Y h =>
    (to (@represented _ _ (`2 Y))
       ∘[Fun] (fmap[Curried_Hom C] (op h) ∘[Fun] from (@represented _ _ (`2 X)))
     ; I)
|}.
Next Obligation.
  symmetry; apply (repr_induced_unique X0 X _ g).
  apply repr_compatible_of_at; intros d k; simpl.
  apply proper_morphism.
  pose proof (iso_from_to (@represented _ _ X0) d k) as HH; simpl in HH.
  rewrite HH.
  now rewrite id_left.
Qed.

(* Faithfulness: the compatibility condition determines τ at every element,
   because ψ is invertible and so every element of K d is ψ_d of something. *)
Definition ReprObj_Faithful : Functor.Faithful ReprObjFunctor.
Proof.
  constructor; simpl; intros X Y f g E d z.
  assert (Hz : transform[to (@represented _ _ (`2 X))] d
                 (transform[from (@represented _ _ (`2 X))] d z) ≈ z).
  { pose proof (iso_to_from (@represented _ _ (`2 X)) d z) as HT; simpl in HT.
    rewrite HT.
    srewrite (@fmap_id _ _ (`1 X) d); reflexivity. }
  pose proof (repr_compatible_at
                (repr_induced_compatible (`2 X) (`2 Y) (`1 f)) d
                (transform[from (@represented _ _ (`2 X))] d z)) as Ef.
  pose proof (repr_compatible_at
                (repr_induced_compatible (`2 X) (`2 Y) (`1 g)) d
                (transform[from (@represented _ _ (`2 X))] d z)) as Eg.
  simpl in Ef, Eg.
  rewrite <- Hz, <- Ef, <- Eg.
  now rewrite E.
Qed.

End ReprFunctor.

Arguments ReprSubcat C.
Arguments ReprCat C.
Arguments ReprObjFunctor C.

(** ** Non-vacuity

    Over the delooping of (ℕ, +) — one object, hom-set ℕ, composition
    addition, identity 0 — a natural transformation between representable
    copresheaves is a natural number, and the arrow it names is that number.
    Both the transformation and the induced arrow are non-identities, which is
    what makes the correspondence's content visible: a witness at which both
    sides were identities would demonstrate nothing. *)

Section Witness.

Notation BNat := (Deloop Nat_Plus).

(* The transformation named by n, against the tautological representations. *)
Definition wit_tau (n : nat) := @fmap _ _ (Curried_Hom BNat) ttt ttt n.

(* The induced arrow COMPUTES here: it is n on the nose.  [eq_refl] is the
   convertibility exception. *)
Definition wit_induced_computes (n : nat) :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau n) = n := eq_refl.

Lemma wit_tau_not_id : wit_tau 3%nat ≈ nat_id → False.
Proof. intro Hx; pose proof (Hx ttt 0%nat) as H0; simpl in H0; discriminate. Qed.

Lemma wit_induced_not_id :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau 3%nat)
    ≈ id{BNat} → False.
Proof. intro Hx; simpl in Hx; discriminate. Qed.

(* The same at an in-tree [Representable] instance rather than the
   tautological one: [YoEvalAt_Representable] (Functor/Hom/Yoneda/Natural.v:413)
   represents evaluation at an object by the representable copresheaf.  Acting
   on each functor by [fmap] at n is a transformation of evaluations. *)
Program Definition wit_ev_tau (n : nat)
  : @YoEvalAt BNat ttt ⟹ @YoEvalAt BNat ttt := {|
  transform := fun F => fmap[F] n
|}.
Next Obligation. exact (@naturality_sym _ _ _ _ f ttt ttt n x0). Qed.
Next Obligation. exact (@naturality _ _ _ _ f ttt ttt n x0). Qed.

(* Here the induced arrow does NOT come out on the nose — the Yoneda
   isomorphism's backward leg leaves an [∘ id], which over (ℕ, +) is a
   [n + 0] — so the agreement is stated at [≈], and the [eq_refl] negative is
   pinned in Test/ProbeRepresentableInduced.v. *)
Lemma wit_ev_induced (n : nat) :
  repr_induced (YoEvalAt_Representable BNat ttt)
               (YoEvalAt_Representable BNat ttt) (wit_ev_tau n)
    ≈ wit_tau n.
Proof. simpl; intros; unfold op; now rewrite <- plus_n_O. Qed.

Lemma wit_ev_tau_not_id : wit_ev_tau 3%nat ≈ nat_id → False.
Proof.
  intro Hx.
  pose proof (Hx (fobj[Curried_Hom BNat] ttt) 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

Lemma wit_ev_induced_not_id :
  repr_induced (YoEvalAt_Representable BNat ttt)
               (YoEvalAt_Representable BNat ttt) (wit_ev_tau 3%nat)
    ≈ id → False.
Proof. intro Hx; pose proof (Hx ttt 0%nat) as H0; simpl in H0; discriminate. Qed.

End Witness.
