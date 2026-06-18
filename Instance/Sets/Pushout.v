Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Pushouts in [Sets] *)

(* nLab:      https://ncatlab.org/nlab/show/pushout
   Wikipedia: https://en.wikipedia.org/wiki/Pushout_(category_theory)

   For setoid-morphisms [f : A → B] and [g : A → C] in [Sets], the pushout
   of the span [B <-f- A -g-> C] is the quotient [(B ⊔ C)/~]: the apex
   carrier is [B + C] (the Coq sum type), equipped with the smallest
   equivalence relation containing:

     - the existing setoid equivalences on [B] (lifted via [inl])
       and on [C] (lifted via [inr]);
     - the "glue" identifications [inl (f a) ~ inr (g a)] for every [a : A].

   This matches the standard Set construction: the disjoint union (coproduct)
   modulo the finest equivalence relation with [f a ~ g a].  The cocone legs
   are the two injections [inl : B ~> apex] and [inr : C ~> apex], and the
   universal property (UMP) factors any competing cocone [(q1, q2)] with
   [q1 ∘ f ≈ q2 ∘ g] through a unique copairing mediator out of the quotient.

   Because the apex is a setoid, the equivalence relation is carried by the
   object itself rather than by a Coq quotient type, so the whole construction
   is [funext]-free.  We realise [~] as an inductive type [pushout_eq] with
   explicit reflexivity, symmetry, transitivity, an inl-congruence, an
   inr-congruence, and a glue constructor.

   The setoid laws (refl/sym/trans) are immediate from the constructors;
   the universal property is proved by induction on [pushout_eq].

   This file is the concrete realisation needed by
   [Construction/Cospan/Corelation.v]'s [CorelComposable Sets] instance. *)

Section SetsPushout.

(** Inductive equivalence-closure relation on [carrier B + carrier C]. *)
Section PushoutEqDef.

Context {A B C : SetoidObject}.
Context (f : SetoidMorphism A B) (g : SetoidMorphism A C).

Inductive pushout_eq :
    Datatypes.sum (carrier B) (carrier C)
 -> Datatypes.sum (carrier B) (carrier C)
 -> Type :=
  | po_inl_cong : forall b1 b2 : carrier B,
      @equiv _ B b1 b2 ->
      pushout_eq (@Datatypes.inl (carrier B) (carrier C) b1)
                 (@Datatypes.inl (carrier B) (carrier C) b2)
  | po_inr_cong : forall c1 c2 : carrier C,
      @equiv _ C c1 c2 ->
      pushout_eq (@Datatypes.inr (carrier B) (carrier C) c1)
                 (@Datatypes.inr (carrier B) (carrier C) c2)
  | po_glue : forall a : carrier A,
      pushout_eq (@Datatypes.inl (carrier B) (carrier C) (f a))
                 (@Datatypes.inr (carrier B) (carrier C) (g a))
  | po_sym : forall x y : Datatypes.sum (carrier B) (carrier C),
      pushout_eq x y ->
      pushout_eq y x
  | po_trans : forall x y z : Datatypes.sum (carrier B) (carrier C),
      pushout_eq x y ->
      pushout_eq y z ->
      pushout_eq x z.

End PushoutEqDef.

Arguments pushout_eq {A B C} f g _ _.

(** Reflexivity comes from [po_inl_cong] / [po_inr_cong] applied to the
    underlying setoid's reflexivity. *)
Lemma pushout_eq_refl {A B C : SetoidObject}
      (f : SetoidMorphism A B) (g : SetoidMorphism A C)
      (x : Datatypes.sum (carrier B) (carrier C)) :
  pushout_eq f g x x.
Proof.
  destruct x as [b | c].
  - apply po_inl_cong; reflexivity.
  - apply po_inr_cong; reflexivity.
Qed.

(** The pushout apex as a [SetoidObject]. *)
Program Definition pushout_apex_setoid
        {A B C : SetoidObject}
        (f : SetoidMorphism A B) (g : SetoidMorphism A C) : SetoidObject :=
  {| carrier := Datatypes.sum (carrier B) (carrier C);
     is_setoid :=
       {| equiv := pushout_eq f g;
          setoid_equiv := _ |} |}.
Next Obligation.
  constructor.
  - intros x. apply pushout_eq_refl.
  - intros x y H. apply po_sym; exact H.
  - intros x y z H1 H2. eapply po_trans; eauto.
Qed.

(** The two injection morphisms. *)
Program Definition pushout_inl_mor
        {A B C : SetoidObject}
        (f : SetoidMorphism A B) (g : SetoidMorphism A C) :
        SetoidMorphism B (pushout_apex_setoid f g) :=
  {| morphism := fun b => Datatypes.inl b |}.
Next Obligation.
  unfold Proper, respectful; intros b1 b2 Hb.
  apply po_inl_cong; exact Hb.
Qed.

Program Definition pushout_inr_mor
        {A B C : SetoidObject}
        (f : SetoidMorphism A B) (g : SetoidMorphism A C) :
        SetoidMorphism C (pushout_apex_setoid f g) :=
  {| morphism := fun c => Datatypes.inr c |}.
Next Obligation.
  unfold Proper, respectful; intros c1 c2 Hc.
  apply po_inr_cong; exact Hc.
Qed.

(** ** Mediating morphism

    Given a cocone [(q1 : B → Q, q2 : C → Q)] with [q1 ∘ f ≈ q2 ∘ g], the
    mediator [pushout_med : B + C → Q] sends [inl b ↦ q1 b], [inr c ↦ q2 c].
    Respect for [pushout_eq] is proved by induction on the relation. *)

(** Underlying function on sums, used as the morphism. *)
Definition pushout_mediator_fun
        {B C Q : SetoidObject}
        (q1 : SetoidMorphism B Q) (q2 : SetoidMorphism C Q)
        (x : Datatypes.sum (carrier B) (carrier C)) : carrier Q :=
  match x with
  | Datatypes.inl b => q1 b
  | Datatypes.inr c => q2 c
  end.

(** Respectfulness of [pushout_mediator_fun] for [pushout_eq], by induction
    on the equivalence-closure derivation. *)
Lemma pushout_mediator_respects
        {A B C Q : SetoidObject}
        (f : SetoidMorphism A B) (g : SetoidMorphism A C)
        (q1 : SetoidMorphism B Q) (q2 : SetoidMorphism C Q)
        (Hcomm : forall a : carrier A, @equiv _ Q (q1 (f a)) (q2 (g a)))
        (x y : Datatypes.sum (carrier B) (carrier C))
        (Hxy : pushout_eq f g x y) :
  @equiv _ Q (pushout_mediator_fun q1 q2 x) (pushout_mediator_fun q1 q2 y).
Proof.
  induction Hxy as
    [ b1 b2 Hb
    | c1 c2 Hc
    | a
    | x y Hxy IH
    | x y z Hxy1 IH1 Hxy2 IH2 ].
  - simpl. apply proper_morphism; exact Hb.
  - simpl. apply proper_morphism; exact Hc.
  - simpl. exact (Hcomm a).
  - symmetry; exact IH.
  - transitivity (pushout_mediator_fun q1 q2 y); [exact IH1 | exact IH2].
Qed.

Program Definition pushout_mediator
        {A B C Q : SetoidObject}
        (f : SetoidMorphism A B) (g : SetoidMorphism A C)
        (q1 : SetoidMorphism B Q) (q2 : SetoidMorphism C Q)
        (Hcomm : forall a : carrier A, @equiv _ Q (q1 (f a)) (q2 (g a))) :
        SetoidMorphism (pushout_apex_setoid f g) Q :=
  {| morphism := pushout_mediator_fun q1 q2 |}.
Next Obligation.
  unfold Proper, respectful; intros x y Hxy.
  exact (pushout_mediator_respects f g q1 q2 Hcomm x y Hxy).
Qed.

End SetsPushout.

(** ** The [HasPushouts Sets] instance

    Each pushout is packaged as a [Pullback] in [Sets^op] using the
    machinery in [Structure/Pushout.v]. *)

#[export] Program Instance Sets_HasPushouts : HasPushouts Sets := {|
  pushout := fun X Y Z f g =>
    {| Pull := pushout_apex_setoid f g;
       pullback_fst := pushout_inl_mor f g;
       pullback_snd := pushout_inr_mor f g;
       pullback_commutes := _;
       ump_pullbacks := _
    |}
|}.
Next Obligation.
  (* Goal after Program: [pushout_eq f g (inl (f x)) (inr (g x))],
     which is exactly the [po_glue] constructor. *)
  apply po_glue.
Defined.
Next Obligation.
  (* UMP in Sets^op: given a cocone (q1 : Y → Q, q2 : Z → Q) in Sets with
     q1 ∘ f ≈ q2 ∘ g, build the unique mediator Pull → Q. *)
  rename X0 into Hcomm.
  unshelve refine
    (Build_Unique _ _ _ (pushout_mediator f g q1 q2 _) _ _).
  - (* The compatibility hypothesis Hcomm expressed pointwise. *)
    intros a. exact (Hcomm a).
  - simpl; split; intros b; reflexivity.
  - (* Uniqueness: any v : Pull → Q agreeing on both injections equals
       the mediator pointwise.  Case split on the sum constructor. *)
    intros v [Hv1 Hv2].
    intros [b | c]; simpl.
    + symmetry; exact (Hv1 b).
    + symmetry; exact (Hv2 c).
Defined.

(** ** Corollary: a pushout-apex element is reached by [inl] or [inr]

    Every element of the pushout apex carrier is *definitionally* in [B + C]
    (the Coq sum type), so this corollary is just the standard sum case
    split.  It's recorded here for downstream use in the
    [CorelComposable Sets] instance, where we need to know that the
    composite copairing of a pushout-cocone is surjective. *)

Lemma pushout_apex_case
      {A B C : SetoidObject}
      (f : SetoidMorphism A B) (g : SetoidMorphism A C)
      (x : carrier (pushout_apex_setoid f g)) :
  (exists b : carrier B, x = Datatypes.inl b) \/
  (exists c : carrier C, x = Datatypes.inr c).
Proof.
  destruct x as [b | c]; [left | right]; eauto.
Qed.
