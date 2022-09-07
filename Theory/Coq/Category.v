Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Functor.Endo.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Constant.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* [Coq] represents the category of Coq types and functions.

   This category is meant to be used for programming, and so it, and the
   constructions built on it, differ from the conventions of the main category
   theory library -- even though we show that all constructions map into the
   concepts of that library.

   For example, morphisms here are compared by definitional equality. This
   requires functional extensionality to be assumed in most proofs, but frees
   the programmer from maintaining towers of setoids, especially when
   higher-order functions are involved (for example, consider a simple proof
   such as [f = g → fmap ap f = fmap ap g]; for this to work over Setoids, a
   Proper instance for fmap is required that takes the Proper instance for ap
   into account).

   While the larger library [Category.Theory] assumes that proofs are a
   primary interest, and so uses Setoid plumbing everywhere, in this sub-
   library it is assumed that computational results are the main interest, and
   so some axioms are considered justified to relieve the proof burden. *)

Definition compose_respects' {x y z} :
  Proper (@equiv _ (eq_Setoid (y → z)) ==>
          @equiv _ (eq_Setoid (x → y)) ==>
          @equiv _ (eq_Setoid (x → z)))
    (λ (f : y → z) (g : x → y) x, f (g x)).
Proof.
  proper.
  now rewrite X, X0.
Qed.

#[export]
Instance Coq : Category := {
  obj              := Type;
  hom              := λ x y, x → y;
  homset           := λ x y, eq_Setoid (x → y);
  id               := λ _ x, x;
  compose          := λ _ _ _ f g x, f (g x);
  compose_respects := λ _ _ _, compose_respects';
  id_left          := λ _ _ _, eq_refl;
  id_right         := λ _ _ _, eq_refl;
  comp_assoc       := λ _ _ _ _ _ _ _, eq_refl;
  comp_assoc_sym   := λ _ _ _ _ _ _ _, eq_refl;
}.

Arguments obj {Category}%category_scope : simpl never.
Arguments hom {Category}%category_scope (_ _)%object_scope : simpl never.
Arguments id {Category}%category_scope {x}%object_scope : simpl never.
Arguments compose {Category}%category_scope {x y z}%object_scope
  (f g)%homset_scope : simpl never.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).
Notation "$ x" := (λ f, f x) (at level 60).

#[export]
Program Instance Coq_Terminal : @Terminal Coq := {
  terminal_obj := unit : Type;
  one := λ _ a, tt
}.
Next Obligation.
  extensionality x0.
  destruct (f x0), (g x0); reflexivity.
Qed.

#[export]
Program Instance Coq_Cartesian : @Cartesian Coq := {
  product_obj := λ x y, x * y;
  fork := λ _ _ _ f g x, (f x, g x);
  exl  := λ _ _ p, fst p;
  exr  := λ _ _ p, snd p
}.
Next Obligation.
  split; intros.
  - split; rewrite H; clear H; cbv; auto.
  - simplify.
    rewrite <- H, <- H0; clear H H0.
    cbv.
    extensionality x0.
    destruct (h x0); reflexivity.
Qed.

#[export]
Program Instance Coq_Monoidal : @Monoidal Coq :=
  @CC_Monoidal Coq Coq_Cartesian Coq_Terminal.

#[export]
Program Instance Coq_Closed : @Closed Coq Coq_Cartesian := {
  exponent_obj := λ x y, x → y;
  exp_iso := λ _ _ _, {|
    to   := {| morphism := λ f a b, f (a, b) |};
    from := {| morphism := λ f '(x, y), f x y |}
  |}
}.
Next Obligation.
  proper; extensionality X0; simplify; now cbv.
Qed.
Next Obligation.
  proper; extensionality X0; simplify; now cbv.
Qed.

#[export]
Program Instance Coq_ClosedMonoidal : @ClosedMonoidal Coq :=
  @CCC_ClosedMonoidal Coq Coq_Cartesian Coq_Terminal Coq_Closed.

#[export]
Program Instance Coq_Initial : Initial Coq := {
  terminal_obj := False : Type;
  one := λ _ _, False_rect _ _
}.
Next Obligation.
  extensionality x0.
  contradiction.
Qed.

#[export]
Program Instance Coq_Cocartesian : @Cocartesian Coq := {
  product_obj := sum;
  fork := λ _ _ _ f g x,
    match x with
    | Datatypes.inl v => f v
    | Datatypes.inr v => g v
    end;
  exl  := λ _ _ p, Datatypes.inl p;
  exr  := λ _ _ p, Datatypes.inr p
}.
Next Obligation.
  split; intros.
  - split; intros;
    rewrite H; reflexivity.
  - extensionality x0.
    destruct x0; firstorder.
    + eapply equal_f in a; eauto.
    + eapply equal_f in b; eauto.
Qed.

Lemma injectivity_is_monic `(f : x ~> y) :
  (∀ x y, f x = f y → x = y) ↔ Monic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    extensionality x0.
    cbv in HB.
    eapply equal_f in HB; eauto.
  - intros HA ?? HB.
    pose (λ (_ : unit), x0) as const_x.
    pose (λ (_ : unit), y0) as const_y.
    destruct HA.
    specialize (monic unit const_x const_y).
    unfold const_x in monic.
    unfold const_y in monic.
    cbv in monic.
    eapply equal_f in monic; auto.
    + now rewrite HB.
    + exact tt.
Qed.

Lemma surjectivity_is_epic `(f : x ~> y) :
  (∀ y, exists x, f x = y)%type ↔ Epic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    extensionality x0.
    specialize (HA x0).
    destruct HA as [? HA].
    rewrite <- HA.
    cbv in HB.
    eapply equal_f in HB; eauto.
  - intros HA ?.
    destruct HA.
    specialize epic with (z := Prop).
    specialize epic with (g1 := λ y0, (exists x0, f x0 = y0)%type).
    simpl in *.
    specialize epic with (g2 := λ y, True).
    cbv in epic.
    eapply equal_f in epic; eauto.
    + now rewrite epic.
    + intros.
      Axiom propositional_extensionality : ∀ P : Prop, P → P = True.
      extensionality x0.
      apply propositional_extensionality.
      now exists x0.
Qed.
