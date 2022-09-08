Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Morphisms.
Require Import Category.Functor.Strong.
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

#[export]
Program Instance Coq : Category := {
  obj     := Type;
  hom     := λ A B : Type, A → B;
  homset  := λ _ _, {| equiv := λ f g, ∀ x, f x = g x |};
  id      := λ _ x, x;
  compose := λ _ _ _ g f x, g (f x)
}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation. proper; congruence. Qed.

#[export]
Program Instance Coq_Terminal : @Terminal Coq := {
  terminal_obj := unit : Type;
  one := λ _ a, tt
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

#[export]
Program Instance Coq_Cartesian : @Cartesian Coq := {
  product_obj := λ x y, x * y : Type;
  fork := λ _ _ _ f g x, (f x, g x);
  exl  := λ _ _ p, fst p;
  exr  := λ _ _ p, snd p
}.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  intros; simplify; intros.
  - rewrite H; reflexivity.
  - rewrite H; reflexivity.
  - intros; simplify.
    rewrite <- H, <- H0.
    rewrite <- surjective_pairing; reflexivity.
Qed.

#[export]
Program Instance Coq_Monoidal : @Monoidal Coq :=
  @CC_Monoidal Coq Coq_Cartesian Coq_Terminal.

#[export]
Program Instance Coq_Closed : @Closed Coq _ := {
  exponent_obj := Basics.arrow;
  exp_iso := λ _ _ _,
    {| to   := {| morphism := λ f a b, f (a, b) |}
     ; from := {| morphism := λ f p, f (fst p) (snd p) |} |}
}.
Next Obligation. proper; extensionality X0; congruence. Qed.
Next Obligation. proper; congruence. Qed.

#[export]
Program Instance Coq_ClosedMonoidal : @ClosedMonoidal Coq :=
  @CCC_ClosedMonoidal Coq Coq_Cartesian Coq_Terminal Coq_Closed.

#[export]
Program Instance Coq_Initial : Initial Coq := {
  terminal_obj := False;
  one := λ _ _, False_rect _ _
}.
Next Obligation. contradiction. Qed.

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
  - destruct x0; firstorder.
Qed.

Lemma injectivity_is_monic `(f : x ~> y) :
  (∀ x y, f x = f y → x = y) ↔ Monic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    apply HA, HB.
  - intros HA ?? HB.
    pose (λ (_ : unit), x0) as const_x.
    pose (λ (_ : unit), y0) as const_y.
    destruct HA.
    specialize (monic unit const_x const_y).
    unfold const_x in monic.
    unfold const_y in monic.
    eapply monic; eauto.
    + simpl; intuition.
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
    specialize (HA x0).
    destruct HA as [? HA].
    rewrite <- HA.
    apply HB.
  - intros HA ?.
    destruct HA.
    specialize epic with (z := Prop).
    specialize epic with (g1 := λ y0, (exists x0, f x0 = y0)%type).
    simpl in *.
    specialize epic with (g2 := λ y, True).
    erewrite epic.
    + constructor.
    + intros.
      Axiom propositional_extensionality : ∀ P : Prop, P → P = True.
      apply propositional_extensionality.
      exists x0.
      reflexivity.
Qed.

(** All endofunctors in Coq have strength *)

#[export]
Program Instance Coq_StrongFunctor (F : Coq ⟶ Coq) : StrongFunctor F := {|
  strength := λ _ _ p, fmap (λ y, (fst p, y)) (snd p)
|}.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  f_equal.
Qed.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  now srewrite (@fmap_id _ _ F).
Qed.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  f_equal.
Qed.
