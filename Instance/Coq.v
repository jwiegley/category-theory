Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
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
  isCartesianProduct a b := {|
    Cartesian.fork := λ _ f g x, (f x, g x);
    exl  := λ p, fst p;
    exr  := λ p, snd p
  |}
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
  isCartesianProduct _ _ := {|
  Cartesian.fork := λ _ f g x,
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := λ p, Datatypes.inl p;
  exr  := λ p, Datatypes.inr p
  |}
}.
Next Obligation.
  split; intros.
  - split; intros;
    rewrite H; reflexivity.
  - destruct x; firstorder.
Qed.

(** All endofunctors in Coq have strength *)

#[export]
Program Instance Coq_StrongFunctor (F : Coq ⟶ Coq) : StrongFunctor F := {|
  strength := λ _ _ p, fmap[F] (λ y, (fst p, y)) (snd p)
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
