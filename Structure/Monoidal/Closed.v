Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Cartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
(* Unset Transparent Obligations. *)

Section Closed.

Context {C : Category}.

(* Wikipedia (https://en.wikipedia.org/wiki/Closed_monoidal_category):

A closed monoidal category C is a category equipped, for every two
objects A and B, with

  - an object A ⇒ B,
  - a morphism eval[A, B]: (A ⇒ B) ⊗ A → B,

satisfying the following universal property: for every morphism
    f : X ⊗ A → B

there exists a unique morphism
    h : X → A ⇒ B

such that
    f = eval[A, B] ∘ (h ⊗ id[A])
*)

Reserved Infix "⇒" (at level 30, right associativity).

Class ClosedMonoidal := {
  closed_is_cartesian : @CartesianMonoidal C;

  exponent_obj : obj → obj → obj    (* internal homs *)
    where "x ⇒ y" := (exponent_obj x y);

  exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z;

  curry'   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := to (@exp_iso x y z);
  uncurry' {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := from (@exp_iso x y z);

  eval' {x y} : (x ⇒ y) ⨂ x ~> y := @uncurry' _ _ _ id;

  ump_exponents' {x y z} (f : x ⨂ y ~> z) :
    ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id)
}.
#[export] Existing Instance closed_is_cartesian.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : object_scope.

Context `{ClosedMonoidal}.

Definition curry   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := @curry' _ x y z.
Definition uncurry {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := @uncurry' _ x y z.
Arguments curry' {_ _ _ _} /.
Arguments uncurry' {_ _ _ _} /.

Definition eval {x y} : (x ⇒ y) ⨂ x ~> y := uncurry id.
Arguments eval' {_ _ _} /.

Remove Hints Sets_Product_Monoidal : typeclass_instances.

Definition ump_exponents {x y z} (f : x ⨂ y ~> z) :
  ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id) := @ump_exponents' _ x y z f.

#[global] Program Instance curry_respects (a b c : C) :
  Proper (equiv ==> equiv) (@curry a b c).
Next Obligation.
  proper.
  unfold curry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct to; simpl in *.
  rewrites; reflexivity.
Qed.

#[global] Program Instance uncurry_respects (a b c : C) :
  Proper (equiv ==> equiv) (@uncurry a b c).
Next Obligation.
  proper.
  unfold uncurry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct from; simpl in *.
  rewrites; reflexivity.
Qed.

Corollary curry_uncurry {x y z} (f : x ~> y ⇒ z) :
  curry (uncurry f) ≈ f.
Proof.
  sapply (iso_to_from (@exp_iso _ x y z)).
Qed.

Corollary uncurry_curry {x y z} (f : x ⨂ y ~> z) :
  uncurry (curry f) ≈ f.
Proof.
  sapply (iso_from_to (@exp_iso _ x y z)).
Qed.

#[local] Hint Rewrite @curry_uncurry : categories.
#[local] Hint Rewrite @uncurry_curry : categories.
#[local] Hint Rewrite @ump_exponents : categories.

Definition flip `{@BraidedMonoidal C} {x y z : C} `(f : x ~> y ⇒ z) :
  y ~> x ⇒ z := curry (uncurry f ∘ braid).

Corollary curry_eval {x y : C} :
  curry eval ≈ @id _ (x ⇒ y).
Proof.
  intros; unfold eval; simpl; cat.
Qed.

#[local] Hint Rewrite @curry_eval : categories.

Corollary curry_inj {x y z : C} (f g : x ⨂ y ~> z) :
  curry f ≈ curry g → f ≈ g.
Proof.
  intros.
  rewrite <- (uncurry_curry f).
  rewrite <- (uncurry_curry g).
  rewrites; reflexivity.
Qed.

Corollary uncurry_inj {x y z : C} (f g : x ~> y ⇒ z) :
  uncurry f ≈ uncurry g → f ≈ g.
Proof.
  intros.
  rewrite <- (curry_uncurry f).
  rewrite <- (curry_uncurry g).
  rewrites; reflexivity.
Qed.

End Closed.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : category_scope.

#[export] Hint Rewrite @curry_uncurry : categories.
#[export] Hint Rewrite @uncurry_curry : categories.
#[export] Hint Rewrite @ump_exponents : categories.
#[export] Hint Rewrite @curry_eval : categories.
