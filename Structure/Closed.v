Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cartesian.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Closed.

Context {C : Category}.
Context `{@Cartesian C}.

Class Closed := {
  Exp : ob -> ob -> ob    (* internal homs *)
    where "y ^ x" := (Exp x y);

  exp_iso {x y z} : x × y ~> z ≊ x ~> z^y;

  curry'   {x y z} := to (@exp_iso x y z);
  uncurry' {x y z} := from (@exp_iso x y z);

  eval' {x y} : y^x × x ~> y := uncurry' _ _ _ id;

  ump_exponents' {x y z} (f : x × y ~> z) :
    eval' ∘ first (curry' _ _ _ f) ≈ f
}.

Notation "y ^ x" := (Exp x y)
  (at level 30, right associativity) : object_scope.

Context `{@Closed}.

Definition curry   {x y z} := @curry' _ x y z.
Definition uncurry {x y z} := @uncurry' _ x y z.
Arguments curry' {_ _ _ _} /.
Arguments uncurry' {_ _ _ _} /.

Definition eval {x y} : y^x × x ~> y := uncurry id.
Arguments eval' {_ _ _} /.

Definition ump_exponents {x y z} (f : x × y ~> z) :
  eval ∘ first (curry f) ≈ f := @ump_exponents' _ x y z f.

Global Program Instance parametric_morphism_curry (a b c : C) :
  Proper (equiv ==> equiv) (@curry a b c).
Next Obligation.
  proper.
  unfold curry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct to; simpl in *.
  rewrites; reflexivity.
Qed.

Global Program Instance parametric_morphism_uncurry (a b c : C) :
  Proper (equiv ==> equiv) (@uncurry a b c).
Next Obligation.
  proper.
  unfold uncurry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct from; simpl in *.
  rewrites; reflexivity.
Qed.

Corollary curry_uncurry {x y z} (f : x ~> z^y) :
  curry (uncurry f) ≈ f.
Proof.
  replace (curry (uncurry f)) with ((curry ∘ uncurry) f) by auto.
  unfold curry, uncurry; simpl.
  pose proof (iso_to_from (@exp_iso _ x y z)) as HA.
  unfold equiv in HA; simpl in HA.
  autounfold in HA.
  unfold equiv in HA; simpl in HA.
  apply HA.
Qed.

Corollary uncurry_curry {x y z} (f : x × y ~> z) :
  uncurry (curry f) ≈ f.
Proof.
  replace (uncurry (curry f)) with ((uncurry ∘ curry) f) by auto.
  unfold curry, uncurry; simpl.
  pose proof (iso_from_to (@exp_iso _ x y z)) as HA.
  simpl in HA.
  unfold equiv in HA; simpl in HA.
  autounfold in HA.
  unfold equiv in HA; simpl in HA.
  apply HA.
Qed.

Hint Rewrite @curry_uncurry : categories.
Hint Rewrite @uncurry_curry : categories.
Hint Rewrite @ump_exponents : categories.

Definition flip {x y z : C} `(f : x ~> z ^ y) : y ~> z ^ x :=
  curry (uncurry f ∘ swap).

Corollary eval_curry {x y z w : C} (f : y × z ~> w) (g : x ~> y) (h : x ~> z) :
  eval ∘ ((curry f ∘ g) △ h) ≈ f ∘ g △ h.
Proof.
  intros.
  rewrite <- (ump_exponents f) at 2.
  rewrite <- comp_assoc.
  unfold first.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
Qed.

Hint Rewrite @eval_curry : categories.

Corollary curry_eval {x y : C} :
  curry eval ≈ @id _ (y^x).
Proof.
  intros; unfold eval; simpl; cat.
Qed.

Hint Rewrite @curry_eval : categories.

Corollary eval_first {x y z : C} (f : x ~> z^y) :
  eval ∘ first f ≈ uncurry f.
Proof.
  rewrite <- (curry_uncurry f); cat.
Qed.

Corollary curry_inj {x y z : C} (f g : x × y ~> z) :
  curry f ≈ curry g -> f ≈ g.
Proof.
  intros.
  rewrite <- (uncurry_curry f).
  rewrite <- (uncurry_curry g).
  rewrites; reflexivity.
Qed.

Corollary uncurry_inj {x y z : C} (f g : x ~> z^y) :
  uncurry f ≈ uncurry g -> f ≈ g.
Proof.
  intros.
  rewrite <- (curry_uncurry f).
  rewrite <- (curry_uncurry g).
  rewrites; reflexivity.
Qed.

Corollary curry_comp_l {x y z w : C} (f : y × z ~> w) (g : x ~> y) :
  curry f ∘ g ≈ curry (f ∘ first g).
Proof.
  apply uncurry_inj; cat.
  rewrite <- (ump_exponents (uncurry (curry f ∘ g))).
  rewrite curry_uncurry.
  unfold first in *.
  rewrite <- comp_assoc.
  rewrite eval_curry.
  reflexivity.
Qed.

Corollary curry_comp {x y z w : C} (f : z ~> w) (g : x × y ~> z) :
  curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g.
Proof.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite eval_first; cat.
Qed.

Corollary uncurry_comp_r {x y z w : C} (f : z ~> w) (g : x ~> z^y) :
  f ∘ uncurry g ≈ uncurry (curry (f ∘ eval) ∘ g).
Proof.
  rewrite curry_comp_l; cat.
  rewrite <- comp_assoc.
  rewrite eval_first; reflexivity.
Qed.

Corollary uncurry_comp {x y z w : C} (f : y ~> w^z) (g : x ~> y) :
  uncurry (f ∘ g) ≈ uncurry f ∘ first g.
Proof.
  intros.
  apply curry_inj; cat.
  rewrite <- curry_comp_l; cat.
Qed.

Theorem curry_id {x y z : C} (f : x ~> y) :
  curry (@id _ (y × z)) ∘ f ≈ curry (first f).
Proof.
  intros.
  rewrite curry_comp_l.
  apply uncurry_inj; cat.
Qed.

Global Program Instance exp_prod_l {x y z : C} :
  z^(x × y) ≅ (z^y)^x := {
  to   := curry (curry (eval ∘ to prod_assoc));
  from := curry (uncurry eval ∘ from prod_assoc)
}.
Next Obligation.
  rewrite curry_comp_l.
  unfold first.
  rewrite curry_comp_l.
  unfold first.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- comp_assoc; cat.
  rewrite comp_assoc; cat.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- comp_assoc; cat.
  rewrite comp_assoc; cat.
  rewrite comp_assoc; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- fork_comp.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- comp_assoc; cat.
  rewrite fork_comp; cat.
Qed.
Next Obligation.
  rewrite curry_comp_l.
  apply uncurry_inj; cat.
  rewrite <- comp_assoc.
  rewrite <- eval_first.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (first eval)).
  unfold first at 1.
  rewrite <- fork_comp.
  rewrite <- comp_assoc; cat.
  unfold first.
  rewrite <- fork_comp.
  rewrite <- comp_assoc; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- fork_comp.
  rewrite <- comp_assoc; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- fork_comp; cat.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- comp_assoc; cat.
  rewrite fork_comp; cat.
Qed.

Hint Rewrite @exp_prod_l : isos.

Global Program Instance exp_prod_r {x y z : C} :
  (y × z)^x ≅ y^x × z^x := {
  to   := curry (exl ∘ eval) △ curry (exr ∘ eval);
  from := curry (uncurry exl △ uncurry exr)
}.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- fork_exl_exr.
  apply fork_inv; split;
  rewrite <- curry_comp; cat;
  pose proof (@eval_first) as HA;
  unfold first in HA;
  rewrites; cat.
Qed.
Next Obligation.
  apply uncurry_inj.
  rewrite uncurry_comp; cat.
  rewrite <- fork_comp.
  rewrite <- !eval_first.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp; cat.
  rewrite fork_comp; cat.
  unfold first; cat.
Qed.

Hint Rewrite @exp_prod_r : isos.

Lemma curry_fork {x y z w : C} (f : x × y ~> z) (g : x × y ~> w) :
  curry (f △ g) ≈ from exp_prod_r ∘ curry f △ curry g.
Proof.
  simpl.
  apply uncurry_inj; cat.
  rewrite uncurry_comp; cat.
  unfold first.
  rewrite <- fork_comp.
  apply fork_inv; split;
  rewrite <- eval_curry;
  rewrite curry_uncurry;
  rewrite comp_assoc; cat.
Qed.

Corollary curry_unfork {x y z w : C} (f : x × y ~> z) (g : x × y ~> w) :
  curry f △ curry g ≈ to exp_prod_r ∘ curry (f △ g).
Proof.
  rewrite curry_fork.
  rewrite comp_assoc.
  rewrite iso_to_from; cat.
Qed.

Context `{@Terminal C}.

Global Program Instance exp_one {x : C} :
  x^One ≅ x := {
  to   := eval ∘ id △ one;
  from := curry exl
}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite <- fork_comp; cat.
  rewrite <- (id_right (curry exl)); cat.
Qed.
Next Obligation.
  rewrite comp_assoc.
  rewrite !curry_comp_l.
  apply uncurry_inj; cat.
  unfold first, eval; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- fork_comp.
  rewrite id_left.
  cut (@one _ _ (x^One) ∘ exl ≈ exr).
    intros; rewrites; cat.
  cat.
Qed.

Hint Rewrite @exp_one : isos.

End Closed.

Notation "y ^ x" := (Exp x y) : category_scope.

Hint Rewrite @curry_uncurry : categories.
Hint Rewrite @uncurry_curry : categories.
Hint Rewrite @ump_exponents : categories.
Hint Rewrite @eval_curry : categories.
Hint Rewrite @curry_eval : categories.
Hint Rewrite @exp_prod_l : isos.
Hint Rewrite @exp_prod_r : isos.
Hint Rewrite @exp_one : isos.
