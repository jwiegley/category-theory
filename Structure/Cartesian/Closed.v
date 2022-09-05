Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Closed.

Context {C : Category}.
Context `{@Cartesian C}.

Class Closed := {
  exponent_obj : obj → obj → obj    (* internal homs *)
    where "y ^ x" := (exponent_obj x y);

  exp_iso {x y z} : x × y ~> z ≊ x ~> z^y;

  curry'   {x y z} : x × y ~> z → x ~> z^y := to (@exp_iso x y z);
  uncurry' {x y z} : x ~> z^y → x × y ~> z := from (@exp_iso x y z);

  eval' {x y} : y^x × x ~> y := @uncurry' _ _ _ id;

  ump_exponents' {x y z} (f : x × y ~> z) :
    eval' ∘ first (@curry' _ _ _ f) ≈ f
}.

Notation "y ^ x" := (exponent_obj x y)
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

Corollary curry_uncurry {x y z} (f : x ~> z^y) :
  curry (uncurry f) ≈ f.
Proof.
  sapply (iso_to_from (@exp_iso _ x y z)).
Qed.

Corollary uncurry_curry {x y z} (f : x × y ~> z) :
  uncurry (curry f) ≈ f.
Proof.
  sapply (iso_from_to (@exp_iso _ x y z)).
Qed.

#[local] Hint Rewrite @curry_uncurry : categories.
#[local] Hint Rewrite @uncurry_curry : categories.
#[local] Hint Rewrite @ump_exponents : categories.

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

#[local] Hint Rewrite @eval_curry : categories.

Corollary curry_eval {x y : C} :
  curry eval ≈ @id _ (y^x).
Proof.
  intros; unfold eval; simpl; cat.
Qed.

#[local] Hint Rewrite @curry_eval : categories.

Corollary eval_first {x y z : C} (f : x ~> z^y) :
  eval ∘ first f ≈ uncurry f.
Proof.
  rewrite <- (curry_uncurry f); cat.
Qed.

Corollary curry_inj {x y z : C} (f g : x × y ~> z) :
  curry f ≈ curry g → f ≈ g.
Proof.
  intros.
  rewrite <- (uncurry_curry f).
  rewrite <- (uncurry_curry g).
  rewrites; reflexivity.
Qed.

Corollary uncurry_inj {x y z : C} (f g : x ~> z^y) :
  uncurry f ≈ uncurry g → f ≈ g.
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

#[global] Program Instance exp_respects_iso {x y z : C} :
  Proper (Isomorphism ==> Isomorphism ==> Isomorphism) exponent_obj.
Next Obligation.
  proper.
  transitivity (y1 ^ x0). {
    isomorphism.
    - apply (curry (to X0 ∘ eval)).
    - apply (curry (from X0 ∘ eval)).
    - rewrite <- curry_comp.
      rewrite comp_assoc.
      rewrite iso_to_from, id_left.
      rewrite curry_eval.
      reflexivity.
    - rewrite <- curry_comp.
      rewrite comp_assoc.
      rewrite iso_from_to, id_left.
      rewrite curry_eval.
      reflexivity.
  }
  isomorphism.
  - apply (curry (eval ∘ second (from X))).
  - apply (curry (eval ∘ second (to X))).
  - rewrite curry_comp_l.
    rewrite <- comp_assoc.
    rewrite <- first_second.
    rewrite comp_assoc.
    rewrite eval_first.
    rewrite uncurry_curry.
    rewrite <- comp_assoc.
    rewrite <- second_comp.
    rewrite iso_to_from.
    rewrite second_id, id_right.
    rewrite curry_eval.
    reflexivity.
  - rewrite curry_comp_l.
    rewrite <- comp_assoc.
    rewrite <- first_second.
    rewrite comp_assoc.
    rewrite eval_first.
    rewrite uncurry_curry.
    rewrite <- comp_assoc.
    rewrite <- second_comp.
    rewrite iso_from_to.
    rewrite second_id, id_right.
    rewrite curry_eval.
    reflexivity.
Qed.

#[global] Program Instance exp_prod_l {x y z : C} :
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

#[local] Hint Rewrite @exp_prod_l : isos.

#[global] Program Instance exp_prod_r {x y z : C} :
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

#[local] Hint Rewrite @exp_prod_r : isos.

#[local] Obligation Tactic := program_simpl.

#[global] Program Instance exp_swap {x y z : C} :
  (z^y)^x ≅ (z^x)^y := {
  to   := to exp_prod_l
        ∘ to (@exp_respects_iso x y z _ _ (@prod_comm _ _ x y) z z iso_id)
        ∘ from exp_prod_l;
  from := to exp_prod_l
        ∘ from (@exp_respects_iso x y z _ _ (@prod_comm _ _ x y) z z iso_id)
        ∘ from exp_prod_l
}.
Next Obligation.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (curry _) (curry _)).
  rewrite (iso_from_to exp_prod_l), id_left.
  rewrite (comp_assoc (exp_respects_iso _ _ _ _ _ _)).
  rewrite iso_to_from, id_left.
  apply (iso_to_from exp_prod_l).
Defined.
Next Obligation.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (curry _) (curry _)).
  rewrite (iso_from_to exp_prod_l), id_left.
  rewrite (comp_assoc _ (exp_respects_iso _ _ _ _ _ _)).
  rewrite iso_from_to, id_left.
  apply (iso_to_from exp_prod_l).
Defined.

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

#[global] Program Instance exp_one {x : C} :
  x^1 ≅ x := {
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
  cut (@one _ _ (x^1) ∘ exl ≈ exr).
    intros; rewrites; cat.
  cat.
Qed.

#[local] Hint Rewrite @exp_one : isos.

#[global] Program Instance one_exp {x : C} :
  1^x ≅ 1 := {
  to   := one;
  from := curry one
}.
Next Obligation. apply one_unique. Qed.
Next Obligation.
  rewrite curry_comp_l.
  rewrite one_comp.
  apply uncurry_inj.
  rewrite uncurry_curry.
  apply one_unique.
Qed.

#[local] Hint Rewrite @one_exp : isos.

End Closed.

Notation "y ^ x" := (exponent_obj x y) : category_scope.

#[export] Hint Rewrite @curry_uncurry : categories.
#[export] Hint Rewrite @uncurry_curry : categories.
#[export] Hint Rewrite @ump_exponents : categories.
#[export] Hint Rewrite @eval_curry : categories.
#[export] Hint Rewrite @curry_eval : categories.
#[export] Hint Rewrite @exp_prod_l : isos.
#[export] Hint Rewrite @exp_prod_r : isos.
#[export] Hint Rewrite @exp_one : isos.
