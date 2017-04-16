Require Import Category.Lib.
Require Export Category.Structure.Cartesian.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Closed.

Context `{C : Category}.
Context `{@Cartesian C}.

Class Closed := {
  Exp : ob -> ob -> ob    (* internal homs *)
    where "Y ^ X" := (Exp X Y);

  exp_iso {X Y Z} : X × Y ~{C}~> Z ≃ X ~> Z^Y;

  curry'   {X Y Z} := to (@exp_iso X Y Z);
  uncurry' {X Y Z} := from (@exp_iso X Y Z);

  eval' {X Y} : Y^X × X ~> Y := uncurry' _ _ _ id;

  ump_exponents' {X Y Z} (f : X × Y ~> Z) :
    eval' ∘ first (curry' _ _ _ f) ≈ f
}.

Notation "Y ^ X" := (Exp X Y) : category_scope.

Context `{@Closed}.

Definition curry   {X Y Z} := @curry' _ X Y Z.
Definition uncurry {X Y Z} := @uncurry' _ X Y Z.
Arguments curry' {_ _ _ _} /.
Arguments uncurry' {_ _ _ _} /.

Definition eval {X Y} : Y^X × X ~> Y := @eval' _ X Y.
Arguments eval' {_ _ _} /.

Definition ump_exponents {X Y Z} (f : X × Y ~> Z) :
  eval ∘ first (curry f) ≈ f := @ump_exponents' _ X Y Z f.

Corollary curry_uncurry {X Y Z} (f : X ~> Z^Y) :
  curry (uncurry f) ≈ f.
Proof.
  replace (curry (uncurry f)) with ((curry ∘ uncurry) f) by auto.
  unfold curry, uncurry; simpl.
  pose proof (iso_to_from (@exp_iso _ X Y Z)) as HA.
  simpl in HA.
  rewrite HA; cat.
Qed.

Corollary uncurry_curry {X Y Z} (f : X × Y ~> Z) :
  uncurry (curry f) ≈ f.
Proof.
  replace (uncurry (curry f)) with ((uncurry ∘ curry) f) by auto.
  unfold curry, uncurry; simpl.
  pose proof (iso_from_to (@exp_iso _ X Y Z)) as HA.
  simpl in HA.
  rewrite HA; cat.
Qed.

Hint Rewrite @curry_uncurry : categories.
Hint Rewrite @uncurry_curry : categories.
Hint Rewrite @ump_exponents : categories.

Global Program Instance parametric_morphism_curry (a b c : C) :
  Proper (equiv ==> equiv) (@curry a b c).
Next Obligation.
  intros ?? HA.
  unfold curry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct to; simpl in *.
  rewrite HA; reflexivity.
Defined.

Global Program Instance parametric_morphism_uncurry (a b c : C) :
  Proper (equiv ==> equiv) (@uncurry a b c).
Next Obligation.
  intros ?? HA.
  unfold uncurry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct from; simpl in *.
  rewrite HA; reflexivity.
Defined.

Definition flip {X Y Z : C} `(f : X ~> Z ^ Y) : Y ~> Z ^ X :=
  curry (uncurry f ∘ swap).

Corollary eval_curry {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) (h : X ~> Z) :
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

Corollary curry_eval {X Y : C} :
  curry eval ≈ @id _ (Y^X).
Proof.
  intros; unfold eval; simpl; cat.
Qed.

Hint Rewrite @curry_eval : categories.

Corollary eval_first {X Y Z : C} (f : X ~> Z^Y) :
  eval ∘ first f ≈ uncurry f.
Proof.
  rewrite <- (curry_uncurry f); cat.
Qed.

Corollary curry_inj {X Y Z : C} (f g : X × Y ~> Z) :
  curry f ≈ curry g -> f ≈ g.
Proof.
  intros Hcurry.
  rewrite <- (uncurry_curry f).
  rewrite <- (uncurry_curry g).
  rewrite Hcurry; reflexivity.
Qed.

Corollary uncurry_inj {X Y Z : C} (f g : X ~> Z^Y) :
  uncurry f ≈ uncurry g -> f ≈ g.
Proof.
  intros Hcurry.
  rewrite <- (curry_uncurry f).
  rewrite <- (curry_uncurry g).
  rewrite Hcurry; reflexivity.
Qed.

Corollary curry_comp_l {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) :
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

Corollary curry_comp {X Y Z W : C} (f : Z ~> W) (g : X × Y ~> Z) :
  curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g.
Proof.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite eval_first; cat.
Qed.

Corollary uncurry_comp_r {X Y Z W : C} (f : Z ~> W) (g : X ~> Z^Y) :
  f ∘ uncurry g ≈ uncurry (curry (f ∘ eval) ∘ g).
Proof.
  rewrite curry_comp_l; cat.
  rewrite <- comp_assoc.
  rewrite eval_first; reflexivity.
Qed.

Corollary uncurry_comp {X Y Z W : C} (f : Y ~> W^Z) (g : X ~> Y) :
  uncurry (f ∘ g) ≈ uncurry f ∘ first g.
Proof.
  intros.
  apply curry_inj; cat.
  rewrite <- curry_comp_l; cat.
Qed.

Theorem curry_id {X Y Z : C} (f : X ~> Y) :
  curry (@id _ (Y × Z)) ∘ f ≈ curry (first f).
Proof.
  intros.
  rewrite curry_comp_l.
  apply uncurry_inj; cat.
Qed.

Global Program Instance exp_prod_l {X Y Z : C} :
  Z^(X × Y) ≅ (Z^Y)^X := {
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

(* (Y × Z)^X ~> Y^X × Z^X *)
Global Program Instance exp_prod_r {X Y Z : C} :
  (Y × Z)^X ≅ Y^X × Z^X := {
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
  rewrite HA; cat.
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

Context `{@Terminal C}.

Notation "X ^ 1" := (Exp One X) (at level 30).

Global Program Instance exp_one {X : C} :
  X^1 ≅ X := {
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
  cut (@one _ _ (X^1) ∘ exl ≈ exr).
    intro Hone.
    rewrite Hone; cat.
  cat.
Qed.

Hint Rewrite @exp_one : isos.

End Closed.

Notation "Y ^ X" := (Exp X Y) : category_scope.

Notation "X ^ 1" := (Exp One X) (at level 30).

Hint Rewrite @curry_uncurry : categories.
Hint Rewrite @uncurry_curry : categories.
Hint Rewrite @ump_exponents : categories.
Hint Rewrite @eval_curry : categories.
Hint Rewrite @curry_eval : categories.
Hint Rewrite @exp_prod_l : isos.
Hint Rewrite @exp_prod_r : isos.
Hint Rewrite @exp_one : isos.

Section ClosedFunctor.

Context `{F : C ⟶ D}.
Context `{@CartesianFunctor C D F CA CB}.
Context `{@Closed C CA}.
Context `{@Closed D CB}.

Class ClosedFunctor := {
  fobj_exp_iso {X Y : C} : F (Y^X) ≅ F Y ^ F X;

  exp_in  := fun X Y => from (@fobj_exp_iso X Y);
  exp_out := fun X Y => to   (@fobj_exp_iso X Y);

  fmap_curry {X Y Z : C} {f : X × Y ~> Z} :
    fmap (curry f) ≈ exp_in _ _ ∘ curry (fmap f ∘ prod_in);
  fmap_uncurry {X Y Z : C} (f : X ~> Z^Y) :
    fmap (uncurry f) ≈ uncurry (exp_out _ _ ∘ fmap f) ∘ prod_out
}.

Context `{@ClosedFunctor}.

Arguments exp_in {_ _ _} /.
Arguments exp_out {_ _ _} /.

Corollary fmap_eval {X Y : C} :
  fmap (@eval C _ _ X Y) ≈ uncurry (curry eval ∘ exp_out) ∘ prod_out.
Proof.
  intros.
  unfold eval, eval'.
  rewrite fmap_uncurry; cat.
Qed.

Corollary exp_in_out {X Y : C} :
  exp_in ∘ exp_out ≈ @id _ (F (Y^X)).
Proof. apply iso_from_to. Qed.

Hint Rewrite @exp_in_out : functors.

Corollary exp_out_in {X Y : C} :
  exp_out ∘ exp_in ≈ @id _ (F Y ^ F X).
Proof. apply iso_to_from. Qed.

Hint Rewrite @exp_out_in : functors.

Corollary exp_in_inj {X Y Z : C} (f g : F X ~> F Z ^ F Y) :
  exp_in ∘ f ≈ exp_in ∘ g <-> f ≈ g.
Proof.
  split; intros Hexp.
    rewrite <- id_left.
    rewrite <- exp_out_in.
    rewrite <- comp_assoc.
    rewrite Hexp.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hexp.
  reflexivity.
Qed.

Corollary exp_out_inj {X Y Z : C} (f g : F X ~> F (Z^Y)) :
  exp_out ∘ f ≈ exp_out ∘ g <-> f ≈ g.
Proof.
  split; intros Hexp.
    rewrite <- id_left.
    rewrite <- exp_in_out.
    rewrite <- comp_assoc.
    rewrite Hexp.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hexp.
  reflexivity.
Qed.

End ClosedFunctor.

Arguments exp_in {_ _ _ _ _ _ _ _ _ _ _} /.
Arguments exp_out {_ _ _ _ _ _ _ _ _ _ _} /.

Hint Rewrite @exp_in_out : functors.
Hint Rewrite @exp_out_in : functors.
