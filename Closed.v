Require Import Lib.
Require Export Cartesian.

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

  curry   {X Y Z} (f : X × Y ~> Z) : X ~> Z^Y;
  uncurry {X Y Z} (f : X ~> Z^Y) : X × Y ~> Z;

  eval {X Y} : Y^X × X ~> Y := uncurry id;

  curry_respects   : ∀ X Y Z, Proper (eqv ==> @eqv _ X (Z^Y))   curry;
  uncurry_respects : ∀ X Y Z, Proper (eqv ==> @eqv _ (X × Y) Z) uncurry;

  curry_uncurry {X Y Z} (f : X ~> Z^Y) :   curry   (uncurry f) ≈ f;
  uncurry_curry {X Y Z} (f : X × Y ~> Z) : uncurry (curry   f) ≈ f;

  univ_exponents {X Y Z} (f : X × Y ~> Z) :
    eval ∘ first (curry f) ≈ f
}.

Notation "Y ^ X" := (Exp X Y) : category_scope.

Context `{@Closed}.

Hint Rewrite @curry_uncurry : categories.
Hint Rewrite @uncurry_curry : categories.
Hint Rewrite @univ_exponents : categories.

Global Program Instance parametric_morphism_curry (a b c : C) :
  Proper (eqv ==> eqv) curry := curry_respects a b c.

Global Program Instance parametric_morphism_uncurry (a b c : C) :
  Proper (eqv ==> eqv) uncurry := uncurry_respects a b c.

Corollary eval_curry {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) (h : X ~> Z) :
  eval ∘ ((curry f ∘ g) △ h) ≈ f ∘ g △ h.
Proof.
  intros.
  rewrite <- (univ_exponents f) at 2.
  rewrite <- comp_assoc.
  unfold first.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
Qed.

Hint Rewrite @eval_curry : categories.

Corollary curry_eval {X Y : C} :
  curry eval ≈ @id _ (Y^X).
Proof.
  intros; unfold eval; cat.
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
  intros.
  apply uncurry_inj; cat.
  rewrite <- (univ_exponents (uncurry (curry f ∘ g))).
  rewrite curry_uncurry.
  unfold first in *.
  rewrite <- comp_assoc.
  rewrite eval_curry.
  reflexivity.
Qed.

Corollary curry_comp {X Y Z W : C} (f : Z ~> W) (g : X × Y ~> Z) :
  curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g.
Proof.
  intros.
  rewrite curry_comp_l.
  apply uncurry_inj; cat.
  rewrite <- comp_assoc.
  rewrite eval_first; cat.
Qed.

Corollary uncurry_comp_r {X Y Z W : C} (f : Z ~> W) (g : X ~> Z^Y) :
  f ∘ uncurry g ≈ uncurry (curry (f ∘ eval) ∘ g).
Proof.
  intros.
  apply curry_inj; cat.
  rewrite <- (univ_exponents (f ∘ eval)).
  rewrite eval_first; cat.
  rewrite curry_comp_l.
  apply uncurry_inj; cat.
  rewrite <- comp_assoc.
  rewrite eval_first.
  reflexivity.
Qed.

Corollary uncurry_comp {X Y Z W : C} (f : Y ~> W^Z) (g : X ~> Y) :
  uncurry (f ∘ g) ≈ uncurry f ∘ uncurry (curry id ∘ g).
Proof.
  intros.
  rewrite uncurry_comp_r.
  apply curry_inj; cat.
  rewrite comp_assoc.
  rewrite <- curry_comp; cat.
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
  iso_to   := curry (curry (eval ∘ iso_to prod_assoc));
  iso_from := curry (uncurry eval ∘ iso_from prod_assoc)
}.
Obligation 1.
  constructor; simpl; intros.
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
Admitted.

Hint Rewrite @exp_prod_l : isos.

Global Program Instance exp_prod_r {X Y Z : C} :
  (Y × Z)^X ≅ Y^X × Z^X := {
  iso_to   := _;
  iso_from := _
}.
Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 3.
Admitted.

Hint Rewrite @exp_prod_r : isos.

Context `{@Terminal C}.

Notation "X ^ 1" := (Exp One X) (at level 30).

Global Program Instance exp_one {X : C} :
  X^1 ≅ X := {
  iso_to   := eval ∘ id △ one;
  iso_from := curry exl
}.
Obligation 1.
  constructor; simpl; intros.
    rewrite <- comp_assoc.
    rewrite <- fork_comp; cat.
    rewrite <- (id_right (curry exl)); cat.
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
Hint Rewrite @univ_exponents : categories.
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

  exp_in  := fun X Y => iso_from (@fobj_exp_iso X Y);
  exp_out := fun X Y => iso_to   (@fobj_exp_iso X Y);

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
  unfold eval.
  rewrite fmap_uncurry; cat.
Qed.

Corollary exp_in_out {X Y : C} :
  exp_in ∘ exp_out ≈ @id _ (F (Y^X)).
Proof.
  intros.
  apply iso_from_to.
  apply iso_witness.
Qed.

Hint Rewrite @exp_in_out : functors.

Corollary exp_out_in {X Y : C} :
  exp_out ∘ exp_in ≈ @id _ (F Y ^ F X).
Proof.
  intros.
  apply iso_to_from.
  apply iso_witness.
Qed.

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
