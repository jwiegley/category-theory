Require Import Lib.
Require Export Cartesian.

Generalizable All Variables.

Class Closed (ob : Type) := {
  closed_cartesian :> Cartesian ob;

  Exp : ob -> ob -> ob    (* internal homs *)
    where "Y ^ X" := (Exp X Y);

  curry   {X Y Z} (f : X × Y ~> Z) : X ~> Z^Y;
  uncurry {X Y Z} (f : X ~> Z^Y) : X × Y ~> Z;

  eval {X Y} : Y^X × X ~> Y := uncurry id;

  curry_respects   : ∀ X Y Z, Proper (eqv ==> @eqv _ _ X (Z^Y))   curry;
  uncurry_respects : ∀ X Y Z, Proper (eqv ==> @eqv _ _ (X × Y) Z) uncurry;

  curry_uncurry {X Y Z} (f : X ~> Z^Y) :   curry   (uncurry f) ≈ f;
  uncurry_curry {X Y Z} (f : X × Y ~> Z) : uncurry (curry   f) ≈ f;

  univ_exponents {X Y Z} (f : X × Y ~> Z) :
    eval ∘ first (curry f) ≈ f
}.

Notation "Y ^ X" := (Exp X Y) : category_scope.

Hint Rewrite @curry_uncurry : categories.
Hint Rewrite @uncurry_curry : categories.
Hint Rewrite @univ_exponents : categories.

Global Program Instance parametric_morphism_curry `(_ : Closed C) (a b c : C) :
  Proper (eqv ==> eqv)  (@curry C _ a b c) := curry_respects a b c.

Global Program Instance parametric_morphism_uncurry `(_ : Closed C) (a b c : C) :
  Proper (eqv ==> eqv)  (@uncurry C _ a b c) := uncurry_respects a b c.

Corollary eval_curry `{Closed C}
          {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) (h : X ~> Z) :
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

Corollary eval_first `{Closed C} {X Y Z : C} (f : X ~> Z^Y) :
  eval ∘ first f ≈ uncurry f.
Proof.
  rewrite <- (curry_uncurry f); cat.
Qed.

Corollary curry_uncurry' `{Closed C} {X Y Z : C} (f : X ~> Z^Y) :
  curry (uncurry f) ≈ f.
Proof.
  (* Can this be proven in terms of the universal property? *)
Abort.

Corollary curry_inj `{Closed C} {X Y Z : C} (f g : X × Y ~> Z) :
  curry f ≈ curry g -> f ≈ g.
Proof.
  intros.
  rewrite <- (uncurry_curry f).
  rewrite <- (uncurry_curry g).
  rewrite H0; reflexivity.
Qed.

Corollary uncurry_inj `{Closed C} {X Y Z : C} (f g : X ~> Z^Y) :
  uncurry f ≈ uncurry g -> f ≈ g.
Proof.
  intros.
  rewrite <- (curry_uncurry f).
  rewrite <- (curry_uncurry g).
  rewrite H0; reflexivity.
Qed.

Corollary curry_eval `{Closed C} {X Y : C} :
  curry eval ≈ @id _ _ (Y^X).
Proof.
  intros; unfold eval; cat.
Qed.

Hint Rewrite @curry_eval : categories.

Corollary curry_comp_l `{Closed C}
          {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) :
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

Corollary curry_comp `{Closed C}
          {X Y Z W : C} (f : Z ~> W) (g : X × Y ~> Z) :
  curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g.
Proof.
  intros.
  rewrite curry_comp_l.
  apply uncurry_inj; cat.
  rewrite <- comp_assoc.
  rewrite eval_first; cat.
Qed.

Corollary uncurry_comp_r `{Closed C}
          {X Y Z W : C} (f : Z ~> W) (g : X ~> Z^Y) :
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

Corollary uncurry_comp `{Closed C}
          {X Y Z W : C} (f : Y ~> W^Z) (g : X ~> Y) :
  uncurry (f ∘ g) ≈ uncurry f ∘ uncurry (curry id ∘ g).
Proof.
  intros.
  rewrite uncurry_comp_r.
  apply curry_inj; cat.
  rewrite comp_assoc.
  rewrite <- curry_comp; cat.
Qed.

Theorem curry_id `{Closed C} {X Y Z : C} (f : X ~> Y) :
  curry (@id _ _ (Y × Z)) ∘ f ≈ curry (first f).
Proof.
  intros.
  rewrite curry_comp_l.
  apply uncurry_inj; cat.
Qed.

Theorem exp_prod_l `{Closed C} {X Y Z : C} :
  Z^(X × Y) ≅ (Z^Y)^X.
Proof.
  intros.
  refine {| iso_to   := curry (curry (eval ∘ iso_to prod_comp))
          ; iso_from := curry (uncurry eval ∘ iso_from prod_comp) |}.
  constructor; simpl; intros.
Admitted.

Hint Rewrite @exp_prod_l : isos.

Theorem exp_prod_r `{Closed C} {X Y Z : C} :
  (Y × Z)^X ≅ Y^X × Z^X.
Proof.
  intros.
  refine {| iso_to   := _
          ; iso_from := _ |}.
  constructor; simpl; intros.
Admitted.

Hint Rewrite @exp_prod_r : isos.

Notation "X ^ 1" := (Exp One X) (at level 30).

Theorem exp_one `{Closed C} {X : C} :
  X^1 ≅ X.
Proof.
  intros.
  refine {| iso_to   := eval ∘ id △ one
          ; iso_from := curry exl |}.
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
  cut (@one _ _ (X^1) ∘ exl ≈ exr); intros.
    rewrite H0; cat.
  cat.
Qed.

Hint Rewrite @exp_one : isos.

Class ClosedFunctor `(_ : Closed C) `(_ : Closed D) := {
  cartesian_functor :> CartesianFunctor C D;

  fobj_exp_iso {X Y : C} : fobj (Y^X) ≅ fobj Y ^ fobj X;

  exp_in  := fun X Y => iso_from (@fobj_exp_iso X Y);
  exp_out := fun X Y => iso_to   (@fobj_exp_iso X Y);

  fmap_curry {X Y Z : C} {f : X × Y ~> Z} :
    fmap (@curry C _ X Y Z f) ≈ exp_in _ _ ∘ curry (fmap f ∘ prod_in);
  fmap_uncurry {X Y Z : C} (f : X ~> Z^Y) :
    fmap (@uncurry C _ X Y Z f) ≈ uncurry (exp_out _ _ ∘ fmap f) ∘ prod_out
}.

Arguments ClosedFunctor C {_} D {_}.

Arguments exp_in {C _ D _ _ _ _} /.
Arguments exp_out {C _ D _ _ _ _} /.

Corollary fmap_eval `{ClosedFunctor C D} {X Y : C} :
  fmap (@eval C _ X Y) ≈ uncurry (curry eval ∘ exp_out) ∘ prod_out.
Proof.
  intros.
  unfold eval.
  rewrite fmap_uncurry; cat.
Qed.

Corollary exp_in_out `{ClosedFunctor C D} {X Y : C} :
  exp_in ∘ exp_out ≈ @id _ _ (fobj (Y^X)).
Proof.
  intros.
  apply iso_from_to.
  apply iso_witness.
Qed.

Hint Rewrite @exp_in_out : functors.

Corollary exp_out_in `{ClosedFunctor C D} {X Y : C} :
  exp_out ∘ exp_in ≈ @id _ _ (fobj Y ^ fobj X).
Proof.
  intros.
  apply iso_to_from.
  apply iso_witness.
Qed.

Hint Rewrite @exp_out_in : functors.

Corollary exp_in_inj `{ClosedFunctor C D}
          {X Y Z : C} (f g : fobj X ~> fobj Z ^ fobj Y) :
  exp_in ∘ f ≈ exp_in ∘ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- exp_out_in.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Corollary exp_out_inj `{ClosedFunctor C D}
          {X Y Z : C} (f g : fobj X ~> fobj (Z^Y)) :
  exp_out ∘ f ≈ exp_out ∘ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- exp_in_out.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite H2.
  reflexivity.
Qed.
