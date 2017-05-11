Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Closed.
Require Export Category.Functor.Structure.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

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
  exp_in ∘ f ≈ exp_in ∘ g <--> f ≈ g.
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
  exp_out ∘ f ≈ exp_out ∘ g <--> f ≈ g.
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
