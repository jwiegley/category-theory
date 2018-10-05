Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Cartesian.Closed.
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
  fobj_exp_iso {x y : C} : F (y^x) ≅ F y ^ F x;

  exp_in  := fun x y => from (@fobj_exp_iso x y);
  exp_out := fun x y => to   (@fobj_exp_iso x y);

  fmap_curry {x y z : C} {f : x × y ~> z} :
    fmap (curry f) ≈ exp_in _ _ ∘ curry (fmap f ∘ prod_in);
  fmap_uncurry {x y z : C} (f : x ~> z^y) :
    fmap (uncurry f) ≈ uncurry (exp_out _ _ ∘ fmap f) ∘ prod_out
}.

Context `{@ClosedFunctor}.

Arguments exp_in {_ _ _} /.
Arguments exp_out {_ _ _} /.

Corollary fmap_eval {x y : C} :
  fmap (@eval C _ _ x y) ≈ uncurry (curry eval ∘ exp_out) ∘ prod_out.
Proof.
  intros.
  unfold eval, eval'.
  rewrite fmap_uncurry; cat.
Qed.

Corollary exp_in_out {x y : C} :
  exp_in ∘ exp_out ≈ @id _ (F (y^x)).
Proof. apply iso_from_to. Qed.

Hint Rewrite @exp_in_out : functors.

Corollary exp_out_in {x y : C} :
  exp_out ∘ exp_in ≈ @id _ (F y ^ F x).
Proof. apply iso_to_from. Qed.

Hint Rewrite @exp_out_in : functors.

Corollary exp_in_inj {x y z : C} (f g : F x ~> F z ^ F y) :
  exp_in ∘ f ≈ exp_in ∘ g ↔ f ≈ g.
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

Corollary exp_out_inj {x y z : C} (f g : F x ~> F (z^y)) :
  exp_out ∘ f ≈ exp_out ∘ g ↔ f ≈ g.
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
