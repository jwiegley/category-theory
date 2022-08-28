Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Export Category.Structure.Premonoidal.

Generalizable All Variables.

Section Monoidal.

Context {C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Program Definition Fork {C : Category} `{@Binoidal C} :
  C ∏ C ⟶ C := {|
  fobj := λ '(x, y), (x ⊗ y)%object;
  fmap := fun _ _ '(f, g) => f ⊗ g
|}.
Next Obligation.
  proper; simpl in *.
  destruct H.
  now rewrite X, H0.
Qed.
Next Obligation.
  unfold composite_ff'; simpl.
  rewrite l_fmap_id, r_fmap_id; cat.
Qed.
Next Obligation.
  unfold composite_ff'; simpl.
  rewrite l_fmap_comp, r_fmap_comp.
  comp_left.
  rewrite !comp_assoc.
  comp_right.
  enough (central h0).
  - now rewrite (snd (X _ _ h1)).
  - repeat intro.
    split; simpl.
    + destruct H; simpl.
Admitted.

Class Monoidal := {
  monoidal_is_premonoidal : @Premonoidal C;

  tensor : C ∏ C ⟶ C := Fork where "x ⨂ y" := (tensor (x, y));
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "x ⨂ y" := (@tensor _ _ (x%object, y%object))
  (at level 30, right associativity) : object_scope.
Notation "x ⨂[ M ] y" := (fobj[@tensor _ M] (x, y))
  (at level 30, only parsing, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.
Notation "f ⨂[ M ] g" := (bimap[@tensor _ M] f g)
  (at level 30, only parsing, right associativity) : morphism_scope.
