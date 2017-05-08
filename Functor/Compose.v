Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

Program Definition Compose
        `{C : Category} `{D : Category} `{E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.
Next Obligation.
  proper.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  intros; rewrite !fmap_comp; reflexivity.
Qed.

Hint Unfold Compose.

Infix "○" := Compose (at level 30, right associativity) : category_scope.
