Set Warnings "-notation-overridden".

Require Import Category.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 40, left associativity).

Class Category := {
  ob : Type;

  uhom := Type : Type;
  hom : ob -> ob -> uhom where "a ~> b" := (hom a b);
  homset :> ∀ X Y, Setoid (X ~> Y);

  id {A} : A ~> A;
  compose {A B C} (f: B ~> C) (g : A ~> B) : A ~> C
    where "f ∘ g" := (compose f g);

  compose_respects (X Y Z : ob) :>
    Proper (equiv ==> equiv ==> equiv) (@compose X Y Z);

  dom {A B} (f: A ~> B) := A;
  cod {A B} (f: A ~> B) := B;

  id_left  {X Y} (f : X ~> Y) : id ∘ f ≈ f;
  id_right {X Y} (f : X ~> Y) : f ∘ id ≈ f;

  comp_assoc {X Y Z W} (f : Z ~> W) (g : Y ~> Z) (h : X ~> Y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
}.

Arguments dom {_ _ _} _.
Arguments cod {_ _ _} _.

Infix "~>" := hom (at level 90, right associativity) : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 90) : category_scope.
Infix "∘" := compose : category_scope.

Notation "ob[ C ]" := (@ob C) (at level 0, format "ob[ C ]") : category_scope.
Notation "id[ X ]" := (@id _ X)
  (at level 50, format "id[ X ]") : category_scope.

Notation "f ≈[ C ] g" := (@equiv _ (@homset C _ _) f g)
  (at level 79, only parsing) : category_scope.

Coercion ob : Category >-> Sortclass.

Hint Rewrite @id_left : categories.
Hint Rewrite @id_right : categories.

Section Category.

Context `{C : Category}.

Corollary dom_id {X : C} : dom (@id C X) = X.
Proof. auto. Qed.

Corollary cod_id {X : C} : dom (@id C X) = X.
Proof. auto. Qed.

Corollary dom_comp {X Y Z : C} (g : Y ~> Z) (f : X ~> Y) :
  dom g = cod f <-> dom (g ∘ f) = dom f.
Proof. split; auto. Qed.

Corollary cod_comp {X Y Z : C} (g : Y ~> Z) (f : X ~> Y) :
  dom g = cod f <-> cod (g ∘ f) = cod g.
Proof. split; auto. Qed.

End Category.

Hint Extern 10 (?X ∘ ?Y ≈ ?Z ∘ ?Q) =>
  apply compose_respects; auto : category_laws.
Hint Extern 10 (?X ∘ (?Y ∘ ?Z) ≈ ?W) =>
  rewrite <- comp_assoc; cat : category_laws.
Hint Extern 10 ((?X ∘ ?Y) ∘ ?Z ≈ ?W) =>
  rewrite comp_assoc; cat : category_laws.
