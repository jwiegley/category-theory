Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Functor.

Context `{C : Category}.
Context `{D : Category}.

Class Functor := {
  fobj : C -> D;
  fmap {X Y : C} (f : X ~> Y) : fobj X ~> fobj Y;

  fmap_respects {X Y} :> Proper (equiv ==> equiv) (@fmap X Y);

  fmap_id {X : C} : fmap (@id C X) ≈ id;
  fmap_comp {X Y Z : C} (f : Y ~> Z) (g : X ~> Y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.

End Functor.

(* Functors used as functions will map objects of categories, similar to the
   way type constructors behave in Haskell. *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C D) (at level 90, right associativity).

Arguments fmap {C D Functor X Y} f.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : category_scope.
Infix "<$[ F ]>" := (@fmap _ _ F _ _)
  (at level 29, left associativity, only parsing) : category_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : category_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : category_scope.

Notation "fmap[ F ]" := (@fmap _ _ F _ _)
  (at level 9, format "fmap[ F ]") : category_scope.

Hint Rewrite @fmap_id : categories.

Program Definition functor_comp
        `{C : Category} `{D : Category} `{E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.
Next Obligation.
  intros ?? HA.
  rewrite HA; reflexivity.
Qed.
Next Obligation.
  intros.
  rewrite !fmap_id.
  reflexivity.
Qed.
Next Obligation.
  intros.
  rewrite !fmap_comp.
  reflexivity.
Qed.

Infix "○" := functor_comp (at level 30, right associativity) : category_scope.

(* The Identity [Functor] *)

Global Program Instance Identity : C ⟶ C := {
  fobj := fun X => X;
  fmap := fun _ _ f => f
}.
(* Next Obligation. repeat intro; auto. Qed. *)
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
