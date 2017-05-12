Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Functor.

Context `{C : Category}.
Context `{D : Category}.

Class Functor := {
  fobj : C -> D;
  fmap {X Y : C} (f : X ~> Y) : fobj X ~> fobj Y;

  fmap_respects :> ∀ X Y, Proper (equiv ==> equiv) (@fmap X Y);

  fmap_id {X : C} : fmap (@id C X) ≈ id;
  fmap_comp {X Y Z : C} (f : Y ~> Z) (g : X ~> Y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.

End Functor.

Bind Scope functor_scope with Functor.
Delimit Scope functor_type_scope with functor_type.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.
Open Scope functor_scope.

(* Functors used as functions will map objects of categories, similar to the
   way type constructors behave in Haskell. *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

Arguments fmap
  {C%category D%category Functor%functor X%object Y%object} f%morphism.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : morphism_scope.
Infix "<$[ F ]>" := (@fmap _ _ F%functor _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "fobj[ F ]" := (@fobj _ _ F%functor)
  (at level 9, format "fobj[ F ]") : object_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 9, format "fmap[ F ]") : morphism_scope.

Hint Rewrite @fmap_id : categories.

Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).

Section Identity.

Context `{C : Category}.
Context `{D : Category}.

Global Program Definition Id : C ⟶ C := {|
  fobj := fun X => X;
  fmap := fun _ _ f => f
|}.

End Identity.

Arguments Id {C} /.

Notation "Id[ C ]" := (@Id C) (at level 9, format "Id[ C ]") : category_scope.

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

Notation "F ○ G" := (Compose F%functor G%functor)
  (at level 30, right associativity) : category_scope.

Program Instance fmap_iso `{C : Category} `{D : Category} `(F : C ⟶ D) :
  Proper (Isomorphism ==> Isomorphism) F.
Next Obligation.
  proper.
  refine {| to   := fmap[F] (to X)
          ; from := fmap (from X) |}.
    rewrite <- fmap_comp.
    rewrite iso_to_from; cat.
  rewrite <- fmap_comp.
  rewrite iso_from_to; cat.
Defined.

Instance fobj_respects `{C : Category} `{D : Category} `(F : C ⟶ D) :
  Proper (equiv ==> equiv) (@fobj C D F) := @fmap_iso _ _ _.
