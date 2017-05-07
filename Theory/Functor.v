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

(* Functors used as functions will map objects of categories, similar to the
   way type constructors behave in Haskell. *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C D)
  (at level 90, right associativity) : category_scope.

Arguments fmap {C D Functor X Y} f.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : category_scope.
Infix "<$[ F ]>" := (@fmap _ _ F _ _)
  (at level 29, left associativity, only parsing) : category_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : category_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : category_scope.

Notation "fobj[ F ]" := (@fobj _ _ F)
  (at level 9, format "fobj[ F ]") : category_scope.
Notation "fmap[ F ]" := (@fmap _ _ F _ _)
  (at level 9, format "fmap[ F ]") : category_scope.

Hint Rewrite @fmap_id : categories.

Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).

Program Instance fmap_iso `{C : Category} `{D : Category}
        `(F : C ⟶ D) :
  Proper (Isomorphism ==> Isomorphism) F.
Next Obligation.
  proper.
  refine {| to   := fmap[F] (to X)
          ; from := fmap (from X) |}.
    rewrite <- fmap_comp.
    rewrite iso_to_from; cat.
  rewrite <- fmap_comp.
  rewrite iso_from_to; cat.
Qed.
