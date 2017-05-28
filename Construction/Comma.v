Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Comma.

Context {A : Category}.
Context {B : Category}.
Context {C : Category}.

Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

(* Wikipedia: "... a comma category (a special case being a slice category) is
   a construction in category theory. It provides another way of looking at
   morphisms: instead of simply relating objects of a category to one another,
   morphisms become objects in their own right. This notion was introduced in
   1963 by F. W. Lawvere (Lawvere, 1963 p. 36), although the technique did not
   become generally known until many years later. Several mathematical
   concepts can be treated as comma categories. Comma categories also
   guarantee the existence of some limits and colimits. The name comes from
   the notation originally used by Lawvere, which involved the comma
   punctuation mark." *)

Program Definition Comma : Category := {|
  ob      := { p : A ∏ B & S (fst p) ~> T (snd p) };
  hom     := fun x y => (fst (`` x) ~> fst (`` y)) * (snd (`` x) ~> snd (`` y));
  homset  := fun _ _ =>
    {| equiv := fun f g => (fst f ≈ fst g) * (snd f ≈ snd g) |};
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g)
|}.

Program Instance comma_proj  : Comma ⟶ A ∏ B.
Program Instance comma_proj1 : Comma ⟶ A.
Program Instance comma_proj2 : Comma ⟶ B.

End Comma.

Notation "S ↓ T" := (@Comma _ _ _ S T) (at level 90) : category_scope.

Theorem comma_proj_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  x ≅ y -> ``x ≅[A ∏ B] ``y.
Proof.
  destruct 1; simpl.
  isomorphism; assumption.
Qed.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Definition Cocomma {A : Category} {B : Category} {C : Category}
  {S : A ⟶ C} {T : B ⟶ C} := @Comma (B^op) (A^op) (C^op) (T^op) (S^op).

Notation "S ↑ T" := (@Cocomma _ _ _ S T) (at level 90) : category_scope.
