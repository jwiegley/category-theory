Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

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
  hom     := fun x y =>
    { f : (fst (`` x) ~> fst (`` y)) * (snd (`` x) ~> snd (`` y))
    & projT2 y ∘ fmap (fst f) ≈ fmap (snd f) ∘ projT2 x };
  homset  := fun _ _ =>
    {| equiv := fun f g => (fst ``f ≈ fst ``g) * (snd ``f ≈ snd ``g) |};
  id      := fun _ => ((id, id); _);
  compose := fun _ _ _ f g => ((fst ``f ∘ fst ``g, snd ``f ∘ snd ``g); _)
|}.
Next Obligation.
  simpl in *.
  rewrite !fmap_comp.
  rewrite comp_assoc.
  rewrites.
  rewrite <- !comp_assoc.
  rewrites.
  reflexivity.
Qed.

Program Instance comma_proj  : Comma ⟶ A ∏ B := {|
  fobj := fun x => ``x;
  fmap := fun _ _ f => (fst ``f, snd ``f)
|}.
Program Instance comma_proj1 : Comma ⟶ A := {|
  fobj := fun x => fst ``x;
  fmap := fun _ _ f => fst ``f
|}.
Program Instance comma_proj2 : Comma ⟶ B := {|
  fobj := fun x => snd ``x;
  fmap := fun _ _ f => snd ``f
|}.

End Comma.

Notation "S ↓ T" := (@Comma _ _ _ S T) (at level 90) : category_scope.

Theorem comma_proj_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  x ≅ y -> ``x ≅[A ∏ B] ``y.
Proof.
  destruct 1; simpl.
  isomorphism.
  - exact (`1 to).
  - exact (`1 from).
  - apply iso_to_from.
  - apply iso_from_to.
Qed.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Definition Cocomma {A : Category} {B : Category} {C : Category}
  {S : A ⟶ C} {T : B ⟶ C} := @Comma (B^op) (A^op) (C^op) (T^op) (S^op).

Notation "S ↑ T" := (@Cocomma _ _ _ S T) (at level 90) : category_scope.
