Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Comma.

Context {A B C : Category}.

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
  obj     := ∃ p : A ∏ B, S (fst p) ~{C}~> T (snd p);
  hom     := fun x y =>
    ∃ f : (fst (`1 x) ~{A}~> fst (`1 y)) * (snd (`1 x) ~{B}~> snd (`1 y)),
      `2 y ∘ fmap[S] (fst f) ≈ fmap[T] (snd f) ∘ `2 x;
  homset  := fun _ _ =>
    {| equiv := fun f g => (fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g) |};
  id      := fun _ => ((id, id); _);
  compose := fun _ _ _ f g => ((fst `1 f ∘ fst `1 g, snd `1 f ∘ snd `1 g); _)
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

Program Instance comma_proj_nat : S ○ comma_proj1 ⟹ T ○ comma_proj2.

End Comma.

Notation "S ↓ T" := (@Comma _ _ _ S T) (at level 90) : category_scope.

Theorem comma_proj_mor_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  x ≅ y -> `1 x ≅[A ∏ B] `1 y.
Proof.
  destruct 1; simpl.
  isomorphism.
  - exact (`1 to).
  - exact (`1 from).
  - apply iso_to_from.
  - apply iso_from_to.
Defined.

Theorem comma_proj_com_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  forall iso : x ≅ y,
    `2 x ≈ fmap[T] (snd `1 (from iso)) ∘ `2 y ∘ fmap[S] (fst `1 (to iso)).
Proof.
  intros.
  pose proof (iso_from_to iso); simpl in X.
  destruct (from iso), x0; simpl in *.
  rewrite <- e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (fst X).
  cat.
Qed.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Definition Cocomma {A : Category} {B : Category} {C : Category}
  {S : A ⟶ C} {T : B ⟶ C} := @Comma (B^op) (A^op) (C^op) (T^op) (S^op).

Notation "S ↑ T" := (@Cocomma _ _ _ S T) (at level 90) : category_scope.
