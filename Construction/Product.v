Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Product.

Context `{C : Category}.
Context `{D : Category}.

(* A Groupoid is a category where all morphisms are isomorphisms, and morphism
   equivalence is equivalence of isomorphisms. *)

Program Definition Product : Category := {|
  ob      := C * D;
  hom     := fun X Y => (fst X ~> fst Y) * (snd X ~> snd Y);
  homset  := fun _ _ => {| equiv := fun f g =>
                             (fst f ≈ fst g) * (snd f ≈ snd g) |} ;
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g)
|}.

End Product.

Notation "C ∏ D" := (@Product C D) (at level 90) : category_scope.

Require Import Category.Theory.Functor.

Program Instance Fst `{C : Category} `{D : Category} : C ∏ D ⟶ C := {
  fobj := fst;
  fmap := fun _ _ => fst
}.

Program Instance Snd `{C : Category} `{D : Category} : C ∏ D ⟶ D := {
  fobj := snd;
  fmap := fun _ _ => snd
}.

Program Definition Swap
        `{C : Category} `{D : Category} : (C ∏ D) ⟶ (D ∏ C) := {|
  fobj := fun x => (snd x, fst x);
  fmap := fun _ _ f => (snd f, fst f);
|}.

Corollary fst_comp `{C : Category} `{D : Category} X Y Z
          (f : Y ~{C ∏ D}~> Z) (g : X ~{C ∏ D}~> Y) :
  fst f ∘ fst g ≈ fst (f ∘ g).
Proof. reflexivity. Qed.

Corollary snd_comp `{C : Category} `{D : Category} X Y Z
          (f : Y ~{C ∏ D}~> Z) (g : X ~{C ∏ D}~> Y) :
  snd f ∘ snd g ≈ snd (f ∘ g).
Proof. reflexivity. Qed.
