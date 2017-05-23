Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Functor.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Bifunctors can be curried:

  C × D ⟶ E --> C ⟶ [D, E] ~~~ (C, D) -> E --> C -> D -> E

  Where ~~~ should be read as "Morally equivalent to".

  Note: We do not need to define Bifunctors as a separate class, since they
  can be derived from functors mapping to a category of functors. So in the
  following two definitions, [P] is effectively our bifunctor.

  The trick to [bimap] is that both the [Functor] instances we need (for
  [fmap] and [fmap1]), and the [Natural] instance, can be found in the
  category of functors we're mapping to by applying [P]. *)

Program Definition HomFunctor `(C : Category) : C^op ∏ C ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom C (fst p) (snd p)
                    ; is_setoid := @homset (C) (fst p) (snd p) |};
  fmap := fun X Y (f : X ~{C^op ∏ C}~> Y) =>
            {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.

Program Definition Curried_HomFunctor `(C : Category) : C^op ⟶ [C, Sets] := {|
  fobj := fun X => {|
    fobj := fun Y => {| carrier := @hom C X Y
                      ; is_setoid := @homset C X Y |};
    fmap := fun Y Z (f : Y ~{C}~> Z) =>
              {| morphism := fun (g : X ~{C}~> Y) =>
                               (f ∘ g) : X ~{C}~> Z |}
  |};
  fmap := fun X Y (f : X ~{C^op}~> Y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ op f |}
  |}
|}.
Next Obligation.
  simpl; intros.
  unfold op.
  apply comp_assoc.
Qed.

Coercion Curried_HomFunctor : Category >-> Functor.

Notation "'Hom' ( A , ─ )" := (@Curried_HomFunctor _ A) : category_scope.

Program Definition CoHomFunctor_Alt `(C : Category) : C ∏ C^op ⟶ Sets :=
  HomFunctor C ○ Swap.

Program Definition CoHomFunctor `(C : Category) : C ∏ C^op ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom (C^op) (fst p) (snd p)
                    ; is_setoid := @homset (C^op) (fst p) (snd p) |};
  fmap := fun X Y (f : X ~{C ∏ C^op}~> Y) =>
    {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.

Program Definition Curried_CoHomFunctor `(C : Category) : C ⟶ [C^op, Sets] := {|
  fobj := fun X => {|
    fobj := fun Y => {| carrier := @hom (C^op) X Y
                      ; is_setoid := @homset (C^op) X Y |};
    fmap := fun Y Z (f : Y ~{C^op}~> Z) =>
              {| morphism := fun (g : X ~{C^op}~> Y) =>
                               (f ∘ g) : X ~{C^op}~> Z |}
  |};
  fmap := fun X Y (f : X ~{C}~> Y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ op f |}
  |}
|}.
Next Obligation.
  simpl; intros.
  symmetry.
  apply comp_assoc.
Qed.

(*
Require Import Category.Instance.Cat.Closed.

Program Instance CoHomFunctor `(C : Category) : C ∏ C^op ⟶ Sets.
Next Obligation.
  pose (Curried_CoHomFunctor C).
  pose (@uncurry Cat _ _ C (C^op) Sets).
  destruct h; simpl in morphism.
  (* This does not work due to universe problems. *)
  apply (morphism f).
*)

(* Coercion Curried_CoHomFunctor : Category >-> Functor. *)

Notation "'Hom' ( ─ , A )" := (@Curried_CoHomFunctor _ A) : category_scope.
