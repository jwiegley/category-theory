Set Warnings "-notation-overridden".
Set Warnings "-notation-incompatible-format".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Reserved Notation "C ^op" (at level 7, left associativity).

Definition Opposite `(C : Category) : Category := {|
  obj     := @obj C;
  hom     := fun x y => @hom C y x;
  homset  := fun x y => @homset C y x;
  id      := @id C;
  compose := fun _ _ _ f g => g ∘ f;

  compose_respects := fun x y z f g fg h i hi =>
    @compose_respects C z y x h i hi f g fg;

  id_left  := fun x y f => @id_right C y x f;
  id_right := fun x y f => @id_left C y x f;

  comp_assoc := fun x y z w f g h => @comp_assoc_sym C w z y x h g f;
  comp_assoc_sym := fun x y z w f g h => @comp_assoc C w z y x h g f
|}.

Notation "C ^op" := (@Opposite C)
  (at level 7, format "C ^op", left associativity) : category_scope.

Lemma op_invol {C : Category} : (C^op)^op = C.
Proof.
  unfold Opposite; simpl.
  destruct C; simpl.
  f_equal.
Qed.

Definition op   {C : Category} {x y} (f : y ~{C}~> x) : x ~{C^op}~> y := f.
Definition unop {C : Category} {x y} (f : x ~{C^op}~> y) : y ~{C}~> x := f.

(* If two objects are isomorphic in C, then they are also isomorphic in C^op,
   just the conversion arrows are flipped. *)

Require Export Category.Theory.Isomorphism.

#[global]
Program Instance Isomorphism_Opposite {C : Category} {x y : C}
       (iso : @Isomorphism C x y) :
  @Isomorphism (C^op) x y := {
  to := from iso;
  from := to iso;
  iso_to_from := iso_to_from iso;
  iso_from_to := iso_from_to iso
}.
