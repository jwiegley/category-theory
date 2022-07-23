Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* A product of two categories forms a category. All of the methods are
   spelled out here to ease simplification. *)

Definition Product (C D : Category) : Category := {|
  obj     := C * D;
  hom     := fun x y => (fst x ~> fst y) * (snd x ~> snd y);
  homset  := fun x y =>
    let setoid_C := @homset C (fst x) (fst y) in
    let setoid_D := @homset D (snd x) (snd y) in
    {| equiv := fun f g =>
         (@equiv _ setoid_C (fst f) (fst g) *
          @equiv _ setoid_D (snd f) (snd g))
     ; setoid_equiv := _
         {| Equivalence_Reflexive  := fun x =>
              (@Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_C) (fst x),
               @Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_D) (snd x))
          ; Equivalence_Symmetric  := fun x y f =>
              (@Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst f),
               @Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd f))
          ; Equivalence_Transitive := fun x y z f g =>
              (@Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst z)
                 (fst f) (fst g),
               @Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd z)
                 (snd f) (snd g)) |} |};
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g);

  compose_respects := fun x y z f g fg h i hi =>
    (compose_respects (fst x) (fst y) (fst z)
                      (fst f) (fst g) (fst fg) (fst h) (fst i) (fst hi),
     compose_respects (snd x) (snd y) (snd z)
                      (snd f) (snd g) (snd fg) (snd h) (snd i) (snd hi));

  id_left  := fun x y f =>
    (@id_left C (fst x) (fst y) (fst f),
     @id_left D (snd x) (snd y) (snd f));
  id_right := fun x y f =>
    (@id_right C (fst x) (fst y) (fst f),
     @id_right D (snd x) (snd y) (snd f));

  comp_assoc := fun x y z w f g h =>
    (@comp_assoc C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h));
  comp_assoc_sym := fun x y z w f g h =>
    (@comp_assoc_sym C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc_sym D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h))
|}.

Notation "C ∏ D" := (@Product C D) (at level 90) : category_scope.

Require Import Category.Theory.Functor.

#[global]
Program Instance Fst {C : Category} {D : Category} : C ∏ D ⟶ C := {
  fobj := fst;
  fmap := fun _ _ => fst
}.

#[global]
Program Instance Snd {C : Category} {D : Category} : C ∏ D ⟶ D := {
  fobj := snd;
  fmap := fun _ _ => snd
}.

Program Definition Swap
        {C : Category} {D : Category} : (C ∏ D) ⟶ (D ∏ C) := {|
  fobj := fun x => (snd x, fst x);
  fmap := fun _ _ f => (snd f, fst f);
|}.

Corollary fst_comp {C : Category} {D : Category} x y z
          (f : y ~{C ∏ D}~> z) (g : x ~{C ∏ D}~> y) :
  fst f ∘ fst g ≈ fst (f ∘ g).
Proof. reflexivity. Qed.

Corollary snd_comp {C : Category} {D : Category} x y z
          (f : y ~{C ∏ D}~> z) (g : x ~{C ∏ D}~> y) :
  snd f ∘ snd g ≈ snd (f ∘ g).
Proof. reflexivity. Qed.

Require Import Category.Construction.Opposite.

Corollary Product_Opposite {C D : Category} : (C ∏ D) ^op = (C^op ∏ D^op).
Proof. reflexivity. Qed.
