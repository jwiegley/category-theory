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
  ob      := C * D;
  hom     := fun X Y => (fst X ~> fst Y) * (snd X ~> snd Y);
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

  compose_respects := fun X Y Z f g fg h i hi =>
    (compose_respects (fst X) (fst Y) (fst Z)
                      (fst f) (fst g) (fst fg) (fst h) (fst i) (fst hi),
     compose_respects (snd X) (snd Y) (snd Z)
                      (snd f) (snd g) (snd fg) (snd h) (snd i) (snd hi));

  id_left  := fun X Y f =>
    (@id_left C (fst X) (fst Y) (fst f),
     @id_left D (snd X) (snd Y) (snd f));
  id_right := fun X Y f =>
    (@id_right C (fst X) (fst Y) (fst f),
     @id_right D (snd X) (snd Y) (snd f));

  comp_assoc := fun X Y Z W f g h =>
    (@comp_assoc C (fst X) (fst Y) (fst Z) (fst W) (fst f) (fst g) (fst h),
     @comp_assoc D (snd X) (snd Y) (snd Z) (snd W) (snd f) (snd g) (snd h));
  comp_assoc_sym := fun X Y Z W f g h =>
    (@comp_assoc_sym C (fst X) (fst Y) (fst Z) (fst W) (fst f) (fst g) (fst h),
     @comp_assoc_sym D (snd X) (snd Y) (snd Z) (snd W) (snd f) (snd g) (snd h))
|}.

Notation "C ∏ D" := (@Product C D) (at level 90) : category_scope.

Require Import Category.Theory.Functor.

Program Instance Fst {C : Category} {D : Category} : C ∏ D ⟶ C := {
  fobj := fst;
  fmap := fun _ _ => fst
}.

Program Instance Snd {C : Category} {D : Category} : C ∏ D ⟶ D := {
  fobj := snd;
  fmap := fun _ _ => snd
}.

Program Definition Swap
        {C : Category} {D : Category} : (C ∏ D) ⟶ (D ∏ C) := {|
  fobj := fun x => (snd x, fst x);
  fmap := fun _ _ f => (snd f, fst f);
|}.

Corollary fst_comp {C : Category} {D : Category} X Y Z
          (f : Y ~{C ∏ D}~> Z) (g : X ~{C ∏ D}~> Y) :
  fst f ∘ fst g ≈ fst (f ∘ g).
Proof. reflexivity. Qed.

Corollary snd_comp {C : Category} {D : Category} X Y Z
          (f : Y ~{C ∏ D}~> Z) (g : X ~{C ∏ D}~> Y) :
  snd f ∘ snd g ≈ snd (f ∘ g).
Proof. reflexivity. Qed.

Require Import Category.Construction.Opposite.

Corollary Product_Opposite {C D : Category} : (C ∏ D) ^op = (C^op ∏ D^op).
Proof. reflexivity. Qed.
