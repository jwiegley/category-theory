Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Instance.Coq.
Require Export Coq.Sets.Ensembles.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The category whose objects are Ensembles on some type, and whose morphisms
   are injective mappings. *)

Program Definition Ens : Category := {|
  obj     := ∃ T : Type, Ensemble T;
  hom     := fun A B =>
    ∃ f : ``A -> ``B, ∀ x : ``A, In _ (projT2 A) x ↔ In _ (projT2 B) (f x);
  homset  := fun P Q => {| equiv := fun f g => forall x, ``f x = ``g x |};
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g =>  (``f \o ``g; _)
|}.
Next Obligation. equivalence; rewrite H, H0; reflexivity. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. proper; rewrite H, H0; reflexivity. Qed.

(* The category whose objects are Ensembles on a given type, and whose
   morphisms are injective mappings. *)

Program Definition EnsT (T : Type) : Category := {|
  obj     := Ensemble T;
  hom     := fun A B =>
    ∃ f : T -> T, ∀ x : T, In _ A x ↔ In _ B (f x);
  homset  := fun P Q => {| equiv := fun f g => forall x, ``f x = ``g x |};
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g =>  (``f \o ``g; _)
|}.
Next Obligation. equivalence; rewrite H, H0; reflexivity. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. proper; rewrite H, H0; reflexivity. Qed.
