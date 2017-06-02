Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The canonical map just exposed the functor object mapping to the Coq type
   system, so that it can find the related functor through instance lookup.
   However, since only one such functor can match a given pattern, this is why
   it is termed canonical. *)

Class CanonicalMap {C : Category} (F : C -> C) : Type := {
  map {x y} (f : x ~> y) : F x ~> F y;

  is_functor : C ⟶ C;
  fobj_related {x} : F x ≅ is_functor x;
  fmap_related {x y} (f : x ~> y) :
    map f ≈ from fobj_related ∘ fmap[is_functor] f ∘ to fobj_related
}.

Coercion is_functor : CanonicalMap >-> Functor.

Program Instance Identity_CanonicalMap {C : Category} :
  CanonicalMap (fun x => x) | 9 := {
  map := fun _ _ f => f;
  is_functor := Id
}.

Program Instance Functor_CanonicalMap {C : Category} {F : C ⟶ C} :
  CanonicalMap F := {
  map := fun _ _ f => fmap[F] f;
  is_functor := F
}.

Program Instance Functor_Eta_CanonicalMap {C : Category} {F : C ⟶ C} :
  CanonicalMap (fun x => F x) := {
  map := fun _ _ f => fmap[F] f;
  is_functor := F
}.

Program Instance Functor_Map_CanonicalMap {C : Category}
        `{G : @CanonicalMap C P} {F : C ⟶ C} :
  CanonicalMap (fun x => F (P x)) := {
  map := fun _ _ f => fmap[F] (map f);
  is_functor := F ○ G
}.
Next Obligation.
  destruct G; simpl.
  apply fobj_respects.
  apply fobj_related0.
Defined.
Next Obligation.
  destruct G; simpl.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  apply fmap_related0.
Defined.
