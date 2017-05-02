Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Hom.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Wikipedia: "Let C be a locally small category and let Set be the category
   of sets. For each object A of C let Hom(A,–) be the hom functor that maps
   object X to the set Hom(A,X).

   A functor F : C → Set is said to be representable if it is naturally
   isomorphic to Hom(A,–) for some object A of C. A representation of F is a
   pair (A, Φ) where

       Φ : Hom(A,–) → F

   is a natural isomorphism.

   A contravariant functor G from C to Set is the same thing as a functor G :
   Cop → Set and is commonly called a presheaf. A presheaf is representable
   when it is naturally isomorphic to the contravariant hom-functor Hom(–,A)
   for some object A of C." *)

Class Representable `{C : Category} (F : C ⟶ Sets) := {
  represents {A : C} : Hom(A,─) ≅ F
}.
