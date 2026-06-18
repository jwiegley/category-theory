Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Representable functors. *)

(* nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

   A functor F : C ⟶ Sets is representable when it is naturally isomorphic to
   a covariant hom-functor Hom(A, ─) for some object A of C, the representing
   object. In library notation this natural isomorphism is

       [Hom A,─] ≅ F     (an iso in the functor category [C, Sets]),

   so [represented] below is precisely Wikipedia's pair (A, Φ): [repr_obj] is
   A and [represented] is the natural iso Φ : Hom(A, ─) ⟹ F. By the Yoneda
   lemma such a Φ is determined by a single universal element of F(A), namely
   Φ_A(id A), and the representing object is unique up to (unique) isomorphism;
   these facts are developed in Structure/UniversalProperty.v. A contravariant
   representable G : C^op ⟶ Sets (a presheaf) is instead naturally isomorphic
   to Hom(─, A); see [Hom ─,A] (Curried_CoHom) in Functor/Hom.v. *)

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

Class Representable `(F : C ⟶ Sets) := {
  repr_obj : C;                          (* the representing object A *)
  represented : [Hom repr_obj,─] ≅ F     (* natural iso Φ : Hom(A, ─) ⟹ F *)
}.

Coercion Representable_to_obj `(F : C ⟶ Sets) (R : Representable F) : C :=
  @repr_obj _ _ R.
