Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Hom.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Profunctor.

Generalizable All Variables.

(** Representable profunctors versus adjunctions. *)

(* nLab: https://ncatlab.org/nlab/show/profunctor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   An adjunction is exactly a natural isomorphism of representable profunctors.
   For F : D ⟶ C and U : C ⟶ D (the library orients F ⊣ U with F the left
   adjoint D ⟶ C and U the right adjoint C ⟶ D), the two representable
   profunctors of Theory/Profunctor.v are

     Repr_left F  : D ⇸ C,   (d, c) ↦ C(F d, c),
     Repr_right U : D ⇸ C,   (d, c) ↦ D(d, U c),

   both objects of the profunctor category [D^op ∏ C, Sets]. An adjunction
   F ⊣ U is precisely a natural isomorphism Repr_left F ≅ Repr_right U in that
   category: this is the hom-set (transpose) form of an adjunction.

   The witnessing isomorphism is literally the hom-bifunctor isomorphism hom_adj
   of Adjunction/Hom.v, whose two sides Hom C ◯ (F^op ∏⟶ Id) and
   Hom D ◯ (Id^op ∏⟶ U) are definitionally Repr_left F and Repr_right U. So
   this file is a repackaging, through the profunctor vocabulary, of the two
   conversions already established there — Adjunction_Universal_to_Hom (from the
   universal-property adjunction Theory/Adjunction.v to the hom-iso form) and
   Adjunction_Hom_to_Universal (back) — bundled into the Type-valued iff
   representable_adjunction. Both directions are genuine, so the iff holds at
   full strength; nothing here is a one-way implication. *)

Section RepresentableAdjunction.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(* Forward direction: an adjunction F ⊣ U transposes to a natural isomorphism of
   the representable profunctors. Concretely we route the universal-property
   adjunction through Adjunction_Universal_to_Hom to obtain the hom-bifunctor
   isomorphism hom_adj, whose endpoints are Repr_left F and Repr_right U. *)
Definition adjunction_to_repr_iso (A : F ⊣ U) :
  Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U :=
  @hom_adj C D F U (@Adjunction_Universal_to_Hom C D F U A).

(* Reverse direction: a natural isomorphism Repr_left F ≅ Repr_right U is exactly
   the datum of an Adjunction_Hom (its hom_adj field), which converts back to a
   universal-property adjunction through Adjunction_Hom_to_Universal. *)
Definition repr_iso_to_adjunction
  (iso : Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U) : F ⊣ U :=
  @Adjunction_Hom_to_Universal C D F U {| hom_adj := iso |}.

(* The representability criterion for adjunctions as a Type-valued iff (↔ is
   iffT here), bundling the two conversions above. *)
Definition representable_adjunction :
  (F ⊣ U) ↔ (Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U) :=
  (adjunction_to_repr_iso, repr_iso_to_adjunction).

End RepresentableAdjunction.
