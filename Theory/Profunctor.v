Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Profunctors and representable profunctors. *)

(* nLab: https://ncatlab.org/nlab/show/profunctor
   Wikipedia: https://en.wikipedia.org/wiki/Profunctor

   A profunctor from C to D (also called a distributor or a bimodule, written
   C ⇸ D) is a functor

     C^op ∏ D ⟶ Sets,

   contravariant in its first argument and covariant in its second. It sends a
   pair (c, d) to a setoid P(c, d) of "heteromorphisms" from c to d, carrying a
   left action of C and a right action of D by composition. Since hom-sets here
   are setoids, profunctors land in Sets, the category of setoids.

   Following the binding universe discipline of this development, a profunctor
   is kept as a per-pair object: the profunctors C ⇸ D are the objects of the
   functor category [C^op ∏ D, Sets] (Instance/Fun.v), whose morphisms are
   natural transformations and whose object equivalence Prof_Setoid is a natural
   isomorphism (Functor_Setoid, Theory/Functor.v). We never assemble a single
   category of all profunctors between all categories — that would raise the
   universe level — so the bicategory-lite composition and coherence live as
   lemmas in these per-pair functor categories (the Construction/Profunctor
   modules). *)

Definition Profunctor (C D : Category) := (C^op ∏ D) ⟶ Sets.

Notation "C ⇸ D" := (Profunctor C D)
  (at level 90, right associativity) : category_scope.

(* The identity profunctor on C is the hom-bifunctor Hom C : C^op ∏ C ⟶ Sets of
   Functor/Hom.v, viewed at the profunctor type C ⇸ C. On (c, c') it is the
   hom-set C(c, c'), with C acting on both sides by composition; it is the unit
   for profunctor composition (Construction/Profunctor/Compose.v reuses Hom C as
   its prof_id). *)
Definition Id_Profunctor (C : Category) : C ⇸ C := Hom C.

(* Representable profunctors. A functor F : C ⟶ D presents the profunctor

     Repr_left F : C ⇸ D,     (c, d) ↦ D(F c, d),

   covariantly representable on the left, while a functor U : D ⟶ C presents

     Repr_right U : C ⇸ D,    (c, d) ↦ C(c, U d),

   representable on the right. Both are built from the hom-bifunctor of the
   target (resp. source) precomposed with F (resp. U) in one slot and the
   identity in the other, exactly the two composites appearing in the hom-set
   adjunction hom_adj of Adjunction/Hom.v:

     Repr_left F  = Hom D ◯ (F^op ∏⟶ Id),
     Repr_right U = Hom C ◯ (Id^op ∏⟶ U).

   When F ⊣ U (the library orients F : D ⟶ C and U : C ⟶ D), these specialise
   to the two sides Hom C ◯ (F^op ∏⟶ Id) and Hom D ◯ (Id^op ∏⟶ U) of hom_adj,
   so the adjunction is precisely a natural isomorphism Repr_left F ≅ Repr_right
   U in the profunctor category (developed in Theory/Profunctor/Adjunction.v). *)

Definition Repr_left {C D : Category} (F : C ⟶ D) : C ⇸ D :=
  Hom D ◯ (F^op ∏⟶ (@Id D)).

Definition Repr_right {C D : Category} (U : D ⟶ C) : C ⇸ D :=
  Hom C ◯ ((@Id C)^op ∏⟶ U).

(* The equivalence of profunctors C ⇸ D is inherited from the functor category
   [C^op ∏ D, Sets]: two profunctors are equivalent exactly when they are
   naturally isomorphic (Functor_Setoid). This is a plain setoid handle, not a
   registered category instance, keeping the development fully polymorphic. *)
Definition Prof_Setoid (C D : Category) : Setoid (C ⇸ D) :=
  @Functor_Setoid (C^op ∏ D) Sets.
