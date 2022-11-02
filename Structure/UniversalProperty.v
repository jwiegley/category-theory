Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.

(* A predicate on objects of a category can be called a "universal property" *)
(* if satisfying the predicate is equivalent to representing a certain functor. *)
(* This definition of a universal property contains all examples that I am aware of
   but I do not claim it is completely exhaustive. *)
Check @Isomorphism Sets.
Class IsUniversalProperty (C : Category) (P : C → Type) (eqP : forall c, Setoid (P c)) :=
  {
    repr_functor : C ⟶ Sets ;
    repr_equivalence : forall c : C,
      @Isomorphism Sets 
        (Build_SetoidObject (P c) (eqP c))
        (Build_SetoidObject (Isomorphism [Hom c,─] repr_functor) _)
  }.

Proposition IsCartesianProductIsUniversalProperty (C : Category) (x y : C) :
  IsUniversalProperty C (fun z => IsCartesianProduct x y z)
    (fun z => CartesianProductStructureEquiv x y z).
Proof.
  unshelve eapply Build_IsUniversalProperty.
  
