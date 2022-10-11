Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(* A Groupoid is a category where all morphisms are isomorphisms, and morphism
   equivalence is equivalence of isomorphisms. *)

Program Definition GroupoidOf (C : Category) : Category := {|
  obj     := @obj C;
  hom     := @Isomorphism C;
  homset  := @iso_setoid C;
  id      := @iso_id C;
  compose := @iso_compose C
|}.

Class isGroupoid (C : Category) := { all_are_iso : forall (c c': C)
                                                          (f : c ~> c'), isIsomorphism f }.

Class Groupoid := { catOfGroupoid :> Category ; catIsGroupoid : isGroupoid catOfGroupoid }.

#[export] Existing Instance catIsGroupoid.
Coercion catOfGroupoid : Groupoid >-> Category.
(* A groupoid can be thought of as a proof-relevant setoid satisfying some additional
   properties with regards to the way proofs compose.

   If (A,~) is a setoid, and B : A -> Type, where B is not "proof-irrelevant" but may
   contain additional information, then one wants to prove that x ≈ y -> (B x -> B y) but
   beyond this it may be useful to supply additional information about the way that the
   map B x -> B y depends on the proof of x ≈ y.

   In particular it may be useful to prove that (A, ~) is not just a setoid but a groupoid, 
   and that B depends functorially on A. (Not all setoids are groupoids.)

   We begin by showing that the standard equality determines a groupoid structure on the
   elements of the hom type.
 *)

Proposition path_comp_assoc {A : Type} {w x y z : A} (f : w = x) (g : x = y) (h : y = z) :
  eq_trans (eq_trans f g) h =   eq_trans f (eq_trans g h).
Proof.
  destruct f, g, h. reflexivity.
Qed.

Proposition path_comp_right {A : Type} {x y: A} (f : x = y) : eq_trans (eq_refl x) f = f.
Proof.
  destruct f; reflexivity.
Qed.

Proposition path_comp_left {A : Type} {x y: A} (f : x = y) : eq_trans f (eq_refl y) = f.
Proof.
  destruct f; reflexivity.
Qed.


#[export] Program Instance path_category (A: Type) : Category := {|
    obj := A;
    hom := fun x y => x = y;
    homset := fun _ _ => {| equiv := eq |};
    id := fun _ => eq_refl;
    compose := fun x y z f g => eq_trans g f;
    compose_respects := _;
    id_left := fun _ _ _ => path_comp_left _;
    id_right := fun _ _ _ => path_comp_right _;
    comp_assoc := fun _ _ _ _ _ _ _ => path_comp_assoc _ _ _  
  |}.
Print path_category.

#[export] Instance path_category_isGroupoid (A : Type) : isGroupoid (path_category A).
Proof.
  apply Build_isGroupoid.
  intros x y. simpl. intro f. unshelve eapply Build_isIsomorphism.
  { apply eq_sym; exact f. }
  { destruct f; reflexivity. }
  { destruct f; reflexivity. }
Defined.

#[export] Instance path_groupoid (A : Type) : Groupoid := {|
      catOfGroupoid := (path_category A);
      catIsGroupoid := _;
    |} .
