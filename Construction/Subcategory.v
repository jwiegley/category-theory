Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Subcategory.

Context (C : Category).

Record Subcategory := {
  (* Given a category C, a subcategory D consists of a subcollection of the
     collection of objects of C *)
  sobj : C -> Type;
  (* and a subcollection of the collection of morphisms of D such that: *)
  (* If the morphism f : x → y is in D, then so are x and y. *)
  shom {x y : C} : sobj x -> sobj y -> (x ~> y) -> Type;

  (* If f : x → y and g : y → z are in D, then so is the composite
     g ∘ f : x → z. *)
  scomp {x y z : C} (ox : sobj x) (oy : sobj y) (oz : sobj z)
        {f : y ~> z} {g : x ~> y} :
    shom oy oz f -> shom ox oy g -> shom ox oz (f ∘ g);

  (* If x is in D then so is the identity morphism 1ₓ. *)
  sid {x : C} (ox : sobj x) : shom ox ox (@id C x)
}.

Variable S : Subcategory.

(* These conditions ensure that D is a category in its own right... *)
Program Definition Sub : Category := {|
  obj     := { x : C & sobj S x };
  hom     := fun x y => { f : `1 x ~> `1 y & shom S `2 x `2 y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun x => (id; sid S `2 x);
  compose := fun x y z f g  => (`1 f ∘ `1 g; scomp S `2 x `2 y `2 z `2 f `2 g)
|}.

(* ... and the inclusion D ⟶ C is a functor. *)
Program Instance Incl : Sub ⟶ C := {
  fobj := fun x => `1 x;
  fmap := fun x y f => `1 f
}.

(* Additionally, we say that D is...

   A full subcategory if for any x and y in D, every morphism f : x → y in C
   is also in D... *)

Definition Full : Type :=
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f : x ~> y), shom S ox oy f.

(* ... (that is, the inclusion functor D ⟶ C is full) *)

Lemma Full_Implies_Full_Functor : Full -> Functor.Full Incl.
Proof.
  unfold Full; intros.
  construct.
  - exists g.
    destruct x, y.
    apply X; auto.
  - proper.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* A replete subcategory if for any x in D and any isomorphism f : x ≅ y in C,
   both y and f are also in D. *)

Definition Replete : Type :=
  ∀ (x : C) (ox : sobj S x) (y : C) (f : x ≅ y),
    { oy : sobj S y & shom S ox oy (to f) ∧ shom S oy ox (from f) }.

(* A wide subcategory if every object of C is also an object of D. *)

Definition Wide : Type := ∀ x : C, sobj S x.

End Subcategory.
