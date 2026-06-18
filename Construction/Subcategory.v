Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Section Subcategory.

Context (C : Category).

(** A subcategory D of a category C. *)

(* nLab: https://ncatlab.org/nlab/show/subcategory
   Wikipedia: https://en.wikipedia.org/wiki/Subcategory

   A subcategory D of C is given by a subcollection [sobj] of the objects of C
   together with, for each pair of selected objects, a subcollection [shom] of
   the C-morphisms between them, closed under identity ([sid]) and composition
   ([scomp]). The source/target closure condition (if f : x ~> y is in D then
   so are x and y) holds here by construction: [shom] is only indexed by
   objects ox, oy already selected from [sobj].

   These conditions make D a category in its own right ([Sub] below) for which
   the inclusion D ⟶ C ([Incl]) is a functor; that inclusion is always
   faithful, since on each hom-set it is the first projection out of a sigma
   type. A subcategory is full when [shom] retains every C-morphism between
   selected objects ([Full]), and wide (lluf) when [sobj] selects every object
   of C ([Wide]). *)

Record Subcategory := {
  sobj : C → Type;                  (* sub-collection of the objects of C *)

  (* sub-collection of the C-morphisms between selected objects *)
  shom {x y : C} : sobj x → sobj y → (x ~> y) → Type;

  (* closed under composition: if f : y ~> z and g : x ~> y are in D, then so
     is the composite f ∘ g : x ~> z *)
  scomp {x y z : C} (ox : sobj x) (oy : sobj y) (oz : sobj z)
        {f : y ~> z} {g : x ~> y} :
    shom oy oz f → shom ox oy g → shom ox oz (f ∘ g);

  (* closed under identity: if x is in D then so is the identity 1ₓ *)
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

Lemma Full_Implies_Full_Functor : Full → Functor.Full Incl.
Proof.
  unfold Full; intros.
  construct.
  - exists g.
    destruct x, y.
    apply X; auto.
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
