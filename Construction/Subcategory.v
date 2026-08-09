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
   faithful ([Incl_Faithful]), since on each hom-set it is the first
   projection out of a sigma type. A subcategory is full when [shom] retains
   every C-morphism between selected objects ([Full]), and wide (lluf) when
   [sobj] selects every object of C ([Wide]).  In a full subcategory an
   ambient isomorphism lifts ([Full_sub_iso]) and, in particular, two
   membership proofs for one object give isomorphic objects of [Sub]
   ([Full_membership_iso]) — which is why a skeleton's uniqueness clause is
   stated at the level of [Sub]'s objects rather than their carriers
   (Theory/Skeleton.v). *)

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

(* The inclusion is faithful for every subcategory, full or not: on hom-sets
   it is the first projection out of a sigma type, and [Sub]'s hom-setoid
   compares exactly those first projections.  This is a plain [Definition]
   rather than an [Instance], following [Full_Implies_Full_Functor] below:
   registering it would put a [Faithful] goal into typeclass search for
   every consumer of this file, for no gain. *)

Program Definition Incl_Faithful : Faithful Incl := {| fmap_inj := _ |}.

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

(* In a full subcategory every ambient isomorphism between selected objects
   lifts, because both legs are retained by [Full] and the two laws are
   compared by [Sub]'s hom-setoid, i.e. on carriers. *)

Program Definition Full_sub_iso (full : Full) {x y : C}
        (ox : sobj S x) (oy : sobj S y) (f : x ≅ y) :
  ((x; ox) : Sub) ≅[Sub] (y; oy) := {|
  to   := (to f; full x y ox oy (to f));
  from := (from f; full y x oy ox (from f))
|}.
Next Obligation. apply iso_to_from. Qed.
Next Obligation. apply iso_from_to. Qed.

(* The special case at the identity: two membership proofs for one object
   give isomorphic — never equal — objects of [Sub].  Theory/Skeleton.v
   quotes this when explaining why a skeleton's uniqueness clause is stated
   at the level of [Sub]'s objects rather than their carriers.  Provided
   for reference; it is [Full_sub_iso] at [iso_id]. *)

Program Definition Full_membership_iso (full : Full) (x : C)
        (p q : sobj S x) : ((x; p) : Sub) ≅[Sub] (x; q) := {|
  to   := (id[x]; full x x p q id);
  from := (id[x]; full x x q p id)
|}.

(* A replete subcategory if for any x in D and any isomorphism f : x ≅ y in C,
   both y and f are also in D. *)

Definition Replete : Type :=
  ∀ (x : C) (ox : sobj S x) (y : C) (f : x ≅ y),
    { oy : sobj S y & shom S ox oy (to f) ∧ shom S oy ox (from f) }.

(* A wide subcategory if every object of C is also an object of D. *)

Definition Wide : Type := ∀ x : C, sobj S x.

End Subcategory.
