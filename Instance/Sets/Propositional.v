Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.

Generalizable All Variables.

(** * Propositional equality for the objects and homs of [Sets] *)

(* nLab:    https://ncatlab.org/nlab/show/Bishop+set
   nLab:    https://ncatlab.org/nlab/show/h-set
   Book:    The Univalent Foundations Program, "Homotopy Type Theory", IAS
            2013, Definition 3.1.1 and Definition 3.3.1
   Book:    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
            §V.6 and §V.7, printed p. 128

   Lib/Setoid/Propositional.v introduces [PropEquiv S]: the property that a
   setoid's `≈` is logically equivalent to a [Prop]-valued relation, and
   explains why that has to be a property of particular setoids rather than a
   change to [Class Setoid].  This file carries the property along the
   constructions of [Sets] that the concrete algebraic categories are built
   from, since those categories are categories of setoids with structure and
   their limits are created out of [Sets].

   WHAT TRANSPORTS.  Hom-setoids, whose `≈` is pointwise into the target
   ([SetoidMorphism_equiv], Instance/Sets.v:144); binary products, whose `≈` is
   componentwise ([Sets_Cartesian], Instance/Sets/Cartesian.v:33); indexed
   products, whose `≈` is pointwise in the index ([Sets_iprod_equiv],
   Instance/Sets/Products.v:256); and limits, whose `≈` is the underlying
   indexed product's, the compatibility witness playing no part
   ([Sets_limit_equiv], Instance/Sets/Complete.v:141).  In each case the
   [Prop] relation is the obvious pointwise or componentwise one, and the
   [Example]s below read that back at [eq_refl] rather than asserting it.

   The limit transport is the one with consequences: [Ab] and [RMod R] get
   their limits by CREATION along the forgetful functors down to [Sets]
   (Instance/Ab/Limit.v, Instance/Mod/Limit.v), so [limit_PropEquiv] is what
   makes a limit of propositional algebras propositional again.

   WHAT DOES NOT TRANSPORT, AND HOW THAT WAS MEASURED.  There is no instance
   here of the shape [∀ X : SetoidObject, PropEquiv (is_setoid X)], and none of
   [LocallyPropositional Sets] or [LocallyPropositional Cat].  The obvious
   route -- take [pequiv f g := inhabited (f ≈ g)] -- supplies [pequiv_from] and
   then stops: [pequiv_to] would have to eliminate a [Prop] into the
   [Type]-valued goal [f ≈ g].  For [Cat] that is not merely inconvenient, and
   Test/ProbePropEquiv.v measures it: an [F ≈ G] in [Cat] IS a family of
   isomorphisms (Theory/Functor.v:149, installed at Instance/Cat.v:145), and
   projecting the isomorphism at [x] out of an [inhabited (F ≈ G)] is refused.
   For [Sets] the situation is weaker and is stated as such: an arbitrary
   [SetoidObject] carries an arbitrary [Type]-valued `≈`, so no route to a
   [Prop] mirror is available in general; that is an absence of a construction,
   not a proof that none exists.  Which is exactly why the algebraic object
   records of the later phases CARRY a [PropEquiv] field rather than deriving
   one. *)

(** ** The property, at the level of a [Sets] object *)

(* [PropEquivObj X] is [PropEquiv] of the setoid [X] carries.  It is the field
   the concrete algebraic object records take, spelled once here so that those
   records need not repeat [is_setoid].

   Measured (About under Set Printing Universes):

     PropEquivObj@{u u0 u1} : SetoidObject@{u0 u1} → Type@{u}
     (* u u0 u1 |= Set < u, u0 <= u, u1 <= u *)

   -- the carrier and proof universes of the object bound it from below and
   nothing bounds it from above, so it sits at the object's own level. *)
Definition PropEquivObj (X : SetoidObject) : Type := PropEquiv (is_setoid X).

(** ** Hom-setoids *)

(* Two setoid maps are `≈` when they agree pointwise up to the target's `≈`
   (Instance/Sets.v:144), so a [Prop] mirror on the TARGET gives one on the
   hom-setoid, pointwise.  The source needs nothing.

   Measured:

     hom_PropEquiv@{u} :
       ∀ {x y : SetoidObject@{u u}},
       PropEquiv@{u u} y → PropEquiv@{u u} SetoidMorphism_Setoid@{u u u}
     (* u |=  *)

   -- ONE universe, with no constraint at all: the transport neither raises
   the level nor pins it. *)
#[export] Instance hom_PropEquiv {x y : SetoidObject} (Py : PropEquiv (is_setoid y)) :
  PropEquiv (@SetoidMorphism_Setoid x y).
Proof.
  unshelve refine
    {| pequiv := fun f g : SetoidMorphism x y =>
                   forall a : carrier x, @pequiv _ _ Py (f a) (g a) |}.
  - intros f g H a; exact (pequiv_to _ _ (H a)).
  - intros f g H a; exact (pequiv_from _ _ (H a)).
Defined.

(* The hom-setoid of [Sets] IS [SetoidMorphism_Setoid] on the nose
   (Instance/Sets.v:201), so the instance above is an instance for [Sets]'s
   [homset] without further work. *)
Example hom_PropEquiv_is_Sets_homset (x y : SetoidObject) :
  @SetoidMorphism_Setoid x y = @homset Sets x y := eq_refl.

(* The relation it supplies is the pointwise one, read back at [eq_refl]. *)
Example hom_pequiv_is_pointwise {x y : SetoidObject}
  (Py : PropEquiv (is_setoid y)) (f g : x ~{Sets}~> y) :
  @pequiv _ _ (hom_PropEquiv Py) f g
    = (forall a : carrier x, @pequiv _ _ Py (f a) (g a)) := eq_refl.

(** ** Binary products *)

(* [Sets_Cartesian]'s product setoid is componentwise
   (Instance/Sets/Cartesian.v:33).  The conjunction below is Coq's [and],
   written `/\`; the library's `∧` is [prod] and would leave the relation in
   [Type].

   Measured:

     product_PropEquiv@{u u0} :
       ∀ {x y : SetoidObject@{u0 u0}},
       PropEquiv@{u0 u0} x → PropEquiv@{u0 u0} y →
       PropEquiv@{u0 u0} (Cartesian.product_obj x y)
     (* u u0 |= u0 < u, and the stdlib bounds u0 <= prod_rect.u0..u2,
        u0 <= projections.u0, u0 <= projections.u1 *)

   -- the second universe [u] is [Sets]'s own object level, one above the
   carriers, and comes from naming [Sets_Cartesian]; the PropEquiv itself
   stays at [u0]. *)
#[export] Instance product_PropEquiv {x y : SetoidObject}
  (Px : PropEquiv (is_setoid x)) (Py : PropEquiv (is_setoid y)) :
  PropEquiv (is_setoid (@product_obj Sets Sets_Cartesian x y)).
Proof.
  unshelve refine
    {| pequiv := fun p q => @pequiv _ _ Px (fst p) (fst q)
                            /\ @pequiv _ _ Py (snd p) (snd q) |}.
  - intros p q [H1 H2]; exact (pequiv_to _ _ H1, pequiv_to _ _ H2).
  - intros p q H; split;
      [ exact (pequiv_from _ _ (fst H)) | exact (pequiv_from _ _ (snd H)) ].
Defined.

Example product_pequiv_is_componentwise {x y : SetoidObject}
  (Px : PropEquiv (is_setoid x)) (Py : PropEquiv (is_setoid y))
  (p q : carrier (@product_obj Sets Sets_Cartesian x y)) :
  @pequiv _ _ (product_PropEquiv Px Py) p q
    = (@pequiv _ _ Px (fst p) (fst q) /\ @pequiv _ _ Py (snd p) (snd q))
  := eq_refl.

(** ** Indexed products *)

(* [Sets_iprod_equiv F g h := ∀ i, g i ≈ h i] (Instance/Sets/Products.v:256):
   pointwise in the index, so the [Prop] mirror is pointwise too.  The index
   type [A] is arbitrary and carries no setoid, exactly as [HasIndexedProducts]
   asks.

   Measured:

     iprod_PropEquiv@{u u0 u1 u2 u3} :
       ∀ {A : Type@{u}} (F : A → SetoidObject@{u2 u3}),
       (∀ i : A, PropEquiv@{u2 u3} (F i)) →
       PropEquiv@{u0 u1} (Sets_iprod_obj@{u u0 u1 u2 u3} F)
     (* u u0 u1 u2 u3 |= u <= u0, u <= u1, u2 <= u0, u3 <= u1 *)

   -- the product's carrier universe [u0] is bounded below by the INDEX and by
   the components, and by nothing else: a product over a carrier-sized index of
   carrier-sized factors stays carrier-sized. *)
#[export] Instance iprod_PropEquiv {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i))) :
  PropEquiv (is_setoid (Sets_iprod_obj F)).
Proof.
  unshelve refine {| pequiv := fun g h => forall i : A, @pequiv _ _ (H i) (g i) (h i) |}.
  - intros g h Hgh i. exact (pequiv_to _ _ (Hgh i)).
  - intros g h Hgh i. exact (pequiv_from _ _ (Hgh i)).
Defined.

Example iprod_pequiv_is_pointwise {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i)))
  (g h : carrier (Sets_iprod_obj F)) :
  @pequiv _ _ (iprod_PropEquiv F H) g h
    = (forall i : A, @pequiv _ _ (H i) (g i) (h i)) := eq_refl.

(** ** Limits *)

(* [Sets_limit_equiv p q := `1 p ≈ `1 q] (Instance/Sets/Complete.v:141): the
   compatibility witness carried alongside a family is not compared, so the
   [Prop] mirror is the underlying indexed product's, i.e. pointwise in the
   shape.

   Measured:

     limit_PropEquiv@{u u0 u1 u2} :
       ∀ {D : Category@{u1 u2 u2}} (F : D ⟶ Sets),
       (∀ d : obj[D], PropEquiv@{u2 u2} (F d)) →
       PropEquiv@{u u} (Sets_limit_obj@{u1 u2 u0 u} F)
     (* u u0 u1 u2 |= u2 < u0, u1 <= u, u2 <= u, plus Projections and
        compose bounds *)

   -- the limit's carrier universe [u] is bounded below by the SHAPE's object
   universe [u1] as well as by the components, which is the size constraint the
   solution-set argument runs into elsewhere. *)
#[export] Instance limit_PropEquiv {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d))) :
  PropEquiv (is_setoid (Sets_limit_obj F)).
Proof.
  unshelve refine
    {| pequiv := fun p q : Sets_limit_carrier F =>
                   forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d) |}.
  - intros p q Hpq d. exact (pequiv_to _ _ (Hpq d)).
  - intros p q Hpq d. exact (pequiv_from _ _ (Hpq d)).
Defined.

Example limit_pequiv_is_pointwise {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d)))
  (p q : Sets_limit_carrier F) :
  @pequiv _ _ (limit_PropEquiv F H) p q
    = (forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d)) := eq_refl.

(** ** Locally propositional categories *)

(* A category is LOCALLY PROPOSITIONAL when each of its hom-setoids has a
   [Prop] equality.  This is the hypothesis under which a construction that
   turns an object of an ambient category into a concrete algebraic object --
   a functor of points, an internal hom of group objects -- lands back among
   the propositional carriers.  It is deliberately a property of the AMBIENT
   category and says nothing about its objects.

   Instance/Sets.v's [Sets] is not declared to have it, for the reason in this
   file's header; neither is [Cat], and Test/ProbePropEquiv.v measures the
   refusal for [Cat].

   Measured:

     LocallyPropositional@{u u0} : Category@{u0 u u} → Type@{max(Set+1,u,u0)}
     (* u u0 |=  *)

   -- at the maximum of the category's OBJECT and HOM universes, the object one
   entering through the [∀ x y : C]. *)
Class LocallyPropositional (C : Category) := {
  locally_prop : forall x y : C, PropEquiv (@homset C x y)
}.

(* The constructor: naming a [Prop]-valued relation on each hom and the two
   implications is enough.  As in Lib/Setoid/Propositional.v, the relation has
   to be named -- an ascription [(f ≈ g : Prop)] is refused. *)
Definition LocallyPropositional_of_relation (C : Category)
  (R : forall x y : C, (x ~> y) -> (x ~> y) -> Prop)
  (to : forall (x y : C) (f g : x ~> y), R x y f g -> f ≈ g)
  (from : forall (x y : C) (f g : x ~> y), f ≈ g -> R x y f g) :
  LocallyPropositional C :=
  {| locally_prop := fun x y =>
       PropEquiv_of_relation (R x y) (to x y) (from x y) |}.

(* The hom-setoid whose `≈` is Coq's [eq] (Theory/Category.v:242) is
   propositional outright.  Any category declaring [homset := Morphism_equality]
   -- Instance/One.v's [_1] and Instance/Zero.v's [_0] among them -- is
   therefore locally propositional by [LocallyPropositional_of_relation] with
   [R := fun _ _ => eq]; the instances for the individual such categories are
   left to the files that need them, since each would pull its own import in
   here. *)
#[export] Instance Morphism_equality_PropEquiv {ob : Type}
  {hom : ob -> ob -> Type} (x y : ob) :
  PropEquiv (@Morphism_equality ob hom x y).
Proof.
  unshelve refine {| pequiv := @eq (hom x y) |}.
  - intros f g h; exact h.
  - intros f g h; exact h.
Defined.

(* The same statement for a whole category, as a transport rather than an
   instance: "C's hom-setoid IS strict equality" is not a property of an
   arbitrary [C] that instance resolution can check, so it is taken as a
   hypothesis. *)
Definition LocallyPropositional_of_eq (C : Category)
  (H : forall x y : C, @homset C x y = Morphism_equality x y) :
  LocallyPropositional C.
Proof.
  constructor.
  intros x y.
  rewrite (H x y).
  exact (Morphism_equality_PropEquiv x y).
Defined.
