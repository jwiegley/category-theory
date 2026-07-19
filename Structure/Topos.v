Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* Elementary toposes.

   nLab:      https://ncatlab.org/nlab/show/topos
   nLab:      https://ncatlab.org/nlab/show/power+object
   Wikipedia: https://en.wikipedia.org/wiki/Topos

   An elementary topos is a category with finite limits that is cartesian
   closed and has a subobject classifier.  Finite limits are carried
   EXPLICITLY here as terminal object + binary products + pullbacks: the
   reduction of pullbacks to products and equalizers (and conversely) is not
   formalized in this library, so we do not pretend one component subsumes
   another, and we deliberately do not add equalizers to the class.

   Universe note: the class is a plain record of the component classes, each
   universe-polymorphic over the ambient category; it introduces no universe
   constraints beyond those of its fields. *)

Class ElementaryTopos (C : Category) := {
  topos_terminal   : @Terminal C;
  topos_cartesian  : @Cartesian C;
  topos_pullbacks  : @HasPullbacks C;
  topos_closed     : @Closed C topos_cartesian;
  topos_classifier : @SubobjectClassifier C topos_terminal
}.

#[export] Existing Instance topos_terminal.
#[export] Existing Instance topos_cartesian.
#[export] Existing Instance topos_pullbacks.
#[export] Existing Instance topos_closed.
#[export] Existing Instance topos_classifier.

(* The power object of a: the exponential Ω^a.  Mind the argument order of
   Structure/Cartesian/Closed.v: [exponent_obj x y] displays as y ^ x, so
   [Ω ^ a] is [exponent_obj a Ω]. *)
Definition Pow {C : Category} {H : ElementaryTopos C} (a : C) : C := Ω ^ a.

(* The relations isomorphism: subobjects of a × b (relations between a and b)
   correspond to morphisms a ~> Pow b, as an isomorphism of setoids in Sets.
   It is the composite of the classification isomorphism

       SubObj (a × b)  ≅  (a × b ~> Ω)       (classifier_classifies)

   with the exponential transpose

       (a × b ~> Ω)  ≅  (a ~> Ω^b)           (exp_iso)

   Orientation: the in-tree [exp_iso] of Structure/Cartesian/Closed.v curries
   the SECOND factor of the product — Hom(x × y, z) ≅ Hom(x, z^y) — so the
   relation's first leg a is the remaining source and its second leg b is the
   exponent: SubObj (a × b) ≅ (a ~> Pow b).  Both directions and the round
   trips come from composing the two isomorphisms in Sets. *)
Definition relations_iso {C : Category} {H : ElementaryTopos C} (a b : C) :
  @Isomorphism Sets {| carrier := SubObj (a × b) |}
                    {| carrier := a ~> Pow b |} :=
  iso_compose exp_iso (classifier_classifies (a × b)).
