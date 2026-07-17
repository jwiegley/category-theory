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

(* Where toposes come from, and what they are for

   nLab:      https://ncatlab.org/nlab/show/topos
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere%E2%80%93Tierney_topology
   Book:  Artin, Grothendieck, Verdier, "Théorie des topos et cohomologie
          étale des schémas" (SGA 4), Lecture Notes in Mathematics 269,
          270, 305, Springer, 1972-1973
   Paper: Lawvere, "Quantifiers and Sheaves", Actes du Congrès
          International des Mathématiciens (Nice 1970), vol. 1,
          Gauthier-Villars, 1971, pp. 329-334

   An elementary topos is at once a generalized universe of sets and a
   categorical model of higher-order intuitionistic logic, and the
   tension between those two readings is why the concept repays study
   (nLab, "topos"; Mac Lane, Moerdijk, "Sheaves in Geometry and Logic",
   Springer 1992).  Set is the prototype of the first reading: every
   construction one performs on sets — products, function spaces, power
   sets, subsets cut out by a predicate — has a counterpart in an
   arbitrary topos, an abstract context for doing mathematics.

   Two lineages converged on the definition recorded above.  Grothendieck
   and his school introduced toposes around 1963-1964 as generalized
   spaces adequate for sheaf cohomology — the étale cohomology built to
   study the Weil conjectures — a Grothendieck topos being the category
   of sheaves on a small site (SGA 4, Tome 1, exposé IV "Topos", by
   Grothendieck and Verdier).  Independently, around 1969-1970, Lawvere
   and Tierney isolated a first-order, finitely axiomatizable description:
   a category with finite limits that is cartesian closed and carries a
   subobject classifier.  The adjective "elementary" marks exactly this,
   that the axioms pass almost directly into first-order logic, unlike the
   site-and-sheaf construction.  The description grew out of Lawvere's
   structural account of the category of sets (Lawvere, "An elementary
   theory of the category of sets", Proc. Natl. Acad. Sci. USA 52, 1964),
   which had already isolated the properties of Set that became the
   axioms — a structural, pluralistic alternative to ZF set theory.

   The subobject classifier is the component binding the two readings.
   In Set it is the two-element set 2, and a subset is the same datum as
   its characteristic function into 2, recovered as the pullback of the
   point true : 1 ~> 2.  An arbitrary topos replaces 2 by an object Ω, so
   that subobjecthood becomes representable: every mono is the pullback
   of one generic mono [truth] : 1 ~> Ω along a unique classifying map,
   which is the content of [classifier_classifies] of
   Structure/SubobjectClassifier.v.  Exponentiating gives the power
   object [Pow] a := Ω ^ a, the categorical power set, and [relations_iso]
   reads a subobject of a × b — an element of [SubObj] (a × b), a relation
   between a and b — as a map a ~> [Pow] b, currying its classifying
   predicate through the transpose [exp_iso].

   Under the logical reading Ω is the object of truth values, and the
   subobjects of any object form a Heyting algebra rather than a Boolean
   one, so the law of excluded middle and the axiom of choice need not
   hold internally while the remainder of higher-order reasoning goes
   through.  This internal type theory is the Mitchell-Bénabou language
   of the topos, its quantifiers appearing as adjoint functors.  Lawvere
   and Tierney observed that a Grothendieck topology is encoded by an
   idempotent, finite-meet-preserving endomorphism j : Ω ~> Ω; these
   Lawvere-Tierney topologies cut out the subtoposes as categories of
   sheaves, internalizing Grothendieck's construction (Lawvere 1971;
   Tierney).  Giraud's theorem (1972) closes the circle: an elementary
   topos with a small generating set, all small colimits, coproducts
   disjoint and universal, and equivalence relations effective is exactly
   a category of sheaves on a small site.

   The library exercises both readings.  Construction/Slice.v records the
   fundamental theorem of topos theory — every slice of a topos is again
   a topos (McLarty, "Elementary Categories, Elementary Toposes", Oxford
   University Press 1992) — and names [ElementaryTopos] as its target;
   Theory/Sheaf/Category.v carries the generalized-space side as sheaves
   inside presheaves; Adjunction/SAFT.v draws on the same subobject
   vocabulary through well-poweredness.  Computationally Ω is a type of
   truth values and the classifying [char] is the decision procedure of a
   subobject, so the classification isomorphism reads a subobject as its
   own membership predicate.  Skeletal FinSet makes this literal: Ω is 2,
   the classifying map is a decidable finite search, and the assembled
   [ElementaryTopos] witness [FinSet_Topos] of Instance/FinSet/Topos.v
   reduces, with [Pow] 2 evaluating to 4 by eq_refl.  In Sets the
   truth-value setoid lives one universe up, so the classifier survives
   as the cross-universe theorems of Instance/Sets/Classifier.v rather
   than a single instance. *)

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
