Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** The core groupoid of a category C: its maximal sub-groupoid. *)

(* nLab: https://ncatlab.org/nlab/show/core
   nLab: https://ncatlab.org/nlab/show/groupoid
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid

   A groupoid is a category in which every morphism is an isomorphism
   (invertible). Given a category C, its core is the maximal sub-groupoid:
   the same objects as C, but with only the isomorphisms of C as morphisms.
   Here [Groupoid C] realises that core. Its objects are @obj C; a morphism
   x ~> y is an isomorphism x ≅ y in C (hom := @Isomorphism C); the identity
   is iso_id and composition is iso_compose. Morphism equivalence is equivalence
   of isomorphisms (homset := @iso_setoid C), i.e. two isos agree when their
   `to` and `from` components agree under `≈` (see Theory.Isomorphism).

   The core construction is the underlying-groupoid functor and is right adjoint
   to the inclusion Grpd ↪ Cat: a functor out of a groupoid into C must send
   every morphism to an isomorphism, so it factors through the core. *)

(* Groupoids before categories, and the core at work

   nLab:  https://ncatlab.org/nlab/show/groupoid
   Paper: Brandt, "Über eine Verallgemeinerung des Gruppenbegriffes",
          Mathematische Annalen 96, 1927
   Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of
          the London Mathematical Society 19, 1987
   Paper: Weinstein, "Groupoids: Unifying Internal and External Symmetry",
          Notices of the American Mathematical Society 43, 1996

   Groupoids predate categories by nearly two decades.  Heinrich Brandt
   introduced and named them in a 1926/27 paper in the Mathematische
   Annalen, the outcome of over thirteen years spent extending Gauss's
   composition of binary quadratic forms to quaternary forms; the same
   circle of ideas let him carry ideal arithmetic over to quaternion
   algebras, a finite groupoid standing in for the classical finite
   abelian class group (Brown 1987).  Brandt in fact required an arrow
   between every pair of objects — the connected case, still called a
   Brandt groupoid — and the modern definition, a category in which
   every morphism is invertible, is the later relaxation.  Brown also
   records the remark that Brandt's axioms influenced Eilenberg and Mac
   Lane's definition of a category, together with Eilenberg's denial of
   it: had they thought of groupoids, they would have used them as an
   example.

   What a groupoid offers beyond a group is symmetry between objects
   rather than of a single object.  Weinstein's survey opens from the
   observation that many objects exhibit what is plainly recognized as
   symmetry yet possess few or no nontrivial automorphisms: a finite
   bathroom tiling has a four-element symmetry group, while its visible
   repetitive pattern is recovered by restricting the transformation
   groupoid of the ambient group action (Weinstein 1996).  The same
   relocation of structure drives the fundamental groupoid π₁(X, A) on
   a set A of base points: for a union with disconnected intersection
   there is no good single choice of base point, and Brown's
   formulation of the van Kampen theorem — one base point per
   component, the result an amalgamated free product of groupoids,
   following Higgins — proves a stronger theorem more simply (Brown
   1987).  Ehresmann, from 1950, added topological and differentiable
   structure and made groupoids a working tool of differential
   geometry; Grothendieck used them to tame the equivalence relations
   arising in moduli problems, and Connes replaced function algebras on
   intractable quotients by groupoid convolution algebras (Brown 1987;
   Weinstein 1996).

   Type theory rediscovered the notion from the inside.  In intensional
   Martin-Löf type theory the identity proofs of a type compose, invert,
   and associate up to higher identity, so each type carries groupoid
   structure rather than a mere equivalence relation; interpreting types
   as groupoids yields a model in which uniqueness of identity proofs is
   not derivable (Hofmann and Streicher, "The groupoid model refutes
   uniqueness of identity proofs", LICS 1994), and the full tower of
   iterated identity types is a weak ω-groupoid (Lumsdaine, "Weak
   ω-categories from intensional type theory", TLCA 2009; van den Berg
   and Garner, "Types are weak ω-groupoids", Proc. London Math. Soc.
   102, 2011).  Groupoids likewise model homotopy 1-types, the first
   rung of the homotopy hypothesis (nLab: groupoid).

   Within this library the core is the setoid of isomorphisms made
   compositional.  Because [Groupoid C] is an honest category, the
   generic rewriting lemmas — [id_left], [comp_assoc],
   [compose_respects] — apply verbatim to chains of isomorphisms, and
   Structure/UniversalProperty.v relies on exactly this, discharging the
   uniqueness leg of a universal property by computing inside [Groupoid]
   of a functor category into Sets.  Theory/Isomorphism.v supplies each
   morphism-level field of the construction, and its [iso_sym] provides
   the inverses that make the result a groupoid rather than merely a
   category.  The file constructs the core of a given C; no standalone
   category of groupoids exists in-tree, so the adjunction remark in
   the header above remains prose rather than a theorem.  The other
   adjoint to the same inclusion — localization, which universally
   inverts every morphism rather than discarding the non-invertible
   ones (nLab: core) — has its in-tree relative in
   Construction/Localization.v, and Theory/Category/Semi.v records the
   complementary weakening of the category axioms, dropping identities
   where the groupoid demands inverses. *)

Program Definition Groupoid (C : Category) : Category := {|
  obj     := @obj C;
  hom     := @Isomorphism C;
  homset  := @iso_setoid C;
  id      := @iso_id C;
  compose := @iso_compose C
|}.
