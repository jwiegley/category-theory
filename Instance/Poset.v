Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Closed.
Require Export Category.Structure.Initial.
Require Export Category.Structure.Terminal.
Require Export Category.Instance.Coq.
Require Export Category.Instance.Proset.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

(* Any partially-ordered set forms a category (directly from its preorder,
   since it simply adds asymmetry). See also [Pos], the category of
   partially-ordered sets (where the sets are the objects, and morphisms are
   monotonic mappings.

   Wikipedia: "Every poset (and every preorder) may be considered as a
   category in which every hom-set has at most one element. More explicitly,
   let hom(x, y) = {(x, y)} if x ≤ y (and otherwise the empty set) and (y, z)
   ∘ (x, y) = (x, z). Such categories are sometimes called posetal.

   Posets are equivalent to one another if and only if they are isomorphic. In
   a poset, the smallest element, if it exists, is an initial object, and the
   largest element, if it exists, is a terminal object. Also, every preordered
   set is equivalent to a poset. Finally, every subcategory of a poset is
   isomorphism-closed." *)

Instance Poset `{C : Category} `{R : crelation C}
         `(P : PreOrder C R) `{A : Asymmetric C R} : Category := Proset P.
