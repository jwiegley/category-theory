Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

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

Definition Poset {C : Category} `{R : relation C}
           `(P : PreOrder C R) `{Asymmetric C R} : Category := Proset P.
