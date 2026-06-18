Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Monoid.

Generalizable All Variables.

(** * Group objects in a cartesian monoidal category *)

(* nLab:      https://ncatlab.org/nlab/show/group+object
   Wikipedia: https://en.wikipedia.org/wiki/Group_object

   A group object in a category with finite products (here packaged as a
   cartesian monoidal category, where ⨂ is the product × and I is the terminal
   object 1) is a monoid object (mappend, mempty) on an object [grp] together
   with an inversion morphism [inverse : grp ~> grp] satisfying the two-sided
   inverse law. Writing μ = mappend, η = mempty, ι = inverse, ∆ for the
   diagonal grp ~> grp ⨂ grp and [eliminate] for the discard grp ~> I, the law
   is, as an equation of endomorphisms grp ~> grp:

     μ ∘ (ι ⨂ id) ∘ ∆ ≈ η ∘ eliminate ≈ μ ∘ (id ⨂ ι) ∘ ∆.

   The right-hand side η ∘ eliminate is the constant-at-the-unit endomorphism
   (nLab/Wikipedia's e_G = e ∘ !), NOT the unit object I: both inversion
   composites collapse to "send everything to the identity element". The
   associativity and two-sided unit laws come from the underlying monoid object
   ([groupobject_is_monoid]). This matches nLab/Wikipedia exactly; equivalently,
   [grp] is a group object iff each hom Hom(X, grp) is a group naturally in X.

   See Structure/Group/Proofs.v for the derived facts (uniqueness of inverses,
   the antihomomorphism law μ ∘ (ι ⨂ ι) ≈ ι ∘ μ ∘ braid, etc.). *)

Section GroupObject.

Context `{@CartesianMonoidal C}.

Class GroupObject (grp : C) := {
  (* Underlying monoid object: supplies mappend (μ), mempty (η) and the
     associativity + two-sided unit laws. *)
  groupobject_is_monoid : MonoidObject grp;
  (* Inversion / antipode ι : grp ~> grp. *)
  inverse : grp ~> grp;

  (* Left inverse: μ ∘ (ι ⨂ id) ∘ ∆ ≈ η ∘ eliminate (the constant-identity
     endomorphism). Copy g with ∆, invert the left copy, then multiply. *)
  left_inverse : mappend ∘ inverse ⨂ id ∘ ∆ grp ≈ mempty ∘ eliminate;

  (* Right inverse: μ ∘ (id ⨂ ι) ∘ ∆ ≈ η ∘ eliminate, dually inverting the
     right copy. *)
  right_inverse : mappend ∘ id ⨂ inverse ∘ ∆ grp ≈ mempty ∘ eliminate;
}.
#[export] Existing Instance groupobject_is_monoid.

Coercion groupobject_is_monoid : GroupObject >-> MonoidObject.

End GroupObject.

(* Projection to the inversion morphism ι of a given group object [G]. *)
Notation "'inverse' [ G ]" := (@inverse _ _ G _)
  (at level 9, format "inverse [ G ]") : category_scope.
