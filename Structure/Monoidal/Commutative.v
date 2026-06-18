Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section CommutativeMonoidal.

Context {C : Category}.
Context `{@SymmetricMonoidal C}.

(** Commutative monoidal category (self-braiding triviality). *)

(* nLab:      https://ncatlab.org/nlab/show/commutative+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

   A commutative monoidal category (nLab) is, strictly speaking, a commutative
   monoid object in (Cat, ×): a symmetric monoidal category whose associators,
   unitors AND braidings are all identity natural transformations, so that the
   braiding β_{x,y} ≈ id for every pair of objects and consequently x ⨂ y =
   y ⨂ x holds on the nose. That is the maximally strict notion of a
   "commutative" tensor product.

   This class does NOT impose that full strictness. It captures the weaker,
   purely self-referential condition that the braiding restricted to the
   DIAGONAL is trivial:

       braid ≈ id                       << x ⨂ x ~~> x ⨂ x >>

   i.e. β_{x,x} ≈ 1_{x ⨂ x} for every object x. Equivalently, swapping an
   object's two tensor copies of ITSELF does nothing. (In any symmetric
   monoidal category β_{x,x} is already an involution, β_{x,x} ∘ β_{x,x} ≈ id,
   by braid_invol; this axiom asks for the strictly stronger fact that β_{x,x}
   is the identity, not merely its own inverse — false in, e.g., super vector
   spaces, where swapping two odd vectors introduces a sign.)

   The two conditions are linked by a theorem of Kim (2016): a symmetric
   monoidal category is symmetric-monoidally EQUIVALENT to a commutative
   monoidal category iff all its self-braidings β_{x,x} are identities (proved
   assuming the objects can be totally ordered, e.g. under choice). The "only
   if" direction is immediate, since the property is equivalence-invariant.
   Hence this class names exactly the equivalence-invariant shadow of nLab's
   strict definition, without demanding strict equality of objects.

   Note the distinct meaning of "commutative" in
   Theory/Algebra/CommutativeMonoid.v: there it is a property of a MONOID
   OBJECT X in a symmetric monoidal category (mu ∘ braid ≈ mu), constraining a
   chosen multiplication. Here "commutative" is a property of the ambient
   MONOIDAL STRUCTURE itself (braid ≈ id on the diagonal), constraining no
   algebra. The two are independent. *)

Class CommutativeMonoidal := {
  (* Self-braiding is trivial: β_{x,x} ≈ 1_{x ⨂ x} for every object x. *)
  commutative {x} : @braid _ _ x x ≈ id
}.

End CommutativeMonoidal.
