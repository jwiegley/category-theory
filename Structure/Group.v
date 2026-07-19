Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
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

(* Where group objects come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/Hopf+algebra
   Paper: Eckmann, Hilton, "Group-Like Structures in General Categories I:
          Multiplications and Comultiplications", Mathematische Annalen
          145, 1962

   A group object answers the question of what a group is when elements
   are unavailable.  The definition transcribes the group axioms as
   commuting diagrams — multiplication, unit, and inversion as morphisms,
   with no reference to underlying elements — and it follows that the same
   diagrams, interpreted in different ambient categories, yield
   topological groups in Top, Lie groups in smooth manifolds, group
   schemes in schemes over a base, simplicial groups in simplicial sets,
   and strict 2-groups in Cat (nLab and Wikipedia, as cited in the header
   above).

   The systematic notion is due to Eckmann and Hilton (1962), who called
   such structures G-objects and reached them from homotopy theory: the
   natural group structure of the cohomology H^n(X; G) is explained by a
   group-like multiplication on the Eilenberg–MacLane space K(G, n) in the
   homotopy category, with axioms "formulated entirely in terms of the
   maps of the category".  The same paper contains the functor-of-points
   reading — a G-object structure on A endows each hom-set H(X, A) with a
   group structure, naturally in X, and its Theorem 4.3 shows that every
   natural family of group structures on hom-sets arises this way —
   together with a footnote, added in proof, connecting the observation
   to Grothendieck's representable functors.  Algebraic geometry took
   that reading as primary at the same moment: group schemes as group
   objects, presented equivalently as representable functors into Grp,
   are the subject of SGA 3 (Demazure, Grothendieck, "Schémas en
   groupes", Springer LNM 151–153, 1970, from the 1962–64 séminaire).
   Mac Lane canonized the notion as "Groups in Categories" (Categories
   for the Working Mathematician, 2nd ed., 1998, Section III.6), and
   Awodey opens his chapter on groups and categories with it (Category
   Theory, 2nd ed., 2010, Chapter 4).

   The notion also sees structure that ordinary group theory cannot.  A
   group object in Grp itself is an abelian group: the two
   multiplications satisfy an interchange law, and the Eckmann–Hilton
   argument (Eckmann, Hilton, Theorem 1.12 in "Structure maps in group
   theory", Fundamenta Mathematicae 50, 1961) forces them to coincide and
   to commute — the same argument shows that the homotopy groups π_n are
   abelian for n ≥ 2.  nLab further records a recognition principle: a
   monoid object is a group object exactly when its associativity square
   is a pullback, so once stated through limits, invertibility is a
   property of a monoid rather than extra structure.

   The [CartesianMonoidal] hypothesis is load-bearing.  Both inverse laws
   [left_inverse] and [right_inverse] are written in copy/discard
   vocabulary — ∆ copies the value, [eliminate] discards it — and a
   general monoidal category supplies neither, which is why
   [MonoidObject] in Structure/Monoid.v asks for no such hypothesis
   (Monad/Monoid.v internalizes it in the endofunctor category under
   composition, a tensor that is not cartesian) while [GroupObject] must.
   Replacing the missing diagonal by a chosen compatible comonoid
   structure turns [inverse] into an antipode and the inverse laws into
   the antipode axioms; the result is a Hopf monoid, in Vect a Hopf
   algebra (nLab), the structure first observed by Hopf in the homology
   of Lie groups (Hopf, "Über die Topologie der
   Gruppen-Mannigfaltigkeiten und ihre Verallgemeinerungen", Annals of
   Mathematics 42(1), 1941).  A commutative Hopf algebra is in turn the
   same as a group object in the opposite category of algebras — that is,
   in affine schemes (nLab) — and every commutative Hopf algebra over a
   field arises so from an affine group scheme, an antiequivalence of
   categories (Wikipedia, "Hopf algebra").  The copy/discard vocabulary
   for monoidal categories with a comonoid supply is developed in
   Structure/Monoidal/CopyDiscard.v, and the library's concrete contact
   with the antipode is the Hopf law between Z- and X-spiders in
   Instance/ZX.v. *)

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
