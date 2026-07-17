Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The opposite (dual) category C^op. *)

(* nLab: https://ncatlab.org/nlab/show/opposite+category
   Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

   C^op has the same objects as C, with hom-sets reversed,
   hom[C^op] x y := hom[C] y x, so that f : y ~> x in C is read as
   f : x ~{C^op}~> y.  Identities are unchanged and composition is reversed:
   g ∘ f in C^op is f ∘ g in C.

   Duality is built in here so that (C^op)^op = C holds by reflexivity: the
   two associativity laws are swapped (comp_assoc uses comp_assoc_sym and vice
   versa) and compose_respects is re-bracketed symmetrically, so applying the
   construction twice lands every field back on its original (see op_invol,
   provable by [reflexivity]). *)

(* Duality: the principle, its history, and what strictness buys

   nLab (duality): https://ncatlab.org/nlab/show/duality
   nLab (presheaf): https://ncatlab.org/nlab/show/presheaf
   Wikipedia: https://en.wikipedia.org/wiki/Dual_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Duality_(projective_geometry)

   The opposite category is the theorem-doubling device of category
   theory.  Because the axioms for a category are invariant under
   reversing every arrow, a statement holds in C precisely when its dual —
   source and target swapped, composites read in the other order — holds
   in C^op, so any theorem proved for all categories yields its dual with
   no further work (Mac Lane, "Categories for the Working Mathematician",
   Springer 1978, p. 33; Awodey, "Category Theory", Oxford 2010).  nLab
   states the point at the level of the theory itself: the signature of
   the elementary theory of categories carries a nontrivial involution, so
   every formal theorem has a formal dual — the same phenomenon as the
   meet/join duality of lattices and the point/line duality of the
   projective plane.

   That precedent is older than the subject by a century.  In the
   projective geometry of the early nineteenth century, Gergonne, who
   coined the term "duality", printed dual theorems side by side in his
   journal, while Poncelet held the point/line interchange to be a
   consequence of the theory of poles and polars: two points determine a
   line, two lines meet in a point, one theorem read twice.  Category
   theory then internalized the phenomenon from its first pages —
   Eilenberg and Mac Lane open with the dual vector space, coin
   "contravariant" for the arrow-reversing functor, and observe that the
   double dual is natural where the single dual is not (Eilenberg and
   Mac Lane, "General theory of natural equivalences", Trans. Amer. Math.
   Soc. 58 1945).  Mac Lane soon made duality itself the object of study:
   restate the element-based notions of group theory purely in terms of
   homomorphisms and composition, and dual axioms yield dual theorems
   (Mac Lane, "Groups, categories and duality", Proc. Nat. Acad. Sci. 34
   1948; "Duality for groups", Bull. Amer. Math. Soc. 56 1950).  Pursued
   through Buchsbaum and Grothendieck, that program produced abelian
   categories, whose self-dual axioms hand homological algebra two dual
   results out of one (Goswami and Janelidze, "Duality in non-abelian
   algebra IV", arXiv:1704.01863 2018).

   Downstream of this file the library takes dual concepts by definition,
   not by analogy: a comonad is a monad on C^op (Theory/Monad.v), a
   colimit is a limit of the opposite diagram (Structure/Limit.v), initial
   objects are terminal in C^op (Structure/Initial.v), coproducts are
   opposite products (Structure/Cocartesian.v), a coend is an end of the
   opposed functor (Structure/Coend.v), and F-coalgebras apply the
   construction twice (Construction/FCoalg.v).  Each one-line definition
   inherits the entire theory of its primal concept.  Contravariance is
   equally the substrate of representability: a presheaf is a functor out
   of U^op (Theory/Sheaf.v), and the curried hom [Curried_Hom] of
   Functor/Hom.v, itself a functor from C^op, feeds the Yoneda development
   of Functor/Hom/Yoneda.v.  Opposition extends to functors (F^op, in
   Functor/Opposite.v) and to natural transformations, where the direction
   reverses: a transformation between F^op and G^op corresponds to one
   from G to F (Natural/Transformation/Opposite.v).  Up to natural
   isomorphism the identity and op are the only autoequivalences of Cat
   (nLab): arrow reversal is the one nontrivial symmetry the subject has.

   Whether reversing twice is literally the identity is a genuine design
   fork among proof assistants.  agda-unimath states that its opposite
   construction is a definitional involution, proved by refl; Agda's 1Lab
   swaps its identity laws just as this file does, but keeps a single
   associativity field, reversed by a path inversion, and — with eta
   disabled on its precategory record — exhibits involutivity as an
   isomorphism of precategories with identity components; agda-categories
   records that its bicategory-level op is only almost a definitional
   involution.  The paired fields of the base records here exist for this
   file's sake: [comp_assoc_sym] carries no content beyond [comp_assoc]
   (Theory/Category.v derives it in [Build_Category']), and
   [naturality_sym] repeats the device for 2-cells
   (Theory/Natural/Transformation.v), so [Opposite] permutes fields
   rather than composing them with symmetry proofs, and the dual
   definitions above unfold to their primal counterparts with no
   rewriting along an isomorphism — Comonad/Core.v reads each comonad law
   as its monad law backwards by exactly this.  At the level of arrows
   the construction costs nothing, since [op] and [unop] move no data.
   The working programmer's C^op is Haskell's Data.Functor.Contravariant,
   whose instances — predicates, comparisons, equivalence relations —
   consume values where covariant functors produce them, and whose
   documentation notes that the dual of a Functor is just a Functor;
   because op squared is the identity, there are likewise no cocomonads
   (Milewski, "Products and Coproducts", 2015). *)

Definition Opposite `(C : Category) : Category := {|
  obj     := @obj C;
  hom     := fun x y => @hom C y x;
  homset  := fun x y => @homset C y x;
  id      := @id C;
  compose := fun _ _ _ f g => g ∘ f;

  compose_respects := fun x y z f g fg h i hi =>
    @compose_respects C z y x h i hi f g fg;

  id_left  := fun x y f => @id_right C y x f;
  id_right := fun x y f => @id_left C y x f;

  comp_assoc := fun x y z w f g h => @comp_assoc_sym C w z y x h g f;
  comp_assoc_sym := fun x y z w f g h => @comp_assoc C w z y x h g f
|}.

Notation "C ^op" := (@Opposite C)
  (at level 7, format "C ^op", left associativity) : category_scope.

Lemma op_invol {C : Category} : (C^op)^op = C.
Proof.
  unfold Opposite; simpl.
  destruct C; simpl.
  f_equal.
Qed.

(* [op] and [unop] re-read a C-morphism as a C^op-morphism and back. Since the
   hom-sets are definitionally equal, both are the identity on the underlying
   arrow; they only flip how its direction is named. *)

Definition op   {C : Category} {x y} (f : y ~{C}~> x) : x ~{C^op}~> y := f.
Definition unop {C : Category} {x y} (f : x ~{C^op}~> y) : y ~{C}~> x := f.

(* If two objects are isomorphic in C, then they are also isomorphic in C^op,
   just the conversion arrows are flipped. *)

Require Import Category.Theory.Isomorphism.

#[export]
Program Instance Isomorphism_Opposite {C : Category} {x y : C}
       (iso : @Isomorphism C x y) :
  @Isomorphism (C^op) x y := {
  to := from iso;
  from := to iso;
  iso_to_from := iso_to_from iso;
  iso_from_to := iso_from_to iso
}.
