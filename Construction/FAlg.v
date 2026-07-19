Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** * The category of F-algebras *)

(* nLab:      https://ncatlab.org/nlab/show/algebra+over+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/F-algebra

   For an endofunctor [F : C ⟶ C], an F-algebra is an object [a] with a
   structure map [α : F a ~> a] (this is [FAlgebra F a] of Theory/Functor.v).
   A morphism of F-algebras [(a, α) ~> (b, β)] is a carrier map [h : a ~> b]
   commuting with the structure maps: [h ∘ α ≈ β ∘ fmap[F] h].  These form the
   category [FAlg F]; its initial object (when it exists) is the least fixed
   point of [F], and Lambek's lemma shows the initial structure map is an
   isomorphism [F μF ≅ μF] (Theory/Lambek.v).

   The construction mirrors [Monad/Eilenberg/Moore.v]: a bundled hom class
   [FAlgHom] carrying the commuting square, a dependent-pair object carrier,
   and a hom-setoid comparing the underlying carrier maps. *)

(* Where the construction comes from, and what recursion becomes

   nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Catamorphism
   Paper: Lambek, "A Fixpoint Theorem for Complete Categories",
          Mathematische Zeitschrift 103, 1968
   Paper: Adámek, "Free algebras and automata realizations in the
          language of categories", Comment. Math. Univ. Carolinae 15(4),
          1974
   Paper: Meijer, Fokkinga, Paterson, "Functional Programming with
          Bananas, Lenses, Envelopes and Barbed Wire", FPCA 1991, LNCS 523
   Paper: Rutten, "Universal coalgebra: a theory of systems",
          Theoretical Computer Science 249(1), 2000

   The least-fixed-point reading the header records has a precise origin.
   Lambek (1968) sought fixed points of an endofunctor by locating an
   INITIAL algebra rather than by iterating the functor; the invertibility
   lemma the header names is the observation that underwrites the method.
   The modern literature reads that lemma as a categorification of the
   Knaster–Tarski lattice fixed-point theorem, and Lambek returned to the
   theme over cartesian closed bases in "Least Fixpoints of Endofunctors
   of Cartesian Closed Categories" (Math. Structures in Comp. Sci. 3,
   1993).

   Naming [FAlg F] a category, and not μF a fixed point alone, is what
   turns recursion into a universal property.  For any target algebra
   (a, β) there is exactly one algebra map out of the initial object, and
   its carrier is the CATAMORPHISM, the categorical fold.  Existence of
   that map is what permits a definition by structural recursion, and
   uniqueness is the induction and fusion principle used to reason about
   it.  Theory/Recursion.v makes this literal: [cata β] is
   [falg_hom[ @zero (FAlg F) I (a ; β) ]], the carrier of the initial
   mediator, and [cata_commutes] is its recursion equation.

   The programming lineage runs through this fold.  Bird and Meertens
   built a calculus of programs in the 1980s in which folds are the
   central operator, and Malcolm (1990) gave the categorical definition of
   a catamorphism as the unique homomorphism out of an initial algebra.
   Meijer, Fokkinga and Paterson (1991) introduced the banana-bracket
   notation for it, cast explicit recursion as the functional-programming
   counterpart of the arbitrary goto that structured programming had
   abandoned, and recovered the structured schemes — cata, ana, hylo —
   from which the later Haskell idiom descends; Wadler ("Recursive Types
   for Free!", 1990) ties inductive types to initial F-algebras in the
   same spirit.

   The header assumes an initial object "when it exists"; Adámek (1974)
   supplies it, building μF as the colimit of the ω-chain
   0 → F0 → F²0 → … whenever F preserves that colimit.  Theory/Adamek.v
   carries this as [adamek], proven from the leg-agreement hypothesis
   [AdamekData], over the diagram [Chain] (Construction/Chain.v) indexed by
   the ordinal ω (Instance/Omega.v).  The option endofunctor [NatF] in
   Theory/Adamek/Corollaries.v records the endofunctor side, though only
   the functor is formalized there; its [nat] initiality is left as a
   cross-reference to the list algebra, not a proven theorem.  The
   book-length account is Adámek and Trnková, Automata and Algebras in
   Categories (1990).

   Dually, [FCoalg] (Construction/FCoalg.v) is the category of coalgebras,
   whose TERMINAL object is the greatest fixed point νF — codata in place
   of data.  Rutten (2000) organizes this side into a theory of systems:
   finite data are initial algebras, whereas streams, automata and
   transition systems are final coalgebras, and the algebra / homomorphism
   / congruence trinity dualizes to coalgebra / homomorphism /
   bisimulation, with coinduction the proof principle, resting on the
   bisimulation of Milner (1980) and Park (1981) and the non-wellfounded
   sets of Aczel (1988).  In-tree, [lambek_final] and [ana] mirror
   [lambek] and [cata], and Instance/Sets/Streams.v realizes streams as
   the final [StreamF]-coalgebra with equality taken as bisimilarity.

   Read computationally, an object (a, β : F a ~> a) is a one-layer
   evaluator: given a top constructor layer whose children have already
   been reduced to results — an element of F a — it returns a result of
   type a.  For the list signature [ListF A] (Instance/Coq/Lists.v),
   sending X to 1 + A × X, the structure map is a pair: a nil case and a
   cons step, precisely the two arguments of foldr.  It follows that the
   initial algebra is the type of finite F-shaped values with its
   constructor bundle for a structure map, and [cata β] is the recursive
   fold threading β through the whole shape — realized axiom-free with
   [list A] as μ (ListF A). *)

Class FAlgHom `(F : C ⟶ C) (a b : C)
      (α : FAlgebra F a) (β : FAlgebra F b) := {
  falg_hom : a ~> b;
  falg_commutes : falg_hom ∘ α ≈ β ∘ fmap[F] falg_hom
}.

Notation "falg_hom[ H ]" := (@falg_hom _ _ _ _ _ _ H)
  (at level 9, format "falg_hom[ H ]") : morphism_scope.

Program Definition FAlg `(F : C ⟶ C) : Category := {|
  obj     := ∃ a : C, FAlgebra F a;
  hom     := fun x y => FAlgHom F ``x ``y (`2 x) (`2 y);
  homset  := fun _ _ => {| equiv := fun f g => falg_hom[f] ≈ falg_hom[g] |};
  id      := fun _ => {| falg_hom := id |};
  compose := fun _ _ _ f g => {| falg_hom := falg_hom[f] ∘ falg_hom[g] |}
|}.
Next Obligation.
  (* the composite carrier map is an algebra map, pasting the two squares
     (the id-map and the setoid/category-law obligations are discharged by the
     ambient obligation tactic, as in Monad/Eilenberg/Moore.v). *)
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- falg_commutes.
  rewrite <- !comp_assoc.
  rewrite <- falg_commutes.
  reflexivity.
Qed.

(* The forgetful functor to the underlying category, dropping the structure. *)
Program Definition FAlg_Forget `(F : C ⟶ C) : FAlg F ⟶ C := {|
  fobj := fun x => ``x;
  fmap := fun x y f => falg_hom[f]
|}.
