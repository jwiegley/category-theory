Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   An initial object `0` is an object equipped, for every object `x`, with a
   morphism `zero : 0 ~> x` (written `¡` in the literature), subject to the
   universal mapping property that this morphism is unique: any two morphisms
   `0 ~> x` are equal (zero_unique). This is exactly the dual of a terminal
   object: an initial object in C is a terminal object in C^op, with all arrows
   reversed. The dual of `one : x ~> 1` is `zero : 0 ~> x`. An object that is
   both initial and terminal is a zero object. *)

(* Where initial objects come from, and what they are for

   Wikipedia: https://en.wikipedia.org/wiki/Universal_property
   nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   nLab:      https://ncatlab.org/nlab/show/empty+type

   The initial object is the purest species of universal property: an
   object characterized not by any internal structure but solely by its
   relationship to everything else.  Universal mapping properties of
   this kind were presented by Pierre Samuel in 1948 for topological
   constructions and subsequently used extensively by Bourbaki, a
   decade before Kan independently introduced the closely related
   notion of adjoint functors in 1958 (Wikipedia, "Universal
   property").  The initial object is the empty case of the whole
   theory of colimits — the colimit of the empty diagram, equivalently
   the nullary coproduct — which is why the unit laws [coprod_zero_l]
   and [coprod_zero_r] of Structure/Cocartesian.v exhibit 0 as the unit
   of the coproduct.  Any two initial objects are isomorphic by a
   unique isomorphism, and this uniqueness up to unique isomorphism,
   shared by every universal construction, is what licenses speaking of
   THE initial object (Milewski, "Products and Coproducts", 2015).
   When the initial object moreover coincides with the terminal one,
   Structure/ZeroObject.v records the coincidence as [zero_coincide],
   and the additive spine of the library builds on it.

   A substantial portion of category theory reduces to exhibiting an
   initial object somewhere.  A universal arrow from c to a functor F IS
   an initial object of a comma category (Wikipedia, "Universal
   property"), and Theory/Universal/Arrow.v defines it exactly so, as
   the field [arrow_initial]; a colimit is an initial cocone; and a left
   adjoint to U exists precisely when each comma category d ↓ U has an
   initial object, the pivot on which Freyd's adjoint functor theorem
   turns.  That pivot is load-bearing in-tree: Theory/WeaklyInitial.v
   promotes a weakly initial family to a genuine initial object by
   Freyd's product-plus-equalizer construction
   ([initial_from_weakly_initial]), and Adjunction/GAFT.v concludes the
   theorem through [GAFT_from_initials].  Even the empty category [_0]
   of Instance/Zero.v is an instance, initial in Cat via the vacuous
   functor [From_0].

   The initial object also seeds the categorical account of induction.
   Adámek constructs the initial F-algebra as the colimit of the ω-chain
   0 ~> F 0 ~> F² 0 ~> ... based at the initial object (Adámek, "Free
   algebras and automata realizations in the language of categories",
   Comment. Math. Univ. Carolinae 1974); in this library the chain of
   Construction/Chain.v starts at [initial_obj], and Theory/Adamek.v
   derives the initial algebra as [adamek].  Lambek had already observed
   that the structure map of any initial algebra is an isomorphism
   (Lambek, "A Fixpoint Theorem for Complete Categories", Mathematische
   Zeitschrift 1968), formalized as [lambek] in Theory/Lambek.v; and the
   unique algebra morphism out of the initial algebra is the fold —
   [cata] of Theory/Recursion.v — so structural recursion is initiality
   put to work.  The ADJ group made this the basis of programming
   language semantics: abstract syntax is an initial algebra, and a
   semantics is the unique homomorphism into any target algebra, with
   compositionality following at once (Goguen, Thatcher, Wagner, Wright,
   "Initial Algebra Semantics and Continuous Algebras", JACM 1977).

   The computational reading of this file is the empty type.  In
   Instance/Coq.v, [Coq_Initial] witnesses False as the initial object
   of the category of Coq types, the unique arrow out being [False_rect]
   — the empty function, Haskell's Void with its absurd (Milewski,
   "Products and Coproducts", 2015).  Under propositions-as-types the
   empty type is falsehood, its eliminator is exactly ex falso
   quodlibet, and the eta-rule supplies the uniqueness half of
   initiality (nLab, "empty type").  Read this way, [zero_unique] costs
   nothing: a function out of the empty type is defined by zero clauses,
   and any two such functions agree because there is no argument on
   which they could differ. *)

(* To be initial is just to be terminal in the opposite category; but to avoid
   confusion, we'd like a set of notations specific to categories with initial
   objects. As a consequence the initial-object UMP is not restated here as a
   primitive Class: `Initial C` literally unfolds to `Terminal (C^op)`, and the
   projections below recover the C-side names (initial_obj, zero, zero_unique)
   from the Terminal fields. *)

Notation "'Initial' C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.

Section Initial_.

Context `{I : @Initial C}.

(* The initial object `0` itself (terminal in C^op).         *)
Definition initial_obj : C := @terminal_obj _ I.

(* The unique morphism `¡ : 0 ~> x` (the `one` of C^op).      *)
Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

(* Uniqueness: any two morphisms out of `0` are equivalent.   *)
Definition zero_unique {x} (f g : initial_obj ~{C}~> x) : f ≈ g :=
  @one_unique _ I _ _ _.

End Initial_.

Notation "0" := initial_obj : object_scope.

Notation "zero[ C ]" := (@zero _ _ C)
  (at level 9, format "zero[ C ]") : morphism_scope.

(* Postcomposing the unique morphism `0 ~> x` is again unique (dual of
   one_comp): any `f ∘ zero` is forced to equal `zero` by zero_unique. *)
Corollary zero_comp `{T : @Initial C} {x y : C} {f : x ~> y} :
  f ∘ zero ≈ zero.
Proof. apply (@one_comp _ T). Qed.
