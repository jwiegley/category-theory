Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(** * Limit of a diagram (terminal cone) *)

(* nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   Wikipedia: "Let F : J ⟶ C be a diagram of shape J in a category C. A cone
   to F is an object N of C together with a family ψX : N ⟶ F(X) of morphisms
   indexed by the objects X of J, such that for every morphism f : X ⟶ Y in J,
   we have F(f) ∘ ψX = ψY.

   "A limit of the diagram F : J ⟶ C is a cone (L, φ) to F such that for any
   other cone (N, ψ) to F there exists a unique morphism u : N ⟶ L such that
   φX ∘ u = ψX for all X in J.

   "One says that the cone (N, ψ) factors through the cone (L, φ) with the
   unique factorization u. The morphism u is sometimes called the mediating
   morphism."

   Equivalently, the limit is the terminal object of the category of cones
   over F: the universal cone through which every other cone factors uniquely
   (nLab). The cone (L, φ) is recorded here as a [Cone F] (see
   [Structure/Cone.v]); a [Limit] bundles such a terminal cone with its
   universal property. In library notation the universal property reads:

       ∀ N : Cone F, ∃! u : vertex_obj[N] ~> vertex_obj[L],
         ∀ x : J, φ_x ∘ u ≈ ψ_x,

   where φ = vertex_map[L] are the limit's legs and ψ = vertex_map[N] are the
   competing cone's legs. (The same presheaf-representability view appears in
   [Structure/UniversalProperty/Limit.v], where representing [ConePresheaf F]
   is shown equivalent to being a limit.) *)

(* Where limits come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/colimit
   EoM:   https://encyclopediaofmath.org/wiki/Projective_limit
   Blog:  https://bartoszmilewski.com/2015/04/15/limits-and-colimits/
   Paper: Kan, "Adjoint functors", Transactions of the American
          Mathematical Society 87(2), 1958

   The concept is younger than its examples.  Inverse and direct limits
   over directed index sets were first studied as such in the 1930s, in
   connection with topological concepts such as Čech cohomology
   (Encyclopedia of Mathematics, "Projective limit"); the p-adic integers
   arise as the inverse limit of the rings Z/pⁿZ under remainder maps,
   and profinite groups, the Galois groups of infinite extensions among
   them, are inverse limits of finite groups (Wikipedia, "Inverse limit"
   and "Profinite group").  The formulation over an arbitrary diagram
   shape is due to Daniel Kan, in Chapter II of the 1958 paper that also
   introduced adjoint functors and Kan extensions (nLab, "colimit");
   those early articles still call colimits "direct limits", the directed
   special case lending the general notion its name for a while.

   The purpose of the general definition is economy: one universal
   property covers every construction that glues a diagram along a shape.
   Varying only J recovers the terminal object (J empty,
   Structure/Limit/Terminal.v), binary and indexed products (J discrete,
   Structure/Limit/Cartesian.v and Structure/Limit/Product.v), equalizers
   (J a parallel pair — Structure/Equalizer.v defines [Equalizer] as a
   [Limit] over [Parallel]), pullbacks (J a cospan,
   Structure/Pullback/Limit.v), and the classical inverse limits above
   (J a directed poset, read contravariantly).  Whatever is proved once
   about [Limit] — uniqueness up to unique isomorphism, preservation,
   construction from products and equalizers — thereby specializes to
   each of these at no further cost.

   Two reformulations knit the concept into the rest of the theory.
   Instance/Cones/Limit.v turns the terminal-cone slogan of the header
   into a theorem, extracting a [Limit F] from a terminal object of the
   category [Cones F] ([Limit_Cones]); Structure/Limit/Kan/Extension.v
   exhibits the limit as the right Kan extension of F along the unique
   functor J ⟶ 1, the other thread of Kan's 1958 paper.  When limits of
   every shape exist, they assemble into functors right adjoint to the
   constant-diagram functors Δ (Riehl, "Category Theory in Context",
   Dover 2016, Proposition 4.6.1).

   Downstream, the file is load-bearing in two ways.  Completeness — all
   small limits, quantified in Structure/Complete.v as [Complete] — is
   the standing hypothesis of the adjoint functor theorems, and
   Construction/Comma/Limit.v with Adjunction/GAFT.v concludes Freyd's
   theorem from it (Mac Lane, "Categories for the Working Mathematician",
   Springer GTM 5 1998, Chapter V).  The preservation vocabulary of
   Structure/Limit/Preservation.v ([PreservesLimit]) supports RAPL and
   LAPC — right adjoints preserve limits, left adjoints preserve
   colimits, with no size restriction (Riehl, Theorem 4.6.2) — proved
   in-tree as Adjunction/Continuity.v's [rapl_is_alimit] and its duals.
   Together with the existence theorem — a category with products and
   equalizers has all limits (Riehl, Theorem 3.5.11, dual form) — these
   make limits the everyday currency of adjunction arguments.

   The computational reading is concrete.  Products are pair types and
   the terminal object is unit (the reading Instance/Coq.v realizes); an
   equalizer carves out the subset on which two functions agree; and a
   pullback computes a most general unifier, which is how Milewski frames
   Hindley–Milner type inference (Milewski, "Limits and Colimits", 2015).
   The existence theorem is in effect a program: a limit is the part of
   the product of all F x whose components are compatible along every
   arrow of J, exactly the shape of the funext-free end of
   Instance/Sets/End.v.  The inverse-limit technique that opened the
   history returns in semantics — Scott's D∞ model of the untyped
   λ-calculus is an inverse limit of function lattices solving
   D ≅ [D → D], an equation Cantor confines to singletons in Set (Scott,
   "Continuous Lattices", Springer LNM 274 1972) — while the ω-chain
   apparatus of Construction/Chain.v and Theory/Adamek.v is the in-tree
   colimit-side counterpart, building initial algebras. *)
Class Limit `(F : J ⟶ C) := {
  (* The limit cone (L, φ): the terminal/universal cone over F. *)
  limit_cone : Cone F;

  (* Universal property: every cone N factors through the limit cone by a
     unique mediating morphism u on apexes, satisfying φ_x ∘ u ≈ ψ_x for
     every x in J. Here [N ~> limit_cone] is, via the [vertex_obj] coercion,
     a morphism vertex_obj[N] ~> vertex_obj[limit_cone] in C. *)
  ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone, ∀ x : J,
    vertex_map[limit_cone] ∘ u ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x
}.

(* [IsALimit F c] is the same universal property as [Limit], but with the
   apex pinned to a chosen object [c : C]: it is the (proof-relevant)
   predicate "c, with its leg family, is a limit of F". This apex-fixed form
   is the one consumed by [Structure/UniversalProperty/Limit.v]. *)
Class IsALimit `(F : J ⟶ C) (c : C) := {
    (* The limit's legs over the fixed apex c (the cone (c, φ)). *)
    limit_acone : ACone c F;
    (* Universal property at the fixed apex: every cone N factors through c by
       a unique u : vertex_obj[N] ~> c with φ_x ∘ u ≈ ψ_x for every x. The
       first [vertex_map] is φ (from [limit_acone]); the second is ψ (from N). *)
    ump_limit : ∀ N : Cone F, ∃! u : N ~> c, ∀ x : J,
    vertex_map _ ∘ u ≈ vertex_map x
  }.

(* Setoid on the limit witnesses at a fixed apex c: two witnesses are
   identified exactly when their leg families ([limit_acone]) agree as cones
   (pointwise up to ≈, via [AConeEquiv]); the universal-property proof is
   irrelevant to this equivalence. *)
Program Definition LimitSetoid `(F : J ⟶ C) (c : C) : Setoid (IsALimit F c) :=
  {| equiv := fun l1 l2 => @limit_acone _ _ _ _ l1 ≈ @limit_acone _ _ _ _ l2 |}.
Next Obligation.
  abstract(equivalence;
           specialize X with j; specialize X0 with j;
           exact (Equivalence_Transitive _ _ _ X X0)).
Defined.

Coercion limit_cone : Limit >-> Cone.

Require Import Category.Functor.Opposite.

(* The colimit of F is the dual notion: a limit of the opposite diagram
   F^op, i.e. the universal cocone / initial object of the category of
   cocones over F (nLab, Wikipedia). *)
Definition Colimit `(F : J ⟶ C) := Limit (F^op).
