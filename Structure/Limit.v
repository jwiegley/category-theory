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
