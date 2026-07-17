Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(* A pullback (also called a fibered product) is the limit of a cospan
   `b → a ← c`; it is dual to the pushout (a pullback in C is a pushout in
   C^op).

   nLab:      https://ncatlab.org/nlab/show/pullback
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   Universal property, in this library's notation: a pullback of f and g is an
   object [Pull] with projections [pullback_fst : Pull ~> x] and
   [pullback_snd : Pull ~> y] satisfying f ∘ pullback_fst ≈ g ∘ pullback_snd,
   such that for every (Q, q1, q2) with f ∘ q1 ≈ g ∘ q2 there is a unique
   u : Q ~> Pull with pullback_fst ∘ u ≈ q1 and pullback_snd ∘ u ≈ q2. *)

(* Given a cospan in C:

           A         B
            \       /
           f \     / g
              \   /
                v
                C

   This can be thought of, set-theoretically, as singling out the pairs that
   agree under f and g, i.e. those satisfying the equation:

      f(a) = g(b),   for a ∈ A, b ∈ B

   A pullback is the subset of the cartesian product of A and B,
   X ⊆ A × B, consisting of exactly those pairs (a, b) for which f(a) = g(b),
   where the following diagram commutes:

                 X
               /   \
           pA /     \ pB
             /       \
            A         B
             \       /
            f \     / g
               \   /
                 v
                 C

   An example of this is an INNER JOIN of two SQL tables, where f projects a
   primary key from A, and g a foreign key referencing A, so that X contains
   exactly those pairs of rows from A and B where id(A) = fkey(B).

   Wikipedia: "In fact, the pullback is the universal solution to finding a
   commutative square like this. In other words, given any commutative square
   [replacing in the above X with Y, and pA and pB with qA and qB] there is a
   unique function h : Y → X such that pA ∘ h ≈ qA and pB ∘ h ≈ qB." *)

(* Definition, in terms of morphisms and universal properties:

   Wikipedia: "A pullback of the morphisms f and g consists of an object P
   [Pull] and two morphisms p1 : P → X [pullback_fst] and p2 : P → Y
   [pullback_snd] for which the diagram

       P ---p2---> Y
       |           |
     p1|           |g
       |           |
       X ---f----> Z

   commutes. Moreover, the pullback (P, p1, p2) must be universal with respect
   to this diagram. That is, for any other such triple (Q, q1, q2) for which
   the following diagram commutes, there must exist a unique u : Q → P (called
   a mediating morphism) such that

    p1 ∘ u = q1,    p2 ∘ u = q2

   As with all universal constructions, a pullback, if it exists, is unique up
   to isomorphism. In fact, given two pullbacks (A, a1, a2) and (B, b1, b2) of
   the same cospan X → Z ← Y, there is a unique isomorphism between A and B
   respecting the pullback structure (proven below as [pullback_unique])." *)

(* Purpose, history, and the reach of the pullback

   nLab:  https://ncatlab.org/nlab/show/base+change
   nLab:  https://ncatlab.org/nlab/show/finite+limit
   nLab:  https://ncatlab.org/nlab/show/hyperdoctrine
   nLab:  https://ncatlab.org/nlab/show/span

   The pullback is the categorical semantics of an equation (nLab,
   "pullback"), and every use of it is some avatar of solving that equation
   universally.  One limit thereby subsumes many familiar operations.
   Pulling a monomorphism back along f computes the preimage of the
   subobject it names; the pullback of two monomorphisms is the
   intersection of subobjects; the pullback of f along itself is its
   kernel pair ([kernel_pair] in Structure/Regular.v); and trivializing z
   to the terminal object recovers the binary product, the reduction
   recorded in the closing notes of this file.  Conversely, a terminal
   object together with [HasPullbacks] generates every finite limit
   (Borceux, "Handbook of Categorical Algebra" I, Prop. 2.8.2), which is
   why Structure/Regular.v presents finite completeness economically as
   exactly those two structures.

   The name is imported from topology.  Steenrod's induced bundle
   (Steenrod, "The Topology of Fibre Bundles", Princeton University Press
   1951) forms, from a bundle over M and a map N → M, the bundle of pairs
   of a point of N and a bundle point over its image — this construction
   verbatim — and the classification of principal G-bundles as pullbacks
   of a universal bundle made the operation central to algebraic topology.
   Algebraic geometry knows the same limit as Grothendieck's produit fibré
   (Grothendieck and Dieudonné, "Éléments de géométrie algébrique" I,
   Publ. Math. IHÉS 4, 1960, §3.2); base change along a morphism is the
   engine of the relative point of view there, and for affine schemes the
   fibre product of Spec A and Spec B over Spec R is Spec of the tensor
   product A ⊗_R B (Wikipedia, "Pullback (category theory)").  The
   adjective "cartesian" descends from Grothendieck's fibered categories
   (Streicher, "Fibered Categories à la Jean Bénabou", arXiv:1801.02927):
   the cartesian arrows of the codomain fibration are precisely pullback
   squares, a correspondence realized in-tree by
   [codomain_cleaving_pullbacks] in Construction/Displayed/Codomain.v.

   In categorical logic, substitution is pullback.  Lawvere's
   hyperdoctrines (Lawvere, "Adjointness in Foundations", Dialectica 23,
   1969) cast reindexing along f as the interpretation of substitution and
   the quantifiers ∃ and ∀ as its adjoints, and Seely identified locally
   cartesian closed categories as semantics for dependent type theory
   (Seely, "Locally cartesian closed categories and type theory", Math.
   Proc. Camb. Phil. Soc. 95, 1984), reading the adjoint triple
   Σ_f ⊣ f* ⊣ Π_f as dependent sum, substitution, and dependent product.
   The base-change functor between slices, with its left adjoint, is built
   in Construction/Slice/Pullback.v as [Bang_Functor] ⊣ [Star_Functor];
   topos theory rests on the same operation, for
   Structure/SubobjectClassifier.v exhibits every mono as a pullback of
   [truth] in exactly one way, and Theory/Subobject/Functor.v obtains the
   Sub functor by chosen-pullback reindexing.

   A design note.  The [Pullback] record below packages the apex
   existentially — a pullback of f and g exists, and here is one — so it
   cannot assert that a GIVEN commuting square is a pullback.  The
   apex-pinned predicate [IsPullback], with conversions in both
   directions, the pasting law [pullback_paste], mono-stability
   [monic_pullback_stable], and the strengthened uniqueness
   [pullback_transport] — re-derived there because [pullback_unique]
   below is Qed-opaque — live in Theory/Morphisms/Stability.v, and that
   split carries the subobject and classifier developments.
   Structure/Pullback/Limit.v reconciles this record with [Limit] of a
   cospan diagram over the walking roof of Instance/Roof.v;
   Construction/Span/Category.v composes spans by exactly this
   construction (nLab, "span"); Instance/FinSet/Classifier.v computes
   [FinSet_Pullbacks] as counted subsets, so pullback objects reduce on
   closed inputs; and the INNER JOIN reading in the header above is
   developed by Spivak ("Category Theory for the Sciences", MIT Press
   2014).

   [WeakPullback] earns its keep in coalgebra.  Rutten's structure theory
   of bisimulations (Rutten, "Universal coalgebra: a theory of systems",
   Theoretical Computer Science 249, 2000) turns on whether an
   endofunctor weakly preserves pullbacks — carries pullback squares to
   weak pullback squares — and existence-only mediators, as in
   [weak_ump_pullbacks], are exactly what that hypothesis consumes. *)

Record Pullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  Pull         : C;            (* the pullback object  b ×_a c (fibered product) *)
  pullback_fst : Pull ~> x;    (* projection p1 : Pull ~> x *)
  pullback_snd : Pull ~> y;    (* projection p2 : Pull ~> y *)

  (* the projection square commutes *)
  pullback_commutes : f ∘ pullback_fst ≈ g ∘ pullback_snd;

  (* universal property: the commuting square is terminal among such squares,
     i.e. every competing cone (Q, q1, q2) factors through a unique mediator u *)
  ump_pullbacks : ∀ Q (q1 : Q ~> x) (q2 : Q ~> y), f ∘ q1 ≈ g ∘ q2
    → ∃! u : Q ~> Pull, pullback_fst ∘ u ≈ q1 ∧ pullback_snd ∘ u ≈ q2
}.

Coercion pullback_ob {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z)
         (L : Pullback f g) := @Pull _ _ _ _ _ _ L.

(** Pullbacks are unique up to a unique isomorphism respecting the projections.
    This is the standard proof from the universal property: each pullback gives
    a mediating morphism into the other, and the round-trip mediator into a
    pullback from itself must equal [id] by uniqueness. *)
Lemma pullback_unique {C : Category} {x y z : C} {f : x ~> z} {g : y ~> z}
      (P Q : Pullback f g) : Pull f g P ≅ Pull f g Q.
Proof.
  pose proof (ump_pullbacks f g Q _ (pullback_fst f g P) (pullback_snd f g P)
                            (pullback_commutes f g P)) as HQ.
  pose proof (ump_pullbacks f g P _ (pullback_fst f g Q) (pullback_snd f g Q)
                            (pullback_commutes f g Q)) as HP.
  pose proof (ump_pullbacks f g P _ (pullback_fst f g P) (pullback_snd f g P)
                            (pullback_commutes f g P)) as HPP.
  pose proof (ump_pullbacks f g Q _ (pullback_fst f g Q) (pullback_snd f g Q)
                            (pullback_commutes f g Q)) as HQQ.
  destruct (unique_property HQ) as [HQfst HQsnd].
  destruct (unique_property HP) as [HPfst HPsnd].
  unshelve refine {|
    to   := unique_obj HQ;
    from := unique_obj HP
  |}.
  - (* to ∘ from ≈ id at Pull Q, by uniqueness against HQQ *)
    transitivity (unique_obj HQQ).
    + symmetry; apply (uniqueness HQQ); split.
      * rewrite comp_assoc, HQfst; exact HPfst.
      * rewrite comp_assoc, HQsnd; exact HPsnd.
    + apply (uniqueness HQQ); split; apply id_right.
  - (* from ∘ to ≈ id at Pull P, by uniqueness against HPP *)
    transitivity (unique_obj HPP).
    + symmetry; apply (uniqueness HPP); split.
      * rewrite comp_assoc, HPfst; exact HQfst.
      * rewrite comp_assoc, HPsnd; exact HQsnd.
    + apply (uniqueness HPP); split; apply id_right.
Qed.

(** A category has all binary pullbacks if every cospan has a pullback.
    This is the dual of [HasPushouts] in [Structure/Pushout.v]. *)
Class HasPullbacks (C : Category) : Type := {
  pullback : forall {x y z : C} (f : x ~> z) (g : y ~> z), Pullback f g
}.

Arguments pullback {C _ x y z} f g.

(* A weak pullback differs from a pullback in that the mediating morphism is
   merely required to exist; uniqueness is dropped. *)
Record WeakPullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  weak_pull : C;
  weak_pullback_fst : weak_pull ~> x;
  weak_pullback_snd : weak_pull ~> y;

  weak_pullback_commutes :
    f ∘ weak_pullback_fst ≈ g ∘ weak_pullback_snd;

  weak_ump_pullbacks :
    ∀ Q (q1 : Q ~> x) (q2 : Q ~> y),
      f ∘ q1 ≈ g ∘ q2
      → ∃ u : Q ~> weak_pull,
          weak_pullback_fst ∘ u ≈ q1 ∧ weak_pullback_snd ∘ u ≈ q2
}.

(* Every pullback is a weak pullback by forgetting uniqueness. *)
Definition Pullback_to_WeakPullback {C : Category} {x y z : C}
           {f : x ~> z} {g : y ~> z} (P : Pullback f g) : WeakPullback f g.
Proof.
  refine {|
    weak_pull              := Pull f g P;
    weak_pullback_fst      := pullback_fst f g P;
    weak_pullback_snd      := pullback_snd f g P;
    weak_pullback_commutes := pullback_commutes f g P
  |}.
  intros Q q1 q2 H.
  pose proof (ump_pullbacks f g P Q q1 q2 H) as U.
  exists (unique_obj U).
  exact (unique_property U).
Defined.

(* jww (2017-06-01): TODO *)
(* Wikipedia: "The pullback is similar to the product, but not the same. One
   may obtain the product by "forgetting" that the morphisms f and g exist,
   and forgetting that the object Z exists. One is then left with a discrete
   category containing only the two objects X and Y, and no arrows between
   them. This discrete category may be used as the index set to construct the
   ordinary binary product. Thus, the pullback can be thought of as the
   ordinary (Cartesian) product, but with additional structure. Instead of
   "forgetting" Z, f, and g, one can also "trivialize" them by specializing Z
   to be the terminal object (assuming it exists). f and g are then uniquely
   determined and thus carry no information, and the pullback of this cospan
   can be seen to be the product of X and Y." *)

(* jww (2017-06-02): *)
(* Wikipedia: "... another way of characterizing the pullback: as the
   equalizer of the morphisms f ∘ p1, g ∘ p2 : X × Y → Z where X × Y is the
   binary product of X and Y and p1 and p2 are the natural projections. This
   shows that pullbacks exist in any category with binary products and
   equalizers. In fact, by the existence theorem for limits, all finite limits
   exist in a category with a terminal object, binary products and
   equalizers." *)
