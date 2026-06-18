Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Comma.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/cone
   Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)
   nLab: https://ncatlab.org/nlab/show/diagonal+functor

   A cone over a diagram F : J ⟶ C with apex N is the same data as a natural
   transformation Δ(N) ⟹ F out of the constant (diagonal) functor at N, and
   the same data as an object of the comma category (Δ ↓ F). The two lemmas
   below realise the first two of these equivalences in library notation:
   [Cone_Natural_Transform] proves Δ[J](N) ⟹ F ↔ Cone[N] F (a leg family with
   apex N), and [Cone_Comma] proves (Δ ↓ Δ(F)) ↔ Cone F (the diagram F is
   encoded as the constant functor Δ(F) : 1 ⟶ [J, C] so that both sides of the
   comma share a codomain). Limits arise as the universal/terminal such cone,
   equivalently as the right adjoint Δ ⊣ lim of the diagonal functor.

   Wikipedia: "At first glance cones seem to be slightly abnormal
   constructions in category theory. They are maps from an object to a functor
   (or vice versa). In keeping with the spirit of category theory we would
   like to define them as morphisms or objects in some suitable category. In
   fact, we can do both.

   "Let J be a small category and let Cᴶ be the category of diagrams of type J
   in C (this is nothing more than a functor category). Define the diagonal
   functor Δ : C → Cᴶ as follows: Δ(N) : J → C is the constant functor to N
   for all N in C.

   "If F is a diagram of type J in C, the following statements are equivalent:

     - ψ is a cone from N to F
     - ψ is a natural transformation from Δ(N) to F
     - (N, ψ) is an object in the comma category (Δ ↓ F)

   "The dual statements are also equivalent:

     - ψ is a co-cone from F to N
     - ψ is a natural transformation from F to Δ(N)
     - (N, ψ) is an object in the comma category (F ↓ Δ)

   "These statements can all be verified by a straightforward application of
   the definitions. Thinking of cones as natural transformations we see that
   they are just morphisms in Cᴶ with source (or target) a constant functor." *)

Lemma Cone_Natural_Transform `(F : [J, C]) :
  ∀ N : C, Δ[J](N) ⟹ F ↔ Cone[N] F.
Proof.
  split; intros.
  - construct; [ exact (X x) |].
    abstract(pose proof (naturality[X] _ _ f) as nat;
        simpl in nat;
        rewrite id_right in nat;
             now apply nat).
  - construct.
    + now apply X.
    + abstract(simpl; rewrite id_right; apply cone_coherence).
    + abstract(simpl; rewrite id_right; symmetry; apply cone_coherence).
Defined.

(* See Instance/Cones/Comma.v for the analogous statement upgraded to a
   functorial equivalence Cones F ≅[Cat] (Δ ↓ =(F)) between the whole category
   of cones and the comma category. *)

Lemma Cone_Comma `(F : [J, C]) : (Δ ↓ Δ(F)) ↔ Cone F.
Proof.
  split; simpl.
  - intros [[? ?] f].
    simplify; simpl in *.
    unshelve econstructor; [ exact o | unshelve econstructor ].
    + now apply f.
    + abstract(destruct f; simpl in *; intros x y f;
      rewrite <- (id_right (transform y));
      now apply naturality).
  - intros X.
    destruct X.
    exists (vertex_obj, vertex_obj).
    construct.
    + now apply vertex_map.
    + abstract(simpl;
               rewrite id_right;
               now apply cone_coherence).
    + abstract(simpl;
               rewrite id_right;
               symmetry;
               now apply cone_coherence).
Defined.
