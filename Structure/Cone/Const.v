Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Comma.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* Wikipedia: "At first glance cones seem to be slightly abnormal
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

(** See Instance/Cones/Comma for a similar proof involving the category of
    cones. *)

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
