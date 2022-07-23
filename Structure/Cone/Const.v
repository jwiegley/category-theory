Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Comma.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

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
  - construct.
    + construct.
      * exact N.
      * now apply X.
      * pose proof (naturality[X] _ _ f) as nat.
        simpl in nat.
        rewrite id_right in nat.
        now apply nat.
    + reflexivity.
  - destruct X as [X H], X.
    transform; intros;
    simpl in *; subst; simpl_eq.
    + now apply vertex_map.
    + rewrite id_right.
      now apply ump_cones.
    + rewrite id_right.
      symmetry.
      now apply ump_cones.
Qed.

(** See Instance/Cones/Comma for a similar proof involving the category of
    cones. *)

Lemma Cone_Comma `(F : [J, C]) : (Δ ↓ Δ(F)) ↔ Cone F.
Proof.
  split; simpl.
  - intros [[? ?] f].
    simplify; simpl in *.
    unshelve refine (Build_Cone _ _ _ _ _ _);
    simpl in *; intros.
    + exact o.
    + now apply f.
    + destruct f; simpl in *.
      rewrite <- (id_right (transform y)).
      now apply naturality.
  - intros X.
    destruct X.
    exists (vertex_obj, vertex_obj).
    construct.
    + now apply vertex_map.
    + simpl.
      rewrite id_right.
      now apply ump_cones.
    + simpl.
      rewrite id_right.
      symmetry.
      now apply ump_cones.
Qed.
