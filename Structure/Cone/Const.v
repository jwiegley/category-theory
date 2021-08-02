Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Comma.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(**

At first glance cones seem to be slightly abnormal constructions in category
theory. They are maps from an object to a functor (or vice versa). In keeping
with the spirit of category theory we would like to define them as morphisms
or objects in some suitable category. In fact, we can do both.

Let J be a small category and let Cᴶ be the category of diagrams of type J in
C (this is nothing more than a functor category). Define the diagonal functor
Δ : C → Cᴶ as follows: Δ(N) : J → C is the constant functor to N for all N in
C.

If F is a diagram of type J in C, the following statements are equivalent:

  - ψ is a cone from N to F
  - ψ is a natural transformation from Δ(N) to F
  - (N, ψ) is an object in the comma category (Δ ↓ F)

The dual statements are also equivalent:

  - ψ is a co-cone from F to N
  - ψ is a natural transformation from F to Δ(N)
  - (N, ψ) is an object in the comma category (F ↓ Δ)

These statements can all be verified by a straightforward application of the
definitions. Thinking of cones as natural transformations we see that they are
just morphisms in Cᴶ with source (or target) a constant functor.

*)

Lemma Cone_Natural_Transform `(F : [J, C]) :
  ∀ N : C, Diagonal J N ⟹ F ↔ { ψ : Cone F | vertex_obj[ψ] = N }.
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

(** jww (2021-08-02): This should be J, not 1. *)
Lemma Cone_Comma `(F : [1, C]) :
  ∀ N : C, Diagonal 1 N ↓ F ↔ { ψ : Cone F | vertex_obj[ψ] = N }.
Proof.
  split; simpl.
  - intros [[? ?] f].
    simplify; simpl in *.
    unshelve refine (exist _ (Build_Cone _ _ _ _ _ _) eq_refl);
    simpl in *; intros.
    + destruct x.
      exact f.
    + now cat.
  - intros [X H].
    destruct X.
    simpl in *; subst.
    exists (tt, tt).
    now apply vertex_map.
Qed.
