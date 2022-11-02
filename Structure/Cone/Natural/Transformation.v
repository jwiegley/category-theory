Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(* A natural transformation Δd ⟹ F (where Δd is the Constant functor on d) is
   the same as a cone over F (whose vertex is d). *)

Monomorphic Theorem Cone_Transform `(F : J ⟶ C) (d : C) :
  Δ[J](d) ⟹ F ↔ { c : Cone F | vertex_obj = d }.
Proof. 
  split; intros.
  - unshelve eexists.
    + unshelve econstructor; intros; [ exact d | unshelve econstructor ].
      * apply X.
      * abstract(simpl; intros;
        rewrite (naturality[X]); cat).
    + reflexivity.
  - transform; simpl; intros;
    destruct X; subst.
    + apply x0.
    + cat; apply cone_coherence.
    + cat; symmetry; apply cone_coherence.
Defined.
