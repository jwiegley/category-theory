Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/cone
   Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

   A cone over a diagram F : J ⟶ C with apex d is the same data as a natural
   transformation Δ[J](d) ⟹ F out of the constant (diagonal) functor at d:
   the components of the transformation are the legs of the cone, and the
   naturality squares are the cone's commuting triangles (Wikipedia: "ψ is a
   cone from N to F" iff "ψ is a natural transformation from Δ(N) to F"). This
   is the equivalence (a) ↔ (b) of that article; (c), the comma-category form
   (Δ ↓ F), is treated separately.

   [Cone_Transform] restates this as Δ[J](d) ⟹ F ↔ { c : Cone F | vertex_obj =
   d }: a cone bundled with its apex pinned to d. The apex is matched by object
   equality (=) rather than ≈, since it identifies objects (not morphisms).
   Structure/Cone/Const.v proves the same equivalence in the unbundled form
   Δ[J](N) ⟹ F ↔ Cone[N] F (a bare leg family with apex N). *)

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
