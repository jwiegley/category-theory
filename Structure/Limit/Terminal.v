Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Universal.Arrow.
Require Export Category.Structure.Cone.
Require Export Category.Structure.Limit.
Require Export Category.Functor.Diagonal.
Require Export Category.Instance.Zero.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Theorem Terminal_Limit (C : Category) (F : 0 ⟶ C) :
  Limit F ↔ @Terminal C.
Proof.
  split; intros.
  - construct.
    + exact (vertex_obj[X]).
    + given (cone : Cone F). {
        unshelve (refine {| vertex_obj := x |}); intros.
          inversion x0.
        inversion x0.
      }
      destruct (@ump_limits _ _ _ X cone).
      apply unique_obj.
    + given (cone : Cone F). {
        unshelve (refine {| vertex_obj := x |}); intros.
          inversion x0.
        inversion x0.
      }
      destruct (@ump_limits _ _ _ X cone).
      pose proof (uniqueness f).
      pose proof (uniqueness g).
      rewrite <- X0, <- X1.
      * reflexivity.
      * intro x0; inversion x0.
      * intro x0; inversion x0.
  - construct.
    + construct.
      * exact terminal_obj.
      * inversion x.
      * inversion x.
    + simpl.
      unshelve eexists.
      * exact one.
      * intros.
        inversion x.
      * intros.
        apply one_unique.
Qed.
