Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Zero.

Generalizable All Variables.

Theorem Terminal_Limit (C : Category) (F : 0 ⟶ C) :
  Limit F ↔ @Terminal C.
Proof.
  split; intros.
  - construct.
    + exact (vertex_obj[X]).
    + given (cone : Cone F). {
        unshelve (refine {| vertex_obj := x |}); unshelve econstructor; intros.
        - inversion x0.
        - inversion x0.
      }
      destruct (@ump_limits _ _ _ X cone).
      apply unique_obj.
    + given (cone : Cone F). {
        unshelve (refine {| vertex_obj := x |}); unshelve econstructor; intros.
        - inversion x0.
        - inversion x0.
      }
      destruct (@ump_limits _ _ _ X cone).
      pose proof (uniqueness f).
      pose proof (uniqueness g).
      rewrite <- X0, <- X1.
      * reflexivity.
      * intro x0; inversion x0.
      * intro x0; inversion x0.
  - construct.
    + construct; [ | unshelve econstructor ].
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
