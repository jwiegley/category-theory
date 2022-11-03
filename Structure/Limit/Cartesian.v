Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Instance.Two.Discrete.

Generalizable All Variables.

Theorem Cartesian_Limit (C : Category) :
  (∀ F : Two_Discrete ⟶ C, Limit F) ↔ @Cartesian C.
Proof.
  split; intros.
  - construct.
    + exact (vertex_obj[X (Pick_Two X0 X1)]).
    + simpl.
      given (cone : Cone (Pick_Two y z)). { 
        unshelve (refine {| vertex_obj := x |}); intros.
        unshelve econstructor.
        - destruct x0; simpl; auto.
        - intros. destruct x0, y0; cat;
          pose proof (TwoDHom_inv _ _ f0) as H; inv H.
      }
      destruct (@ump_limits _ _ _ (X (Pick_Two y z)) cone).
      apply unique_obj.
    + simpl. 
      destruct (X (Pick_Two x y)).
      destruct limit_cone.
      simpl. change x with (fobj[Pick_Two x y] TwoDX).
      apply (@vertex_map _ _ Two_Discrete (Pick_Two x y) _ TwoDX).
    + simpl.
      destruct (X (Pick_Two x y)).
      destruct limit_cone.
      apply (@vertex_map _ _ Two_Discrete (Pick_Two x y) _ TwoDY).
    + proper.
      apply uniqueness; simpl; intros.
      destruct x2; simpl.
      * rewrite H.
        destruct (ump_limits _).
        apply (unique_property TwoDX).
      * rewrite H0.
        destruct (ump_limits _).
        apply (unique_property TwoDY).
    + simpl.
      destruct (ump_limits _); simpl in *.
      split; intros.
      * split.
        ** rewrite H.
           apply (unique_property TwoDX).
        ** rewrite H.
           apply (unique_property TwoDY).
      * destruct H.
        symmetry.
        apply uniqueness; intros.
        destruct x0; auto.
  - construct.
    + construct; [ exact (product_obj (fobj[F] TwoDX) (fobj[F] TwoDY)) | construct ].
      * destruct x.
        ** apply exl.
        ** apply exr.
      * simpl.
        destruct x, y;
        pose proof (TwoDHom_inv _ _ f) as H; inv H.
        ** now rewrite fmap_id, id_left.
        ** now rewrite fmap_id, id_left.
    + unshelve eexists.
      * apply fork; destruct N; apply vertex_map.
      * intros.
        destruct x; simpl.
        ** now rewrite exl_fork.
        ** now rewrite exr_fork.
      * intros.
        simpl in *.
        rewrite <- !H.
        rewrite fork_comp.
        rewrite fork_exl_exr.
        cat.
Qed.
