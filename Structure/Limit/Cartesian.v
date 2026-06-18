Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Instance.Two.Discrete.

Generalizable All Variables.

(** * Binary products as limits of a discrete two-object diagram *)

(* nLab:      https://ncatlab.org/nlab/show/product
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   A binary product is the limit of a diagram of shape [Two_Discrete], the
   discrete category with two objects and only identity morphisms (see
   [Instance/Two/Discrete.v]). A functor F : Two_Discrete ⟶ C picks out an
   ordered pair of objects (F TwoDX, F TwoDY); a cone over F is an apex with
   two legs into those objects, and the limit cone is exactly the product
   F TwoDX × F TwoDY with its projections exl, exr as legs. The terminal-cone
   universal property of the limit coincides with the product UMP
   ([ump_products] in [Structure/Cartesian.v]); the empty discrete diagram
   gives the nullary product, the terminal object (see [Structure/Limit/
   Terminal.v]).

   This theorem records the equivalence in both directions: C has a limit for
   every two-object discrete diagram iff C is cartesian (has all binary
   products).

       (∀ F : Two_Discrete ⟶ C, Limit F)  ↔  Cartesian C

   Left to right: a chosen pair of objects is presented as [Pick_Two x y], the
   limit's apex becomes the product object, and the limit legs become exl/exr;
   the limit's mediating morphism becomes the pairing [fork]. Right to left:
   the product object is the cone apex and exl/exr are its legs, with [fork]
   supplying the unique factorization. *)

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
      apply vertex_map.
    + simpl.
      destruct (X (Pick_Two x y)).
      destruct limit_cone.
      simpl. change y with (fobj[Pick_Two x y] TwoDY).
      apply vertex_map.
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
