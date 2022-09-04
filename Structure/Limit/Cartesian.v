Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Limit.
Require Export Category.Structure.Cartesian.
Require Export Category.Instance.Two.Discrete.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Pick_Two {C : Category} (a b : C) :
  Two_Discrete ⟶ C := {|
  fobj := λ x,
    match x with
    | TwoDX => a
    | TwoDY => b
    end;
  fmap := λ x y _,
    match x, y with
    | TwoDX, TwoDX => id
    | TwoDY, TwoDY => id
    | _,    _      => !
    end
|}.
Next Obligation.
  destruct x, y; auto with two_laws.
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x; auto with two_laws; cat.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws; cat.
Qed.

Theorem Cartesian_Limit (C : Category) :
  (∀ F : Two_Discrete ⟶ C, Limit F) ↔ @Cartesian C.
Proof.
  split; intros.
  - construct.
    + exact (vertex_obj[X (Pick_Two X0 X1)]).
    + simpl.
      given (cone : Cone (Pick_Two y z)). {
        unshelve (refine {| vertex_obj := x |}); intros.
        - destruct x0; simpl; auto.
        - destruct x0, y0;
          dependent destruction f0; simpl; cat.
      }
      destruct (@ump_limits _ _ _ (X (Pick_Two y z)) cone).
      apply unique_obj.
    + simpl.
      destruct (X (Pick_Two x y)).
      destruct limit_cone.
      apply (vertex_map TwoDX).
    + simpl.
      destruct (X (Pick_Two x y)).
      destruct limit_cone.
      apply (vertex_map TwoDY).
    + proper.
      apply uniqueness; simpl; intros.
      destruct x2; simpl.
      * rewrite X0.
        destruct (ump_limits _).
        apply (unique_property TwoDX).
      * rewrite X1.
        destruct (ump_limits _).
        apply (unique_property TwoDY).
    + simpl.
      destruct (ump_limits _); simpl in *.
      split; intros.
      * split.
        ** rewrite X0.
           apply (unique_property TwoDX).
        ** rewrite X0.
           apply (unique_property TwoDY).
      * destruct X0.
        symmetry.
        apply uniqueness; intros.
        destruct x0; auto.
  - construct.
    + construct.
      * exact (product_obj (fobj[F] TwoDX) (fobj[F] TwoDY)).
      * destruct x.
        ** apply exl.
        ** apply exr.
      * simpl.
        destruct x, y;
        dependent destruction f.
        ** now rewrite fmap_id, id_left.
        ** now rewrite fmap_id, id_left.
    + unshelve eexists.
      * apply fork.
        ** apply vertex_map.
        ** apply vertex_map.
      * intros.
        destruct x; simpl.
        ** now rewrite exl_fork.
        ** now rewrite exr_fork.
      * intros.
        simpl in *.
        rewrite <- !X0.
        rewrite fork_comp.
        rewrite fork_exl_exr.
        cat.
Qed.
