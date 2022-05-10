Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Structure.Cartesian.Closed.
Require Export Category.Instance.Fun.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Cat.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Definition pairing {A B : Type} (p : A * B) : p = (fst p, snd p) :=
  match p with (x, y) => eq_refl end.

#[global] Program Instance Cat_Closed : @Closed Cat Cat_Cartesian := {
  exponent_obj := @Fun;         (* the internal hom is a functor category *)
  exp_iso := fun A B C =>
    {| to :=
       {| morphism := fun F : A × B ⟶ C =>
          {| fobj := fun x : A =>
             {| fobj := fun y : B => F (x, y)
              ; fmap := fun J K (f : J ~{B}~> K) =>
                  fmap[F] (@id A x, f) |}
           ; fmap := fun J K (f : J ~{A}~> K) =>
             {| transform := fun L : B =>
                  fmap[F] (f, @id B L) |} |} |}
     ; from :=
       {| morphism := fun F : A ⟶ [B, C] =>
          {| fobj := fun x : A × B => F (fst x) (snd x)
           ; fmap := fun J K (f : J ~{A × B}~> K) =>
               fmap (snd f) ∘ transform[fmap[F] (fst f)] _ |} |} |}
}.
Next Obligation.
  proper; apply fmap_respects.
  split; simpl; cat.
Qed.
Next Obligation.
  rewrite <- fmap_comp; simpl.
  apply fmap_respects; split; simpl; cat.
Qed.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects; simpl; cat; simpl; cat.
Qed.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects; simpl; cat.
Qed.
Next Obligation.
  proper; simpl; cat;
  rewrites; reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- fmap_comp.
  apply fmap_respects; cat; simpl; cat.
Qed.
Next Obligation.
  proper.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * apply x0.
      * simpl.
        rewrite e.
        rewrite !comp_assoc.
        rewrite iso_to_from; cat.
      * simpl.
        rewrite e.
        rewrite !comp_assoc.
        rewrite iso_to_from; cat.
    + transform; simpl; intros.
      * apply x0.
      * simpl.
        rewrite e.
        rewrite <- !comp_assoc.
        rewrite iso_to_from; cat.
      * simpl.
        rewrite e.
        rewrite <- !comp_assoc.
        rewrite iso_to_from; cat.
    + simpl; cat; apply iso_to_from.
    + simpl; cat; apply iso_from_to.
  - apply e.
Qed.
Next Obligation.
  proper.
  rewrite H.
  comp_left.
  destruct F; simpl in *.
  apply fmap_respects.
  assumption.
Qed.
Next Obligation.
  simpl; cat.
  destruct F; simpl in *.
  rewrite fmap_id; cat.
Qed.
Next Obligation.
  symmetry.
  rewrite naturality.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[F o1] h2)).
  rewrite <- fmap_comp.
  rewrite naturality.
  rewrite comp_assoc.
  destruct F; simpl in *.
  rewrite <- !fmap_comp.
  rewrite naturality.
  reflexivity.
Qed.
Next Obligation.
  proper; simpl.
  - isomorphism.
    + apply x0.
    + apply (from (x0 _)).
    + srewrite (iso_to_from (x0 x1)); cat.
    + srewrite (iso_from_to (x0 x1)); cat.
  - simpl.
    rewrite e.
    do 2 comp_right.
    apply naturality.
Qed.
Next Obligation.
  constructive; simpl.
  - transform; simpl; intros.
    + exact id.
    + destruct x; simpl in *.
      rewrite fmap_id; cat.
    + destruct x; simpl in *.
      rewrite fmap_id; cat.
  - transform; simpl; intros.
    + exact id.
    + destruct x; simpl in *.
      rewrite fmap_id; cat.
    + destruct x; simpl in *.
      rewrite fmap_id; cat.
  - simpl; cat.
  - destruct x; simpl in *.
    rewrite fmap_id; cat.
  - destruct x; simpl in *; cat.
Qed.
Next Obligation.
  constructive; simpl.
  - rewrite <- pairing.
    exact id.
  - rewrite <- pairing.
    exact id.
  - destruct x0; simpl; cat.
  - destruct x0; simpl; cat.
  - destruct f; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; simpl; cat.
Qed.
Next Obligation.
  constructive; simpl.
  - rewrite <- pairing.
    exact id.
  - rewrite <- pairing.
    exact id.
  - destruct x; simpl; cat.
  - destruct x; simpl; cat.
  - destruct f; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; simpl; cat.
Qed.
