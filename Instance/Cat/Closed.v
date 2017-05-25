Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Closed.
Require Export Category.Instance.Fun.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Cat.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Definition pairing {A B : Type} (p : A * B) : p = (fst p, snd p) :=
  match p with (x, y) => eq_refl end.

Program Instance Cat_Closed : @Closed Cat Cat_Cartesian := {
  Exp := @Fun;                  (* the internal hom is a functor category *)
  exp_iso := fun A B C =>
    {| to :=
       {| morphism := fun F : A × B ⟶ C =>
          {| fobj := fun X : A =>
             {| fobj := fun Y : B => F (X, Y)
              ; fmap := fun J K (f : J ~{B}~> K) =>
                  fmap[F] (@id A X, f) |}
           ; fmap := fun J K (f : J ~{A}~> K) =>
             {| transform := fun L : B =>
                  fmap[F] (f, @id B L)
                    : F (J, L) ~{C}~> F (K, L) |} |} |}
     ; from :=
       {| morphism := fun F : A ⟶ [B, C] =>
          {| fobj := fun X : A × B => F (fst X) (snd X)
           ; fmap := fun J K (f : J ~{A × B}~> K) =>
               fmap[F (fst K)] (snd f) ∘ transform[fmap[F] (fst f)] _
                 : F (fst J) (snd J) ~{C}~> F (fst K) (snd K) |} |} |}
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
  proper.
  simpl; cat.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- fmap_comp.
  apply fmap_respects; cat; simpl; cat.
Qed.
Next Obligation.
  proper.
  constructive; simpl; intros.
  all:swap 2 4.
  - unshelve (refine {| transform := fun Y0 : B =>
                          _ (transform[to X] (X0, Y0)) |});
    simpl; intros.
    + exact x0.
    + apply naturality.
    + symmetry; apply naturality.
  - unshelve (refine {| transform := fun Y0 : B =>
                          _ (transform[from X] (X0, Y0)) |});
    simpl; intros.
    + exact x0.
    + apply naturality.
    + symmetry; apply naturality.
  - simpl; symmetry; apply naturality.
  - simpl; apply naturality.
  - simpl; apply naturality.
  - simpl; symmetry; apply naturality.
  - destruct X; simpl in *.
    apply iso_to_from.
  - destruct X; simpl in *.
    apply iso_from_to.
Qed.
Next Obligation.
  proper.
  rewrite y0.
  apply compose_respects.
    apply fmap_respects.
    reflexivity.
  destruct F; simpl in *.
  apply fmap_respects.
  assumption.
Qed.
Next Obligation.
  simpl; cat.
  destruct F; simpl in *.
  rewrite fmap_id.
  destruct (fobj o); simpl in *.
  apply fmap_id0.
Qed.
Next Obligation.
  simpl in *; cat.
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
  proper.
  constructive; simpl.
  all:swap 2 4.
  - apply X.
  - apply X.
  - destruct X0, Y, f; simpl in *.
    rewrite naturality.
    rewrite <- comp_assoc.
    rewrite <- naturality.
    rewrite comp_assoc.
    rewrite <- naturality.
    rewrite comp_assoc.
    comp_left.
    destruct (to X); simpl in *.
    apply naturality_sym.
  - destruct X0, Y, f; simpl in *.
    rewrite naturality.
    rewrite <- comp_assoc.
    rewrite naturality.
    rewrite comp_assoc.
    rewrite naturality.
    rewrite comp_assoc.
    apply compose_respects; cat.
    destruct (to X); simpl in *.
    apply naturality.
  - destruct X0, Y, f; simpl in *.
    rewrite naturality.
    rewrite <- comp_assoc.
    rewrite naturality.
    rewrite comp_assoc.
    rewrite naturality.
    rewrite comp_assoc.
    apply compose_respects; cat.
    destruct (from X); simpl in *.
    apply naturality.
  - destruct X0, Y, f; simpl in *.
    rewrite naturality.
    rewrite <- comp_assoc.
    rewrite <- naturality.
    rewrite comp_assoc.
    rewrite <- naturality.
    rewrite comp_assoc.
    comp_left.
    destruct (from X); simpl in *.
    apply naturality_sym.
  - destruct A0; simpl; cat.
    destruct X; simpl in *.
    apply iso_to_from.
  - destruct A0; simpl; cat.
    destruct X; simpl in *.
    apply iso_from_to.
Qed.
Next Obligation.
  constructive; simpl.
  all:swap 2 4.
  - transform; simpl; intros.
    + apply (x X), id.
    + simpl; cat.
      destruct x; simpl in *.
      rewrite fmap_id; cat.
    + simpl; cat.
      destruct x; simpl in *.
      rewrite fmap_id; cat.
  - transform; simpl; intros.
    + apply (x X), id.
    + simpl; cat.
      destruct x; simpl in *.
      rewrite fmap_id; cat.
    + simpl; cat.
      destruct x; simpl in *.
      rewrite fmap_id; cat.
  - simpl; cat.
  - simpl; cat.
  - simpl; cat.
  - simpl; cat.
  - simpl; cat.
    destruct x; simpl in *.
    rewrite fmap_id; cat.
  - simpl; cat.
    destruct x; simpl in *.
    rewrite fmap_id; cat.
Qed.
Next Obligation.
  constructive; simpl.
  all:swap 2 4.
  - rewrite <- pairing.
    exact id.
  - rewrite <- pairing.
    exact id.
  - destruct X, Y, f; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; cat; simpl; cat.
  - destruct X, Y, f; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; cat; simpl; cat.
  - destruct X, Y, f; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; cat; simpl; cat.
  - destruct X, Y, f; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; cat; simpl; cat.
  - destruct A0; simpl; cat.
  - destruct A0; simpl; cat.
Qed.
Next Obligation.
  constructive; simpl.
  all:swap 2 4.
  - rewrite <- pairing.
    exact id.
  - rewrite <- pairing.
    exact id.
  - destruct X0, Y0, f0; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; cat; simpl; cat.
  - destruct X0, Y0, f0; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; cat; simpl; cat.
  - destruct X0, Y0, f0; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; cat; simpl; cat.
  - destruct X0, Y0, f0; simpl; cat.
    rewrite <- fmap_comp.
    apply fmap_respects; cat; simpl; cat.
  - destruct A; simpl; cat.
  - destruct A; simpl; cat.
Qed.
