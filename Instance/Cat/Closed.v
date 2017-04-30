Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Closed.
Require Export Category.Instance.Nat.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Cat.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Definition pairing {A B : Type} (p : A * B) : p = (fst p, snd p) :=
  match p with (x, y) => eq_refl end.

Program Instance Cat_Closed : @Closed Cat Cat_Cartesian := {
  Exp := @Nat;
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
  proper.
  simplify equiv; intros.
  apply fmap_respects; cat.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- fmap_comp.
  apply fmap_respects; cat; simpl; cat.
Qed.
Next Obligation.
  proper.
  constructive; simpl.
  all:swap 2 3.
  - unshelve (refine {| transform := fun Y0 : B => _ (to X (X0, Y0)) |});
    simpl; intros.
      exact x0.
    apply natural_transformation.
  - unshelve (refine {| transform := fun Y0 : B => _ (from X (X0, Y0)) |});
    simpl; intros.
      exact x0.
    apply natural_transformation.
  - simplify equiv; intros.
    apply natural_transformation.
  - simplify equiv; intros.
    apply natural_transformation.
  - simplify equiv; intros.
    simplify equiv; intros.
    destruct X; simpl.
    simplify equiv in iso_to_from.
    apply iso_to_from.
  - simplify equiv; intros.
    simplify equiv; intros.
    destruct X; simpl.
    simplify equiv in iso_from_to.
    apply iso_from_to.
Qed.
Next Obligation.
  proper.
  rewrite b.
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
  simplify equiv in fmap_id.
  rewrite fmap_id.
  destruct (fobj o); simpl in *.
  apply fmap_id0.
Qed.
Next Obligation.
  simpl in *; cat.
  symmetry.
  rewrite natural_transformation.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[F o1] h2)).
  rewrite <- fmap_comp.
  rewrite natural_transformation.
  rewrite comp_assoc.
  destruct F; simpl in *.
  simplify equiv in fmap_comp.
  rewrite <- !fmap_comp.
  rewrite natural_transformation.
  reflexivity.
Qed.
Next Obligation.
  proper.
  constructive; simpl.
  all:swap 2 3.
  - apply X.
  - apply X.
  - destruct X0, Y, f; simpl in *.
    rewrite natural_transformation.
    rewrite <- comp_assoc.
    rewrite (@natural_transformation _ _ _ _ (to X o)).
    rewrite comp_assoc.
    rewrite natural_transformation.
    rewrite comp_assoc.
    apply compose_respects; cat.
    destruct (to X); simpl.
    specialize (natural_transformation _ _ h); simpl in *.
    apply natural_transformation.
  - destruct X0, Y, f; simpl in *.
    rewrite natural_transformation.
    rewrite <- comp_assoc.
    rewrite (@natural_transformation _ _ _ _ (from X o)).
    rewrite comp_assoc.
    rewrite natural_transformation.
    rewrite comp_assoc.
    apply compose_respects; cat.
    destruct (from X); simpl.
    specialize (natural_transformation _ _ h); simpl in *.
    apply natural_transformation.
  - simplify equiv; intros.
    destruct A0; simpl; cat.
    destruct X; simpl in *.
    simplify equiv in iso_to_from.
    simplify equiv in iso_to_from.
    apply iso_to_from.
  - simplify equiv; intros.
    destruct A0; simpl; cat.
    destruct X; simpl in *.
    simplify equiv in iso_from_to.
    simplify equiv in iso_from_to.
    apply iso_from_to.
Qed.
Next Obligation.
  simplify equiv; intros.
  constructive; simpl.
  all:swap 2 3.
  - unshelve (refine {| transform := fun Y0 : B => _ |});
    simpl; intros.
      apply (x X).
      apply id.
    simpl; cat.
    destruct x; simpl.
    simplify equiv in fmap_id.
    rewrite fmap_id; cat.
  - unshelve (refine {| transform := fun Y0 : B => _ |});
    simpl; intros.
      apply (x X).
      apply id.
    simpl; cat.
    destruct x; simpl.
    simplify equiv in fmap_id.
    rewrite fmap_id; cat.
  - simplify equiv; intros; cat.
  - simplify equiv; intros; cat.
  - simplify equiv; intros.
    simplify equiv; intros; cat.
    destruct x; simpl in *.
    simplify equiv in fmap_id.
    rewrite fmap_id; cat.
  - simplify equiv; intros.
    simplify equiv; intros; cat.
    destruct x; simpl in *.
    simplify equiv in fmap_id.
    rewrite fmap_id; cat.
Qed.
Next Obligation.
  simplify equiv; intros.
  constructive; simpl.
  all:swap 2 3.
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
  - simplify equiv; intros.
    destruct A0; simpl; cat.
  - simplify equiv; intros.
    destruct A0; simpl; cat.
Qed.
Next Obligation.
  simplify equiv.
  constructive; simpl.
  all:swap 2 3.
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
  - simplify equiv; intros.
    destruct A; simpl; cat.
  - simplify equiv; intros.
    destruct A; simpl; cat.
Qed.
