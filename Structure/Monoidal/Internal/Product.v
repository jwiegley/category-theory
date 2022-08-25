Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Import Category.Functor.Product.Internal.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Symmetric.
Require Export Category.Structure.Monoidal.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section InternalProduct.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

#[local] Ltac solveit :=
  unfold proj_left, proj_right;
  try split; intros; unfork; cat.

#[local] Obligation Tactic := idtac.

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Program Definition InternalProduct_Monoidal : @Monoidal C := {|
  tensor := InternalProductFunctor C;
  I := 1
|}.
Next Obligation.
  (* now solveit. Undo. *)
  intros.
  symmetry.
  apply exr_fork.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros.
  simpl.
  rewrite <- !fork_comp.
  apply fork_respects.
  - rewrite id_left.
    rewrite exl_fork.
    cat.
  - rewrite id_left.
    rewrite exr_fork_assoc.
    apply id_right.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. simpl.
  symmetry.
  apply exl_fork.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. simpl.
  rewrite <- !fork_comp.
  apply fork_respects.
  - rewrite exl_fork_assoc.
    cat.
  - cat.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. simpl.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite !exl_fork_assoc.
  apply fork_respects.
  { rewrite exl_fork_comp.
    apply comp_assoc_sym.
  }
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply fork_respects.
  - rewrite exr_fork_assoc.
    rewrite !exl_fork_assoc.
    rewrite !exr_fork_comp.
    apply comp_assoc.
  - rewrite !exr_fork_assoc.
    symmetry.
    apply exr_fork.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. simpl.
  do 5 rewrite <- fork_comp.
  repeat apply fork_respects.
  - rewrite !exl_fork_assoc.
    symmetry.
    apply exl_fork.
  - rewrite !exl_fork_assoc.
    rewrite !exr_fork_assoc.
    rewrite exl_fork_comp.
    apply comp_assoc.
  - rewrite !exr_fork_assoc.
    rewrite !exr_fork_comp.
    apply comp_assoc.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. simpl.
  rewrite <- fork_comp.
  apply fork_respects.
  - rewrite id_left.
    symmetry.
    apply exl_fork.
  - rewrite id_left.
    rewrite exr_fork_assoc.
    symmetry. apply exr_fork.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. simpl.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  apply fork_respects.
  { rewrite id_left.
    rewrite exl_fork_assoc.
    rewrite exl_fork.
    rewrite exl_fork_assoc.
    rewrite exl_fork_comp.
    apply comp_assoc.
  }
  rewrite exr_fork_assoc.
  do 3 rewrite <- fork_comp.
  rewrite exl_fork_assoc.
  rewrite exl_fork_assoc.
  apply fork_respects.
  { symmetry.
    etransitivity.
    { rewrite <- comp_assoc.
      apply compose_respects; [reflexivity|].
      rewrite exl_fork_assoc.
      apply exr_fork_comp.
    }
    rewrite exl_fork_comp.
    apply comp_assoc_sym.
  }
  rewrite exr_fork.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply fork_respects.
  { rewrite exl_fork_assoc.
    symmetry.
    etransitivity.
    { rewrite <- comp_assoc.
      apply compose_respects; [reflexivity|].
      rewrite exl_fork_assoc.
      apply exr_fork_comp.
    }
    apply exr_fork_comp.
  }
  symmetry.
  rewrite exr_fork.
  rewrite exr_fork.
  apply id_left.
Qed.

Lemma exl_swap {x y z w} :
  (@exl x y z w) ∘ swap ≈ exr.
Proof.
  (* now solveit. Undo. *)
  unfork. cat.
Qed.

Lemma exr_swap {x y z w} :
  (@exr x y z w) ∘ swap ≈ exl.
Proof.
  (* now solveit. Undo. *)
  unfork. cat.
Qed.

Program Definition InternalProduct_BraidedMonoidal :
  @BraidedMonoidal C InternalProduct_Monoidal := {|
  braid := fun x y =>
    {| to   := @swap C _ x y
     ; from := @swap C _ y x
     ; iso_to_from := swap_invol
     ; iso_from_to := swap_invol
    |}
|}.
Next Obligation.
  simpl; split; intros.
  - rewrite <- fork_comp.
    rewrite <- fork_comp.
    rewrite swap_fork.
    rewrite <- fork_comp.
    apply fork_respects.
    + rewrite <- comp_assoc.
      rewrite <- comp_assoc.
      rewrite <- comp_assoc.
      apply compose_respects; try reflexivity.
      rewrite exl_fork_comp.
      rewrite exr_fork.
      rewrite !id_left.
      apply exl_swap.
    + rewrite id_left.
      rewrite id_left.
      rewrite id_left.
      rewrite exr_fork.
      rewrite exl_fork.
      rewrite <- comp_assoc.
      apply compose_respects; try reflexivity.
      apply exr_swap.
  - rewrite <- fork_comp.
    rewrite <- fork_comp.
    rewrite swap_fork.
    rewrite <- fork_comp.
    apply fork_respects.
    + rewrite id_left.
      rewrite exl_fork.
      rewrite id_left.
      rewrite exr_fork.
      rewrite <- comp_assoc.
      apply compose_respects; try reflexivity.
      apply exl_swap.
    + rewrite <- comp_assoc.
      rewrite <- comp_assoc.
      rewrite <- comp_assoc.
      apply compose_respects; try reflexivity.
      rewrite exr_fork_comp.
      rewrite exl_fork.
      rewrite !id_left.
      apply exr_swap.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. simpl.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply fork_respects.
  { rewrite exl_fork_assoc.
    rewrite id_left.
    rewrite exl_fork_assoc.
    symmetry.
    rewrite <- comp_assoc.
    rewrite swap_fork.
    rewrite exl_fork_assoc.
    rewrite exl_fork.
    unfold swap.
    rewrite exl_fork_comp.
    reflexivity.
  }
  rewrite exr_fork_assoc.
  rewrite swap_fork.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply fork_respects.
  - rewrite exr_fork.
    rewrite id_left.
    rewrite swap_fork.
    rewrite exl_fork_assoc.
    rewrite exr_fork.
    reflexivity.
  - rewrite exl_fork_assoc.
    rewrite comp_assoc.
    rewrite exr_swap.
    etransitivity.
    2: {
      apply compose_respects; [reflexivity|].
      symmetry.
      apply swap_fork.
    }
    symmetry.
    apply exr_fork.
Qed.

Definition InternalProduct_SymmetricMonoidal :
  @SymmetricMonoidal C InternalProduct_Monoidal := {|
  symmetric_is_braided := InternalProduct_BraidedMonoidal;
  braid_invol := @swap_invol _ _
|}.

Program Definition InternalProduct_CartesianMonoidal :
  @CartesianMonoidal C InternalProduct_Monoidal := {|
  cartesian_is_semicartesian := {| eliminate := fun _ => one |};
  cartesian_is_relevant := {| diagonal  := fun _ => id △ id |}
|}.
Next Obligation.
  (* now solveit. Undo. *)
  cat_simpl.
Qed.
Next Obligation.
  exact InternalProduct_SymmetricMonoidal.
Defined.
Next Obligation.
  cat_simpl.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply fork_respects.
  - rewrite exl_fork_assoc.
    cat.
  - rewrite exr_fork_assoc.
    cat.
Qed.
Next Obligation.
  cat_simpl. apply fork_respects; try reflexivity.
  apply one_unique.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  simpl. intros.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  rewrite !exl_fork_assoc.
  rewrite !exl_fork_comp.
  apply fork_respects.
  { cat. }
  rewrite exr_fork_assoc.
  rewrite id_right.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply fork_respects.
  - rewrite exl_fork_assoc.
    rewrite exr_fork_comp.
    cat_simpl.
  - rewrite exr_fork.
    cat_simpl.
Qed.
Next Obligation.
  intros. simpl.
  rewrite swap_fork.
  reflexivity.
Qed.
Next Obligation.
  intros. simpl.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply fork_respects.
  - rewrite <- fork_comp.
    rewrite exl_fork.
    rewrite id_left.
    rewrite <- fork_comp.
    rewrite <- fork_comp.
    rewrite exl_fork.
    rewrite exl_fork_assoc.
    rewrite exl_fork_comp.
    rewrite id_left.
    rewrite <- fork_exl_exr.
    apply fork_respects; try reflexivity.
    rewrite exr_fork_assoc.
    rewrite comp_assoc.
    rewrite comp_assoc.
    rewrite comp_assoc.
    rewrite exl_fork.
    rewrite exl_fork_assoc.
    rewrite comp_assoc.
    rewrite exl_swap.
    rewrite exl_fork_assoc.
    rewrite exr_fork.
    rewrite !exr_fork_assoc.
    rewrite exl_fork_comp.
    cat_simpl.
  - rewrite exr_fork_assoc.
    rewrite comp_assoc.
    rewrite comp_assoc.
    rewrite comp_assoc.
    rewrite exr_fork.
    rewrite <- fork_comp.
    rewrite exl_fork_assoc.
    rewrite comp_assoc.
    rewrite exr_swap.
    rewrite <- fork_comp.
    rewrite exl_fork_assoc.
    rewrite exl_fork.
    rewrite <- fork_comp.
    rewrite <- fork_comp.
    rewrite <- fork_comp.
    rewrite <- fork_exl_exr.
    apply fork_respects.
    + rewrite exr_fork_assoc.
      rewrite exl_fork.
      rewrite exl_fork_assoc.
      rewrite exr_fork_comp.
      cat_simpl.
    + rewrite exr_fork.
      rewrite id_left.
      rewrite exr_fork.
      rewrite !exr_fork_assoc.
      rewrite exr_fork_comp.
      cat_simpl.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. simpl.
  unfold proj_left.
  simpl.
  rewrite exl_fork.
  rewrite exl_fork_assoc.
  cat_simpl.
Qed.
Next Obligation.
  (* now solveit. Undo. *)
  intros. unfold proj_right. simpl.
  rewrite exr_fork.
  rewrite exr_fork_assoc.
  cat_simpl.
Qed.
Next Obligation.
  intros. simpl.
  apply exr_swap.
Qed.
Next Obligation.
  intros. simpl.
  apply exl_swap.
Qed.

End InternalProduct.
