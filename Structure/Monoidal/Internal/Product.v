Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section InternalProduct.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

#[local] Ltac solveit :=
  unfold proj_left, proj_right;
  try split; intros; unfork; cat.

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Program Definition CC_Monoidal : @Monoidal C := {|
  tensor := InternalProductFunctor C;
  I := 1
|}.
Next Obligation.
  intros.
  simpl.
  rewrite <- !fork_comp.
  apply Cartesian.fork_respects.
  - rewrite id_left.
    rewrite exl_fork.
    cat.
    apply one_unique.
  - rewrite id_left.
    rewrite exr_fork_assoc.
    apply id_right.
Qed.
Next Obligation.
  intros. simpl.
  rewrite <- !fork_comp.
  apply Cartesian.fork_respects.
  - rewrite exl_fork_assoc.
    cat.
  - cat.
    apply one_unique.
Qed.
Next Obligation.
  (* Time Succeed solve [solveit]. *)
  intros. simpl.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite !exl_fork_assoc.
  apply Cartesian.fork_respects.
  { rewrite exl_fork_comp.
    apply comp_assoc_sym.
  }
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply Cartesian.fork_respects.
  - rewrite exr_fork_assoc.
    rewrite !exl_fork_assoc.
    rewrite !exr_fork_comp.
    apply comp_assoc.
  - rewrite !exr_fork_assoc.
    symmetry.
    apply exr_fork.
Qed.
Next Obligation.
  (* Time Succeed solve [solveit]. *)
  intros. simpl.
  do 5 rewrite <- fork_comp.
  repeat apply Cartesian.fork_respects.
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
  (* Time Succeed solve [solveit]. *)
  intros. simpl.
  rewrite <- fork_comp.
  apply Cartesian.fork_respects.
  - rewrite id_left.
    symmetry.
    apply exl_fork.
  - rewrite id_left.
    rewrite exr_fork_assoc.
    symmetry. apply exr_fork.
Qed.
Next Obligation.
  (* Time Succeed solve [solveit]. *)
  intros. simpl.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  apply Cartesian.fork_respects.
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
  apply Cartesian.fork_respects.
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
  apply Cartesian.fork_respects.
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
  @exl x y z w ∘ swap ≈ exr.
Proof. solveit. Qed.

Lemma exr_swap {x y z w} :
  @exr x y z w ∘ swap ≈ exl.
Proof. solveit. Qed.

Program Definition CC_BraidedMonoidal : @BraidedMonoidal C := {|
  braided_is_monoidal := CC_Monoidal;
  braid := @swap C _
|}.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  rewrite swap_fork.
  rewrite <- fork_comp.
  apply Cartesian.fork_respects.
  - rewrite <- comp_assoc.
    rewrite <- comp_assoc.
    rewrite <- comp_assoc.
    apply compose_respects; try reflexivity.
    rewrite exl_fork_comp.
    rewrite exr_fork.
    rewrite !id_left.
    apply exl_swap.
  - rewrite id_left.
    rewrite id_left.
    rewrite id_left.
    rewrite exr_fork.
    rewrite exl_fork.
    rewrite <- comp_assoc.
    apply compose_respects; try reflexivity.
    apply exr_swap.
Qed.
Next Obligation.
  (* Time Succeed solve [solveit]. *)
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply Cartesian.fork_respects.
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
  apply Cartesian.fork_respects.
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
Next Obligation.
  (* Time Succeed solve [solveit]. *)
  intros. simpl.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply Cartesian.fork_respects.
  { rewrite exl_fork_assoc.
    rewrite id_left.
    rewrite swap_fork.
    rewrite <- comp_assoc.
    rewrite swap_fork.
    symmetry.
    rewrite <- fork_comp.
    rewrite exl_fork.
    rewrite <- comp_assoc.
    rewrite exr_fork.
    rewrite exl_fork.
    rewrite <- fork_comp.
    rewrite <- comp_assoc.
    rewrite exr_fork.
    rewrite exl_fork.
    unfold swap.
    rewrite exl_fork_comp.
    reflexivity.
  }
  rewrite exr_fork_assoc.
  rewrite !id_left.
  rewrite <- comp_assoc.
  rewrite exr_fork.
  unfold swap.
  rewrite comp_assoc.
  rewrite exr_fork.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc exr (exr △ exl)).
  rewrite exr_fork.
  rewrite exl_fork.
  rewrite exr_fork.
  reflexivity.
Qed.

Program Definition CC_BalancedMonoidal : @BalancedMonoidal C := {|
  balanced_is_braided := CC_BraidedMonoidal;
  twist := fun x =>
    {| to   := id
     ; from := id
     ; iso_to_from := _
     ; iso_from_to := _
    |}
|}.

Definition CC_SymmetricMonoidal : @SymmetricMonoidal C := {|
  symmetric_is_balanced := CC_BalancedMonoidal;
  braid_invol := @swap_invol _ _
|}.

Program Definition CC_RelevanceMonoidal : @RelevanceMonoidal C := {|
  relevance_is_symmetric := CC_SymmetricMonoidal;
  diagonal  := fun o => Cartesian.fork id id
|}.
Next Obligation.
  cat_simpl.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply Cartesian.fork_respects.
  - rewrite exl_fork_assoc.
    cat.
  - rewrite exr_fork_assoc.
    cat.
Qed.
Next Obligation.
  cat_simpl. apply Cartesian.fork_respects; try reflexivity.
  apply one_unique.
Qed.
Next Obligation.
  (* Time Succeed solve [solveit]. *)
  simpl. intros.
  rewrite <- fork_comp.
  symmetry.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  rewrite !exl_fork_assoc.
  rewrite !exl_fork_comp.
  apply Cartesian.fork_respects.
  { cat. }
  rewrite exr_fork_assoc.
  rewrite id_right.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  apply Cartesian.fork_respects.
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
  apply Cartesian.fork_respects.
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
    apply Cartesian.fork_respects; try reflexivity.
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
    apply Cartesian.fork_respects.
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

Program Definition CC_SemicartesianMonoidal :
  @SemicartesianMonoidal C CC_Monoidal := {|
  eliminate := fun o => one[o]
|}.
Next Obligation.
  intros.
  apply one_unique.
Qed.

#[local] Obligation Tactic := program_simpl; solveit; auto.

Program Definition CC_CartesianMonoidal : @CartesianMonoidal C := {|
  cartesian_is_relevance     := CC_RelevanceMonoidal;
  cartesian_is_semicartesian := CC_SemicartesianMonoidal;
|}.

Context `{CL : @Closed C _}.

Program Definition CCC_ClosedMonoidal : @ClosedMonoidal C := {|
  closed_is_cartesian := CC_CartesianMonoidal;
  exponent_obj := λ x y, @fobj _ _ (@InternalHomFunctor C _ CL) (x, y);
  exp_iso := @Cartesian.Closed.exp_iso C _ _;
|}.
Next Obligation.
  exists (to (@Cartesian.Closed.exp_iso C _ _ x y z) f).
  - cat.
  - intros.
    rewrite X; clear X.
    rewrite id_left.
    pose proof (@Cartesian.Closed.eval_first C _ _ _ _ _ v).
    cbv in X.
    rewrite X.
    sapply (iso_to_from (@Cartesian.Closed.exp_iso C _ _ x y z)).
Qed.

End InternalProduct.
