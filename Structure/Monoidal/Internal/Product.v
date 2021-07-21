Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

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

Local Obligation Tactic := unfold proj_left, proj_right.

Local Ltac fork_simpl :=
  match goal with
  | |- _ ∘ _ ∘ _ ≈ _ =>
    rewrite comp_assoc_sym
  | |- id{C} ∘ _ ≈ _ =>
    rewrite id_left
  | |- _ ∘ id{C} ≈ _ =>
    rewrite id_right
  | |- exl ∘ exl △ _ ≈ _ =>
    apply exl_fork
  | |- exl ∘ exr △ _ ≈ _ =>
    apply exl_fork
  | |- exl ∘ _ △ _ ≈ _ =>
    rewrite exl_fork
  | |- exr ∘ _ △ _ ≈ _ =>
    rewrite exr_fork
  | |- _ △ _ ∘ _ ≈ _ =>
    rewrite <- fork_comp
  | |- (exl △ exr) △ _ ≈ _ =>
    eapply transitivity;
      [apply fork_respects; [apply fork_exl_exr|reflexivity]|]
  | |- _ △ (exl △ exr) ≈ _ =>
    eapply transitivity;
      [apply fork_respects; [reflexivity|apply fork_exl_exr]|]
  | |- _ △ _ ≈ _ △ _ => apply fork_respects
  end.

Local Ltac solve_fork_split :=
  match goal with
  | |- exr ∘ _ ≈ _ =>
    eapply transitivity; [apply compose_respects; [reflexivity|]; repeat fork_simpl;
                          match goal with
                          | |- _ △ _ ≈ _ => reflexivity
                          | _ => idtac
                          end
                         |]; repeat fork_simpl; match goal with
                                                | |- _ △ _ ≈ _ => reflexivity
                                                | _ => idtac
                                                end
  | |- exl ∘ _ ≈ _ =>
    eapply transitivity; [apply compose_respects; [reflexivity|]; repeat fork_simpl;
                          match goal with
                          | |- _ △ _ ≈ _ => reflexivity
                          | _ => idtac
                          end
                         |]; repeat fork_simpl; match goal with
                                                | |- _ △ _ ≈ _ => reflexivity
                                                | _ => idtac
                                                end
  end.

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Program Definition InternalProduct_Monoidal : @Monoidal C := {|
  tensor := InternalProductFunctor C;
  I := 1
|}.
Next Obligation.
  cat_simpl.
Qed.
Next Obligation.
  cat_simpl.
  rewrite <- !fork_comp.
  repeat fork_simpl.
  { cat. }
  transitivity (g ∘ id{C}).
  2: { cat. }
  apply compose_respects; [reflexivity|].
  cat.
Qed.
Next Obligation.
  cat_simpl.
Qed.
Next Obligation.
  cat_simpl.
  rewrite <- !fork_comp.
  repeat fork_simpl.
  2: { cat. }
  transitivity (g ∘ id{C}).
  2: { cat. }
  apply compose_respects; [reflexivity|].
  cat.
Qed.
Next Obligation.
  cat_simpl.
  repeat fork_simpl.
  symmetry; repeat fork_simpl; symmetry; repeat fork_simpl.
  - symmetry.
    solve_fork_split.
    apply compose_respects; [reflexivity|].
    symmetry.
    repeat fork_simpl.
    reflexivity.
  - symmetry.
    repeat fork_simpl.
    solve_fork_split.
    apply compose_respects; [reflexivity|].
    symmetry.
    solve_fork_split.
    reflexivity.
  - symmetry.
    fork_simpl.
    apply compose_respects; [reflexivity|].
    symmetry.
    solve_fork_split.
    reflexivity.
Qed.
Next Obligation.
  cat_simpl.
  repeat fork_simpl; symmetry; repeat fork_simpl; symmetry; repeat fork_simpl; symmetry; repeat fork_simpl.
  - apply compose_respects; [reflexivity|].
    symmetry.
    solve_fork_split.
  - solve_fork_split.
    apply compose_respects; [reflexivity|].
    symmetry.
    solve_fork_split.
    reflexivity.
  - solve_fork_split.
    apply compose_respects; [reflexivity|].
    symmetry.
    fork_simpl.
    reflexivity.
Qed.
Next Obligation.
  intros. simpl.
  symmetry; repeat fork_simpl.
  { reflexivity. }
  solve_fork_split.
  cat.
Qed.
Next Obligation.
  intros; simpl.
  repeat fork_simpl.
  symmetry. repeat fork_simpl.
  - solve_fork_split; [reflexivity|].
    symmetry.
    repeat fork_simpl.
    solve_fork_split.
    solve_fork_split.
    reflexivity.
  - symmetry. repeat fork_simpl.
    + symmetry. repeat fork_simpl.
      solve_fork_split; [reflexivity|].
      symmetry.
      solve_fork_split.
      { solve_fork_split.
        { solve_fork_split. }
        repeat fork_simpl.
        solve_fork_split.
      }
      repeat fork_simpl.
      reflexivity.
    + symmetry. repeat fork_simpl.
      * symmetry. repeat fork_simpl.
        solve_fork_split.
        { solve_fork_split.
          { solve_fork_split. }
          repeat fork_simpl.
          solve_fork_split.
        }
        repeat fork_simpl.
        reflexivity.
      * symmetry.
        solve_fork_split.
        { solve_fork_split. }
        repeat fork_simpl.
        reflexivity.
Qed.

Program Definition InternalProduct_SymmetricMonoidal :
  @SymmetricMonoidal C InternalProduct_Monoidal := {|
  twist := fun x y =>
    {| to   := @swap C _ x y
     ; from := @swap C _ y x
     ; iso_to_from := swap_invol
     ; iso_from_to := swap_invol
    |}
|}.
Next Obligation.
  unfold swap.
  simpl. split; intros.
  - repeat fork_simpl.
    symmetry. repeat fork_simpl.
    + solve_fork_split.
      rewrite comp_assoc_sym.
      apply compose_respects; [reflexivity|].
      repeat fork_simpl.
      symmetry.
      solve_fork_split.
    + solve_fork_split.
      symmetry.
      repeat fork_simpl.
      solve_fork_split.
      apply compose_respects; [reflexivity|].
      fork_simpl.
      reflexivity.
  - repeat fork_simpl.
    symmetry. repeat fork_simpl.
    + solve_fork_split.
      symmetry.
      repeat fork_simpl.
      solve_fork_split.
      apply compose_respects; [reflexivity|].
      fork_simpl.
    + solve_fork_split.
      rewrite comp_assoc_sym.
      apply compose_respects; [reflexivity|].
      solve_fork_split.
      symmetry.
      solve_fork_split.
      reflexivity.
Qed.
Next Obligation.
  simpl. intros. apply swap_invol.
Defined.
Next Obligation.
  simpl. unfold swap. intros.
  repeat fork_simpl. symmetry. repeat fork_simpl.
  - solve_fork_split.
    solve_fork_split.
    symmetry.
    repeat fork_simpl.
    solve_fork_split.
    { solve_fork_split. }
    repeat fork_simpl.
    reflexivity.
  - symmetry. repeat fork_simpl.
    + solve_fork_split.
      { solve_fork_split. }
      repeat fork_simpl.
      symmetry.
      solve_fork_split.
      { solve_fork_split. }
      repeat fork_simpl.
      reflexivity.
    + solve_fork_split.
      symmetry.
      solve_fork_split.
      { solve_fork_split. }
      solve_fork_split.
      solve_fork_split.
      reflexivity.
Qed.

Program Definition InternalProduct_CartesianMonoidal :
  @CartesianMonoidal C InternalProduct_Monoidal := {|
  is_semicartesian := {| eliminate := fun _ => one |};
  is_relevance := {| diagonal  := fun _ => id △ id |}
|}.
Next Obligation.
  cat_simpl.
Qed.
Next Obligation.
  apply InternalProduct_SymmetricMonoidal.
Defined.
Next Obligation.
  cat_simpl.
  repeat fork_simpl.
  symmetry. repeat fork_simpl.
  all: symmetry; repeat fork_simpl.
  all: transitivity (g ∘ id{C}); [|cat].
  all: apply compose_respects; [reflexivity|].
  all: cat.
Qed.
Next Obligation.
  apply fork_respects.
    apply one_unique.
  reflexivity.
Qed.
Next Obligation.
  intros. simpl.
  repeat fork_simpl.
  symmetry. repeat fork_simpl.
  - solve_fork_split.
    { solve_fork_split. }
    repeat fork_simpl.
    symmetry.
    repeat fork_simpl.
    reflexivity.
  - symmetry. repeat fork_simpl; symmetry; repeat fork_simpl.
    all: solve_fork_split.
    3: reflexivity.
    { solve_fork_split. }
    solve_fork_split.
    reflexivity.
Qed.
Next Obligation.
  simpl. unfold swap.
  intros.
  repeat fork_simpl; reflexivity.
Qed.

Next Obligation.
  intros. simpl. unfold swap. symmetry.
  eapply transitivity.
  2: {
    apply fork_respects; apply fork_exl_exr.
  }
  repeat fork_simpl.
  - repeat solve_fork_split.
    reflexivity.
  - repeat solve_fork_split.
    all: reflexivity.
  - repeat solve_fork_split.
    all: reflexivity.
Qed.
Next Obligation.
  intros. simpl.
  repeat fork_simpl.
  solve_fork_split.
  reflexivity.
Qed.
Next Obligation.
  intros. simpl.
  repeat fork_simpl.
  solve_fork_split.
  reflexivity.
Qed.
Next Obligation.
  intros. simpl. unfold swap.
  fork_simpl.
  reflexivity.
Qed.
Next Obligation.
  intros. simpl. unfold swap.
  fork_simpl.
Qed.

End InternalProduct.
