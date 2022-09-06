Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section MonoidalFunctors.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {G : C ⟶ D}.

Context {E : Category}.
Context `{@Monoidal E}.
Context {F : D ⟶ E}.

#[local] Obligation Tactic := program_simpl.

#[global] Program Instance Id_MonoidalFunctor :
  @MonoidalFunctor C C _ _ Id[C] := {
  pure_iso := iso_id;
  ap_functor_iso := {| to   := {| transform := fun _ => _ |}
                     ; from := {| transform := fun _ => _ |} |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation.
  simpl; intros.
  destruct H1; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. apply tensor_assoc. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

#[global] Program Instance Id_LaxMonoidalFunctor :
  @LaxMonoidalFunctor C C _ _ Id[C] := {
  lax_pure := id;
  ap_functor_nat := {| transform := fun _ => _ |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. apply tensor_assoc. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

End MonoidalFunctors.
