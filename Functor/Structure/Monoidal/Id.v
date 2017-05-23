Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Structure.Monoidal.
Require Export Category.Functor.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section MonoidalFunctors.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {G : C ⟶ D}.

Context {E : Category}.
Context `{@Monoidal E}.
Context {F : D ⟶ E}.

Local Obligation Tactic := program_simpl.

Global Program Instance Id_MonoidalFunctor :
  @MonoidalFunctor C C _ _ Id[C] := {
  pure_iso := id_iso;
  ap_functor_iso := {| to   := {| transform := fun _ => _ |}
                     ; from := {| transform := fun _ => _ |} |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation.
  simpl; intros.
  destruct H1; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. apply tensor_assoc. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

Global Program Instance Id_LaxMonoidalFunctor :
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
Next Obligation. apply tensor_assoc. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

End MonoidalFunctors.
