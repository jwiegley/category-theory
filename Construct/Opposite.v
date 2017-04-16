Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Reserved Notation "C ^op" (at level 90).

Program Instance Opposite `(C : Category) : Category := {
  ob      := @ob C;
  hom     := fun x y => @hom C y x;
  id      := @id C;
  compose := fun _ _ _ f g => g ∘ f
}.
Obligation 1.
  intros ?? HA ?? HB.
  rewrite HA, HB; reflexivity.
Defined.
Obligation 2. cat. Defined.
Obligation 3. cat. Defined.
Obligation 4. rewrite comp_assoc; reflexivity. Defined.

Notation "C ^op" := (@Opposite C)
  (at level 90, format "C ^op") : category_scope.

Open Scope equiv_scope.

Lemma op_involutive `{C : Category} : (C^op)^op = C.
Proof.
  unfold Opposite; simpl.
  destruct C; simpl.
  unfold Opposite_obligation_1; simpl.
  unfold Opposite_obligation_2; simpl.
  unfold Opposite_obligation_3; simpl.
  unfold Opposite_obligation_4; simpl.
  f_equal.
  extensionality X.
  extensionality Y.
  extensionality Z.
  extensionality x.
  extensionality y.
  extensionality HA.
  extensionality x0.
  extensionality y0.
  extensionality HB.
  compute.
  (* jww (2017-04-13): Need to define equivalence of categories. *)
Abort.

Definition op `{C : Category} : ∀ {X Y : C},
  (X ~{C^op}~> Y) → (Y ~{C}~> X).
Proof. intros; assumption. Defined.

Definition unop `{C : Category} : ∀ {X Y : C},
  (Y ~{C}~> X) → (X ~{C^op}~> Y).
Proof. auto. Defined.

Program Instance Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op := {
    fobj := @fobj C D F;
    fmap := fun X Y f => @fmap C D F Y X (op f)
}.
Next Obligation.
  repeat intro.
  apply fmap_respects.
  unfold op.
  assumption.
Defined.
Next Obligation. unfold op; apply fmap_id. Qed.
Next Obligation. unfold op; apply fmap_comp. Qed.

Program Instance Reverse_Opposite_Functor `(F : C^op ⟶ D^op) : C ⟶ D := {
    fobj := @fobj _ _ F;
    fmap := fun X Y f => unop (@fmap _ _ F Y X f)
}.
Next Obligation.
  repeat intro; unfold unop.
  rewrite X0; reflexivity.
Defined.
Next Obligation.
  unfold unop.
  unfold fmap. simpl.
  pose (@fmap_id _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e X). auto.
Defined.
Next Obligation.
  unfold unop.
  unfold fmap. simpl.
  pose (@fmap_comp _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e Z Y X g f).
  auto.
Defined.

Lemma op_functor_involutive `(F : Functor) :
  Reverse_Opposite_Functor (Opposite_Functor F) ≈ F.
Proof.
  unfold Reverse_Opposite_Functor.
  unfold Opposite_Functor.
  destruct F; simpl;
  unfold functor_equiv; simpl; intros.
  reflexivity.
Defined.
