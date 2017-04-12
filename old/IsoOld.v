Require Import CT.Category.
Require Import CT.Functor.

Generalizable All Variables.

Definition isomorphic `{C : Category} (X Y : C) : Prop :=
  exists (f : X ~> Y), exists (g : Y ~> X),
      f ∘ g ≈ id /\ g ∘ f ≈ id.

Notation "X ≅ Y" := (isomorphic X Y) (at level 50) : cat_scope.

Program Instance Iso_Equivalence `{Category} : Equivalence isomorphic.
Obligation 1.
  intro x.
  exists id.
  exists id.
  rewrite left_id.
  firstorder.
Qed.
Obligation 2.
  firstorder.
Qed.
Obligation 3.
  intros x y z H1 H2.
  firstorder.
  exists (x1 ∘ x0).
  exists (x2 ∘ x3).
  rewrite comp_assoc.
  assert ((x1 ∘ x0) ∘ x2 ≈ x1 ∘ (x0 ∘ x2)).
    rewrite comp_assoc.
    reflexivity.
  assert ((x2 ∘ x3) ∘ x1 ≈ x2 ∘ (x3 ∘ x1)).
    rewrite comp_assoc.
    reflexivity.
  rewrite H4, H0, right_id.
  rewrite comp_assoc.
  rewrite H5, H3, right_id.
  firstorder.
Qed.

Add Parametric Relation `{C : Category} {A B : C} : (@ob C) isomorphic
  reflexivity proved by (@Equivalence_Reflexive _ _ Iso_Equivalence)
  symmetry proved by (@Equivalence_Symmetric _ _ Iso_Equivalence)
  transitivity proved by (@Equivalence_Transitive _ _ Iso_Equivalence)
  as Isomorphic_relation.

Inductive Identity (A : Type) := Id : A -> Identity A.

Definition runId `(x : Identity A) : A := match x with Id x => x end.

Require Import FunctionalExtensionality.

Lemma identity_iso : forall (A : Type), Identity A ≅ A.
Proof.
  intro A.
  unfold isomorphic; simpl.
  exists (@runId A).
  exists (Id A).
  unfold runId; simpl.
  firstorder.
  extensionality x.
  destruct x; trivial.
Qed.

Definition Codensity m a := forall (r : Type), (a -> m r) -> m r.

Axiom Codensity_parametricity :
  forall `(f : A -> B) `(x : Codensity m A)
         (fmap : forall A B, (A -> B) -> m A -> m B)
         (pure : forall A, A -> m A),
  fmap _ _ f (x A (pure A)) = x B (fun x => pure _ (f x)).

Lemma codensity_id_iso : forall A, Codensity Identity A ≅ Identity A.
Proof.
  intro A.
  unfold Codensity, isomorphic; simpl.
  exists (fun (k : (∀ r : Type, (A → Identity r) → Identity r)) => k A (Id A)).
  exists (fun x r k => k (runId x)).
  unfold runId; simpl.
  split.
    extensionality x.
    destruct x; trivial.
  extensionality x.
  extensionality r.
  extensionality k.
  pose proof (@Codensity_parametricity A r (fun x => runId (k x)) Identity x
                (fun _ _ f x => match x with Id x => Id _ (f x) end) Id).
  unfold runId in *.
  replace (λ x0 : A, Id r match k x0 with
                          | Id x1 => x1
                          end)
    with k in H.
    rewrite <- H.
    destruct (x A (Id A)); trivial.
  extensionality x0.
  destruct (k x0); trivial.
Qed.
