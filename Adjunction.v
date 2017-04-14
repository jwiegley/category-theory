Require Import Lib.
Require Export Functor.
Require Export Iso.

Section Adjunction.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.

Class Adjunction := {
  unit   {a : D} : a ~> U (F a);
  counit {a : C} : F (U a) ~> a;

  leftAdjunct  {a b} (f : F a ~> b) : a ~> U b := fmap f ∘ unit;
  rightAdjunct {a b} (f : a ~> U b) : F a ~> b := counit ∘ fmap f;

  adj_left_right {a b} (f : a ~> U b) : leftAdjunct (rightAdjunct f) ≈ f;
  adj_right_left {a b} (f : F a ~> b) : rightAdjunct (leftAdjunct f) ≈ f
}.

End Adjunction.

Arguments Adjunction {C D} F U.

Notation "F ⊣ G" := (@Adjunction _ _ F G) (at level 70) : category_scope.

Program Instance adj_identity `{C : Category} : Identity ⊣ Identity := {
  unit := fun _ => id;
  counit := fun _ => id
}.
Obligation 1. cat. Qed.
Obligation 2. cat. Qed.

Program Definition adj_compose `{C : Category} `{D : Category} `{E : Category}
   (F : D ⟶ C) (U : C ⟶ D) (F' : E ⟶ D) (U' : D ⟶ E) (X : F ⊣ U) (Y : F' ⊣ U')
   : functor_comp F' F ⊣ functor_comp U U' :=
  {| unit   := fun _ => fmap unit ∘ unit
   ; counit := fun _ => counit ∘ fmap counit |}.
Obligation 1.
  pose proof (adj_left_right (counit ∘ fmap f)) as Hadj.
  unfold leftAdjunct, rightAdjunct in Hadj.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite Hadj.
  apply adj_left_right.
Qed.
Obligation 2.
  pose proof (adj_right_left (fmap f ∘ unit)) as Hadj.
  unfold leftAdjunct, rightAdjunct in Hadj.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite Hadj.
  apply adj_right_left.
Qed.

Record Adj_Morphism `{C : Category} `{D : Category} := {
  free_functor : D ⟶ C;
  forgetful_functor : C ⟶ D;
  adjunction : free_functor ⊣ forgetful_functor
}.

(* jww (2017-04-13): Define adjoint equivalence. *)
(*
Lemma adj_id_left `{C : Category} `{D : Category} `(F : D ⟶ C) `(U : C ⟶ D) :
  adj_compose Id Id F U adj_identity (F ⊣ U) = F ⊣ U.
Proof.
  destruct F.
  unfold functor_comp.
  simpl.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Qed.

Lemma adj_id_right `(F : @Functor C D) : functor_comp F Id = F.
Proof.
  destruct F.
  unfold functor_comp.
  simpl.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Qed.
*)

Program Instance Adj : Category := {
  ob := Category;
  hom := @Adj_Morphism
}.
Obligation 1.
  apply {| free_functor      := Identity
         ; forgetful_functor := Identity |}.
Defined.
Obligation 2.
  destruct f, g.
  apply {| adjunction := adj_compose _ _ _ _ _ _ |}.
Defined.
Obligation 3.
  destruct f.
Admitted.
Obligation 4.
  destruct f.
Admitted.
Obligation 5.
  destruct f.
Admitted.
