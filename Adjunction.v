Require Import Lib.
Require Export Functor.
Require Export Iso.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Adjunction.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.

Class Adjunction := {
  adj_left  {a b} (f : F a ~{C}~> b) : a ~{D}~> U b;
  adj_right {a b} (f : a ~{D}~> U b) : F a ~{C}~> b;

  adj_left_respects  : ∀ X Y, Proper (@eqv _ (F X) Y ==> eqv) adj_left;
  adj_right_respects : ∀ X Y, Proper (@eqv _ X (U Y) ==> eqv) adj_right;

  unit   {a : D} : a ~> U (F a) := adj_left id;
  counit {a : C} : F (U a) ~> a := adj_right id;

  adj_left_right {a b} (f : a ~> U b) : adj_left (adj_right f) ≈ f;
  adj_right_left {a b} (f : F a ~> b) : adj_right (adj_left f) ≈ f;

  (* adj_left and adj_right must be natural in both arguments *)

  adj_left_nat_l {a b c} (f : F b ~> c) (g : a ~> b) :
    adj_left (f ∘ fmap[F] g) ≈ adj_left f ∘ g;
  adj_left_nat_r {a} {b} {c : C} (f : b ~> c) (g : F a ~> b) :
    adj_left (f ∘ g) ≈ fmap[U] f ∘ adj_left g;

  adj_right_nat_l {a b c} (f : b ~> U c) (g : a ~> b) :
    adj_right (f ∘ g) ≈ adj_right f ∘ fmap[F] g;
  adj_right_nat_r {a} {b} {c : C} (f : b ~> c) (g : a ~> U b) :
    adj_right (fmap[U] f ∘ g) ≈ f ∘ adj_right g
}.

Context `{@Adjunction}.

Global Program Instance parametric_morphism_adj_left a b :
  Proper (eqv ==> eqv) adj_left := adj_left_respects a b.

Global Program Instance parametric_morphism_adj_right a b :
  Proper (eqv ==> eqv) adj_right := adj_right_respects a b.

Corollary adj_left_unit  {a b} (f : F a ~> b) :
  adj_left f ≈ fmap f ∘ unit.
Proof.
  rewrite <- (id_right f).
  rewrite adj_left_nat_r.
  rewrite fmap_comp; cat.
Qed.

Corollary adj_right_counit {a b} (f : a ~> U b) :
  adj_right f ≈ counit ∘ fmap f.
Proof.
  rewrite <- (id_left f).
  rewrite adj_right_nat_l.
  rewrite fmap_comp; cat.
Qed.

Corollary counit_unit  {a} : counit ∘ fmap[F] unit ≈ @id C (F a).
Proof.
  unfold unit, counit.
  rewrite <- adj_right_nat_l.
  rewrite <- fmap_id.
  rewrite adj_right_nat_r; cat.
  apply adj_right_left.
Qed.

Corollary unit_counit  {a} : fmap[U] counit ∘ unit ≈ @id D (U a).
Proof.
  unfold unit, counit.
  rewrite <- adj_left_nat_r.
  rewrite <- (@fmap_id _ _ F).
  rewrite adj_left_nat_l; cat.
  apply adj_left_right.
Qed.

Corollary adj_right_unit {a} : adj_right unit ≈ @id C (F a).
Proof. apply adj_right_left. Qed.

Corollary adj_left_counit {a} : adj_left counit ≈ @id D (U a).
Proof. apply adj_left_right. Qed.

End Adjunction.

Arguments Adjunction {C D} F U.

Notation "F ⊣ G" := (@Adjunction _ _ F G) (at level 70) : category_scope.

Program Instance adj_identity `{C : Category} : Identity ⊣ Identity := {
  adj_left  := fun _ _ => _;
  adj_right := fun _ _ => _
}.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Program Definition adj_compose `{C : Category} `{D : Category} `{E : Category}
   (F : D ⟶ C) (U : C ⟶ D) (F' : E ⟶ D) (U' : D ⟶ E) (X : F ⊣ U) (Y : F' ⊣ U') :
  functor_comp F F' ⊣ functor_comp U' U := {|
  adj_left  := fun a b (f : F (F' a) ~> b) => adj_left (adj_left f);
  adj_right := fun a b (f : a ~> U' (U b)) => adj_right (adj_right f)
|}.
Next Obligation. intros ?? HA; rewrite HA; reflexivity. Defined.
Next Obligation. intros ?? HA; rewrite HA; reflexivity. Defined.
Next Obligation. rewrite adj_left_right, adj_left_right; reflexivity. Qed.
Next Obligation. rewrite adj_right_left, adj_right_left; reflexivity. Qed.
Next Obligation. rewrite <- !adj_left_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !adj_left_nat_r; reflexivity. Qed.
Next Obligation. rewrite <- !adj_right_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !adj_right_nat_r; reflexivity. Qed.

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

(*
jww (2017-04-13): TODO
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
  admit.
Admitted.
Obligation 4.
  destruct f.
Admitted.
Obligation 5.
  destruct f.
Admitted.
*)
