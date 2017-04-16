Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Isomorphism.

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
  adj_iso  {a b} : F a ~{C}~> b ≃ a ~{D}~> U b;

  adj_left'  {X Y} := to (@adj_iso X Y);
  adj_right' {X Y} := from (@adj_iso X Y);

  (* adj_left and adj_right must be natural in both arguments *)

  adj_left_nat_l' {a b c} (f : F b ~> c) (g : a ~> b) :
    adj_left' _ _ (f ∘ fmap[F] g) ≈ adj_left' _ _ f ∘ g;
  adj_left_nat_r' {a} {b} {c : C} (f : b ~> c) (g : F a ~> b) :
    adj_left' _ _ (f ∘ g) ≈ fmap[U] f ∘ adj_left' _ _ g;

  adj_right_nat_l' {a b c} (f : b ~> U c) (g : a ~> b) :
    adj_right' _ _ (f ∘ g) ≈ adj_right' _ _ f ∘ fmap[F] g;
  adj_right_nat_r' {a} {b} {c : C} (f : b ~> c) (g : a ~> U b) :
    adj_right' _ _ (fmap[U] f ∘ g) ≈ f ∘ adj_right' _ _ g
}.

Context `{@Adjunction}.

Definition adj_left  {X Y} := @adj_left' _ X Y.
Definition adj_right {X Y} := @adj_right' _ X Y.
Arguments adj_left' {_ _ _} /.
Arguments adj_right' {_ _ _} /.

Definition adj_left_nat_l {a b c} (f : F b ~> c) (g : a ~> b) :
  adj_left (f ∘ fmap[F] g) ≈ adj_left f ∘ g := @adj_left_nat_l' _ a b c f g.
Definition adj_left_nat_r {a} {b} {c : C} (f : b ~> c) (g : F a ~> b) :
  adj_left (f ∘ g) ≈ fmap[U] f ∘ adj_left g := @adj_left_nat_r' _ a b c f g.

Definition adj_right_nat_l {a b c} (f : b ~> U c) (g : a ~> b) :
  adj_right (f ∘ g) ≈ adj_right f ∘ fmap[F] g := @adj_right_nat_l' _ a b c f g.
Definition adj_right_nat_r {a} {b} {c : C} (f : b ~> c) (g : a ~> U b) :
  adj_right (fmap[U] f ∘ g) ≈ f ∘ adj_right g := @adj_right_nat_r' _ a b c f g.

Definition unit   {a : D} : a ~> U (F a) := adj_left id.
Definition counit {a : C} : F (U a) ~> a := adj_right id.

Corollary adj_left_right {a b} (f : a ~> U b) : adj_left (adj_right f) ≈ f.
Proof.
  unfold adj_left, adj_right; simpl.
  apply (iso_to_from adj_iso).
Qed.

Definition adj_right_left {a b} (f : F a ~> b) : adj_right (adj_left f) ≈ f.
Proof.
  unfold adj_left, adj_right; simpl.
  apply (iso_from_to adj_iso).
Qed.

Global Program Instance parametric_morphism_adj_left a b :
  Proper (equiv ==> equiv) (@adj_left a b).
Next Obligation.
  intros ?? HA.
  unfold adj_left; simpl in *.
  destruct adj_iso; simpl in *.
  destruct to; simpl in *.
  rewrite HA; reflexivity.
Defined.

Global Program Instance parametric_morphism_adj_right a b :
  Proper (equiv ==> equiv) (@adj_right a b).
Next Obligation.
  intros ?? HA.
  unfold adj_right; simpl in *.
  destruct adj_iso; simpl in *.
  destruct from; simpl in *.
  rewrite HA; reflexivity.
Defined.

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
  adj_iso := fun _ _ =>
    {| to   := {| morphism := _ |}
     ; from := {| morphism := _ |} |}
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
  adj_iso := fun a b =>
    {| to   := {| morphism := fun (f : F (F' a) ~> b) => adj_left (adj_left f) |}
     ; from := {| morphism := fun (f : a ~> U' (U b)) => adj_right (adj_right f) |} |}
|}.
Next Obligation. intros ?? HA; rewrite HA; reflexivity. Defined.
Next Obligation. intros ?? HA; rewrite HA; reflexivity. Defined.
Next Obligation.
  unfold Basics.compose.
  rewrite adj_left_right, adj_left_right; reflexivity.
Qed.
Next Obligation.
  unfold Basics.compose.
  rewrite adj_right_left, adj_right_left; reflexivity.
Qed.
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
*)
