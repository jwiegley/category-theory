Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Adjunction.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.

Class Adjunction := {
  adj_iso  {a b} : F a ~{C}~> b ≊ a ~{D}~> U b;

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
  pose proof (iso_to_from (@adj_iso H a b)) as HA.
  simpl in HA.
  apply HA.
Qed.

Definition adj_right_left {a b} (f : F a ~> b) : adj_right (adj_left f) ≈ f.
Proof.
  unfold adj_left, adj_right; simpl.
  pose proof (iso_from_to (@adj_iso H a b)) as HA.
  simpl in HA.
  apply HA.
Qed.

Global Program Instance parametric_morphism_adj_left a b :
  Proper (equiv ==> equiv) (@adj_left a b).
Next Obligation.
  intros ?? HA.
  unfold adj_left; simpl in *.
  destruct adj_iso; simpl in *.
  destruct to; simpl in *.
  rewrite HA; reflexivity.
Qed.

Global Program Instance parametric_morphism_adj_right a b :
  Proper (equiv ==> equiv) (@adj_right a b).
Next Obligation.
  intros ?? HA.
  unfold adj_right; simpl in *.
  destruct adj_iso; simpl in *.
  destruct from; simpl in *.
  rewrite HA; reflexivity.
Qed.

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

Program Instance adj_id `{C : Category} : Identity ⊣ Identity := {
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

Program Definition adj_comp
        `{C : Category} `{D : Category} `{E : Category}
        (F : D ⟶ C) (U : C ⟶ D) (F' : E ⟶ D) (U' : D ⟶ E)
        (X : F ⊣ U) (Y : F' ⊣ U') :
  F ○ F' ⊣ U' ○ U := {|
  adj_iso := fun a b =>
    {| to   := {| morphism := fun (f : F (F' a) ~> b) => adj_left (adj_left f) |}
     ; from := {| morphism := fun (f : a ~> U' (U b)) => adj_right (adj_right f) |} |}
|}.
Next Obligation. intros ?? HA; rewrite HA; reflexivity. Qed.
Next Obligation. intros ?? HA; rewrite HA; reflexivity. Qed.
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

Notation "F ⊚ G" := (@adj_comp _ _ _ _ _ _ _ F G)
  (at level 30, right associativity) : category_scope.

Record adj_morphism `{C : Category} `{D : Category} := {
  free_functor : D ⟶ C;
  forgetful_functor : C ⟶ D;
  adjunction : free_functor ⊣ forgetful_functor
}.

Program Instance adj_morphism_setoid `{C : Category} `{D : Category} :
  Setoid (@adj_morphism C D) := {
  equiv := fun f g =>
             free_functor f ≈ free_functor g ∧
             forgetful_functor f ≈ forgetful_functor g
}.
Next Obligation.
  pose proof (@functor_equiv_equivalence C D) as HA.
  pose proof (@functor_equiv_equivalence D C) as HB.
  constructor; split; auto.
  - reflexivity.
  - reflexivity.
  - destruct H; symmetry; assumption.
  - destruct H; symmetry; assumption.
  - destruct H, H0; transitivity (free_functor y); assumption.
  - destruct H, H0;
    transitivity (forgetful_functor y); assumption.
Qed.

Program Instance Adj : Category := {
  ob := Category;
  hom := @adj_morphism;
  id := fun X =>
          {| free_functor      := @Identity X
           ; forgetful_functor := @Identity X |};
  compose := fun A B C f g =>
    {| adjunction :=
             @adj_comp A B C (free_functor g) (forgetful_functor g)
                       (free_functor f) (forgetful_functor f)
                       (adjunction g) (adjunction f) |}
}.
Next Obligation.
  repeat intros ?? [f f0] HA HB [f1 f2].
  apply adj_morphism_setoid.
  destruct HA, HB; split;
  unfold functor_equiv in *; simpl in *; intros;
  destruct x, y; simpl in *; intro X0; simpl.
    specialize (f1 (free_functor2 X0)).
    symmetry.
    etransitivity.
      apply f1.
    eapply fobj_respects.
    apply f.
  specialize (f0 (forgetful_functor0 X0)).
  symmetry.
  etransitivity.
    apply f0.
  eapply fobj_respects.
  apply f2.
  Unshelve.
  - apply (free_functor2 X0).
  - apply (forgetful_functor0 X0).
Qed.
Next Obligation.
  destruct f.
  unfold functor_equiv; simpl; split; intros;
  reflexivity.
Qed.
Next Obligation.
  destruct f.
  unfold functor_equiv; simpl; split; intros;
  reflexivity.
Qed.
Next Obligation.
  destruct f, g, h.
  unfold functor_equiv; simpl; split; intros;
  reflexivity.
Qed.
