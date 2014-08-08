Require Export Hask.Category.
Require Export Hask.Functors.

Open Scope type_scope.

Generalizable All Variables.

Record Pullback (C : Category) (Z : C) {X Y} (f : X ~> Z) (g : Y ~> Z) :=
{ pullback_obj : C
; pullback_fst : pullback_obj ~> X
; pullback_snd : pullback_obj ~> Y
; pullback_ump_1 : f ∘ pullback_fst = g ∘ pullback_snd
; pullback_ump_2 : ∀ {Q} (q1 : Q ~> X) (q2 : Q ~> Y),
    {    u : Q ~> pullback_obj & pullback_snd ∘ u = q2 ∧ pullback_fst ∘ u = q1
    ∧ ∀ (v : Q ~> pullback_obj), pullback_snd ∘ v = q2 ∧ pullback_fst ∘ v = q1 → v = u }
}.

Class HasTerminal (C : Category) :=
{ term_obj     : C
; term_mor     : forall {X}, X ~> term_obj
; terminal_law : forall {X} (f g : X ~> term_obj), f = g
}.

Record Product {C : Category} {X Y} :=
{ pobj : C
; fst : pobj ~> X
; snd : pobj ~> Y
; product_ump : ∀ {Q} (q1 : Q ~> X) (q2 : Q ~> Y),
    {    u : Q ~> pobj & snd ∘ u = q2 ∧ fst ∘ u = q1
    ∧ ∀ (v : Q ~> pobj), snd ∘ v = q2 ∧ fst ∘ v = q1 → v = u }
}.

Section EpisMonos.

  Context `{C : Category}.
  Variable X Y : C.
  Variable f : X ~{C}~> Y.

  Definition Epic       := ∀ {Z} (g1 g2 : Y ~> Z), g1 ∘ f = g2 ∘ f → g1 = g2.
  Definition Monic      := ∀ {Z} (g1 g2 : Z ~> X), f ∘ g1 = f ∘ g2 → g1 = g2.
  Definition Bimorphic  := Epic ∧ Monic.
  Definition Section'   := { g : Y ~> X & g ∘ f = id }.
  Definition Retraction := { g : Y ~> X & f ∘ g = id }.

  Lemma retractions_are_epic : Retraction → Epic.
  Proof.
    intros.
    unfold Epic.
    unfold Retraction in X0.
    intros.
    destruct X0.
    rewrite <- right_identity.
    symmetry.
    rewrite <- right_identity.
    rewrite <- e.
    rewrite comp_assoc.
    rewrite comp_assoc.
    f_equal.
    auto.
  Qed.

  Definition SplitEpi := Retraction.

  Lemma sections_are_monic : Section' → Monic.
  Proof.
    intros.
    unfold Monic.
    unfold Section' in X0.
    intros.
    destruct X0.
    rewrite <- left_identity.
    symmetry.
    rewrite <- left_identity.
    rewrite <- e.
    rewrite <- comp_assoc.
    rewrite <- comp_assoc.
    f_equal.
    auto.
  Qed.

  Definition SplitMono := Section'.

  Definition Isomorphism :=
    { s : Section' & { r : Retraction & projT1 s = projT1 r } }.

  Lemma monic_retractions_are_iso : Retraction → Monic → Isomorphism.
  Proof.
    intros.
    unfold Isomorphism.
    unfold Monic in H.
    unfold Retraction in X0.
    destruct X0.
    unfold Section'.
    unfold Retraction.
    assert {g : Y ~{ C }~> X & g ∘ f = id}.
      exists x. specialize (H X (x ∘ f) id).
      rewrite H. reflexivity.
      rewrite comp_assoc.
      rewrite e.
      rewrite left_identity.
      rewrite right_identity.
      reflexivity.
    exists X0.
    assert {g : Y ~{ C }~> X & f ∘ g = id}.
      exists x. assumption.
    exists X1.
    destruct X0.
    destruct X1.
    simpl.
    specialize (H X (x0 ∘ f) (x1 ∘ f)).
    rewrite <- right_identity.
    rewrite <- e1.
    rewrite comp_assoc.
    rewrite <- H.
    rewrite <- comp_assoc.
    rewrite e1.
    auto.
    symmetry.
    rewrite comp_assoc.
    rewrite e0.
    rewrite e1.
    rewrite left_identity.
    rewrite right_identity.
    reflexivity.
  Qed.

  Lemma epic_sections_are_iso : Epic → Section' → Isomorphism.
  Proof.
    unfold Epic.
    unfold Section'.
    unfold Isomorphism.
    intros.
    unfold Section'.
    unfold Retraction.
    destruct X0.
    assert {g : Y ~{ C }~> X & g ∘ f = id/ X}.
      exists x. assumption.
    exists X0.
    assert {g : Y ~{ C }~> X & f ∘ g = id/ Y}.
      exists x. specialize (H Y (f ∘ x) id).
      rewrite H. reflexivity.
      rewrite <- comp_assoc.
      rewrite e.
      rewrite left_identity.
      rewrite right_identity.
      reflexivity.
    exists X1.
    destruct X0.
    destruct X1.
    simpl.
    specialize (H Y (f ∘ x0) (f ∘ x1)).
    rewrite <- left_identity.
    rewrite <- e0.
    rewrite <- comp_assoc.
    rewrite e1.
    auto.
  Qed.

End EpisMonos.

Definition flip_section (C : Category) `(f : X ~> Y)
  (s : @Section' C X Y f) : @Retraction C Y X (projT1 s).
Proof.
  unfold Retraction.
  unfold Section' in s.
  destruct s.
  exists f.
  simpl.
  assumption.
Defined.

Definition flip_retraction (C : Category) `(f : X ~> Y)
  (s : @Retraction C X Y f) : @Section' C Y X (projT1 s).
Proof.
  unfold Section'.
  unfold Retraction in s.
  destruct s.
  exists f.
  simpl.
  assumption.
Defined.

Definition flip_iso (C : Category) `(f : X ~> Y)
  (i : @Isomorphism C X Y f) : @Isomorphism C Y X (projT1 (projT1 i)).
Proof.
  unfold Isomorphism in *.
  unfold Section' in *.
  unfold Retraction in *.
  destruct i. simpl.
  destruct x. simpl.
  destruct s.
  destruct x0. simpl in e0.
  subst.
  assert {g : X ~{ C }~> Y & g ∘ x0 = id} as H.
    exists f. assumption.
  exists H.
  assert {g : X ~{ C }~> Y & x0 ∘ g = id} as H1.
    exists f. assumption.
  exists H1.
  destruct H.
  destruct H1.
  simpl.
  rewrite <- left_identity.
  rewrite <- e0.
  rewrite <- comp_assoc.
  rewrite e2.
  rewrite right_identity.
  reflexivity.
Defined.

Lemma injectivity_is_monic `(f : X ~> Y)
  : (∀ x y, f x = f y → x = y) ↔ @Monic Sets X Y f.
Proof. split.
- intros.
  unfold Monic.
  intros.
  extensionality e.
  apply H.
  simpl in H0.
  apply (equal_f H0).
- intros.
  unfold Monic in H.
  pose (fun (_ : unit) => x) as const_x.
  pose (fun (_ : unit) => y) as const_y.
  specialize (H unit const_x const_y).
  unfold const_x in H.
  unfold const_y in H.
  simpl in H.
  apply equal_f in H.
  + assumption.
  + extensionality e. assumption.
  + constructor.
Qed.

Lemma existence_exists :
  ∀ {A} (a : A) (P : A → Prop), P a → (∃ y : A, P y) = P a.
Proof.
  intros.
  assert (forall P Q : Prop, P <-> Q -> P = Q).
    intros. destruct H0. admit.
  apply H0.
  split; intros; auto.
  exists a.
  assumption.
Qed.

Lemma surjectivity_is_epic `(f : X ~> Y)
  : (∀ y, ∃ x, f x = y) ↔ @Epic Sets X Y f.
Proof. split.
- intros.
  unfold Epic.
  intros.
  simpl in H0.
  extensionality e.
  specialize (H e).
  destruct H.
  rewrite <- H.
  apply (equal_f H0).
- intros.
  unfold Epic in H.
  specialize H with (Z := Prop).
  specialize H with (g1 := fun y0 => ∃ x0, f x0 = y0).
  simpl in *.
  specialize H with (g2 := fun y  => y = y).
  eapply equal_f in H.
  erewrite H. constructor.
  extensionality e.
  rewrite (existence_exists e).
  reflexivity.
  reflexivity.
Qed.

Lemma id_iso : ∀ (C : Category) (X : C), @Isomorphism C X X id.
Proof.
  intros.
  unfold Isomorphism, Section', Retraction.
  pose (@id C X).
  assert {g : X ~{ C }~> X & g ∘ id = id} as H.
    exists h. auto.
  exists H.
  assert {g : X ~{ C }~> X & id ∘ g = id} as J.
    exists h. auto.
  exists J.
  simpl.
  destruct H.
  destruct J.
  simpl.
  rewrite right_identity in e.
  rewrite left_identity in e0.
  rewrite e.
  rewrite e0.
  reflexivity.
Qed.

(* Definition Uniqueness `(f : X ~> Y), *)

(* Notation "X ≅ Y" := (Isomorphism X Y) (at level 50) : type_scope. *)
(* Notation "x ≡ y" := (to x = y /\ from y = x) (at level 50). *)

Lemma uniqueness_of_products (C : Category) : ∀ {X Y} (p q : @Product C X Y),
  let    ump1 := product_ump q (fst p) (snd p)
  in let ump2 := product_ump p (fst q) (snd q)
  in projT1 ump1 ∘ projT1 ump2 = id ∧ projT1 ump2 ∘ projT1 ump1 = id.
Proof.
  intros.
  split.
    destruct ump1.
    destruct ump2.
    simpl.
    destruct a.
    destruct H0.
    destruct a0.
    destruct H3.
    pose id_iso.
    unfold Isomorphism in i.
Abort.

(*
(* Tuples in the Sets category satisfy the UMP for products.
*)
Program Instance Pair {X Y : Set}
  : Product Sets (X * Y) (@fst X Y) (@snd X Y).
Obligation 1. (* product ump *)
  exists (fun x => (x1 x, x2 x)).
  intros. constructor.
    intros. unfold fst. reflexivity.
  split.
    intros. unfold snd. reflexivity.
  intros.
  inversion H.
  extensionality e.
  rewrite <- H0.
  rewrite <- H1.
  destruct (v e).
  reflexivity.
Defined.

Definition Tuple_map {Z X Y} (f : X → Y) (p : Z * X) : Z * Y :=
  match p with
  | pair z x => @pair Z Y z (f x)
  end.

Program Instance Tuple_Functor {Z} : Sets ⟶ Sets :=
{ fobj := fun X => Z * X
; fmap := @Tuple_map Z
}.
Obligation 1. extensionality e. crush. Defined.
Obligation 2. extensionality e. crush. Defined.
*)