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

  Definition Epic :=
    ∀ {Z} (g1 g2 : Y ~> Z), g1 ∘ f = g2 ∘ f → g1 = g2.

  Definition Monic :=
    ∀ {Z} (g1 g2 : Z ~> X), f ∘ g1 = f ∘ g2 → g1 = g2.

  Definition Bimorphic := Epic ∧ Monic.

  Definition Section' := { g : Y ~> X & g ∘ f = id }.

  Definition Retraction := { g : Y ~> X & f ∘ g = id }.

  Lemma retraction_epic : Retraction → Epic.
  Proof.
    intros.
    unfold Epic.
    intros.
    unfold Retraction in X0.
    destruct X0.
  Admitted.

  Lemma section_monic : Section' → Monic.
  Admitted.

  Definition Isomorphism :=
    { s : Section' & ∃ r : Retraction, projT1 s = projT1 r }.

  Lemma retraction_monic_iso :
    Retraction → Monic → Isomorphism.
  Admitted.

  Lemma epic_section_iso :
    Epic → Section' → Isomorphism.
  Admitted.

End EpisMonos.

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

(* Notation "X ≅ Y" := (Isomorphism X Y) (at level 50) : type_scope. *)
(* Notation "x ≡ y" := (to x = y /\ from y = x) (at level 50). *)

Lemma uniqueness_of_products (C : Category) :
  ∀ {X Y} (p q : @Product C X Y),
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
    specialize (H1 x).
    specialize (H4 x0).
    intuition.
    (* rewrite <- H0 in H2. *)
    (* rewrite <- comp_assoc in H2. *)
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