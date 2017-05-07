Set Warnings "-notation-overridden".

(* jww (2017-04-13): TODO
Program Definition Lim_Sets `(J : Category) : [J, Sets] ⟶ Sets := {|
    fobj := fun F =>
    fmap := fun _ _ n F_x z => (transport/n) (F_x z)
|}.

Lemma distribute_forall : ∀ a {X} P, (a → ∀ (x : X), P x) → (∀ x, a → P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

Lemma forall_distribute : ∀ a {X} P, (∀ x, a → P x) → (a → ∀ (x : X), P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

Program Definition Sets_Const_Nat (J : Category) (F : [J, Sets])
  (a : Type) (f : a → ∀ x : J, F x) : @Const Sets J a ⟾ F.
Obligation 2.
  extensionality e.
  unfold Sets_Const_Nat_obligation_1.
  remember (f e) as j.
  destruct F. simpl. clear.
  destruct J.
  crush. clear.
  (* jww (2014-08-12): We don't believe this is true. *)

Program Instance Sets_Const_Lim_Iso (J : Category) (a : Sets) (F : [J, Sets])
  : @Isomorphism Sets (Const a ⟾ F) (a → Lim_Sets J F).
Obligation 1.
  destruct F. simpl.
  destruct X.
  apply transport0.
  auto.
Qed.
Obligation 2.
  apply Sets_Const_Nat.
  auto.
Qed.
Obligation 3.
  extensionality e.
  unfold Sets_Const_Lim_Iso_obligation_1.
  unfold Sets_Const_Lim_Iso_obligation_2.
  extensionality f.
  extensionality g.
  destruct F. simpl.
  unfold Sets_Const_Nat_obligation_1.
  reflexivity.
Qed.
Obligation 4.
  extensionality e.
  unfold Sets_Const_Lim_Iso_obligation_1.
  unfold Sets_Const_Lim_Iso_obligation_2.
  unfold Sets_Const_Nat.
  destruct e.
  unfold Sets_Const_Nat_obligation_1.
  unfold Sets_Const_Nat_obligation_2.
  apply nat_irrelevance.
  extensionality f.
  extensionality g.
  destruct F. simpl.
  reflexivity.
Qed.

Program Instance Sets_Complete : Complete Sets.
Obligation 1.
  exists (Lim_Sets J).
  apply Build_Adjunction.
  intros. simpl.
  apply Sets_Const_Lim_Iso.
Qed.
*)