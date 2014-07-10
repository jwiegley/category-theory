Require Export Axioms.

Definition Sing (x : set): set := {x, x}.

Lemma Sing_I : ∀ x, x ∈ (Sing x).
Proof. intros. compute. auto. Qed.

Hint Resolve Sing_I.

Lemma Sing_E : ∀ x y, y ∈ (Sing x) → y = x.
Proof.
  intros. compute in *.
  apply UPair_E in H. inversion H; auto.
Qed.

Hint Resolve Sing_E.

Ltac sing := apply Sing_I ; try auto.
Ltac sing_e H := apply Sing_E in H ; try auto.

Definition Zero := ∅.
Definition One := Sing ∅.
Definition Two := { ∅, One }.

(* We need to be able to extract information from equalities of unordered
   pairs and or singltons.
*)
Lemma UU_ex : forall W X Y Z, UPair W X = UPair Y Z ->
  ( W = Y /\ X = Z ) \/ ( W = Z /\ X = Y ).
Proof.
  intros.
  assert (C: W ∈ UPair Y Z). rewrite <- H. pair_1.
  assert (D: X ∈ UPair Y Z). rewrite <- H. pair_2.
  assert (E: Y ∈ UPair W X). rewrite H. pair_1.
  assert (F: Z ∈ UPair W X). rewrite H. pair_2.
  pair_e C; pair_e D; pair_e E; pair_e F.
Qed.

Lemma SU_ex : forall X Y Z, Sing X = UPair Y Z -> X = Y /\ X = Z.
Proof.
  intros.
  assert (C: X ∈ UPair Y Z). rewrite <- H. pair_1.
  assert (D: Y ∈ Sing X). rewrite H. pair_1.
  assert (E: Z ∈ Sing X). rewrite H. pair_2.
  pair_e C; pair_e D; pair_e E.
Qed.

Lemma US_ex : forall X Y Z, UPair Y Z = Sing X -> X = Y /\ X = Z.
Proof.
  intros.
  assert (C: Y ∈ Sing X). rewrite <- H. pair_1.
  assert (D: Z ∈ Sing X). rewrite <- H. pair_2.
  assert (E: X ∈ UPair Y Z). rewrite H. pair_1.
  pair_e C; pair_e D; pair_e E.
Qed.

Lemma SS_ex : forall X Y, Sing X = Sing Y -> X = Y.
Proof.
  intros.
  assert (C: X ∈ Sing Y). rewrite <- H. sing.
  assert (D: Y ∈ Sing X). rewrite H. sing.
  pair_e C; pair_e D.
Qed.

Ltac inv_SU_eq :=
  repeat let E1 := fresh "E" in
         let E2 := fresh "E" in
         let E3 := fresh "E" in
         let E4 := fresh "E" in
         match goal with
         | [H : UPair ?A ?B = UPair ?C ?D |- _ ] =>
             destruct (UU_ex H) as [[E1 E2] | [E3 E4]]; clear H; subst
         | [H : Sing ?A = UPair ?B ?C |- _ ] =>
             destruct (SU_ex H) as [E1 E2]; clear H; subst
         | [H : UPair ?A ?B = Sing ?C |- _ ] =>
             destruct (US_ex H) as [E1 E2]; clear H; subst
         | [H : Sing ?A = Sing ?B |- _ ] =>
             apply SS_ex in H; subst
         end.
