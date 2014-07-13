Require Export Axioms.

Definition Sep (X : set) (P : set → Prop) : set :=
  ε (inhabits _ ∅) (fun Z => ∀ x, x ∈ Z → x ∈ X ∧ P x ).

(*
Lemma Sep_correct : forall X P x, x ∈ (Sep X P) <-> x ∈ X ∧ P x.
Proof.
  intros X P. unfold Sep. apply ε_spec.
  destruct (classic (exists x : set, x ∈ X /\ P x)).
    (* x_def exists *) destruct H as [x_def [M p]].
      set (F_spec x y := P x /\ x = y \/ ~ P x /\ x_def = y).
      set (F x := ε (inhabits ∅) (F_spec x)).
      assert (FC: forall x, F_spec x (F x)).
        intros x. refine (ε_spec (inhabits ∅) (F_spec x) _). unfold F_spec.
        destruct (classic (P x)) as [p' | p']; [exists x | exists x_def]; tauto.
      assert (A: forall x, P x -> x = F x ) by firstorder.
      assert (B: forall x, ~ P x -> x_def = F x) by firstorder.
      exists (Repl F X). intros x. split; intros H.
        apply ReplE in H. destruct H as [z [K L]].
          destruct (classic (P z)) as [p' | p'].
            assert (E: z = F z) by apply (A _ p'). split; congruence.
            assert (E: x_def = F z) by apply (B _ p'). split; congruence.
        destruct H as [M' p']. assert (E: x = F x) by apply (A _ p').
          rewrite E. auto with TG_set.
    (* no x_def *) exists ∅. firstorder using Empty_E.
Qed.
*)

(* (Definition of Separation is correct). For all bounding sets X and for all
   predicates on sets P, the set Sep X P, mathematically {x ∈ X | P x}, is
   exactly the subset of X where all elements satisfy P.
*)
Lemma Sep_I : ∀ X, ∀ P : set → Prop, ∀ x, x ∈ X → P x → x ∈ (Sep X P).
Proof.
  intros. unfold Sep.
Admitted.

Hint Resolve Sep_I.

Lemma Sep_E1 : ∀ X P x, x ∈ (Sep X P) → x ∈ X.
Proof.
  intros. unfold Sep in H.
Admitted.

Hint Resolve Sep_E1.

Lemma Sep_E2 : ∀ X P x, x ∈ (Sep X P) → P x.
Proof.
  intros. unfold Sep in H.
Admitted.

Lemma Sep_E : ∀ X P x, x ∈ (Sep X P) → x ∈ X ∧ P x.
Proof.
  intros. unfold Sep in H.
Admitted.

Hint Resolve Sep_E.
