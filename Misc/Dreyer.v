Require Export Coq.Setoids.Setoid.

Set Printing Universes.

Definition N : Type := forall A, A -> (A -> A) -> A.

Definition zero : N := fun _ z s => z.
Definition succ : N -> N := fun x => fun _ z s => s (x _ z s).

Definition C_0 := zero.

Fixpoint C_n (n : nat) :=
  match n with
    | O => C_0
    | S x => succ (C_n x)
  end.

Theorem succ_swap : forall n, succ (C_n n) = C_n (S n).
Proof. reflexivity. Qed.

Theorem dreyer_1 : forall (n : nat), exists (e : N),
  @e N zero succ = C_n n.
Proof.
  intros. induction n as [| n'].
    apply ex_intro with (x := zero). reflexivity.
    destruct IHn'.
    apply ex_intro with (x := succ x).
    rewrite <- succ_swap.
    assert (forall o, C_n o N zero succ = C_n o ->
            succ (C_n o) N zero succ = succ (C_n o)).
      intros. induction o. reflexivity.
        simpl in IHo.
        rewrite <- succ_swap.
        rewrite <- succ_swap in H0.
        rewrite <- H0 at 2. reflexivity.
    rewrite <- H. reflexivity.
Qed.