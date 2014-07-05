Inductive Truth : Prop :=
  | True : Truth
  | False : Truth.

Definition ble (a b : Truth) : Truth :=
  match a with
    | True => b
    | False => True
  end.

Definition band (a b : Truth) : Truth :=
  match a with
    | True => b
    | False => False
  end.

Definition bor (a b : Truth) : Truth :=
  match a with
    | True => True
    | False => b
  end.

Definition bnot (a : Truth) : Truth :=
  match a with
    | True => False
    | False => True
  end.

Definition bimpl (a b : Truth) : Truth := bor (bnot a) b.

Theorem bool_heyting : forall {a b c : Truth},
  ble (band c a) b = True <-> ble c (bimpl a b) = True.
Proof.
  intros. compute. destruct c. destruct a. destruct b.
  split; reflexivity.
  split; intros; apply H.
  split; destruct b; reflexivity.
  split; reflexivity.
Qed.