(*
  repeat (
    match goal with
    | [ H : { _ | _ }%type |- _ ] => destruct H
    | [ |- { _ | _ }%type ] => econstructor
    | [ H : { _ | _  & _ }%type |- _ ] => destruct H
    | [ |- { _ | _  & _ }%type ] => econstructor
    | [ H : _ ∧ _ |- _ ] => destruct H
    | [ |- _ ∧ _ ] => econstructor
    end; simpl in *; intuition; eauto).
  destruct f.
*)
