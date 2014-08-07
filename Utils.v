Require Export Coq.Program.Equality.
Require Export Coq.Unicode.Utf8.
Require Export FunctionalExtensionality.
Require Export Hask.CpdtTactics.

Set Printing Width 100.

Definition π1 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT1 k.
Definition π2 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT2 k.

(* Commonly occurring patterns that can now be solved with 'auto'. *)
Hint Extern 4 (?A = ?A) => reflexivity.
Hint Extern 7 (?X = ?Z) => match goal
  with [H : ?X = ?Y, H' : ?Y = ?Z |- ?X = ?Z] => transitivity Y end.

Ltac simple_solver :=
  intros;
  try extensionality e;
  compute;
  repeat (
    match goal with
    | [ |- context f [match ?X with _ => _ end] ] =>
      is_var X; destruct X; auto
    end);
  auto.
