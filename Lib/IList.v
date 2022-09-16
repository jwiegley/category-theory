Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section ilist.

Context {A : Type}.
Context {B : A → Type}.

Fixpoint ilist (l : list A) : Type :=
  match l with
  | []      => unit
  | x :: xs => B x * ilist xs
  end.

Definition icons
           (a : A)
           {l : list A}
           (b : B a)
           (il : ilist l) : ilist (a :: l) :=
  (b, il).

Definition inil : ilist [] := tt.

(* Get the car of an ilist. *)
Definition ilist_hd {As : list A} (il : ilist As) :
  match As return ilist As → Type with
    | a :: As' => fun il => B a
    | [] => fun _ => unit
  end il :=
  match As return
        ∀ (il : ilist As),
          match As return ilist As → Type with
            | a :: As' => fun il => B a
            | [] => fun _ => unit
          end il with
    | a :: As => fun il => fst il
    | [] => fun il => tt
  end il.

(* Get the cdr of an ilist. *)
Definition ilist_tl {As : list A} (il : ilist As) :
  match As return ilist As → Type with
    | a :: As' => fun il => ilist As'
    | [] => fun _ => unit
  end il :=
  match As return
        ∀ (il : ilist As),
          match As return ilist As → Type with
            | a :: As' => fun il => ilist As'
            | [] => fun _ => unit
          end il with
    | a :: As => fun il => snd il
    | [] => fun il => tt
  end il.

Definition ith (n : nat) {As : list A} (il : ilist As)
  {defA : A} (defB : B defA) : B (nth n As defA).
Proof.
  generalize dependent As.
  induction n; intros.
  - destruct As; simpl.
    + exact defB.
    + exact (fst il).
  - destruct As; simpl.
    + exact defB.
    + apply IHn.
      exact (snd il).
Defined.

Definition ith_exact `{EqDec A} (n : nat) (a : A)
  {As : list A} (il : ilist As) : option (B a).
Proof.
  generalize dependent As.
  induction n; intros.
  - destruct As; simpl.
    + exact None.
    + simpl in il.
      destruct (eq_dec a a0); subst.
      * exact (Some (fst il)).
      * exact None.
  - destruct As; simpl.
    + exact None.
    + simpl in il.
      destruct il.
      exact (IHn As i).
Defined.

Equations iapp `(xs : ilist l) `(ys : ilist l') : ilist (l ++ l') :=
  iapp (l:=[]) tt ys := ys;
  iapp (x, xs) ys := (x, iapp xs ys).

Equations isplit `(xs : ilist (l ++ l')) : ilist l * ilist l'  :=
  isplit (l:=[]) xs := (tt, xs);
  isplit (x, xs) with isplit xs := {
    | (xs', ys) => ((x, xs'), ys)
  }.

End ilist.

Equations imap `(f : A → C) `(k : ∀ (a : A), B a → D (f a))
  `(xs : @ilist A B l) : @ilist C D (map f l) :=
  imap f k (l:=[]) tt := tt;
  imap f k (l:=j :: js) (x, xs) := (k j x, imap f k xs).

Equations imap' `(k : ∀ (a : A), B a → C a)
  `(xs : @ilist A B l) : @ilist A C l :=
  imap' k (l:=[]) tt := tt;
  imap' k (l:=j :: js) (x, xs) := (k j x, imap' k xs).
