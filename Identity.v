Require Export Functors.

Inductive Identity (X : Type) : Type :=
  | Id : X -> Identity X.

Definition Identity_map {X Y} (f : X -> Y) (x : Identity X) : Identity Y :=
  match x with | Id y => Id Y (f y) end.

Hint Unfold Identity_map.

Definition Identity_apply {X Y} (f : Identity (X -> Y)) (x : Identity X)
: Identity Y :=
  match f with
   | Id f' => match x with
       | Id x' => Id Y (f' x')
     end
  end.

Definition Identity_join {X} (x : Identity (Identity X)) : Identity X :=
  match x with | Id (Id y) => Id X y end.

Program Instance Identity_Functor (X : Type) : Functor Identity :=
{ fmap := @Identity_map
}.
Next Obligation. ext_eq. autounfold. destruct x; auto. Defined.
Next Obligation. ext_eq. autounfold. destruct x; auto. Defined.

(*
Global Instance Identity_Applicative (X : Type) : Applicative Identity :=
{ is_functor := Identity_Functor X
; eta := Id
; apply := @Identity_apply
}.
Proof.
  (* app_identity *)
  intros. compute. destruct v. reflexivity.
  (* app_composition *)
  intros. compute. destruct u. destruct v. destruct w. reflexivity.
  (* app_homomorphism *)
  intros. compute. reflexivity.
  (* app_interchange *)
  intros. compute. destruct u. reflexivity.  Defined.

Global Instance Identity_Monad (X : Type) : Monad Identity :=
{ is_applicative := Identity_Applicative X
; mu := @Identity_join
}.
Proof.
  (* monad_law_1 *)
  intros. compute. destruct x. destruct i. destruct i. reflexivity.
  (* monad_law_2 *)
  intros. compute. destruct x. reflexivity.
  (* monad_law_3 *)
  intros. compute. destruct x. reflexivity.
  (* monad_law_4 *)
  intros. compute. reflexivity.
  (* monad_law_5 *)
  intros. compute. destruct x. destruct i. reflexivity.  Defined.
*)