(* PROBE for QA finding E1 (#916): how many natural transformations Id ==> option
   are there on Coq Types?

   #916's Work item 2 orders: "Prove that Nat(Id, (-)+) has exactly ONE element,
   the 'inject' transformation x |-> Some x".  That is FALSE.  Naturality forces
   alpha_X x = fmap x (alpha_unit tt) by probing at the singleton, and
   option unit has TWO inhabitants, so there are exactly two such families:
   Some, and the constant-None family.  This probe exhibits both, proves they
   are natural, and proves they are distinct -- which already refutes "exactly
   one" without needing the full uniqueness argument. *)

Require Import Coq.Init.Datatypes.

Definition nat_trans (F G : Type -> Type) := forall X : Type, F X -> G X.

Definition omap {A B} (f : A -> B) (o : option A) : option B :=
  match o with Some a => Some (f a) | None => None end.

(* Candidate 1: the injection. *)
Definition inject : nat_trans (fun X => X) option := fun X x => Some x.

(* Candidate 2: the constant-None family. *)
Definition constNone : nat_trans (fun X => X) option := fun X _ => None.

(* Both are natural: omap f (alpha_X x) = alpha_Y (f x). *)
Theorem inject_natural :
  forall (X Y : Type) (f : X -> Y) (x : X), omap f (inject X x) = inject Y (f x).
Proof. reflexivity. Qed.

Theorem constNone_natural :
  forall (X Y : Type) (f : X -> Y) (x : X), omap f (constNone X x) = constNone Y (f x).
Proof. reflexivity. Qed.

(* They are distinct, so Nat(Id, option) has AT LEAST two elements. *)
Theorem inject_neq_constNone : inject <> constNone.
Proof.
  intro H.
  assert (inject unit tt = constNone unit tt) as HC by (rewrite H; reflexivity).
  simpl in HC. discriminate.
Qed.

(* The counting engine: option unit has exactly two inhabitants, which is what
   bounds the family count above by two once naturality pins alpha to alpha_unit. *)
Theorem option_unit_exactly_two :
  forall o : option unit, o = Some tt \/ o = None.
Proof. intro o. destruct o as [u|]. - left. destruct u. reflexivity. - right. reflexivity. Qed.
