Set Warnings "-notation-overridden".

Require Export Solver.Expr.

Unset Equations WithK.

Generalizable All Variables.

Section Denote.

Context `{Env}.

(** The denotation Functor from syntactic terms over environment indices. *)

Import EqNotations.

Fixpoint termD_work dom (e : Term arr_idx) :
  option (∃ cod, objs dom ~> objs cod) :=
  match e with
  | Ident => Some (dom; @id _ (objs dom))
  | Morph a =>
    match arrs a with
    | Some (x; (y; f)) =>
      match Eq_eq_dec x dom with
      | Specif.left edom =>
        Some (y; rew [fun x => objs x ~> objs y] edom in f)
      | _ => None
      end
    | _ => None
    end
  | Comp f g =>
    match termD_work dom g with
    | Some (mid; g) =>
      match termD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition termD dom cod (e : Term arr_idx) : option (objs dom ~> objs cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod => Some (rew [fun y => objs dom ~> objs y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Fixpoint exprD (e : Expr arr_idx) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => termD x y f ≈ termD x y g
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Definition option_arr_equiv {dom cod}
           (x y : option (objs dom ~{ cat }~> objs cod)) :=
  match x, y with
  | Some f, Some g => f ≈ g
  | None, None => True
  | _, _ => False
  end.

Global Instance option_arr_equivalence {dom cod} :
  Equivalence (@option_arr_equiv dom cod).
Proof.
  unfold option_arr_equiv.
  equivalence.
  - destruct x; cat.
  - destruct x, y; cat; desh.
  - destruct x, y, z; cat; repeat desh.
    contradiction.
Qed.

Global Program Instance option_arr_Setoid {dom cod} :
  Setoid (option (objs dom ~{ cat }~> objs cod)) := {
  equiv := option_arr_equiv
}.

Ltac finish :=
  program_simpl;
  proper;
  unfold option_arr_equiv, termD in *; simpl in *;
  repeat desh; cat; repeat desg; cat;
  repeat desh; cat; repeat desg; cat.

Program Definition Denoted : Category := {|
  obj := obj_idx;
  hom := fun _ _ => Term arr_idx;
  homset := fun dom cod => {| equiv := fun f g =>
    termD dom cod f ≈ termD dom cod g |};
  id := fun _ => Ident;
  compose := fun _ _ _ => Comp
|}.
Next Obligation.
  equivalence.
  now transitivity (termD dom cod y).
Qed.
Next Obligation.
  proper.
  finish.
Admitted.
Next Obligation. finish. Qed.
Next Obligation. finish. Qed.
Next Obligation. finish; inv Heqo; cat. Qed.
Next Obligation. finish. Qed.

End Denote.
