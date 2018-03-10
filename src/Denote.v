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

Lemma termD_Ident {x} : termD x x Ident = Some id.
Proof.
  unfold termD; simpl; intros.
  now rewrite Pos_eq_dec_refl.
Defined.

Lemma termD_Comp_impl {f g dom mid cod f' g'} :
  termD mid cod f = Some f'
    -> termD dom mid g = Some g'
    -> termD dom cod (Comp f g) = Some (f' ∘ g').
Proof.
  unfold termD; simpl; intros;
  now repeat desh; repeat desg.
Defined.

Fixpoint exprD (e : Expr arr_idx) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => termD x y f ≈ termD x y g
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

End Denote.
