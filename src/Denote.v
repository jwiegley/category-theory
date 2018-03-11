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

Lemma termD_app {dom cod f g} :
  ∃ mid, termD dom cod (Comp f g)
           = termD mid cod f ∘[opt_arrs] termD dom mid g.
Proof.
  unfold termD; simpl.
  destruct (termD_work dom g) eqn:?.
  - destruct s.
    exists x.
    destruct f; simpl; intros.
    + rewrite Pos_eq_dec_refl.
      destruct (Pos.eq_dec x cod); subst; auto.
    + destruct (arrs a) eqn:?.
        destruct s, s.
        repeat desg; repeat desh; cat.
      repeat desg; repeat desh; cat.
    + destruct (termD_work x f2) eqn:?; auto.
      destruct s.
      destruct (termD_work x0 f1) eqn:?; auto.
      destruct s.
      rewrite Pos_eq_dec_refl.
      destruct (Pos.eq_dec x1 cod); subst; auto.
  - exists cod.
    destruct (termD_work cod f) eqn:?; auto.
    destruct s.
    destruct (Pos.eq_dec x cod); subst; auto.
Qed.

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
