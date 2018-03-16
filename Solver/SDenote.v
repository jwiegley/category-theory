Set Warnings "-notation-overridden".

Require Export Category.Solver.SExpr.
Require Export Category.Solver.Denote.

Generalizable All Variables.

Section Denote.

Context `{Env}.

(** The denotation Functor from syntactic sterms over environment indices. *)

Import VectorNotations.
Import EqNotations.

Program Fixpoint stermD_work dom (e : STerm positive) :
  option (∃  cod, objs[@dom] ~> objs[@cod]) :=
  match e with
  | SIdent => Some (dom; @id _ (objs[@dom]))
  | SMorph a =>
    match Fin.of_nat (Nat.pred (Pos.to_nat a)) num_arrs with
    | inleft f =>
      match Eq_eq_dec (fst (tys[@f])) dom with
      | left H =>
        Some (snd (tys[@f]);
              rew [fun x => objs[@x] ~> _] H in helper (ith arrs f))
      | _ => None
      end
    | _ => None
    end
  | SComp f g =>
    match stermD_work dom g with
    | Some (mid; g) =>
      match stermD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition stermD dom cod (e : STerm positive) :
  option (objs[@dom] ~> objs[@cod]) :=
  match stermD_work dom e with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod =>
      Some (rew [fun y => objs[@dom] ~> objs[@y]] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Fixpoint STerm_embed_work dom (e : STerm positive) :
  option (∃ cod, Term tys dom cod) :=
  match e with
  | SIdent => Some (dom; Ident)
  | SMorph a =>
    match Fin.of_nat (Nat.pred (Pos.to_nat a)) num_arrs with
    | inleft f =>
      match Eq_eq_dec (fst (tys[@f])) dom with
      | left H =>
        Some (snd (tys[@f]); rew [fun x => Term _ x _] H in Morph f)
      | _ => None
      end
    | _ => None
    end
  | SComp f g =>
    match STerm_embed_work dom g with
    | Some (mid; g) =>
      match STerm_embed_work mid f with
      | Some (y; f) => Some (y; Comp f g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition STerm_embed dom cod (e : STerm positive) :
  option (Term tys dom cod) :=
  match STerm_embed_work dom e with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod => Some (rew [fun y => Term tys _ y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Ltac teardown :=
  repeat match goal with
           [ H : context[match ?b with _ => _ end] |- _ ] =>
           destruct b eqn:?; [|discriminate]; cat
         end; subst.

Lemma stermD_embeds e {dom cod} (f : objs[@dom] ~> objs[@cod]) :
  stermD dom cod e = Some f
    -> ∃ t, STerm_embed dom cod e = Some t ∧ termD t = f.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold stermD, STerm_embed; induction e; simpl; intros.
  - destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
    exists Ident.
    cat.
  - destruct (Fin.of_nat _ _); [|discriminate].
    destruct (Fin_eq_dec _ _); [|discriminate].
    destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
    exists (Morph t).
    cat.
  - destruct (stermD_work dom e2) eqn:?; [|discriminate].
    destruct s.
    destruct (stermD_work x e1) eqn:?; [|discriminate].
    destruct s.
    destruct (Fin_eq_dec _ _); [|discriminate].
    subst.
    inv H0.
    specialize (IHe1 x cod h0).
    specialize (IHe2 dom x h).
    rewrite Heqo in IHe2.
    rewrite Heqo0 in IHe1.
    rewrite Eq_eq_dec_refl in IHe1.
    rewrite Eq_eq_dec_refl in IHe2.
    simpl_eq.
    destruct (IHe1 eq_refl), p; clear IHe1.
    destruct (IHe2 eq_refl), p; clear IHe2.
    subst.
    destruct (STerm_embed_work dom e2) eqn:?; [|discriminate].
    destruct s.
    destruct (STerm_embed_work x e1) eqn:?; [|discriminate].
    destruct s.
    destruct (Eq_eq_dec _ _); [|discriminate].
    destruct (Eq_eq_dec _ _); [|discriminate].
    subst.
    inv e.
    inv e3.
    rewrite Heqo2.
    rewrite Fin_eq_dec_refl.
    exists (Comp x0 x1).
    cat.
Qed.

(*
Lemma stermD_app {dom cod f g} :
  ∃ mid, stermD dom cod (SComp f g)
           = stermD mid cod f ∘[opt_arrs] stermD dom mid g.
Proof.
  unfold stermD; simpl.
  destruct (stermD_work dom g) eqn:?.
  - destruct s.
    exists x.
    destruct f; simpl; intros.
    + rewrite Pos_eq_dec_refl.
      destruct (Pos.eq_dec x cod); subst; auto.
    + destruct (arrs a) eqn:?.
        destruct s, s.
        repeat desg; repeat desh; cat.
      repeat desg; repeat desh; cat.
    + destruct (stermD_work x f2) eqn:?; auto.
      destruct s.
      destruct (stermD_work x0 f1) eqn:?; auto.
      destruct s.
      rewrite Pos_eq_dec_refl.
      destruct (Pos.eq_dec x1 cod); subst; auto.
  - exists cod.
    destruct (stermD_work cod f) eqn:?; auto.
    destruct s.
    destruct (Pos.eq_dec x cod); subst; auto.
Qed.
*)

Program Fixpoint sexprD (e : SExpr positive) : Type :=
  match e with
  | STop           => True
  | SBottom        => False
  | SEquiv x y f g =>
    match Fin.of_nat (Nat.pred (Pos.to_nat x)) num_objs with
    | inleft d =>
      match Fin.of_nat (Nat.pred (Pos.to_nat y)) num_objs with
      | inleft c =>
        match stermD d c f, stermD d c g with
        | Some f, Some g => f ≈ g
        | _, _ => False
        end
      | _ => False
      end
    | _ => False
    end
  | SAnd p q       => sexprD p ∧ sexprD q
  | SOr p q        => sexprD p + sexprD q
  | SImpl p q      => sexprD p -> sexprD q
  end.

End Denote.
