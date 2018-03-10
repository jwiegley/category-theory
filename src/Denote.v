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

(*
Import EqNotations.

Equations termD (dom cod : obj_idx) (e : Term arr_idx) :
  option (objs dom ~> objs cod) :=
  termD dom cod Ident <= eq_dec dom cod => {
    | Specif.left H =>
      Some (rew [fun x => _ ~> objs x] H in @id cat (objs dom));
    | _ => None
  };
  termD dom cod (Morph a) <= arrs a => {
    | Some (existT d (existT c f)) <= eq_dec dom d => {
        | Specif.left H1 <= eq_dec cod c => {
            | Specif.left H2 =>
              Some (rew <- [fun x => objs x ~> _] H1 in
                    rew <- [fun x => _ ~> objs x] H2 in f);
            | _ => None
          };
        | _ => None
      };
    | _ => None
  };
  termD dom cod (Comp f g) <= Term_cod dom g => {
    | Some mid <= termD mid cod f => {
        | Some f' <= termD dom mid g => {
            | Some g' => Some (f' ∘ g');
            | _ => None
          };
        | _ => None
      };
    | _ => None
  }.
*)

Lemma termD_rect
      (P : Term arr_idx -> ∀ dom cod, objs dom ~> objs cod -> Type) :
     (∀ dom, termD dom dom Ident = Some id -> P Ident dom dom id)
  -> (∀ a dom cod f', arrs a = Some (dom; (cod; f'))
        -> termD dom cod (Morph a) = Some f'
        -> P (Morph a) dom cod f')
  -> (∀ f mid cod f', termD mid cod f = Some f'
        -> P f mid cod f'
        -> ∀ g dom g', termD dom mid g = Some g'
        -> P g dom mid g' -> P (Comp f g) dom cod (f' ∘ g'))
  -> ∀ f dom cod f', termD dom cod f = Some f'
       -> P f dom cod f'.
Proof.
  unfold termD.
  induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate]; subst; auto.
    inversion H0; subst.
    apply X.
    simpl.
    now rewrite Pos_eq_dec_refl.
  - destruct (arrs a) eqn:?; [|discriminate].
    destruct s, s.
    destruct (Pos.eq_dec x dom); [|discriminate].
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    inversion H0; subst.
    apply X0.
      now rewrite Heqo.
    simpl.
    rewrite Heqo.
    rewrite Pos_eq_dec_refl.
    now rewrite Pos_eq_dec_refl.
  - destruct (termD_work dom f2) eqn:?; [|discriminate].
    destruct s.
    destruct (termD_work x f1) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst; simpl in *.
    specialize (IHf1 x cod h0).
    specialize (IHf2 dom x h).
    rewrite Heqo0, Pos_eq_dec_refl in IHf1.
    rewrite Heqo, Pos_eq_dec_refl in IHf2.
    specialize (IHf1 eq_refl).
    specialize (IHf2 eq_refl).
    specialize (X1 f1 x cod h0).
    rewrite Heqo0, Pos_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf1 f2 dom h).
    rewrite Heqo, Pos_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf2).
    inversion H0; subst.
    apply X1.
Defined.

(** Determine the co-domain of an environment, given its domain. *)

Equations Term_cod (dom : obj_idx) (e : Term arr_idx) : option obj_idx :=
  Term_cod dom Ident := Some dom;
  Term_cod dom (Morph a) <= arrs a => {
    | Some (existT d (existT cod _)) <= eq_dec dom d => {
        | Specif.left _ => Some cod;
        | _ => None
      };
    | None => None
  };
  Term_cod dom (Comp f g) <= Term_cod dom g => {
    | Some mid => Term_cod mid f;
    | None => None
  }.

Lemma Term_cod_Some {f dom cod f'} :
  termD_work dom f = Some (cod; f') -> Term_cod dom f = Some cod.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction f; simpl; intros.
  - rewrite Term_cod_equation_1.
    now inv H0.
  - rewrite Term_cod_equation_2.
    unfold Term_cod_obligation_2.
    unfold Term_cod_obligation_1.
    now desh; desh.
  - rewrite Term_cod_equation_3.
    unfold Term_cod_obligation_3.
    desh; desh.
    desg; rewrite (IHf2 _ _ _ Heqo) in Heqo1.
      inv Heqo1.
      apply (IHf1 _ _ _ Heqo0).
    discriminate.
Defined.

Lemma Term_cod_Some_inv {f dom cod} :
  Term_cod dom f = Some cod -> ∃ f', termD dom cod f = Some f'.
Proof.
  unfold termD.
  generalize dependent cod.
  generalize dependent dom.
  induction f; simpl; intros.
  - rewrite Term_cod_equation_1 in H0.
    inv H0.
    exists id.
    now equalities.
  - rewrite Term_cod_equation_2 in H0.
    unfold Term_cod_obligation_2 in H0.
    unfold Term_cod_obligation_1 in H0.
    desh; desh.
    exists e0.
    now equalities.
  - rewrite Term_cod_equation_3 in H0.
    unfold Term_cod_obligation_3 in H0.
    desh.
    destruct (IHf1 _ _ H0); clear IHf1.
    destruct (IHf2 _ _ Heqo); clear IHf2.
    repeat desh.
    now exists (x ∘ x0).
Defined.

Lemma Term_cod_None {f dom} :
  Term_cod dom f = None -> ∀ cod, termD dom cod f = None.
Proof.
  unfold termD.
  generalize dependent dom.
  induction f; simpl; intros.
  - inversion H0.
  - rewrite Term_cod_equation_2 in H0.
    unfold Term_cod_obligation_2 in H0.
    unfold Term_cod_obligation_1 in H0.
    unfold termD; simpl.
    now desh; cat; desh; desg; desh.
  - rewrite Term_cod_equation_3 in H0.
    unfold Term_cod_obligation_3 in H0.
    desh.
      clear IHf2.
      specialize (IHf1 _ H0).
      destruct (Term_cod_Some_inv Heqo); clear Heqo.
      unfold termD in e.
      repeat desh; repeat desg; auto.
      now specialize (IHf1 cod); desh.
    specialize (IHf2 _ Heqo).
    repeat desh; repeat desg; auto.
    now specialize (IHf2 x); desh.
Defined.

Lemma termD_Ident {x} : termD x x Ident = Some id.
Proof.
  unfold termD; simpl; intros.
  now rewrite Pos_eq_dec_refl.
Defined.

Lemma termD_Morph {f dom cod f'} :
  arrs f = Some (dom; (cod; f')) ↔ termD dom cod (Morph f) = Some f'.
Proof.
  unfold termD; simpl; split; intros.
    rewrite H0.
    now rewrite !Pos_eq_dec_refl.
  destruct (arrs f) eqn:?; [|discriminate].
  destruct s, s.
  destruct (BinPos.Pos.eq_dec x dom); subst; [|discriminate].
  destruct (BinPos.Pos.eq_dec x0 cod); subst; [|discriminate].
  inversion H0; subst; clear H0.
  reflexivity.
Defined.

Lemma termD_Comp {f g dom cod} :
  termD dom cod (Comp f g) =
    match Term_cod dom g with
    | Some mid =>
      match termD dom mid g with
      | Some g' =>
        match termD mid cod f with
        | Some f' => Some (f' ∘ g')
        | None => None
        end
      | None => None
      end
    | None => None
    end.
Proof.
  unfold termD; simpl; intros.
  generalize dependent cod.
  generalize dependent dom.
  induction g; simpl; intros.
  - rewrite Term_cod_equation_1.
    rewrite Pos_eq_dec_refl.
    desg; desh; auto.
    now desg.
  - rewrite Term_cod_equation_2.
    unfold Term_cod_obligation_2.
    desg; repeat (cat; desh).
    + unfold Term_cod_obligation_1.
      desg; rewrite Heqo1; desg; auto.
        now inv Heqo0.
      now desh.
    + unfold Term_cod_obligation_1.
      now desg; desg; desh.
    + unfold Term_cod_obligation_1.
      now desg.
  - rewrite Term_cod_equation_3.
    unfold Term_cod_obligation_3.
    repeat desg;
    repeat desh; auto.
    + apply Term_cod_Some in Heqo4.
      rewrite Heqo4 in Heqo2; inv Heqo2.
      apply Term_cod_Some in Heqo5.
      rewrite Heqo5 in Heqo0; inv Heqo0.
      contradiction.
    + apply Term_cod_Some in Heqo.
      rewrite Heqo in Heqo1; inv Heqo1.
      apply Term_cod_Some in Heqo3.
      congruence.
    + apply Term_cod_Some in Heqo.
      congruence.
Defined.

Lemma termD_Comp_impl {f g dom mid cod f' g'} :
  termD mid cod f = Some f'
    -> termD dom mid g = Some g'
    -> termD dom cod (Comp f g) = Some (f' ∘ g').
Proof.
  unfold termD; simpl; intros;
  now repeat desh; repeat desg.
Defined.

Lemma termD_Comp_None_right {f g dom} :
  termD_work dom g = None
    -> termD_work dom (Comp f g) = None.
Proof.
  unfold termD; simpl; intros;
  now repeat desh; repeat desg.
Defined.

Lemma arrows_nil {dom cod f f'} :
  arrows f = []%list
    -> termD_work dom f = Some (cod; f')
    -> ∃ H : dom = cod,
         f' ≈ rew [fun x => _ ~> objs x] H in @id cat (objs dom).
Proof.
  clear; intros.
  generalize dependent cod.
  generalize dependent dom.
  induction f; simpl in *; intros.
  - inv H1.
    exists eq_refl.
    reflexivity.
  - desh.
  - repeat desh.
    apply List.app_eq_nil in H0.
    destruct H0.
    firstorder idtac.
    destruct (X _ _ _ Heqo); subst.
    destruct (X0 _ _ _ Heqo0); subst.
    exists eq_refl.
    rewrite e1, e2; cat.
Qed.

Lemma arrows_termD_nil {f} :
  arrows f = []%list
    -> ∀ dom, termD_work dom f ≈ Some (dom; id).
Proof.
  clear; intros.
  generalize dependent dom.
  induction f; simpl in *; intros; auto.
  - rewrite eq_dec_refl; cat.
  - discriminate.
  - apply List.app_eq_nil in H0.
    destruct H0.
    firstorder idtac.
    repeat desg.
    + specialize (X dom).
      specialize (X0 x).
      rewrite Heqo in X.
      rewrite Heqo0 in X0.
      simpl in X, X0.
      desh.
      rewrite eq_dec_refl in X.
      rewrite X, X0; cat.
    + destruct (arrows_nil H0 Heqo0); subst.
      destruct (arrows_nil H1 Heqo); subst.
      contradiction.
    + specialize (X0 x).
      rewrite Heqo0 in X0.
      simpl in X0.
      contradiction.
    + specialize (X dom).
      rewrite Heqo in X.
      simpl in X.
      contradiction.
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
