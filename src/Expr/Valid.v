Set Warnings "-notation-overridden".

Require Import Coq.Bool.Bool.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.

Generalizable All Variables.

Section ExprValid.

Context `{Env}.

Inductive ValidTerm (dom : obj_idx) : obj_idx -> Term -> Type :=
  | IdentityTerm : ValidTerm dom dom Identity
  | MorphTerm : forall cod f f',
      arrs f = Some (dom; (cod; f'))
        -> ValidTerm dom cod (Morph f)
  | ComposeTerm : forall mid cod f g,
      ValidTerm mid cod f
        -> ValidTerm dom mid g
        -> ValidTerm dom cod (Compose f g).

Definition getTerm {dom cod} `(a : ValidTerm dom cod f) : Term := f.
Arguments getTerm {dom cod f} a /.

Equations getMorph {dom cod} `(a : ValidTerm dom cod f) :
  objs dom ~> objs cod :=
  getMorph IdentityTerm := id;
  getMorph (MorphTerm f _) := f;
  getMorph (ComposeTerm _ _ f g) := getMorph f ∘ getMorph g.

Definition ValidTerm_size {dom cod} `(a : ValidTerm dom cod f) : nat :=
  term_size f.
Arguments ValidTerm_size {dom cod f} a /.

Definition ValidTerm_compose {dom mid cod}
           `(f : ValidTerm mid cod t)
           `(g : ValidTerm dom mid u) : ValidTerm dom cod (Compose t u) :=
  ComposeTerm dom mid cod t u f g.
Arguments ValidTerm_compose {dom mid cod t} f {u} g /.

Import EqNotations.

Program Definition option_dec {A} (x : option A) :
  (∃ y : A, x = Some y) + (x = None) :=
  match x with
  | Some y => inl (y; _)
  | None => inr _
  end.

Equations fromTerm_work (dom : obj_idx) (f : Term) :
  option (∃ cod, ValidTerm dom cod f) :=
  fromTerm_work dom Identity := Some (dom; IdentityTerm dom);
  fromTerm_work dom (Morph a) <= option_dec (arrs a) => {
    | inl (existT (existT dom' (existT cod f')) Hf')
      <= eq_dec dom dom' => {
        | left H =>
          Some (cod; MorphTerm dom cod a
                  (rew <- [fun x => objs x ~> _] H in f') _);
        | _ => None
      };
    | inr _ => None
  };
  fromTerm_work dom (Compose f g)
    <= fromTerm_work dom g => {
      | Some (existT mid u) <= fromTerm_work mid f => {
          | Some (existT cod t) =>
            Some (cod; ComposeTerm dom mid cod f g t u);
          | None => None
        };
      | None => None
    }.

Definition fromTerm dom cod (f : Term) : option (ValidTerm dom cod f) :=
  match fromTerm_work dom f with
  | Some (y; v) =>
    match Eq_eq_dec y cod with
    | left H => Some (rew [fun y => ValidTerm dom y f] H in v)
    | _ => None
    end
  | _ => None
  end.

Lemma termD_ValidTerm {dom cod f f'} :
  termD dom cod f = Some f' -> ValidTerm dom cod f.
Proof.
  intros.
  pattern f, dom, cod, f', H0.
  refine (termD_rect (fun dom cod _ f => ValidTerm dom cod f) _ _ _ _ _ _ _ _);
  intros; try econstructor; eauto.
Defined.

Lemma termD_work_getMorph_fromTerm {dom f} :
  termD_work dom f = option_map (fun '(cod; p) => (cod; getMorph p))
                                (fromTerm_work dom f).
Proof.
  generalize dependent dom.
  induction f; simpl; intros.
  - rewrite fromTerm_work_equation_1; simpl.
    now rewrite getMorph_equation_1.
  - rewrite fromTerm_work_equation_2.
    unfold fromTerm_work_obligation_3.
    unfold fromTerm_work_obligation_2.
    unfold fromTerm_work_obligation_1.
    destruct (option_dec (arrs a)).
      destruct s, x, s; simpl.
      dependent rewrite e.
      unfold eq_dec.
      destruct (Pos.eq_dec x dom).
        subst.
        rewrite Pos_eq_dec_refl; simpl.
        f_equal.
      destruct (Pos.eq_dec dom x); auto.
      subst; contradiction.
    now rewrite e.
  - rewrite fromTerm_work_equation_3.
    unfold fromTerm_work_obligation_5.
    unfold fromTerm_work_obligation_4.
    rewrite IHf2; simpl.
    destruct (fromTerm_work dom f2) eqn:?; simpl; auto.
    destruct s.
    rewrite IHf1; simpl.
    destruct (fromTerm_work x f1) eqn:?; simpl; auto.
    now destruct s.
Defined.

Lemma termD_getMorph_fromTerm {dom cod f} :
  termD dom cod f = option_map getMorph (fromTerm dom cod f).
Proof.
  unfold termD, fromTerm; intros.
  rewrite termD_work_getMorph_fromTerm.
  destruct (fromTerm_work dom f); simpl; auto.
  destruct s.
  destruct (Pos.eq_dec x cod); subst; auto.
Defined.

End ExprValid.
