Set Warnings "-notation-overridden".

Require Import Coq.Bool.Bool.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.

Generalizable All Variables.

Section NormalValid.

Context `{Env}.

(* A reified arrow is a list of morphism indices within the current
   environment that denotes a known arrow. *)
Inductive ValidArrow (dom : obj_idx) : obj_idx -> list arr_idx -> Type :=
  | IdentityArrow : ValidArrow dom dom []
  | ComposedArrow : forall mid cod f f' gs,
      arrs f = Some (mid; (cod; f'))
        -> ValidArrow dom mid gs
        -> ValidArrow dom cod (f :: gs).

Definition getArrList {dom cod} `(a : ValidArrow dom cod fs) :
  list arr_idx := fs.
Arguments getArrList {dom cod fs} a /.

Equations getArrMorph {dom cod} `(a : ValidArrow dom cod fs) :
  objs dom ~> objs cod :=
  getArrMorph IdentityArrow := id;
  getArrMorph (ComposedArrow f _ _ g) := f ∘ getArrMorph g.

Definition ValidArrow_size {dom cod} `(a : ValidArrow dom cod fs) : nat :=
  length (getArrList a).

Lemma ValidArrow_app_inv {dom cod fs gs} :
  ValidArrow dom cod (fs ++ gs)
    -> ∃ mid, ValidArrow dom mid gs ∧ ValidArrow mid cod fs.
Proof.
  intros.
  generalize dependent cod.
  induction fs; simpl; intros.
    exists cod.
    intuition; constructor.
  inversion X; subst.
  destruct (IHfs _ X0), p.
  exists x.
  intuition.
  eapply ComposedArrow; eauto.
Defined.

Lemma ValidArrow_app {dom mid cod fs gs} :
  ValidArrow mid cod fs
    -> ValidArrow dom mid gs
    -> ValidArrow dom cod (fs ++ gs).
Proof.
  intros.
  generalize dependent mid.
  generalize dependent cod.
  induction fs; simpl; intros; auto.
    inversion X; subst; auto.
  inversion X; subst.
  specialize (IHfs _ _ X1).
  econstructor; eauto.
Defined.

Lemma getArrDom {dom cod} `(a : ValidArrow dom cod (f :: fs)) :
  match arrs (last fs f) with
  | Some (dom'; _) => dom = dom'
  | None => False
  end.
Proof.
  inversion a; subst.
  destruct fs using rev_ind; simpl.
    inversion a.
    inversion X.
    now rewrite H2.
  clear IHfs.
  rewrite last_rcons.
  destruct (ValidArrow_app_inv X), p.
  inversion v; subst.
  rewrite H3.
  inversion X0; subst.
  reflexivity.
Qed.

Lemma getArrCod {dom cod} `(a : ValidArrow dom cod (f :: fs)) :
  match arrs f with
  | Some (_; (cod'; _)) => cod = cod'
  | None => False
  end.
Proof.
  inversion a; subst; simpl.
  now rewrite H2.
Qed.

Corollary ValidArrow_id_eq {dom cod}
          `(f : ValidArrow dom cod []) : dom = cod.
Proof. inversion f; subst; auto. Defined.

Lemma ValidArrow_dom_cod_eq {dom cod}
      `(f : ValidArrow dom cod (x :: xs))
      `(g : ValidArrow dom' cod' (x :: xs)) :
  dom = dom' ∧ cod = cod'.
Proof.
  intros.
  pose proof (getArrDom f).
  pose proof (getArrCod f).
  pose proof (getArrDom g).
  pose proof (getArrCod g).
  destruct (arrs x); [|contradiction].
  destruct s, s; subst.
  destruct (arrs (last xs x)); [|contradiction].
  destruct s, s; subst.
  split; auto.
Qed.

Corollary ValidArrow_dom_eq {dom cod}
          `(f : ValidArrow dom cod (x :: xs))
          `(g : ValidArrow dom' cod (x :: xs)) :
  dom = dom'.
Proof. intros; destruct (ValidArrow_dom_cod_eq f g); auto. Qed.

Corollary ValidArrow_cod_eq {dom cod}
          `(f : ValidArrow dom cod (x :: xs))
          `(g : ValidArrow dom cod' (x :: xs)) :
  cod = cod'.
Proof. intros; destruct (ValidArrow_dom_cod_eq f g); auto. Qed.

Lemma getArrMorph_ValidArrow_comp {dom mid cod}
          `(f : ValidArrow mid cod xs)
          `(g : ValidArrow dom mid ys) :
  getArrMorph (ValidArrow_app f g) ≈ getArrMorph f ∘ getArrMorph g.
Proof.
  induction f; simpl; simpl_eq; simpl.
    rewrite getArrMorph_equation_1; cat.
  rewrite !getArrMorph_equation_2.
  rewrite IHf; cat.
Qed.

Equations ValidArrow_eq_equiv {dom cod fs}
          (f g : ValidArrow dom cod fs) : getArrMorph f ≈ getArrMorph g :=
  ValidArrow_eq_equiv f g by rec fs (MR lt (@length arr_idx)) :=
  ValidArrow_eq_equiv IdentityArrow IdentityArrow := reflexivity _;
  ValidArrow_eq_equiv (ComposedArrow f _ _ f') (ComposedArrow g _ _ g') := _.
Next Obligation.
  rewrite !getArrMorph_equation_2.
  destruct wildcard7.
    inversion f'; subst.
    inversion g'; subst.
    rewrite (ValidArrow_eq_equiv _ _ _ f' g') by constructor.
    comp_right.
    rewrite wildcard3 in wildcard8.
    inversion wildcard8.
    apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Pos.eq_dec].
    apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Pos.eq_dec].
    subst.
    reflexivity.
  pose proof (ValidArrow_cod_eq f' g'); subst.
  rewrite (ValidArrow_eq_equiv _ _ _ f' g') by constructor.
  comp_right.
  rewrite wildcard3 in wildcard8.
  inversion wildcard8.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Pos.eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Pos.eq_dec].
  subst.
  reflexivity.
Qed.

Lemma ValidArrow_app_equiv {dom mid cod}
      `(f : ValidArrow dom cod (gs ++ hs))
      `(g : ValidArrow mid cod gs)
      `(h : ValidArrow dom mid hs) :
  getArrMorph f ≈ getArrMorph g ∘ getArrMorph h.
Proof.
Abort.

End NormalValid.
