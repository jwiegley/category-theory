Set Warnings "-notation-overridden".

Require Import Coq.Bool.Bool.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Normal.TList.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.

Generalizable All Variables.

Section NormalValid.

Context `{H : Env}.

(*

jww (2018-03-05): This is only possible if we can assert UIP of positive map
lookups on the same key, and finding the same element.

Equations ArrowList_eq_dec {dom cod fs}
          (f g : ArrowList dom cod fs) : { f = g } + { f ≠ g } :=
  ArrowList_eq_dec f g by rec fs (MR lt (@length arr_idx)) :=
  ArrowList_eq_dec tnil tnil := left eq_refl;
  ArrowList_eq_dec (ComposedArrow midf _ _ _ _ _ IHf)
                    (ComposedArrow midg _ _ _ _ _ IHg)
    <= Eq_eq_dec midf midg => {
         | left eq_refl := _ (ArrowList_eq_dec IHf IHg);
         | right _ := right _
       }.
Next Obligation.
  destruct x.
    left; subst.
    pose proof wildcard18.
    rewrite wildcard13 in H0.
    inversion H0; clear H0.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Pos.eq_dec].
    apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Pos.eq_dec].
    subst.
    f_equal.
    unfold arrs in *.
    pose proof wildcard18.
    apply FMapPositive.PositiveMap.elements_correct in H0.
*)

Equations getArrMorph {dom cod} (a : ArrowList dom cod) :
  objs dom ~> objs cod :=
  getArrMorph tnil := id;
  getArrMorph (tcons f g) := mor f ∘ getArrMorph g.

(*
Lemma ArrowList_compose_inv {dom cod fs gs} :
  ArrowList dom cod (fs ++ gs)
    -> ∃ mid, ArrowList dom mid gs ∧ ArrowList mid cod fs.
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

Lemma ArrowList_compose {dom mid cod fs gs} :
  ArrowList mid cod fs
    -> ArrowList dom mid gs
    -> ArrowList dom cod (fs ++ gs).
Proof.
  intros.
  generalize dependent mid.
  generalize dependent cod.
  induction fs; simpl; intros; auto;
  inversion X; subst; auto.
  specialize (IHfs _ _ X1).
  econstructor; eauto.
Defined.

Lemma getArrDom {dom cod} `(a : ArrowList dom cod (f :: fs)) :
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
  destruct (ArrowList_compose_inv X), p.
  inversion v; subst.
  rewrite H3.
  inversion X0; subst.
  reflexivity.
Qed.

Lemma getArrCod {dom cod} `(a : ArrowList dom cod (f :: fs)) :
  match arrs f with
  | Some (_; (cod'; _)) => cod = cod'
  | None => False
  end.
Proof.
  inversion a; subst; simpl.
  now rewrite H2.
Qed.

Corollary ArrowList_id_eq {dom cod}
          `(f : ArrowList dom cod []) : dom = cod.
Proof. inversion f; subst; auto. Defined.

Lemma ArrowList_dom_cod_eq {dom cod}
      `(f : ArrowList dom cod (x :: xs))
      `(g : ArrowList dom' cod' (x :: xs)) :
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

Corollary ArrowList_dom_eq {dom cod}
          `(f : ArrowList dom cod (x :: xs))
          `(g : ArrowList dom' cod (x :: xs)) :
  dom = dom'.
Proof. intros; destruct (ArrowList_dom_cod_eq f g); auto. Qed.

Corollary ArrowList_cod_eq {dom cod}
          `(f : ArrowList dom cod (x :: xs))
          `(g : ArrowList dom cod' (x :: xs)) :
  cod = cod'.
Proof. intros; destruct (ArrowList_dom_cod_eq f g); auto. Qed.
*)

Lemma getArrMorph_ArrowList_compose {dom mid cod}
      (f : ArrowList mid cod)
      (g : ArrowList dom mid) :
  getArrMorph (f +++ g) ≈ getArrMorph f ∘ getArrMorph g.
Proof.
  induction f.
    rewrite getArrMorph_equation_1; cat.
  rewrite <- tlist_app_comm_cons.
  rewrite !getArrMorph_equation_2.
  now rewrite IHf; cat.
Qed.

(*
Equations ArrowList_eq_arr {dom cod fs}
          (f g : ArrowList dom cod fs) : getArrMorph f = getArrMorph g :=
  ArrowList_eq_arr f g by rec fs (MR lt (@length arr_idx)) :=
  ArrowList_eq_arr tnil tnil := eq_refl;
  ArrowList_eq_arr (ComposedArrow f _ _ f') (ComposedArrow g _ _ g') := _.
Next Obligation.
  rewrite !getArrMorph_equation_2.
  destruct wildcard7;
  [ inversion f'; inversion g'; subst
  | pose proof (ArrowList_cod_eq f' g'); subst ];
  rewrite (ArrowList_eq_arr _ _ _ f' g') by constructor;
  rewrite wildcard3 in wildcard8;
  inversion wildcard8;
  do 2 (apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Pos.eq_dec]);
  now subst.
Qed.

Fixpoint sublistp `{Equality A} (ys xs : list A) : bool :=
  (list_beq Eq_eqb (firstn (length ys) xs) ys) |||
  match xs with
  | nil => false
  | x :: xs => sublistp ys xs
  end.

Example sublistp_ex1 : sublistp [2; 3]%positive [1; 2; 3; 4]%positive = true.
Proof. reflexivity. Qed.
*)

(*
Equations ArrowList_split {dom cod fs}
          (f : ArrowList dom cod fs) gs
          (is_present : sublistp gs fs = true) :
  ∃ i j xs ys, (ArrowList j cod xs * ArrowList i j gs * ArrowList dom i ys) :=
  ArrowList_split f [] _ :=
    (cod; (cod; ([]; (fs; (tnil cod, tnil cod, f)))));
  ArrowList_split (ComposedArrow f f' fs Hf IHf) gs _
    <= list_eq_dec Eq_eq_dec (firstn (length gs) (f :: fs)) (f :: fs) => {
      | left _ =>
        (_; (_; (_; (_; (_, _, _)))));
      | right _ =>
        match ArrowList_split IHf gs _ with
          (i; (j; (xs; (ys; (beg, mid, fin))))) => _
        end
    }.
Next Obligation.
Abort.
*)

(*
Import EqNotations.

Lemma ArrowList_Identity {dom} (f : ArrowList dom dom []) :
  getArrMorph f ≈ id.
Proof.
  dependent elimination f as [tnil].
  reflexivity.
Qed.

Lemma ArrowList_Compose {dom cod}
      `(f : ArrowList dom cod (gs ++ hs)) :
  ∃ mid (g : ArrowList mid cod gs)
        (h : ArrowList dom mid hs),
    getArrMorph f ≈ getArrMorph g ∘ getArrMorph h.
Proof.
  destruct (ArrowList_compose_inv f), p.
  exists x, v0, v.
  generalize dependent cod.
  induction gs; simpl; intros.
    inversion v0; subst.
    rewrite (ArrowList_eq_arr f v); cat.
    rewrite (ArrowList_Identity v0); cat.
  dependent elimination f as [ComposedArrow f _ _ f'].
  dependent elimination v0 as [ComposedArrow g _ _ g'].
  rewrite !getArrMorph_equation_2.
  rewrite wildcard3 in wildcard5.
  inversion wildcard5; subst.
  rewrite <- comp_assoc.
  rewrite <- (IHgs _ f' g').
  comp_right.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Pos.eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Pos.eq_dec].
  subst.
  reflexivity.
Qed.
*)

End NormalValid.
