Set Warnings "-notation-overridden".

Require Import Coq.Bool.Bool.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
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
Require Import Solver.Normal.TList.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.

Generalizable All Variables.

Section NormalValid.

Context `{H : Env}.

Import EqNotations.

Equations getArrMorph {dom cod} (a : ArrowList dom cod) :
  objs dom ~> objs cod :=
  getArrMorph tnil := id;
  getArrMorph (tcons f g) := mor f ∘ getArrMorph g.

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

Program Definition option_dec {A} (x : option A) :
  (∃ y : A, x = Some y) + (x = None) :=
  match x with
  | Some y => inl (y; _)
  | None => inr _
  end.

Equations Term_to_ArrowList_work (dom : obj_idx) (f : Term) :
  option (∃ cod, ArrowList dom cod) :=
  Term_to_ArrowList_work dom Identity := Some (dom; tnil);
  Term_to_ArrowList_work dom (Morph a) <= option_dec (arrs a) => {
    | inl (existT (existT dom' (existT cod f')) Hf')
      <= eq_dec dom dom' => {
        | left H =>
          Some (cod; Build_Arrow dom cod a
                  (rew <- [fun x => objs x ~> _] H in f') _ ::: tnil);
        | _ => None
      };
    | inr _ => None
  };
  Term_to_ArrowList_work dom (Compose f g)
    <= Term_to_ArrowList_work dom g => {
      | Some (existT mid u) <= Term_to_ArrowList_work mid f => {
          | Some (existT cod t) =>
            Some (cod; t +++ u);
          | None => None
        };
      | None => None
    }.

Definition Term_to_ArrowList dom cod (f : Term) : option (ArrowList dom cod) :=
  match Term_to_ArrowList_work dom f with
  | Some (y; v) =>
    match Eq_eq_dec y cod with
    | left H => Some (rew [fun y => ArrowList dom y] H in v)
    | _ => None
    end
  | _ => None
  end.

Global Program Instance mor_work_Setoid {dom} :
  Setoid (∃ cod : obj_idx, objs dom ~> objs cod) := {
  equiv := fun f g => match Eq_eq_dec `1 f `1 g with
    | left H => `2 f ≈ rew <- [fun x => _ ~> objs x] H in `2 g
    | right _ => False
    end
}.
Next Obligation.
  equivalence; simpl in *.
  - now rewrite Pos_eq_dec_refl.
  - destruct (Pos.eq_dec x1 x0); [|contradiction]; subst.
    rewrite Pos_eq_dec_refl.
    now symmetry.
  - destruct (Pos.eq_dec x1 x0); [|contradiction]; subst.
    destruct (Pos.eq_dec x2 x0); [|contradiction]; subst.
    now transitivity e0.
Qed.

Lemma termD_work_getMorph_fromTerm {dom f} :
  termD_work dom f ≈ option_map (fun '(cod; p) => (cod; getArrMorph p))
                                (Term_to_ArrowList_work dom f).
Proof.
  generalize dependent dom.
  induction f; intros.
  - rewrite Term_to_ArrowList_work_equation_1; simpl.
    rewrite Pos_eq_dec_refl; cat.
  - rewrite Term_to_ArrowList_work_equation_2.
    unfold Term_to_ArrowList_work_obligation_3.
    unfold Term_to_ArrowList_work_obligation_2.
    unfold Term_to_ArrowList_work_obligation_1.
    destruct (option_dec (arrs a)).
      destruct s, x, s; simpl.
      dependent rewrite e.
      unfold eq_dec.
      destruct (Pos.eq_dec x dom).
        subst.
        rewrite Pos_eq_dec_refl; simpl.
        rewrite Pos_eq_dec_refl; simpl.
        rewrite getArrMorph_equation_2; simpl.
        rewrite getArrMorph_equation_1; simpl.
        simpl_eq; cat.
      destruct (Pos.eq_dec dom x); auto.
        subst; contradiction.
      constructor.
    now simpl; rewrite e.
  - rewrite Term_to_ArrowList_work_equation_3.
    unfold Term_to_ArrowList_work_obligation_5.
    unfold Term_to_ArrowList_work_obligation_4.
    specialize (IHf2 dom).
    destruct (Term_to_ArrowList_work dom f2) eqn:?; auto.
      destruct s.
      simpl termD_work.
      simpl option_map in IHf2.
      destruct (termD_work dom f2); [|inversion IHf2]; auto.
      destruct s.
      specialize (IHf1 x0).
      destruct (Term_to_ArrowList_work x0 f1) eqn:?; auto.
        destruct s.
        simpl option_map in IHf1.
        destruct (termD_work x0 f1); [|inversion IHf1]; auto.
        destruct s.
        do 2 red in IHf1.
        do 2 red in IHf2.
        simpl in *.
        destruct (Pos.eq_dec x0 x); [|contradiction].
        destruct (Pos.eq_dec x2 x1); [|contradiction].
        subst.
        rewrite Heqo0.
        simpl.
        rewrite Pos_eq_dec_refl.
        simpl_eq.
        rewrite getArrMorph_ArrowList_compose.
        now rewrite IHf1, IHf2.
      simpl in IHf1.
      destruct (termD_work x0 f1); [contradiction|]; auto.
      do 2 red in IHf2.
      simpl in *.
      destruct (Pos.eq_dec x0 x); [|contradiction].
      subst.
      rewrite Heqo0; simpl; auto.
    simpl in *.
    destruct (termD_work dom f2); [contradiction|]; auto.
Defined.

Lemma termD_getMorph_fromTerm {dom cod f} :
  termD dom cod f ≈ option_map getArrMorph (Term_to_ArrowList dom cod f).
Proof.
  unfold termD, Term_to_ArrowList.
  pose proof (@termD_work_getMorph_fromTerm dom f).
  red in X.
  destruct (termD_work dom f) eqn:?.
    destruct s.
    destruct (Term_to_ArrowList_work dom f) eqn:?; simpl; auto.
      destruct s.
      simpl in X.
      destruct (Pos.eq_dec x x0); subst; [|contradiction].
      destruct (Pos.eq_dec x0 cod); subst.
        exact X.
      constructor.
    simpl in X.
    contradiction.
  destruct (Term_to_ArrowList_work dom f) eqn:?; simpl; auto.
  destruct s.
  simpl in *.
  contradiction.
Defined.

Lemma Term_to_ArrowList_sound {dom cod f f'} :
  termD dom cod f = Some f'
    -> ∃ xs, Term_to_ArrowList dom cod f = Some xs.
Proof.
  unfold termD, Term_to_ArrowList; intros.
  generalize dependent cod.
  generalize dependent dom.
  induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate].
    subst.
    exists tnil.
    rewrite Term_to_ArrowList_work_equation_1.
    rewrite Pos_eq_dec_refl.
    reflexivity.
  - rewrite Term_to_ArrowList_work_equation_2.
    unfold Term_to_ArrowList_work_obligation_3.
    destruct (option_dec (arrs a)).
      destruct s, x, s.
      rewrite e in *.
      destruct (Pos.eq_dec x dom); [|discriminate]; subst.
      rewrite eq_dec_refl.
      destruct (Pos.eq_dec x0 cod); [|discriminate]; subst.
      simpl in *.
      rewrite Pos_eq_dec_refl.
      simpl.
      eexists; reflexivity.
    rewrite e in *.
    discriminate.
  - rewrite Term_to_ArrowList_work_equation_3.
    unfold Term_to_ArrowList_work_obligation_5.
    destruct (termD_work dom f2) eqn:?; [|discriminate].
    destruct s.
    destruct (termD_work x f1) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x0 cod); [|discriminate]; subst.
    simpl in *.
    specialize (IHf1 x cod h0).
    rewrite Heqo0, Pos_eq_dec_refl in IHf1.
    specialize (IHf1 eq_refl).
    specialize (IHf2 dom x h).
    rewrite Heqo, Pos_eq_dec_refl in IHf2.
    specialize (IHf2 eq_refl).
    simpl in *.
    destruct IHf1 as [xs ?].
    destruct IHf2 as [ys ?].
    exists (xs +++ ys).
    destruct (Term_to_ArrowList_work dom f2); [|discriminate].
    destruct s; simpl.
    destruct (Pos.eq_dec x0 x); [|discriminate]; subst.
    unfold Term_to_ArrowList_work_obligation_4.
    destruct (Term_to_ArrowList_work x f1); [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x0 cod); [|discriminate]; subst.
    simpl in *.
    inversion e; subst.
    inversion e0; subst.
    reflexivity.
Defined.

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
