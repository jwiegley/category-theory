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

(*

jww (2018-03-05): This is only possible if we can assert UIP of positive map
lookups on the same key, and finding the same element.

Equations ValidArrow_eq_dec {dom cod fs}
          (f g : ValidArrow dom cod fs) : { f = g } + { f ≠ g } :=
  ValidArrow_eq_dec f g by rec fs (MR lt (@length arr_idx)) :=
  ValidArrow_eq_dec IdentityArrow IdentityArrow := left eq_refl;
  ValidArrow_eq_dec (ComposedArrow midf _ _ _ _ _ IHf)
                    (ComposedArrow midg _ _ _ _ _ IHg)
    <= Eq_eq_dec midf midg => {
         | left eq_refl := _ (ValidArrow_eq_dec IHf IHg);
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

Definition getArrList {dom cod} `(a : ValidArrow dom cod fs) :
  list arr_idx := fs.
Arguments getArrList {dom cod fs} a /.

Equations getArrMorph {dom cod} `(a : ValidArrow dom cod fs) :
  objs dom ~> objs cod :=
  getArrMorph IdentityArrow := id;
  getArrMorph (ComposedArrow f _ _ g) := f ∘ getArrMorph g.

Definition ValidArrow_size {dom cod} `(a : ValidArrow dom cod fs) : nat :=
  length (getArrList a).

Lemma ValidArrow_compose_inv {dom cod fs gs} :
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

Lemma ValidArrow_compose {dom mid cod fs gs} :
  ValidArrow mid cod fs
    -> ValidArrow dom mid gs
    -> ValidArrow dom cod (fs ++ gs).
Proof.
  intros.
  generalize dependent mid.
  generalize dependent cod.
  induction fs; simpl; intros; auto;
  inversion X; subst; auto.
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
  destruct (ValidArrow_compose_inv X), p.
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

Lemma getArrMorph_ValidArrow_compose {dom mid cod}
          `(f : ValidArrow mid cod xs)
          `(g : ValidArrow dom mid ys) :
  getArrMorph (ValidArrow_compose f g) ≈ getArrMorph f ∘ getArrMorph g.
Proof.
  induction f; simpl.
    rewrite getArrMorph_equation_1; cat.
  rewrite !getArrMorph_equation_2.
  rewrite IHf; cat.
Qed.

Equations ValidArrow_eq_arr {dom cod fs}
          (f g : ValidArrow dom cod fs) : getArrMorph f = getArrMorph g :=
  ValidArrow_eq_arr f g by rec fs (MR lt (@length arr_idx)) :=
  ValidArrow_eq_arr IdentityArrow IdentityArrow := eq_refl;
  ValidArrow_eq_arr (ComposedArrow f _ _ f') (ComposedArrow g _ _ g') := _.
Next Obligation.
  rewrite !getArrMorph_equation_2.
  destruct wildcard7;
  [ inversion f'; inversion g'; subst
  | pose proof (ValidArrow_cod_eq f' g'); subst ];
  rewrite (ValidArrow_eq_arr _ _ _ f' g') by constructor;
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

(*
Equations ValidArrow_split {dom cod fs}
          (f : ValidArrow dom cod fs) gs
          (is_present : sublistp gs fs = true) :
  ∃ i j xs ys, (ValidArrow j cod xs * ValidArrow i j gs * ValidArrow dom i ys) :=
  ValidArrow_split f [] _ :=
    (cod; (cod; ([]; (fs; (IdentityArrow cod, IdentityArrow cod, f)))));
  ValidArrow_split (ComposedArrow f f' fs Hf IHf) gs _
    <= list_eq_dec Eq_eq_dec (firstn (length gs) (f :: fs)) (f :: fs) => {
      | left _ =>
        (_; (_; (_; (_; (_, _, _)))));
      | right _ =>
        match ValidArrow_split IHf gs _ with
          (i; (j; (xs; (ys; (beg, mid, fin))))) => _
        end
    }.
Next Obligation.
Abort.
*)

Import EqNotations.

Lemma ValidArrow_Identity {dom} (f : ValidArrow dom dom []) :
  getArrMorph f ≈ id.
Proof.
  dependent elimination f as [IdentityArrow].
  reflexivity.
Qed.

Lemma ValidArrow_Compose {dom cod}
      `(f : ValidArrow dom cod (gs ++ hs)) :
  ∃ mid (g : ValidArrow mid cod gs)
        (h : ValidArrow dom mid hs),
    getArrMorph f ≈ getArrMorph g ∘ getArrMorph h.
Proof.
  destruct (ValidArrow_compose_inv f), p.
  exists x, v0, v.
  generalize dependent cod.
  induction gs; simpl; intros.
    inversion v0; subst.
    rewrite (ValidArrow_eq_arr f v); cat.
    rewrite (ValidArrow_Identity v0); cat.
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

End NormalValid.
