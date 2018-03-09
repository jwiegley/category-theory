Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.

Require Import Equations.Equations.
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
Require Import Solver.Normal.Valid.
Require Import Solver.Normal.Valid.Sound.
Require Import Solver.Normal.Valid.Adjoint.
Require Import Solver.Normal.Category.

Generalizable All Variables.

Section Subst.

Context `{Env}.

Definition rev_arr_equiv {cod dom} (x y : RevArrow cod dom) : Type :=
  arr x = arr y.
Arguments rev_arr_equiv {cod dom} x y.

Program Instance rev_arr_equivalence {j i} :
  Equivalence (@rev_arr_equiv j i).
Next Obligation.
  unfold rev_arr_equiv.
  repeat intro.
  now symmetry.
Qed.
Next Obligation.
  unfold rev_arr_equiv.
  repeat intro.
  now transitivity (arr y).
Qed.

Program Instance rev_arr_Setoid {i j} : Setoid (RevArrow i j) := {
  equiv := rev_arr_equiv;
  setoid_equiv := rev_arr_equivalence
}.

Program Instance rev_arr_equiv_dec {j i} :
  EquivDec (B:=RevArrow) (H:=@rev_arr_Setoid j i).
Next Obligation.
  unfold CEquivalence.equiv, rev_arr_equiv, complement.
  destruct x, y; simpl.
  destruct (EqDec.eq_dec arr arr0); subst; auto.
    exact (Some eq_refl).
  exact None.
Defined.

Lemma rev_arr_eqb_equiv {cod dom} (f g : RevArrow cod dom) :
  rev_arr_equiv f g -> mor f ≈ mor g.
Proof.
  unfold rev_arr_equiv; intros.
  induction f, g; simpl in *.
  subst.
  rewrite present in present0.
  inversion present0.
  do 2 (apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Eq_eq_dec]).
  now subst.
Qed.

Lemma option_map_Proper `{Setoid A} `{Setoid B} (f : A -> B) :
  Proper (equiv ==> equiv) f ->
  Proper (equiv ==> equiv) (option_map f).
Proof. proper; destruct x, y; simpl; auto. Defined.

Lemma getArrMorph_Proper {dom cod} :
  Proper (tlist_equiv (B:=RevArrow) (@rev_arr_Setoid) ==> equiv)
         (@getArrMorph _ dom cod).
Proof.
  proper.
  induction x; dependent elimination y; simpl.
  - cat.
  - inversion X.
  - inversion X.
  - simpl in X.
    unfold TList.tlist_equiv_obligation_1 in X.
    destruct (EqDec.eq_dec j0 j); [|contradiction].
    subst.
    destruct X.
    rewrite (IHx xs).
      comp_right.
      now apply rev_arr_eqb_equiv.
    exact t.
Defined.

Definition ArrowList_find
           {j k : obj_idx} (sub : ArrowList j k)
           {i l : obj_idx} (big : ArrowList i l) :
  option (ArrowList k l * ArrowList i j) :=
  tlist_find_wlist (B:=RevArrow)
                   (@rev_arr_Setoid)
                   (@rev_arr_equiv_dec)
                   (i:=l) (j:=k) (k:=j) (l:=i) sub big.

Definition ArrowList_find_app
           {j k : obj_idx} (sub : ArrowList j k)
           {i l : obj_idx} (big : ArrowList i l) {pre post} :
  ArrowList_find sub big = Some (pre, post)
      -> tlist_equiv (@rev_arr_Setoid) big (pre +++ sub +++ post) :=
  fun H =>
    tlist_find_wlist_app (B:=RevArrow)
                         (@rev_arr_Setoid)
                         (@rev_arr_equiv_dec)
                         (i:=l) (j:=k) (k:=j) (l:=i)
                         sub big H.

(** The job of [rewrite_arrows] is, given two arrows being compared for
equivalence, and another pair of equivalent arrows, and a witness to the fact
that the first of the second pair is somewhere within the first arrow of the
first pair, we can rewrite a goal state in terms of denoted terms into a goal
comparing arrowlists after the rewrite has been applied. *)

Lemma rewrite_arrows {dom cod} {f f' g g' i j h h' k k' a b} :
  ∀ (Hf : termD dom cod f = Some f')
    (Hg : termD dom cod g = Some g')
    (Hh : termD i j h = Some h')
    (Hk : termD i j k = Some k'),
    let fs := `1 (Term_to_ArrowList_sound Hf) in
    let gs := `1 (Term_to_ArrowList_sound Hg) in
    let hs := `1 (Term_to_ArrowList_sound Hh) in
    ArrowList_find hs fs = Some (a, b)
      -> a +++ hs +++ b ≈ gs
      -> termD dom cod f ≈ termD dom cod g.
Proof.
  intros.
  rewrite !termD_getMorph_fromTerm.
  remember (Term_to_ArrowList_sound Hf) as HHf; destruct HHf.
  remember (Term_to_ArrowList_sound Hg) as HHg; destruct HHg.
  remember (Term_to_ArrowList_sound Hh) as HHh; destruct HHh.
  rewrite e, e0; simpl.
  unfold fs in *; clear fs.
  unfold gs in *; clear gs.
  unfold hs in *; clear hs.
  simpl in *.
  pose proof (ArrowList_find_app x1 x (pre:=a) (post:=b) H0).
  apply getArrMorph_Proper in X0.
  now rewrite X0.
Defined.

Print Assumptions rewrite_arrows.

End Subst.
