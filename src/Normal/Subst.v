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
Require Import Solver.Expr.Valid.
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

Definition arr_equiv {dom cod} (x y : Arrow dom cod) : Type :=
  arr x = arr y.
Arguments arr_equiv {dom cod} x y.

Program Instance arr_equivalence {i j} : Equivalence (@arr_equiv i j).
Next Obligation.
  unfold arr_equiv.
  repeat intro.
  now symmetry.
Qed.
Next Obligation.
  unfold arr_equiv.
  repeat intro.
  now transitivity (arr y).
Qed.

Program Instance arr_equiv_dec {i j} :
  EquivDec (B:=Arrow) (i:=i) (j:=j) (@arr_equiv i j)
           (H:=@arr_equivalence i j).
Next Obligation.
  unfold CEquivalence.equiv, arr_equiv, complement.
  destruct x, y; simpl.
  destruct (EqDec.eq_dec arr arr0); auto.
Defined.

Lemma arr_eqb_equiv {dom cod} (f g : Arrow dom cod) :
  arr_equiv f g -> mor f ≈ mor g.
Proof.
  unfold arr_equiv; intros.
  induction f, g; simpl in *.
  subst.
  rewrite present in present0.
  inversion present0.
  do 2 (apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Eq_eq_dec]).
  now subst.
Qed.

Lemma rewrite_arrows {dom cod} :
  ∀ f f' (Hf : termD dom cod f = Some f')
    g g' (Hg : termD dom cod g = Some g'),
  termD_ArrowList Hf ≈ termD_ArrowList Hg ->
  termD dom cod f ≈ termD dom cod g.
Proof.
  intros.
  rewrite !termD_getMorph_fromTerm.
  destruct (fromTerm dom cod f) eqn:?,
           (fromTerm dom cod g) eqn:?.
  simpl.
  admit.
  rewrite !getMorph_getArrMorph.
  red.
  rewrite Hf, Hg.
  f_equiv.
  red in X.
  (* jww (2018-03-08): Need a way to turn termD = Some into a ValidTerm,
     and then from there go to an ArrowList. *)
Abort.

End Subst.
