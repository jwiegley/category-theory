Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Coq.Vectors.Vector.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
Require Import Category.Lib.IList.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Env.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.

Generalizable All Variables.

Import VectorNotations.

Definition Arr {a o} (tys : Vector.t (obj_pair o) a)
           (cod dom : obj_idx o) :=
  { f : arr_idx a & dom = fst (tys[@f]) & cod = snd (tys[@f]) }.

Definition Arrows {a o} (tys : Vector.t (obj_pair o) a)
           (dom cod : obj_idx o) :=
  tlist (Arr tys) cod dom.

Global Instance Fin_EqDec (n : nat) : EqDec (Fin.t n) := {
  eq_dec := Fin_eq_dec
}.

Section Arrows.

Context `{Env}.

Import EqNotations.

Local Obligation Tactic := unfold Arr; program_simpl.

Global Program Instance arrow_EqDec (i j : obj_idx num_objs) :
  EqDec (Arr tys i j).
Next Obligation.
Admitted.
(*   destruct (Eq_eq_dec x y) eqn:Heqe; subst. *)
(*     left. *)
(*     now f_equal; eapply eq_proofs_unicity. *)
(*   right; intro. *)
(*   apply n. *)
(*   now inv H0. *)
(* Defined. *)

Fixpoint arrows `(t : Term tys d c) : Arrows tys d c :=
  match t with
  | Ident    => tnil
  | Morph a  => existT2 _ _ a eq_refl eq_refl ::: tnil
  | Comp f g => arrows f +++ arrows g
  end.

Fixpoint arrowsD `(t : Arrows tys d c) : objs[@d] ~> objs[@c] :=
  match t with
  | tnil => id
  | tcons _ f fs =>
    match f with
      existT2 _ _ f H1 H2 =>
      rew <- [fun x => _ ~> objs[@x]] H2 in
        helper (ith arrs f)
          ∘ rew [fun x => _ ~> objs[@x]] H1 in arrowsD fs
    end
  end.

Fixpoint unarrows `(t : Arrows tys d c) : Term tys d c :=
  match t with
  | tnil => Ident
  | existT2 _ _ x Hd Hc ::: xs =>
    Comp (rew <- [fun x => Term _ _ x] Hc in
          rew <- [fun x => Term _ x _] Hd in Morph x) (unarrows xs)
  end.

Theorem arrows_unarrows d c (xs : Arrows tys d c) :
  arrows (unarrows xs) = xs.
Proof.
  induction xs; simpl; auto.
  destruct b; subst; simpl.
  rewrite IHxs.
  simpl_eq.
  dependent elimination xs; simpl; auto.
Qed.

Theorem unarrows_app d m c (t1 : Arrows tys m c) (t2 : Arrows tys d m) :
  termD (unarrows (t1 +++ t2)) ≈ termD (Comp (unarrows t1) (unarrows t2)).
Proof.
  induction t1; simpl; cat.
  destruct b; subst.
  simpl_eq.
  destruct t2; simpl; cat.
  comp_left.
  apply IHt1.
Qed.

Theorem unarrows_arrows d c (t : Term tys d c) :
  termD (unarrows (arrows t)) ≈ termD t.
Proof.
  induction t; simpl; cat.
  rewrite unarrows_app; simpl.
  now rewrite IHt1, IHt2.
Defined.

Fixpoint indices `(t : Arrows tys d c) : list (arr_idx num_arrs) :=
  match t with
  | tnil => List.nil
  | existT2 _ _ f _ _ ::: fs => f :: indices fs
  end.

Theorem indices_impl {d c} (x y : Arrows tys d c) :
  indices x = indices y -> x = y.
Proof.
  induction x; dependent elimination y;
  simpl; auto; intros.
  - destruct a.
    inv H0.
  - destruct b.
    inv H0.
  - destruct a, b.
    inv H0.
    f_equal; auto.
    f_equal; auto.
    Fail apply eq_proofs_unicity.
Admitted.

Theorem indices_app d m c (t1 : Arrows tys m c) (t2 : Arrows tys d m) :
  indices (t1 +++ t2) = (indices t1 ++ indices t2)%list.
Proof.
  induction t1; simpl in *; cat.
  destruct t2; simpl; cat.
    now rewrite List.app_nil_r.
  f_equal.
  rewrite <- tlist_app_comm_cons; simpl.
  rewrite IHt1; simpl.
  now destruct b, a.
Qed.

End Arrows.
