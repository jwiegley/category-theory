Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Category.Lib.TList.
Require Export Category.Solver.Denote.

Generalizable All Variables.

Import VectorNotations.

Definition Arrows {a} (tys : Vector.t obj_pair a) (dom cod : obj_idx) :=
  tlist (A:=obj_idx)
        (fun c d => { f : arr_idx a & d = fst (tys[@f])
                                    & c = snd (tys[@f]) }) cod dom.

Global Instance positive_EqDec : EqDec positive := {
  eq_dec := Eq_eq_dec
}.

Section Normal.

Context `{Env}.

Import EqNotations.

Global Program Instance arrow_EqDec (i j : obj_idx) :
  EqDec {f : arr_idx num_arrs & i = fst (nth tys f) & j = snd (nth tys f)}.
Next Obligation.
  destruct (Eq_eq_dec x y); subst.
    left.
    f_equal; apply eq_proofs_unicity.
  right; intro.
  apply n.
  now inv H0.
Defined.

Fixpoint arrows `(t : Term tys d c) : Arrows tys d c :=
  match t with
  | Ident    => tnil
  | Morph a  => existT2 _ _ a eq_refl eq_refl ::: tnil
  | Comp f g => arrows f +++ arrows g
  end.

Fixpoint unarrows `(t : Arrows tys d c) : Term tys d c :=
  match t with
  | tnil => Ident
  | existT2 _ _ x Hd Hc ::: xs =>
    Comp (rew <- [fun x => Term _ _ x] Hc in
          rew <- [fun x => Term _ x _] Hd in Morph x) (unarrows xs)
  end.

Theorem arrows_unarrows d c (xs : Arrows tys d c) : arrows (unarrows xs) = xs.
Proof.
  induction xs; simpl; auto.
  destruct b. simpl.
  rewrite IHxs.
  simpl_eq.
  dependent elimination e0; simpl.
  dependent elimination e; simpl.
  dependent elimination xs; simpl; auto.
Qed.

Theorem unarrows_app d m c (t1 : Arrows tys m c) (t2 : Arrows tys d m) :
  termD (unarrows (t1 +++ t2)) ≈ termD (Comp (unarrows t1) (unarrows t2)).
Proof.
  induction t1; simpl; cat.
  destruct b.
  simpl_eq.
  dependent elimination e0; simpl.
  dependent elimination e; simpl.
  destruct t2; simpl; cat.
  comp_left.
  apply IHt1.
Defined.

Theorem unarrows_arrows d c (t : Term tys d c) :
  termD (unarrows (arrows t)) ≈ termD t.
Proof.
  induction t; simpl; cat.
  rewrite unarrows_app; simpl.
  now rewrite IHt1, IHt2.
Defined.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv _ _ f g => termD (unarrows (arrows f)) ≈ termD (unarrows (arrows g))
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Theorem exprAD_sound (e : Expr) : exprAD e -> exprD e.
Proof.
  induction e; intuition; simpl in *.
  now rewrite !unarrows_arrows in X.
Defined.

End Normal.
