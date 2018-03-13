Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Category.Lib.TList.
Require Export Category.Lib.NETList.
Require Export Category.Solver.Denote.

Generalizable All Variables.

Import VectorNotations.

Definition Arr {a} (tys : Vector.t obj_pair a) (cod dom : obj_idx) :=
  { f : arr_idx a & dom = fst (tys[@f]) & cod = snd (tys[@f]) }.

Definition NEArrows {a} (tys : Vector.t obj_pair a) (dom cod : obj_idx) :=
  netlist (A:=obj_idx) (Arr tys) cod dom.

Definition Arrows {a} (tys : Vector.t obj_pair a) (dom cod : obj_idx) :=
  tlist (A:=obj_idx) (Arr tys) cod dom.

Global Instance positive_EqDec : EqDec positive := {
  eq_dec := Eq_eq_dec
}.

Section Normal.

Context `{Env}.

Import EqNotations.

Local Obligation Tactic := unfold Arr; program_simpl.

Global Program Instance arrow_EqDec (i j : obj_idx) : EqDec (Arr tys i j).
Next Obligation.
  destruct (Eq_eq_dec x y); subst.
    left.
    f_equal; apply eq_proofs_unicity.
  right; intro.
  apply n.
  now inv H0.
Defined.

Fixpoint winnow `(t : Arrows tys d c) : NEArrows tys d c + { d = c } :=
  match t with
  | tnil => inright eq_refl
  | tcons _ f fs =>
    inleft (match winnow fs with
            | inright H => tfin (rew <- [fun x => Arr _ _ x] H in f)
            | inleft fs => f :::: fs
            end)
  end.

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

Fixpoint unnearrows `(t : NEArrows tys d c) : Term tys d c :=
  match t with
  | tfin (existT2 _ _ x Hd Hc) =>
    rew <- [fun x => Term _ _ x] Hc in
    rew <- [fun x => Term _ x _] Hd in Morph x
  | tadd _ (existT2 _ _ x Hd Hc) xs =>
    Comp (rew <- [fun x => Term _ _ x] Hc in
          rew <- [fun x => Term _ x _] Hd in Morph x) (unnearrows xs)
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

Theorem unnearrows_arrows d c (t : Term tys d c) :
  termD (match winnow (arrows t) with
         | inright H => rew H in Ident
         | inleft f => unnearrows f
         end) ≈ termD t.
Proof.
  symmetry.
  rewrite <- unarrows_arrows.
  induction (arrows t); simpl; cat.
  destruct b; subst; simpl_eq; simpl.
  destruct (winnow a); simpl.
    comp_left.
    apply IHa.
    apply unnearrows.
    assumption.
  dependent elimination e; simpl in *.
  rewrite IHa; cat.
  apply unarrows.
  assumption.
Defined.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv d _ f g =>
    termD (match winnow (arrows f) with
         | inright H => rew H in Ident
         | inleft f => unnearrows f
         end)
      ≈
    termD (match winnow (arrows g) with
           | inright H => rew H in Ident
           | inleft g => unnearrows g
           end)
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Theorem exprAD_sound (e : Expr) : exprAD e -> exprD e.
Proof.
  induction e; intuition; simpl in *.
  now rewrite !unnearrows_arrows in X.
Defined.

End Normal.
