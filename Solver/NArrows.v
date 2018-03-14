Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Category.Lib.TList.
Require Export Category.Lib.NETList.
Require Export Category.Solver.Arrows.

Generalizable All Variables.

Import VectorNotations.

Section NArrows.

Context `{Env}.

Import EqNotations.

(*
Fixpoint arrowsD `(t : Arrows tys d c) : objs d ~> objs c :=
  match t with
  | tnil => id
  | tcons _ f fs =>
    match f with
      existT2 _ _ f H1 H2 =>
      rew <- [fun x => _ ~> objs x] H2 in
        helper (ith arrs f) ∘ rew [fun x => _ ~> objs x] H1 in arrowsD fs
    end
  end.

Theorem arrowsD_app d m c (t1 : Arrows tys m c) (t2 : Arrows tys d m) :
  arrowsD (t1 +++ t2) ≈ arrowsD t1 ∘ arrowsD t2.
Proof.
  induction t1; simpl; cat.
  destruct b; subst.
  simpl_eq.
  destruct t2; simpl; cat.
  comp_left.
  apply IHt1.
Qed.

Theorem term_arrows `(f : Term tys d c) : termD f ≈ arrowsD (arrows f).
Proof.
  induction f; simpl; cat.
  now rewrite arrowsD_app, IHf1, IHf2.
Qed.
*)

Definition NArrows {a} (tys : Vector.t obj_pair a) (dom cod : obj_idx) :=
  netlist (A:=obj_idx) (Arr tys) cod dom.

Fixpoint unnarrows `(t : NArrows tys d c) : Term tys d c :=
  match t with
  | tfin (existT2 _ _ x Hd Hc) =>
    rew <- [fun x => Term _ _ x] Hc in
    rew <- [fun x => Term _ x _] Hd in Morph x
  | tadd _ (existT2 _ _ x Hd Hc) xs =>
    Comp (rew <- [fun x => Term _ _ x] Hc in
          rew <- [fun x => Term _ x _] Hd in Morph x) (unnarrows xs)
  end.

Fixpoint winnow `(t : Arrows tys d c) : NArrows tys d c + { d = c } :=
  match t with
  | tnil => inright eq_refl
  | tcons _ f fs =>
    inleft (match winnow fs with
            | inright H => tfin (rew <- [fun x => Arr _ _ x] H in f)
            | inleft fs => f :::: fs
            end)
  end.

Theorem unnarrows_arrows d c (t : Term tys d c) :
  termD (match winnow (arrows t) with
         | inright H => rew H in Ident
         | inleft f => unnarrows f
         end) ≈ termD t.
Proof.
  symmetry.
  rewrite <- unarrows_arrows.
  induction (arrows t); simpl; cat.
  destruct b; subst; simpl_eq; simpl.
  destruct (winnow a); simpl.
    comp_left.
    apply IHa.
    apply unnarrows.
    assumption.
  dependent elimination e; simpl in *.
  rewrite IHa; cat.
  apply unarrows.
  assumption.
Qed.

Fixpoint narrowsD `(t : NArrows tys d c) : objs d ~> objs c :=
  match t with
  | tfin f =>
    match f with
      existT2 _ _ f H1 H2 =>
      rew <- [fun x => objs x ~> _] H1 in
      rew <- [fun x => _ ~> objs x] H2 in helper (ith arrs f)
    end
  | tadd _ f fs =>
    match f with
      existT2 _ _ f H1 H2 =>
      rew <- [fun x => _ ~> objs x] H2 in
        helper (ith arrs f) ∘ rew [fun x => _ ~> objs x] H1 in narrowsD fs
    end
  end.

Theorem term_unnarrows `(f : NArrows tys d c) :
  termD (unnarrows f) ≈ narrowsD f.
Proof.
  induction f; simpl;
  destruct b; subst; simpl; simpl_eq; cat.
Qed.

Theorem term_narrows `(f : Term tys d c) :
  termD f ≈ match winnow (arrows f) with
            | inright H => rew [fun x => _ ~> objs x] H in @id cat (objs d)
            | inleft f => narrowsD f
            end.
Proof.
  rewrite <- unarrows_arrows.
  induction (arrows f); simpl; cat.
  destruct b; subst; simpl.
  clear IHa.
  rewrite <- unnarrows_arrows.
  rewrite arrows_unarrows.
  destruct (winnow a); simpl; simpl_eq.
    now rewrite term_unnarrows.
  subst; cat.
Qed.

End NArrows.
