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

Definition NArrows {a} (tys : Vector.t obj_pair a) (dom cod : obj_idx) :=
  netlist (A:=obj_idx) (Arr tys) cod dom.

Fixpoint narrows `(t : Arrows tys d c) : NArrows tys d c + { d = c } :=
  match t with
  | tnil => inright eq_refl
  | tcons _ f fs =>
    inleft (match narrows fs with
            | inright H => tfin (rew <- [fun x => Arr _ _ x] H in f)
            | inleft fs => f :::: fs
            end)
  end.

Fixpoint unnarrows `(t : NArrows tys d c) : Term tys d c :=
  match t with
  | tfin (existT2 _ _ x Hd Hc) =>
    rew <- [fun x => Term _ _ x] Hc in
    rew <- [fun x => Term _ x _] Hd in Morph x
  | tadd _ (existT2 _ _ x Hd Hc) xs =>
    Comp (rew <- [fun x => Term _ _ x] Hc in
          rew <- [fun x => Term _ x _] Hd in Morph x) (unnarrows xs)
  end.

Theorem unnarrows_arrows d c (t : Term tys d c) :
  termD (match narrows (arrows t) with
         | inright H => rew H in Ident
         | inleft f => unnarrows f
         end) ≈ termD t.
Proof.
  symmetry.
  rewrite <- unarrows_arrows.
  induction (arrows t); simpl; cat.
  destruct b; subst; simpl_eq; simpl.
  destruct (narrows a); simpl.
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
  termD f ≈ match narrows (arrows f) with
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
  destruct (narrows a); simpl; simpl_eq.
    now rewrite term_unnarrows.
  subst; cat.
Qed.

End NArrows.
