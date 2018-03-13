Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Category.Solver.Normal.

Generalizable All Variables.

Section Rewrite.

Context `{Env}.

Corollary termD_Comp `{Env} d m c (x : Term tys m c) (y : Term tys d m) :
  termD (Comp x y) ≈ termD x ∘ termD y.
Proof. reflexivity. Defined.

Definition Arrows_find
           {j k} (xs : Arrows tys j k)
           {i l} (ys : Arrows tys i l) :
  option (Arrows tys k l * Arrows tys i j) :=
  tlist_find_sublist xs ys.

Corollary Arrows_find_app
      {j k} (g : Arrows tys j k)
      {i l} (f : Arrows tys i l) {pre post} :
  Arrows_find g f = Some (pre, post)
    -> termD (unarrows f) ≈ termD (unarrows (pre +++ g +++ post)).
Proof. now intros; rewrite (tlist_find_sublist_app _ _ H0). Defined.

Import EqNotations.

Lemma Term_find_app
      {j k} (g h : Term tys j k)
      {i l} (f : Term tys i l) {pre post} :
  Arrows_find (arrows g) (arrows f) = Some (pre, post)
    -> termD g ≈ termD h
    -> termD f ≈
         match winnow pre, winnow post with
         | inright H1, inright H2 =>
           rew <- [fun x => objs x ~> _] H2 in
           rew [fun x => _ ~> objs x] H1 in termD h
         | inright H, _ =>
           rew [fun x => _ ~> objs x] H in (termD h ∘ termD (unarrows post))
         | _, inright H =>
           rew <- [fun x => objs x ~> _] H in (termD (unarrows pre) ∘ termD h)
         | _, _ =>
           termD (unarrows pre) ∘ termD h ∘ termD (unarrows post)
         end.
Proof.
  intros.
  rewrite <- unarrows_arrows.
  erewrite Arrows_find_app; eauto.
  repeat rewrite unarrows_app, termD_Comp.
  rewrite unarrows_arrows.
  rewrite X.
  destruct pre, post; simpl; cat.
Defined.

End Rewrite.
