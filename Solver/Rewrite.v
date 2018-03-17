Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Category.Lib.TList.
Require Export Category.Solver.NArrows.

Generalizable All Variables.

Section Rewrite.

Context `{Env}.

Import VectorNotations.
Import EqNotations.

Lemma Term_find_app
      {j k} (g h : Term tys j k)
      {i l} (f : Term tys i l) {pre post} :
  tlist_find_sublist (arrows g) (arrows f) = Some (pre, post)
    -> termD g ≈ termD h
    -> termD f ≈
         match narrows pre, narrows post with
         | inright H1, inright H2 =>
           rew <- [fun x => objs[@x] ~> _] H2 in
           rew [fun x => _ ~> objs[@x]] H1 in termD h
         | inright H, inleft post =>
           rew [fun x => _ ~> objs[@x]] H in (termD h ∘ narrowsD post)
         | inleft pre, inright H =>
           rew <- [fun x => objs[@x] ~> _] H in (narrowsD pre ∘ termD h)
         | inleft pre, inleft post =>
           narrowsD pre ∘ termD h ∘ narrowsD post
         end.
Proof.
  intros.
  rewrite <- unarrows_arrows.
  rewrite (tlist_find_sublist_app _ _ H0).
  repeat (rewrite unarrows_app; simpl).
  rewrite unarrows_arrows.
  rewrite X.
  rewrite <- unnarrows_arrows.
  rewrite <- (unnarrows_arrows _ _ (unarrows post)) at 1.
  rewrite !arrows_unarrows.
  destruct (narrows pre), (narrows post);
  simpl_eq; subst; simpl;
  rewrite ?term_unnarrows; cat.
Qed.

End Rewrite.

Require Export Category.Solver.Reify.

Ltac rrewrite H := revert H; reify_terms_and_then
  ltac:(fun env g =>
          change (@exprD env g);
          red;
          match goal with
          | [ H0 : @termD ?E ?A ?B ?X ≈ @termD _ _ _ ?Y
            |- @termD _ ?D ?C ?F ≈ termD ?G ] =>
            let o := fresh "o" in
            pose (tlist_find_sublist (arrows X) (arrows F)) as o;
            vm_compute in o;
            etransitivity;
            [apply (@Term_find_app E A B X Y D C F _ _ (@eq_refl _ o)); auto|];
            clear o;
            vm_compute
          end;
          vm_compute in H;
          match goal with [ E : Env |- _ ] => clear E end).

Example sample_3 :
  ∀ (C : Category) (x y z w : C)
    (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z),
    g ∘ h ≈ i ->
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  (* Set Ltac Profiling. *)
  Fail Time rrewrite X.
  (* Show Ltac Profile. *)
  Fail rewrite <- X; cat.
  Fail apply comp_assoc.
  cat.
Qed.

Print Assumptions sample_3.
