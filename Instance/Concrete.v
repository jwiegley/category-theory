Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Coq.MSets.MSetInterface.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Module Concrete (O : DecidableType) (S : WSetsOn O).

Fixpoint In' (f : O.t * O.t) (l : list (O.t * O.t)) : Prop :=
    match l with
      | nil => False
      | (x, y) :: m => (O.eq (fst f) x /\ O.eq (snd f) y) \/ In f m
    end.

Fixpoint Subset' (X Y : O.t) (l : list (O.t * O.t)) : list (O.t * O.t) :=
  filter (fun p => if O.eq_dec (fst p) X
                   then if O.eq_dec (snd p) Y
                        then true
                        else false
                   else false) l.
Arguments Subset' X Y l : simpl never.

Lemma Subset'_cons X Y x xs :
  Subset' X Y (x :: xs)
    = if O.eq_dec (fst x) X
      then if O.eq_dec (snd x) Y
           then x :: Subset' X Y xs
           else Subset' X Y xs
      else Subset' X Y xs.
Proof.
  induction xs; unfold Subset'; simpl;
  destruct (O.eq_dec (fst x) X);
  destruct (O.eq_dec (snd x) Y); auto.
Qed.

Lemma In_Subset'_inv X Y x y xs :
  In (x, y) (Subset' X Y xs) -> O.eq x X ∧ O.eq y Y.
Proof.
  induction xs; simpl; intros; [tauto|].
  rewrite Subset'_cons in H.
  destruct (O.eq_dec (fst a) X);
  destruct (O.eq_dec (snd a) Y); auto.
  destruct H; subst; auto.
Qed.

Local Obligation Tactic := program_simpl.

Program Instance Concrete (Obs : S.t) (Homs : list (O.t * O.t)) : Category := {
  ob  := { x : O.t | S.In x Obs };
  hom := fun X Y =>
    { f : list (O.t * O.t)
    | ∀ h, In' h f <-> In' h ((X, Y) :: Subset' X Y  Homs) }%type;
  homset := fun X Y =>
    {| equiv := fun f g => ∀ h, In' h f <-> In' h g |}%type;
  id := fun X => exist _ ((X, X) :: nil) _
}.
Next Obligation.
  equivalence.
  - apply H1; assumption.
  - apply H1; assumption.
  - apply H2, H1; assumption.
  - apply H1, H2; assumption.
Qed.
Next Obligation.
  firstorder.
  apply In_Subset'_inv in H0.
  constructor; auto.
Qed.
Next Obligation. firstorder. Defined.
Next Obligation.
  proper; simpl in *;
  destruct x, x0, y, y0; simpl in *;
  firstorder.
Qed.
Next Obligation.
  firstorder; simpl in *.
  - destruct f.
      pose proof (proj2 (H (X, Y))); firstorder.
      specialize (H4 (reflexivity _) (reflexivity _)).
      contradiction.
    pose proof (proj2 (H (t, t0))); firstorder.
  - destruct f.
      pose proof (proj2 (H (X, Y))); firstorder.
      specialize (H3 (reflexivity _) (reflexivity _)).
      contradiction.
    pose proof (proj2 (H (t, t0))); firstorder.
  - destruct f.
      contradiction.
    pose proof (proj1 (H (t, t0))); firstorder.
Qed.
Next Obligation.
  firstorder; simpl in *.
  - destruct f.
      pose proof (proj2 (H (X, Y))); firstorder.
      specialize (H4 (reflexivity _) (reflexivity _)).
      contradiction.
    pose proof (proj2 (H (t, t0))); firstorder.
  - destruct f.
      pose proof (proj2 (H (X, Y))); firstorder.
      specialize (H3 (reflexivity _) (reflexivity _)).
      contradiction.
    pose proof (proj2 (H (t, t0))); firstorder.
  - destruct f.
      contradiction.
    pose proof (proj1 (H (t, t0))); firstorder.
Qed.
Next Obligation. firstorder. Qed.

End Concrete.
