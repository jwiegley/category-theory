Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Applicative.Proofs.
Require Import Category.Theory.Coq.Monad.Proofs.
Require Import Category.Theory.Coq.Maybe.

Generalizable All Variables.

Import MonadNotations.

Lemma Maybe_choose_spec {a} {x y : Maybe a} :
  isJust (x <|> y) = (isJust x || isJust y)%bool.
Proof.
  destruct x; auto.
Qed.

Lemma fmap_endo_just {c} (f : c → c) (m : Maybe c) (x : c) :
  f <$> m = Just x <-> exists y, x = f y /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - inversion_clear H.
    eexists; eauto.
  - destruct H, H; subst.
    now inversion_clear H0.
  - discriminate.
  - destruct H, H; discriminate.
Qed.

Lemma fmap_endo_nothing {c} (f : c → c) (m : Maybe c) :
  f <$> m = Nothing <-> m = Nothing.
Proof. induction m; simpl; intuition auto; discriminate. Qed.

Lemma ap_endo_just {c} (f : c → c → c) (m n : Maybe c) (x : c) :
  f <$> m <*> n = Just x
    <-> exists y z, x = f y z /\ m = Just y /\ n = Just z.
Proof.
  induction m, n; simpl; split; intros.
  - inversion_clear H.
    eexists; eauto.
  - destruct H, H, H, H0; subst.
    inversion_clear H0.
    now inversion_clear H1.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
Qed.

Lemma ap_endo_nothing {c} (f : c → c → c) (m n : Maybe c) :
  f <$> m <*> n = Nothing <-> m = Nothing \/ n = Nothing.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.

Lemma bind_endo_just {c} (f : c → Maybe c) (m : Maybe c) (x : c) :
  m >>= f = Just x <-> exists y, f y = Just x /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - destruct (f a) eqn:?.
    + inversion H; subst.
      now eexists; eauto.
    + unfold bind in H.
      simpl in H.
      congruence.
  - destruct H, H.
    inversion H0; subst.
    now unfold bind; simpl.
  - discriminate.
  - destruct H, H.
    discriminate.
Qed.

Lemma bind_endo_nothing {c} (f : c → Maybe c) (m : Maybe c) :
  m >>= f = Nothing <-> m = Nothing \/ exists y, f y = Nothing /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - destruct (f a) eqn:?.
    + unfold bind in H; simpl in H.
      congruence.
    + right.
      now eexists; eauto.
  - destruct H.
    + discriminate.
    + firstorder eauto.
      inversion_clear H0.
      now unfold bind; simpl.
  - now left.
  - reflexivity.
Qed.

Lemma alt_endo_just {c} (m n : Maybe c) (x : c) :
  m <|> n = Just x <-> m = Just x \/ (m = Nothing /\ n = Just x).
Proof. induction m; simpl; intuition auto; discriminate. Qed.

Lemma alt_endo_nothing {c} (m n : Maybe c) :
  m <|> n = Nothing <-> m = Nothing /\ n = Nothing.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.

Program Definition Maybe_Functor : IsFunctor Maybe_Functor := {|
  a_fmap := Maybe_Functor;
|}.
Next Obligation.
  proper.
  destruct x1; simpl; auto.
  now rewrite H.
Qed.
Next Obligation.
  now destruct x0.
Qed.
Next Obligation.
  now destruct x0.
Qed.
