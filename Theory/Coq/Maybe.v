Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.
Require Import Category.Theory.Coq.Traversable.

Generalizable All Variables.

Notation Maybe   := option.
Notation Nothing := None.
Notation Just    := Some.

Definition fromMaybe `(x : a) (my : Maybe a) : a :=
  match my with
  | Just z  => z
  | Nothing => x
  end.

Definition maybe `(x : b) `(f : a → b) (my : Maybe a) : b :=
  match my with
  | Just z  => f z
  | Nothing => x
  end.

Definition Maybe_map `(f : X → Y) (x : Maybe X) : Maybe Y :=
  match x with
  | Nothing => Nothing
  | Just x' => Just (f x')
  end.

#[export]
Instance Maybe_Functor : Functor Maybe := {
  fmap := @Maybe_map
}.

Definition Maybe_apply {X Y} (f : Maybe (X → Y)) (x : Maybe X) : Maybe Y :=
  match f with
  | Nothing => Nothing
  | Just f' => match x with
    | Nothing => Nothing
    | Just x' => Just (f' x')
    end
  end.

#[export]
Instance Maybe_Applicative : Applicative Maybe := {
  pure := @Just;
  ap := @Maybe_apply
}.

Definition Maybe_join {X} (x : Maybe (Maybe X)) : Maybe X :=
  match x with
  | Nothing => Nothing
  | Just Nothing => Nothing
  | Just (Just x') => Just x'
  end.

Definition Maybe_bind {X Y} (m : Maybe X) (f : X → Maybe Y) : Maybe Y :=
  match m with
  | Nothing => Nothing
  | Just m' => f m'
  end.

#[export]
Instance Maybe_Monad : Monad Maybe := {
  bind := @Maybe_bind
}.

Definition isJust {a} (x : Maybe a) := if x then true else false.

Definition Maybe_choose {a} (x y : Maybe a) : Maybe a :=
  match x with
  | Nothing => y
  | Just _  => x
  end.

#[export]
Instance Maybe_Alternative : Alternative Maybe := {
  empty  := @Nothing;
  choose := @Maybe_choose
}.

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

Definition Maybe_append `{Semigroup a} (x y : Maybe a) : Maybe a :=
  match x, y with
  | Nothing, x     => x
  | x, Nothing     => x
  | Just x, Just y => Just (x ⊗ y)
  end.

#[global]
Program Instance Semigroup_Maybe `{Semigroup a} : Semigroup (Maybe a) := {
  mappend := Maybe_append
}.

#[export]
Program Instance Monoid_option `{Monoid a} : Monoid (Maybe a) := {
  mempty := None
}.

#[export]
Instance Maybe_Traversable : Traversable Maybe := {
  sequence := λ _ _ _ _ x,
    match x with
    | Nothing => pure Nothing
    | Just x  => fmap Just x
    end
}.

#[export]
Instance Maybe_Tupersable {rep} : Tupersable rep Maybe := {
  sequenceT := fun A (s : rep) x =>
    match x with
    | Nothing => (s, Nothing)
    | Just (s', x)  => (s', Just x)
    end
}.
