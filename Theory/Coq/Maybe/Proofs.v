Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Applicative.Proofs.
Require Import Category.Theory.Coq.Monad.Proofs.
Require Import Category.Theory.Coq.Maybe.

Generalizable All Variables.

(** Law proofs for the Maybe/option [1 + a] instances *)

(* nLab: https://ncatlab.org/nlab/show/maybe+monad
   Wikipedia: https://en.wikipedia.org/wiki/Option_type

   The instances themselves live in [Theory/Coq/Maybe.v]; here we record their
   lawfulness.  The final [Maybe_Functor : IsFunctor] discharges the two functor
   laws -- identity [fmap id = id] and composition [fmap (g ∘ f) = fmap g ∘ fmap f]
   -- by exhibiting the operation as a genuine endofunctor on [Coq] (an
   [AFunctor]), exactly as the sibling [Either] and [Tuple] proof files do.

   The preceding lemmas are characterisation ("spec") lemmas describing each
   operation by its action on [Just]/[Nothing].  They make precise the equations
   the sources give for the functor/applicative/monad/Alternative structure --
   [fmap f Nothing = Nothing], [Just f <*> Just x = Just (f x)],
   [Nothing >>= f = Nothing], [Just x >>= f = f x], left-biased [<|>] -- as
   biconditionals on when a result is [Just x] versus [Nothing]. *)

Import MonadNotations.

(* [<|>] (left-biased choice) returns a [Just] iff either operand does. *)

Lemma Maybe_choose_spec {a} {x y : Maybe a} :
  isJust (x <|> y) = (isJust x || isJust y)%bool.
Proof.
  destruct x; auto.
Qed.

(* Functor: [fmap f m] is [Just x] exactly when [m = Just y] and [x = f y]. *)
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

(* Applicative: [f <$> m <*> n] is [Just x] exactly when both arguments are
   [Just] and [x] is their combination. *)
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

(* Monad: [m >>= f] is [Just x] exactly when [m = Just y] and [f y = Just x]. *)
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

(* Alternative: [m <|> n] is [Just x] via the left operand, or via the right
   when the left is [Nothing] (left-biased choice). *)
Lemma alt_endo_just {c} (m n : Maybe c) (x : c) :
  m <|> n = Just x <-> m = Just x \/ (m = Nothing /\ n = Just x).
Proof. induction m; simpl; intuition auto; discriminate. Qed.

Lemma alt_endo_nothing {c} (m n : Maybe c) :
  m <|> n = Nothing <-> m = Nothing /\ n = Nothing.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.

(* The lawful functor instance: [Maybe] is a genuine endofunctor on [Coq],
   discharging the identity and composition functor laws.  (The name reuses the
   source [Maybe_Functor] instance, as in the [Either]/[Tuple] proof files.) *)
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
