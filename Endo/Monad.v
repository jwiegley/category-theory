Require Export Applicative.

Class Monad (M : Type -> Type) :=
{ is_applicative :> Applicative M

; mu : forall {X}, M (M X) -> M X

; monad_law_1 : forall {X}, mu ∘ fmap mu = (@mu X) ∘ mu
; monad_law_2 : forall {X}, mu ∘ fmap (@eta M is_applicative X) = id
; monad_law_3 : forall {X}, (@mu X) ∘ eta = id
; monad_law_4 : forall {X Y} (f : X -> Y), mu ∘ fmap (fmap f) = fmap f ∘ mu
}.

Notation "mu/ M" := (@mu M _ _) (at level 68).
Notation "mu/ M N" := (@mu (fun X => M (N X)) _ _) (at level 66).

Definition bind {M} `{Monad M} {X Y}
  (f : (X -> M Y)) (x : M X) : M Y := mu (fmap f x).

Notation "m >>= f" := (bind f m) (at level 67, left associativity).

Theorem monad_law_1_x
  : forall (M : Type -> Type) (m_dict : Monad M) A (x : M (M (M A))),
  mu (fmap mu x) = (@mu M m_dict A) (mu x).
Proof.
  intros.
  assert (mu (fmap mu x) = (mu ∘ fmap mu) x).
    unfold compose. reflexivity.
  assert (mu (mu x) = (mu ∘ mu) x).
    unfold compose. reflexivity.
  rewrite H. rewrite H0.
  rewrite monad_law_1.
  reflexivity.
Qed.

Theorem monad_law_2_x
  : forall (M : Type -> Type) (m_dict : Monad M) A (x : M A),
  mu (fmap (@eta M _ A) x) = x.
Proof.
  intros.
  assert (mu (fmap eta x) = (mu ∘ fmap eta) x).
    unfold compose. reflexivity.
  rewrite H.
  rewrite monad_law_2.
  reflexivity.
Qed.

Theorem monad_law_3_x
  : forall (M : Type -> Type) (m_dict : Monad M) A (x : M A),
  (@mu M m_dict A) (eta x) = x.
Proof.
  intros.
  assert (mu (eta x) = (mu ∘ eta) x).
    unfold compose. reflexivity.
  rewrite H.
  rewrite monad_law_3.
  reflexivity.
Qed.

Theorem monad_law_4_x
  : forall (M : Type -> Type) (m_dict : Monad M)
      A B (f : A -> B) (x : M (M A)),
  mu (fmap (fmap f) x) = fmap f (mu x).
Proof.
  intros.
  assert (mu (fmap (fmap f) x) = (mu ∘ fmap (fmap f)) x).
    unfold compose. reflexivity.
  assert (fmap f (mu x) = (fmap f ∘ mu) x).
    unfold compose. reflexivity.
  rewrite H. rewrite H0.
  rewrite monad_law_4.
  reflexivity.
Qed.
