Require Import Coq.Vectors.Vector.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep.
Require Import FunctionalExtensionality.

Generalizable All Variables.

(* If we know the exact sizes, we know whether appends imply equality of parts. *)
Lemma append_inv a n m (x x' : t a n) (y y' : t a m) :
  append x y = append x' y' -> x = x' /\ y = y'.
Proof.
  intros.
  induction x; simpl in *; subst.
  - now induction x' using case0.
  - induction x' using caseS'; simpl in *.
    inversion H; subst; clear H.
    apply inj_pair2 in H2.
    specialize (IHx _ H2).
    intuition; subst.
    reflexivity.
Qed.

Fixpoint concat `(xs : t (t a n) m) : t a (m * n) :=
  match xs with
  | nil _ => nil a
  | cons _ hd n tl => append hd (concat tl)
  end.

Lemma concat_respects a n m (x : t (t a n) m) n' m' (x' : t (t a n') m') :
  n = n' -> m = m' -> x ~= x' -> concat x ~= concat x'.
Proof. intros; subst; reflexivity. Qed.

Lemma concat_inj a n m (x y : t (t a n) m) : concat x = concat y -> x = y.
Proof.
  intros.
  induction x; simpl in *.
  - now induction y using case0.
  - induction y using caseS'; simpl in *.
    apply append_inv in H.
    destruct H; subst.
    apply f_equal.
    now apply IHx.
Qed.

Lemma nil_inv `(x : t a 0) : x = nil a.
Proof. now induction x using case0. Qed.

Lemma nil_sing `(x : t a 1) : cons _ (hd x) _ (nil a) = x.
Proof.
  induction x using caseS'.
  simpl.
  now induction x using case0.
Qed.

Program Fixpoint group_dep {a : Type} (m n : nat) (xs : t a (m * n)) :
  { xss : t (t a n) m & xs = concat xss } :=
  match m with
  | O => (existT _ (nil _) _)
  | S m' =>
      match splitat n xs with
      | (ys, zs) => let (zss, H) := group_dep m' n zs
                    in (existT _ (cons _ ys _ zss) _)
      end
  end.
Next Obligation.
  destruct (mult_n_O n); simpl.
  now apply nil_inv.
Defined.
Next Obligation.
  destruct (mult_n_Sm n m'); simpl.
  destruct (PeanoNat.Nat.add_comm n (n * m')); simpl.
  symmetry in Heq_anonymous.
  apply append_splitat in Heq_anonymous.
  rewrite <- Heq_anonymous.
  reflexivity.
Defined.

Definition group {a : Type} (m n : nat) (xs : t a (m * n)) : t (t a n) m :=
  projT1 (group_dep m n xs).

Import VectorNotations.

Inductive Shape :=
  | Bottom
  | Top
  | Plus (x y : Shape)
  | Times (x y : Shape).

Fixpoint size (s : Shape) : nat :=
  match s with
  | Bottom => 0
  | Top => 1
  | Plus x y => size x + size y
  | Times x y => size x * size y
  end.

Fixpoint unsize (n : nat) : Shape :=
  match n with
  | O => Bottom
  | S n => Plus Top (unsize n)
  end.

Theorem size_unsize n : size (unsize n) = n.
Proof. now induction n; simpl; auto. Qed.

Theorem unsize_size : (forall s, unsize (size s) = s) -> False.
Proof.
  intros.
  specialize (H Top).
  simpl in H.
  inversion H.
Qed.

Inductive Trie (a : Type) : Shape -> Type :=
  | Unit : Trie a Bottom             (* a^0 = 1 *)
  | Id : a -> Trie a Top             (* a^1 = a *)
    (* a^(b+c) = a^b * a^c *)
  | Join {x y} : Trie a x -> Trie a y -> Trie a (Plus x y)
    (* a^(b*c) = (a^b)^c *)
  | Joins {x y} :
    (* This allows us to positively express Trie (Trie a y) x *)
    forall z, (z -> Trie a y) -> Trie z x -> Trie a (Times x y).

Arguments Unit {a}.
Arguments Id {a} _.
Arguments Join {a x y} _ _.
Arguments Joins {a x y} _ _ _.

Open Scope program_scope.

Fixpoint vec `(x : Trie a s) : Vector.t a (size s) :=
  match x with
  | Unit         => nil a
  | Id x         => cons a x 0 (nil a)
  | Join xs ys   => vec xs ++ vec ys
  | Joins _ k xs => concat (map (vec ∘ k) (vec xs))
  end.

Program Fixpoint trie `(x : Vector.t a (size s)) : Trie a s :=
  match s with
  | Bottom    => Unit
  | Top       => Id (@hd a 0 x)
  | Plus s t  => let (ys, zs) := splitat (size s) x
                 in Join (trie ys) (trie zs)
  | Times s t => Joins (Vector.t a (size t)) trie
                       (trie (group (size s) (size t) x))
  end.

Fixpoint vec_trie `(x : Vector.t a (size s)) : vec (trie x) ~= x.
Proof.
  induction s; simpl in *.
  - now rewrite nil_inv.
  - now rewrite nil_sing.
  - destruct (splitat (size s1) x) eqn:Heqe; simpl in *.
    apply append_splitat in Heqe.
    rewrite Heqe; clear Heqe.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - unfold group.
    destruct (group_dep _ _ _) eqn:Heqe; simpl in *.
    subst.
    apply concat_respects; auto.
    rewrite vec_trie.
    assert ((fun x1 : t a (size s2) => vec (trie x1)) = Datatypes.id). {
      clear -vec_trie.
      extensionality w.
      now rewrite vec_trie.
    }
    unfold compose.
    rewrite H.
    now rewrite map_id.
Qed.

Theorem trie_vec `(x : Trie a s) : trie (vec x) = x.
Proof.
  induction x; simpl; auto.
  - rewrite splitat_append.
    now rewrite IHx1, IHx2.
  - unfold group.
    destruct (group_dep _ _ _) eqn:Heqe; simpl in *.
    clear Heqe.
    apply concat_inj in e; subst.
Abort.
