Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Functor.Representable.
Require Export Category.Instance.Fun.
Require Export Category.Instance.Coq.
Require Export Category.Instance.Sets.
Require Export Coq.Vectors.Vector.
Require Export Coq.Classes.RelationClasses.

Generalizable All Variables.
Set Primitive Projections.
(* Set Universe Polymorphism. *)
(* Unset Transparent Obligations. *)

Import EqNotations.

Lemma append_respects a
      n m (x : t a n) (y : t a m)
      n' m' (x' : t a n') (y' : t a m') :
  n = n' -> m = m' -> x ~= x' -> y ~= y' -> append x y ~= append x' y'.
Proof. intros; subst; reflexivity. Qed.

(* If we know the exact sizes, we know whether appends imply equality of parts. *)
Lemma append_inv a n m (x x' : t a n) (y y' : t a m) :
  append x y = append x' y' -> x = x' ∧ y = y'.
Proof.
  intros.
  induction x; simpl in *; subst.
  - now induction x' using case0.
  - induction x' using caseS'; simpl in *.
    inv H.
    intuition.
    apply inj_pair2 in H2.
    destruct (IHx _ H2); subst.
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

Corollary concat_nil a n : concat (nil (t a n)) = nil a.
Proof. reflexivity. Qed.

Corollary concat_cons a n m (h : t a n) (t : t (t a n) m) :
  concat (cons _ h _ t) = append h (concat t).
Proof. reflexivity. Qed.

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
  ∃ xss : t (t a n) m, xs = concat xss :=
  match m with
  | O => (nil _; _)
  | S m' =>
      match splitat n xs with
      | (ys, zs) => let (zss, H) := group_dep m' n zs
                    in (cons _ ys _ zss; _)
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
  rewrite Heq_anonymous.
  reflexivity.
Defined.

Definition group {a : Type} (m n : nat) (xs : t a (m * n)) : t (t a n) m :=
  `1 (group_dep m n xs).

Theorem group_concat {a : Type} (m n : nat) (xs : t a (m * n)) :
  concat (group m n xs) = xs.
Proof.
  unfold group.
  destruct (group_dep m n xs); subst.
  reflexivity.
Qed.

Import VectorNotations.

Lemma cons_respects a n m h i (x : t a n) (y : t a m) :
  h = i -> n = m -> x ~= y -> h :: x ~= i :: y.
Proof. intros; subst; reflexivity. Qed.

Lemma append_nil a n (x : t a n) : x ++ [] ~= x.
Proof.
  induction x; simpl.
  - reflexivity.
  - now apply cons_respects.
Qed.

Lemma concat_sing a n (x : t a n) : concat [x] ~= x.
Proof.
  unfold concat; simpl.
  destruct (mult_n_Sm n 0); simpl.
  destruct (PeanoNat.Nat.add_comm n (n * 0)); simpl.
  destruct (mult_n_O n); simpl.
  now apply append_nil.
Qed.

Lemma map_respects a b (f g : a -> b) n m (x : t a n) (y : t a m) :
  (∀ x, f x = g x) -> n = m -> x ~= y -> map f x ~= map g y.
Proof.
  intros; subst.
  induction y; simpl; auto.
  now apply cons_respects.
Qed.

Lemma map_nil `(f : a -> b) : map f (nil a) = nil b.
Proof. reflexivity. Qed.

Lemma hd_map `(f : a -> b) `(xs : t a (S n)) :
  hd (map f xs) = f (hd xs).
Proof. now dependent induction xs. Qed.

Lemma tl_map `(f : a -> b) `(xs : t a (S n)) :
  tl (map f xs) = map f (tl xs).
Proof. now dependent induction xs. Qed.

Lemma splitat_map `(f : a -> b) l r `(xs : t a (l + r)) :
  splitat l (map f xs) = (map f (fst (splitat l xs)), map f (snd (splitat l xs))).
Proof.
  induction l; auto.
  simpl.
  rewrite tl_map.
  rewrite IHl; clear IHl.
  rewrite hd_map.
  assert (@splitat a l r (@tl a (l + r) xs) =
            @splitat a l r
                     (@tl a
                          ((fix add (n m : nat) {struct n} : nat :=
                              match n with
                              | 0%nat => m
                              | S p => S (add p m)
                              end) l r) xs)) by auto.
  rewrite <- !H; clear H.
  now destruct (splitat _ _).
Qed.

Lemma map_append `(f : a -> b) `(xs : t a n) `(ys : t a m) :
  map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  induction xs; simpl.
  - reflexivity.
  - now rewrite IHxs.
Qed.

Lemma map_concat `(f : a -> b) `(xs : t (t a n) m) :
  map f (concat xs) = concat (map (map f) xs).
Proof.
  induction xs; simpl.
  - now destruct (mult_n_O n).
  - destruct (mult_n_Sm n n0); simpl.
    destruct (PeanoNat.Nat.add_comm n (n * n0)); simpl.
    rewrite <- IHxs.
    now apply map_append.
Qed.

Lemma group_map `(f : a -> b) n m `(xs : t a (n * m)) :
  group n m (map f xs) = map (map f) (group n m xs).
Proof.
  induction n; simpl in *; auto.
Abort.

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

Theorem unsize_size :
  (∀ s, unsize (size s) = s) -> False.
Proof.
  intros.
  specialize (H Top).
  simpl in H.
  inversion H.
Qed.

Definition Shape_equiv (x y : Shape) : Type :=
  size x = size y.

Program Instance Shape_Setoid : Setoid Shape := {|
  equiv := Shape_equiv
|}.
Next Obligation.
  unfold Shape_equiv.
  equivalence.
  now rewrite H, H0.
Qed.

Lemma Shape_plus_zero x : Plus x Bottom ≈ x.
Proof.
  simpl; unfold Shape_equiv; simpl.
  now rewrite plus_n_O.
Qed.

Lemma Shape_zero_plus x : Plus Bottom x ≈ x.
Proof.
  simpl; unfold Shape_equiv; auto.
Qed.

Lemma Shape_plus_assoc x y z : Plus x (Plus y z) ≈ Plus (Plus x y) z.
Proof.
  simpl; unfold Shape_equiv; simpl.
  now rewrite PeanoNat.Nat.add_assoc.
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
    assert ((λ x1 : t a (size s2), vec (trie x1)) = Datatypes.id). {
      clear -vec_trie.
      extensionality w.
      now rewrite vec_trie.
    }
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
Admitted.

Lemma vec_respects a s (x y : Trie a s) : x = y -> vec x ~= vec y.
Proof. intros; subst; reflexivity. Qed.

Fixpoint Trie_map {s : Shape} `(f : a -> b) (x : Trie a s) : Trie b s :=
  match x with
  | Unit => Unit
  | Id x => Id (f x)
  | Join xs ys => Join (Trie_map f xs) (Trie_map f ys)
  | Joins z k xs => Joins z (Trie_map f ∘ k) xs
  end.

Theorem trie_map {s : Shape} `(f : a -> b) (xs : t a (size s)) :
  trie (map f xs) = Trie_map f (trie xs).
Proof.
  induction s; simpl in *; auto.
  - now rewrite hd_map.
  - destruct (splitat (size s1) (map f xs)) eqn:Heqe; simpl.
    rewrite splitat_map in Heqe.
    inv Heqe.
    rewrite IHs1, IHs2.
    now destruct (splitat (size s1) xs).
  -
Abort.

Fixpoint Trie_inject `(x : Vector.t a n) : Trie a (unsize n) :=
  match x with
  | nil _ => Unit
  | cons _ h n x => Join (Id h) (Trie_inject x)
  end.

Lemma vec_inject `(x : Vector.t a n) : vec (Trie_inject x) ~= x.
Proof.
  induction x; simpl; auto.
  apply cons_respects; auto.
  now apply size_unsize.
Qed.

Theorem Trie_map_flatten `(f : a -> b) `(t : Trie a s) :
  vec (Trie_map f t) ~= map f (vec t).
Proof.
  induction t; auto.
  - simpl.
    rewrite map_append.
    now rewrite IHt1, IHt2.
  - simpl in *.
    rewrite map_concat.
    rewrite map_map.
    apply concat_respects; auto.
    apply map_respects; auto.
    intros.
    now rewrite H.
Qed.

Definition Trie_case0 {a : Type}
           (P : Trie a Bottom → Type) (Punit : P Unit)
           (v : Trie a Bottom) : P v.
Proof. now dependent induction v. Defined.

Definition Trie_case1 {a : Type}
           (P : Trie a Top → Type) (Punit : ∀ x, P (Id x))
           (v : Trie a Top) : P v.
Proof. now dependent induction v. Defined.

Fixpoint Trie_fold_right `(f : a → b → b) `(t : Trie a s) (z : b) : b :=
  match t with
  | Unit => z
  | Id x => f x z
  | Join xs ys => Trie_fold_right f xs (Trie_fold_right f ys z)
  | Joins _ k xss => Trie_fold_right (Trie_fold_right f ∘ k) xss z
  end.

Definition Trie_fold_right2
           `(f : a → b → c → c)
           (z : c)
           (s : Shape)
           (v1 : Trie a s)
           (v2 : Trie b s) : c.
Proof.
  induction s; simpl in *.
  - exact z.
  - destruct v1 using Trie_case1.
    destruct v2 using Trie_case1.
    exact (f x x0 z).
  - dependent destruction v1.
    dependent destruction v2.
    specialize (IHs1 v1_1 v2_1).
    specialize (IHs2 v1_2 v2_2).
    admit.
  - dependent destruction v1.
    dependent destruction v2.
    admit.
Admitted.

Definition
  Trie_rect2
  {a b : Type}
  (P : ∀ s : Shape, Trie a s → Trie b s → Type)
  (Punit : P Bottom Unit Unit)
  (Pid : (∀ (a : a) (b : b), P Top (Id a) (Id b)))
  (Pjoin : (∀ (s1 : Shape) (x1 : Trie a s1) (x2 : Trie b s1)
              (s2 : Shape) (y1 : Trie a s2) (y2 : Trie b s2),
               P s1 x1 x2 → P s2 y1 y2
               → P (Plus s1 s2) (Join x1 y1) (Join x2 y2)))
  (Pjoins : (∀ (z1 z2 : Type) (s1 : Shape)
               (xs1 : Trie z1 s1) (xs2 : Trie z2 s1)
               (s2 : Shape)
               (k1 : z1 -> Trie a s2)
               (k2 : z2 -> Trie b s2),
                Trie_fold_right2 (λ z1 z2 p, p ∧ P s2 (k1 z1) (k2 z2))
                                 True s1 xs1 xs2
                → P (Times s1 s2) (Joins z1 k1 xs1) (Joins z2 k2 xs2)))
  (s : Shape) (v1 : Trie a s) (v2 : Trie b s) : P s v1 v2.
Proof.
  induction s; simpl in *.
  - induction v1 using Trie_case0.
    induction v2 using Trie_case0.
    exact Punit.
  - induction v1 using Trie_case1.
    induction v2 using Trie_case1.
    now apply Pid.
  - dependent induction v1.
    dependent induction v2.
    now apply Pjoin.
  - dependent induction v1.
    dependent induction v2.
    apply Pjoins.
Abort.

Definition Trie_equiv {s : Shape} {a : Type} (x y : Trie a s) : Type :=
  vec x = vec y.

Program Instance Trie_Setoid {s : Shape} {a : Type} : Setoid (Trie a s) := {|
  equiv := Trie_equiv
|}.
Next Obligation.
  unfold Trie_equiv.
  constructor; repeat intro; intuition.
  now rewrite H, H0.
Qed.

Program Instance Trie_Functor (s : Shape) : Coq ⟶ Sets := {|
  fobj := λ a,
    {| carrier := Trie a s
     ; is_setoid := @Trie_Setoid s a |};
  fmap := λ _ _ f,
    {| morphism := @Trie_map s _ _ f
     ; proper_morphism := _ |}
|}.
Next Obligation.
  proper.
  unfold Trie_equiv in *.
  rewrite !Trie_map_flatten.
  now rewrite X.
Qed.
Next Obligation.
  proper.
  unfold Trie_equiv in *.
  rewrite !Trie_map_flatten.
  f_equal.
  extensionality w.
  now apply H.
Qed.
Next Obligation.
  unfold Trie_equiv in *.
  rewrite Trie_map_flatten.
  induction (vec x0); simpl; auto.
  f_equal.
  exact IHt.
Qed.
Next Obligation.
  unfold Trie_equiv in *.
  rewrite !Trie_map_flatten.
  now rewrite map_map.
Qed.

(*
Program Instance Trie_Representable (s : Shape) :
  Representable (Trie_Functor s) := {|
  repr_obj := Shape;
  represented := _
|}.
*)

Program Definition Tries (a : Type) : Category := {|
  obj     := Shape;
  hom     := λ x y, Trie a x -> Trie a y;
  homset  := λ _ _, {| equiv := fun f g => ∀ x, f x = g x |};
  id      := _;
  compose := _
|}.
Next Obligation.
  equivalence;
  unfold Trie_equiv in *; intuition.
  now rewrite H1, H2.
Qed.
Next Obligation.
  proper.
  unfold Tries_obligation_3.
  now rewrite H0, H.
Qed.

Program Definition Vectors (a : Type) : Category := {|
  obj     := nat;
  hom     := λ x y, Vector.t a x -> Vector.t a y;
  homset  := λ _ _, {| equiv := fun f g => ∀ x, f x = g x |};
  id      := _;
  compose := _
|}.
Next Obligation.
  equivalence;
  unfold Trie_equiv in *; intuition.
  now rewrite H1, H2.
Qed.
Next Obligation.
  proper.
  unfold Vectors_obligation_3.
  now rewrite H0, H.
Qed.

Program Definition Cardinality (a : Type) : Tries a ⟶ Vectors a := {|
  fobj := size;
  fmap := λ _ _ f, vec ∘ f ∘ trie
|}.
Next Obligation.
  proper.
  now rewrite H.
Qed.
Next Obligation.
  unfold Tries_obligation_2.
  unfold Vectors_obligation_2.
  now rewrite vec_trie.
Qed.
Next Obligation.
  unfold Tries_obligation_3.
  unfold Vectors_obligation_3.
  f_equal.
  apply JMeq_congr.
  now rewrite (@trie_vec _ _ (g (trie x0))).
Qed.

Program Definition Canonicity (a : Type) : Vectors a ⟶ Tries a := {|
  fobj := unsize;
  fmap := λ _ _ f, trie ∘ f ∘ vec
|}.
Next Obligation. now rewrite size_unsize. Defined.
Next Obligation. now rewrite size_unsize. Defined.
Next Obligation.
  proper.
  unfold Canonicity_obligation_1.
  unfold Canonicity_obligation_2.
  now rewrite H.
Qed.
Next Obligation.
  unfold Canonicity_obligation_1.
  unfold Canonicity_obligation_2.
  unfold Vectors_obligation_2.
  unfold Tries_obligation_2.
  destruct (size_unsize x); simpl.
  now apply trie_vec.
Qed.
Next Obligation.
  unfold Canonicity_obligation_1.
  unfold Canonicity_obligation_2.
  unfold Vectors_obligation_3.
  unfold Tries_obligation_3.
  rewrite !vec_trie.
  f_equal.
  f_equal.
  apply JMeq_congr.
  f_equal.
  remember (rew [λ H : nat, t a H] eq_ind_r (λ n : nat, n = x) eq_refl (size_unsize x)
             in vec x0) as o.
  clear.
  assert (∀ x,
          rew [λ H : nat, t a H] eq_ind_r (λ n : nat, n = y) eq_refl (size_unsize y) in
          rew [λ H : nat, t a H] eq_ind_r (λ n : nat, y = n) eq_refl (size_unsize y) in x = x). {
    clear.
    now destruct (size_unsize y); simpl.
  }
  now rewrite H.
Qed.

Program Definition Card_Canon_Adjunction a :
  Cardinality a ⊣ Canonicity a := {|
  adj := λ x y,
    {| to   := {| morphism := λ f, _ |};
       from := {| morphism := λ f, _ |}
     |}
|}.
Next Obligation.
  apply trie.
  rewrite size_unsize.
  apply f.
  apply vec.
  exact X.
Defined.
Next Obligation.
  proper.
  unfold Card_Canon_Adjunction_obligation_1.
  now rewrite H.
Qed.
Next Obligation.
  rewrite <- size_unsize.
  apply vec.
  apply f.
  apply trie.
  exact X.
Defined.
Next Obligation.
  proper.
  unfold Card_Canon_Adjunction_obligation_3.
  now rewrite H.
Qed.
Next Obligation.
  unfold Card_Canon_Adjunction_obligation_1.
  unfold Card_Canon_Adjunction_obligation_3.
  destruct (size_unsize y); simpl.
  rewrite trie_vec.
  now apply trie_vec.
Qed.
Next Obligation.
  unfold Card_Canon_Adjunction_obligation_1.
  unfold Card_Canon_Adjunction_obligation_3.
  rewrite vec_trie.
  assert (∀ x, rew [t a] size_unsize y in rew <- [λ n : nat, t a n] size_unsize y in x = x). {
    clear.
    now destruct (size_unsize y); simpl.
  }
  rewrite H.
  now rewrite vec_trie.
Qed.
Next Obligation.
  unfold Card_Canon_Adjunction_obligation_1.
  unfold Vectors_obligation_3.
  unfold Tries_obligation_3.
  now rewrite trie_vec.
Qed.
Next Obligation.
  unfold Card_Canon_Adjunction_obligation_1.
  unfold Vectors_obligation_3.
  unfold Tries_obligation_3.
  unfold Canonicity_obligation_1.
  unfold Canonicity_obligation_2.
  rewrite vec_trie.
  apply JMeq_congr.
  assert (∀ x, rew [λ H : nat, t a H] eq_ind_r (λ n : nat, n = y) eq_refl (size_unsize y) in
               rew <- [λ n : nat, t a n] size_unsize y in x = x). {
    clear.
    now destruct (size_unsize y); simpl.
  }
  rewrite H; clear H.
  assert (∀ x, rew <- [λ n : nat, t a n] size_unsize z in x =
               rew [λ H : nat, t a H] eq_ind_r (λ n : nat, z = n) eq_refl (size_unsize z) in x). {
    clear.
    now destruct (size_unsize z); simpl.
  }
  rewrite H.
  reflexivity.
Qed.
Next Obligation.
  unfold Card_Canon_Adjunction_obligation_3.
  unfold Tries_obligation_3.
  unfold Vectors_obligation_3.
  now rewrite trie_vec.
Qed.
Next Obligation.
  unfold Card_Canon_Adjunction_obligation_3.
  unfold Tries_obligation_3.
  unfold Vectors_obligation_3.
  unfold Canonicity_obligation_1.
  unfold Canonicity_obligation_2.
  rewrite vec_trie.
  assert (∀ x, rew [t a] size_unsize z in
               rew [λ H : nat, t a H]
                   eq_ind_r (λ n : nat, z = n) eq_refl (size_unsize z) in x = x). {
    clear.
    now destruct (size_unsize z); simpl.
  }
  rewrite H; clear H.
  assert (∀ x, rew [λ H : nat, t a H] eq_ind_r (λ n : nat, n = y) eq_refl (size_unsize y) in x =
               rew [t a] size_unsize y in x). {
    clear.
    now destruct (size_unsize y); simpl.
  }.
  now rewrite H.
Qed.
