Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

Import ListNotations.

Section Vector.

Variable A : Type.

Definition Vec : nat → Type :=
  fix vec n := match n return Type with
               | O   => unit
               | S n => prod A (vec n)
               end.

Definition vnil : Vec 0 := tt.

Definition vsing (x : A) : Vec 1 := (x, tt).

Definition vcons {n} (x : A) (v : Vec n) : Vec (S n) := (x, v).

Definition vec_rect : forall (P : forall {n}, Vec n → Type),
  P vnil
    → (forall {n} (x : A) (v : Vec n), P v → P (vcons x v))
    → forall {n} (v : Vec n), P v.
Proof.
Admitted.

Definition vecn_rect : forall (P : forall {n}, Vec n → Type),
  (forall x : A, P (vsing x))
    → (forall {n} (x : A) (v : Vec (S n)), P v → P (vcons x v))
    → forall {n} (v : Vec (S n)), P v.
Proof. Admitted.

Definition vec_to_list `(v : Vec n) : list A.
Proof. Admitted.

Lemma vec_list_cons (x : A) `(xs : Vec n) :
  vec_to_list (vcons x xs) = x :: vec_to_list xs.
Proof. Admitted.

Lemma vec_to_list_size `(v : Vec n) : length (vec_to_list v) = n.
Proof. Admitted.

Definition list_to_vec (l : list A) : Vec (length l).
Proof. Admitted.

Theorem vec_list (xs : list A) : vec_to_list (list_to_vec xs) = xs.
Proof. Admitted.

Import EqNotations.

Theorem list_vec `(v : Vec n) :
  rew (vec_to_list_size v) in list_to_vec (vec_to_list v) = v.
Proof. Admitted.

Definition vfoldr_with_index
  {B : Type} {n} (f : Fin.t n → A → B → B) (b : B) (v : Vec n) : B.
Proof. Admitted.

Definition vfoldr {B : Type} {n} (f : A → B → B) (b : B) (v : Vec n) : B :=
  vfoldr_with_index (fun _ => f) b v.

Definition vfoldl_with_index
  {B : Type} {n} (f : Fin.t n → B → A → B) (b : B) (v : Vec n) : B.
Proof. Admitted.

Definition vfoldl {B : Type} {n} (f : B → A → B) (b : B) (v : Vec n) : B :=
  vfoldl_with_index (fun _ => f) b v.

Definition vconst {n} (i : A) : Vec n.
Proof. Admitted.

Definition vreplace {n} (v : Vec n) (p : Fin.t n) (i : A) : Vec n.
Proof. Admitted.

Definition vnth {n} (v : Vec n) (p : Fin.t n) : A.
Proof. Admitted.

Definition vmodify {n} (v : Vec n) (p : Fin.t n) (f : A → A) : Vec n :=
  vreplace v p (f (vnth v p)).

Lemma vnth_vconst (x : A) {n} (i : Fin.t n) : vnth (vconst x) i = x.
Proof. Admitted.

Definition vshiftin {n} (v : Vec n) (i : A) : Vec (S n).
Proof. Admitted.

Definition vapp {n m} (v : Vec n) (u : Vec m) : Vec (n + m).
Proof. Admitted.

(*
Definition widen_id {n} := widen_ord (leqnSn n).

Lemma widen_ord_spec : forall n x (H : n <= n), widen_ord H x = x.
Proof. Admitted.
  move=> ? [? ?] ?.
  rewrite /widen_ord.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Lemma widen_ord_inj : forall m n (H : m <= n), injective (widen_ord H).
Proof. Admitted.
  move=> m n H.
  rewrite /injective => x1 x2.
  by invert; apply ord_inj.
Qed.

Lemma widen_ord_refl : forall n (H : n <= n) x, widen_ord (m := n) H x = x.
Proof. Admitted.
  move=> n H.
  case=> m Hm.
  rewrite /widen_ord /=.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Lemma map_widen_ord_refl : forall b n (H : n <= n) (xs : list (Fin.t n * b)),
  [list (let: (xid, reg) := i in (widen_ord (m:=n) H xid, reg)) | i <- xs] = xs.
Proof. Admitted.
  move=> b n H.
  elim=> //= [x xs IHxs].
  rewrite IHxs.
  case: x => [xid reg].
  congr ((_, reg) :: xs).
  exact: widen_ord_refl.
Qed.
*)

(* The following properties are all to support the [beginnings] Theorem at
   the end of Spec.v. *)

Definition vec_ind : forall (P : forall {n}, Vec n → Prop),
  P vnil
    → (forall {n} (x : A) (v : Vec n), P v → P (vcons x v))
    → forall {n} (v : Vec n), P v := vec_rect.

Definition vecn_ind : forall (P : forall {n}, Vec n → Prop),
  (forall x : A, P (vsing x))
    → (forall {n} (x : A) (v : Vec (S n)), P v → P (vcons x v))
    → forall {n} (v : Vec (S n)), P v := vecn_rect.

(*
Lemma vnth_cons0 : forall n i (v : Vec n) H,
  vnth (vcons i v) (@Ordinal (S n) 0 H) = i.
Proof. Admitted. by move=> n i; elim/vec_ind. Qed.

Lemma vnth_consn : forall n i (v : Vec n) m, forall H: m < n,
  vnth (vcons i v) (@Ordinal (S n) m.+1 H) = vnth v (@Ordinal n m H).
Proof. Admitted. by move=> n i; elim/vec_ind. Qed.
*)

Lemma vshiftin_cons : forall n z (v : Vec n) i,
  vshiftin (vcons z v) i = vcons z (vshiftin v i).
Proof. Admitted.

(*
Lemma vnth_last : forall n (i : A) (v : Vec n),
  vnth (vshiftin v i) ord_max = i.
Proof. Admitted.
*)

Lemma vreplace_cons0 n (k : Fin.t (S n)) : forall i (v : Vec n) z,
  k = Fin.F1 → vreplace (vcons i v) k z = vcons z v.
Proof. Admitted.

(*
Lemma vreplace_consn : forall n m i (v : Vec n) z, forall H: m < n,
  vreplace (vcons i v) (@Ordinal (S n) m.+1 H) z
    = vcons i (vreplace v (@Ordinal n m H) z).
Proof. Admitted. by move=> n m i; elim/vec_ind. Qed.
*)

Lemma vnth_vreplace : forall n (v : Vec n) k z,
  vnth (vreplace v k z) k = z.
Proof. Admitted.

Lemma fin1_eq : forall (j k : Fin.t 1), j = k.
Proof. Admitted.

Lemma vnth_vreplace_neq : forall n (v : Vec n) (k j : Fin.t n) (z : A),
  k ≠ j → vnth (vreplace v k z) j = vnth v j.
Proof. Admitted.

(*
Definition vnth_vshiftin {n} : forall (z : A) (v : Vec n) k,
  vnth (vshiftin v z) (widen_id k) = vnth v k.
Proof. Admitted.
  move=> z v k.
  case: n => [|n] in k v *;
    first exact: fin_contra.
  elim/vecn_ind: v => [x|sz x xs IHxs] in k *.
    rewrite /vshiftin /=.
    by elim/@fin_ind: k => //.
  rewrite vshiftin_cons.
  elim/@fin_ind: k => [Hk|? ? _].
    have →: Hk = ltn0Sn sz by exact: eq_irrelevance.
    by rewrite vnth_cons0.
  rewrite !vnth_consn -IHxs.
  congr (vnth _ (Ordinal _)).
  exact: eq_irrelevance.
Qed.
*)

End Vector.

Definition vmap {A B : Type} {n} (f : A → B) (v : Vec A n) : Vec B n.
Proof. Admitted.

Definition vmap_with_index {A B : Type} {n} (f : Fin.t n → A → B) (v : Vec A n) :
  Vec B n.
Proof. Admitted.

Definition vtranspose {m n : nat} a : Vec (Vec a n) m → Vec (Vec a m) n.
Proof. Admitted.

Arguments vsing [A] _ /.
Arguments vcons [A n] _ _ /.
Arguments vconst [A n] !i.
Arguments vfoldr_with_index [A B n] f !b !v.
Arguments vfoldr [A B n] f !b !v.
Arguments vfoldl_with_index [A B n] f !b !v.
Arguments vfoldl [A B n] f !b !v.
Arguments vreplace [A n] !v !p !i.
Arguments vnth [A n] !v !p.
Arguments vmodify [A n] !v !p !f.
Arguments vapp [A n m] !v !u.
Arguments vshiftin [A n] !v !i.
Arguments vmap [A B n] f !v.
Arguments vmap_with_index [A B n] f !v.
Arguments vec_to_list [A n] !v.
Arguments list_to_vec [A] !l.
