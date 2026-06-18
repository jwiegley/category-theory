From Coq Require Import List.
From Coq Require Import Lia.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.

Generalizable All Variables.
Set Transparent Obligations.

(** Finite partial maps *)

(* nLab: https://ncatlab.org/nlab/show/partial+function
   Wikipedia: https://en.wikipedia.org/wiki/Associative_array

   This is a utility library, not a categorical construction: [Map k v] is
   the abstract data type of a finite partial map (associative array,
   dictionary, "function with finite domain") from keys [k] to values [v].
   It is represented concretely as a list of key/value bindings, so it is
   isomorphic to an association list [list (k * v)] (see [toList]/[fromList]).
   Later bindings of a key are shadowed by earlier ones, exactly as for an
   association list scanned front-to-back; [compress] computes the canonical
   shadow-free representative.

   The observational notion of equality is extensional: two maps are
   equivalent iff they agree on every [lookup] (see [Map_Setoid]), matching
   the associative-array law
       lookup k (insert j v m) = if k = j then Some v else lookup k m.

   The API mirrors Haskell's [Data.Map] (containers package): [empty],
   [singleton], [insert], [delete], [adjust], [alter], [member], [size],
   [findWithDefault], the [*WithKey] variants, the folds, and the functorial
   [map]/[mapWithKey].  See
   https://hackage.haskell.org/package/containers/docs/Data-Map-Lazy.html *)

(* nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)

   [map : (v -> b) -> Map k v -> Map k b] is the functorial action (fmap)
   of the endofunctor [Map k -] on the category of Coq types, fixing the key
   type [k].  It satisfies the two functor laws up to the extensional [Map]
   equivalence: [map id ≈ id] and [map (g ∘ f) ≈ map g ∘ map f] (these laws
   are not proved here, but follow because [map] rewrites values pointwise
   and preserves every key, hence commutes with [lookup]).  [mapWithKey]
   is the key-aware variant [k -> v -> b], not a plain functor since the
   transported function may depend on the key. *)

Section Map.

Import ListNotations.

Context {k v : Type}.

(* A finite map as a list of bindings: [Add i x m] prepends the binding
   [i ↦ x] to [m].  When a key occurs more than once the earliest (outermost)
   binding wins, since [lookup] scans front-to-back. *)
Inductive Map : Type :=
  | Add : k → v → Map → Map     (* cons a key/value binding *)
  | Empty : Map.                (* the empty map *)

Derive NoConfusion NoConfusionHom Subterm for Map.

Inductive MapsTo `{EqDec k} (i : k) (x : v) : Map -> Prop :=
  | MapsTo_hd i' x' m : i = i' -> x = x' → MapsTo (Add i' x' m)
  | MapsTo_tl i' x' m : i ≠ i' → MapsTo m -> MapsTo (Add i' x' m).

Fixpoint lookup `{EqDec k} (i : k) (m : Map) : option v :=
  match m with
  | Empty => None
  | Add i' x m =>
      if eq_dec i i'
      then Some x
      else lookup i m
  end.

Lemma pneq_dec `{EqDec k} {x y : k} (N : x ≠ y) :
  { N' | eq_dec x y = right N' }.
Proof.
  destruct (eq_dec x y); auto.
  - subst; contradiction.
  - now exists n.
Qed.

Fixpoint MapsTo_lookup `{EqDec k} i x m : MapsTo i x m ↔ lookup i m = Some x.
Proof.
  split; intros.
  - induction H0; subst; simpl.
    + now rewrite peq_dec_refl.
    + destruct (pneq_dec H0).
      now rewrite e.
  - induction m; simpl in *.
    + destruct (eq_dec i k0); subst.
      * inv H0.
        now left.
      * right; auto.
    + discriminate.
Qed.

(* Extensional equality of maps: two maps are equivalent iff they agree on
   every [lookup].  This is the associative-array notion of equality, under
   which structural noise (binding order, shadowed/duplicate bindings) is
   quotiented away. *)
#[export]
Program Instance Map_Setoid `{EqDec k} : Setoid (Map) := {|
  equiv := λ m1 m2, ∀ k, lookup k m1 = lookup k m2
|}.
Next Obligation.
  constructor; repeat intro; auto.
  transitivity (lookup k0 y); congruence.
Qed.

Fixpoint member `{EqDec k} (i : k) (m : Map) : bool :=
  match m with
  | Empty => false
  | Add i' _ m => if eq_dec i i' then true else member i m
  end.

#[export]
Program Instance member_respects `{EqDec k} :
  Proper (eq ==> equiv ==> eq) member.
Next Obligation.
  repeat intro; subst.
  specialize (H1 y).
  generalize dependent y0.
  induction x0; simpl; intros.
  - destruct (eq_dec y k0) eqn:Heqe; simpl.
    + subst.
      clear -H1.
      induction y0; simpl in *; auto.
      * destruct (eq_dec k0 k1) eqn:Heqe; simpl; auto.
      * congruence.
    + now apply IHx0.
  - induction y0; simpl in *; auto.
    destruct (eq_dec y k0) eqn:Heqe; simpl.
    + congruence.
    + now apply IHy0.
Qed.

Fixpoint toList (m : Map) : list (k * v) :=
  match m with
  | Empty => []
  | Add i x m => (i, x) :: toList m
  end.

Fixpoint fromList (l : list (k * v)) : Map :=
  match l with
  | [] => Empty
  | (i, x) :: xs => Add i x (fromList xs)
  end.

Lemma toList_fromList (l : list (k * v)) : toList (fromList l) = l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl.
  now rewrite IHl.
Qed.

Lemma fromList_toList (m : Map) : fromList (toList m) = m.
Proof.
  induction m; simpl; auto.
  now rewrite IHm.
Qed.

Definition null (m : Map) : bool :=
  if m then false else true.

#[export]
Program Instance null_respects `{EqDec k} : Proper (equiv ==> eq) null.
Next Obligation.
  repeat intro.
  generalize dependent y.
  induction x, y; simpl; intros; auto.
  - specialize (H0 k0).
    rewrite peq_dec_refl in H0.
    discriminate.
  - specialize (H0 k0).
    rewrite peq_dec_refl in H0.
    discriminate.
Qed.

Fixpoint delete `{EqDec k} (i : k) (m : Map) : Map :=
  match m with
  | Empty => m
  | Add i' x m =>
      if eq_dec i i'
      then delete i m
      else Add i' x (delete i m)
  end.

Lemma delete_idem `{EqDec k} i m :
  delete i (delete i m) = delete i m.
Proof.
  induction m; simpl; auto.
  destruct (eq_dec i k0) eqn:Heqe; auto; simpl.
  rewrite Heqe.
  now rewrite IHm.
Qed.

Lemma delete_comm `{EqDec k} i j m :
  delete i (delete j m) = delete j (delete i m).
Proof.
  generalize dependent j.
  generalize dependent i.
  induction m; simpl; intros; auto.
  destruct (eq_dec i k0) eqn:Heqe1; auto; simpl.
  - destruct (eq_dec j k0) eqn:Heqe2; auto; simpl.
    now rewrite Heqe1.
  - destruct (eq_dec j k0) eqn:Heqe2; auto; simpl.
    rewrite Heqe1.
    now rewrite IHm.
Qed.

Fixpoint size (m : Map) : nat :=
  match m with
  | Add _ _ m => 1 + size m
  | Empty => 0
  end.

Lemma size_delete `{EqDec k} i m : (size (delete i m) <= size m)%nat.
Proof.
  induction m; simpl; auto.
  destruct (eq_dec i k0) eqn:Heqe;
  auto; simpl; lia.
Qed.

Equations compress `{EqDec k} (m : Map) : Map by wf (size m) :=
  compress Empty := Empty;
  compress (Add i' x m) := Add i' x (compress (delete i' m)).
Next Obligation.
  specialize (compress H m).
  pose proof (size_delete i' m); lia.
Qed.

Lemma compress_delete `{EqDec k} i m :
  compress (delete i m) = delete i (compress m).
Proof.
  generalize dependent i.
  apply FunctionalElimination_compress;
  simpl; intros; auto.
  destruct (eq_dec i i') eqn:Heqe.
  - subst.
    rewrite <- H1.
    now rewrite delete_idem.
  - simp compress; simpl.
    f_equal.
    rewrite <- H1.
    now rewrite delete_comm.
Qed.

Lemma size_compress `{EqDec k} m : (size (compress m) <= size m)%nat.
Proof.
  induction m; auto.
  simp compress; simpl.
  apply le_n_S.
  rewrite compress_delete.
  now rewrite size_delete.
Qed.

Fixpoint findWithDefault `{EqDec k} (d : v) (i : k) (m : Map) : v :=
  match m with
  | Empty => d
  | Add i' x m =>
      if eq_dec i i'
      then x
      else findWithDefault d i m
  end.

Definition empty : Map := Empty.

Definition singleton (i : k) (x : v) : Map := Add i x empty.

Fixpoint insert `{EqDec k} (i : k) (x : v) (m : Map) : Map :=
  match m with
  | Empty => singleton i x
  | Add i' x' m =>
      if eq_dec i i'
      then Add i x m
      else Add i' x' (insert i x m)
  end.

Lemma lookup_insert `{EqDec k} i j x m :
  lookup i (insert j x m) = if eq_dec i j then Some x else lookup i m.
Proof.
  destruct (eq_dec i j) eqn:Heqe1.
  - induction m; simpl; intros.
    + destruct (eq_dec j k0) eqn:Heqe2; simpl.
      * now rewrite Heqe1.
      * subst.
        now rewrite Heqe2.
    + now destruct (eq_dec i j).
  - induction m; simpl; intros.
    + destruct (eq_dec j k0) eqn:Heqe2; simpl.
      * rewrite Heqe1.
        subst.
        now rewrite Heqe1.
      * now rewrite IHm.
    + now destruct (eq_dec i j).
Qed.

Lemma lookup_delete `{EqDec k} i j m :
  lookup i (delete j m) = if eq_dec i j then None else lookup i m.
Proof.
  induction m; simpl.
  - destruct (eq_dec i j) eqn:Heqe1.
    + destruct (eq_dec j k0) eqn:Heqe2; auto.
      simpl; subst.
      now rewrite Heqe2.
    + destruct (eq_dec j k0) eqn:Heqe2; simpl; auto.
      * subst.
        now rewrite Heqe1.
      * now destruct (eq_dec i k0).
  - now destruct (eq_dec i j).
Qed.

Lemma compress_equiv `{EqDec k} m :
  m ≈ compress m.
Proof.
  apply FunctionalElimination_compress;
  repeat intro; auto.
  simpl in *.
  rewrite <- X.
  rewrite lookup_delete.
  now destruct (eq_dec k0 i').
Qed.

Lemma insert_delete `{EqDec k} i x m :
  insert i x (delete i m) ≈ insert i x m.
Proof.
  induction m; simpl; intros; auto.
  destruct (eq_dec i k0) eqn:Heqe.
  - subst.
    rewrite IHm; clear IHm.
    now rewrite lookup_insert.
  - simpl.
    rewrite Heqe; simpl.
    now rewrite IHm.
Qed.

Fixpoint insertWith `{EqDec k} (f : v → v → v) (i : k) (x : v) (m : Map) : Map :=
  match m with
  | Empty => singleton i x
  | Add i' x' m =>
      if eq_dec i i'
      then Add i (f x x') m
      else Add i' x' (insertWith f i x m)
  end.

Fixpoint insertWithKey `{EqDec k} (f : k → v → v → v) (i : k) (x : v) (m : Map) : Map :=
  match m with
  | Empty => singleton i x
  | Add i' x' m =>
      if eq_dec i i'
      then Add i (f i x x') m
      else Add i' x' (insertWithKey f i x m)
  end.

Fixpoint insertLookupWithKey `{EqDec k} (f : k → v → v → v) (i : k) (x : v) (m : Map) :
  option v * Map :=
  match m with
  | Empty => (None, singleton i x)
  | Add i' x' m =>
      if eq_dec i i'
      then (Some x', Add i (f i x x') m)
      else
        let '(old, m') := insertLookupWithKey f i x m in
        (old, Add i' x' m')
  end.

Fixpoint adjust `{EqDec k} (f : v → v) (i : k) (m : Map) : Map :=
  match m with
  | Empty => Empty
  | Add i' x' m =>
      if eq_dec i i'
      then Add i' (f x') m
      else Add i' x' (adjust f i m)
  end.

Fixpoint adjustWithKey `{EqDec k} (f : k → v → v) (i : k) (m : Map) : Map :=
  match m with
  | Empty => Empty
  | Add i' x' m =>
      if eq_dec i i'
      then Add i' (f i' x') m
      else Add i' x' (adjustWithKey f i m)
  end.

Fixpoint alter `{EqDec k} (f : option v → option v) (i : k) (m : Map) : Map :=
  match m with
  | Empty =>
      match f None with
      | None => empty
      | Some v => singleton i v
      end
  | Add i' x' m =>
      if eq_dec i i'
      then
        match f (Some x') with
        | None => m
        | Some v => Add i' v m
        end
      else Add i' x' (alter f i m)
  end.

End Map.

Arguments Map k v : clear implicits.

(* Functorial action (fmap) of the endofunctor [Map k -]: transport values
   along [f], leaving keys and structure fixed. *)
Fixpoint map `(f : v → b) `(m : Map k v) : Map k b :=
  match m with
  | Empty => Empty
  | Add i x m => Add i (f x) (map f m)
  end.

Fixpoint mapWithKey `(f : k → v → b) (m : Map k v) : Map k b :=
  match m with
  | Empty => Empty
  | Add i x m => Add i (f i x) (mapWithKey f m)
  end.

Fixpoint fold `(f : v → b → b) (z : b) `(m : Map k v) : b :=
  match m with
  | Empty => z
  | Add _ x m => fold f (f x z) m
  end.

Fixpoint foldrWithKey `(f : k → v → b → b) (z : b) (m : Map k v) : b :=
  match m with
  | Empty => z
  | Add i x m => f i x (foldrWithKey f z m)
  end.

Fixpoint foldlWithKey `(f : k → v → b → b) (z : b) (m : Map k v) : b :=
  match m with
  | Empty => z
  | Add i x m => foldlWithKey f (f i x z) m
  end.

Import ListNotations.

Fixpoint elems `(m : Map k v) : list v :=
  match m with
  | Empty => []
  | Add _ x m => x :: elems m
  end.

Fixpoint keys `(m : Map k v) : list k :=
  match m with
  | Empty => []
  | Add i _ m => i :: keys m
  end.

Definition assocs `(m : Map k v) : list (k * v) := toList m.

Fixpoint filter `(f : v → bool) `(m : Map k v) : Map k v :=
  match m with
  | Empty => Empty
  | Add i x m =>
      if f x
      then Add i x (filter f m)
      else filter f m
  end.

Fixpoint mapMaybe `(f : v → option b) `(m : Map k v) : Map k b :=
  match m with
  | Empty => Empty
  | Add i x m =>
      match f x with
      | Some x' => Add i x' (mapMaybe f m)
      | None => mapMaybe f m
      end
  end.
