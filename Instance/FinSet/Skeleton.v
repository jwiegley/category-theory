Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Skeleton.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * FinSet is skeletal *)

(* nLab: https://ncatlab.org/nlab/show/FinSet
   Wikipedia: https://en.wikipedia.org/wiki/Skeleton_(category_theory)

   Instance/FinSet.v has called itself "the skeletal category of finite
   sets" since it was written, and Structure/BiCCC/Strict.v and
   Structure/Topos.v both lean on that reading in prose.  This file turns
   the reading into the theorem [FinSet_Skeletal]: in [FinSet] isomorphic
   objects are EQUAL, i.e. an isomorphism [m ≅ n] of natural numbers forces
   [m = n].

   The argument is the pigeonhole principle twice.  [FinSet]'s hom-setoid is
   pointwise Leibniz equality, so the two isomorphism laws are literally
   [∀ i, from f (to f i) = i] and its mirror; each therefore makes one leg
   injective, and an injection [Fin.t m → Fin.t n] forces [m ≤ n]
   ([fin_inj_le]).  [Nat.le_antisymm] closes it.

   PORTABILITY.  The supporting list lemmas are proved locally on purpose,
   not imported:

   - [map_len] duplicates two lines rather than name [List.map_length]
     (deprecated on Rocq 9.1) or [length_map] (absent on Coq 8.19);
   - [NoDup_map_inj] is local because Coq.Logic.FinFun is not on this
     library's load path;
   - [fin_pred]/[fin_FS_inj] follow the version-portable idiom of
     Instance/FinSet/Classifier.v: the retraction is built from
     [Fin.caseS'] alone, so it stays within the primitives available on
     every supported version, and the file needs no dependence on
     stdlib's [Fin.FS_inj];
   - [all_fin] is redefined here rather than taken from
     Instance/FinSet/Pushout.v, whose copy comes attached to the whole
     union-find [components] development and carries neither its length nor
     its duplicate-freedom.

   These local names deliberately collide with the identically-named
   helpers of Instance/FinSet/Classifier.v and Instance/FinSet/Pushout.v;
   a consumer importing more than one of those files should qualify
   them.

   [FinSet_Skeleton] then packages [FinSet] as a [Skeleton] of itself
   through [Skeleton_of_Skeletal]; it is the trivial route, and the
   non-trivial witness for the [Skeleton] record lives in
   Theory/Skeleton/Separation.v. *)

(** ** Local list lemmas *)

Lemma map_len {A B : Type} (f : A → B) (l : list A) :
  List.length (List.map f l) = List.length l.
Proof. induction l; simpl; auto. Qed.

Lemma NoDup_map_inj {A B : Type} (f : A → B)
      (inj : ∀ x y, f x = f y → x = y) (l : list A) :
  List.NoDup l → List.NoDup (List.map f l).
Proof.
  induction 1; simpl; constructor; auto.
  intro Hin; apply List.in_map_iff in Hin as [z [Hz Hzin]].
  apply inj in Hz; subst; contradiction.
Qed.

(** ** Successor injectivity for [Fin.t], portably *)

Definition fin_pred {n : nat} (d : Fin.t n) (i : Fin.t (S n)) : Fin.t n :=
  Fin.caseS' i (fun _ => Fin.t n) d (fun j => j).

Lemma fin_FS_inj {n : nat} (x y : Fin.t n) : Fin.FS x = Fin.FS y → x = y.
Proof. intro H; exact (f_equal (fin_pred x) H). Qed.

(** ** The canonical enumeration of [Fin.t n] *)

Fixpoint all_fin (n : nat) : list (Fin.t n) :=
  match n with
  | O   => nil
  | S k => cons Fin.F1 (List.map (@Fin.FS k) (all_fin k))
  end.

Lemma all_fin_length (n : nat) : List.length (all_fin n) = n.
Proof. induction n; simpl; [reflexivity|]; now rewrite map_len, IHn. Qed.

Lemma all_fin_full (n : nat) (i : Fin.t n) : List.In i (all_fin n).
Proof.
  induction i as [k|k i IH]; simpl; [now left|].
  right; now apply List.in_map.
Qed.

Lemma all_fin_nodup (n : nat) : List.NoDup (all_fin n).
Proof.
  induction n as [|k IH]; simpl; [constructor|].
  constructor.
  - intro H; apply List.in_map_iff in H as [j [Hj _]]; discriminate.
  - apply NoDup_map_inj; [ exact (@fin_FS_inj k) | exact IH ].
Qed.

(** ** The pigeonhole principle *)

Lemma fin_inj_le {m n : nat} (f : Fin.t m → Fin.t n)
      (inj : ∀ i j, f i = f j → i = j) : (m <= n)%nat.
Proof.
  pose proof (List.NoDup_incl_length
                (l := List.map f (all_fin m)) (l' := all_fin n)) as H.
  rewrite map_len, !all_fin_length in H.
  apply H.
  - apply NoDup_map_inj; [exact inj | apply all_fin_nodup].
  - intros x _; apply all_fin_full.
Qed.

(** ** Skeletality *)

Theorem FinSet_Skeletal : Skeletal FinSet.
Proof.
  intros m n f.
  apply Nat.le_antisymm.
  - apply (fin_inj_le (to f)).
    intros i j Hij.
    pose proof (iso_from_to f i) as Hi.
    pose proof (iso_from_to f j) as Hj.
    simpl in Hi, Hj.
    now rewrite <- Hi, <- Hj, Hij.
  - apply (fin_inj_le (from f)).
    intros i j Hij.
    pose proof (iso_to_from f i) as Hi.
    pose proof (iso_to_from f j) as Hj.
    simpl in Hi, Hj.
    now rewrite <- Hi, <- Hj, Hij.
Qed.

Definition FinSet_Skeleton : Skeleton FinSet :=
  Skeleton_of_Skeletal FinSet_Skeletal.
