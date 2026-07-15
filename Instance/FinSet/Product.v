Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * Computable products on skeletal FinSet

    The product of the canonical m-element and n-element sets is the
    canonical (m * n)-element set, mediated by the standard base-n
    positional codec: the pair (a, b) is encoded as the digit string
    "a then b", i.e. the number a·n + b.  Both directions are structural
    fixpoints in the closed-computation style of [fin_split]/[fin_join]
    from [Instance/FinSet.v] — built only from [Fin.L], [Fin.R] and
    [fin_split], primitives available on every supported Coq/Rocq
    version — so pairings and projections REDUCE on closed inputs by
    [eq_refl].

    Since [Nat.mul] recurses as [S m' * n = n + m' * n], the encoding of
    (F1, b) is the first block [Fin.L (m' * n) b], and encoding along
    [Fin.FS] skips one block via [Fin.R n]. *)

(** [fin_pair a b] encodes the pair (a, b) as position a·n + b of the
    canonical (m * n)-element set, by structural recursion on [a]. *)
Fixpoint fin_pair {m n : nat} (a : Fin.t m) : Fin.t n → Fin.t (m * n) :=
  match a in Fin.t m return Fin.t n → Fin.t (m * n) with
  | @Fin.F1 m' => fun b => Fin.L (m' * n) b
  | @Fin.FS m' a' => fun b => Fin.R n (fin_pair a' b)
  end.

(** [fin_unpair] decodes a position of the canonical (m * n)-element set
    into its quotient/remainder pair, by structural recursion on [m]:
    each step peels one n-element block off through [fin_split]. *)
Fixpoint fin_unpair {m n : nat} {struct m} :
  Fin.t (m * n) → (Fin.t m * Fin.t n)%type :=
  match m return Fin.t (m * n) → (Fin.t m * Fin.t n)%type with
  | O => fun p => Fin.case0 (fun _ => (Fin.t 0 * Fin.t n)%type) p
  | S m' => fun p =>
      match @fin_split n (m' * n) p with
      | Datatypes.inl b => (Fin.F1, b)
      | Datatypes.inr q =>
          let '(a, b) := @fin_unpair m' n q in (Fin.FS a, b)
      end
  end.

(* The computability acceptance test: the codec reduces by [eq_refl].
   With m = 2, n = 3 the pair (1, 1) sits at position 1·3 + 1 = 4. *)
Example fin_pair_computes :
  @fin_pair 2 3 (Fin.FS Fin.F1) (Fin.FS Fin.F1)
    = Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))) := eq_refl.

Example fin_unpair_computes :
  @fin_unpair 2 3 (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
    = (Fin.FS Fin.F1, Fin.FS Fin.F1) := eq_refl.

(** ** The round trips

    Equality here is Leibniz equality on [Fin.t] VALUES — object-level
    data of the skeletal category, matching the pointwise-[eq] hom-setoid
    of [FinSet]. *)

Lemma fin_unpair_pair {m n : nat} (a : Fin.t m) (b : Fin.t n) :
  fin_unpair (fin_pair a b) = (a, b).
Proof.
  induction a as [m' | m' a IH]; simpl.
  - (* (F1, b) is the first block: split lands left. *)
    rewrite fin_split_L; reflexivity.
  - (* (FS a, b) skips one block: split lands right, then recurse. *)
    rewrite fin_split_R, IH; reflexivity.
Qed.

Lemma fin_pair_unpair {m n : nat} (p : Fin.t (m * n)) :
  fin_pair (fst (fin_unpair p)) (snd (fin_unpair p)) = p.
Proof.
  induction m as [| m' IH].
  - exact (Fin.case0
             (fun p : Fin.t 0 =>
                @fin_pair 0 n (fst (@fin_unpair 0 n p))
                              (snd (@fin_unpair 0 n p)) = p)
             p).
  - (* The scrutinee is spelled with explicit implicits so that it matches
       the occurrence [simpl] exposes in the goal. *)
    simpl; destruct (@fin_split n (m' * n) p) as [b | q] eqn:Hs.
    + (* p decodes as (F1, b): re-encoding is the left injection, and
         [fin_join_split] identifies it with p. *)
      simpl; rewrite <- (@fin_join_split n (m' * n) p), Hs; reflexivity.
    + (* p decodes through the recursive call on the tail q. *)
      specialize (IH q).
      destruct (@fin_unpair m' n q) as [a b]; simpl in IH.
      simpl; rewrite IH, <- (@fin_join_split n (m' * n) p), Hs.
      reflexivity.
Qed.

(** ** The cartesian structure

    The product object is [m * n], pairing is pointwise [fin_pair], and
    the projections are the components of [fin_unpair]; the universal
    property is exactly the two round trips, pointwise. *)

#[export] Program Instance FinSet_Cartesian : @Cartesian FinSet := {|
  product_obj := fun m n => (m * n)%nat;
  fork := fun x y z (f : Fin.t x → Fin.t y) (g : Fin.t x → Fin.t z) i =>
    fin_pair (f i) (g i);
  exl := fun y z (p : Fin.t (y * z)) => fst (fin_unpair p);
  exr := fun y z (p : Fin.t (y * z)) => snd (fin_unpair p)
|}.
Next Obligation.
  (* The pairing respects pointwise equality in both arguments. *)
  intros f f' Hf g g' Hg i.
  rewrite (Hf i), (Hg i); reflexivity.
Qed.
Next Obligation.
  (* The universal property: h ≈ ⟨f, g⟩ exactly when the two decodings of
     h recover f and g — pointwise, by the round trips. *)
  split.
  - intros Hh; split; intro i; simpl;
      rewrite (Hh i), fin_unpair_pair; reflexivity.
  - intros [Hl Hr] i.
    rewrite <- (Hl i), <- (Hr i), fin_pair_unpair; reflexivity.
Qed.

(* Closed pairings evaluated at concrete elements, by [eq_refl]: the fork
   of the two projections out of Fin.t 6 = Fin.t (2 * 3) re-encodes each
   element to itself, checked here at position 4 = (1, 1). *)
Example fork_computes :
  @fork FinSet FinSet_Cartesian 6%nat 2%nat 3%nat
    (fun p : Fin.t 6 => fst (@fin_unpair 2 3 p))
    (fun p : Fin.t 6 => snd (@fin_unpair 2 3 p))
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
    = Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))) := eq_refl.

(** ** Alignment with the terminal object

    The product with the chosen terminal object [1] of [FinSet_Terminal]
    lands on the nat [1 * n] (resp. [n * 1]), which is the object [n]
    itself: a propositional equality of OBJECTS of the skeletal category
    (nat values), recorded for downstream files that need to transport
    along the unitors on the nose. *)

Lemma FinSet_prod_one_l (n : nat) :
  @product_obj FinSet FinSet_Cartesian
    (@terminal_obj FinSet FinSet_Terminal) n = n.
Proof. apply Nat.mul_1_l. Qed.

Lemma FinSet_prod_one_r (n : nat) :
  @product_obj FinSet FinSet_Cartesian
    n (@terminal_obj FinSet FinSet_Terminal) = n.
Proof. apply Nat.mul_1_r. Qed.
