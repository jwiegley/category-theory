Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Matr.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * Row operations are left multiplication by a matrix

    Riehl, "Category Theory in Context", 2nd ed., §2.2, Corollary 2.2.10
    (printed p. 65) [riehl:2.2:cor10].
    nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
    Wikipedia: https://en.wikipedia.org/wiki/Elementary_matrix

    In the matrix category (Instance/Matr.v: objects the naturals, an
    arrow m ~> n an n × m matrix over a rig R), the matrices with n rows
    are the elements of the represented presheaf [Hom ─,n], and a ROW
    OPERATION — an operation defined uniformly on all matrices with n
    rows, commuting with right multiplication — is exactly a natural
    endomorphism of that presheaf.  The Yoneda lemma therefore makes
    Gaussian elimination categorical: every row operation is left
    multiplication by the single n × n matrix obtained by applying the
    operation to the identity, and that matrix is unique.

    THE DERIVATION IS THE POINT, as the issue insists: the corollary is
    read off Functor/Hom/Yoneda.v's [Yoneda_Embedding] — the setoid
    isomorphism  Presheaves [Hom ─,n] [Hom ─,n] ≊ (n ~> n)  — rather
    than proved by a matrix computation.  Its [from] direction IS
    left-multiplication, so the factorization is the round trip
    [iso_from_to] read pointwise, the representing matrix is the [to]
    direction (evaluation at the identity, [representing_matrix_at_id]),
    and uniqueness is injectivity of [to] through the other round trip.
    In the headline theorem no entry of any matrix is ever inspected
    (the supporting lemmas bind entry indices only to peel Matr's
    entrywise hom-setoid).

    NATURALITY IS LINEARITY.  The presheaf action of [Hom ─,n] is right
    multiplication, so the naturality square of an endomorphism η says
    η (M · f) ≈ η M · f — the "linearity in the columns" that lets an
    operation defined row-wise be applied before or after a change of
    basis on the source.  [row_operation_natural] and
    [Build_row_operation] state the two directions: every row operation
    has the property, and any ≈-respecting family with the property
    assembles into a row operation.

    THE WITNESS: swapping the two rows of a 2 × m matrix, packaged as
    [swap_rows_op] over any rig, with its representing matrix computed
    entrywise BY [eq_refl] over ℕ — the permutation matrix
    [[0,1],[1,0]], as Gaussian elimination expects. *)

(** ** Row operations *)

Section RowOps.

Context (R : RigObject).

(* A row operation on matrices with n rows: a natural endomorphism of
   the presheaf represented by n.  [Presheaves] is the functor category
   [(Matr R)^op, Sets]; its homs are natural transformations. *)
Definition row_operation (n : nat) : Type :=
  @hom (@Presheaves (Matr R) Sets)
    (@Curried_CoHom (Matr R) n) (@Curried_CoHom (Matr R) n).

(* Naturality, read concretely: a row operation commutes with right
   multiplication — the linearity the corollary's proof turns on. *)
Lemma row_operation_natural {n : nat} (η : row_operation n)
  {m m' : nat} (f : m' ~{Matr R}~> m) (M : m ~{Matr R}~> n) :
  transform[η] m' (M ∘[Matr R] f) ≈ transform[η] m M ∘[Matr R] f.
Proof.
  symmetry; exact (@naturality _ _ _ _ η _ _ f M).
Qed.

(* Conversely, any ≈-respecting family commuting with right
   multiplication is a row operation: naturality is EXACTLY that
   property, so the two notions coincide. *)
Program Definition Build_row_operation {n : nat}
  (φ : ∀ m : nat, (m ~{Matr R}~> n) → (m ~{Matr R}~> n))
  (φ_respects : ∀ m (M M' : m ~{Matr R}~> n),
     M ≈ M' → φ m M ≈ φ m M')
  (φ_linear : ∀ (m m' : nat) (f : m' ~{Matr R}~> m) (M : m ~{Matr R}~> n),
     φ m' (M ∘[Matr R] f) ≈ φ m M ∘[Matr R] f) :
  row_operation n :=
  Build_Transform' (F := @Curried_CoHom (Matr R) n)
    (G := @Curried_CoHom (Matr R) n)
    (fun m => {| morphism := φ m ; proper_morphism := φ_respects m |})
    _.

(** ** The corollary, through the Yoneda embedding *)

(* The representing matrix of a row operation: the [to] direction of the
   Yoneda embedding's isomorphism. *)
Definition representing_matrix {n : nat} (η : row_operation n) :
  n ~{Matr R}~> n :=
  to (Yoneda_Embedding (Matr R) n n) η.

(* It is the operation applied to the identity matrix — evaluation at
   the identity being the forward map of the Yoneda lemma. *)
Lemma representing_matrix_at_id {n : nat} (η : row_operation n) :
  representing_matrix η ≈ transform[η] n (@id (Matr R) n).
Proof.
  unfold representing_matrix; simpl.
  reflexivity.
Qed.

(* Riehl, Corollary 2.2.10: every row operation is left multiplication
   by its representing matrix.  The proof is the [iso_from_to] round
   trip of the embedding, read pointwise — the [from] direction is
   literally left-composition. *)
Theorem row_operations_are_left_multiplication {n : nat}
  (η : row_operation n) (m : nat) (M : m ~{Matr R}~> n) :
  transform[η] m M ≈ representing_matrix η ∘[Matr R] M.
Proof.
  symmetry.
  exact (iso_from_to (Yoneda_Embedding (Matr R) n n) η m M).
Qed.

(* ...and the representing matrix is unique: any matrix that acts as η
   by left multiplication is the representing matrix, by injectivity of
   the embedding's [to] through the other round trip. *)
Theorem representing_matrix_unique {n : nat}
  (η : row_operation n) (P : n ~{Matr R}~> n) :
  (∀ (m : nat) (M : m ~{Matr R}~> n),
     transform[η] m M ≈ P ∘[Matr R] M) →
  P ≈ representing_matrix η.
Proof.
  intro HP.
  rewrite <- (iso_to_from (Yoneda_Embedding (Matr R) n n) P).
  unfold representing_matrix.
  apply (proper_morphism (to (Yoneda_Embedding (Matr R) n n))).
  (* the transformations agree pointwise, in the opposite orientation *)
  intros m M i j; simpl.
  symmetry.
  apply (HP m M i j).
Qed.

End RowOps.

(** ** A worked elementary operation: swapping two rows *)

Section Swap.

Context (R : RigObject).

(* The transposition of Fin.t 2. *)
Definition fin2_swap (i : Fin.t 2) : Fin.t 2 :=
  match i with
  | Fin.F1 => Fin.FS Fin.F1
  | Fin.FS _ => Fin.F1
  end.

(* Swapping the two rows of a 2 × m matrix.  Rows are permuted, columns
   untouched, so right multiplication passes through — the linearity
   hypothesis is definitional. *)
Program Definition swap_rows_op : row_operation R 2 :=
  Build_row_operation R
    (fun m M => fun i j => M (fin2_swap i) j)
    _ _.

End Swap.

(** ** The representing matrix of the swap computes over ℕ *)

(* Applying the swap to the 2 × 2 identity yields the permutation matrix
   [[0,1],[1,0]], entry by entry, by pure computation. *)
Example swap_rep_00 :
  representing_matrix Nat_Rig (swap_rows_op Nat_Rig) Fin.F1 Fin.F1 = 0%nat
  := eq_refl.
Example swap_rep_01 :
  representing_matrix Nat_Rig (swap_rows_op Nat_Rig)
    Fin.F1 (Fin.FS Fin.F1) = 1%nat := eq_refl.
Example swap_rep_10 :
  representing_matrix Nat_Rig (swap_rows_op Nat_Rig)
    (Fin.FS Fin.F1) Fin.F1 = 1%nat := eq_refl.
Example swap_rep_11 :
  representing_matrix Nat_Rig (swap_rows_op Nat_Rig)
    (Fin.FS Fin.F1) (Fin.FS Fin.F1) = 0%nat := eq_refl.
