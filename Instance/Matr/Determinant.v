Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** * The determinant over a commutative ring

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.4
    (printed p. 16): the determinant is the archetypal natural
    transformation — for a commutative ring K, [det] is a map from the
    n × n matrices over K to K, natural in K, and multiplicative
    [maclane:I.4:construction1]; the same construction is what §I.4
    Exercise 6 needs [maclane:I.4:ex6].

    This file develops the determinant over Instance/Matr.v's matrix
    category, on the base [RingObject] of Theory/Algebra/Rig.v with the
    commutativity hypothesis stated exactly as Instance/Rng.v's
    [CRng_Sub] states it.  Everything is setoid-level: entries are
    compared with [≈], never [=], and no axiom is used anywhere.

    THE DEFINITION is the first-column Laplace expansion,
    [det A = Σ_i (-1)^i · A i 0 · det (minor A i 0)], by structural
    recursion on the size.  [fin_delete] is the order-preserving
    injection [Fin.t n → Fin.t (S n)] missing a given index, so
    [minor A i j] deletes row i and column j.

    THE ROAD TO MULTIPLICATIVITY.  [det_mul] is the load-bearing
    theorem, and the route is the classical one, arranged to avoid the
    two usual formalization sinkholes (a flat sum over the symmetric
    group, and the fixed-point-free-involution cancellation).

    - Multilinearity in each column ([det_col_add], [det_col_mul]) is
      immediate from the recursion: column 0 enters linearly, and every
      other column enters only through the minors.

    - The Laplace expansion along the first ROW ([det_row_expand]) is
      proved by induction, both sides reducing to the same double sum
      over a doubly-deleted matrix.  It is what makes alternation
      tractable: with columns 0 and 1 equal, the row expansion has only
      two surviving terms and their minors are literally the same
      matrix, so they cancel ([det_alt01]) — no involution argument.

    - From [det_alt01] the swap of columns 0 and 1 negates the
      determinant ([det_swap01], by bilinearity), a swap of two later
      columns negates it by induction through the minors
      ([det_swap_FS]), and a general transposition is a conjugate of
      those two ([det_swap]).  General alternation ([det_alt]) then
      follows by moving the two equal columns to positions 0 and 1 —
      note that it does NOT follow from [det M ≈ - det M], which says
      nothing in characteristic 2.

    - [det_perm]: for EVERY [f : Fin.t n → Fin.t n], injective or not,
      [det (A ∘ f) ≈ det (P f) · det A], where [P f] is the 0/1 matrix
      of f.  Proved by induction on n; the non-injective case is caught
      by a decidable finite search and killed by [det_alt].

    - The product expansion is organized as a NESTED sum ([expand])
      over the columns of B rather than a flat sum over functions, so
      neither the symmetric group nor the products [Π_j B (f j) j] ever
      need to be enumerated: [det (A ∘ B)] and [det B] are the same
      nested sum with different leaves, and [det_perm] relates the
      leaves by the constant factor [det A].

    THE ADJUGATE.  With both expansions in hand the rest of the
    classical package follows: [det_transpose] (the column-0 expansion
    of the transpose IS the row-0 expansion of the original, minor for
    minor), the expansion along an ARBITRARY column ([det_col_expand],
    through the cycle [rotf] that moves column j to the front — its
    permutation matrix has determinant [(-1)^j] by one application of
    the definition, with no induction, and [det_perm] supplies the
    rest), the alien-cofactor identity ([det_col_alien], which is the
    expansion of a matrix with one column overwritten by another), and
    hence [adj] with [adj_mul_l] and [adj_mul_r]:
    [adj A ∘ A ≈ A ∘ adj A ≈ det A · I].  A square matrix therefore has
    a two-sided inverse exactly when its determinant is a unit
    ([det_unit_of_inverse] and [inverse_of_det_unit], with
    [det_unit_of_iso] and [iso_of_det_unit] in [Matr]'s composition
    vocabulary).

    NATURALITY in the ring ([det_map]) is the [Matr]-level content of
    Mac Lane's §I.4: a rig homomorphism between rings commutes with
    [det], since the formula is polynomial.  No extra clause is needed
    for negation — that is Theory/Algebra/Rig.v's theorem [RigHom_neg].

    THREE SECTIONS.  [Determinant] fixes only the ring and carries what
    does not need commutativity: the ring arithmetic, [fin_delete],
    [pow_neg1], [minor], [det], [det_respects] and [det_id].
    [DeterminantComm] adds the commutativity hypothesis and carries
    everything from multilinearity to [det_mul]; since Lib.v's
    project-wide [Default Proof Using "Type"] discharges only the
    section variables occurring in a statement, that section sets
    ["All"], so its lemmas take the ring and its commutativity proof as
    their two leading arguments.  [DetMap] takes two rings and a
    homomorphism.  Everything is axiom-free: [Print Assumptions det_mul]
    answers "Closed under the global context". *)

Section Determinant.

Context (R : RingObject).

Notation K := (carrier (rig_setoid (ring_rig R))).

Local Infix "⊕" := (rig_add R) (at level 50, left associativity).
Local Infix "⊗" := (rig_mul R) (at level 40, left associativity).
Local Notation "⊖ x" := (ring_neg R x) (at level 35, right associativity).
Local Notation "0R" := (rig_zero R).
Local Notation "1R" := (rig_one R).

(** ** Ring arithmetic

    The consequences of the ring axioms used below that Instance/Rng.v
    does not already carry ([ring_neg_r], [ring_neg_add] and
    [ring_neg_involutive] are taken from there). *)

Lemma ring_neg_unique (a b : K) : a ⊕ b ≈ 0R → b ≈ ⊖ a.
Proof.
  intro H.
  rewrite <- (rig_add_zero_l R b).
  rewrite <- (ring_neg_l R a).
  rewrite rig_add_assoc.
  rewrite H.
  now rewrite rig_add_zero_r.
Qed.

(* Instance/Rng.v's [ring_neg_r] with the ring argument fixed, so that
   the rewrites below match without an explicit instantiation. *)
Lemma ring_neg_r' (a : K) : a ⊕ ⊖ a ≈ 0R.
Proof. apply ring_neg_r. Qed.

Lemma ring_neg_zero : ⊖ 0R ≈ 0R.
Proof.
  symmetry; apply ring_neg_unique.
  now rewrite rig_add_zero_l.
Qed.

Lemma ring_neg_mul_l (a b : K) : (⊖ a) ⊗ b ≈ ⊖ (a ⊗ b).
Proof.
  apply ring_neg_unique.
  rewrite <- rig_distr_r.
  rewrite ring_neg_r'.
  apply rig_mul_zero_l.
Qed.

Lemma ring_neg_mul_r (a b : K) : a ⊗ (⊖ b) ≈ ⊖ (a ⊗ b).
Proof.
  apply ring_neg_unique.
  rewrite <- rig_distr_l.
  rewrite ring_neg_r'.
  apply rig_mul_zero_r.
Qed.

(** ** Deleting an index

    [fin_delete skip] is the order-preserving injection whose image is
    everything but [skip]. *)

Fixpoint fin_delete {n : nat} : Fin.t (S n) → Fin.t n → Fin.t (S n) :=
  match n with
  | O => fun _ x => Fin.case0 _ x
  | S m => fun skip =>
      Fin.caseS' skip (fun _ => Fin.t (S m) → Fin.t (S (S m)))
        (fun x => Fin.FS x)
        (fun s x =>
           Fin.caseS' x (fun _ => Fin.t (S (S m)))
             Fin.F1
             (fun y => Fin.FS (fin_delete s y)))
  end.

Lemma fin_delete_F1 {n : nat} (x : Fin.t n) :
  fin_delete Fin.F1 x = Fin.FS x.
Proof. destruct n; [ inversion x | reflexivity ]. Qed.

Lemma fin_delete_FS_F1 {n : nat} (s : Fin.t (S n)) :
  fin_delete (Fin.FS s) Fin.F1 = Fin.F1.
Proof. reflexivity. Qed.

Lemma fin_delete_FS_FS {n : nat} (s : Fin.t (S n)) (y : Fin.t n) :
  fin_delete (Fin.FS s) (Fin.FS y) = Fin.FS (fin_delete s y).
Proof. reflexivity. Qed.

(* The image of [fin_delete skip] misses exactly [skip]. *)
Lemma fin_delete_neq {n : nat} (skip : Fin.t (S n)) (x : Fin.t n) :
  fin_delete skip x ≠ skip.
Proof.
  revert skip x; induction n; intros skip x; [ inversion x |].
  pattern skip; apply (Fin.caseS' skip); clear skip.
  - rewrite fin_delete_F1; discriminate.
  - intro s.
    pattern x; apply (Fin.caseS' x); clear x.
    + rewrite fin_delete_FS_F1; discriminate.
    + intros y Heq.
      rewrite fin_delete_FS_FS in Heq.
      exact (IHn s y (Fin.FS_inj _ _ Heq)).
Qed.

Lemma fin_delete_inj {n : nat} (skip : Fin.t (S n)) (x y : Fin.t n) :
  fin_delete skip x = fin_delete skip y → x = y.
Proof.
  revert skip x y; induction n; intros skip x y; [ inversion x |].
  pattern skip; apply (Fin.caseS' skip); clear skip.
  - rewrite !fin_delete_F1; apply Fin.FS_inj.
  - intro s.
    pattern x; apply (Fin.caseS' x); clear x;
      pattern y; apply (Fin.caseS' y); clear y.
    + reflexivity.
    + intros p Heq; rewrite fin_delete_FS_F1, fin_delete_FS_FS in Heq.
      discriminate.
    + intros p Heq; rewrite fin_delete_FS_F1, fin_delete_FS_FS in Heq.
      discriminate.
    + intros p q Heq.
      rewrite !fin_delete_FS_FS in Heq.
      now rewrite (IHn s q p (Fin.FS_inj _ _ Heq)).
Qed.

(** ** The index of a finite ordinal, and the alternating sign *)

Definition fidx {n : nat} (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).

Lemma fidx_F1 {n : nat} : @fidx (S n) Fin.F1 = 0%nat.
Proof. reflexivity. Qed.

Lemma fidx_FS {n : nat} (i : Fin.t n) : fidx (Fin.FS i) = S (fidx i).
Proof. unfold fidx; simpl; now destruct (Fin.to_nat i). Qed.

(* (-1)^k. *)
Fixpoint pow_neg1 (k : nat) : K :=
  match k with
  | O => 1R
  | S j => ⊖ (pow_neg1 j)
  end.

Lemma pow_neg1_S (k : nat) : pow_neg1 (S k) ≈ ⊖ (pow_neg1 k).
Proof. reflexivity. Qed.

Lemma pow_neg1_mul (a b : nat) :
  pow_neg1 (a + b)%nat ≈ pow_neg1 a ⊗ pow_neg1 b.
Proof.
  induction a; simpl.
  - now rewrite rig_mul_one_l.
  - rewrite IHa; now rewrite ring_neg_mul_l.
Qed.

(** ** The determinant, by first-column Laplace expansion *)

Definition minor {n : nat} (A : Matrix R (S n) (S n)) (i j : Fin.t (S n)) :
  Matrix R n n :=
  fun r c => A (fin_delete i r) (fin_delete j c).

Fixpoint det {n : nat} : Matrix R n n → K :=
  match n with
  | O => fun _ => 1R
  | S k => fun A =>
      fin_sum R (fun i : Fin.t (S k) =>
        pow_neg1 (fidx i) ⊗ A i Fin.F1 ⊗ det (minor A i Fin.F1))
  end.

(* The two unfolding steps, as rewrite rules: [simpl] would unfold the
   finite sum as well and leave the goal in a shape the [fin_sum] kit no
   longer matches. *)
Lemma det_S {n : nat} (A : Matrix R (S n) (S n)) :
  det A = fin_sum R (fun i : Fin.t (S n) =>
            pow_neg1 (fidx i) ⊗ A i Fin.F1 ⊗ det (minor A i Fin.F1)).
Proof. reflexivity. Qed.

Lemma fin_sum_S {n : nat} (f : Fin.t (S n) → K) :
  fin_sum R f = rig_add R (f Fin.F1) (fin_sum R (fun i => f (Fin.FS i))).
Proof. reflexivity. Qed.

Lemma det_respects {n : nat} (A B : Matrix R n n) :
  (∀ i j, A i j ≈ B i j) → det A ≈ det B.
Proof.
  revert A B; induction n; intros A B H; [ reflexivity |].
  rewrite !det_S.
  apply fin_sum_respects; intro i.
  apply rig_mul_respects.
  - apply rig_mul_respects; [ reflexivity | apply H ].
  - apply IHn; intros r c; apply H.
Qed.

(** ** The determinant of the identity *)

Lemma delta_FS {n : nat} (i j : Fin.t n) :
  delta R (Fin.FS i) (Fin.FS j) ≈ delta R i j.
Proof.
  unfold delta.
  destruct (Fin.eq_dec i j) as [He|Hne],
           (Fin.eq_dec (Fin.FS i) (Fin.FS j)) as [He'|Hne'];
    try reflexivity.
  - contradiction Hne'; now rewrite He.
  - contradiction Hne; now apply Fin.FS_inj.
Qed.

Lemma det_id {n : nat} : det (fun i j : Fin.t n => delta R i j) ≈ 1R.
Proof.
  induction n; [ reflexivity |].
  rewrite det_S, fin_sum_S.
  rewrite (fin_sum_respects R
    (fun i : Fin.t n =>
       pow_neg1 (fidx (Fin.FS i)) ⊗ delta R (Fin.FS i) Fin.F1
         ⊗ det (minor (fun p q : Fin.t (S n) => delta R p q)
                  (Fin.FS i) Fin.F1))
    (fun _ => 0R)).
  2: { intro i.
       rewrite (delta_neq R (Fin.FS i) Fin.F1) by discriminate.
       rewrite rig_mul_zero_r.
       apply rig_mul_zero_l. }
  rewrite fin_sum_zero, rig_add_zero_r.
  rewrite delta_refl.
  rewrite rig_mul_one_l, rig_mul_one_l.
  transitivity (det (fun i j : Fin.t n => delta R i j)); [| exact IHn ].
  apply det_respects; intros r c; unfold minor.
  rewrite !fin_delete_F1.
  apply delta_FS.
Qed.

End Determinant.

(** * The commutative development

    Everything from here on spends commutativity of the base ring.  The
    section sets [Default Proof Using "All"] (Lib.v's project-wide
    default is ["Type"], which discharges only the section variables
    occurring in a statement, and [Rcomm] occurs in almost none of
    them), so every lemma below takes the ring and its commutativity
    proof as its two leading arguments. *)

Section DeterminantComm.

Context (R : RingObject).
Context (Rcomm : ∀ a b, rig_mul R a b ≈ rig_mul R b a).

Set Default Proof Using "All".

Notation K := (carrier (rig_setoid (ring_rig R))).

Local Infix "⊕" := (rig_add R) (at level 50, left associativity).
Local Infix "⊗" := (rig_mul R) (at level 40, left associativity).
Local Notation "⊖ x" := (ring_neg R x) (at level 35, right associativity).
Local Notation "0R" := (rig_zero R).
Local Notation "1R" := (rig_one R).

Local Notation det := (det R).
Local Notation minor := (minor R).
Local Notation pow_neg1 := (pow_neg1 R).

(** ** Multilinearity in the columns

    Column 0 enters the recursion linearly and every other column enters
    only through the minors, so both clauses are a direct induction.
    The hypotheses are stated in "agree away from column j" form rather
    than through a substitution operator, which keeps them free of
    decidable-equality noise at the point of use. *)

Lemma mul_swap (a b c : K) : a ⊗ (b ⊗ c) ≈ b ⊗ (a ⊗ c).
Proof. rewrite <- !rig_mul_assoc; now rewrite (Rcomm a b). Qed.

Lemma mul_pull (p x b d : K) : p ⊗ (x ⊗ b) ⊗ d ≈ x ⊗ (p ⊗ b ⊗ d).
Proof. rewrite (mul_swap p x b); apply rig_mul_assoc. Qed.

Lemma det_col_add {n : nat} (A B C : Matrix R n n) (j : Fin.t n) :
  (∀ i k, k ≠ j → A i k ≈ B i k) →
  (∀ i k, k ≠ j → A i k ≈ C i k) →
  (∀ i, A i j ≈ B i j ⊕ C i j) →
  det A ≈ det B ⊕ det C.
Proof.
  revert A B C j; induction n as [|k IH]; intros A B C j.
  - inversion j.
  - pattern j; apply (Fin.caseS' j).
    + intros HB HC Hj.
      rewrite !det_S, <- fin_sum_add.
      apply fin_sum_respects; intro i.
      assert (HmB : det (minor A i Fin.F1) ≈ det (minor B i Fin.F1)).
      { apply det_respects; intros r c; unfold minor.
        rewrite fin_delete_F1; apply HB; discriminate. }
      assert (HmC : det (minor A i Fin.F1) ≈ det (minor C i Fin.F1)).
      { apply det_respects; intros r c; unfold minor.
        rewrite fin_delete_F1; apply HC; discriminate. }
      transitivity ((pow_neg1 (fidx i) ⊗ B i Fin.F1 ⊗ det (minor A i Fin.F1))
                      ⊕ (pow_neg1 (fidx i) ⊗ C i Fin.F1
                           ⊗ det (minor A i Fin.F1))).
      * rewrite <- rig_distr_r.
        apply rig_mul_respects; [| reflexivity ].
        rewrite <- rig_distr_l.
        apply rig_mul_respects; [ reflexivity | apply Hj ].
      * apply rig_add_respects; apply rig_mul_respects;
          first [ reflexivity | assumption ].
    + intros j0 HB HC Hj.
      rewrite !det_S, <- fin_sum_add.
      apply fin_sum_respects; intro i.
      assert (Hm : det (minor A i Fin.F1)
                     ≈ det (minor B i Fin.F1) ⊕ det (minor C i Fin.F1)).
      { apply (IH _ _ _ j0).
        - intros r c Hc; unfold minor; rewrite fin_delete_F1.
          apply HB; intro Heq; apply Hc; exact (Fin.FS_inj _ _ Heq).
        - intros r c Hc; unfold minor; rewrite fin_delete_F1.
          apply HC; intro Heq; apply Hc; exact (Fin.FS_inj _ _ Heq).
        - intro r; unfold minor; rewrite fin_delete_F1; apply Hj. }
      rewrite Hm, rig_distr_l.
      apply rig_add_respects; apply rig_mul_respects; try reflexivity.
      * apply rig_mul_respects; [ reflexivity |].
        apply HB; discriminate.
      * apply rig_mul_respects; [ reflexivity |].
        apply HC; discriminate.
Qed.

Lemma det_col_mul {n : nat} (A B : Matrix R n n) (j : Fin.t n) (x : K) :
  (∀ i k, k ≠ j → A i k ≈ B i k) →
  (∀ i, A i j ≈ x ⊗ B i j) →
  det A ≈ x ⊗ det B.
Proof.
  revert A B j; induction n as [|k IH]; intros A B j.
  - inversion j.
  - pattern j; apply (Fin.caseS' j).
    + intros HB Hj.
      rewrite !det_S, fin_sum_mul_l.
      apply fin_sum_respects; intro i.
      assert (HmB : det (minor A i Fin.F1) ≈ det (minor B i Fin.F1)).
      { apply det_respects; intros r c; unfold minor.
        rewrite fin_delete_F1; apply HB; discriminate. }
      rewrite HmB, (Hj i).
      apply mul_pull.
    + intros j0 HB Hj.
      rewrite !det_S, fin_sum_mul_l.
      apply fin_sum_respects; intro i.
      assert (Hm : det (minor A i Fin.F1) ≈ x ⊗ det (minor B i Fin.F1)).
      { apply (IH _ _ j0).
        - intros r c Hc; unfold minor; rewrite fin_delete_F1.
          apply HB; intro Heq; apply Hc; exact (Fin.FS_inj _ _ Heq).
        - intro r; unfold minor; rewrite fin_delete_F1; apply Hj. }
      rewrite Hm.
      rewrite (HB i Fin.F1) by discriminate.
      apply mul_swap.
Qed.

(* A zero column kills the determinant: the scalar clause at x = 0. *)
Lemma det_col_zero {n : nat} (A : Matrix R n n) (j : Fin.t n) :
  (∀ i, A i j ≈ 0R) → det A ≈ 0R.
Proof.
  intro Hj.
  rewrite (det_col_mul A A j 0R).
  - apply rig_mul_zero_l.
  - reflexivity.
  - intro i; rewrite (Hj i); symmetry; apply rig_mul_zero_l.
Qed.

(** ** The Laplace expansion along the first row

    Both the definition (expansion along column 0) and the row expansion
    reduce, after one further expansion of each minor, to the same
    double sum over the matrix with row 0 and row i, and column 0 and
    column j, deleted — the terms MATCH pairwise, so no cancellation or
    involution argument is needed.  This is the one place where the two
    orders of deletion have to be reconciled, and [fin_delete] was
    defined so that both reconciliations
    ([fin_delete F1 c = FS c] and
     [fin_delete (FS i) (FS r) = FS (fin_delete i r)]) hold by
    conversion. *)

Lemma row_expand_term (p q x y d : K) :
  (⊖ p) ⊗ x ⊗ (q ⊗ y ⊗ d) ≈ (⊖ q) ⊗ y ⊗ (p ⊗ x ⊗ d).
Proof.
  rewrite !ring_neg_mul_l.
  now rewrite (mul_swap (p ⊗ x) (q ⊗ y) d).
Qed.

Lemma det_row_expand {n : nat} (A : Matrix R (S n) (S n)) :
  det A ≈ fin_sum R (fun j : Fin.t (S n) =>
            pow_neg1 (fidx j) ⊗ A Fin.F1 j ⊗ det (minor A Fin.F1 j)).
Proof.
  revert A; induction n as [|m IH]; intro A.
  - rewrite (det_S R A); reflexivity.
  - rewrite (det_S R A).
    rewrite (fin_sum_S R (fun i : Fin.t (S (S m)) =>
      pow_neg1 (fidx i) ⊗ A i Fin.F1 ⊗ det (minor A i Fin.F1))).
    rewrite (fin_sum_S R (fun j : Fin.t (S (S m)) =>
      pow_neg1 (fidx j) ⊗ A Fin.F1 j ⊗ det (minor A Fin.F1 j))).
    apply rig_add_respects; [ reflexivity |].
    (* Expand each minor of the column-0 expansion along ITS first row. *)
    transitivity
      (fin_sum R (fun i : Fin.t (S m) => fin_sum R (fun c : Fin.t (S m) =>
         pow_neg1 (fidx (Fin.FS i)) ⊗ A (Fin.FS i) Fin.F1
           ⊗ (pow_neg1 (fidx c) ⊗ A Fin.F1 (Fin.FS c)
                ⊗ det (fun r' c' => A (Fin.FS (fin_delete i r'))
                                      (Fin.FS (fin_delete c c'))))))).
    { apply fin_sum_respects; intro i.
      rewrite (IH (minor A (Fin.FS i) Fin.F1)).
      rewrite fin_sum_mul_l.
      apply fin_sum_respects; intro c.
      apply rig_mul_respects; [ reflexivity |].
      apply rig_mul_respects.
      - apply rig_mul_respects; [ reflexivity |].
        unfold minor; rewrite fin_delete_FS_F1, fin_delete_F1; reflexivity.
      - apply det_respects; intros r' c'; unfold minor.
        rewrite !fin_delete_F1, fin_delete_FS_FS; reflexivity. }
    (* Exchange the two sums and match the terms. *)
    transitivity
      (fin_sum R (fun c : Fin.t (S m) => fin_sum R (fun i : Fin.t (S m) =>
         pow_neg1 (fidx (Fin.FS c)) ⊗ A Fin.F1 (Fin.FS c)
           ⊗ (pow_neg1 (fidx i) ⊗ A (Fin.FS i) Fin.F1
                ⊗ det (fun r' c' => A (Fin.FS (fin_delete i r'))
                                      (Fin.FS (fin_delete c c'))))))).
    { rewrite (fin_sum_swap R (fun i c : Fin.t (S m) =>
         pow_neg1 (fidx (Fin.FS i)) ⊗ A (Fin.FS i) Fin.F1
           ⊗ (pow_neg1 (fidx c) ⊗ A Fin.F1 (Fin.FS c)
                ⊗ det (fun r' c' => A (Fin.FS (fin_delete i r'))
                                      (Fin.FS (fin_delete c c')))))).
      apply fin_sum_respects; intro c.
      apply fin_sum_respects; intro i.
      rewrite !fidx_FS, !pow_neg1_S.
      apply row_expand_term. }
    (* Fold the inner sum back into the minor of the row expansion. *)
    apply fin_sum_respects; intro c.
    rewrite <- fin_sum_mul_l.
    apply rig_mul_respects; [ reflexivity |].
    rewrite (det_S R (minor A Fin.F1 (Fin.FS c))).
    apply fin_sum_respects; intro i.
    apply rig_mul_respects.
    + apply rig_mul_respects; [ reflexivity |].
      unfold minor; rewrite fin_delete_F1, fin_delete_FS_F1; reflexivity.
    + apply det_respects; intros r' c'; unfold minor.
      rewrite !fin_delete_F1, fin_delete_FS_FS; reflexivity.
Qed.

(** ** Alternation

    With columns 0 and 1 equal, the row expansion has exactly two
    surviving terms: deleting any LATER column leaves columns 0 and 1
    still equal and still adjacent, so those minors vanish by induction,
    while deleting column 0 or column 1 leaves literally the same
    matrix.  The two survivors carry opposite signs and cancel. *)

Lemma add_head_zero (a b c : K) : a ⊕ b ≈ 0R → a ⊕ (b ⊕ c) ≈ c.
Proof using Type.
  intro H; rewrite <- rig_add_assoc, H; apply rig_add_zero_l.
Qed.

Lemma neg_cancel_terms (x d : K) :
  pow_neg1 0 ⊗ x ⊗ d ⊕ pow_neg1 1 ⊗ x ⊗ d ≈ 0R.
Proof using Type.
  simpl.
  rewrite rig_mul_one_l.
  rewrite ring_neg_mul_l, rig_mul_one_l, ring_neg_mul_l.
  apply ring_neg_r'.
Qed.

(* The head of the row expansion cancels, leaving only the columns from
   position 2 on. *)
Lemma det_alt01_tail {n : nat} (A : Matrix R (S (S n)) (S (S n))) :
  (∀ i, A i Fin.F1 ≈ A i (Fin.FS Fin.F1)) →
  det A ≈ fin_sum R (fun j : Fin.t n =>
    pow_neg1 (fidx (Fin.FS (Fin.FS j))) ⊗ A Fin.F1 (Fin.FS (Fin.FS j))
      ⊗ det (minor A Fin.F1 (Fin.FS (Fin.FS j)))).
Proof.
  intro Heq.
  rewrite det_row_expand, fin_sum_S, fin_sum_S.
  cbv beta.
  apply add_head_zero.
  assert (Hm : det (minor A Fin.F1 Fin.F1)
                 ≈ det (minor A Fin.F1 (Fin.FS Fin.F1))).
  { apply det_respects; intros r c; unfold minor.
    rewrite !fin_delete_F1.
    pattern c; apply (Fin.caseS' c).
    - rewrite fin_delete_FS_F1; symmetry; apply Heq.
    - intro c0; rewrite fin_delete_FS_FS, fin_delete_F1; reflexivity. }
  rewrite Hm, (Heq Fin.F1).
  apply neg_cancel_terms.
Qed.

Lemma det_alt01 {n : nat} (A : Matrix R (S (S n)) (S (S n))) :
  (∀ i, A i Fin.F1 ≈ A i (Fin.FS Fin.F1)) → det A ≈ 0R.
Proof.
  revert A; induction n as [|n' IH]; intros A Heq.
  - rewrite (det_alt01_tail A Heq); reflexivity.
  - rewrite (det_alt01_tail A Heq).
    rewrite (fin_sum_respects R _ (fun _ => 0R)).
    + apply fin_sum_zero.
    + intro j.
      rewrite (IH (minor A Fin.F1 (Fin.FS (Fin.FS j)))).
      * apply rig_mul_zero_r.
      * intro i; unfold minor.
        rewrite !fin_delete_F1, fin_delete_FS_F1, fin_delete_FS_FS,
          fin_delete_FS_F1.
        apply Heq.
Qed.

(** ** Transpositions of columns

    [fswap p q] is the transposition of the index set; the determinant
    of a column-transposed matrix is the negative.  Position (0,1) comes
    from alternation by bilinearity, a transposition of two LATER
    columns comes by induction through the minors, and the general case
    is the conjugate [τ σ τ] of those two. *)

Definition fswap {n : nat} (p q x : Fin.t n) : Fin.t n :=
  match Fin.eq_dec x p with
  | left _ => q
  | right _ => match Fin.eq_dec x q with
               | left _ => p
               | right _ => x
               end
  end.

Lemma fswap_l {n : nat} (p q : Fin.t n) : fswap p q p = q.
Proof using Type.
  unfold fswap; destruct (Fin.eq_dec p p) as [_|Hne];
    [ reflexivity | now contradiction Hne ].
Qed.

Lemma fswap_r {n : nat} (p q : Fin.t n) : fswap p q q = p.
Proof using Type.
  unfold fswap; destruct (Fin.eq_dec q p) as [He|_]; [ now rewrite He |].
  destruct (Fin.eq_dec q q) as [_|Hne];
    [ reflexivity | now contradiction Hne ].
Qed.

Lemma fswap_other {n : nat} (p q x : Fin.t n) :
  x ≠ p → x ≠ q → fswap p q x = x.
Proof using Type.
  intros Hp Hq; unfold fswap.
  destruct (Fin.eq_dec x p); [ contradiction |].
  destruct (Fin.eq_dec x q); [ contradiction | reflexivity ].
Qed.

Lemma fswap_involutive {n : nat} (p q x : Fin.t n) :
  fswap p q (fswap p q x) = x.
Proof using Type.
  unfold fswap at 2.
  destruct (Fin.eq_dec x p) as [He|Hp]; [ now rewrite fswap_r, He |].
  destruct (Fin.eq_dec x q) as [He|Hq]; [ now rewrite fswap_l, He |].
  now apply fswap_other.
Qed.

(* A matrix with its first two columns replaced. *)
Definition put01 {n : nat} (A : Matrix R (S (S n)) (S (S n)))
  (u v : Fin.t (S (S n)) → K) : Matrix R (S (S n)) (S (S n)) :=
  fun i j =>
    match Fin.eq_dec j Fin.F1 with
    | left _ => u i
    | right _ =>
        match Fin.eq_dec j (Fin.FS Fin.F1) with
        | left _ => v i
        | right _ => A i j
        end
    end.

Lemma put01_0 {n : nat} (A : Matrix R (S (S n)) (S (S n))) u v i :
  put01 A u v i Fin.F1 = u i.
Proof using Type.
  unfold put01; destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|Hne];
    [ reflexivity | now contradiction Hne ].
Qed.

Lemma put01_1 {n : nat} (A : Matrix R (S (S n)) (S (S n))) u v i :
  put01 A u v i (Fin.FS Fin.F1) = v i.
Proof using Type.
  unfold put01.
  destruct (Fin.eq_dec (Fin.FS Fin.F1) Fin.F1); [ discriminate |].
  destruct (Fin.eq_dec (Fin.FS Fin.F1) (Fin.FS Fin.F1)) as [_|Hne];
    [ reflexivity | now contradiction Hne ].
Qed.

Lemma put01_off {n : nat} (A : Matrix R (S (S n)) (S (S n))) u v i k :
  k ≠ Fin.F1 → k ≠ Fin.FS Fin.F1 → put01 A u v i k = A i k.
Proof using Type.
  intros H0 H1; unfold put01.
  destruct (Fin.eq_dec k Fin.F1); [ contradiction |].
  destruct (Fin.eq_dec k (Fin.FS Fin.F1)); [ contradiction | reflexivity ].
Qed.

Lemma put01_off0 {n : nat} (A : Matrix R (S (S n)) (S (S n))) u u' v i k :
  k ≠ Fin.F1 → put01 A u v i k = put01 A u' v i k.
Proof using Type.
  intro H0; unfold put01.
  destruct (Fin.eq_dec k Fin.F1); [ contradiction | reflexivity ].
Qed.

Lemma put01_off1 {n : nat} (A : Matrix R (S (S n)) (S (S n))) u v v' i k :
  k ≠ Fin.FS Fin.F1 → put01 A u v i k = put01 A u v' i k.
Proof using Type.
  intro H1; unfold put01.
  destruct (Fin.eq_dec k Fin.F1); [ reflexivity |].
  destruct (Fin.eq_dec k (Fin.FS Fin.F1)); [ contradiction | reflexivity ].
Qed.

Lemma det_swap01 {n : nat} (A : Matrix R (S (S n)) (S (S n))) :
  det (fun i j => A i (fswap Fin.F1 (Fin.FS Fin.F1) j)) ≈ ⊖ (det A).
Proof.
  pose (c0 := fun i : Fin.t (S (S n)) => A i Fin.F1).
  pose (c1 := fun i : Fin.t (S (S n)) => A i (Fin.FS Fin.F1)).
  pose (s := fun i : Fin.t (S (S n)) => c0 i ⊕ c1 i).
  (* The doubled matrix has equal first two columns. *)
  assert (Hzero : det (put01 A s s) ≈ 0R).
  { apply det_alt01; intro i; rewrite put01_0, put01_1; reflexivity. }
  (* Split column 0, then column 1 in each half. *)
  assert (H1 : det (put01 A s s)
                 ≈ det (put01 A c0 s) ⊕ det (put01 A c1 s)).
  { apply (det_col_add _ _ _ Fin.F1).
    - intros i k Hk; rewrite (put01_off0 A s c0 s i k Hk); reflexivity.
    - intros i k Hk; rewrite (put01_off0 A s c1 s i k Hk); reflexivity.
    - intro i; rewrite !put01_0; reflexivity. }
  assert (H2 : det (put01 A c0 s)
                 ≈ det (put01 A c0 c0) ⊕ det (put01 A c0 c1)).
  { apply (det_col_add _ _ _ (Fin.FS Fin.F1)).
    - intros i k Hk; rewrite (put01_off1 A c0 s c0 i k Hk); reflexivity.
    - intros i k Hk; rewrite (put01_off1 A c0 s c1 i k Hk); reflexivity.
    - intro i; rewrite !put01_1; reflexivity. }
  assert (H3 : det (put01 A c1 s)
                 ≈ det (put01 A c1 c0) ⊕ det (put01 A c1 c1)).
  { apply (det_col_add _ _ _ (Fin.FS Fin.F1)).
    - intros i k Hk; rewrite (put01_off1 A c1 s c0 i k Hk); reflexivity.
    - intros i k Hk; rewrite (put01_off1 A c1 s c1 i k Hk); reflexivity.
    - intro i; rewrite !put01_1; reflexivity. }
  assert (H4 : det (put01 A c0 c0) ≈ 0R).
  { apply det_alt01; intro i; rewrite put01_0, put01_1; reflexivity. }
  assert (H5 : det (put01 A c1 c1) ≈ 0R).
  { apply det_alt01; intro i; rewrite put01_0, put01_1; reflexivity. }
  assert (H6 : det (put01 A c0 c1) ≈ det A).
  { apply det_respects; intros i j.
    destruct (Fin.eq_dec j Fin.F1) as [He|H0].
    - rewrite He, put01_0; reflexivity.
    - destruct (Fin.eq_dec j (Fin.FS Fin.F1)) as [He|H1'].
      + rewrite He, put01_1; reflexivity.
      + rewrite (put01_off A c0 c1 i j H0 H1'); reflexivity. }
  assert (H7 : det (put01 A c1 c0)
                 ≈ det (fun i j => A i (fswap Fin.F1 (Fin.FS Fin.F1) j))).
  { apply det_respects; intros i j.
    destruct (Fin.eq_dec j Fin.F1) as [He|H0].
    - rewrite He, put01_0, fswap_l; reflexivity.
    - destruct (Fin.eq_dec j (Fin.FS Fin.F1)) as [He|H1'].
      + rewrite He, put01_1, fswap_r; reflexivity.
      + rewrite (put01_off A c1 c0 i j H0 H1'), (fswap_other _ _ _ H0 H1').
        reflexivity. }
  (* 0 ≈ (0 ⊕ det A) ⊕ (det (swap) ⊕ 0) *)
  rewrite H1, H2, H3, H4, H5, H6, H7 in Hzero.
  rewrite rig_add_zero_l, rig_add_zero_r in Hzero.
  apply ring_neg_unique; exact Hzero.
Qed.

Lemma fin_sum_neg {m : nat} (f : Fin.t m → K) :
  fin_sum R (fun i => ⊖ (f i)) ≈ ⊖ (fin_sum R f).
Proof using Type.
  induction m; simpl.
  - symmetry; apply ring_neg_zero.
  - rewrite IHm; symmetry; apply ring_neg_add.
Qed.

Lemma fswap_sym {n : nat} (p q x : Fin.t n) : fswap p q x = fswap q p x.
Proof using Type.
  destruct (Fin.eq_dec x p) as [->|Hp].
  - rewrite fswap_l, fswap_r; reflexivity.
  - destruct (Fin.eq_dec x q) as [->|Hq].
    + rewrite fswap_r, fswap_l; reflexivity.
    + rewrite (fswap_other p q x Hp Hq), (fswap_other q p x Hq Hp).
      reflexivity.
Qed.

Lemma fswap_FS {n : nat} (p q c : Fin.t n) :
  fswap (Fin.FS p) (Fin.FS q) (Fin.FS c) = Fin.FS (fswap p q c).
Proof using Type.
  destruct (Fin.eq_dec c p) as [->|Hp].
  - rewrite fswap_l, fswap_l; reflexivity.
  - destruct (Fin.eq_dec c q) as [->|Hq].
    + rewrite fswap_r, fswap_r; reflexivity.
    + assert (H1 : Fin.FS c ≠ Fin.FS p)
        by (intro Heq; apply Hp; exact (Fin.FS_inj _ _ Heq)).
      assert (H2 : Fin.FS c ≠ Fin.FS q)
        by (intro Heq; apply Hq; exact (Fin.FS_inj _ _ Heq)).
      rewrite (fswap_other _ _ _ H1 H2), (fswap_other _ _ _ Hp Hq).
      reflexivity.
Qed.

Lemma fin1_singleton (x : Fin.t 1) : x = Fin.F1.
Proof using Type.
  pattern x; apply (Fin.caseS' x); [ reflexivity | intro y; inversion y ].
Qed.

Lemma fin_not_F1 {n : nat} (x : Fin.t (S n)) :
  x ≠ Fin.F1 → { y : Fin.t n & x = Fin.FS y }.
Proof using Type.
  pattern x; apply (Fin.caseS' x).
  - intro H; exfalso; now apply H.
  - intros y _; exists y; reflexivity.
Qed.

(* Transposing two columns other than the first: the first column is
   untouched and each minor undergoes the corresponding transposition
   one size down. *)
Lemma det_swap_FS {n : nat} (A : Matrix R (S n) (S n)) (p q : Fin.t n)
  (IH : ∀ (B : Matrix R n n) (u v : Fin.t n), u ≠ v →
          det (fun i j => B i (fswap u v j)) ≈ ⊖ (det B)) :
  p ≠ q → det (fun i j => A i (fswap (Fin.FS p) (Fin.FS q) j)) ≈ ⊖ (det A).
Proof.
  intro Hpq.
  assert (Hfirst : fswap (Fin.FS p) (Fin.FS q) Fin.F1 = Fin.F1).
  { apply fswap_other; discriminate. }
  rewrite (det_S R (fun i j => A i (fswap (Fin.FS p) (Fin.FS q) j))).
  rewrite (det_S R A), <- fin_sum_neg.
  apply fin_sum_respects; intro i.
  assert (Hminor :
    det (minor (fun i' j => A i' (fswap (Fin.FS p) (Fin.FS q) j)) i Fin.F1)
      ≈ ⊖ (det (minor A i Fin.F1))).
  { transitivity (det (fun r c => minor A i Fin.F1 r (fswap p q c))).
    - apply det_respects; intros r c; unfold minor.
      rewrite !fin_delete_F1, fswap_FS; reflexivity.
    - apply (IH (minor A i Fin.F1) p q Hpq). }
  rewrite Hminor, Hfirst.
  apply ring_neg_mul_r.
Qed.

(* Transposing the first column with a later one: adjacent by
   [det_swap01], otherwise the conjugate τ σ τ of an adjacent swap by a
   swap of two later columns. *)
Lemma fswap_conj {n : nat} (q1 : Fin.t n) (x : Fin.t (S (S n))) :
  fswap Fin.F1 (Fin.FS (Fin.FS q1)) x
  = fswap Fin.F1 (Fin.FS Fin.F1)
      (fswap (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1))
         (fswap Fin.F1 (Fin.FS Fin.F1) x)).
Proof using Type.
  assert (HQ0 : Fin.FS (Fin.FS q1) ≠ (Fin.F1 : Fin.t (S (S n))))
    by discriminate.
  assert (HQ1 : Fin.FS (Fin.FS q1) ≠ Fin.FS (Fin.F1 : Fin.t (S n)))
    by (intro Hx; apply Fin.FS_inj in Hx; discriminate).
  assert (H10 : Fin.FS (Fin.F1 : Fin.t (S n)) ≠ Fin.F1) by discriminate.
  destruct (Fin.eq_dec x Fin.F1) as [->|Hx0].
  - rewrite (fswap_l Fin.F1 (Fin.FS (Fin.FS q1))).
    rewrite (fswap_l Fin.F1 (Fin.FS (Fin.F1 : Fin.t (S n)))).
    rewrite (fswap_l (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1))).
    rewrite (fswap_other Fin.F1 (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1)) HQ0 HQ1).
    reflexivity.
  - destruct (Fin.eq_dec x (Fin.FS Fin.F1)) as [->|Hx1].
    + rewrite (fswap_other Fin.F1 (Fin.FS (Fin.FS q1)) (Fin.FS Fin.F1)
                 H10 (fun H => HQ1 (eq_sym H))).
      rewrite (fswap_r Fin.F1 (Fin.FS (Fin.F1 : Fin.t (S n)))).
      rewrite (fswap_other (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1)) Fin.F1
                 (fun H => H10 (eq_sym H)) (fun H => HQ0 (eq_sym H))).
      rewrite (fswap_l Fin.F1 (Fin.FS (Fin.F1 : Fin.t (S n)))).
      reflexivity.
    + destruct (Fin.eq_dec x (Fin.FS (Fin.FS q1))) as [->|HxQ].
      * rewrite (fswap_r Fin.F1 (Fin.FS (Fin.FS q1))).
        rewrite (fswap_other Fin.F1 (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1))
                   HQ0 HQ1).
        rewrite (fswap_r (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1))).
        rewrite (fswap_r Fin.F1 (Fin.FS (Fin.F1 : Fin.t (S n)))).
        reflexivity.
      * rewrite (fswap_other Fin.F1 (Fin.FS (Fin.FS q1)) x Hx0 HxQ).
        rewrite (fswap_other Fin.F1 (Fin.FS Fin.F1) x Hx0 Hx1).
        rewrite (fswap_other (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1)) x Hx1 HxQ).
        rewrite (fswap_other Fin.F1 (Fin.FS Fin.F1) x Hx0 Hx1).
        reflexivity.
Qed.

Lemma det_swap_F1 {m : nat} (A : Matrix R (S (S m)) (S (S m)))
  (q0 : Fin.t (S m))
  (IH : ∀ (B : Matrix R (S m) (S m)) (u v : Fin.t (S m)), u ≠ v →
          det (fun i j => B i (fswap u v j)) ≈ ⊖ (det B)) :
  det (fun i j => A i (fswap Fin.F1 (Fin.FS q0) j)) ≈ ⊖ (det A).
Proof.
  pattern q0; apply (Fin.caseS' q0); clear q0.
  - apply det_swap01.
  - intro q1.
    transitivity (det (fun i j => A i
      (fswap Fin.F1 (Fin.FS Fin.F1)
        (fswap (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1))
          (fswap Fin.F1 (Fin.FS Fin.F1) j))))).
    { apply det_respects; intros i j; now rewrite <- fswap_conj. }
    assert (E1 : det (fun i j => A i (fswap Fin.F1 (Fin.FS Fin.F1) j))
                   ≈ ⊖ (det A)) by apply det_swap01.
    assert (E2 : det (fun i j => A i
                   (fswap Fin.F1 (Fin.FS Fin.F1)
                     (fswap (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1)) j)))
                 ≈ ⊖ (det (fun i j => A i (fswap Fin.F1 (Fin.FS Fin.F1) j)))).
    { apply (det_swap_FS (fun i j => A i (fswap Fin.F1 (Fin.FS Fin.F1) j))
               Fin.F1 (Fin.FS q1) IH).
      discriminate. }
    assert (E3 : det (fun i j => A i
                   (fswap Fin.F1 (Fin.FS Fin.F1)
                     (fswap (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1))
                       (fswap Fin.F1 (Fin.FS Fin.F1) j))))
                 ≈ ⊖ (det (fun i j => A i
                        (fswap Fin.F1 (Fin.FS Fin.F1)
                          (fswap (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1)) j))))).
    { apply (det_swap01 (fun i j => A i
               (fswap Fin.F1 (Fin.FS Fin.F1)
                 (fswap (Fin.FS Fin.F1) (Fin.FS (Fin.FS q1)) j)))). }
    rewrite E3, E2, E1.
    apply ring_neg_involutive.
Qed.

Lemma det_swap {n : nat} (A : Matrix R n n) (p q : Fin.t n) :
  p ≠ q → det (fun i j => A i (fswap p q j)) ≈ ⊖ (det A).
Proof.
  revert A p q; induction n as [|n1 IH]; intros A p q Hpq.
  - inversion p.
  - destruct n1 as [|m].
    + rewrite (fin1_singleton p), (fin1_singleton q) in Hpq.
      exfalso; now apply Hpq.
    + destruct (Fin.eq_dec p Fin.F1) as [->|Hp].
      * destruct (Fin.eq_dec q Fin.F1) as [->|Hq];
          [ exfalso; now apply Hpq |].
        destruct (fin_not_F1 q Hq) as [q0 ->].
        apply (det_swap_F1 A q0 IH).
      * destruct (Fin.eq_dec q Fin.F1) as [->|Hq].
        -- destruct (fin_not_F1 p Hp) as [p0 ->].
           transitivity (det (fun i j => A i (fswap Fin.F1 (Fin.FS p0) j))).
           { apply det_respects; intros i j; now rewrite fswap_sym. }
           apply (det_swap_F1 A p0 IH).
        -- destruct (fin_not_F1 p Hp) as [p0 ->].
           destruct (fin_not_F1 q Hq) as [q0 ->].
           apply (det_swap_FS A p0 q0 IH).
           intro Heq; apply Hpq; now rewrite Heq.
Qed.

(** ** General alternation

    Two equal columns anywhere kill the determinant.  This does NOT
    follow from [det M ≈ ⊖ det M] — that is vacuous in characteristic 2
    — so the two columns are transported to positions 0 and 1 by at most
    two transpositions and [det_alt01] is applied there. *)

Lemma neg_eq_zero (x : K) : ⊖ x ≈ 0R → x ≈ 0R.
Proof using Type.
  intro H.
  transitivity (x ⊕ ⊖ x).
  - rewrite H; now rewrite rig_add_zero_r.
  - apply ring_neg_r'.
Qed.

Lemma fswap_id {n : nat} (p x : Fin.t n) : fswap p p x = x.
Proof using Type.
  unfold fswap; destruct (Fin.eq_dec x p) as [He|_]; [ now rewrite He |].
  destruct (Fin.eq_dec x p) as [He|_]; [ now rewrite He | reflexivity ].
Qed.

Lemma det_alt {n : nat} (M : Matrix R n n) (j k : Fin.t n) :
  j ≠ k → (∀ i, M i j ≈ M i k) → det M ≈ 0R.
Proof.
  revert M j k; destruct n as [|n1]; intros M j k Hjk Heq.
  - inversion j.
  - destruct n1 as [|m].
    + rewrite (fin1_singleton j), (fin1_singleton k) in Hjk.
      exfalso; now apply Hjk.
    + pose (M1 := fun i c => M i (fswap Fin.F1 j c)).
      pose (k1 := fswap Fin.F1 j k).
      assert (Hk1 : k1 ≠ Fin.F1).
      { intro He; apply Hjk.
        assert (Hx : fswap Fin.F1 j (fswap Fin.F1 j k)
                       = fswap Fin.F1 j Fin.F1)
          by (unfold k1 in He; now rewrite He).
        rewrite fswap_involutive, fswap_l in Hx.
        now rewrite Hx. }
      assert (HM1col : ∀ i, M1 i Fin.F1 ≈ M1 i k1).
      { intro i; unfold M1, k1.
        rewrite fswap_l, fswap_involutive.
        apply Heq. }
      assert (HM1 : det M1 ≈ 0R).
      { destruct (Fin.eq_dec k1 (Fin.FS Fin.F1)) as [He|Hne].
        - apply det_alt01; intro i; rewrite <- He; apply HM1col.
        - pose (M2 := fun i c => M1 i (fswap (Fin.FS Fin.F1) k1 c)).
          assert (H2 : det M2 ≈ ⊖ (det M1)).
          { apply det_swap; intro He2; apply Hne; now rewrite He2. }
          assert (Ha : (Fin.F1 : Fin.t (S (S m))) ≠ Fin.FS Fin.F1)
            by discriminate.
          assert (Hb : (Fin.F1 : Fin.t (S (S m))) ≠ k1)
            by (intro H; apply Hk1; now rewrite H).
          assert (H2z : det M2 ≈ 0R).
          { apply det_alt01; intro i; unfold M2.
            rewrite (fswap_other _ _ _ Ha Hb), fswap_l.
            apply HM1col. }
          apply neg_eq_zero; rewrite <- H2; exact H2z. }
      destruct (Fin.eq_dec j Fin.F1) as [He|Hne].
      * transitivity (det M1); [| exact HM1 ].
        apply det_respects; intros i c; unfold M1.
        rewrite He, fswap_id; reflexivity.
      * assert (Hs : det M1 ≈ ⊖ (det M)).
        { apply det_swap; intro He2; apply Hne; now rewrite <- He2. }
        apply neg_eq_zero; rewrite <- Hs; exact HM1.
Qed.

(** ** Reindexing the columns by an arbitrary map

    [permat f] is the 0/1 matrix of [f].  For EVERY [f] — injective or
    not — reindexing the columns of A by f multiplies the determinant by
    [det (permat f)].  The induction moves [f F1] to position 0 by a
    transposition; either some later index is then also sent to 0, in
    which case both sides vanish by [det_alt], or the residual map
    restricts to the smaller index set and the induction hypothesis
    applies inside every minor.  Injectivity is never assumed: the
    dichotomy is settled by a finite search. *)

Definition permat {n : nat} (f : Fin.t n → Fin.t n) : Matrix R n n :=
  fun i j => delta R i (f j).

Lemma fin_search {m : nat} (P : Fin.t m → Prop)
  (dec : ∀ i, {P i} + {P i → False}) :
  {i : Fin.t m & P i} + (∀ i, P i → False).
Proof using Type.
  induction m as [|m1 IHm].
  - right; intro i; inversion i.
  - destruct (dec Fin.F1) as [HP|HnP].
    + left; exists Fin.F1; exact HP.
    + destruct (IHm (fun i => P (Fin.FS i)) (fun i => dec (Fin.FS i)))
        as [[i Hi]|Hall].
      * left; exists (Fin.FS i); exact Hi.
      * right; intro i; pattern i; apply (Fin.caseS' i);
          [ exact HnP | exact Hall ].
Qed.

(* The predecessor of a non-zero index, with a default that the
   [fpred_FS] hypothesis rules out. *)
Definition fpred {k : nat} (d : Fin.t k) (x : Fin.t (S k)) : Fin.t k :=
  Fin.caseS' x (fun _ => Fin.t k) d (fun y => y).

Lemma fpred_FS {k : nat} (d : Fin.t k) (x : Fin.t (S k)) :
  (x = Fin.F1 → False) → Fin.FS (fpred d x) = x.
Proof using Type.
  pattern x; apply (Fin.caseS' x).
  - intro H; exfalso; now apply H.
  - intros y _; reflexivity.
Qed.

Lemma det_perm {n : nat} (A : Matrix R n n) (f : Fin.t n → Fin.t n) :
  det (fun i j => A i (f j)) ≈ det (permat f) ⊗ det A.
Proof.
  revert A f; induction n as [|k IH]; intros A f.
  - simpl; symmetry; apply rig_mul_one_l.
  - (* Moving [f F1] into position 0 costs exactly [det (permat s)]. *)
    assert (Hsw : ∀ B : Matrix R (S k) (S k),
      det (fun i j => B i (fswap Fin.F1 (f Fin.F1) j))
        ≈ det (permat (fswap Fin.F1 (f Fin.F1))) ⊗ det B).
    { intro B.
      destruct (Fin.eq_dec (f Fin.F1) Fin.F1) as [He|Hne].
      - assert (Hid : det (permat (fswap Fin.F1 (f Fin.F1))) ≈ 1R).
        { transitivity (det (fun i j : Fin.t (S k) => delta R i j)).
          - apply det_respects; intros i j; unfold permat.
            rewrite He, fswap_id; reflexivity.
          - apply det_id. }
        rewrite Hid, rig_mul_one_l.
        apply det_respects; intros i j.
        rewrite He, fswap_id; reflexivity.
      - assert (Hneg : det (permat (fswap Fin.F1 (f Fin.F1))) ≈ ⊖ 1R).
        { transitivity (⊖ (det (fun i j : Fin.t (S k) => delta R i j))).
          - apply (det_swap (fun i j : Fin.t (S k) => delta R i j)
                     Fin.F1 (f Fin.F1)).
            intro Hx; apply Hne; now rewrite <- Hx.
          - rewrite det_id; reflexivity. }
        rewrite Hneg, rig_mul_neg_one.
        apply (det_swap B Fin.F1 (f Fin.F1)).
        intro Hx; apply Hne; now rewrite <- Hx. }
    destruct (fin_search (fun c : Fin.t k =>
                fswap Fin.F1 (f Fin.F1) (f (Fin.FS c)) = Fin.F1)
                (fun c => Fin.eq_dec _ _)) as [[c Hc]|Hnone].
    + (* Two columns of A coincide, and so do two columns of [permat f]. *)
      assert (Hfc : f (Fin.FS c) = f Fin.F1).
      { rewrite <- (fswap_involutive Fin.F1 (f Fin.F1) (f (Fin.FS c))), Hc.
        apply fswap_l. }
      assert (HA : det (fun i j => A i (f j)) ≈ 0R).
      { apply (det_alt _ Fin.F1 (Fin.FS c)); [ discriminate |].
        intro i; rewrite Hfc; reflexivity. }
      assert (HP : det (permat f) ≈ 0R).
      { apply (det_alt _ Fin.F1 (Fin.FS c)); [ discriminate |].
        intro i; unfold permat; rewrite Hfc; reflexivity. }
      rewrite HA, HP; symmetry; apply rig_mul_zero_l.
    + (* The residual map restricts one size down. *)
      pose (h' := fun c : Fin.t k =>
                    fpred c (fswap Fin.F1 (f Fin.F1) (f (Fin.FS c)))).
      assert (Hh' : ∀ c, Fin.FS (h' c)
                           = fswap Fin.F1 (f Fin.F1) (f (Fin.FS c))).
      { intro c; unfold h'; apply fpred_FS; apply Hnone. }
      assert (HB : ∀ B : Matrix R (S k) (S k),
        det (fun i j => B i (fswap Fin.F1 (f Fin.F1) (f j)))
          ≈ det (permat h') ⊗ det B).
      { intro B.
        rewrite (det_S R (fun i j => B i (fswap Fin.F1 (f Fin.F1) (f j)))).
        rewrite (det_S R B), fin_sum_mul_l.
        apply fin_sum_respects; intro i.
        assert (Hminor :
          det (minor (fun i' j => B i' (fswap Fin.F1 (f Fin.F1) (f j)))
                 i Fin.F1)
            ≈ det (permat h') ⊗ det (minor B i Fin.F1)).
        { transitivity (det (fun r c => minor B i Fin.F1 r (h' c))).
          - apply det_respects; intros r c; unfold minor.
            rewrite !fin_delete_F1, Hh'; reflexivity.
          - apply IH. }
        rewrite Hminor, (fswap_r Fin.F1 (f Fin.F1)).
        apply mul_swap. }
      assert (HAf : det (fun i j => A i (f j))
                      ≈ det (permat h')
                          ⊗ det (fun i j => A i (fswap Fin.F1 (f Fin.F1) j))).
      { transitivity (det (fun i j =>
          (fun (i' : Fin.t (S k)) j' => A i' (fswap Fin.F1 (f Fin.F1) j'))
            i (fswap Fin.F1 (f Fin.F1) (f j)))).
        - apply det_respects; intros i j; simpl.
          now rewrite fswap_involutive.
        - apply (HB (fun (i' : Fin.t (S k)) j' =>
                       A i' (fswap Fin.F1 (f Fin.F1) j'))). }
      assert (HPf : det (permat f)
                      ≈ det (permat h')
                          ⊗ det (permat (fswap Fin.F1 (f Fin.F1)))).
      { transitivity (det (fun i j =>
          permat (fswap Fin.F1 (f Fin.F1)) i
            (fswap Fin.F1 (f Fin.F1) (f j)))).
        - apply det_respects; intros i j; unfold permat.
          now rewrite fswap_involutive.
        - apply (HB (permat (fswap Fin.F1 (f Fin.F1)))). }
      rewrite HAf, HPf, (Hsw A), rig_mul_assoc.
      reflexivity.
Qed.

(** ** Multiplicativity

    Column j of the product [A ∘ B] is the B-weighted combination of the
    columns of A, so the determinant expands over the columns of B.  The
    expansion is kept NESTED ([expand], one [fin_sum] per column) rather
    than flattened into a sum over all maps [Fin.t n → Fin.t n]: the
    products [Π_j B (f j) j] then never have to be formed, and the whole
    combinatorial layer — enumerating maps, isolating the injective
    ones, and reading off their signs — disappears.  [det (A ∘ B)] and
    [det B] are literally the same nested sum with different leaves, and
    [det_perm] relates those leaves by the CONSTANT factor [det A], so
    [expand_scale] pulls it out through every level at once. *)

Definition setcol {n : nat} (M : Matrix R n n) (j : Fin.t n)
  (v : Fin.t n → K) : Matrix R n n :=
  fun i c => match Fin.eq_dec c j with
             | left _ => v i
             | right _ => M i c
             end.

Lemma setcol_at {n : nat} (M : Matrix R n n) j v i :
  setcol M j v i j = v i.
Proof using Type.
  unfold setcol; destruct (Fin.eq_dec j j) as [_|H];
    [ reflexivity | now contradiction H ].
Qed.

Lemma setcol_off {n : nat} (M : Matrix R n n) j v i k :
  k ≠ j → setcol M j v i k = M i k.
Proof using Type.
  intro H; unfold setcol; destruct (Fin.eq_dec k j);
    [ contradiction | reflexivity ].
Qed.

(* A column that is a finite sum of scaled vectors splits the
   determinant into the corresponding finite sum. *)
Lemma det_col_sum {n : nat} (M : Matrix R n n) (j : Fin.t n) {m : nat}
  (c : Fin.t m → K) (V : Fin.t m → Fin.t n → K) :
  (∀ i, M i j ≈ fin_sum R (fun l => c l ⊗ V l i)) →
  det M ≈ fin_sum R (fun l => c l ⊗ det (setcol M j (V l))).
Proof.
  revert M c V; induction m as [|m1 IHm]; intros M c V Hcol; simpl.
  - apply (det_col_zero M j); intro i; apply Hcol.
  - assert (Hsplit : det M
      ≈ det (setcol M j (fun i => c Fin.F1 ⊗ V Fin.F1 i))
        ⊕ det (setcol M j
                 (fun i => fin_sum R
                             (fun l => c (Fin.FS l) ⊗ V (Fin.FS l) i)))).
    { apply (det_col_add _ _ _ j).
      - intros i k Hk; rewrite (setcol_off M j _ i k Hk); reflexivity.
      - intros i k Hk; rewrite (setcol_off M j _ i k Hk); reflexivity.
      - intro i; rewrite !setcol_at; apply Hcol. }
    rewrite Hsplit.
    apply rig_add_respects.
    + apply (det_col_mul _ (setcol M j (V Fin.F1)) j (c Fin.F1)).
      * intros i k Hk; rewrite !(setcol_off M j _ i k Hk); reflexivity.
      * intro i; rewrite !setcol_at; reflexivity.
    + rewrite (IHm (setcol M j
                      (fun i => fin_sum R
                                  (fun l => c (Fin.FS l) ⊗ V (Fin.FS l) i)))
                 (fun l => c (Fin.FS l)) (fun l => V (Fin.FS l))).
      * apply fin_sum_respects; intro l.
        apply rig_mul_respects; [ reflexivity |].
        apply det_respects; intros i k.
        destruct (Fin.eq_dec k j) as [->|Hk].
        -- rewrite !setcol_at; reflexivity.
        -- rewrite !(setcol_off _ j _ i k Hk); reflexivity.
      * intro i; rewrite setcol_at; reflexivity.
Qed.

(** *** The nested expansion *)

Definition upd_fn {n : nat} (f : Fin.t n → Fin.t n) (j l : Fin.t n) :
  Fin.t n → Fin.t n :=
  fun c => match Fin.eq_dec c j with
           | left _ => l
           | right _ => f c
           end.

Fixpoint expand {n : nat} (B : Matrix R n n) (js : list (Fin.t n))
  (Phi : (Fin.t n → Fin.t n) → K) (f : Fin.t n → Fin.t n) : K :=
  match js with
  | nil => Phi f
  | j :: js' =>
      fin_sum R (fun l => B l j ⊗ expand B js' Phi (upd_fn f j l))
  end.

(* DISCLOSURE: this is the tree's THIRD copy of the Fin enumeration —
   Instance/FinSet/Skeleton.v's [fin_enum] (with [fin_enum_full] and
   [fin_enum_nodup], and its own [nodup_map_FS]) has the identical
   body, and Instance/FinSet/Pushout.v carries [all_fin]/[In_all_fin].
   It is re-derived here to keep Instance/Matr free of a
   cross-hierarchy dependency on the FinSet development for ~15 lines
   of list code, following the naming-disclosure convention
   Skeleton.v itself sets; the map-FS NoDup helper is named
   [map_FS_NoDup] here to avoid colliding with Skeleton.v's. *)
Fixpoint all_fins (n : nat) : list (Fin.t n) :=
  match n with
  | O => nil
  | S k => Fin.F1 :: List.map Fin.FS (all_fins k)
  end.

Lemma all_fins_complete : ∀ (n : nat) (i : Fin.t n),
  List.In i (all_fins n).
Proof using Type.
  induction n as [|k IHk]; intro i; [ inversion i |].
  pattern i; apply (Fin.caseS' i).
  - left; reflexivity.
  - intro p; right; apply List.in_map; apply IHk.
Qed.

Lemma map_FS_NoDup {k : nat} (l : list (Fin.t k)) :
  List.NoDup l → List.NoDup (List.map Fin.FS l).
Proof using Type.
  induction 1 as [|x l Hx Hl IHl]; simpl; constructor.
  - intro Hin.
    apply List.in_map_iff in Hin; destruct Hin as [y [Heq Hy]].
    apply Hx; rewrite <- (Fin.FS_inj _ _ Heq); exact Hy.
  - exact IHl.
Qed.

Lemma all_fins_nodup : ∀ (n : nat), List.NoDup (all_fins n).
Proof using Type.
  induction n as [|k IHk]; simpl; constructor.
  - intro Hin.
    apply List.in_map_iff in Hin; destruct Hin as [y [Heq _]]; discriminate.
  - apply map_FS_NoDup; exact IHk.
Qed.

Lemma det_expand {n : nat} (A B : Matrix R n n) (js : list (Fin.t n)) :
  List.NoDup js →
  ∀ (M : Matrix R n n) (f : Fin.t n → Fin.t n),
  (∀ i j, List.In j js → M i j ≈ fin_sum R (fun l => A i l ⊗ B l j)) →
  (∀ i j, (List.In j js → False) → M i j ≈ A i (f j)) →
  det M ≈ expand B js (fun g => det (fun i j => A i (g j))) f.
Proof.
  induction js as [|j js' IHjs]; intros Hnd M f Hin Hout; simpl.
  - apply det_respects; intros i k.
    apply Hout; intro Hc; inversion Hc.
  - (* [NoDup] has two constructors, so it cannot be eliminated into the
       Type-valued [≈]; take it apart with the Prop-level projections. *)
    assert (Hnotin := proj1 (proj1 (List.NoDup_cons_iff j js') Hnd)).
    assert (Hnd' := proj2 (proj1 (List.NoDup_cons_iff j js') Hnd)).
    rewrite (det_col_sum M j (fun l => B l j) (fun l i => A i l)).
    2: { intro i.
         rewrite (Hin i j (or_introl eq_refl)).
         apply fin_sum_respects; intro l; apply Rcomm. }
    apply fin_sum_respects; intro l.
    apply rig_mul_respects; [ reflexivity |].
    apply (IHjs Hnd' (setcol M j (fun i => A i l)) (upd_fn f j l)).
    + intros i j' Hj'.
      rewrite (setcol_off M j _ i j').
      * apply Hin; right; exact Hj'.
      * intro Heq; apply Hnotin; rewrite <- Heq; exact Hj'.
    + intros i j' Hj'.
      destruct (Fin.eq_dec j' j) as [->|Hne].
      * rewrite setcol_at; unfold upd_fn.
        destruct (Fin.eq_dec j j) as [_|Hc];
          [ reflexivity | now contradiction Hc ].
      * rewrite (setcol_off M j _ i j' Hne).
        unfold upd_fn; destruct (Fin.eq_dec j' j); [ contradiction |].
        apply Hout; intros [He|He];
          [ apply Hne; now symmetry | now apply Hj' ].
Qed.

Lemma expand_scale {n : nat} (B : Matrix R n n) (js : list (Fin.t n))
  (Phi Psi : (Fin.t n → Fin.t n) → K) (x : K) :
  (∀ g, Phi g ≈ Psi g ⊗ x) →
  ∀ f, expand B js Phi f ≈ expand B js Psi f ⊗ x.
Proof.
  induction js as [|j js' IHjs]; intros H f; simpl.
  - apply H.
  - rewrite fin_sum_mul_r.
    apply fin_sum_respects; intro l.
    rewrite (IHjs H (upd_fn f j l)).
    symmetry; apply rig_mul_assoc.
Qed.

(* Mac Lane §I.4: the determinant is multiplicative. *)
Theorem det_mul {n : nat} (A B : Matrix R n n) :
  det (fun i j => fin_sum R (fun l => A i l ⊗ B l j)) ≈ det A ⊗ det B.
Proof.
  assert (HAB : det (fun i j => fin_sum R (fun l => A i l ⊗ B l j))
                  ≈ expand B (all_fins n)
                      (fun g => det (fun i j => A i (g j))) (fun x => x)).
  { apply (det_expand A B (all_fins n) (all_fins_nodup n)).
    - intros i j _; reflexivity.
    - intros i j Hj; exfalso; apply Hj; apply all_fins_complete. }
  assert (HB : det B
                 ≈ expand B (all_fins n)
                     (fun g => det (fun i j => delta R i (g j)))
                     (fun x => x)).
  { transitivity (det (fun i j => fin_sum R (fun l => delta R i l ⊗ B l j))).
    - apply det_respects; intros i j; symmetry.
      apply (fin_sum_delta_l R i (fun l => B l j)).
    - apply (det_expand (fun i j => delta R i j) B (all_fins n)
               (all_fins_nodup n)).
      + intros i j _; reflexivity.
      + intros i j Hj; exfalso; apply Hj; apply all_fins_complete. }
  assert (Hscale : expand B (all_fins n)
                     (fun g => det (fun i j => A i (g j))) (fun x => x)
                   ≈ expand B (all_fins n)
                       (fun g => det (fun i j => delta R i (g j)))
                       (fun x => x) ⊗ det A).
  { apply expand_scale; intro g; apply (det_perm A g). }
  rewrite HAB, Hscale, <- HB.
  apply Rcomm.
Qed.

(* The same theorem in the vocabulary of Instance/Matr.v: the
   determinant of a composite is the product of the determinants.  For
   square matrices [Matr]'s index flip is invisible — composition at
   [n ~> n] is the plain matrix product. *)
Corollary det_compose {n : nat} (A B : n ~{Matr (ring_rig R)}~> n) :
  det (A ∘ B) ≈ det A ⊗ det B.
Proof. apply det_mul. Qed.

(** ** Transposition

    Having both expansions makes [det Aᵀ ≈ det A] a three-line
    induction: the column-0 expansion of the transpose is the row-0
    expansion of the original, minor for minor. *)

Lemma pow_neg1_square (k : nat) : pow_neg1 k ⊗ pow_neg1 k ≈ 1R.
Proof using Type.
  induction k; simpl.
  - apply rig_mul_one_l.
  - rewrite ring_neg_mul_l, ring_neg_mul_r, ring_neg_involutive.
    exact IHk.
Qed.

Lemma delta_map_inj {p q : nat} (g : Fin.t p → Fin.t q)
  (Hinj : ∀ x y, g x = g y → x = y) (r c : Fin.t p) :
  delta R (g r) (g c) ≈ delta R r c.
Proof using Type.
  unfold delta.
  destruct (Fin.eq_dec (g r) (g c)) as [He|Hne],
           (Fin.eq_dec r c) as [He'|Hne'];
    try reflexivity.
  - contradiction Hne'; now apply Hinj.
  - contradiction Hne; now rewrite He'.
Qed.

Lemma det_transpose {n : nat} (A : Matrix R n n) :
  det (fun i j => A j i) ≈ det A.
Proof.
  revert A; induction n as [|k IH]; intro A; [ reflexivity |].
  rewrite (det_S R (fun i j => A j i)), (det_row_expand A).
  apply fin_sum_respects; intro j.
  apply rig_mul_respects; [ reflexivity |].
  transitivity (det (fun r c => minor A Fin.F1 j c r)).
  - apply det_respects; intros r c; unfold minor; reflexivity.
  - apply (IH (minor A Fin.F1 j)).
Qed.

(** ** Expansion along an arbitrary column

    [rotf j] moves column j to the front, keeping the others in order;
    it is exactly the map [F1 ↦ j], [FS c ↦ fin_delete j c], so the
    minors of the rotated matrix along column 0 ARE the minors of the
    original along column j, definitionally.  Its permutation matrix has
    determinant [(-1)^j] by a single application of the first-column
    expansion — no induction — and [det_perm] does the rest.

    Expanding along column j with the entries of a DIFFERENT column k
    gives zero (the "alien cofactor" identity): that is the expansion of
    the matrix whose column j has been overwritten by column k, which
    has two equal columns. *)

Definition rotf {m : nat} (j c : Fin.t (S m)) : Fin.t (S m) :=
  Fin.caseS' c (fun _ => Fin.t (S m)) j (fun c' => fin_delete j c').

Lemma det_permat_rot {m : nat} (j : Fin.t (S m)) :
  det (permat (rotf j)) ≈ pow_neg1 (fidx j).
Proof.
  rewrite (det_S R (permat (rotf j))).
  transitivity (fin_sum R (fun i : Fin.t (S m) =>
    delta R j i ⊗ (pow_neg1 (fidx i)
                     ⊗ det (minor (permat (rotf j)) i Fin.F1)))).
  { apply fin_sum_respects; intro i.
    transitivity (pow_neg1 (fidx i) ⊗ delta R j i
                    ⊗ det (minor (permat (rotf j)) i Fin.F1)).
    - apply rig_mul_respects; [| reflexivity ].
      apply rig_mul_respects; [ reflexivity |].
      apply (delta_sym R i j).
    - rewrite rig_mul_assoc; apply mul_swap. }
  rewrite (fin_sum_delta_l R j
    (fun i => pow_neg1 (fidx i)
                ⊗ det (minor (permat (rotf j)) i Fin.F1))).
  assert (HD : det (minor (permat (rotf j)) j Fin.F1) ≈ 1R).
  { transitivity (det (fun r c : Fin.t m => delta R r c)); [| apply det_id ].
    apply det_respects; intros r c; unfold minor, permat.
    rewrite fin_delete_F1.
    apply (delta_map_inj (fin_delete j) (fin_delete_inj j) r c). }
  rewrite HD; apply rig_mul_one_r.
Qed.

Lemma det_col_expand {m : nat} (A : Matrix R (S m) (S m)) (j : Fin.t (S m)) :
  pow_neg1 (fidx j) ⊗ det A
    ≈ fin_sum R (fun i => pow_neg1 (fidx i) ⊗ A i j ⊗ det (minor A i j)).
Proof.
  transitivity (det (fun i c => A i (rotf j c))).
  - rewrite (det_perm A (rotf j)), det_permat_rot; reflexivity.
  - rewrite (det_S R (fun i c => A i (rotf j c))).
    apply fin_sum_respects; intro i.
    apply rig_mul_respects; [ reflexivity |].
    apply det_respects; intros r c; unfold minor.
    rewrite fin_delete_F1; reflexivity.
Qed.

Lemma det_col_alien {m : nat} (A : Matrix R (S m) (S m))
  (j k : Fin.t (S m)) :
  j ≠ k →
  fin_sum R (fun i => pow_neg1 (fidx i) ⊗ A i k ⊗ det (minor A i j)) ≈ 0R.
Proof.
  intro Hjk.
  assert (Hdet : det (setcol A j (fun i => A i k)) ≈ 0R).
  { apply (det_alt _ j k Hjk); intro i.
    rewrite setcol_at, (setcol_off A j _ i k (fun H => Hjk (eq_sym H))).
    reflexivity. }
  transitivity (fin_sum R (fun i =>
    pow_neg1 (fidx i) ⊗ setcol A j (fun i' => A i' k) i j
      ⊗ det (minor (setcol A j (fun i' => A i' k)) i j))).
  - apply fin_sum_respects; intro i.
    apply rig_mul_respects.
    + apply rig_mul_respects; [ reflexivity |].
      rewrite setcol_at; reflexivity.
    + apply det_respects; intros r c; unfold minor.
      rewrite (setcol_off A j _ (fin_delete i r) (fin_delete j c)
                 (fin_delete_neq j c)).
      reflexivity.
  - rewrite <- (det_col_expand (setcol A j (fun i' => A i' k)) j), Hdet.
    apply rig_mul_zero_r.
Qed.

(** ** The adjugate, and invertibility

    [adj A] is the transposed cofactor matrix.  Both Laplace identities
    together say [adj A ∘ A ≈ A ∘ adj A ≈ det A · I]: the diagonal
    entries are the expansion of [det A] along a column (resp. a row),
    and the off-diagonal entries are the alien-cofactor zero.  The row
    identity is the column identity at the transpose, which is why
    [det_transpose] was worth having.

    Consequently a square matrix is invertible exactly when its
    determinant is a unit — stated elementwise (and in [Matr]'s
    composition vocabulary) rather than through an [Isomorphism], so
    that it composes with whatever invertibility interface the GL_n
    development prefers. *)

Definition adj {m : nat} (A : Matrix R (S m) (S m)) : Matrix R (S m) (S m) :=
  fun i j => pow_neg1 (fidx i) ⊗ pow_neg1 (fidx j) ⊗ det (minor A j i).

Lemma adj_term (pi pl d a : K) : pi ⊗ pl ⊗ d ⊗ a ≈ pi ⊗ (pl ⊗ a ⊗ d).
Proof. rewrite !rig_mul_assoc; now rewrite (Rcomm d a). Qed.

Lemma adj_term_r (a pl pj d : K) : a ⊗ (pl ⊗ pj ⊗ d) ≈ pj ⊗ pl ⊗ d ⊗ a.
Proof.
  rewrite !rig_mul_assoc.
  rewrite (mul_swap a pl (pj ⊗ d)).
  rewrite (mul_swap a pj d).
  rewrite (mul_swap pj pl (d ⊗ a)).
  now rewrite (Rcomm d a).
Qed.

Theorem adj_mul_l {m : nat} (A : Matrix R (S m) (S m)) (i j : Fin.t (S m)) :
  fin_sum R (fun l => adj A i l ⊗ A l j) ≈ det A ⊗ delta R i j.
Proof.
  transitivity (pow_neg1 (fidx i)
                  ⊗ fin_sum R (fun l => pow_neg1 (fidx l) ⊗ A l j
                                          ⊗ det (minor A l i))).
  { rewrite fin_sum_mul_l.
    apply fin_sum_respects; intro l.
    unfold adj; apply adj_term. }
  destruct (Fin.eq_dec i j) as [->|Hne].
  - rewrite <- (det_col_expand A j).
    rewrite (delta_refl R j), rig_mul_one_r.
    rewrite <- rig_mul_assoc, pow_neg1_square, rig_mul_one_l.
    reflexivity.
  - rewrite (det_col_alien A i j Hne), (delta_neq R i j Hne).
    rewrite !rig_mul_zero_r; reflexivity.
Qed.

Theorem adj_mul_r {m : nat} (A : Matrix R (S m) (S m)) (i j : Fin.t (S m)) :
  fin_sum R (fun l => A i l ⊗ adj A l j) ≈ det A ⊗ delta R i j.
Proof.
  transitivity (fin_sum R (fun l =>
    adj (fun x y : Fin.t (S m) => A y x) j l
      ⊗ (fun x y : Fin.t (S m) => A y x) l i)).
  - apply fin_sum_respects; intro l.
    assert (Hm : det (minor (fun x y : Fin.t (S m) => A y x) l j)
                   ≈ det (minor A j l)).
    { transitivity (det (fun r c => minor A j l c r)).
      - apply det_respects; intros r c; unfold minor; reflexivity.
      - apply det_transpose. }
    unfold adj; rewrite Hm.
    apply (adj_term_r (A i l) (pow_neg1 (fidx l)) (pow_neg1 (fidx j))
             (det (minor A j l))).
  - rewrite (adj_mul_l (fun x y : Fin.t (S m) => A y x) j i).
    rewrite det_transpose, (delta_sym R j i).
    reflexivity.
Qed.

Lemma det_unit_of_inverse {n : nat} (A B : Matrix R n n) :
  (∀ i j, fin_sum R (fun l => A i l ⊗ B l j) ≈ delta R i j) →
  det A ⊗ det B ≈ 1R.
Proof.
  intro H.
  rewrite <- det_mul.
  transitivity (det (fun i j : Fin.t n => delta R i j)); [| apply det_id ].
  apply det_respects; exact H.
Qed.

Lemma inverse_of_det_unit {m : nat} (A : Matrix R (S m) (S m)) (u : K) :
  det A ⊗ u ≈ 1R →
  ((∀ i j, fin_sum R (fun l => A i l ⊗ (u ⊗ adj A l j)) ≈ delta R i j) *
   (∀ i j, fin_sum R (fun l => (u ⊗ adj A i l) ⊗ A l j) ≈ delta R i j))%type.
Proof.
  intro Hu; split; intros i j.
  - transitivity (u ⊗ fin_sum R (fun l => A i l ⊗ adj A l j)).
    + rewrite fin_sum_mul_l.
      apply fin_sum_respects; intro l; apply mul_swap.
    + rewrite adj_mul_r, <- rig_mul_assoc, (Rcomm u (det A)), Hu.
      apply rig_mul_one_l.
  - transitivity (u ⊗ fin_sum R (fun l => adj A i l ⊗ A l j)).
    + rewrite fin_sum_mul_l.
      apply fin_sum_respects; intro l; apply rig_mul_assoc.
    + rewrite adj_mul_l, <- rig_mul_assoc, (Rcomm u (det A)), Hu.
      apply rig_mul_one_l.
Qed.

(* The same two statements in [Matr]'s vocabulary. *)
Corollary det_unit_of_iso {n : nat} (A B : n ~{Matr (ring_rig R)}~> n) :
  A ∘ B ≈ id → det A ⊗ det B ≈ 1R.
Proof. intro H; apply det_unit_of_inverse; exact H. Qed.

(* The inverse is supplied by the caller, so that the statement stays in
   [Matr]'s hom type instead of an anonymous function that [∘] cannot
   assign a category to. *)
Corollary iso_of_det_unit {m : nat}
  (A B : S m ~{Matr (ring_rig R)}~> S m) (u : K) :
  det A ⊗ u ≈ 1R →
  (∀ i j, B i j ≈ u ⊗ adj A i j) →
  ((A ∘ B ≈ id) * (B ∘ A ≈ id))%type.
Proof.
  intros Hu HB; split; intros i j.
  - transitivity (fin_sum R (fun l => A i l ⊗ (u ⊗ adj A l j))).
    + apply fin_sum_respects; intro l.
      apply rig_mul_respects; [ reflexivity | apply HB ].
    + exact (fst (inverse_of_det_unit A u Hu) i j).
  - transitivity (fin_sum R (fun l => (u ⊗ adj A i l) ⊗ A l j)).
    + apply fin_sum_respects; intro l.
      apply rig_mul_respects; [ apply HB | reflexivity ].
    + exact (snd (inverse_of_det_unit A u Hu) i j).
Qed.

(* The existential form: a unit determinant yields the two-sided
   inverse outright, packaged for consumers ([u · adj A] as the
   inverse matrix). *)
Corollary invertible_of_det_unit {m : nat}
  (A : S m ~{Matr (ring_rig R)}~> S m) (u : K) :
  det A ⊗ u ≈ 1R →
  { B : S m ~{Matr (ring_rig R)}~> S m
  & ((A ∘ B ≈ id) * (B ∘ A ≈ id))%type }.
Proof.
  intro Hu.
  exists (fun i j => u ⊗ adj A i j).
  apply (iso_of_det_unit A _ u Hu).
  intros i j; reflexivity.
Qed.

End DeterminantComm.

(** ** Naturality in the ring

    Mac Lane's §I.4 point: [det] is a map of functors, natural in the
    commutative ring.  Only the [RigHom] structure is used — preservation
    of negation is Theory/Algebra/Rig.v's theorem [RigHom_neg], not an
    extra hypothesis — so this is the entrywise-image statement at the
    level of matrices; the naturality square of §I.4 is its packaging. *)

Section DetMap.

Context (R R' : RingObject).
Context (h : RigHom (ring_rig R) (ring_rig R')).

Lemma rig_map_fin_sum {n : nat}
  (f : Fin.t n → carrier (rig_setoid (ring_rig R))) :
  rig_map h (fin_sum R f) ≈ fin_sum R' (fun i => rig_map h (f i)).
Proof.
  induction n; simpl.
  - apply rig_map_zero.
  - rewrite rig_map_add; now rewrite IHn.
Qed.

Lemma rig_map_pow_neg1 (k : nat) :
  rig_map h (pow_neg1 R k) ≈ pow_neg1 R' k.
Proof.
  induction k; simpl.
  - apply rig_map_one.
  - rewrite (RigHom_neg R R' h (pow_neg1 R k)); now rewrite IHk.
Qed.

Lemma det_map {n : nat} (A : Matrix R n n) :
  rig_map h (det R A) ≈ det R' (fun i j => rig_map h (A i j)).
Proof.
  revert A; induction n; intro A.
  - apply rig_map_one.
  - rewrite !det_S.
    rewrite rig_map_fin_sum.
    apply fin_sum_respects; intro i.
    rewrite !rig_map_mul.
    rewrite rig_map_pow_neg1.
    apply rig_mul_respects; [ reflexivity |].
    apply (IHn (minor R A i Fin.F1)).
Qed.

End DetMap.

(** ** Orientation, pinned by computation

    Over the integers everything in sight reduces, so the shape of the
    expansion is checked by [eq_refl] rather than asserted. *)

Definition m11 (a : Z) : Matrix Int_Ring 1 1 := fun _ _ => a.

Definition m22 (a b c d : Z) : Matrix Int_Ring 2 2 :=
  fun i j =>
    match fidx i, fidx j with
    | O, O => a
    | O, _ => b
    | _, O => c
    | _, _ => d
    end.

Example det_11 : det Int_Ring (m11 5) = 5%Z := eq_refl.

(* ad - bc, with the sign on the (1,0) entry: the first-column
   expansion of [[a,b],[c,d]] is a·d - c·b. *)
Example det_22 : det Int_Ring (m22 1 2 3 4) = (-2)%Z := eq_refl.
Example det_22_id : det Int_Ring (m22 1 0 0 1) = 1%Z := eq_refl.
Example det_22_swap : det Int_Ring (m22 0 1 1 0) = (-1)%Z := eq_refl.

(* Matr's composition really is the matrix product in this orientation:
   the product of [[1,2],[3,4]] and [[0,1],[1,0]] is [[2,1],[4,3]]. *)
Example matr_compose_22 :
  (@compose (Matr Int_Ring) 2%nat 2%nat 2%nat (m22 1 2 3 4) (m22 0 1 1 0))
    Fin.F1 Fin.F1 = 2%Z := eq_refl.

Example det_mul_22 :
  det Int_Ring
    (@compose (Matr Int_Ring) 2%nat 2%nat 2%nat (m22 1 2 3 4) (m22 0 1 1 0))
  = (det Int_Ring (m22 1 2 3 4) * det Int_Ring (m22 0 1 1 0))%Z := eq_refl.

Definition m33 (a b c d e f g h k : Z) : Matrix Int_Ring 3 3 :=
  fun i j =>
    match fidx i, fidx j with
    | O, O => a       | O, S O => b       | O, _ => c
    | S O, O => d     | S O, S O => e     | S O, _ => f
    | _, O => g       | _, S O => h       | _, _ => k
    end.

(* 1·(5·10−6·8) − 4·(2·10−3·8) + 7·(2·6−3·5) = 2 + 16 − 21. *)
Example det_33 : det Int_Ring (m33 1 2 3 4 5 6 7 8 10) = (-3)%Z := eq_refl.

Example det_33_alt : det Int_Ring (m33 1 2 1 4 5 4 7 8 7) = 0%Z := eq_refl.

Example det_mul_33 :
  det Int_Ring
    (@compose (Matr Int_Ring) 3%nat 3%nat 3%nat
       (m33 1 2 3 4 5 6 7 8 10) (m33 2 0 1 1 3 0 0 1 4))
  = (det Int_Ring (m33 1 2 3 4 5 6 7 8 10)
     * det Int_Ring (m33 2 0 1 1 3 0 0 1 4))%Z := eq_refl.

(** ** Mac Lane's own case: the integers

    [Int_Ring] is commutative, so the whole development instantiates;
    these are the §I.4 statements over ℤ, with no hypothesis left
    open. *)

Definition Int_comm : ∀ a b, rig_mul Int_Ring a b ≈ rig_mul Int_Ring b a :=
  fun a b => Z.mul_comm a b.

Definition det_Z_mul {n : nat} (A B : Matrix Int_Ring n n) :
  det Int_Ring
    (fun i j => fin_sum Int_Ring (fun l => rig_mul Int_Ring (A i l) (B l j)))
    ≈ rig_mul Int_Ring (det Int_Ring A) (det Int_Ring B)
  := det_mul Int_Ring Int_comm A B.

Definition det_Z_compose {n : nat} (A B : n ~{Matr Int_Rig}~> n) :
  det Int_Ring (A ∘ B) ≈ rig_mul Int_Ring (det Int_Ring A) (det Int_Ring B)
  := det_compose Int_Ring Int_comm A B.

Definition det_Z_id {n : nat} :
  det Int_Ring (fun i j : Fin.t n => delta Int_Ring i j) ≈ rig_one Int_Ring
  := det_id Int_Ring.

(* The adjugate of [[1,2],[3,4]] is [[4,-2],[-3,1]], and its product
   with the matrix is det = -2 down the diagonal. *)
Example adj_22_00 : adj Int_Ring (m22 1 2 3 4) Fin.F1 Fin.F1 = 4%Z := eq_refl.
Example adj_22_01 :
  adj Int_Ring (m22 1 2 3 4) Fin.F1 (Fin.FS Fin.F1) = (-2)%Z := eq_refl.
Example adj_22_10 :
  adj Int_Ring (m22 1 2 3 4) (Fin.FS Fin.F1) Fin.F1 = (-3)%Z := eq_refl.
Example adj_22_11 :
  adj Int_Ring (m22 1 2 3 4) (Fin.FS Fin.F1) (Fin.FS Fin.F1) = 1%Z := eq_refl.

Example adj_mul_22_diag :
  fin_sum Int_Ring
    (fun l => rig_mul Int_Ring
                (adj Int_Ring (m22 1 2 3 4) Fin.F1 l)
                (m22 1 2 3 4 l Fin.F1))
  = (-2)%Z := eq_refl.

Example adj_mul_22_off :
  fin_sum Int_Ring
    (fun l => rig_mul Int_Ring
                (adj Int_Ring (m22 1 2 3 4) Fin.F1 l)
                (m22 1 2 3 4 l (Fin.FS Fin.F1)))
  = 0%Z := eq_refl.

Definition adj_Z_mul_l {m : nat} (A : Matrix Int_Ring (S m) (S m))
  (i j : Fin.t (S m)) :
  fin_sum Int_Ring
    (fun l => rig_mul Int_Ring (adj Int_Ring A i l) (A l j))
    ≈ rig_mul Int_Ring (det Int_Ring A) (delta Int_Ring i j)
  := adj_mul_l Int_Ring Int_comm A i j.
