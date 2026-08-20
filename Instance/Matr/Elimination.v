(* [Coq.QArith.QArith] MUST precede [Category.Lib]: it exports an [equiv]
   that otherwise shadows Lib/Setoid.v's, and every [Proper] statement
   below then fails to elaborate.  This is the import-order gotcha
   Instance/FdVect.v records in its own header; measured here too. *)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.Matr.Determinant.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * Gaussian elimination: a basis of the left null space

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.3
    Exercise 3 [maclane:III.3:ex3] asks for the coequalizer of a parallel
    pair of matrices.  This file is the LINEAR-ALGEBRA half of that
    exercise and deliberately stops there.  It produces, for an arbitrary
    matrix M over a field equipped with a zero test, a basis of the LEFT
    NULL SPACE of M, packaged with exactly the universal clause such a
    colimit consumes.  Read the scope precisely: the record
    [LeftNullBasis] speaks of [mat_mul] and [mat_zero] and of nothing
    else, and NO colimit, cocone, quotient or structure class of the
    library is mentioned anywhere in this file — but [Matr K] itself IS
    used, and it is used for five things and no more: associativity, the
    two unit laws, the congruence [compose_respects], and the hom-setoid,
    which is taken as the [Setoid] instance on matrices.  All five are
    cited rather than reproved, because [mat_mul] is measured below to BE
    that category's [compose].

    WHAT IS PRODUCED.  For [M : Matrix K m n] the construction returns a
    natural number k, a matrix [E : Matrix K k m] with [E · M ≈ 0], and
    the universal clause: for every z and every [h : Matrix K z m] with
    [h · M ≈ 0] there is a UNIQUE [u : Matrix K z k] with [u · E ≈ h].
    The two halves say, in matrix terms, that the rows of E SPAN the left
    null space of M (existence of u) and are LINEARLY INDEPENDENT
    (uniqueness of u); k is the dimension of that space, so k = m - rank M
    — though no rank function is defined here and the equation is not
    stated, let alone proved.

    ORIENTATION.  Instance/Matr.v follows Mac Lane: an arrow [n ~> m] of
    [Matr R] is an m × n matrix, [Matrix R rows cols] being
    [Fin.t rows → Fin.t cols → carrier R] and [hom n m] being
    [Matrix R m n].  That convention is inherited verbatim, and it is
    MEASURED rather than assumed: [matrix_is_hom],
    [mat_mul_is_compose] and [mat_id_is_id] record by [eq_refl] that
    [Matrix K a b] IS the hom-type [b ~{Matr K}~> a], that the [mat_mul]
    of this file IS [Matr K]'s [compose] with its three object arguments
    in the order (c, b, a), and that [mat_id] IS [Matr K]'s identity.
    Consequently associativity and the two unit laws are cited from the
    category rather than proved again.

    THE DECIDABILITY HYPOTHESIS, AND WHY IT IS FORCED.  Elimination has
    to DECIDE whether a pivot vanishes, and the class it runs over
    supplies no such decision.  [FieldObject] (Instance/FdVect.v) carries
    exactly [field_ring], [field_comm], [field_one_neq_zero], a TOTAL
    [finv], [finv_respects], and [finv_l] — and [finv_l] is GUARDED by
    [x ≉ 0], so the inverse law is unusable until non-vanishing has been
    established.  Over an abstract setoid carrier [≈] is not decidable,
    and the value of [finv] at zero is junk constrained only by
    [finv_respects].  The hypothesis is therefore carried as EXPLICIT
    DATA, in the exact shape Instance/Field.v already prices it: that
    file's [field_dec_stable] takes
    [dec : ∀ a b, (a ≈ b) + (a ≈ b → False)] and discharges it at
    [Q_Field_dec] and [F2_Field_dec].  The section variable [Kdec] below
    has that type verbatim, and [F2_dec_inhabits]/[Q_dec_inhabits]
    record BY ASCRIPTION that those two constants inhabit it, so the
    hypothesis is the tree's own notion and not a new one.  This is not
    a formalization shortcut standing in for a theorem: no decider is
    derivable from [FieldObject], and the tree already treats the
    decider as data at exactly this point.  That non-derivability is
    ARGUED HERE, NOT PROVED -- this tree's convention for exactly this
    shape is to prove it ([Instance/Field.v]'s own
    [stability_is_the_conclusion] and siblings), and no such theorem
    is offered below, so the word "forced" should be read as "no route
    around it was found", not as a proved impossibility.

    One caveat, measured rather
    than anticipated: both in-tree deciders are [Qed] LEMMAS, so neither
    reduces, and the computing witnesses at the end of this file run on
    transparent copies ([f2_dec], [q_dec]) that decide the same
    relations by the same case analyses — see the disclosure there.

    THE COERCION PATH, as measured in the code rather than guessed:
    [FieldObject] has [field_ring :> RingObject] (Instance/FdVect.v) and
    [RingObject] has [ring_rig :> RigObject] (Theory/Algebra/Rig.v), so a
    [K : FieldObject] reaches [Matr]'s parameter as
    [ring_rig (field_ring K)] and [Matrix K a b] elaborates to
    [Matrix (ring_rig (field_ring K)) a b].  SUBTRACTION comes from the
    RING layer's [ring_neg]: a bare rig has no negation, which is why
    this file is stated over a field (a ring would suffice for [mat_sub]
    alone, but not for the pivot division).

    THE ROUTE.  Recursion on the number of COLUMNS.  With no columns
    every row vector is in the left null space, so the identity matrix is
    a basis ([lnb_id], which also covers a column that vanishes
    identically).  With at least one column, split M into its first
    column and the rest: a row vector kills M exactly when it kills the
    first column AND kills the rest.  So take a basis E1 of the left null
    space of the first column, push the remaining columns through it, and
    recurse on [E1 · tail M], which has one column fewer; if E2 is a
    basis for that, then [E2 · E1] is a basis for M ([lnb_step]).  The
    whole construction therefore rests on the SINGLE-COLUMN case, which
    is the pivot step proper ([pivot_basis]): with a pivot entry
    [c p ≉ 0], the vectors [e_{d r} − (c_{d r} / c_p) · e_p], indexed by
    [r : Fin.t m'] through Determinant.v's order-preserving injection
    [fin_delete p] that misses p, are a basis.  The mediator is then
    literally RESTRICTION along [fin_delete p] — [u a r := h a (d r)] —
    and the pivot column of the equation [u · E ≈ h] is where the null
    space hypothesis on h is spent.

    REUSE.  The finite-sum library of Instance/Matr.v ([fin_sum] with its
    congruence, [fin_sum_zero], [fin_sum_add], bilinearity
    [fin_sum_mul_l]/[fin_sum_mul_r] and the Kronecker collapses
    [fin_sum_delta_l]/[fin_sum_delta_r]) and the kit of
    Instance/Matr/Determinant.v ([fin_delete] with [fin_delete_neq],
    [fin_delete_inj] and the three computation rules; the ring
    arithmetic [ring_neg_mul_l], [ring_neg_mul_r], [ring_neg_zero] and
    [ring_neg_unique]; and [fin_sum_neg]) are consumed, not
    re-derived.  What this file adds to that kit is [fin_delete_surj]
    (the complement of a deleted index is exactly the image of
    [fin_delete]) and [fin_sum_delete] (a finite sum splits as the term
    at p plus the sum over the complement of p) — the second is the one
    genuinely new summation lemma, and it is what makes the pivot column
    computable.  Instance/FdVect/Tensor.v has an unrelated lemma named
    [fin_sum_split] about splitting [Fin.t (a + b)]; that file is not
    required here and the names do not collide.

    MEASURED STRENGTHS, strict first.  Closing by [eq_refl]:
    [matrix_is_hom], [mat_mul_is_compose], [mat_id_is_id],
    [mat_equiv_is_homset_equiv] (the local [Setoid] instance on matrices
    IS [Matr K]'s hom-setoid, not a parallel pointwise one), and — the
    two that make [lnb_step] cheap — [mat_mul_col0_strict] and
    [mat_mul_tail_strict], where taking the first column of a product and
    multiplying into the first column give the SAME TERM, so no lemma is
    needed at all.  Over F₂ the dimension, every basis entry, the
    annihilation and the MEDIATOR of the worked example all close by
    [eq_refl]; over ℚ the dimension, the basis entries −2 and 1 and the
    annihilation close by [eq_refl] too, the rational arithmetic
    reducing on closed input.

    FOUR STRICT ATTEMPTS WERE MADE AND REFUTED.  They are recorded here
    rather than as [Fail] probes, this file carrying no probe section:
    (i) [mat_mul (mat_id a) A = A] — the unit law is a genuine
    finite-sum computation, not a conversion, and only [mat_mul_id_l]'s
    [≈] holds; (ii) the same for [mat_sub A A = mat_zero]; (iii) the F₂
    dimension check with the tree's [F2_Field_dec] in place of [f2_dec],
    which is what located the opacity described above; and (iv)
    [lnb_basis f2_col_lnb = lnb_basis f2_ones_lnb], which is refuted at
    whole-matrix Leibniz equality although both entries of both agree —
    the two are produced by different numbers of recursion steps, so
    they are different closed terms with the same values, and the file's
    four [f2_*_basis_*] Examples pin the values.  Each negative was
    stripped of its [Fail] and confirmed to be a genuine conversion
    failure, against a positive control at the same arguments.

    TWO ENGINEERING FINDINGS.  [Coq.QArith.QArith] must be Required
    BEFORE [Category.Lib] — see the comment above the import block; and,
    following the Determinant.v precedent, this file's section sets
    [Default Proof Using "All"], because [Kdec] occurs in proofs
    ([find_nonzero]) without occurring in the corresponding statements,
    so every [Qed] lemma below takes K and [Kdec] as its two leading
    arguments even where [Kdec] is not used.

    NOT DELIVERED BY THIS FILE.  No rank function, and so no proof that
    [lnb_dim] is [m - rank M]; no claim that [lnb_dim] is independent of
    the construction (uniqueness of the dimension is not stated, though
    it follows from the universal clause and would be a natural next
    lemma); no echelon form, no normal form and no pivot list, so nothing
    here decides matrix equivalence; no right null space and no
    transpose-based dual (the transpose functor of Instance/Matr.v would
    give it, and is not used); no statement about [Matr K] as a category
    beyond the three [eq_refl] identifications above; and no bridge to
    any colimit, cocone or quotient vocabulary — that is the next file's
    business, not this one's. *)

(** ** Index arithmetic

    Two facts about Determinant.v's [fin_delete] that its own file does
    not need.  Both are about [Fin.t] alone and mention no algebra, so
    they sit outside the section below. *)

(* [Fin.t 1] is a singleton. *)
Lemma fin1_F1 (j : Fin.t 1) : j = Fin.F1.
Proof.
  pattern j; apply (Fin.caseS' j); clear j.
  - reflexivity.
  - intro y; inversion y.
Qed.

(* [fin_delete p] is onto the complement of p: Determinant.v proves the
   image misses p and that the map is injective, but never that the two
   together exhaust the index set.  The witness is DATA (a [sigT]), which
   is what the pivot case analysis below consumes. *)
Lemma fin_delete_surj {n : nat} (p j : Fin.t (S n)) :
  j ≠ p → { r : Fin.t n & fin_delete p r = j }.
Proof.
  revert p j; induction n as [|n1 IH]; intros p j.
  - intro Hne; exfalso; apply Hne.
    now rewrite (fin1_F1 j), (fin1_F1 p).
  - pattern p; apply (Fin.caseS' p); clear p.
    + pattern j; apply (Fin.caseS' j); clear j.
      * intro H; exfalso; now apply H.
      * intros y _; exists y; apply fin_delete_F1.
    + intro s.
      pattern j; apply (Fin.caseS' j); clear j.
      * intros _; exists Fin.F1; apply fin_delete_FS_F1.
      * intros y Hy.
        assert (Hys : y ≠ s) by (intro He; apply Hy; now rewrite He).
        destruct (IH s y Hys) as [r Hr].
        exists (Fin.FS r).
        now rewrite fin_delete_FS_FS, Hr.
Qed.

(* An index is either the pivot or lies in the image of [fin_delete]. *)
Lemma fin_pivot_cases {n : nat} (p j : Fin.t (S n)) :
  (j = p) + { r : Fin.t n & fin_delete p r = j }.
Proof.
  destruct (Fin.eq_dec j p) as [He|Hne].
  - left; exact He.
  - right; exact (fin_delete_surj p j Hne).
Qed.

Section Elimination.

(** ** The base: a field with a zero test

    [Kdec] has the type Instance/Field.v's [field_dec_stable] takes; see
    the header for why no weaker hypothesis will do. *)

Context (K : FieldObject).
Context (Kdec : ∀ a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b → False)).

Set Default Proof Using "All".

Local Notation Kc := (carrier (rig_setoid K)).

Local Infix "⊕" := (rig_add K) (at level 50, left associativity).
Local Infix "⊗" := (rig_mul K) (at level 40, left associativity).
Local Notation "⊖ x" := (ring_neg K x) (at level 35, right associativity).
Local Notation "0K" := (rig_zero K).
Local Notation "1K" := (rig_one K).

(** ** Matrix vocabulary

    Named here so that every statement below is in matrix terms; the
    three [eq_refl] identifications immediately after show that these
    names are [Matr K]'s own operations and not a parallel development. *)

Definition mat_id (a : nat) : Matrix K a a := fun i j => delta K i j.

Definition mat_zero {a b : nat} : Matrix K a b := fun _ _ => 0K.

Definition mat_mul {a b c : nat} (A : Matrix K a b) (B : Matrix K b c) :
  Matrix K a c :=
  fun i j => fin_sum K (fun l : Fin.t b => A i l ⊗ B l j).

Definition mat_sub {a b : nat} (A B : Matrix K a b) : Matrix K a b :=
  fun i j => A i j ⊕ ⊖ (B i j).

(* Matrices are compared by [Matr K]'s own hom-setoid.  Declaring the
   instance rather than letting [fun_setoid] fire keeps the [≈] of this
   file and the [≈] of the category the SAME term.

   READ THAT PRECISELY, BECAUSE AN EARLIER DRAFT OVERSTATED IT AND AN
   AUDIT REFUTED THE OVERSTATEMENT BY EXPERIMENT.  The draft said this
   instance is NEEDED and that [matrix_is_hom]/[mat_equiv_is_homset_equiv]
   MEASURE the difference.  Neither is so.  The two setoids are
   CONVERTIBLE, so those Examples close by [eq_refl] with or without the
   instance, and deleting this declaration outright leaves the whole file
   compiling clean (rc=0, verified).  What the instance buys is that the
   two [≈]s are the same TERM rather than merely convertible ones, which
   keeps goals readable; it is a convenience, not a necessity, and
   nothing below is load-bearing on it. *)
#[local] Instance Matrix_Setoid {a b : nat} : Setoid (Matrix K a b) :=
  @homset (Matr K) b a.

Example matrix_is_hom (a b : nat) : Matrix K a b = (b ~{Matr K}~> a) :=
  eq_refl.

Example mat_mul_is_compose {a b c : nat}
  (A : Matrix K a b) (B : Matrix K b c) :
  mat_mul A B = @compose (Matr K) c b a A B := eq_refl.

Example mat_id_is_id (a : nat) : mat_id a = @id (Matr K) a := eq_refl.

Example mat_equiv_is_homset_equiv {a b : nat} (A B : Matrix K a b) :
  (A ≈ B) = (A ≈[Matr K] B) := eq_refl.

(** ** Matrix algebra

    Associativity and the unit laws are the category's, cited by the
    identifications above.  Everything else is a finite-sum computation. *)

#[local] Instance mat_mul_respects {a b c : nat} :
  Proper (equiv ==> equiv ==> equiv) (@mat_mul a b c) :=
  @compose_respects (Matr K) c b a.

Lemma mat_mul_assoc {a b c d : nat} (A : Matrix K a b) (B : Matrix K b c)
  (C : Matrix K c d) :
  mat_mul (mat_mul A B) C ≈ mat_mul A (mat_mul B C).
Proof. exact (@comp_assoc_sym (Matr K) d c b a A B C). Qed.

Lemma mat_mul_id_l {a b : nat} (A : Matrix K a b) :
  mat_mul (mat_id a) A ≈ A.
Proof. exact (@id_left (Matr K) b a A). Qed.

Lemma mat_mul_id_r {a b : nat} (A : Matrix K a b) :
  mat_mul A (mat_id b) ≈ A.
Proof. exact (@id_right (Matr K) b a A). Qed.

Lemma mat_mul_zero_r {a b c : nat} (A : Matrix K a b) :
  mat_mul A (@mat_zero b c) ≈ mat_zero.
Proof.
  intros i j.
  transitivity (fin_sum K (fun _ : Fin.t b => 0K)).
  - apply fin_sum_respects; intro l; apply rig_mul_zero_r.
  - apply fin_sum_zero.
Qed.

Lemma mat_mul_zero_l {a b c : nat} (B : Matrix K b c) :
  mat_mul (@mat_zero a b) B ≈ mat_zero.
Proof.
  intros i j.
  transitivity (fin_sum K (fun _ : Fin.t b => 0K)).
  - apply fin_sum_respects; intro l; apply rig_mul_zero_l.
  - apply fin_sum_zero.
Qed.

(** ** Finite sums: what the pivot needs beyond Instance/Matr.v

    [fin_sum_cons] is the unfolding step named as a rewrite rule (plain
    [simpl] would unfold the summand as well and leave the goal in a
    shape the [fin_sum] kit no longer matches — Determinant.v's
    [fin_sum_S] is the same device, restated here over a field so that no
    coercion has to be matched, and given a different name so that
    nothing of Determinant.v's is shadowed).  Additivity of negation
    over a finite sum is NOT restated: Determinant.v's [fin_sum_neg] is
    already stated for an arbitrary [RingObject] with an explicit
    [Proof using Type], so it costs no commutativity and is consumed as
    it stands.  [fin_sum_delete] is the genuinely new one: a sum over
    [Fin.t (S n)] splits as the term at p plus the sum over the
    complement of p, indexed through [fin_delete p]. *)

Lemma fin_sum_cons {n : nat} (f : Fin.t (S n) → Kc) :
  fin_sum K f = f Fin.F1 ⊕ fin_sum K (fun i => f (Fin.FS i)).
Proof. reflexivity. Qed.

Lemma fin_sum_delete {n : nat} (f : Fin.t (S n) → Kc) (p : Fin.t (S n)) :
  fin_sum K f ≈ f p ⊕ fin_sum K (fun r => f (fin_delete p r)).
Proof.
  revert f p; induction n as [|n1 IH]; intros f p.
  - rewrite (fin1_F1 p); reflexivity.
  - pattern p; apply (Fin.caseS' p); clear p.
    + rewrite fin_sum_cons.
      apply rig_add_respects; [ reflexivity |].
      apply fin_sum_respects; intro r.
      now rewrite fin_delete_F1.
    + intro s.
      transitivity (f Fin.F1 ⊕ (f (Fin.FS s)
        ⊕ fin_sum K (fun r => f (Fin.FS (fin_delete s r))))).
      { rewrite fin_sum_cons.
        apply rig_add_respects; [ reflexivity |].
        exact (IH (fun i => f (Fin.FS i)) s). }
      transitivity (f (Fin.FS s) ⊕ (f Fin.F1
        ⊕ fin_sum K (fun r => f (Fin.FS (fin_delete s r))))).
      { rewrite <- !rig_add_assoc.
        apply rig_add_respects; [ apply rig_add_comm | reflexivity ]. }
      apply rig_add_respects; [ reflexivity |].
      rewrite fin_sum_cons.
      apply rig_add_respects.
      * now rewrite fin_delete_FS_F1.
      * apply fin_sum_respects; intro y.
        now rewrite fin_delete_FS_FS.
Qed.

(* Deleting the same index from both arguments leaves the Kronecker
   delta unchanged: injectivity of [fin_delete p] in one direction, and
   nothing at all in the other. *)
Lemma delta_delete {n : nat} (p : Fin.t (S n)) (r s : Fin.t n) :
  delta K (fin_delete p r) (fin_delete p s) ≈ delta K r s.
Proof.
  destruct (Fin.eq_dec r s) as [He|Hne].
  - rewrite He, !delta_refl; reflexivity.
  - rewrite (delta_neq K r s Hne).
    apply delta_neq.
    intro Heq; apply Hne; exact (fin_delete_inj p r s Heq).
Qed.

(** ** Searching for a pivot

    This is the ONLY place [Kdec] is consumed, and it is the whole reason
    the hypothesis is carried: elimination has to know whether a column
    vanishes identically before it can divide by anything.  The result is
    a [sum], so the pivot index is data and the search computes. *)

Definition find_nonzero : ∀ (n : nat) (c : Fin.t n → Kc),
  { i : Fin.t n & (c i ≈ 0K → False) } + (∀ i, c i ≈ 0K).
Proof.
  induction n as [|n1 IH]; intro c.
  - right; intro i; inversion i.
  - destruct (Kdec (c Fin.F1) 0K) as [Hz | Hnz].
    + destruct (IH (fun i => c (Fin.FS i))) as [[i Hi] | Hall].
      * left; exists (Fin.FS i); exact Hi.
      * right; intro i.
        pattern i; apply (Fin.caseS' i); [ exact Hz | exact Hall ].
    + left; exists Fin.F1; exact Hnz.
Defined.

(** ** The pivot basis

    With a pivot entry [c p ≉ 0], the left null space of the column c is
    spanned by the m − 1 vectors [e_{d r} − (c_{d r} / c_p) · e_p], where
    [d := fin_delete p] runs over the complement of p.  Each is visibly
    killed by c, and together they are independent because the [d r]
    coordinate of the r-th one is 1 and of the others is 0. *)

Definition pivot_coeff {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (r : Fin.t m') : Kc :=
  c (fin_delete p r) ⊗ finv K (c p).

Definition pivot_basis {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) : Matrix K m' (S m') :=
  fun r j => delta K (fin_delete p r) j
             ⊕ ⊖ (pivot_coeff c p r ⊗ delta K p j).

(* Multiplying row r of the pivot basis into an arbitrary column g: the
   delta collapses pick out the [d r] and p entries of g. *)
Lemma fin_sum_pivot_row {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (r : Fin.t m') (g : Fin.t (S m') → Kc) :
  fin_sum K (fun l => pivot_basis c p r l ⊗ g l)
    ≈ g (fin_delete p r) ⊕ ⊖ (pivot_coeff c p r ⊗ g p).
Proof.
  transitivity (fin_sum K (fun l => delta K (fin_delete p r) l ⊗ g l)
                ⊕ fin_sum K (fun l =>
                    ⊖ ((pivot_coeff c p r ⊗ delta K p l) ⊗ g l))).
  { rewrite <- fin_sum_add.
    apply fin_sum_respects; intro l.
    unfold pivot_basis.
    rewrite rig_distr_r.
    apply rig_add_respects; [ reflexivity |].
    apply ring_neg_mul_l. }
  apply rig_add_respects; [ apply fin_sum_delta_l |].
  assert (HX : fin_sum K (fun l =>
                 (pivot_coeff c p r ⊗ delta K p l) ⊗ g l)
               ≈ pivot_coeff c p r ⊗ g p).
  { transitivity (pivot_coeff c p r
                  ⊗ fin_sum K (fun l => delta K p l ⊗ g l)).
    - rewrite fin_sum_mul_l.
      apply fin_sum_respects; intro l.
      apply rig_mul_assoc.
    - apply rig_mul_respects; [ reflexivity |].
      apply fin_sum_delta_l. }
  rewrite fin_sum_neg, HX.
  reflexivity.
Qed.

(* Every row of the pivot basis kills the column it was built from —
   this is where [finv_l] is spent, and where [Hp] pays for its guard. *)
Lemma pivot_basis_annihilates {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (Hp : c p ≈ 0K → False) (r : Fin.t m') :
  fin_sum K (fun l => pivot_basis c p r l ⊗ c l) ≈ 0K.
Proof.
  rewrite fin_sum_pivot_row.
  unfold pivot_coeff.
  rewrite rig_mul_assoc.
  rewrite (finv_l K (c p) Hp).
  rewrite rig_mul_one_r.
  apply ring_neg_r.
Qed.

(* The pivot column of a combination of the basis rows. *)
Lemma pivot_col_pivot {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (v : Fin.t m' → Kc) :
  fin_sum K (fun r => v r ⊗ pivot_basis c p r p)
    ≈ ⊖ (fin_sum K (fun r => v r ⊗ pivot_coeff c p r)).
Proof.
  rewrite <- fin_sum_neg.
  apply fin_sum_respects; intro r.
  unfold pivot_basis.
  rewrite (delta_neq K (fin_delete p r) p (fin_delete_neq p r)).
  rewrite delta_refl, rig_mul_one_r, rig_add_zero_l.
  apply ring_neg_mul_r.
Qed.

(* Every other column of a combination of the basis rows reads off the
   corresponding coefficient — this is the independence half. *)
Lemma pivot_col_other {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (v : Fin.t m' → Kc) (r0 : Fin.t m') :
  fin_sum K (fun r => v r ⊗ pivot_basis c p r (fin_delete p r0)) ≈ v r0.
Proof.
  transitivity (fin_sum K (fun r => v r ⊗ delta K r r0)).
  - apply fin_sum_respects; intro r.
    apply rig_mul_respects; [ reflexivity |].
    unfold pivot_basis.
    rewrite (delta_neq K p (fin_delete p r0)
               (fun H => fin_delete_neq p r0 (eq_sym H))).
    rewrite rig_mul_zero_r, ring_neg_zero, rig_add_zero_r.
    apply delta_delete.
  - apply fin_sum_delta_r.
Qed.

(* The pivot column of the mediator's image.  This is the one place the
   hypothesis "h kills the column" is spent, and it is spent through
   [fin_sum_delete]: the sum over all indices splits at p, so the sum
   over the complement is exactly the negative of the p-th term. *)
Lemma pivot_mediator_pivot_col {m' z : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (Hp : c p ≈ 0K → False) (h : Matrix K z (S m'))
  (Hh : ∀ a, fin_sum K (fun l => h a l ⊗ c l) ≈ 0K) (a : Fin.t z) :
  fin_sum K (fun r => h a (fin_delete p r) ⊗ pivot_basis c p r p)
    ≈ h a p.
Proof.
  rewrite pivot_col_pivot.
  assert (Hsum : fin_sum K (fun r =>
                   h a (fin_delete p r) ⊗ pivot_coeff c p r)
                 ≈ ⊖ (h a p ⊗ c p) ⊗ finv K (c p)).
  { transitivity (fin_sum K (fun r =>
        (h a (fin_delete p r) ⊗ c (fin_delete p r)) ⊗ finv K (c p))).
    - apply fin_sum_respects; intro r.
      unfold pivot_coeff.
      symmetry; apply rig_mul_assoc.
    - rewrite <- fin_sum_mul_r.
      apply rig_mul_respects; [| reflexivity ].
      apply (ring_neg_unique K).
      transitivity (fin_sum K (fun l => h a l ⊗ c l)).
      + symmetry; apply (fin_sum_delete (fun l => h a l ⊗ c l) p).
      + apply Hh. }
  rewrite Hsum, ring_neg_mul_l, ring_neg_involutive, rig_mul_assoc.
  rewrite (finv_r K (c p) Hp).
  apply rig_mul_one_r.
Qed.

(** ** Splitting off the first column

    A row vector kills M exactly when it kills the first column and
    kills the remaining ones; [mat_col0] and [mat_tail] name the two
    halves.  The two [eq_refl] Examples are the reason [lnb_step] is
    cheap: taking the first column of a product and multiplying into the
    first column are THE SAME TERM, not merely equivalent matrices, and
    likewise for the tail.  The [≈] restatements exist only so that
    [rewrite] has something to match. *)

Definition mat_col0 {m n : nat} (M : Matrix K m (S n)) : Matrix K m 1 :=
  fun i _ => M i Fin.F1.

Definition mat_tail {m n : nat} (M : Matrix K m (S n)) : Matrix K m n :=
  fun i j => M i (Fin.FS j).

Example mat_mul_col0_strict {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_col0 (mat_mul h M) = mat_mul h (mat_col0 M) := eq_refl.

Example mat_mul_tail_strict {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_tail (mat_mul h M) = mat_mul h (mat_tail M) := eq_refl.

Lemma mat_mul_col0 {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_col0 (mat_mul h M) ≈ mat_mul h (mat_col0 M).
Proof. intros a j; reflexivity. Qed.

Lemma mat_mul_tail {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_tail (mat_mul h M) ≈ mat_mul h (mat_tail M).
Proof. intros a j; reflexivity. Qed.

Lemma col0_of_zero {a n : nat} (X : Matrix K a (S n)) :
  X ≈ mat_zero → mat_col0 X ≈ mat_zero.
Proof. intros H i j; exact (H i Fin.F1). Qed.

Lemma tail_of_zero {a n : nat} (X : Matrix K a (S n)) :
  X ≈ mat_zero → mat_tail X ≈ mat_zero.
Proof. intros H i j; exact (H i (Fin.FS j)). Qed.

Lemma zero_of_col0_tail {a n : nat} (X : Matrix K a (S n)) :
  mat_col0 X ≈ mat_zero → mat_tail X ≈ mat_zero → X ≈ mat_zero.
Proof.
  intros H0 H1 i j.
  pattern j; apply (Fin.caseS' j); clear j.
  - exact (H0 i Fin.F1).
  - intro y; exact (H1 i y).
Qed.

Lemma zero_cols {m : nat} (M : Matrix K m 0) : M ≈ mat_zero.
Proof. intros i j; inversion j. Qed.

(** ** The specification

    [E] is a basis of the left null space of M: its rows are killed by M
    ([lnb_annih]) and every row vector killed by M is a UNIQUE
    combination of them ([lnb_univ]) — existence is spanning,
    uniqueness is linear independence.  Nothing here mentions a colimit,
    a cocone or a quotient; the record speaks of [mat_mul] and
    [mat_zero] and of nothing else. *)

Record LeftNullBasis {m n : nat} (M : Matrix K m n) : Type := {
  lnb_dim : nat;
  lnb_basis : Matrix K lnb_dim m;
  lnb_annih : mat_mul lnb_basis M ≈ mat_zero;
  lnb_univ : ∀ (z : nat) (h : Matrix K z m),
    mat_mul h M ≈ mat_zero →
    ∃! u : Matrix K z lnb_dim, mat_mul u lnb_basis ≈ h
}.

Arguments lnb_dim {m n M} _.
Arguments lnb_basis {m n M} _.
Arguments lnb_annih {m n M} _.
Arguments lnb_univ {m n M} _ _ _ _.

(** ** The degenerate case: a matrix that vanishes

    If M is the zero matrix every row vector is in its left null space,
    so the identity matrix is a basis.  This covers both the
    no-columns base case of the recursion and the column that vanishes
    identically. *)

Definition lnb_id {m n : nat} (M : Matrix K m n) (Hz : M ≈ mat_zero) :
  LeftNullBasis M.
Proof.
  refine {| lnb_dim := m; lnb_basis := mat_id m |}.
  - rewrite mat_mul_id_l; exact Hz.
  - intros z h _.
    refine {| unique_obj := h |}.
    + apply mat_mul_id_r.
    + intros v Hv.
      transitivity (mat_mul v (mat_id m)).
      * symmetry; exact Hv.
      * apply mat_mul_id_r.
Defined.

(** ** One column

    The single-column case is the whole content of elimination: either
    the column vanishes, and the identity is a basis, or a pivot exists
    and the m − 1 vectors of [pivot_basis] are one.  The mediator is
    RESTRICTION along [fin_delete p]. *)

Definition col_null_basis :
  ∀ (m : nat) (C : Matrix K m 1), LeftNullBasis C.
Proof.
  intro m; destruct m as [|m']; intro C.
  - apply (lnb_id C).
    intros i j; inversion i.
  - destruct (find_nonzero (S m') (fun i => C i Fin.F1))
      as [[p Hp] | Hall].
    + refine {| lnb_dim := m';
                lnb_basis := pivot_basis (fun i => C i Fin.F1) p |}.
      * intros r j.
        rewrite (fin1_F1 j).
        exact (pivot_basis_annihilates (fun i => C i Fin.F1) p Hp r).
      * intros z h Hh.
        assert (Hcol : ∀ a, fin_sum K
                        (fun l => h a l ⊗ C l Fin.F1) ≈ 0K)
          by (intro a; exact (Hh a Fin.F1)).
        refine {| unique_obj :=
                    fun a r => h a (fin_delete p r) |}.
        -- intros a j.
           destruct (fin_pivot_cases p j) as [He | [r0 Hr0]].
           ++ rewrite He.
              exact (pivot_mediator_pivot_col
                       (fun i => C i Fin.F1) p Hp h Hcol a).
           ++ rewrite <- Hr0.
              exact (pivot_col_other (fun i => C i Fin.F1) p
                       (fun r => h a (fin_delete p r)) r0).
        -- intros v Hv a r.
           symmetry.
           transitivity (fin_sum K (fun s =>
             v a s ⊗ pivot_basis (fun i => C i Fin.F1) p s
                       (fin_delete p r))).
           ++ symmetry; apply pivot_col_other.
           ++ exact (Hv a (fin_delete p r)).
    + apply (lnb_id C).
      intros i j; rewrite (fin1_F1 j); exact (Hall i).
Defined.

(** ** One column at a time

    A row vector kills M exactly when it kills the first column and the
    rest.  So if E1 is a basis for the first column and E2 is a basis
    for [E1 · tail M], then [E2 · E1] is a basis for M: annihilation is
    associativity, and the mediator for h is obtained by mediating twice,
    which is also why it is unique. *)

Definition lnb_step {m n : nat} (M : Matrix K m (S n))
  (B1 : LeftNullBasis (mat_col0 M))
  (B2 : LeftNullBasis (mat_mul (lnb_basis B1) (mat_tail M))) :
  LeftNullBasis M.
Proof.
  refine {| lnb_dim := lnb_dim B2;
            lnb_basis := mat_mul (lnb_basis B2) (lnb_basis B1) |}.
  - apply zero_of_col0_tail.
    + rewrite mat_mul_col0, mat_mul_assoc, (lnb_annih B1).
      apply mat_mul_zero_r.
    + rewrite mat_mul_tail, mat_mul_assoc.
      exact (lnb_annih B2).
  - intros z h Hh.
    assert (H0 : mat_mul h (mat_col0 M) ≈ mat_zero).
    { rewrite <- mat_mul_col0.
      apply col0_of_zero; exact Hh. }
    assert (H1 : mat_mul (unique_obj (lnb_univ B1 z h H0))
                   (mat_mul (lnb_basis B1) (mat_tail M)) ≈ mat_zero).
    { rewrite <- mat_mul_assoc.
      rewrite (unique_property (lnb_univ B1 z h H0)).
      rewrite <- mat_mul_tail.
      apply tail_of_zero; exact Hh. }
    refine {| unique_obj := unique_obj (lnb_univ B2 z _ H1) |}.
    + rewrite <- mat_mul_assoc.
      rewrite (unique_property (lnb_univ B2 z _ H1)).
      exact (unique_property (lnb_univ B1 z h H0)).
    + intros v Hv.
      apply (uniqueness (lnb_univ B2 z _ H1)).
      symmetry.
      apply (uniqueness (lnb_univ B1 z h H0)).
      rewrite mat_mul_assoc; exact Hv.
Defined.

(** ** The construction

    Recursion on the number of columns.  Every step consumes one column
    through [col_null_basis] and hands the rest, pushed through the
    basis found so far, to the recursive call. *)

Fixpoint lnb_rec (n : nat) :
  ∀ (m : nat) (M : Matrix K m n), LeftNullBasis M :=
  match n with
  | O => fun m M => lnb_id M (zero_cols M)
  | S n' => fun m M =>
      let B1 := col_null_basis m (mat_col0 M) in
      lnb_step M B1
        (lnb_rec n' (lnb_dim B1)
           (mat_mul (lnb_basis B1) (mat_tail M)))
  end.

(* THE HEADLINE: every matrix over a field with a zero test has a basis
   of its left null space, with the universal clause. *)
Definition left_null_basis {m n : nat} (M : Matrix K m n) :
  LeftNullBasis M := lnb_rec n m M.

(** ** The difference form

    A row vector h satisfies [h · A ≈ h · B] exactly when it kills
    [A − B].  That translation is what turns a basis of a left null
    space into a solution of the two-matrix problem, and it is the last
    thing this file says; the two statements are equivalent by ordinary
    matrix algebra, and no further vocabulary is introduced. *)

Lemma mat_mul_sub_r {a b c : nat} (h : Matrix K a b)
  (A B : Matrix K b c) :
  mat_mul h (mat_sub A B) ≈ mat_sub (mat_mul h A) (mat_mul h B).
Proof.
  intros i j.
  transitivity (fin_sum K (fun l =>
                  h i l ⊗ A l j ⊕ ⊖ (h i l ⊗ B l j))).
  - apply fin_sum_respects; intro l.
    unfold mat_sub.
    rewrite rig_distr_l.
    apply rig_add_respects; [ reflexivity |].
    apply ring_neg_mul_r.
  - rewrite fin_sum_add.
    apply rig_add_respects; [ reflexivity |].
    apply fin_sum_neg.
Qed.

Lemma mat_sub_zero {a b : nat} (A B : Matrix K a b) :
  (mat_sub A B ≈ mat_zero) ↔ (A ≈ B).
Proof.
  split.
  - intros H i j.
    assert (Hij : A i j ⊕ ⊖ (B i j) ≈ 0K) by exact (H i j).
    transitivity (A i j ⊕ (⊖ (B i j) ⊕ B i j)).
    + rewrite (ring_neg_l K (B i j)), rig_add_zero_r; reflexivity.
    + rewrite <- rig_add_assoc, Hij, rig_add_zero_l; reflexivity.
  - intros H i j.
    change (A i j ⊕ ⊖ (B i j) ≈ 0K).
    rewrite (H i j).
    apply ring_neg_r.
Qed.

Theorem mat_mul_sub_zero_iff {a b c : nat} (h : Matrix K a b)
  (A B : Matrix K b c) :
  (mat_mul h (mat_sub A B) ≈ mat_zero) ↔ (mat_mul h A ≈ mat_mul h B).
Proof.
  split; intro H.
  - apply (fst (mat_sub_zero (mat_mul h A) (mat_mul h B))).
    rewrite <- mat_mul_sub_r; exact H.
  - rewrite mat_mul_sub_r.
    apply (snd (mat_sub_zero (mat_mul h A) (mat_mul h B))); exact H.
Qed.

(* The two-matrix statement, packaged with no reference to [mat_sub]:
   for any parallel pair there is a matrix E equalizing them on the left
   through which every left-equalizing matrix factors uniquely.  This is
   the whole of what the elimination engine is for. *)
Theorem left_null_basis_diff {m n : nat} (A B : Matrix K m n) :
  { k : nat & { E : Matrix K k m &
      (mat_mul E A ≈ mat_mul E B) ∧
      (∀ (z : nat) (h : Matrix K z m), mat_mul h A ≈ mat_mul h B →
        ∃! u : Matrix K z k, mat_mul u E ≈ h) } }.
Proof.
  pose (Bs := left_null_basis (mat_sub A B)).
  exists (lnb_dim Bs), (lnb_basis Bs).
  split.
  - apply (fst (mat_mul_sub_zero_iff (lnb_basis Bs) A B)).
    exact (lnb_annih Bs).
  - intros z h Hh.
    apply (lnb_univ Bs z h).
    apply (snd (mat_mul_sub_zero_iff h A B)); exact Hh.
Qed.

End Elimination.

(* The field is recoverable from a [LeftNullBasis] but not from a bare
   matrix ([Matrix] is indexed by the underlying RIG), so K stays
   explicit on the matrix operations and becomes implicit on the record's
   projections. *)
Arguments LeftNullBasis K {m n} _.
Arguments lnb_dim {K m n M} _.
Arguments lnb_basis {K m n M} _.
Arguments lnb_annih {K m n M} _.
Arguments lnb_univ {K m n M} _ _ _ _.

(** ** The deciders, and why the in-tree ones are re-proved here

    [F2_Field_dec] and [Q_Field_dec] (Instance/Field.v) inhabit the
    hypothesis EXACTLY — the two ascriptions below record that, and they
    are what makes the section variable [Kdec] the tree's own notion and
    not a new one.  But both are [Qed] lemmas, so no application of
    either reduces, and the elimination engine — which matches on the
    decider's answer to find a pivot — computes with neither.  This was
    MEASURED, not anticipated: with [F2_Field_dec] supplied, the check
    [lnb_dim f2_col_lnb = 1%nat] is rejected by [eq_refl] with "cannot
    unify [lnb_dim f2_col_lnb] and [1%nat]".  The two transparent copies
    below decide the same relations by the same case analyses and differ
    only in ending with [Defined]; they are what the computing witnesses
    run on.  The opacity is Instance/Field.v's, is NOT repaired here, and
    nothing above depends on it being repaired — the construction is
    correct with either. *)

Definition F2_dec_inhabits :
  ∀ a b : carrier (rig_setoid F2_Field), (a ≈ b) + (a ≈ b → False) :=
  F2_Field_dec.

Definition Q_dec_inhabits :
  ∀ a b : carrier (rig_setoid Q_Field), (a ≈ b) + (a ≈ b → False) :=
  Q_Field_dec.

Definition f2_dec (a b : carrier (rig_setoid F2_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct a, b; solve [ left; reflexivity | right; discriminate ].
Defined.

Definition q_dec (a b : carrier (rig_setoid Q_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct (Qeq_dec a b) as [H | H]; [ left | right ]; exact H.
Defined.

(** ** Witnesses over F₂

    [F2_Field] (Instance/Field.v) is the cheapest base at which every
    step of the construction computes: the carrier is [bool] with
    Leibniz equality, the decider is a two-way case analysis, and the
    field operations are [xorb] and [andb].  Each check below closes by
    [eq_refl], so the elimination engine is not merely inhabited, it
    RUNS. *)

(* The 2 × 1 column (1, 1).  Its left null space is the line spanned by
   (1, 1) — over F₂ that is the only nonzero vector killing it. *)
Definition f2_col : Matrix F2_Field 2 1 := fun _ _ => true.

Definition f2_col_lnb : LeftNullBasis F2_Field f2_col :=
  left_null_basis F2_Field f2_dec f2_col.

Example f2_col_dim : lnb_dim f2_col_lnb = 1%nat := eq_refl.

Example f2_col_basis_0 :
  lnb_basis f2_col_lnb Fin.F1 Fin.F1 = true := eq_refl.

Example f2_col_basis_1 :
  lnb_basis f2_col_lnb Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(* The annihilation, COMPUTED rather than cited: 1·1 + 1·1 = 0 in F₂. *)
Example f2_col_annih_computes :
  mat_mul F2_Field (lnb_basis f2_col_lnb) f2_col Fin.F1 Fin.F1 = false :=
  eq_refl.

(* The universal clause is not vacuous.  The row vector (1, 1) kills the
   column, so it must factor through the basis, and the mediator the
   construction produces is the 1 × 1 matrix (1) — computed. *)
Definition f2_h : Matrix F2_Field 1 2 := fun _ _ => true.

Lemma f2_h_kills : mat_mul F2_Field f2_h f2_col ≈ mat_zero F2_Field.
Proof. intros i j; reflexivity. Qed.

(* Stated without an ascription: writing the [∃!] out again would
   elaborate [f2_col_lnb] at fresh universes and the two would not
   unify — measured, and the reason the type is left inferred. *)
Definition f2_mediator := lnb_univ f2_col_lnb 1 f2_h f2_h_kills.

Example f2_mediator_computes :
  unique_obj f2_mediator Fin.F1 Fin.F1 = true := eq_refl.

(* The dimension responds to the matrix, which is what makes the search
   for a pivot load-bearing: the 2 × 2 identity has NO nonzero row
   vector in its left null space... *)
Definition f2_id2 : Matrix F2_Field 2 2 :=
  fun i j => delta F2_Field i j.

Example f2_id2_dim :
  lnb_dim (left_null_basis F2_Field f2_dec f2_id2) = 0%nat :=
  eq_refl.

(* ...while the all-ones 2 × 2 matrix, whose two columns coincide, has a
   one-dimensional one, spanned again by (1, 1). *)
Definition f2_ones : Matrix F2_Field 2 2 := fun _ _ => true.

Definition f2_ones_lnb : LeftNullBasis F2_Field f2_ones :=
  left_null_basis F2_Field f2_dec f2_ones.

Example f2_ones_dim : lnb_dim f2_ones_lnb = 1%nat := eq_refl.

Example f2_ones_basis_0 :
  lnb_basis f2_ones_lnb Fin.F1 Fin.F1 = true := eq_refl.

Example f2_ones_basis_1 :
  lnb_basis f2_ones_lnb Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(** ** A witness over ℚ

    [Q_Field] with this file's own TRANSPARENT [q_dec] -- not the
    Qed-opaque [Q_Field_dec]; an earlier draft of this sentence named the
    latter, contradicting THE DECIDERS above -- is a base in
    which the pivot DIVISION does something: the basis vector of the
    column (1, 2) is (−2, 1), and the coefficient −2 is produced by
    [finv], not by a case analysis.  The entries close by [eq_refl] as
    well, the rational arithmetic reducing on closed input. *)

Definition q_col : Matrix Q_Field 2 1 :=
  fun i _ => match i with
             | Fin.F1 => 1%Q
             | _ => 2%Q
             end.

Definition q_col_lnb : LeftNullBasis Q_Field q_col :=
  left_null_basis Q_Field q_dec q_col.

Example q_col_dim : lnb_dim q_col_lnb = 1%nat := eq_refl.

Example q_col_basis_0 :
  lnb_basis q_col_lnb Fin.F1 Fin.F1 = (-2 # 1)%Q := eq_refl.

Example q_col_basis_1 :
  lnb_basis q_col_lnb Fin.F1 (Fin.FS Fin.F1) = (1 # 1)%Q := eq_refl.

(* (−2)·1 + 1·2 = 0, computed in ℚ. *)
Example q_col_annih_computes :
  mat_mul Q_Field (lnb_basis q_col_lnb) q_col Fin.F1 Fin.F1
    = (0 # 1)%Q := eq_refl.
