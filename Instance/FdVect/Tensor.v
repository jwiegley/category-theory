(** * The diagonal square functor on FdVect, and what maps into it

    Riehl, "Category Theory in Context", §1.4 Example 1.4.4(vii),
    printed p. 26.  Over a field the assignment V ↦ V ⊗ V extends to an
    endofunctor of finite-dimensional vector spaces, and Riehl's
    observation is that the ONLY natural transformation from the
    identity functor to it is the zero one.  It is the elementary
    illustration that "a map given at every object" is far weaker than
    "a natural family": the naturality square at the scalar map
    v ↦ λ·v forces λ·α_V(v) ≈ λ²·α_V(v) for every scalar λ, and at
    λ = 2 that reads 2a ≈ 4a, whence 2a ≈ 0 and — the characteristic
    hypothesis being 1 + 1 ≉ 0 — a ≈ 0.  That is [diag_transform_zero]
    below, and [diag_transform_zero_Q] is it over ℚ.

    THE PRE-EXISTING ABSTRACT COUNTERPART, and how it differs.  This
    tree already carries a no-cloning statement:
    Structure/Monoidal/Collapse.v:526's

      Theorem no_cloning : @braid C _ x x ≈ id[(x ⨂ x)%object]

    (Abramsky, arXiv:0910.2401, Theorem 11).  Its hypotheses are a
    compact closed category equipped with a RelevanceMonoidal structure
    — that is, a natural cocommutative diagonal ∆, which the same file
    records at [diagonal_natural'] as being precisely a natural
    transformation from the identity functor to the squaring functor —
    and its conclusion is that the braiding on every diagonal square
    collapses to the identity.  So it ASSUMES the natural diagonal and
    derives a degeneracy of the ambient category from it, abstractly,
    with no object of any category ever inspected.

    The present file is Riehl's CONCRETE computation instead: it fixes
    one category, the finite-dimensional based spaces of
    Instance/FdVect.v, builds the squaring endofunctor there by hand,
    and proves that the transformations themselves are all zero.
    Neither statement implies the other.  Collapse.v's result says
    nothing about which categories carry a natural diagonal — it is
    silent on inhabitation — and it concerns the braiding, which
    [FdVect] has not been given at all: no monoidal structure on this
    tree's [FdVect] is built here or anywhere else in the tree, and
    Structure/Monoidal/CompactClosed.v's mentions of finite-dimensional
    vector spaces are prose in its header essay, not an instance.
    Conversely
    nothing below rules out a natural diagonal in some other compact
    closed category, and nothing below is discharged by citing
    no_cloning: the two proofs share no lemma, and the word "cloning"
    is a name for a family of results, not an argument.  What they do
    share is a moral, which is why they are cross-referenced here.

    SCOPE, stated plainly.  The full tensor BIFUNCTOR is NOT built.
    Nothing here defines ⊗ on pairs of spaces, on pairs of maps, or its
    unitors and associator; there is no monoidal structure on [FdVect]
    in this file or in the tree.  What is built is the DIAGONAL
    endofunctor [TensorSq] alone, which is all Riehl's example needs
    and all the theorem quantifies over.  Its object realization is the
    based space of dimension n·n, [StdVect F (fdv_dim V * fdv_dim V)]:
    an object of [FdVect F] is a module together with CHOSEN
    coordinates (Instance/FdVect.v's design decision, disclosed at
    length there), so the tensor square of a based space is canonically
    the based space on the product index set, indexed by
    Instance/FinSet/Product.v's [fin_pair]/[fin_unpair] codec.  On
    morphisms [TensorSq] acts by the Kronecker square of the matrix,
    which is exactly what f ⊗ f does in coordinates.  A reader wanting
    the bifunctor should read this as its restriction along the
    diagonal, not as a substitute for it.

    THE CHARACTERISTIC HYPOTHESIS IS EXPLICIT.  The scaling argument
    cancels a 2, so it needs 1 + 1 ≉ 0; over a field of characteristic
    two the computation stalls at 2a ≈ 2a and proves nothing.  The
    hypothesis is therefore carried as a named argument
    [two_nz : rig_add F (rig_one F) (rig_one F) ≈ rig_zero F → False]
    on the theorem rather than hidden in a class, and it is discharged
    concretely at ℚ in [diag_transform_zero_Q], which is the file's
    witness that the hypothesis is satisfiable.

    [finv] BECOMES LOAD-BEARING HERE.  Instance/FdVect.v closes with
    the disclosure that the matrix equivalence spends only the
    COMMUTATIVITY of the base ring — that [finv], [finv_l] and
    [field_one_neq_zero] are content of the [FieldObject] class rather
    than premises of that theorem, so the whole equivalence would
    restate over any commutative ring.  This file is where the
    inversion earns its keep: [double_zero] multiplies by [finv F two]
    and spends [finv_l] to cancel the 2, and there is no route around
    it, since over a commutative ring in which 2 is a zero divisor the
    conclusion is simply not available.  Commutativity is spent too,
    in [mul_shuffle4] and [mul_swap_left] and in [scale] (a scalar map
    is linear only over a commutative ring), but it is no longer the
    only thing spent.

    UPSTREAMING CANDIDATES.  [fin_sum_split], [fin_sum_pair],
    [fin_pair_inj], [delta_pair] and [fin_sum_pair_mul] are statements
    about the finite-sum engine and the pairing codec with no vector
    space anywhere in them; they belong beside Instance/Matr.v's
    [fin_sum_swap] and are kept here only because this is the first
    consumer.  Their one dependency outside Matr.v is
    Instance/FinSet/Product.v, which Matr.v does not currently import.

    ORIENTATION.  [fentry f i k] is the coordinate k of the image of
    the i-th basis vector, so the SOURCE index comes first — the
    transpose of Instance/Matr.v's convention, chosen so that
    [hom_coords] reads coord(f v) k ≈ Σ_i coord(v) i · fentry f i k
    with the summed index adjacent in both factors.  Nothing depends
    on the choice beyond internal consistency, and [fentry_id] pins it
    down: the identity's table is [delta k i], not [delta i k]. *)

(* [Coq.QArith.QArith] is imported FIRST for the same reason
   Instance/FdVect.v gives: it exports a competing [equiv], which would
   shadow [Category.Lib.Setoid.equiv] in every [Proper] signature
   below.  Importing the library afterwards restores the intended one. *)
Require Import Coq.QArith.QArith.
Require Import Coq.Vectors.Fin.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FdVect.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

Section Tensor.

Context (F : FieldObject).

(* An abbreviation for the underlying rig, purely to keep the finite-sum
   applications below inside the column budget.  It is a section-local
   notation and disappears at [End Tensor]. *)
Notation FR := (field_ring F).

(** ** The index kit

    Five statements about [fin_sum] and the [fin_pair]/[fin_unpair]
    codec, none of which mentions a vector space.  They are what turns
    a sum over the product index set Fin.t (m * n) into a double sum,
    and a product of two Kronecker deltas into one. *)

(* A sum over Fin.t (a + b) splits into the two blocks cut out by
   [Fin.L] and [Fin.R].  Both index shifts reduce judgmentally, so the
   induction needs no transport. *)
Lemma fin_sum_split (a b : nat)
  (h : Fin.t (a + b) → carrier (rig_setoid F)) :
  fin_sum FR h
    ≈ rig_add F (fin_sum FR (fun i : Fin.t a => h (Fin.L b i)))
                (fin_sum FR (fun j : Fin.t b => h (Fin.R a j))).
Proof.
  revert h.
  induction a as [| a' IH]; intro h; simpl.
  - now rewrite rig_add_zero_l.
  - rewrite (IH (fun x : Fin.t (a' + b) => h (Fin.FS x))).
    now rewrite rig_add_assoc.
Qed.

(* A sum over Fin.t (m * n) is the double sum over its two components,
   the codec's first clause being [Fin.L] and its second [Fin.R], both
   judgmentally. *)
Lemma fin_sum_pair (m n : nat)
  (h : Fin.t (m * n) → carrier (rig_setoid F)) :
  fin_sum FR h
    ≈ fin_sum FR (fun i : Fin.t m =>
        fin_sum FR (fun j : Fin.t n => h (fin_pair i j))).
Proof.
  revert h.
  induction m as [| m' IH]; intro h; simpl.
  - reflexivity.
  - rewrite (fin_sum_split n (m' * n) h).
    apply rig_add_respects; [ reflexivity |].
    apply (IH (fun q : Fin.t (m' * n) => h (Fin.R n q))).
Qed.

(* The codec is injective, by its own round trip. *)
Lemma fin_pair_inj {m n : nat} (i k : Fin.t m) (j l : Fin.t n) :
  fin_pair i j = fin_pair k l → (i = k) * (j = l).
Proof.
  intro H.
  pose proof (f_equal (@fin_unpair m n) H) as Hp.
  rewrite !fin_unpair_pair in Hp.
  exact (f_equal fst Hp, f_equal snd Hp).
Qed.

(* A delta on the product index set factors as the product of the two
   component deltas. *)
Lemma delta_pair {m n : nat} (i k : Fin.t m) (j l : Fin.t n) :
  delta FR (fin_pair i j) (fin_pair k l)
    ≈ rig_mul F (delta FR i k) (delta FR j l).
Proof.
  destruct (Fin.eq_dec i k) as [Hik | Hik];
  destruct (Fin.eq_dec j l) as [Hjl | Hjl].
  - subst.
    rewrite !delta_refl.
    now rewrite rig_mul_one_l.
  - rewrite (delta_neq FR j l Hjl).
    rewrite rig_mul_zero_r.
    apply delta_neq.
    intro Hc.
    exact (Hjl (snd (fin_pair_inj i k j l Hc))).
  - rewrite (delta_neq FR i k Hik).
    rewrite rig_mul_zero_l.
    apply delta_neq.
    intro Hc.
    exact (Hik (fst (fin_pair_inj i k j l Hc))).
  - rewrite (delta_neq FR i k Hik).
    rewrite rig_mul_zero_l.
    apply delta_neq.
    intro Hc.
    exact (Hik (fst (fin_pair_inj i k j l Hc))).
Qed.

(* The form the Kronecker square actually presents: a product of the
   two component deltas of a decoded index pair is the delta of the
   indices themselves. *)
Lemma delta_unpair {m n : nat} (a b : Fin.t (m * n)) :
  rig_mul F (delta FR (fst (fin_unpair a)) (fst (fin_unpair b)))
            (delta FR (snd (fin_unpair a)) (snd (fin_unpair b)))
    ≈ delta FR a b.
Proof.
  transitivity (delta FR
    (fin_pair (fst (fin_unpair a)) (snd (fin_unpair a)))
    (fin_pair (fst (fin_unpair b)) (snd (fin_unpair b)))).
  - symmetry; apply delta_pair.
  - now rewrite !fin_pair_unpair.
Qed.

(* A sum of separated products over the product index set is the
   product of the two sums.  This is the shape [fmap_comp] needs. *)
Lemma fin_sum_pair_mul (m n : nat)
  (h1 : Fin.t m → carrier (rig_setoid F))
  (h2 : Fin.t n → carrier (rig_setoid F)) :
  fin_sum FR (fun p => rig_mul F (h1 (fst (fin_unpair p)))
                                 (h2 (snd (fin_unpair p))))
    ≈ rig_mul F (fin_sum FR h1) (fin_sum FR h2).
Proof.
  rewrite (fin_sum_pair m n
    (fun p => rig_mul F (h1 (fst (fin_unpair p)))
                        (h2 (snd (fin_unpair p))))).
  rewrite (fin_sum_mul_r FR (fin_sum FR h2) h1).
  apply fin_sum_respects; intro i.
  rewrite (fin_sum_mul_l FR (h1 i) h2).
  apply fin_sum_respects; intro j.
  now rewrite fin_unpair_pair.
Qed.

(** ** Two commutative rearrangements

    Both spend [field_comm], and nothing else. *)

Lemma mul_shuffle4 (a b c d : carrier (rig_setoid F)) :
  rig_mul F (rig_mul F a b) (rig_mul F c d)
    ≈ rig_mul F (rig_mul F a c) (rig_mul F b d).
Proof.
  rewrite (rig_mul_assoc F a b (rig_mul F c d)).
  rewrite <- (rig_mul_assoc F b c d).
  rewrite (field_comm F b c).
  rewrite (rig_mul_assoc F c b d).
  rewrite <- (rig_mul_assoc F a c (rig_mul F b d)).
  reflexivity.
Qed.

Lemma mul_swap_left (a b c : carrier (rig_setoid F)) :
  rig_mul F a (rig_mul F b c) ≈ rig_mul F b (rig_mul F a c).
Proof.
  rewrite <- (rig_mul_assoc F a b c).
  rewrite (field_comm F a b).
  apply rig_mul_assoc.
Qed.

(** ** The coordinate kit at a general based space

    Instance/FdVect.v develops the expansion v ≈ Σ_j v_j · e_j and the
    table of a linear map for the STANDARD spaces only ([std_expand],
    [matrix_of], both restricted to [StdVect]).  [TensorSq] needs both
    at an arbitrary based V, since its source is arbitrary; the
    arguments are the same ones, run through [fdv_coord] and
    [fdv_expand] instead of through the identity. *)

(* The i-th basis vector of V: the expansion of the i-th standard
   tuple.  A based object is exactly one for which this makes sense. *)
Definition bvec (V : FdVectObject F) (i : Fin.t (fdv_dim V)) :
  carrier (cmon_setoid (fdv_mod V)) :=
  fdv_expand V (std_basis F (fdv_dim V) i).

(* Coordinates turn a monoid sum into a rig sum, index by index.  This
   is [msum_std] one level up: there the module was F^n and the passage
   was pointwise; here it is any based V and the passage is the
   additivity of [fdv_coord]. *)
Lemma coord_msum (V : FdVectObject F) {p : nat}
  (g : Fin.t p → carrier (cmon_setoid (fdv_mod V)))
  (k : Fin.t (fdv_dim V)) :
  fdv_coord V (msum (fdv_mod V) g) k
    ≈ fin_sum FR (fun t => fdv_coord V (g t) k).
Proof.
  revert g.
  induction p as [| p' IH]; intros g; simpl.
  - apply fdv_coord_zero.
  - rewrite (fdv_coord_plus V (g Fin.F1)
      (msum (fdv_mod V) (fun i => g (Fin.FS i))) k).
    apply rig_add_respects; [ reflexivity |].
    apply (IH (fun i => g (Fin.FS i))).
Qed.

(* Coordinates are jointly injective — they ARE an isomorphism onto
   F^n — so agreeing at every index is agreeing. *)
Lemma coord_ext (V : FdVectObject F)
  (v w : carrier (cmon_setoid (fdv_mod V))) :
  (∀ k, fdv_coord V v k ≈ fdv_coord V w k) → v ≈ w.
Proof.
  intro H.
  transitivity (fdv_expand V (fdv_coord V v)).
  - symmetry; apply fdv_expand_coord.
  - transitivity (fdv_expand V (fdv_coord V w)).
    + apply fdv_expand_respects; exact H.
    + apply fdv_expand_coord.
Qed.

(* Every vector is the sum of its coordinates against the basis. *)
Lemma vec_expansion (V : FdVectObject F)
  (v : carrier (cmon_setoid (fdv_mod V))) :
  v ≈ msum (fdv_mod V)
        (fun i => rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i)).
Proof.
  apply coord_ext; intro k.
  rewrite (coord_msum V
    (fun i => rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i)) k).
  transitivity (fin_sum FR
    (fun i => rig_mul F (fdv_coord V v i) (delta FR i k))).
  - symmetry; apply (fin_sum_delta_r FR k (fdv_coord V v)).
  - apply fin_sum_respects; intro i.
    symmetry.
    rewrite (fdv_coord_smul V (fdv_coord V v i) (bvec V i) k).
    apply rig_mul_respects; [ reflexivity |].
    unfold bvec, std_basis.
    rewrite (fdv_coord_expand V (std_basis F (fdv_dim V) i) k).
    apply delta_sym.
Qed.

(* The table of a linear map: entry (i, k) is the k-th coordinate of
   the image of the i-th basis vector.  The SOURCE index comes first;
   see the header's orientation note. *)
Definition fentry {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (i : Fin.t (fdv_dim V)) (k : Fin.t (fdv_dim W)) :
  carrier (rig_setoid F) :=
  fdv_coord W (cmon_map (rm_hom f) (bvec V i)) k.

Lemma fentry_respects {V W : FdVectObject F}
  (f g : V ~{FdVect F}~> W) (H : f ≈ g)
  (i : Fin.t (fdv_dim V)) (k : Fin.t (fdv_dim W)) :
  fentry f i k ≈ fentry g i k.
Proof.
  exact (fdv_coord_respects W _ _ (H (bvec V i)) k).
Qed.

(* The identity's table is the Kronecker delta — with the arguments in
   this order, which is what pins the orientation down. *)
Lemma fentry_id (V : FdVectObject F) (i k : Fin.t (fdv_dim V)) :
  fentry (@id (FdVect F) V) i k ≈ delta FR k i.
Proof.
  unfold fentry, bvec.
  apply (fdv_coord_expand V (std_basis F (fdv_dim V) i) k).
Qed.

(* A linear map acts on coordinates by its table: this is the whole
   content of "a linear map is a matrix", at an arbitrary based source
   and target.  Instance/FdVect.v's [matrix_of_sur] is the same
   argument at the standard spaces, and this proof follows its shape. *)
Lemma hom_coords {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (v : carrier (cmon_setoid (fdv_mod V))) (k : Fin.t (fdv_dim W)) :
  fdv_coord W (cmon_map (rm_hom f) v) k
    ≈ fin_sum FR (fun i => rig_mul F (fdv_coord V v i) (fentry f i k)).
Proof.
  transitivity (fdv_coord W (cmon_map (rm_hom f)
    (msum (fdv_mod V)
       (fun i => rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i)))) k).
  { exact (fdv_coord_respects W _ _
      (proper_morphism (cmon_map (rm_hom f)) _ _ (vec_expansion V v)) k). }
  transitivity (fdv_coord W (msum (fdv_mod W)
    (fun i => cmon_map (rm_hom f)
       (rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i)))) k).
  { exact (fdv_coord_respects W _ _
      (msum_hom (rm_hom f)
         (fun i => rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i))) k). }
  rewrite (coord_msum W
    (fun i => cmon_map (rm_hom f)
       (rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i))) k).
  apply fin_sum_respects; intro i.
  transitivity (fdv_coord W (rm_smul (fdv_mod W) (fdv_coord V v i)
    (cmon_map (rm_hom f) (bvec V i))) k).
  { exact (fdv_coord_respects W _ _
      (rm_map_smul f (fdv_coord V v i) (bvec V i)) k). }
  apply (fdv_coord_smul W (fdv_coord V v i)
    (cmon_map (rm_hom f) (bvec V i)) k).
Qed.

(* Tables compose by matrix multiplication.  With the orientation fixed
   above this is [hom_coords] at g applied to the image of a basis
   vector, and nothing else: the sum's factors are already [fentry f]
   and [fentry g] on the nose. *)
Lemma fentry_comp {V W X : FdVectObject F}
  (f : V ~{FdVect F}~> W) (g : W ~{FdVect F}~> X)
  (i : Fin.t (fdv_dim V)) (k : Fin.t (fdv_dim X)) :
  fentry (g ∘ f) i k
    ≈ fin_sum FR (fun j => rig_mul F (fentry f i j) (fentry g j k)).
Proof.
  exact (hom_coords g (cmon_map (rm_hom f) (bvec V i)) k).
Qed.

(** ** The diagonal square functor

    V ↦ V ⊗ V, realized on the carried coordinates.  See the header's
    SCOPE paragraph: ⊗ itself is not constructed, and this is not its
    restriction to the diagonal in any formal sense — it is the
    endofunctor whose value at a based space of dimension n is the
    based space of dimension n·n and whose value at a map is the
    Kronecker square of that map's table. *)

Definition TensorSq_obj (V : FdVectObject F) : FdVectObject F :=
  StdVect F (fdv_dim V * fdv_dim V).

(* The Kronecker square of the table of f, at the decoded index pairs
   of a source position p and a target position q. *)
Definition tsq_ker {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (p : Fin.t (fdv_dim V * fdv_dim V))
  (q : Fin.t (fdv_dim W * fdv_dim W)) : carrier (rig_setoid F) :=
  rig_mul F (fentry f (fst (fin_unpair p)) (fst (fin_unpair q)))
            (fentry f (snd (fin_unpair p)) (snd (fin_unpair q))).

Definition tsq_map {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim W * fdv_dim W)) : carrier (rig_setoid F) :=
  fin_sum FR (fun p => rig_mul F (t p) (tsq_ker f p q)).

(** *** Linearity, four lines of the finite-sum engine

    Stated as free-standing lemmas rather than left to [Program], so
    that the packaging below can hand them over as terms and obligation
    ORDER cannot matter. *)

Lemma tsq_map_respects {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (t u : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (H : ∀ p, t p ≈ u p) (q : Fin.t (fdv_dim W * fdv_dim W)) :
  tsq_map f t q ≈ tsq_map f u q.
Proof.
  apply fin_sum_respects; intro p.
  apply rig_mul_respects; [ exact (H p) | reflexivity ].
Qed.

Lemma tsq_map_zero {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (q : Fin.t (fdv_dim W * fdv_dim W)) :
  tsq_map f (fun _ => rig_zero F) q ≈ rig_zero F.
Proof.
  unfold tsq_map.
  transitivity (fin_sum FR
    (fun _ : Fin.t (fdv_dim V * fdv_dim V) => rig_zero F)).
  - apply fin_sum_respects; intro p.
    apply rig_mul_zero_l.
  - apply fin_sum_zero.
Qed.

Lemma tsq_map_plus {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (t u : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim W * fdv_dim W)) :
  tsq_map f (fun p => rig_add F (t p) (u p)) q
    ≈ rig_add F (tsq_map f t q) (tsq_map f u q).
Proof.
  unfold tsq_map.
  transitivity (fin_sum FR (fun p =>
    rig_add F (rig_mul F (t p) (tsq_ker f p q))
              (rig_mul F (u p) (tsq_ker f p q)))).
  - apply fin_sum_respects; intro p.
    apply rig_distr_r.
  - apply fin_sum_add.
Qed.

Lemma tsq_map_smul {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (r : carrier (rig_setoid F))
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim W * fdv_dim W)) :
  tsq_map f (fun p => rig_mul F r (t p)) q
    ≈ rig_mul F r (tsq_map f t q).
Proof.
  unfold tsq_map.
  rewrite (fin_sum_mul_l FR r
    (fun p => rig_mul F (t p) (tsq_ker f p q))).
  apply fin_sum_respects; intro p.
  apply rig_mul_assoc.
Qed.

(** *** The two functor laws that have content *)

(* The identity's Kronecker square is the identity: two deltas fuse
   into one by [delta_unpair], and the sum then collapses. *)
Lemma tsq_map_id (V : FdVectObject F)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  tsq_map (@id (FdVect F) V) t q ≈ t q.
Proof.
  unfold tsq_map.
  transitivity (fin_sum FR (fun p => rig_mul F (t p) (delta FR p q))).
  - apply fin_sum_respects; intro p.
    apply rig_mul_respects; [ reflexivity |].
    unfold tsq_ker.
    transitivity (rig_mul F
      (delta FR (fst (fin_unpair q)) (fst (fin_unpair p)))
      (delta FR (snd (fin_unpair q)) (snd (fin_unpair p)))).
    + apply rig_mul_respects; apply fentry_id.
    + transitivity (delta FR q p).
      * apply delta_unpair.
      * apply delta_sym.
  - apply (fin_sum_delta_r FR q t).
Qed.

(* Functoriality.  Pull the inner sum out, exchange the two sums,
   regroup the four table entries so that the two contractions
   separate, then run [fin_sum_pair_mul] and [fentry_comp]. *)
Lemma tsq_map_comp {V W X : FdVectObject F}
  (f : V ~{FdVect F}~> W) (g : W ~{FdVect F}~> X)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim X * fdv_dim X)) :
  tsq_map (g ∘ f) t q ≈ tsq_map g (tsq_map f t) q.
Proof.
  unfold tsq_map.
  symmetry.
  transitivity (fin_sum FR (fun s => fin_sum FR (fun p =>
    rig_mul F (rig_mul F (t p) (tsq_ker f p s)) (tsq_ker g s q)))).
  { apply fin_sum_respects; intro s.
    apply (fin_sum_mul_r FR (tsq_ker g s q)
      (fun p => rig_mul F (t p) (tsq_ker f p s))). }
  transitivity (fin_sum FR (fun p => fin_sum FR (fun s =>
    rig_mul F (rig_mul F (t p) (tsq_ker f p s)) (tsq_ker g s q)))).
  { apply fin_sum_swap. }
  apply fin_sum_respects; intro p.
  transitivity (fin_sum FR (fun s => rig_mul F (t p) (rig_mul F
    (rig_mul F (fentry f (fst (fin_unpair p)) (fst (fin_unpair s)))
               (fentry g (fst (fin_unpair s)) (fst (fin_unpair q))))
    (rig_mul F (fentry f (snd (fin_unpair p)) (snd (fin_unpair s)))
               (fentry g (snd (fin_unpair s)) (snd (fin_unpair q))))))).
  { apply fin_sum_respects; intro s.
    unfold tsq_ker.
    etransitivity; [ apply rig_mul_assoc |].
    apply rig_mul_respects; [ reflexivity |].
    apply mul_shuffle4. }
  transitivity (rig_mul F (t p) (fin_sum FR (fun s => rig_mul F
    (rig_mul F (fentry f (fst (fin_unpair p)) (fst (fin_unpair s)))
               (fentry g (fst (fin_unpair s)) (fst (fin_unpair q))))
    (rig_mul F (fentry f (snd (fin_unpair p)) (snd (fin_unpair s)))
               (fentry g (snd (fin_unpair s)) (snd (fin_unpair q))))))).
  { symmetry; apply fin_sum_mul_l. }
  apply rig_mul_respects; [ reflexivity |].
  etransitivity.
  { apply (fin_sum_pair_mul (fdv_dim W) (fdv_dim W)
      (fun j => rig_mul F (fentry f (fst (fin_unpair p)) j)
                          (fentry g j (fst (fin_unpair q))))
      (fun j => rig_mul F (fentry f (snd (fin_unpair p)) j)
                          (fentry g j (snd (fin_unpair q))))). }
  unfold tsq_ker.
  apply rig_mul_respects; symmetry; apply fentry_comp.
Qed.

(** *** The packaged morphism and the functor *)

Definition tsq_hom {V W : FdVectObject F} (f : V ~{FdVect F}~> W) :
  TensorSq_obj V ~{FdVect F}~> TensorSq_obj W.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F)
       (std_mod F (fdv_dim V * fdv_dim V))
       (std_mod F (fdv_dim W * fdv_dim W))
       (@Build_CMonHom (std_cmon F (fdv_dim V * fdv_dim V))
                       (std_cmon F (fdv_dim W * fdv_dim W))
          (@Build_SetoidMorphism _ _ _ _ (tsq_map f) _) _ _) _).
  - intros t u H q; exact (tsq_map_respects f t u H q).
  - intro q; exact (tsq_map_zero f q).
  - intros t u q; exact (tsq_map_plus f t u q).
  - intros r t q; exact (tsq_map_smul f r t q).
Defined.

Program Definition TensorSq : FdVect F ⟶ FdVect F := {|
  fobj := TensorSq_obj;
  fmap := fun V W f => tsq_hom f
|}.
Next Obligation.
  intros V W f g H t q.
  apply fin_sum_respects; intro p.
  apply rig_mul_respects; [ reflexivity |].
  apply rig_mul_respects; apply fentry_respects; exact H.
Qed.
Next Obligation.
  intros V t q.
  apply tsq_map_id.
Qed.
Next Obligation.
  intros V W X f g t q.
  apply tsq_map_comp.
Qed.

(** ** Scalar maps, and the arithmetic of cancelling a 2 *)

(* Multiplication by a scalar.  It is a map of F-modules only because F
   is COMMUTATIVE: [rm_map_smul] wants c·(r·v) ≈ r·(c·v), which is
   [rm_smul_assoc] twice around one [field_comm]. *)
Definition scale (c : carrier (rig_setoid F)) (V : FdVectObject F) :
  V ~{FdVect F}~> V.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (fdv_mod V) (fdv_mod V)
       (@Build_CMonHom (fdv_mod V) (fdv_mod V)
          (@Build_SetoidMorphism _ _ _ _
             (rm_smul (fdv_mod V) c) _) _ _) _).
  - intros v w Hvw; now rewrite Hvw.
  - apply rm_smul_zero_r.
  - intros v w; apply rm_smul_distr_l.
  - intros r v.
    transitivity (rm_smul (fdv_mod V) (rig_mul F c r) v).
    + symmetry; apply rm_smul_assoc.
    + transitivity (rm_smul (fdv_mod V) (rig_mul F r c) v).
      * apply rm_smul_respects; [ apply field_comm | reflexivity ].
      * apply rm_smul_assoc.
Defined.

(* The scalar the argument runs at. *)
Definition two : carrier (rig_setoid F) := rig_add F (rig_one F) (rig_one F).

Lemma two_mul (x : carrier (rig_setoid F)) :
  rig_mul F two x ≈ rig_add F x x.
Proof.
  unfold two.
  transitivity (rig_add F (rig_mul F (rig_one F) x)
                          (rig_mul F (rig_one F) x)).
  - apply rig_distr_r.
  - apply rig_add_respects; apply rig_mul_one_l.
Qed.

(* An idempotent for + is zero.  This is where the RING structure is
   spent: [ring_neg] cancels the repeated summand. *)
Lemma add_idem_zero (b : carrier (rig_setoid F)) :
  rig_add F b b ≈ b → b ≈ rig_zero F.
Proof.
  intro H.
  transitivity (rig_add F (ring_neg F b) (rig_add F b b)).
  - transitivity (rig_add F (rig_add F (ring_neg F b) b) b).
    + transitivity (rig_add F (rig_zero F) b).
      * symmetry; apply rig_add_zero_l.
      * apply rig_add_respects; [| reflexivity ].
        symmetry; apply ring_neg_l.
    + apply rig_add_assoc.
  - transitivity (rig_add F (ring_neg F b) b).
    + apply rig_add_respects; [ reflexivity | exact H ].
    + apply ring_neg_l.
Qed.

(* Cancelling the 2.  THIS is where [finv]/[finv_l] become load-bearing
   — see the header — and it is the only place in the file where the
   characteristic hypothesis is consumed. *)
Lemma double_zero (two_nz : two ≈ rig_zero F → False)
  (x : carrier (rig_setoid F)) :
  rig_mul F two x ≈ rig_zero F → x ≈ rig_zero F.
Proof.
  intro H.
  transitivity (rig_mul F (rig_one F) x).
  - symmetry; apply rig_mul_one_l.
  - transitivity (rig_mul F (rig_mul F (finv F two) two) x).
    + apply rig_mul_respects; [| reflexivity ].
      symmetry; exact (finv_l F two two_nz).
    + transitivity (rig_mul F (finv F two) (rig_mul F two x)).
      * apply rig_mul_assoc.
      * transitivity (rig_mul F (finv F two) (rig_zero F)).
        -- apply rig_mul_respects; [ reflexivity | exact H ].
        -- apply rig_mul_zero_r.
Qed.

(* The whole scaling argument, as arithmetic: 4a ≈ 2a forces a ≈ 0. *)
Lemma square_fixes_zero (two_nz : two ≈ rig_zero F → False)
  (a : carrier (rig_setoid F)) :
  rig_mul F (rig_mul F two two) a ≈ rig_mul F two a → a ≈ rig_zero F.
Proof.
  intro H.
  apply (double_zero two_nz).
  apply add_idem_zero.
  transitivity (rig_mul F two (rig_mul F two a)).
  - symmetry; apply two_mul.
  - transitivity (rig_mul F (rig_mul F two two) a).
    + symmetry; apply rig_mul_assoc.
    + exact H.
Qed.

(** ** What [TensorSq] does to a scalar map: it squares the scalar *)

Lemma fentry_scale (c : carrier (rig_setoid F)) (V : FdVectObject F)
  (i k : Fin.t (fdv_dim V)) :
  fentry (scale c V) i k ≈ rig_mul F c (delta FR k i).
Proof.
  unfold fentry.
  transitivity (rig_mul F c (fdv_coord V (bvec V i) k)).
  - apply (fdv_coord_smul V c (bvec V i) k).
  - apply rig_mul_respects; [ reflexivity |].
    unfold bvec.
    apply (fdv_coord_expand V (std_basis F (fdv_dim V) i) k).
Qed.

Lemma tsq_ker_scale (c : carrier (rig_setoid F)) (V : FdVectObject F)
  (p q : Fin.t (fdv_dim V * fdv_dim V)) :
  tsq_ker (scale c V) p q ≈ rig_mul F (rig_mul F c c) (delta FR q p).
Proof.
  unfold tsq_ker.
  transitivity (rig_mul F
    (rig_mul F c (delta FR (fst (fin_unpair q)) (fst (fin_unpair p))))
    (rig_mul F c (delta FR (snd (fin_unpair q)) (snd (fin_unpair p))))).
  - apply rig_mul_respects; apply fentry_scale.
  - etransitivity; [ apply mul_shuffle4 |].
    apply rig_mul_respects; [ reflexivity |].
    apply delta_unpair.
Qed.

(* The Kronecker square of "multiply by c" is "multiply by c²" — the
   whole computational content of Riehl's example. *)
Lemma tsq_map_scale (c : carrier (rig_setoid F)) (V : FdVectObject F)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  tsq_map (scale c V) t q ≈ rig_mul F (rig_mul F c c) (t q).
Proof.
  unfold tsq_map.
  transitivity (fin_sum FR (fun p => rig_mul F (rig_mul F c c)
    (rig_mul F (t p) (delta FR p q)))).
  - apply fin_sum_respects; intro p.
    transitivity (rig_mul F (t p)
      (rig_mul F (rig_mul F c c) (delta FR p q))).
    + apply rig_mul_respects; [ reflexivity |].
      transitivity (rig_mul F (rig_mul F c c) (delta FR q p)).
      * apply tsq_ker_scale.
      * apply rig_mul_respects; [ reflexivity | apply delta_sym ].
    + apply mul_swap_left.
  - transitivity (rig_mul F (rig_mul F c c)
      (fin_sum FR (fun p => rig_mul F (t p) (delta FR p q)))).
    + symmetry; apply fin_sum_mul_l.
    + apply rig_mul_respects; [ reflexivity |].
      apply (fin_sum_delta_r FR q t).
Qed.

(** ** The zero transformation, and Riehl's Example 1.4.4(vii) *)

(* The zero morphism V → V ⊗ V, written out so that the theorem below
   can say "the component IS this" rather than "every value is zero". *)
Definition tsq_zero (V : FdVectObject F) :
  V ~{FdVect F}~> TensorSq_obj V.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (fdv_mod V)
       (std_mod F (fdv_dim V * fdv_dim V))
       (@Build_CMonHom (fdv_mod V)
                       (std_cmon F (fdv_dim V * fdv_dim V))
          (@Build_SetoidMorphism _ _ _ _
             (fun _ (_ : Fin.t (fdv_dim V * fdv_dim V)) =>
                rig_zero F) _) _ _) _).
  - intros v w Hvw q; reflexivity.
  - intro q; reflexivity.
  - intros v w q; symmetry; apply rig_add_zero_l.
  - intros r v q; symmetry; apply rig_mul_zero_r.
Defined.

(* The zero family IS natural, so the theorem below classifies a
   NONEMPTY collection: it says the zero transformation is the only
   one, not that there are none. *)
Program Definition tsq_zero_transform : Id[FdVect F] ⟹ TensorSq := {|
  transform := fun V => tsq_zero V
|}.
Next Obligation.
  intros V W f v q.
  apply tsq_map_zero.
Qed.
Next Obligation.
  intros V W f v q.
  symmetry; apply tsq_map_zero.
Qed.

(** Riehl, "Category Theory in Context", §1.4 Example 1.4.4(vii),
    printed p. 26.  Every natural transformation from the identity
    functor to the diagonal square functor is zero.

    The proof is one naturality square, at the scalar map [scale two V]
    — an endomorphism of the very object in question, so no probe
    object and no dimension-one special case is needed.  Going around
    it one way squares the scalar ([tsq_map_scale]); going around it
    the other way merely reproduces it ([rm_map_smul], the component
    being linear).  So 4a ≈ 2a, and [square_fixes_zero] finishes.

    The hypothesis [two_nz] is the characteristic condition 1 + 1 ≉ 0,
    carried explicitly; in characteristic two the equation 4a ≈ 2a is
    an identity and the conclusion is unavailable. *)
Theorem diag_transform_zero (two_nz : two ≈ rig_zero F → False)
  (alpha : Id[FdVect F] ⟹ TensorSq) (V : FdVectObject F) :
  transform alpha V ≈ tsq_zero V.
Proof.
  intros v q.
  apply (square_fixes_zero two_nz).
  transitivity (tsq_map (scale two V)
    (cmon_map (rm_hom (transform alpha V)) v) q).
  - symmetry; apply tsq_map_scale.
  - transitivity (cmon_map (rm_hom (transform alpha V))
      (rm_smul (fdv_mod V) two v) q).
    + exact (naturality alpha V V (scale two V) v q).
    + exact (rm_map_smul (transform alpha V) two v q).
Qed.

(* The same statement read coordinatewise. *)
Corollary diag_transform_zero_coord
  (two_nz : two ≈ rig_zero F → False)
  (alpha : Id[FdVect F] ⟹ TensorSq) (V : FdVectObject F)
  (v : carrier (cmon_setoid (fdv_mod V)))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  cmon_map (rm_hom (transform alpha V)) v q ≈ rig_zero F.
Proof.
  exact (diag_transform_zero two_nz alpha V v q).
Qed.

End Tensor.

(** ** The characteristic hypothesis, discharged over ℚ

    1 + 1 is 2 # 1 and 0 is 0 # 1, so [Qeq] reduces to 2 = 0 in ℤ; this
    is Instance/FdVect.v's [field_one_neq_zero] obligation for
    [Q_Field] one step further along. *)
Lemma Q_two_nz : two Q_Field ≈ rig_zero Q_Field → False.
Proof.
  unfold two; simpl; unfold Qeq; simpl; discriminate.
Qed.

(** Riehl's example over ℚ: no nonzero natural transformation from the
    identity functor on finite-dimensional ℚ-vector spaces to the
    diagonal square functor. *)
Corollary diag_transform_zero_Q
  (alpha : Id[FdVect Q_Field] ⟹ TensorSq Q_Field)
  (V : FdVectObject Q_Field) :
  transform alpha V ≈ tsq_zero Q_Field V.
Proof.
  exact (diag_transform_zero Q_Field Q_two_nz alpha V).
Qed.

(** ** Acceptance tests *)

(* The object realization: the square of a two-dimensional space is
   four-dimensional, on the nose. *)
Example tensor_dim_two :
  fdv_dim (TensorSq_obj Q_Field (StdVect Q_Field 2)) = 4%nat := eq_refl.

(* The codec's orientation, anchored by computation rather than by
   prose: position (1, 0) of a 2 × 2 index set is position 2, and it
   decodes back. *)
Example fin_pair_anchor :
  @fin_pair 2 2 (Fin.FS Fin.F1) Fin.F1 = Fin.FS (Fin.FS (@Fin.F1 1))
  := eq_refl.

Example fin_unpair_anchor :
  @fin_unpair 2 2 (Fin.FS (Fin.FS (@Fin.F1 1))) = (Fin.FS Fin.F1, Fin.F1)
  := eq_refl.

(* The functor fixes every vector of the square at the identity. *)
Example tsq_id_fixes (V : FdVectObject Q_Field)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid Q_Field))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  cmon_map (rm_hom (fmap[TensorSq Q_Field] (@id (FdVect Q_Field) V))) t q
    ≈ t q.
Proof. apply tsq_map_id. Qed.

(* The zero morphism really is zero, at open arguments. *)
Example tsq_zero_value (V : FdVectObject Q_Field)
  (v : carrier (cmon_setoid (fdv_mod V)))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  cmon_map (rm_hom (tsq_zero Q_Field V)) v q = rig_zero Q_Field := eq_refl.

(* A table entry of a map given independently of any matrix: the
   coordinate swap of ℚ² sends the first basis vector to the second,
   so its (0, 1) entry is 1. *)
Example fentry_swap_01 :
  fentry Q_Field (std_reindex Q_Field fin2_swap) Fin.F1 (Fin.FS Fin.F1)
    = 1%Q := eq_refl.

Example fentry_swap_00 :
  fentry Q_Field (std_reindex Q_Field fin2_swap) Fin.F1 Fin.F1
    = 0%Q := eq_refl.

(* ... and the Kronecker square of that map really permutes the four
   coordinates, so [TensorSq] is not secretly constant on morphisms.
   The 2 × 2 table below is read off the codec: position (i, j) of the
   square carries entry (i, j), and the square of the swap sends
   position (i, j) to position (swap i, swap j). *)
Definition qt4 : Fin.t (2 * 2) → carrier (rig_setoid Q_Field) :=
  fun p => fin2 (fin2 (5 # 1)%Q (6 # 1)%Q)
                (fin2 (7 # 1)%Q (8 # 1)%Q)
             (fst (fin_unpair p)) (snd (fin_unpair p)).

(* Position 0 is (0, 0); its image pulls back from (1, 1), entry 8. *)
Example tsq_swap_00 :
  tsq_map Q_Field (std_reindex Q_Field fin2_swap) qt4 Fin.F1
    = (8 # 1)%Q := eq_refl.

(* Position 1 is (0, 1); its image pulls back from (1, 0), entry 7. *)
Example tsq_swap_01 :
  tsq_map Q_Field (std_reindex Q_Field fin2_swap) qt4 (Fin.FS Fin.F1)
    = (7 # 1)%Q := eq_refl.
