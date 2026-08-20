(* [Coq.QArith.QArith] MUST precede [Category.Lib]: it exports an [equiv]
   that otherwise shadows Lib/Setoid.v's, and every [Proper] statement
   reachable from here then fails to elaborate.  This is the import-order
   gotcha Instance/FdVect.v records in its own header and
   Instance/Matr/Elimination.v measured again; the ℚ witness at the end
   of this file is why the ordering matters here too. *)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Matr.Elimination.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * Coequalizers of matrices

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.3
    Exercise 3 [maclane:III.3:ex3] asks for the coequalizer of a parallel
    pair of matrices.  This file is the CATEGORICAL half of that
    exercise.  The linear-algebra half is Instance/Matr/Elimination.v,
    which is CONSUMED here and neither extended nor re-proved: every
    proof below is one of that file's terms handed to a record field of
    Structure/Coequalizer.v, and this file contains no summation
    argument, no pivot, and no induction of its own.

    WHAT A COEQUALIZER OF MATRICES IS.  For a parallel pair A, B : n ⇉ m
    — two m × n matrices — a map h : m ~> z coforks the pair exactly when
    h·A ≈ h·B, which by Elimination.v's [mat_mul_sub_zero_iff] holds
    exactly when h·(A − B) ≈ 0, that is, exactly when every row of h lies
    in the LEFT NULL SPACE of A − B.  So a universal coforking map is a
    matrix E whose rows are a BASIS of that space: spanning is existence
    of the factorization, linear independence is its uniqueness.  The
    coequalizer OBJECT is then the number of rows of E, the dimension of
    that null space.  NO RANK FUNCTION IS DEFINED, neither here nor in
    Elimination.v, so the familiar reading "k = m − rank (A − B)" is
    neither stated nor proved anywhere in this development; it appears in
    this sentence and nowhere else.

    ORIENTATION.  Inherited verbatim from Instance/Matr.v, which follows
    Mac Lane: an arrow n ~> m of [Matr R] is an m × n matrix, and
    composition is the matrix product with no transposition.  Taking
    x := n, y := m, f := A and g := B, the record of
    Structure/Coequalizer.v asks for an object q := k and a map
    e : y ~> q, which is a k × m matrix E; its [cofork] field
    [e ∘ f ≈ e ∘ g] IS E·A ≈ E·B; a coforking h : y ~> z is a z × m
    matrix; and the mediator u : q ~> z is a z × k matrix whose triangle
    [u ∘ e ≈ h] reads u·E ≈ h.  Those are exactly the four shapes
    Elimination.v's [left_null_basis] produces.

    THE HANDOFF IS PURE CONVERSION, and that was MEASURED rather than
    assumed.  Every statement below is written in the category's own
    vocabulary — [∘] and [≈[Matr K]] — while every proof of a GENERAL
    result, that is every one of the twelve constants of the section
    below, is an Elimination.v term supplied by [:=] with NO tactic.
    (The file does contain eleven tactic scripts, all of them in the two
    witness blocks at the end, where concrete matrices are discriminated;
    the section itself has none.)  There is NO [change] and NO transport
    anywhere in the file, in either part.  What makes this work is that
    Elimination.v identified its own vocabulary with the category's by
    [eq_refl] ([matrix_is_hom]; [mat_mul_is_compose], whose object
    arguments run in the order (c, b, a); [mat_id_is_id]; and
    [mat_equiv_is_homset_equiv], the last recording that its [Setoid]
    instance on matrices IS [Matr K]'s hom-setoid rather than the
    pointwise one [fun_setoid] would otherwise supply).  That instance is
    [#[local]] to Elimination.v, so it is not in scope here — and it is
    not needed, because this file names no bare [≈] on matrices at all.

    THE DECIDABILITY HYPOTHESIS, AND WHY IT IS FORCED.  The hypothesis
    [Kdec] below is not a convenience.  Producing the coequalizing map
    means running elimination, and elimination has to DECIDE whether a
    pivot vanishes, while the class it runs over supplies no such
    decision: [FieldObject] (Instance/FdVect.v) carries [field_ring],
    [field_comm], [field_one_neq_zero], a TOTAL [finv], [finv_respects]
    and [finv_l] — and [finv_l] is GUARDED by [x ≉ 0], so the inverse law
    is unusable until non-vanishing has been established, which is the
    very thing at issue.  Over an abstract setoid carrier [≈] is not
    decidable and the value of [finv] at zero is junk.  The hypothesis is
    therefore carried as explicit DATA in exactly the shape
    Instance/Field.v's [field_dec_stable] takes, and Elimination.v's
    [F2_dec_inhabits] and [Q_dec_inhabits] record BY ASCRIPTION that
    [F2_Field_dec] and [Q_Field_dec] inhabit it, so it is the tree's own
    notion and not a new one.  THE CONSEQUENCE FOR THIS FILE is that
    [Matr_HasCoequalizers] is a plain [Definition] taking the decider as
    an argument and is deliberately NOT registered as a global
    [Instance]: typeclass resolution has no way to produce a decider for
    an abstract field, and registering a hint that can never fire would
    perturb the database for nothing.  A consumer writes
    [Matr_HasCoequalizers K Kdec] and supplies the decider by hand.

    THE RIG CONSTRAINT.  Instance/Matr.v is stated over a RIG, and
    deliberately so: the category laws need associativity, units,
    distributivity and annihilation, and never subtraction.  A
    coequalizer does need subtraction — the passage from the two-matrix
    problem h·A ≈ h·B to the one-matrix problem h·(A − B) ≈ 0 is the
    whole bridge, and it spends [ring_neg]; the pivot step spends [finv]
    on top of that.  The base of this file is therefore a FIELD, and
    NOTHING here says anything about [Matr R] for a bare rig R.  In
    particular nothing is claimed about Awodey's
    [Matr_N := Matr Nat_Rig] (Instance/Matr.v), where A − B does not
    exist: whether that category has coequalizers is a different
    question, and it is not addressed.

    MEASURED STRENGTHS, strict first.  [eq_refl] was attempted before any
    [≈] was accepted, and the artifacts were arranged so that the strict
    form would be available at all: [matr_coeq_obj], [matr_coeq_map] and
    [matr_coeq_desc] are supplied by [:=] rather than by a tactic script
    closed with [Qed], so the object, the map and the [coeq_desc] field
    of the delivered record all REDUCE.  Closing by [eq_refl] at
    [F2_Field]: the coequalizer object of the worked pair (1) and both
    entries of its coequalizing map; the common composite E·A; the
    MEDIATOR extracted from the [coeq_desc] field of the delivered
    record — that last is the one that would have been lost had
    [matr_coeq_desc] been a [Qed] lemma; and the objects of three
    further pairs, pinning k = m at a pair with itself (where the map is
    2 x 2, so it has FOUR entries; two of them are pinned here and all
    four are the identity matrix's -- an earlier draft said "both",
    which is right for the 1 x 2 map of the worked pair and wrong here),
    k = 0 at an invertible difference, and a second non-degenerate
    k = 2 at m = 3.  At [Q_Field] the object, both entries −2 and 1 of
    the coequalizing map, and both sides of the cofork equation (each
    −1) close by [eq_refl] as well, the rational arithmetic reducing on
    closed input.  Also strict: [matr_IsEqualizer_op] IS
    Structure/Pullback/Reduction.v's [IsEqualizer_op_of_IsCoequalizer]
    applied to the record, so that bridge is definitional at this
    instantiation and not merely available.

    FIVE STRICT ATTEMPTS WERE MADE AND REFUTED.  Each was checked by
    removing the failure marker and confirming a genuine CONVERSION
    failure (each reported "cannot unify"), and each is paired with a
    positive control that succeeds at the same arguments; none is a
    universe or elaboration artifact.  They are recorded here rather
    than as probes, this file carrying no probe section.
      (i) [matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A
    = mat_id F2_Field 2] — at a pair with itself the difference vanishes
    and every row vector is in the null space, but the recursion still
    passes through one [lnb_step] per column, so at this pair (which has
    one column) the basis produced is [mat_mul (mat_id 2) (mat_id 2)] and
    not [mat_id 2].  The control is that both of its entries do close by
    [eq_refl], below.  Nothing is claimed about the general shape of the
    residue at more columns; only this instance was measured.
      (ii) [coeq_f2_map = coeq_f2_h] — the coequalizing map of the
    worked F₂ pair and the coforking row vector (1, 1) are refuted equal
    at whole-function Leibniz equality, although the control
    [coeq_f2_map Fin.F1 Fin.F1 = coeq_f2_h Fin.F1 Fin.F1] closes by
    [eq_refl], so the negative is about the two TERMS and not their
    values.
      (iii) the same map against the literal [fun _ _ => true] — refuted
    for the same reason as (ii): entries reduce at CLOSED indices, while
    under binders the Kronecker [delta] is stuck on a free index, so the
    matrix does not reduce to a constant function.
      (iv) [IsCoequalizer A B q e = @IsEqualizer ((Matr K)^op) m n A B q
    e] at the concrete F₂ instance — refuted, which confirms at a
    concrete category what Structure/Pullback/Reduction.v measured
    abstractly (its negatives 6 and 7): the two are separately declared
    records and Coq's record types are nominal, so no agreement between
    their fields makes them one type.  Every FIELD type is convertible,
    which is why the bridges below are [:=] with no tactic.
      (v) [matr_coeq_obj F2_Field F2_Field_dec coeq_f2_A coeq_f2_B
    = 1%nat] — refuted with the TREE's decider in place of the
    transparent copy, which confirms that Elimination.v's opacity
    measurement propagates to this file's constants unchanged; the
    control is the same statement with [f2_dec], which closes.
    One further observation, not an attempt: the [cofork] field has no
    reduction behaviour at all, being built from Elimination.v's [Qed]
    theorem [mat_mul_sub_zero_iff].  That costs nothing — a proof of an
    [≈] carries no data this file wants — and it is worth recording only
    because the neighbouring [coeq_desc] field DOES reduce, so the two
    fields of one record differ in this respect.

    THE DECIDERS.  Elimination.v measured that Instance/Field.v's
    [F2_Field_dec] (:534) and [Q_Field_dec] (:410) are [Qed] LEMMAS, so
    no application of either reduces and the elimination engine computes
    with neither.  Every [eq_refl] witness below therefore runs on that
    file's transparent copies [f2_dec] and [q_dec], which decide the same
    relations by the same case analyses and differ only in ending with
    [Defined].  The opacity is Instance/Field.v's, is NOT repaired here,
    and nothing above depends on it being repaired: the construction is
    correct with either decider, and only the [eq_refl] checks need the
    transparent one — which is exactly what refuted attempt (v) records.

    NOT DELIVERED BY THIS FILE.  No equalizers in [Matr K]: that needs
    the RIGHT null space, which Elimination.v explicitly does not build,
    and transporting the left-handed answer along Instance/Matr.v's
    [Matr_transpose_iso] is real work that is not attempted — what IS
    delivered is [HasEqualizers ((Matr K)^op)], which is the coequalizer
    statement reread through a duality bridge and not a new theorem.  No
    claim that the coequalizer object is m − rank (A − B), there being no
    rank function.  No claim that the object is independent of the
    construction AS A NUMBER: [matr_coeq_iso] gives only that any two
    coequalizers of one pair have isomorphic OBJECTS of [Matr K], and
    concluding from k ≅ k' that k = k' would need exactly the dimension
    argument this development lacks.  No pushouts, no cokernels, no
    [Cocomplete] or [Cocartesian] statement about [Matr K], and no
    reflexive- or split-coequalizer reading.  No statement about [Matr R]
    over a bare rig, per the paragraph above.  No normal form for E: the
    coequalizing map produced is whichever basis the elimination engine
    returns, so two pairs with the same difference up to [≈] are not
    shown to receive the same matrix on the nose — refuted attempts (i)
    to (iii) are three faces of that same limitation.

    THE ASSUMPTION FOOTPRINT is nil and was measured per constant rather
    than sampled: all 58 named constants of this file — the twelve of the
    section plus the 46 of the two witness blocks — report "Closed under
    the global context".  The file uses no [Program] and declares no
    [Instance], so it generates no obligations and the enumeration from
    its own declarations is the complete one; this is the [Print Module]
    caveat docs/AXIOMS.md records, and it does not arise here. *)

Section MatrCoequalizer.

(** ** The base: a field with a zero test

    [Kdec] has the type Instance/Field.v's [field_dec_stable] takes; see
    the header for why nothing weaker will do. *)

Context (K : FieldObject).
Context (Kdec : ∀ a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b → False)).

(** ** The construction

    A basis of the left null space of the difference.  Everything else in
    this section reads that one record through the category's
    vocabulary. *)

Definition matr_lnb {m n : nat} (A B : n ~{Matr K}~> m) :
  LeftNullBasis K (mat_sub K A B) :=
  left_null_basis K Kdec (mat_sub K A B).

(* The coequalizer object: the dimension of the left null space of
   A − B.  Typed as an object of [Matr K], which is [nat]. *)
Definition matr_coeq_obj {m n : nat} (A B : n ~{Matr K}~> m) : Matr K :=
  lnb_dim (matr_lnb A B).

(* The coequalizing map: a basis matrix with k rows and m columns, which
   is what an arrow [m ~> k] of [Matr K] is. *)
Definition matr_coeq_map {m n : nat} (A B : n ~{Matr K}~> m) :
  m ~{Matr K}~> matr_coeq_obj A B :=
  lnb_basis (matr_lnb A B).

(** ** The two clauses

    Both are Elimination.v terms supplied by [:=].  The cofork is
    annihilation of the basis read through [mat_mul_sub_zero_iff]; the
    descent is the basis's own universal clause read through the same
    equivalence in the other direction. *)

Definition matr_coeq_cofork {m n : nat} (A B : n ~{Matr K}~> m) :
  matr_coeq_map A B ∘ A ≈[Matr K] matr_coeq_map A B ∘ B :=
  fst (mat_mul_sub_zero_iff K Kdec (matr_coeq_map A B) A B)
    (lnb_annih (matr_lnb A B)).

(* Kept a transparent [Definition] on purpose: this is the field whose
   reduction the computing witnesses at the end of the file use. *)
Definition matr_coeq_desc {m n : nat} (A B : n ~{Matr K}~> m)
  (z : Matr K) (h : m ~{Matr K}~> z) (Hh : h ∘ A ≈[Matr K] h ∘ B) :
  ∃! u : matr_coeq_obj A B ~{Matr K}~> z,
    u ∘ matr_coeq_map A B ≈[Matr K] h :=
  lnb_univ (matr_lnb A B) z h
    (snd (mat_mul_sub_zero_iff K Kdec h A B) Hh).

(** ** Mac Lane §III.3 Exercise 3

    The elementary coequalizer of an arbitrary parallel pair, and then
    the class quantifying over every parallel pair. *)

Definition matr_IsCoequalizer {m n : nat} (A B : n ~{Matr K}~> m) :
  IsCoequalizer A B (matr_coeq_obj A B) (matr_coeq_map A B) :=
  {| cofork    := matr_coeq_cofork A B
   ; coeq_desc := fun z h Hh => matr_coeq_desc A B z h Hh |}.

(* Deliberately a [Definition] and not an [Instance]; see the header. *)
Definition Matr_HasCoequalizers : HasCoequalizers (Matr K) :=
  {| coeq := fun x y f g =>
       existT _ (matr_coeq_obj f g)
         (existT _ (matr_coeq_map f g) (matr_IsCoequalizer f g)) |}.

(** ** What the generic API then gives

    Nothing here is new content: each is an instantiation of a result of
    Structure/Coequalizer.v at the coequalizer just built. *)

(* A coequalizing map is an epimorphism ([coequalizer_epic]).  So every
   basis matrix the elimination engine returns is epic in [Matr K] — a
   fact about matrices reached with no matrix proof. *)
Definition matr_coeq_epic {m n : nat} (A B : n ~{Matr K}~> m) :
  Epic (matr_coeq_map A B) :=
  coequalizer_epic A B (matr_IsCoequalizer A B).

(* Any other coequalizer of the same pair has an isomorphic object.
   Read the strength: this is an isomorphism in [Matr K], a pair of
   mutually inverse matrices, and it does NOT say the two dimensions are
   equal — see the header's not-delivered list. *)
Definition matr_coeq_iso {m n : nat} (A B : n ~{Matr K}~> m)
  {q : Matr K} {e : m ~{Matr K}~> q} (E : IsCoequalizer A B q e) :
  q ≅ matr_coeq_obj A B :=
  coequalizer_unique A B E (matr_IsCoequalizer A B).

(* The colimit packaging: the same data as a colimit over the walking
   parallel pair ([is_coequalizer_colimit]). *)
Definition matr_coeq_colimit {m n : nat} (A B : n ~{Matr K}~> m) :
  Coequalizer (APair A B) :=
  is_coequalizer_colimit A B (matr_IsCoequalizer A B).

(** ** The dual reading

    Structure/Pullback/Reduction.v's bridges, instantiated.  Both are
    [:=] with no tactic HERE.  Do not read that back into Reduction.v:
    there, only [IsEqualizer_op_of_IsCoequalizer] is a [:=];
    [HasEqualizers_op_of_HasCoequalizers] is a tactic script.  An
    earlier draft said "as they are there", which inverts that.  See
    refuted attempt (iv) for
    what is NOT true of them. *)

Definition matr_IsEqualizer_op {m n : nat} (A B : n ~{Matr K}~> m) :
  @IsEqualizer ((Matr K)^op) m n A B
    (matr_coeq_obj A B) (matr_coeq_map A B) :=
  IsEqualizer_op_of_IsCoequalizer (matr_IsCoequalizer A B).

Definition Matr_op_HasEqualizers : @HasEqualizers ((Matr K)^op) :=
  HasEqualizers_op_of_HasCoequalizers Matr_HasCoequalizers.

End MatrCoequalizer.

(** ** A worked coequalizer over F₂

    [F2_Field] (Instance/Field.v) is the cheapest base at which every
    step computes: the carrier is [bool] with Leibniz equality, addition
    is [xorb], multiplication is [andb], and negation is the identity, so
    the difference of two matrices is their entrywise exclusive or.  The
    decider used throughout is Elimination.v's transparent [f2_dec] and
    NOT Instance/Field.v's [F2_Field_dec], which is a [Qed] lemma through
    which nothing reduces; see the header, and refuted attempt (v) for
    the measurement.

    The pair is A, B : 1 ⇉ 2, that is, two columns of height 2:
    A = (1, 0)ᵀ and B = (0, 1)ᵀ.  Their difference is (1, 1)ᵀ, whose left
    null space is the line spanned by (1, 1), so the coequalizer object
    is 1 — NEITHER 0 NOR m = 2, which is what makes the example
    non-degenerate, and which is proved below rather than asserted. *)

Definition coeq_f2_A : 1%nat ~{Matr F2_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => true | _ => false end.

Definition coeq_f2_B : 1%nat ~{Matr F2_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => false | _ => true end.

Definition coeq_f2_obj : Matr F2_Field :=
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_B.

Definition coeq_f2_map : 2%nat ~{Matr F2_Field}~> coeq_f2_obj :=
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_B.

Definition coeq_f2 :
  IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map :=
  matr_IsCoequalizer F2_Field f2_dec coeq_f2_A coeq_f2_B.

(* The object and both entries of the coequalizing map, COMPUTED. *)
Example coeq_f2_obj_computes : coeq_f2_obj = 1%nat := eq_refl.

Example coeq_f2_map_0 : coeq_f2_map Fin.F1 Fin.F1 = true := eq_refl.

Example coeq_f2_map_1 :
  coeq_f2_map Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(* The common composite E·A is the 1 × 1 matrix (1): the coequalizer
   does not collapse everything in sight. *)
Example coeq_f2_composite :
  (coeq_f2_map ∘ coeq_f2_A) Fin.F1 Fin.F1 = true := eq_refl.

(** *** Non-degeneracy, proved

    Three separate facts.  First, the object is neither of the two
    degenerate answers.  Second, the pair really is a pair: A and B are
    not equivalent arrows, so this is not a coequalizer of something with
    itself.  Third — the categorical form of the same point — the
    coequalizing map is NOT monic, since it identifies those two
    inequivalent arrows, while it IS epic by [matr_coeq_epic]; so it is a
    proper quotient and not an isomorphism in disguise. *)

Lemma coeq_f2_obj_not_zero : coeq_f2_obj ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_f2_obj_not_two : coeq_f2_obj ≠ 2%nat.
Proof. discriminate. Qed.

Lemma coeq_f2_pair_distinct :
  coeq_f2_A ≈[Matr F2_Field] coeq_f2_B → False.
Proof.
  intro H.
  specialize (H Fin.F1 Fin.F1).
  discriminate H.
Qed.

Lemma coeq_f2_map_not_monic : Monic coeq_f2_map → False.
Proof.
  intros [HM].
  apply coeq_f2_pair_distinct.
  exact (HM 1%nat coeq_f2_A coeq_f2_B (cofork coeq_f2)).
Qed.

Definition coeq_f2_map_epic : Epic coeq_f2_map :=
  matr_coeq_epic F2_Field f2_dec coeq_f2_A coeq_f2_B.

(** *** The mediator computes

    The universal clause is not vacuous, and the factorization it
    produces reduces.  The row vector h = (1, 1) coforks the pair —
    h·A = 1 = h·B — so it factors through E, and the mediator the
    construction returns is the 1 × 1 matrix (1).  This is the check that
    would have been lost had [matr_coeq_desc] been closed with [Qed]. *)

Definition coeq_f2_h : 2%nat ~{Matr F2_Field}~> 1%nat := fun _ _ => true.

Lemma coeq_f2_h_coforks :
  coeq_f2_h ∘ coeq_f2_A ≈[Matr F2_Field] coeq_f2_h ∘ coeq_f2_B.
Proof. intros i j; reflexivity. Qed.

(* Stated with the type left inferred, purely for brevity.

   AN EARLIER DRAFT JUSTIFIED THIS BY SAYING THAT WRITING THE [∃!] OUT
   AGAIN WOULD ELABORATE [coeq_f2] AT FRESH UNIVERSES THAT WOULD NOT
   UNIFY, CITING A MEASUREMENT ELIMINATION.V RECORDS AT ITS OWN
   [f2_mediator].  THAT MEASUREMENT IS GENUINE THERE AND DOES NOT HOLD
   HERE: an audit wrote the type out in two spellings at THIS site and
   both are accepted, the mediator still computing.  The claim was
   transferred to a site where it is false, and is recorded as bad
   evidence rather than deleted. *)
Definition coeq_f2_mediator :=
  coeq_desc coeq_f2 coeq_f2_h coeq_f2_h_coforks.

Example coeq_f2_mediator_computes :
  unique_obj coeq_f2_mediator Fin.F1 Fin.F1 = true := eq_refl.

(* The positive control for refuted attempt (ii): the coequalizing map
   and this row vector agree ENTRYWISE by [eq_refl], so the refutation of
   [coeq_f2_map = coeq_f2_h] is about the two terms and not their
   values. *)
Example coeq_f2_map_h_agree_at :
  coeq_f2_map Fin.F1 Fin.F1 = coeq_f2_h Fin.F1 Fin.F1 := eq_refl.

(* The positive control for refuted attempt (iv): the duality bridge is
   definitional at this instantiation, even though the two record TYPES
   are not identified. *)
Example coeq_f2_op_is_bridge :
  matr_IsEqualizer_op F2_Field f2_dec coeq_f2_A coeq_f2_B
  = IsEqualizer_op_of_IsCoequalizer coeq_f2 := eq_refl.

(** *** The object responds to the pair

    Three more pairs, pinning the two degenerate answers and one further
    non-degenerate one, so that the dimension is visibly a function of
    the difference and not a constant.

    (i) A pair with itself: the difference vanishes, every row vector is
    in the left null space, and the coequalizing map computes to the
    entries of the identity matrix on m = 2 — the degenerate case,
    computed rather than assumed.  It is NOT the term [mat_id F2_Field 2]
    on the nose; see refuted attempt (i). *)

Example coeq_f2_self_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_A = 2%nat := eq_refl.

Example coeq_f2_self_map_diag :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A Fin.F1 Fin.F1 = true
  := eq_refl.

Example coeq_f2_self_map_off :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A
    Fin.F1 (Fin.FS Fin.F1) = false := eq_refl.

(* (ii) A difference that is invertible: the left null space is zero, so
   the coequalizer object is 0 and the coequalizing map has no rows. *)

Definition coeq_f2_I : 2%nat ~{Matr F2_Field}~> 2%nat :=
  fun i j => delta F2_Field i j.

Definition coeq_f2_O : 2%nat ~{Matr F2_Field}~> 2%nat := fun _ _ => false.

Example coeq_f2_iden_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f2_I coeq_f2_O = 0%nat := eq_refl.

(* (iii) Height 3, difference (1, 1, 0)ᵀ: the left null space is the
   plane {(a, b, c) : a + b = 0}, of dimension 2 — again neither 0 nor
   m = 3. *)

Definition coeq_f3_A : 1%nat ~{Matr F2_Field}~> 3%nat :=
  fun i _ => match i with
             | Fin.F1 => true
             | Fin.FS Fin.F1 => true
             | _ => false
             end.

Definition coeq_f3_B : 1%nat ~{Matr F2_Field}~> 3%nat := fun _ _ => false.

Example coeq_f3_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B = 2%nat := eq_refl.

Lemma coeq_f3_obj_not_zero :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_f3_obj_not_three :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B ≠ 3%nat.
Proof. discriminate. Qed.

(** ** A worked coequalizer over ℚ

    [Q_Field] with Elimination.v's transparent [q_dec] is a base in which
    the pivot DIVISION does something: the pair A = (3, 5)ᵀ,
    B = (2, 3)ᵀ has difference (1, 2)ᵀ, whose left null space is spanned
    by (−2, 1), and the coefficient −2 is produced by [finv] rather than
    by a case analysis.  Both sides of the cofork equation compute to the
    1 × 1 matrix (−1) — equal, as they must be, and NONZERO, so this is
    not the example in which everything is killed. *)

Definition coeq_q_A : 1%nat ~{Matr Q_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => 3%Q | _ => 5%Q end.

Definition coeq_q_B : 1%nat ~{Matr Q_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => 2%Q | _ => 3%Q end.

Definition coeq_q_obj : Matr Q_Field :=
  matr_coeq_obj Q_Field q_dec coeq_q_A coeq_q_B.

Definition coeq_q_map : 2%nat ~{Matr Q_Field}~> coeq_q_obj :=
  matr_coeq_map Q_Field q_dec coeq_q_A coeq_q_B.

Definition coeq_q :
  IsCoequalizer coeq_q_A coeq_q_B coeq_q_obj coeq_q_map :=
  matr_IsCoequalizer Q_Field q_dec coeq_q_A coeq_q_B.

Example coeq_q_obj_computes : coeq_q_obj = 1%nat := eq_refl.

Example coeq_q_map_0 : coeq_q_map Fin.F1 Fin.F1 = (-2 # 1)%Q := eq_refl.

Example coeq_q_map_1 :
  coeq_q_map Fin.F1 (Fin.FS Fin.F1) = (1 # 1)%Q := eq_refl.

(* Both legs of the cofork, computed on closed rational input. *)
Example coeq_q_left :
  (coeq_q_map ∘ coeq_q_A) Fin.F1 Fin.F1 = (-1 # 1)%Q := eq_refl.

Example coeq_q_right :
  (coeq_q_map ∘ coeq_q_B) Fin.F1 Fin.F1 = (-1 # 1)%Q := eq_refl.

Lemma coeq_q_obj_not_zero : coeq_q_obj ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_q_obj_not_two : coeq_q_obj ≠ 2%nat.
Proof. discriminate. Qed.

Lemma coeq_q_pair_distinct :
  coeq_q_A ≈[Matr Q_Field] coeq_q_B → False.
Proof.
  intro H.
  specialize (H Fin.F1 Fin.F1).
  discriminate H.
Qed.

Lemma coeq_q_map_not_monic : Monic coeq_q_map → False.
Proof.
  intros [HM].
  apply coeq_q_pair_distinct.
  exact (HM 1%nat coeq_q_A coeq_q_B (cofork coeq_q)).
Qed.

Definition coeq_q_map_epic : Epic coeq_q_map :=
  matr_coeq_epic Q_Field q_dec coeq_q_A coeq_q_B.
