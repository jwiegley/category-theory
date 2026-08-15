(** * FdVect: finite-dimensional vector spaces, and the matrix equivalence

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.4
    Exercise 6: the category of finite-dimensional vector spaces over a
    field K is equivalent — not isomorphic — to the matrix category
    [Matr_K] [maclane:I.4:ex6].  Riehl, "Category Theory in Context",
    §1.5 Example 1.5.12: the same statement, presented as the motivating
    illustration of why equivalence, and not isomorphism, is the right
    notion of sameness for categories [riehl:1.5:example12].  (The
    locations follow the convention of issue
    jwiegley/category-theory#256, and as in Instance/Mod.v the printed
    text was not consulted while writing this file, so no page numbers
    are claimed.)  Riehl's route is the one taken here: the comparison
    functor sending n to the standard space K^n is full, faithful and
    essentially surjective, hence an equivalence by
    Theory/Equivalence/FullFaithful.v's [FF_ESO_Equivalence].

    It is not an ISOMORPHISM of categories: [Matr] has exactly one object
    per natural number, while [FdVect F] has one for every
    module-with-coordinates of that dimension.  That is an observation
    about the two collections of objects and is not proved below; what is
    proved is the equivalence, which says the multiplicity carries no
    categorical information.

    WHY THE PROOF IS THE POINT.  "Every finite-dimensional vector space
    is isomorphic to K^n for n its dimension" is the linear algebra
    behind essential surjectivity; "every linear map K^n → K^m is
    multiplication by a unique m × n matrix" is fullness and
    faithfulness.  Riehl's discussion turns on the observation that
    choosing the isomorphism V ≅ K^n is choosing a BASIS, and that no
    natural such choice exists — which is why the quasi-inverse is not
    canonical and the two categories are merely equivalent.  This is
    Makkai's and Ahrens–Kapulkin–Shulman's setting for the axiom of
    choice in category theory (see Theory/Equivalence.v's essay); here no
    choice principle is spent, for the reason recorded next.

    THE BASIS IS DATA, NOT A THEOREM — the file's one design decision,
    disclosed here in full.  Classically every vector space has a basis,
    by Zorn's lemma; even for a space known to be spanned by finitely
    many vectors, thinning a spanning set to a basis needs decidable
    linear dependence.  Neither is assumed here.  An object of [FdVect F]
    is not a module carrying a PROPERTY; it is a module together with a
    CHOSEN coordinate isomorphism to F^n — the fields [fdv_coord] and
    [fdv_expand], their two round trips, and the linearity of
    [fdv_coord].  Since the library's existential quantifier is
    Type-valued ([sigT]), naming the witness as a field rather than
    hiding it behind an ∃ is not a weakening: it is the same data, and it
    keeps every construction below computational.  A basis IS a linear
    isomorphism V ≅ F^n, so nothing is lost mathematically, and
    [FdVect_Matr_Equivalence] checks Closed under the global context —
    no choice, no excluded middle, no funext.  (Linearity of
    [fdv_expand] is NOT a field: it is derivable from the linearity of
    [fdv_coord] and the round trips, and is derived below as
    [fdv_expand_plus], [fdv_expand_smul] and [fdv_expand_zero].)

    This makes [FdVect F] Riehl's INTERMEDIATE CATEGORY of based vector
    spaces, and deliberately so — but only on objects.  The morphisms are
    ARBITRARY linear maps ([RModHom] of the underlying modules); nothing
    requires a morphism to respect the chosen coordinates.  A category
    whose morphisms had to preserve bases would be isomorphic, not merely
    equivalent, to [Matr], and Riehl's Example 1.5.12 would be void.
    Riehl's factorization has a SECOND leg — based spaces down to bare
    finite-dimensional spaces, forgetting the choice — and here that
    leg is VACUOUS rather than omitted: the library's ∃ being
    Type-valued, "has a basis" and "carries a chosen basis" are the
    same data, so the unbased finite-dimensional category IS [FdVect F]
    over again.  The functor [FdVect_Forget : FdVect F ⟶ Vct_F F] is
    NOT that leg — its target is ALL F-modules, infinite-dimensional
    ones included, so no essential-surjectivity claim is available for
    it and none is made.  What it does record, being identity on
    morphisms and hence full and faithful ([FdVect_Forget_Full],
    [FdVect_Forget_Faithful]), is that in the structure/property
    dichotomy the carried coordinates behave as mere PROPERTY relative
    to arbitrary linear maps: a full and faithful forgetful functor
    forgets at most properties, while one forgetting genuine structure
    would be faithful without being full.

    WHAT IS BUILT ON.  Instance/Mod.v supplies [RModObject], [RModHom]
    and [RMod R] — the underlying modules, homomorphisms, hom-setoid,
    identity and composition are reused unchanged, so [FdVect F] adds
    only the coordinate data.  Instance/Matr.v supplies [Matr] and, more
    importantly, its finite-sum engine: [fin_sum] with
    [fin_sum_respects]/[fin_sum_zero]/[fin_sum_add]/[fin_sum_swap], the
    bilinearity pair [fin_sum_mul_l]/[fin_sum_mul_r], and the Kronecker
    collapse [fin_sum_delta_l]/[fin_sum_delta_r] over [delta].  Every
    functor law, and faithfulness entire, is that engine applied, with no
    rig-level summation lemma restated.  Fullness needs the same sum one
    level up — over the module F^n rather than over F — so [msum] and its
    two lemmas ([msum_respects], [msum_hom]) are added here at
    [CMonObject] level, the general shape of which [fin_sum] is the
    additive-monoid-of-a-rig case; [msum_std] then says that in F^n the
    two agree coordinatewise.

    ORIENTATION, pinned by [Matr]'s composition and verified by the
    [eq_refl] probes below.  In [Matr R] an arrow
    n ~> m is an m × n matrix [A : Fin.t m → Fin.t n → carrier R], and
    composition is [(A ∘ B) i j ≈ Σ_l A i l · B l j].  So the functor
    sends A to the map F^n → F^m acting by [(A · v) i ≈ Σ_j A i j · v j]
    — row index outside, column index summed against the vector — and
    functoriality is then literally [Matr]'s associativity obligation
    read one dimension down.  Fullness inverts this: the matrix of a
    linear map f is [entry i j := coord (f (delta-vector j)) i], the
    j-th column being the image of the j-th standard basis vector.

    THE FIELD CLASS lands here rather than in Instance/Mod.v, which
    explicitly deferred it (see that file's SCOPE paragraph): a
    [FieldObject] is a [RingObject] with commutative multiplication, a
    proof that 1 and 0 differ, and a TOTAL inverse [finv] — junk at zero,
    as is standard in constructive algebra and in Coq's own [Qinv] — that
    is [Proper] for ≈ and satisfies [finv_l] away from zero.  Totality is
    what keeps [finv] a setoid function at all; the definer of a field
    owes the properness of the junk value, and for ℚ the stdlib's [Qinv]
    (with 0⁻¹ = 0) already discharges it.  [Vct_F F := RMod (field_ring
    F)] is the name Instance/Mod.v deferred to this issue: vector spaces
    over F are exactly F-modules.

    SCOPE.  Dimension is carried, not computed: no theorem here says two
    coordinate systems on the same space have the same length (that is
    invariance of dimension, which needs the rank argument and is not
    required by the equivalence).  No determinant, no GL_n, no direct
    sums, no duality; the matrix side's transpose self-duality already
    lives in Instance/Matr.v.

    And the honest strength: every proof below the class layer spends
    only the COMMUTATIVITY of the base ring — [finv], [finv_l] and
    [field_one_neq_zero] are content of the [FieldObject] class
    (exercised by [finv_r], [field_no_zero_divisors] and the ℚ
    instance), not premises of the equivalence, so the whole theorem
    would restate verbatim over any commutative ring, [Field_CRng]
    being the bridge such a restatement would cross.  It is stated
    over a field because vector spaces are what both sources name. *)

(* [Coq.QArith.QArith] is imported FIRST, and deliberately: it exports
   [Corelib.Relations.Relation_Definitions.equiv], which would otherwise
   shadow [Category.Lib.Setoid.equiv] and break every [Proper] signature
   below.  Importing the library afterwards restores the intended
   [equiv]. *)
Require Import Coq.QArith.QArith.
Require Import Coq.Vectors.Fin.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** Fields *)

(** A field: a commutative ring in which 1 ≠ 0, equipped with a TOTAL
    multiplicative inverse.  [finv] is a function on the whole carrier —
    it must be, to be a setoid map — so it takes some value at zero; that
    value is junk, constrained only by [finv_respects], and [finv_l]
    holds away from zero.  Nonzeroness is stated as [x ≈ 0 → False],
    which is the constructively meaningful form and the one the library's
    Type-valued logic supports. *)
Record FieldObject := {
  field_ring :> RingObject;

  field_comm : ∀ a b,
    rig_mul field_ring a b ≈ rig_mul field_ring b a;
  field_one_neq_zero :
    rig_one field_ring ≈ rig_zero field_ring → False;

  finv : carrier (rig_setoid field_ring) →
         carrier (rig_setoid field_ring);
  finv_respects : Proper (equiv ==> equiv) finv;

  finv_l : ∀ x, (x ≈ rig_zero field_ring → False) →
    rig_mul field_ring (finv x) x ≈ rig_one field_ring
}.

#[export] Existing Instance finv_respects.

(** The right inverse law, by commutativity — a corollary, not a
    field. *)
Corollary finv_r (F : FieldObject) (x : carrier (rig_setoid F)) :
  (x ≈ rig_zero F → False) → rig_mul F x (finv F x) ≈ rig_one F.
Proof.
  intro Hx.
  rewrite (field_comm F x (finv F x)).
  now apply finv_l.
Qed.

(** A field has no zero divisors: if a · b ≈ 0 and a ≉ 0 then b ≈ 0,
    by multiplying through by a⁻¹.  Not needed by the equivalence, but
    it is the one-line sanity check that the class has content. *)
Lemma field_no_zero_divisors (F : FieldObject)
  (a b : carrier (rig_setoid F)) :
  (a ≈ rig_zero F → False) → rig_mul F a b ≈ rig_zero F →
  b ≈ rig_zero F.
Proof.
  intros Ha Hab.
  rewrite <- (rig_mul_one_l F b).
  rewrite <- (finv_l F a Ha).
  rewrite (rig_mul_assoc F).
  rewrite Hab.
  apply rig_mul_zero_r.
Qed.

(** A field is in particular a commutative ring, so it lands in
    Instance/Rng.v's full subcategory [CRng] — the class is stated over
    [RingObject] plus a commutativity FIELD rather than over an object of
    [CRng] so that [rig_mul], [rig_add] and the rest stay one projection
    away, but the two presentations agree and the bridge is this
    one-liner. *)
Definition Field_CRng (F : FieldObject) : CRng :=
  (field_ring F; field_comm F).

(** Vector spaces over F are F-modules.  Instance/Mod.v deferred this
    name to the present issue; it is a definition rather than a notation
    so that it can be unfolded where the module API is wanted. *)
Definition Vct_F (F : FieldObject) : Category := RMod (field_ring F).

(** ** The rationals as a field *)

(** [Qinv] is total (0⁻¹ = 0), [Proper] for [Qeq] by [Qinv_comp], and
    [Qmult_inv_l] gives the inverse law away from zero — exactly the
    shape the class demands, so no junk-value obligation is left
    over. *)
Program Definition Q_Field : FieldObject := {|
  field_ring := Q_Ring;
  finv       := Qinv
|}.
Next Obligation. intros a b; simpl; apply Qmult_comm. Qed.
Next Obligation. simpl; unfold Qeq; simpl; discriminate. Qed.
Next Obligation. repeat intro; now apply Qinv_comp. Qed.
Next Obligation.
  (* The stdlib supplies only the right-hand law [Qmult_inv_r]; commute. *)
  intros x Hx; simpl.
  transitivity (Qmult x (Qinv x)).
  - apply Qmult_comm.
  - now apply Qmult_inv_r.
Qed.

Example q_field_inv : finv Q_Field (4 # 1) = (1 # 4)%Q := eq_refl.

Example q_field_inv_zero : finv Q_Field (0 # 1) = (0 # 1)%Q := eq_refl.

(** ** Finite-dimensional vector spaces with chosen coordinates *)

(** An object is an F-module together with a chosen linear isomorphism to
    F^n — i.e. a basis, presented as the coordinate/expansion pair rather
    than as a spanning independent family, so that nothing has to be
    proved to exist.  Only [fdv_coord] is required to be linear;
    [fdv_expand]'s linearity is derived below. *)
Record FdVectObject (F : FieldObject) := {
  fdv_mod :> RModObject (field_ring F);
  fdv_dim : nat;

  fdv_coord : carrier (cmon_setoid fdv_mod) →
              (Fin.t fdv_dim → carrier (rig_setoid F));
  fdv_expand : (Fin.t fdv_dim → carrier (rig_setoid F)) →
               carrier (cmon_setoid fdv_mod);

  fdv_coord_respects : ∀ v w, v ≈ w → ∀ i, fdv_coord v i ≈ fdv_coord w i;
  fdv_expand_respects : ∀ c d,
    (∀ i, c i ≈ d i) → fdv_expand c ≈ fdv_expand d;

  (* The two round trips: coordinates ARE an isomorphism onto F^n. *)
  fdv_coord_expand : ∀ c i, fdv_coord (fdv_expand c) i ≈ c i;
  fdv_expand_coord : ∀ v, fdv_expand (fdv_coord v) ≈ v;

  (* ... and it is linear. *)
  fdv_coord_plus : ∀ v w i,
    fdv_coord (cmon_plus fdv_mod v w) i
      ≈ rig_add F (fdv_coord v i) (fdv_coord w i);
  fdv_coord_smul : ∀ r v i,
    fdv_coord (rm_smul fdv_mod r v) i ≈ rig_mul F r (fdv_coord v i)
}.

Arguments fdv_mod {F} _.
Arguments fdv_dim {F} _.
Arguments fdv_coord {F} _ _ _.
Arguments fdv_expand {F} _ _.
Arguments fdv_coord_respects {F} _ _ _ _ _.
Arguments fdv_expand_respects {F} _ _ _ _.
Arguments fdv_coord_expand {F} _ _ _.
Arguments fdv_expand_coord {F} _ _.
Arguments fdv_coord_plus {F} _ _ _ _.
Arguments fdv_coord_smul {F} _ _ _ _.

(** *** The derived facts: [fdv_expand] is linear too

    Each is the same two-line argument — push the claim through
    [fdv_expand_coord], compare coordinates, and use the corresponding
    law for [fdv_coord].  Stating them as fields would have been
    redundant data. *)

Lemma fdv_coord_zero {F : FieldObject} (V : FdVectObject F)
  (i : Fin.t (fdv_dim V)) :
  fdv_coord V (cmon_zero V) i ≈ rig_zero F.
Proof.
  transitivity (fdv_coord V (rm_smul V (rig_zero F) (cmon_zero V)) i).
  - apply fdv_coord_respects.
    symmetry; apply rm_smul_zero_l.
  - rewrite (fdv_coord_smul V (rig_zero F) (cmon_zero V) i).
    apply rig_mul_zero_l.
Qed.

Lemma fdv_expand_plus {F : FieldObject} (V : FdVectObject F)
  (c d : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  fdv_expand V (fun i => rig_add F (c i) (d i))
    ≈ cmon_plus V (fdv_expand V c) (fdv_expand V d).
Proof.
  transitivity (fdv_expand V (fdv_coord V
    (cmon_plus V (fdv_expand V c) (fdv_expand V d)))).
  - apply fdv_expand_respects; intro i.
    symmetry.
    rewrite (fdv_coord_plus V (fdv_expand V c) (fdv_expand V d) i).
    now rewrite !(fdv_coord_expand V).
  - apply fdv_expand_coord.
Qed.

Lemma fdv_expand_smul {F : FieldObject} (V : FdVectObject F)
  (r : carrier (rig_setoid F))
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  fdv_expand V (fun i => rig_mul F r (c i))
    ≈ rm_smul V r (fdv_expand V c).
Proof.
  transitivity (fdv_expand V (fdv_coord V (rm_smul V r (fdv_expand V c)))).
  - apply fdv_expand_respects; intro i.
    symmetry.
    rewrite (fdv_coord_smul V r (fdv_expand V c) i).
    now rewrite (fdv_coord_expand V).
  - apply fdv_expand_coord.
Qed.

Lemma fdv_expand_zero {F : FieldObject} (V : FdVectObject F) :
  fdv_expand V (fun _ => rig_zero F) ≈ cmon_zero V.
Proof.
  transitivity (fdv_expand V (fdv_coord V (cmon_zero V))).
  - apply fdv_expand_respects; intro i.
    symmetry; apply fdv_coord_zero.
  - apply fdv_expand_coord.
Qed.

(** ** The category

    Objects carry coordinates; MORPHISMS DO NOT RESPECT THEM.  A hom is
    an arbitrary module homomorphism of the underlying modules, so the
    hom-setoid, identity and composition are Instance/Mod.v's, reused
    verbatim, and all four category laws hold for the reason they hold in
    [RMod R]: by [reflexivity] on the underlying setoid maps. *)
Program Definition FdVect (F : FieldObject) : Category := {|
  obj    := FdVectObject F;
  hom    := fun V W => @RModHom (field_ring F) (fdv_mod V) (fdv_mod W);
  homset := fun V W =>
    @RModHom_Setoid (field_ring F) (fdv_mod V) (fdv_mod W);
  id      := fun V => @rmod_hom_id (field_ring F) (fdv_mod V);
  compose := fun V W X f g =>
    @rmod_hom_compose (field_ring F) (fdv_mod V) (fdv_mod W) (fdv_mod X)
      f g;

  compose_respects := fun V W X =>
    @rmod_hom_compose_respects (field_ring F)
      (fdv_mod V) (fdv_mod W) (fdv_mod X)
|}.
Next Obligation. intros F V W f a; simpl; reflexivity. Qed.
Next Obligation. intros F V W f a; simpl; reflexivity. Qed.
Next Obligation. intros F V W X Y f g h a; simpl; reflexivity. Qed.
Next Obligation. intros F V W X Y f g h a; simpl; reflexivity. Qed.

(** The forgetful functor to F-modules, i.e. to [Vct_F F]: it drops the
    coordinates and is the identity on morphisms, hence full and
    faithful. *)
Program Definition FdVect_Forget (F : FieldObject) :
  FdVect F ⟶ Vct_F F := {|
  fobj := fun V => fdv_mod V;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros F V W f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F V a; simpl; reflexivity. Qed.
Next Obligation. intros F V W X f g a; simpl; reflexivity. Qed.

#[export] Program Instance FdVect_Forget_Faithful (F : FieldObject) :
  Faithful (FdVect_Forget F) := {|
  fmap_inj := fun V W f g Hfg => Hfg
|}.

#[export] Program Instance FdVect_Forget_Full (F : FieldObject) :
  Full (FdVect_Forget F) := {|
  prefmap := fun V W g => g
|}.
Next Obligation. intros F V W g a; simpl; reflexivity. Qed.

(** ** The standard space F^n

    Tuples [Fin.t n → F] with pointwise structure.  It is built up the
    same tower the general objects sit on — setoid, commutative monoid,
    abelian group, module — so that every law is the corresponding law of
    F, applied at each index.  Its coordinates are the IDENTITY: the
    standard basis is implicit in the indexing, which is exactly what
    makes [StdVect] the image of the comparison functor. *)

Section Std.

Context (F : FieldObject).
Context (n : nat).

Program Definition std_setoid : SetoidObject := {|
  carrier   := Fin.t n → carrier (rig_setoid F);
  is_setoid := {| Setoid.equiv := fun v w => ∀ i, v i ≈ w i
                ; Setoid.setoid_equiv := _ |}
|}.
Next Obligation.
  constructor.
  - intros v i; reflexivity.
  - intros v w H i; symmetry; apply H.
  - intros u v w Huv Hvw i.
    transitivity (v i); [ apply Huv | apply Hvw ].
Qed.

Program Definition std_cmon : CMonObject := {|
  cmon_setoid := std_setoid;
  cmon_zero   := fun _ => rig_zero F;
  cmon_plus   := fun v w i => rig_add F (v i) (w i)
|}.
Next Obligation.
  intros v v' Hv w w' Hw i; simpl in *.
  now rewrite (Hv i), (Hw i).
Qed.
Next Obligation. intros u v w i; simpl; apply rig_add_assoc. Qed.
Next Obligation. intros v w i; simpl; apply rig_add_comm. Qed.
Next Obligation. intros v i; simpl; apply rig_add_zero_l. Qed.

Program Definition std_ab : AbObject := {|
  ab_cmon := std_cmon;
  ab_neg  := fun v i => ring_neg F (v i)
|}.
Next Obligation.
  intros v w Hv i; simpl in *.
  now rewrite (Hv i).
Qed.
Next Obligation. intros v i; simpl; apply ring_neg_l. Qed.

Program Definition std_mod : RModObject (field_ring F) := {|
  rm_ab   := std_ab;
  rm_smul := fun r v i => rig_mul F r (v i)
|}.
Next Obligation.
  intros r s Hrs v w Hv i; simpl in *.
  now rewrite Hrs, (Hv i).
Qed.
Next Obligation. intros r v w i; simpl; apply rig_distr_l. Qed.
Next Obligation. intros r s v i; simpl; apply rig_distr_r. Qed.
Next Obligation. intros r s v i; simpl; apply rig_mul_assoc. Qed.
Next Obligation. intros v i; simpl; apply rig_mul_one_l. Qed.

(** The coordinates of F^n are the identity, so all six coordinate laws
    hold by [reflexivity]. *)
Program Definition StdVect : FdVectObject F := {|
  fdv_mod    := std_mod;
  fdv_dim    := n;
  fdv_coord  := fun v => v;
  fdv_expand := fun c => c
|}.
Next Obligation. intros v w Hv i; exact (Hv i). Qed.
Next Obligation. intros c d Hcd; exact Hcd. Qed.
Next Obligation. intros c i; reflexivity. Qed.
Next Obligation. intros v i; reflexivity. Qed.
Next Obligation. intros v w i; simpl; reflexivity. Qed.
Next Obligation. intros r v i; simpl; reflexivity. Qed.

End Std.

Arguments StdVect F n : clear implicits.

(** The standard basis vector e_j : F^n, the j-th column of the identity
    matrix.  It is [delta] of Instance/Matr.v, reused rather than
    redefined, so the Kronecker collapse lemmas apply to it directly. *)
Definition std_basis (F : FieldObject) (n : nat) (j : Fin.t n) :
  Fin.t n → carrier (rig_setoid F) :=
  fun i => delta (field_ring F) i j.

Example std_dim (F : FieldObject) (n : nat) :
  fdv_dim (StdVect F n) = n := eq_refl.

(** ** Matrices as linear maps: the orientation, pinned by computation *)

(** [mat_apply R A v i = Σ_j A i j · v j].  With [A : Fin.t m → Fin.t n →
    R] — an arrow n ~> m of [Matr R] — this is the map F^n → F^m, the row
    index [i] surviving and the column index [j] contracted against the
    vector.  Everything downstream depends on this choice being the one
    that matches [Matr]'s composition, so it is checked by computation
    immediately below rather than argued for. *)
Definition mat_apply (R : RigObject) {n m : nat}
  (A : Fin.t m → Fin.t n → carrier (rig_setoid R))
  (v : Fin.t n → carrier (rig_setoid R)) :
  Fin.t m → carrier (rig_setoid R) :=
  fun i => fin_sum R (fun j => rig_mul R (A i j) (v j)).

(** A two-element tabulator, for the probes only. *)
Definition fin2 {A : Type} (a b : A) : Fin.t 2 → A :=
  fun i => match i with
           | Fin.F1     => a
           | Fin.FS _   => b
           end.

(* 1 × 1: the 1 × 1 matrix (3) sends the vector (4) to (12). *)
Example mat_apply_1x1 :
  mat_apply Int_Rig (n:=1) (m:=1) (fun _ _ => 3%Z) (fun _ => 4%Z) Fin.F1
    = 12%Z := eq_refl.

(* 2 × 2: [[1,2],[3,4]] · (5,6) = (1·5+2·6, 3·5+4·6) = (17, 39).  Rows
   are the OUTER index — had the orientation been transposed, the answers
   would be (1·5+3·6, 2·5+4·6) = (23, 34), and that reading is refuted
   by computation just below, not by this prose. *)
Definition probe_A : Fin.t 2 → Fin.t 2 → Z :=
  fin2 (fin2 1%Z 2%Z) (fin2 3%Z 4%Z).
Definition probe_v : Fin.t 2 → Z := fin2 5%Z 6%Z.

Example mat_apply_2x2_row0 :
  mat_apply Int_Rig probe_A probe_v Fin.F1 = 17%Z := eq_refl.
Example mat_apply_2x2_row1 :
  mat_apply Int_Rig probe_A probe_v (Fin.FS Fin.F1) = 39%Z := eq_refl.

(* The TRANSPOSED reading, Σ_j A j i · v j, machine-checked: on the
   same probe it yields (23, 34), and its first component differs from
   the true 17 — so the two readings are discriminated by computation,
   which is what "checked rather than argued for" owes. *)
Definition mat_apply_T (R : RigObject) {n m : nat}
  (A : Fin.t m → Fin.t n → carrier (rig_setoid R))
  (v : Fin.t m → carrier (rig_setoid R)) :
  Fin.t n → carrier (rig_setoid R) :=
  fun i => fin_sum R (fun j => rig_mul R (A j i) (v j)).

Example mat_apply_T_2x2_row0 :
  mat_apply_T Int_Rig probe_A probe_v Fin.F1 = 23%Z := eq_refl.
Example mat_apply_T_2x2_row1 :
  mat_apply_T Int_Rig probe_A probe_v (Fin.FS Fin.F1) = 34%Z := eq_refl.
Example mat_apply_orientation_discriminated :
  mat_apply_T Int_Rig probe_A probe_v Fin.F1
    = mat_apply Int_Rig probe_A probe_v Fin.F1 → False.
Proof. intro e; discriminate e. Qed.

(* The identity matrix acts as the identity: Σ_j delta i j · v j ≈ v i,
   which is [fin_sum_delta_l] with no work. *)
Example mat_apply_id (R : RigObject) (n : nat)
  (v : Fin.t n → carrier (rig_setoid R)) (i : Fin.t n) :
  mat_apply R (@id (Matr R) n) v i ≈ v i.
Proof. apply (fin_sum_delta_l R i v). Qed.

(* The j-th column of A is the image of the j-th standard basis vector:
   Σ_l A i l · delta l j ≈ A i j, by [fin_sum_delta_r].  This is the
   equation fullness inverts. *)
Example mat_apply_basis (R : RigObject) {n m : nat}
  (A : Fin.t m → Fin.t n → carrier (rig_setoid R))
  (j : Fin.t n) (i : Fin.t m) :
  mat_apply R A (fun l => delta R l j) i ≈ A i j.
Proof. apply (fin_sum_delta_r R j (fun l => A i l)). Qed.

(** ** Finite sums in a commutative monoid

    Instance/Matr.v's [fin_sum] is this sum for the additive monoid of a
    rig; fullness needs it one level up, for the module F^n itself, in
    order to expand a vector as Σ_j v_j · e_j.  Three lemmas suffice:
    congruence, preservation by monoid homomorphisms, and — inside the
    section below — the observation that in F^n a monoid sum is computed
    coordinatewise by [fin_sum]. *)

Fixpoint msum (M : CMonObject) {p : nat} :
  (Fin.t p → carrier (cmon_setoid M)) → carrier (cmon_setoid M) :=
  match p with
  | O   => fun _ => cmon_zero M
  | S k => fun f => cmon_plus M (f Fin.F1) (msum M (fun i => f (Fin.FS i)))
  end.

Lemma msum_respects (M : CMonObject) {p : nat}
  (f g : Fin.t p → carrier (cmon_setoid M)) :
  (∀ i, f i ≈ g i) → msum M f ≈ msum M g.
Proof.
  revert f g.
  induction p as [| k IHk]; intros f g H; simpl.
  - reflexivity.
  - apply cmon_plus_respects; [ apply H |].
    apply IHk; intro i; apply H.
Qed.

Lemma msum_hom {M N : CMonObject} (h : CMonHom M N) {p : nat}
  (f : Fin.t p → carrier (cmon_setoid M)) :
  cmon_map h (msum M f) ≈ msum N (fun i => cmon_map h (f i)).
Proof.
  revert f.
  induction p as [| k IHk]; intros f; simpl.
  - apply cmon_map_zero.
  - rewrite cmon_map_plus.
    now rewrite (IHk (fun i => f (Fin.FS i))).
Qed.

(** ** The comparison functor *)

Section Comparison.

Context (F : FieldObject).

(** *** Linearity of [mat_apply]

    Four lemmas, each one line of the finite-sum engine: congruence,
    annihilation, additivity (distributivity plus [fin_sum_add]), and
    homogeneity — the last being one of exactly TWO places on the
    equivalence's path where the field's COMMUTATIVITY is spent (the
    other is [matrix_of_sur], sliding a scalar past a basis image;
    [finv_r] spends it a third time, off that path), because a left
    module over a non-commutative ring is not acted on linearly by
    matrices on the left. *)

Lemma mat_apply_respects {n m : nat}
  (A : Fin.t m → Fin.t n → carrier (rig_setoid F))
  (v w : Fin.t n → carrier (rig_setoid F)) :
  (∀ j, v j ≈ w j) →
  ∀ i, mat_apply (field_ring F) A v i
         ≈ mat_apply (field_ring F) A w i.
Proof.
  intros H i.
  apply fin_sum_respects; intro j.
  now rewrite (H j).
Qed.

Lemma mat_apply_zero {n m : nat}
  (A : Fin.t m → Fin.t n → carrier (rig_setoid F)) :
  ∀ i, mat_apply (field_ring F) A (fun _ => rig_zero F) i ≈ rig_zero F.
Proof.
  intro i.
  transitivity (fin_sum (field_ring F) (fun _ : Fin.t n => rig_zero F)).
  - apply fin_sum_respects; intro j.
    apply rig_mul_zero_r.
  - apply fin_sum_zero.
Qed.

Lemma mat_apply_plus {n m : nat}
  (A : Fin.t m → Fin.t n → carrier (rig_setoid F))
  (v w : Fin.t n → carrier (rig_setoid F)) :
  ∀ i, mat_apply (field_ring F) A (fun j => rig_add F (v j) (w j)) i
         ≈ rig_add F (mat_apply (field_ring F) A v i)
                     (mat_apply (field_ring F) A w i).
Proof.
  intro i.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_add F (rig_mul F (A i j) (v j))
                        (rig_mul F (A i j) (w j)))).
  - apply fin_sum_respects; intro j.
    apply rig_distr_l.
  - apply fin_sum_add.
Qed.

Lemma mat_apply_smul {n m : nat}
  (A : Fin.t m → Fin.t n → carrier (rig_setoid F))
  (r : carrier (rig_setoid F))
  (v : Fin.t n → carrier (rig_setoid F)) :
  ∀ i, mat_apply (field_ring F) A (fun j => rig_mul F r (v j)) i
         ≈ rig_mul F r (mat_apply (field_ring F) A v i).
Proof.
  intro i.
  unfold mat_apply.
  rewrite fin_sum_mul_l.
  apply fin_sum_respects; intro j.
  rewrite <- (rig_mul_assoc F), <- (rig_mul_assoc F).
  apply rig_mul_respects; [ apply field_comm | reflexivity ].
Qed.

(** The linear map of a matrix.  Only [proper_morphism] is left to
    [Program]; the three law fields are the lemmas just proved, handed
    over as terms so that obligation ORDER cannot matter. *)
Program Definition mat_hom {n m : nat}
  (A : Fin.t m → Fin.t n → carrier (rig_setoid F)) :
  StdVect F n ~{FdVect F}~> StdVect F m := {|
  rm_hom := {|
    cmon_map      := {| morphism := mat_apply (field_ring F) A |};
    cmon_map_zero := mat_apply_zero A;
    cmon_map_plus := fun v w => mat_apply_plus A v w
  |};
  rm_map_smul := fun r v => mat_apply_smul A r v
|}.
Next Obligation.
  intros n m A v w Hvw.
  exact (mat_apply_respects A v w Hvw).
Qed.

(** Mac Lane §I.4 Exercise 6 / Riehl §1.5 Example 1.5.12: the comparison
    functor.  [fmap_comp] is [Matr]'s associativity obligation read one
    dimension down — bilinearity of · over Σ, then the exchange of double
    sums. *)
Program Definition Matr_to_FdVect : Matr (field_ring F) ⟶ FdVect F := {|
  fobj := fun n => StdVect F n;
  fmap := fun n m A => mat_hom A
|}.
Next Obligation.
  intros n m A B HAB v i; simpl.
  apply fin_sum_respects; intro j.
  now rewrite (HAB i j).
Qed.
Next Obligation.
  intros n v i; simpl.
  apply (fin_sum_delta_l (field_ring F) i v).
Qed.
Next Obligation.
  intros n m k A B v i; simpl.
  unfold Basics.compose, mat_apply; simpl.
  (* Σ_j (Σ_l A i l · B l j) · v j ≈ Σ_l A i l · (Σ_j B l j · v j) *)
  etransitivity.
  { apply fin_sum_respects; intro j.
    apply fin_sum_mul_r. }
  etransitivity.
  { apply fin_sum_respects; intro j.
    apply fin_sum_respects; intro l.
    apply rig_mul_assoc. }
  etransitivity; [ apply fin_sum_swap |].
  symmetry.
  apply fin_sum_respects; intro l.
  apply fin_sum_mul_l.
Qed.

End Comparison.

(** ** Faithful, full, essentially surjective *)

Section FullFaithfulEso.

Context (F : FieldObject).

(** *** Faithful: a matrix is recovered from its map at basis vectors

    [mat_apply A e_j i ≈ A i j] is [fin_sum_delta_r], so two matrices
    inducing the same linear map agree entrywise. *)
Lemma Matr_to_FdVect_faithful {n m : nat}
  (A B : n ~{Matr (field_ring F)}~> m) :
  fmap[Matr_to_FdVect F] A ≈ fmap[Matr_to_FdVect F] B → A ≈ B.
Proof.
  intros H i j.
  transitivity (mat_apply (field_ring F) A (std_basis F n j) i).
  - symmetry.
    apply (fin_sum_delta_r (field_ring F) j (fun l => A i l)).
  - transitivity (mat_apply (field_ring F) B (std_basis F n j) i).
    + exact (H (std_basis F n j) i).
    + apply (fin_sum_delta_r (field_ring F) j (fun l => B i l)).
Qed.

#[export] Program Instance Matr_to_FdVect_Faithful :
  Faithful (Matr_to_FdVect F) := {|
  fmap_inj := fun n m A B H => Matr_to_FdVect_faithful A B H
|}.

(** *** Full: the matrix of a linear map is its table of basis images *)

(** In F^n a monoid sum is computed coordinatewise, because the module
    operations are pointwise. *)
Lemma msum_std {n p : nat}
  (f : Fin.t p → (Fin.t n → carrier (rig_setoid F))) (i : Fin.t n) :
  msum (std_cmon F n) f i
    ≈ fin_sum (field_ring F) (fun j => f j i).
Proof.
  revert f.
  induction p as [| k IHk]; intros f; simpl.
  - reflexivity.
  - apply rig_add_respects; [ reflexivity |].
    apply (IHk (fun j => f (Fin.FS j))).
Qed.

(** Every vector of F^n is the sum of its coordinates against the
    standard basis: v ≈ Σ_j v_j · e_j.  This is [fin_sum_delta_r] once
    the sum is pushed to coordinates by [msum_std]. *)
Lemma std_expand {n : nat} (v : Fin.t n → carrier (rig_setoid F)) :
  (v : carrier (cmon_setoid (std_mod F n)))
    ≈ msum (std_cmon F n)
        (fun j => rm_smul (std_mod F n) (v j) (std_basis F n j)).
Proof.
  intro i.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F (v j) (delta (field_ring F) j i))).
  - symmetry.
    apply (fin_sum_delta_r (field_ring F) i v).
  - symmetry.
    transitivity (fin_sum (field_ring F)
      (fun j => rm_smul (std_mod F n) (v j) (std_basis F n j) i)).
    + apply (msum_std
               (fun j => rm_smul (std_mod F n) (v j) (std_basis F n j)) i).
    + apply fin_sum_respects; intro j.
      apply rig_mul_respects; [ reflexivity | apply delta_sym ].
Qed.

(** The matrix of a linear map: its (i,j) entry is the i-th coordinate
    of the image of the j-th basis vector — the j-th column IS g e_j. *)
Definition matrix_of {n m : nat}
  (g : StdVect F n ~{FdVect F}~> StdVect F m) :
  n ~{Matr (field_ring F)}~> m :=
  fun i j => cmon_map (rm_hom g) (std_basis F n j) i.

(** The section law.  Expand v, push g through the sum ([msum_hom]) and
    through each scalar ([rm_map_smul]), return to coordinates
    ([msum_std]), and commute the two factors. *)
Lemma matrix_of_sur {n m : nat}
  (g : StdVect F n ~{FdVect F}~> StdVect F m) :
  fmap[Matr_to_FdVect F] (matrix_of g) ≈ g.
Proof.
  intros v i; simpl.
  symmetry.
  transitivity (cmon_map (rm_hom g)
    (msum (std_cmon F n)
       (fun j => rm_smul (std_mod F n) (v j) (std_basis F n j))) i).
  { exact (proper_morphism (cmon_map (rm_hom g)) _ _ (std_expand v) i). }
  transitivity (msum (std_cmon F m)
    (fun j => cmon_map (rm_hom g)
                (rm_smul (std_mod F n) (v j) (std_basis F n j))) i).
  { exact (msum_hom (rm_hom g)
             (fun j => rm_smul (std_mod F n) (v j) (std_basis F n j)) i). }
  transitivity (fin_sum (field_ring F)
    (fun j => cmon_map (rm_hom g)
                (rm_smul (std_mod F n) (v j) (std_basis F n j)) i)).
  { apply (msum_std
             (fun j => cmon_map (rm_hom g)
                         (rm_smul (std_mod F n) (v j)
                            (std_basis F n j))) i). }
  apply fin_sum_respects; intro j.
  transitivity (rig_mul F (v j)
    (cmon_map (rm_hom g) (std_basis F n j) i)).
  - exact (rm_map_smul g (v j) (std_basis F n j) i).
  - apply field_comm.
Qed.

#[export] Program Instance Matr_to_FdVect_Full :
  Full (Matr_to_FdVect F) := {|
  prefmap := fun n m g => matrix_of g;
  fmap_sur := fun n m g => matrix_of_sur g
|}.

(** *** Essentially surjective: the chosen coordinates ARE the witness *)

Program Definition std_coord_hom (V : FdVectObject F) :
  V ~{FdVect F}~> StdVect F (fdv_dim V) := {|
  rm_hom := {|
    cmon_map      := {| morphism := fdv_coord V |};
    cmon_map_zero := fdv_coord_zero V;
    cmon_map_plus := fun v w => fdv_coord_plus V v w
  |};
  rm_map_smul := fun r v => fdv_coord_smul V r v
|}.
Next Obligation.
  intros V v w Hvw.
  exact (fdv_coord_respects V v w Hvw).
Qed.

Program Definition std_expand_hom (V : FdVectObject F) :
  StdVect F (fdv_dim V) ~{FdVect F}~> V := {|
  rm_hom := {|
    cmon_map      := {| morphism := fdv_expand V |};
    cmon_map_zero := fdv_expand_zero V;
    cmon_map_plus := fun c d => fdv_expand_plus V c d
  |};
  rm_map_smul := fun r c => fdv_expand_smul V r c
|}.
Next Obligation.
  intros V c d Hcd.
  exact (fdv_expand_respects V c d Hcd).
Qed.

(** A chosen basis IS a linear isomorphism F^dim ≅ V; both inverse laws
    are the round trips, applied pointwise. *)
Program Definition StdVect_iso (V : FdVectObject F) :
  StdVect F (fdv_dim V) ≅[FdVect F] V := {|
  to   := std_expand_hom V;
  from := std_coord_hom V
|}.
Next Obligation. intros V v; simpl; apply fdv_expand_coord. Qed.
Next Obligation. intros V c i; simpl; apply fdv_coord_expand. Qed.

(** [#[local]], deliberately: [eso_obj] is a CHOICE (the carried
    dimension), and chosen-preimage instances stay out of the global
    database — Theory/Equivalence/FullFaithful.v's rationale, and the
    precedent of Construction/Reflective/Idempotent.v.  Section-local
    hints die at [End], so the one consumer,
    [FdVect_Matr_Equivalence], names this constant explicitly;
    downstream callers take the equivalence by name. *)
#[local] Program Instance Matr_to_FdVect_EssSurj :
  EssentiallySurjective (Matr_to_FdVect F) := {|
  eso_obj := fun V => fdv_dim V;
  eso_iso := fun V => StdVect_iso V
|}.

End FullFaithfulEso.

(** ** Mac Lane §I.4 Exercise 6 / Riehl §1.5 Example 1.5.12

    The comparison functor is full, faithful and essentially surjective,
    so Theory/Equivalence/FullFaithful.v's [FF_ESO_Equivalence] hands
    back the equivalence — including the quasi-inverse, which is the
    construction "read off the matrix of a linear map in the chosen
    bases".  No choice principle is consumed: the quasi-inverse is
    assembled from [prefmap] and [eso_iso], both of which are data here
    ([matrix_of] and [StdVect_iso]).  The essential-surjectivity
    witness is passed EXPLICITLY — it carries the choice of preimage
    object, and choices do not ride the instance database (the
    [#[local]] above dies with its section, which is the point). *)
Definition FdVect_Matr_Equivalence (F : FieldObject) :
  EquivalenceOfCategories (Matr_to_FdVect F) :=
  @FF_ESO_Equivalence _ _ (Matr_to_FdVect F) _ _
    (Matr_to_FdVect_EssSurj F).

(** The quasi-inverse sends a space to its carried dimension, on the
    nose — the content of essential surjectivity, made visible. *)
Example equivalence_inverse_dim (F : FieldObject) (V : FdVectObject F) :
  fobj[@quasi_inverse (Matr (field_ring F)) (FdVect F) (Matr_to_FdVect F)
         (FdVect_Matr_Equivalence F)] V
    = fdv_dim V := eq_refl.

(** ** Reindexing maps, and the acceptance tests over ℚ *)

(** Reindexing a tuple along any [s : Fin.t m → Fin.t n] is linear, and
    all three laws hold by [reflexivity], the module operations of F^n
    being pointwise.  This supplies concrete linear maps that are NOT
    presented as matrices, which is what makes the fullness probe below
    a real round trip rather than a restatement. *)
Definition std_reindex (F : FieldObject) {n m : nat}
  (s : Fin.t m → Fin.t n) :
  StdVect F n ~{FdVect F}~> StdVect F m.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (std_mod F n) (std_mod F m)
       (@Build_CMonHom (std_cmon F n) (std_cmon F m)
          (@Build_SetoidMorphism _ _ _ _ (fun v i => v (s i)) _) _ _) _).
  - intros v w Hvw i; exact (Hvw (s i)).
  - intro i; reflexivity.
  - intros v w i; reflexivity.
  - intros r v i; reflexivity.
Defined.

(** *** Dimension two over ℚ *)

Definition qA : 2%nat ~{Matr (field_ring Q_Field)}~> 2%nat :=
  fin2 (fin2 (1 # 1) (2 # 1)) (fin2 (3 # 1) (4 # 1)).

Definition qv : Fin.t 2 → carrier (rig_setoid Q_Field) :=
  fin2 (5 # 1) (6 # 1).

(* [[1,2],[3,4]] · (5,6) = (17, 39), through the functor itself. *)
Example q_fmap_row0 :
  cmon_map (rm_hom (fmap[Matr_to_FdVect Q_Field] qA)) qv Fin.F1
    = (17 # 1)%Q := eq_refl.

Example q_fmap_row1 :
  cmon_map (rm_hom (fmap[Matr_to_FdVect Q_Field] qA)) qv (Fin.FS Fin.F1)
    = (39 # 1)%Q := eq_refl.

(* The fullness round trip recovers the matrix entrywise. *)
Example q_full_roundtrip_01 :
  matrix_of Q_Field (fmap[Matr_to_FdVect Q_Field] qA)
    Fin.F1 (Fin.FS Fin.F1) = (2 # 1)%Q := eq_refl.

Example q_full_roundtrip_10 :
  matrix_of Q_Field (fmap[Matr_to_FdVect Q_Field] qA)
    (Fin.FS Fin.F1) Fin.F1 = (3 # 1)%Q := eq_refl.

(* ... and on a linear map given independently of any matrix: the
   coordinate swap of ℚ², whose matrix is [[0,1],[1,0]]. *)
Definition fin2_swap : Fin.t 2 → Fin.t 2 := fin2 (Fin.FS Fin.F1) Fin.F1.

Definition q_swap : StdVect Q_Field 2 ~{FdVect Q_Field}~> StdVect Q_Field 2 :=
  std_reindex Q_Field fin2_swap.

Example q_swap_matrix_00 :
  matrix_of Q_Field q_swap Fin.F1 Fin.F1 = 0%Q := eq_refl.
Example q_swap_matrix_01 :
  matrix_of Q_Field q_swap Fin.F1 (Fin.FS Fin.F1) = 1%Q := eq_refl.
Example q_swap_matrix_10 :
  matrix_of Q_Field q_swap (Fin.FS Fin.F1) Fin.F1 = 1%Q := eq_refl.
Example q_swap_matrix_11 :
  matrix_of Q_Field q_swap (Fin.FS Fin.F1) (Fin.FS Fin.F1) = 0%Q := eq_refl.

(* The chosen coordinates of the standard space are the identity, so its
   round trips compute — at open vectors, not just at literals. *)
Example q_std_coord_expand (c : Fin.t 2 → carrier (rig_setoid Q_Field))
  (i : Fin.t 2) :
  fdv_coord (StdVect Q_Field 2) (fdv_expand (StdVect Q_Field 2) c) i = c i
  := eq_refl.

Example q_std_expand_coord (v : Fin.t 2 → carrier (rig_setoid Q_Field)) :
  fdv_expand (StdVect Q_Field 2) (fdv_coord (StdVect Q_Field 2) v) = v
  := eq_refl.

(* Vector spaces over ℚ, by the deferred name. *)
Definition Vct_Q : Category := Vct_F Q_Field.
