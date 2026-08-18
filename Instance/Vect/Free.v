(* [Coq.QArith.QArith] is imported FIRST, before [Category.Lib]: it exports
   an [equiv] that shadows [Setoid]'s otherwise.  This is the import-order
   discipline Instance/FdVect.v records at its own head. *)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Free.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The free vector space on a set, as a universal arrow and as an
      adjunction

    nLab:      https://ncatlab.org/nlab/show/free+module
    nLab:      https://ncatlab.org/nlab/show/basis+of+a+vector+space
    Wikipedia: https://en.wikipedia.org/wiki/Free_module
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          GTM 5, §III.1, printed p. 56 — maclane:III.1:construction1
    Book: Mac Lane, ibid., §IV.1, printed p. 79 —
          maclane:IV.1:construction1
    Book: Riehl, Category Theory in Context, §4.0, printed p. 131 —
          riehl:4.0:construction-free-vector-space

    THE HEADLINE.  Mac Lane's §III.1 asks for the vector space V_X of
    formal K-linear combinations on a set X together with its insertion
    of a basis j : X → U(V_X), and for the proof that ⟨V_X, j⟩ is a
    universal arrow from X to the forgetful functor Vect_K ⟶ Set; his
    §IV.1 asks for the SAME content presented as an adjunction, with the
    bijection Vect_K(V_X, W) ≅ Set(X, U W) natural in each variable
    separately; Riehl's §4.0 asks for k[S], its functoriality in S, and
    the adjunction as the headline.  All of that is delivered here, and
    the adjunction — [free_vect_adjunction] — is the principal artifact.

    WHERE THE WORK ACTUALLY IS.  Instance/FdVect.v:223 defines
    [Vct_F F := RMod (field_ring F)]: a vector space over F IS an
    F-module, by DEFINITION and not by an isomorphism of categories.  The
    construction of the free object therefore uses nothing about fields,
    and it is carried out over an arbitrary [RingObject] in
    Instance/Mod/Free.v — the formal-expression carrier, the linear
    extension, the universal property, the functor, the adjunction, both
    naturality clauses, the finite-linear-combination normal form and the
    non-degeneracy results all live there.  This file is the vector-space
    reading, and because the two categories are the same term, every
    specialization below is a CONVERSION: each definition is stated with
    its [Vct_F]-level type and inhabited by the [RMod]-level term, so the
    kernel checks the identification rather than a transport doing it.
    Nothing here re-proves anything.

    WHAT THE FIELD LAYER BUYS.  Exactly one thing, for exactly one
    theorem, and it is worth naming precisely.  Instance/Mod/Free.v's
    BASIS-INJECTIVITY result — and only that one — is stated under the
    hypothesis 1 ≉ 0 in the ring, because over the zero ring every module
    is trivial and that statement is genuinely false there.  (Its
    linear-independence sibling needs no such hypothesis: over the zero
    ring every scalar is already 0, so that statement degenerates to a
    truth rather than to a falsehood and survives unassisted.)  A
    [FieldObject] carries [field_one_neq_zero] as a FIELD, so over a
    field that hypothesis is discharged for free and the only remaining
    cost is a decider for the generating setoid's [≈] — see
    [free_vect_basis_distinct], the one witness below that passes
    [field_one_neq_zero Q_Field], and it passes it with no work.
    Nothing else in the development spends
    commutativity, [finv], or any other field structure — and the
    witnesses below do not either: [free_vect_half_not_one] uses a proper
    fraction as a scalar to show that the scalar ring really is ℚ, but it
    never inverts anything, so no claim is made here that [finv] is
    exercised.

    THE ℚ WITNESS, AND WHY IT IS NOT DEGENERATE.  A free vector space on
    the empty or a one-element set proves nothing, so the generating
    setoid has TWO elements and the target is ℚ regarded as a
    one-dimensional ℚ-vector space (Instance/Mod.v's [Ring_RMod] at
    [field_ring Q_Field]).  The linear extension of the assignment
    e₀ ↦ 3, e₁ ↦ 5 sends 2·e₀ + e₁ to 11, and that COMPUTES: the
    [Example]s below close by [eq_refl] on the carrier ℚ, which is the
    convertibility exception, not a claim about morphisms.  Beyond
    computation, three separations are recorded: the two basis vectors
    are distinct ([free_vect_basis_distinct]), they are linearly
    independent ([free_vect_basis_independent] — the statement a reader
    of §III.1 wants, and the one that spends no 1 ≉ 0, precisely because
    over a degenerate scalar ring it would reduce to a truth rather than
    to a falsehood), and distinct scalars give distinct multiples of one
    basis vector even when the scalars are proper fractions
    ([free_vect_half_not_one]).

    WHAT IS NOT DELIVERED.  Everything Instance/Mod/Free.v's closing
    section disclaims, in particular coefficient uniqueness and therefore
    dimension; additionally, no comparison with Instance/FdVect.v's
    [FdVectObject] (which carries a chosen coordinate isomorphism to Fⁿ),
    so it is NOT proved here that the free vector space on a finite
    generating setoid is finite-dimensional in that file's sense.  That
    comparison needs the coefficient uniqueness just disclaimed, and it
    is the natural next issue. *)

Section FreeVect.

Context (F : FieldObject).

(** ** Vector spaces over F are F-modules, definitionally

    Not an isomorphism of categories and not a transport: the two are the
    same term, which is what makes every specialization below a
    conversion. *)
Example Vct_F_is_RMod : Vct_F F = RMod (field_ring F) := eq_refl.

Definition Vct_Forget : Vct_F F ⟶ Sets := RMod_Forget (field_ring F).

Example Vct_Forget_is_RMod_Forget :
  Vct_Forget = RMod_Forget (field_ring F) := eq_refl.

(** ** The free vector space on a set, and its basis insertion *)

Definition FreeVectObject (X : Sets) : Vct_F F := FreeModObject X.

Definition free_vect_insert (X : Sets)
  : X ~{Sets}~> Vct_Forget (FreeVectObject X) := fv_insert X.

(** ** Mac Lane §III.1: ⟨V_X, j⟩ is a universal arrow

    Every function from X into the underlying set of a vector space W
    extends to one and only one linear map V_X ⟶ W. *)
Theorem free_vect_universal (X : Sets) :
  ∀ (W : Vct_F F) (h : X ~{Sets}~> Vct_Forget W),
    ∃! g : FreeVectObject X ~{Vct_F F}~> W,
      h ≈ fmap[Vct_Forget] g ∘ free_vect_insert X.
Proof. exact (free_module_universal X). Qed.

Definition free_vect_universal_arrow (X : Sets)
  : UniversalArrow X Vct_Forget := free_module_universal_arrow X.

(** The same content in the direct encoding, where the universal object
    is named rather than projected out of a comma category. *)
Definition free_vect_AUniversalArrow (X : Sets)
  : AUniversalArrow X Vct_Forget (FreeVectObject X) :=
  free_module_AUniversalArrow (field_ring F) X.

(** ** Mac Lane §IV.1 and Riehl §4.0: the adjunction

    The principal artifact of this issue. *)

Definition FreeVect : Sets ⟶ Vct_F F := FreeMod (field_ring F).

Definition free_vect_adjunction : FreeVect ⊣ Vct_Forget :=
  free_module_adjunction (field_ring F).

Example FreeVect_obj (X : Sets) : FreeVect X = FreeVectObject X := eq_refl.

Example free_vect_arrow_is_insert (X : Sets) :
  @arrow _ _ X Vct_Forget (free_vect_universal_arrow X)
    = free_vect_insert X := eq_refl.

(** ** Unit and counit

    The unit is the insertion of the basis, definitionally; the counit
    evaluates a formal linear combination, up to [≈] only, for the reason
    Instance/Mod/Free.v gives ([ump_universal_arrows] is [Qed]-opaque). *)

Definition free_vect_unit (X : Sets)
  : X ~{Sets}~> Vct_Forget (FreeVect X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_vect_adjunction X.

Example free_vect_unit_is_insert (X : Sets) (x : carrier X) :
  free_vect_unit X x = free_vect_insert X x := eq_refl.

Definition free_vect_counit (W : Vct_F F)
  : FreeVect (Vct_Forget W) ~{Vct_F F}~> W :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_vect_adjunction W.

Theorem free_vect_counit_evaluates (W : Vct_F F)
  (t : @FVTerm (field_ring F) (Vct_Forget W)) :
  cmon_map (rm_hom (free_vect_counit W)) t
    ≈ fv_eval (@id Sets (Vct_Forget W)) t.
Proof. exact (free_module_counit_evaluates (field_ring F) W t). Qed.

(** ** Riehl's functoriality on maps of generating sets

    Relabelling the generating set relabels the basis vectors. *)
Lemma free_vect_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (rm_hom (fmap[FreeVect] u)) (fv_gen x) ≈ fv_gen (u x).
Proof. exact (@free_module_fmap_generators (field_ring F) X Y u x). Qed.

(** ** §IV.1's bijection, and its two naturality clauses

    Restriction to the basis is the adjunction's forward transpose, and
    it is a bijection with linear extension as its inverse.  The two
    naturality clauses are stated separately, as §IV.1 asks; each is the
    corresponding theorem of Instance/Mod/Free.v read at [Vct_F F], and
    each of those was proved there in the free module's own vocabulary
    rather than by citing the adjunction class. *)

Definition free_vect_restrict {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) : X ~{Sets}~> Vct_Forget W :=
  fv_transpose g.

Example free_vect_restrict_is_adj {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) :
  to (@adj _ _ _ _ free_vect_adjunction X W) g = free_vect_restrict g
  := eq_refl.

Lemma free_vect_restrict_extend {X : Sets} {W : Vct_F F}
  (h : X ~{Sets}~> Vct_Forget W) : free_vect_restrict (fv_extend h) ≈ h.
Proof. exact (fv_transpose_extend (field_ring F) h). Qed.

Lemma free_vect_extend_restrict {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) : fv_extend (free_vect_restrict g) ≈ g.
Proof. exact (fv_extend_transpose (field_ring F) g). Qed.

(** *** Naturality in the set variable *)
Theorem free_vect_naturality_in_set {X Y : Sets} {W : Vct_F F}
  (g : FreeVect Y ~{Vct_F F}~> W) (u : X ~{Sets}~> Y) :
  free_vect_restrict (g ∘ fmap[FreeVect] u) ≈ free_vect_restrict g ∘ u.
Proof. exact (free_module_naturality_in_set (field_ring F) g u). Qed.

(** *** Naturality in the target space *)
Theorem free_vect_naturality_in_space {X : Sets} {W W' : Vct_F F}
  (k : W ~{Vct_F F}~> W') (g : FreeVect X ~{Vct_F F}~> W) :
  free_vect_restrict (k ∘ g) ≈ fmap[Vct_Forget] k ∘ free_vect_restrict g.
Proof. exact (free_module_naturality_in_module (field_ring F) k g). Qed.

(** ** The triangle identities *)

Corollary free_vect_triangle_left (X : Sets) :
  free_vect_counit (FreeVect X) ∘ fmap[FreeVect] (free_vect_unit X)
    ≈ @id (Vct_F F) (FreeVect X).
Proof. exact (free_module_triangle_left (field_ring F) X). Qed.

Corollary free_vect_triangle_right (W : Vct_F F) :
  fmap[Vct_Forget] (free_vect_counit W)
    ∘ free_vect_unit (Vct_Forget W) ≈ @id Sets (Vct_Forget W).
Proof. exact (free_module_triangle_right (field_ring F) W). Qed.

(** ** Riehl's k[S]: every vector is a finite linear combination of basis
       vectors

    The half of the classical "finitely supported k-valued functions"
    description that does not need a decider on the generating setoid.
    Instance/Mod/Free.v's closing note says what the other half costs. *)
Theorem free_vect_finite_combination (X : Sets)
  (t : @FVTerm (field_ring F) X) :
  ∃ l : list (fv_pair (field_ring F) X), fv_eq t (fv_lc l).
Proof. exact (fv_normal_form t). Qed.

End FreeVect.

(* Only the one that changes anything: everything else discharged from
   the section already has [F] explicit. *)
Arguments free_vect_restrict {F X W} g.

(** ** The rational witness

    Two basis vectors over ℚ, and a target that is ℚ itself read as a
    one-dimensional ℚ-vector space.  The generating setoid is
    Instance/Mod/Free.v's [TwoGens] (bool under Leibniz equality),
    reused rather than rebuilt. *)

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — see the same device in Instance/Mod/Free.v. *)
Local Notation qgen  := (@fv_gen (field_ring Q_Field) TwoGens).
Local Notation qsmul := (@fv_smul (field_ring Q_Field) TwoGens).
Local Notation qplus := (@fv_plus (field_ring Q_Field) TwoGens).
Local Notation qzero := (@fv_zero (field_ring Q_Field) TwoGens).

(** ℚ as a vector space over itself. *)
Definition QLine : Vct_F Q_Field := Ring_RMod (field_ring Q_Field).

(** The assignment e₀ ↦ 3, e₁ ↦ 5. *)
Definition q_probe : TwoGens ~{Sets}~> Vct_Forget Q_Field QLine.
Proof.
  unshelve refine {| morphism := fun b : carrier TwoGens => if b then (3 # 1)%Q else (5 # 1)%Q |}.
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(** The linear extension computes: 2·e₀ + e₁ ↦ 2·3 + 5 = 11.  This is
    [eq_refl] on the CARRIER ℚ — the convertibility exception, not a
    statement about morphisms. *)
Example q_free_extend_computes :
  fv_eval q_probe (qplus (qsmul (2 # 1)%Q (qgen true)) (qgen false))
  = (11 # 1)%Q := eq_refl.

Example q_free_extend_generator_true :
  fv_eval q_probe (qgen true) = (3 # 1)%Q := eq_refl.

Example q_free_extend_generator_false :
  fv_eval q_probe (qgen false) = (5 # 1)%Q := eq_refl.

(* [TwoGens] and its distinctness are facts about the generating setoid
   alone, with no ring in them, so both come from Instance/Mod/Free.v
   ([two_gens_dec], [two_gens_distinct]) rather than being restated here. *)

(** *** The basis insertion does not collapse

    The [1 ≉ 0] premise of Instance/Mod/Free.v's general theorem is
    [field_one_neq_zero], a FIELD of [FieldObject], so over a field it
    costs nothing; only the decider is supplied. *)
Theorem free_vect_basis_distinct :
  fv_eq (qgen true) (qgen false) → False.
Proof.
  intro He.
  pose proof (free_module_basis_injective two_gens_dec
                (field_one_neq_zero Q_Field) true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

(** *** The basis is linearly independent

    The statement §III.1's reader wants: if r·e₀ + s·e₁ vanishes then
    both coefficients vanish.  Only the decider is spent — not
    [field_one_neq_zero] — and the reason none is needed is that over a
    trivial scalar ring every scalar is already 0, so the statement
    degenerates to a truth rather than to a falsehood.  Its content is
    therefore carried entirely by the nondegenerate case, which ℚ is. *)
Theorem free_vect_basis_independent (r s : Q) :
  fv_eq (qplus (qsmul r (qgen true)) (qsmul s (qgen false))) qzero →
  ((r == 0)%Q * (s == 0)%Q)%type.
Proof.
  exact (@free_module_two_independent (field_ring Q_Field) TwoGens
           two_gens_dec true false two_gens_distinct r s).
Qed.

(** *** Distinct scalars give distinct multiples of one basis vector

    With proper fractions, so that the scalars are visibly rational and
    not merely integers.  No decidability and no [1 ≉ 0] are spent here. *)
Theorem free_vect_half_not_one :
  fv_eq (qsmul (1 # 2)%Q (qgen true)) (qsmul (1 # 1)%Q (qgen true)) → False.
Proof.
  intro He.
  pose proof (@free_module_scalars_faithful (field_ring Q_Field) TwoGens
                (1 # 2)%Q (1 # 1)%Q true He) as Hq.
  compute in Hq; discriminate Hq.
Qed.
