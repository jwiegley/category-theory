(** * Probe for the free group read through Freyd (issue #442)

    Pins the measured boundaries of Instance/Grp/FreeAFT.v, whose header
    makes two negative claims of its own — the solution set fed to Freyd's
    theorem is circular, and Mac Lane's own index cannot be written at this
    instance IN THE TREE AS IT STANDS — beside the issue's QA claim.  All
    three are pinned below, but not all by refutations: the circularity is
    pinned by a POSITIVE [eq_refl], since what it asserts is an identity
    and not an absence.  The second is pinned by N5, and N5 is expected to
    turn over — see the comment there.

    THE HEADLINE BOUNDARY IS N1: [free_group_via_GAFT_agrees] is `≈` and
    NOTHING STRONGER.  [GAFT] is [Qed]-opaque, so the functor Freyd's
    theorem returns does not reduce to [FreeGrp] — not as a functor (N1),
    not at a single object (N2), and its adjunction is not even of the same
    TYPE as [free_group_adjunction] (N3).  The `≈` that does hold is
    [left_adjoint_iso], and the readback beside N1 shows that it is that
    generic lemma applied and nothing instance-specific.

    THE CIRCULARITY IS LITERAL, not rhetorical, and the readback that says
    so is positive: [Grp_Forget_solution_set_from_adjunction X] IS
    [solution_set_of_adjunction free_group_adjunction X] by [eq_refl], its
    member IS [FreeGrpObject X], and its arrow IS the unit of the very
    adjunction the theorem is meant to produce.  N4 sharpens the last one:
    the arrow is the UNIT, which agrees with [fg_insert] only pointwise (a
    different record), so even the circular solution set is not the
    insertion of generators on the nose.

    N5 is the universe claim, measured: at this application the solution
    set's index is squeezed onto [Set], and Mac Lane's own index
    [Subgroup G] (Instance/Grp/Quotient.v:156) is never there.  The control
    beside it is the same builder at a [Set]-level index ([bool]), which IS
    accepted — so the refusal is about the universe and not about the shape
    of the hypothetical.  N5 pins the REFUSAL, which is real; it does not
    pin a cause, and the cause is not [Grp_Complete] or [GAFT] — see the
    comment at N5 itself, and the target's header, which record what the
    [Set] actually comes from and what removing it would cost.  N5 is one
    of the eleven boundaries that a three-line annotation in
    Instance/Discrete.v would turn over.

    N6 and N7 pin which preservation hypothesis this instance owes: neither
    [Grp_Forget_continuous] ([ContinuousFunctor]) nor
    [Grp_Forget_PreservesAllLimits] (the apex-only class) ascribes where
    [GAFT] asks for the cone-level [PreservesImageLimit], which is why the
    [Continuous_PreservesImageLimit] bridge stands in the term.  N8 records
    that the induced monad's multiplication inherits the counit's opacity:
    [Grp_Forget]'s image of the counit does not reduce to word evaluation,
    which Instance/Grp/Free.v proves only up to `≈`.

    NON-VACUITY IS CARRIED BY TWO THEOREMS, not by refutations.
    [p442_repr_separates] shows the representation distinguishes the two
    elements of [Z2] — a constant or otherwise degenerate transformation
    could not, since the round trip [grp_repr_to ∘ grp_repr_from] is the
    identity — and [p442_repr_obj_not_trivial] upgrades that to: the
    representing object is not isomorphic to the trivial group.  Without
    these the representability clause would be satisfied by the one-element
    group and would say nothing.

    SECTION H, added after the rest, covers the target's injectivity clause:
    that the general result's statement IS the tree's own two-letter one
    (Instance/Grp/Free.v:586) on the nose, while the two proofs are separate
    terms (N9) and the decision procedure is a real argument (N10).

    KINDS, kept lexically apart: NAME-ABSENCE (the instrument), TYPE (I1,
    N3, N6, N7, N10), CONVERSION (N1, N2, N4, N8, N9), UNIVERSE (N5) —
    twelve refutations in all.  Each was stripped one at a time in a copy
    of the WHOLE file and its exact refusal text recorded.  The import list
    is the target's in full, plus Instance/Grp/Quotient.v for [Subgroup],
    which N5 names. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.FreeAFT.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe442_absent_name.

(* I1 instrument, second kind: elaboration is really happening.  This is
   the deliberately ill-typed variant of [p442_repr_obj] below, which DOES
   hold — the representing object is an object of [Grp], and asking for it
   to be the singleton SETOID is a type error, not a conversion one. *)
Fail Example p442_instrument :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable = SetOne := eq_refl.

(** ** A: the application, and the circularity read back *)

(* The theorem is applied to exactly these four arguments. *)
Example p442_via_GAFT_is_GAFT :
  free_group_via_GAFT
    = GAFT Grp_Forget Grp_Complete
           (Continuous_PreservesImageLimit Grp_Forget_continuous)
           Grp_Forget_solution_set_from_adjunction := eq_refl.

(* THE CIRCULARITY, as an [eq_refl].  The third hypothesis fed to Freyd's
   theorem is the singleton family at the unit of the adjunction the
   theorem is meant to produce. *)
Example p442_solution_set_is_circular (X : Sets) :
  Grp_Forget_solution_set_from_adjunction X
    = solution_set_of_adjunction free_group_adjunction X := eq_refl.

Example p442_sol_index (X : Sets) :
  sol_index (Grp_Forget_solution_set_from_adjunction X) = poly_unit := eq_refl.

(* ...and the single member is the word group already in tree. *)
Example p442_sol_obj (X : Sets) (i : poly_unit) :
  sol_obj (Grp_Forget_solution_set_from_adjunction X) i = FreeGrpObject X
  := eq_refl.

Example p442_sol_arr (X : Sets) (i : poly_unit) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i = free_group_unit X
  := eq_refl.

(* control for N4: the arrow and the insertion of generators agree at every
   point, which is Instance/Grp/Free.v's [free_group_unit_is_insert]. *)
Example p442_sol_arr_pointwise (X : Sets) (i : poly_unit) (a : carrier X) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i a = fg_insert X a
  := eq_refl.

(* N4 CONVERSION: but they are not the same MORPHISM.  The unit is
   [fmap[U] id ∘ arrow] and carries its own respectfulness proof; the
   solution set is built from the unit, not from [fg_insert]. *)
Fail Example p442_sol_arr_is_insert (X : Sets) (i : poly_unit) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i = fg_insert X
  := eq_refl.

(** ** B: the QA clause is `≈`, and only `≈` *)

(* control: the agreement that IS delivered... *)
Check (free_group_via_GAFT_agrees : `1 free_group_via_GAFT ≈ FreeGrp).

(* ...and it is [left_adjoint_iso] applied, nothing instance-specific. *)
Example p442_agrees_is_generic :
  free_group_via_GAFT_agrees
    = left_adjoint_iso Grp_Forget _ FreeGrp (`2 free_group_via_GAFT)
                       free_group_adjunction := eq_refl.

(* N1 CONVERSION: the two functors are NOT convertible.  [GAFT] is
   [Qed]-opaque, so its output does not reduce at all. *)
Fail Example p442_gaft_output_is_FreeGrp :
  `1 free_group_via_GAFT = FreeGrp := eq_refl.

(* N2 CONVERSION: nor at a single object — not even at the singleton, where
   the free group is the one-generator group the representation uses. *)
Fail Example p442_gaft_output_obj :
  `1 free_group_via_GAFT SetOne = FreeGrpObject SetOne := eq_refl.

(* N3 TYPE: and the two adjunctions are not comparable by [=] at all, their
   left legs being different terms. *)
Fail Example p442_gaft_adjunction_is_free :
  `2 free_group_via_GAFT = free_group_adjunction := eq_refl.

(** ** C: which hypotheses this instance owes *)

(* control: the application, again, as a [Check] *)
Check (GAFT Grp_Forget Grp_Complete
            (Continuous_PreservesImageLimit Grp_Forget_continuous)
            Grp_Forget_solution_set_from_adjunction).

(* N6 TYPE: [ContinuousFunctor] is not [PreservesImageLimit] — the bridge
   in the target's term is load-bearing. *)
Fail Check (GAFT Grp_Forget Grp_Complete Grp_Forget_continuous
                 Grp_Forget_solution_set_from_adjunction).

(* N7 TYPE: neither is the apex-only class, which Instance/Grp/Limit.v also
   supplies and which is the tempting wrong choice. *)
Fail Check (GAFT Grp_Forget Grp_Complete Grp_Forget_PreservesAllLimits
                 Grp_Forget_solution_set_from_adjunction).

(** ** D: UNIVERSE — why Mac Lane's own solution set cannot be written here

    The header's second reason for not using the subgroups generated by the
    image.  [SolutionSet]'s index is [Type@{u}] with [u] free — the record
    carries an empty constraint set — but at this application it is
    squeezed onto the literal [Set], and [Subgroup G] is never there. *)

Definition p442_GAFT_at_Grp :=
  GAFT Grp_Forget Grp_Complete
       (Continuous_PreservesImageLimit Grp_Forget_continuous).

(* A solution-set builder over an arbitrary index, so that the pair below
   differs in the index type and in nothing else. *)
Definition p442_sols_indexed_by (I : Type)
  (o : ∀ X : Sets, I → Grp)
  (a : ∀ (X : Sets) (i : I), X ~{Sets}~> Grp_Forget (o X i))
  (cov : ∀ (X : Sets) (c : Grp) (h : X ~{Sets}~> Grp_Forget c),
      { i : I & { t : o X i ~{Grp}~> c & fmap[Grp_Forget] t ∘ a X i ≈ h } })
  (X : Sets) : SolutionSet Grp_Forget X :=
  {| sol_index := I
   ; sol_obj := o X
   ; sol_arr := a X
   ; sol_covers := fun c h => cov X c h |}.

(* control: at a [Set]-level index the builder's output IS what [GAFT]
   consumes at this instance. *)
Check (fun o a cov =>
         p442_GAFT_at_Grp (p442_sols_indexed_by bool o a cov)).

(* Former N5, now a positive control: Mac Lane's index is accepted.

   RECORDED CORRECTION.  An earlier revision read: "N5 UNIVERSE: at Mac
   Lane's index it is refused.  WHAT THIS DOES AND DOES NOT PIN.  It pins
   the refusal, in the tree as it stands.  It does NOT pin a cause, and an
   earlier revision of the target's header attributed the cause to [GAFT]
   and [Grp_Complete], which is wrong: the [Set] is a universe-
   minimization artifact of Instance/Discrete.v:59's unannotated
   [DiscreteCat_Functor], reaching GAFT's statement through GAFT.v:249,
   and [Grp_Complete] only transmits it.  Annotating that one donor —
   three lines, no [Qed]-opaque term touched — makes this very [Check]
   succeed, so THIS REFUTATION IS EXPECTED TO TURN OVER when
   Instance/Discrete.v's follow-on lands.  It is one of eleven such
   boundaries in the tree (Instance/Cat/Objects.v:747,
   Structure/Limit/Components.v:1166 and nine Test/Probe* lines); measured
   2026-09-12 in a full copy of this worktree, that annotation breaks no
   proof anywhere in the 977-file build set and turns over exactly those
   eleven and nothing else."

   The cause was diagnosed correctly and the prediction held.  The
   annotation landed in the PR "algebraic carriers are sets"
   (2026-09-17): [DiscreteCat_Functor@{o h p uo uh up +}], now
   Instance/Discrete.v:81, and this line is ACCEPTED.  It is kept at Mac
   Lane's own index [Subgroup G] as a positive control, so dropping the
   annotation refuses it again and breaks this file.

   TWO FIGURES IN THAT PARAGRAPH WERE STALE AND ARE CORRECTED HERE.  The
   build set was 977 files when the prediction was measured; it was 1018
   when the annotation landed.  And the boundary count "eleven" was never
   enumerated: the flip set measured by building the annotated tree is
   TWENTY-TWO commands in FIFTEEN files.  Seven of them are outside
   [Test/] — two in Instance/Cat/Objects.v, two in
   Structure/Limit/Components.v and three in Instance/Indiscrete.v — and
   fifteen are in twelve [Test/Probe*] files: ProbeCommaCreation438,
   ProbeComparison419 (2), ProbeComponents355 (2), ProbeConeSets407 (2),
   ProbeDualNoRightAdjoint433, ProbeFreyd423, ProbeFromProducts416,
   ProbeGAFTCharacterization436, ProbeHomLimit331, ProbeModTensorAFT449,
   ProbeSpanningArrow448, and this file.

   TWO OF THE TWENTY-TWO WOULD HAVE GONE ON PASSING VACUOUSLY, and that is
   worth recording separately.  Instance/Cat/Objects.v and
   Instance/Indiscrete.v each wrote their [Indiscrete] negative as
   [Indiscrete@{uo}], a ONE-universe instance.  Annotating [Indiscrete] as
   [Indiscrete@{o h p}] makes that an arity error — "Universe instance
   length for Indiscrete is 1 but should be 3", measured — so the [Fail]
   would have stayed green while the boundary it guarded was gone.  Both
   were rewritten with all three levels before being turned over.

   The remaining claim held exactly: no proof anywhere in the tree broke,
   and the full build is rc=0. *)
Check (fun (G : Grp) o a cov =>
         p442_GAFT_at_Grp (p442_sols_indexed_by (Subgroup G) o a cov)).

(** ** E: the induced monad *)

Example p442_ret_is_unit (X : Sets) :
  @ret Sets _ free_group_monad X = free_group_unit X := eq_refl.

Example p442_ret_generator (X : Sets) (a : carrier X) :
  @ret Sets _ free_group_monad X a = fg_insert X a := eq_refl.

Example p442_join_is_counit (X : Sets) :
  @join Sets _ free_group_monad X
    = fmap[Grp_Forget] (free_group_counit (FreeGrp X)) := eq_refl.

Example p442_monad_functor_obj (X : Sets) :
  fobj[Grp_Forget ◯ FreeGrp] X = grp_setoid (FreeGrpObject X) := eq_refl.

(* N8 CONVERSION: the multiplication inherits the counit's opacity.
   Instance/Grp/Free.v records that the counit is [unique_obj] of
   [ump_universal_arrows], which is [Qed]-sealed (Theory/Universal/Arrow.v:139,
   closed at :153), so nothing on this side reduces; the agreement with word
   evaluation is [free_group_counit_evaluates], up to `≈` and no more. *)
Fail Example p442_join_is_word_evaluation (X : Sets) :
  @join Sets _ free_group_monad X
    = fmap[Grp_Forget]
        (free_grp_extend (@id Sets (Grp_Forget (FreeGrp X)))) := eq_refl.

(** ** F: the representation, and that it is not degenerate *)

Example p442_repr_obj :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable = FreeGrp SetOne
  := eq_refl.

Example p442_repr_obj_word :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable
    = FreeGrpObject unit_setoid_object := eq_refl.

Example p442_repr_to_component (G : Grp) (f : FreeGrp SetOne ~{Grp}~> G) :
  transform[to (@represented Grp Grp_Forget Grp_Forget_Representable)] G f
    = grp_repr_to G f := eq_refl.

Example p442_repr_from_component (G : Grp) (a : carrier (Grp_Forget G)) :
  transform[from (@represented Grp Grp_Forget Grp_Forget_Representable)] G a
    = grp_repr_from G a := eq_refl.

Example p442_repr_to_is_transpose (G : Grp) (f : FreeGrp SetOne ~{Grp}~> G) :
  grp_repr_to G f = to (grp_adj G) f ttt := eq_refl.

(* The round trip, which is what a degenerate transformation could not
   supply: reading an element back off the homomorphism it names returns
   that element. *)
Lemma p442_repr_to_from (G : Grp) (a : carrier (Grp_Forget G)) :
  grp_repr_to G (grp_repr_from G a) ≈ a.
Proof. exact (iso_to_from (grp_adj G) (grp_repr_const G a) ttt). Qed.

(* NON-VACUITY, first theorem: the representation SEPARATES the two
   elements of [Z2].  A constant transformation into [Hom(FreeGrp 1, Z2)]
   would give one homomorphism for both, so this is a statement no
   degenerate representation could carry. *)
Theorem p442_repr_separates :
  grp_repr_from Z2 true ≈ grp_repr_from Z2 false → False.
Proof.
  intro H.
  apply Z2_nontrivial.
  transitivity (grp_repr_to Z2 (grp_repr_from Z2 true)).
  - symmetry; exact (p442_repr_to_from Z2 true).
  - transitivity (grp_repr_to Z2 (grp_repr_from Z2 false)).
    + exact (proper_morphism (to (grp_adj Z2)) _ _ H ttt).
    + exact (p442_repr_to_from Z2 false).
Qed.

(* NON-VACUITY, second theorem: hence the representing object is not the
   trivial group.  Every pair of homomorphisms out of [Grp_trivial] is
   identified ([Grp_zero_hom_unique]), so an isomorphism with it would
   collapse the two homomorphisms the previous theorem keeps apart. *)
Theorem p442_repr_obj_not_trivial :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable ≅[Grp] Grp_trivial
    → False.
Proof.
  intro i.
  apply p442_repr_separates.
  transitivity (grp_repr_from Z2 true ∘ (from i ∘ to i)).
  - rewrite iso_from_to; rewrite id_right; reflexivity.
  - transitivity (grp_repr_from Z2 false ∘ (from i ∘ to i)).
    + rewrite !comp_assoc.
      rewrite (Grp_zero_hom_unique Z2
                 (grp_repr_from Z2 true ∘ from i)
                 (grp_repr_from Z2 false ∘ from i)).
      reflexivity.
    + rewrite iso_from_to; rewrite id_right; reflexivity.
Qed.

(** ** G: guard block *)

Check @Grp_Forget_solution_set_from_adjunction.
Check @free_group_via_GAFT.
Check @free_group_via_GAFT_agrees.
Check @free_group_monad.
Check @grp_repr_const.
Check @grp_repr_to.
Check @grp_repr_from.
Check @grp_repr_to_natural.
Check @grp_repr_from_natural.
Check @Grp_Forget_Representable.
Check @GAFT.
Check @SolutionSet.
Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @sol_covers.
Check @solution_set_of_adjunction.
Check @Continuous_PreservesImageLimit.
Check @Adjunction_Induced_Monad.
Check @left_adjoint_iso.
Check @Representable.
Check @repr_obj.
Check @represented.
Check @Grp.
Check @Grp_Forget.
Check @Grp_Complete.
Check @Grp_Forget_continuous.
Check @Grp_Forget_PreservesAllLimits.
Check @Grp_trivial.
Check @Grp_zero_hom_unique.
Check @Z2.
Check @Z2_nontrivial.
Check @Subgroup.
Check @FreeGrp.
Check @FreeGrpObject.
Check @free_group_adjunction.
Check @free_group_unit.
Check @free_group_counit.
Check @free_grp_extend.
Check @fg_insert.
Check @unit_setoid_object.

Check @p442_GAFT_at_Grp.
Check @p442_sols_indexed_by.
Check @p442_repr_to_from.
Check @p442_repr_separates.
Check @p442_repr_obj_not_trivial.

(** ** H: the injectivity clause

    Added after the sections above: the target grew Mac Lane's injectivity
    clause, and the tree already had its two-letter case.  What is pinned
    here is that the general statement really does COVER the special one —
    same statement, on the nose — while remaining a separate proof. *)

(* The corollary's statement is the tree's own, converted: [free_group_unit]
   IS [fg_insert] at a generator, so the general result is not a weaker
   restatement of Instance/Grp/Free.v:586. *)
Example p442_two_letters_same_statement :
  (free_group_unit TwoLetters true ≈ free_group_unit TwoLetters false → False)
  = (fg_insert TwoLetters true ≈ fg_insert TwoLetters false → False)
  := eq_refl.

(* N9 CONVERSION: ...but not the same PROOF.  Both are [Qed]-sealed and
   they take different routes — S3 in tree, Z/2 here — so neither reduces
   to the other.  This is what keeps them independent rather than one being
   an alias of the other. *)
Fail Example p442_two_letters_same_proof :
  free_group_two_letters_distinct = free_group_two_generators_distinct
  := eq_refl.

(* N10 TYPE: the decision procedure is a real argument, not an inferable
   one.  Dropping it leaves the two elements where [SetoidDecidable X] is
   expected. *)
Fail Check (fun (X : Sets) (a b : carrier X) =>
              free_group_unit_injective_dec (X:=X) a b).

Check @free_group_transpose_at_unit.
Check @free_group_unit_injective_of_embedding.
Check @free_group_unit_injective_dec.
Check @free_group_two_letters_distinct.
Check @free_group_two_generators_distinct.
Check @SetoidDecidable.
Check @grp_chi.
Check @TwoLetters.
