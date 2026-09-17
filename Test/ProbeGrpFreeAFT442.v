(** * Probe for the free group read through Freyd (issue #442)

    Pins the measured boundaries of Instance/Grp/FreeAFT.v, whose header
    makes two negative claims of its own — the solution set fed to Freyd's
    theorem is circular, and Mac Lane's own index cannot be written at this
    instance IN THE TREE AS IT STANDS — beside the issue's QA claim.  All
    three are pinned below, but not all by refutations: the circularity is
    pinned by a POSITIVE [eq_refl], since what it asserts is an identity
    and not an absence.  CORRECTION, PR "algebraic carriers are sets"
    (2026-09-17): BOTH of those negative claims have since moved.  The
    circularity claim is now about a constant that is kept but no longer
    consumed (section A); the index claim turned over when
    Instance/Discrete.v was annotated, so what stood as N5 is now a
    positive control (section D).  An earlier revision of this paragraph
    ended "The second is pinned by N5, and N5 is expected to turn over —
    see the comment there", and the prediction held.

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
    [Subgroup G] (Instance/Grp/Quotient.v:177) is never there.  The control
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
    (Instance/Grp/Free.v:680) on the nose, while the two proofs are separate
    terms (N9) and the decision procedure is a real argument (N10).

    SECTION I, added by the PR "algebraic carriers are sets" (2026-09-17),
    covers what [free_group_via_GAFT] consumes SINCE that PR: the
    non-circular [Grp_Forget_solution_set_prop], indexed by the [Prop]
    congruences on [FGWord X].  The first paragraph of this header is
    therefore no longer the whole story, and section A carries the recorded
    correction: the circularity claims are now about
    [free_group_via_GAFT_from_adjunction], which is kept.  N13 there pins
    the one thing the unconditional reading costs, [Set < carrier], at a
    named in-tree object.

    KINDS, kept lexically apart: NAME-ABSENCE (the instrument), TYPE (I1,
    N3, N6, N7, N10), CONVERSION (N1, N2, N4, N8, N9, N11, N12), UNIVERSE
    (N13, twice).  CORRECTION: an earlier revision of this line read
    "UNIVERSE (N5) — twelve refutations in all", and both halves were
    stale.  N5 became a positive control when Instance/Discrete.v's
    annotation landed (see section D), and the count was never
    re-measured: the file carried ELEVEN [Fail] commands at that point and
    carries FIFTEEN now, by [grep -c '^Fail'].  Each was stripped one at a
    time in a copy of the WHOLE file and its exact refusal text recorded.
    The import list is the target's in full — including
    Lib/Setoid/Propositional.v, which section I names — plus
    Instance/Grp/Quotient.v for [Subgroup], which section D names. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
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

(** ** A: the CIRCULAR application, and the circularity read back

    RECORDED CORRECTION, PR "algebraic carriers are sets" (2026-09-17).
    Every statement in this section used to be about [free_group_via_GAFT],
    which consumed [Grp_Forget_solution_set_from_adjunction].  That constant
    is kept and is still circular, but the application built from it is now
    named [free_group_via_GAFT_from_adjunction], and this section is
    retargeted onto that name.  ONE LINE of the section changed, the
    four-argument readback below; the other five are statements about the
    solution set itself and compile verbatim.  Section I covers what
    [free_group_via_GAFT] consumes now. *)

(* The theorem is applied to exactly these four arguments. *)
Example p442_via_GAFT_is_GAFT :
  free_group_via_GAFT_from_adjunction
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
   minimization artifact of Instance/Discrete.v:81's unannotated
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
   restatement of Instance/Grp/Free.v:680. *)
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

(** ** I: the NON-CIRCULAR solution set, and the one thing it costs

    Added by the PR "algebraic carriers are sets" (2026-09-17), on the
    pattern of Test/ProbeRngAFTProp.v.  [free_group_via_GAFT] now consumes
    [Grp_Forget_solution_set_prop], the [Prop]-valued congruences on
    [FGWord X].  That change is INVISIBLE TO THE TYPE — the two readings
    inhabit the same statement, and nothing else in the build would notice
    it being reverted — so the [eq_refl] readbacks below name the congruence
    index, and N11 pins that the new index is not the old singleton.

    THE NEW REFUTATIONS ARE N11 (CONVERSION), N12 (CONVERSION) and N13
    (UNIVERSE), taking this file to fifteen.  Each was stripped in a copy of
    the WHOLE file and its exact refusal recorded beside it. *)

Check @IsGrpCongruence.
Check @FGCongIdx.
Check @QGrp_Setoid.
Check @QGrp.
Check @QGrp_insert.
Check @fg_ev.
Check @fg_ker.
Check @fg_ker_is_cong.
Check @fg_ker_idx.
Check @fg_ker_med.
Check @QGrpOf.
Check @QGrpInsertOf.
Check @Grp_Forget_solution_set_prop.
Check @free_group_via_GAFT_from_adjunction.
Check @free_group_monad_via_GAFT.

(* The four arguments of the UNCONDITIONAL application, the twin of
   [p442_via_GAFT_is_GAFT] above.  This is the line that would have to
   change if the circular family came back. *)
Example p442_via_GAFT_prop_is_GAFT :
  free_group_via_GAFT
    = GAFT Grp_Forget Grp_Complete
           (Continuous_PreservesImageLimit Grp_Forget_continuous)
           Grp_Forget_solution_set_prop := eq_refl.

Section PropSolutionReadbacks.

Context (X : Sets).

(* The index IS the congruence type, the members ARE the quotients, and the
   arrows ARE the insertion of generators into them. *)
Example p442_sol_prop_index :
  sol_index (Grp_Forget_solution_set_prop X) = FGCongIdx X := eq_refl.

Example p442_sol_prop_obj (i : FGCongIdx X) :
  sol_obj (Grp_Forget_solution_set_prop X) i = QGrp (`1 i) (`2 i) := eq_refl.

Example p442_sol_prop_arr (i : FGCongIdx X) :
  sol_arr (Grp_Forget_solution_set_prop X) i = QGrp_insert (`1 i) (`2 i)
  := eq_refl.

(* THE SIZE CLAIM, read back rather than argued: every member's carrier is
   the free group's own word type, so the family is a family of QUOTIENTS
   and not a family of arbitrary groups.  That is what keeps the index at
   the carrier universe. *)
Example p442_sol_prop_carrier (i : FGCongIdx X) :
  carrier (grp_setoid (sol_obj (Grp_Forget_solution_set_prop X) i)) = FGWord X
  := eq_refl.

(* The covering is the KERNEL of [free_grp_extend], on the nose. *)
Example p442_ker_idx_is_kernel (G : Grp) (h : X ~{Sets}~> Grp_Forget G) :
  `1 (fg_ker_idx h) = fg_ker h := eq_refl.

Example p442_ker_is_extension_kernel (G : Grp)
  (h : X ~{Sets}~> Grp_Forget G) (u v : FGWord X) :
  fg_ker h u v
    = @pequiv _ _ (grp_prop G) (fg_ev h u) (fg_ev h v) := eq_refl.

End PropSolutionReadbacks.

(** ** N11 (CONVERSION): the new index is not the old singleton

    If a later edit points [Grp_Forget_solution_set_prop] back at
    [solution_set_of_adjunction], this line stops refusing.  The control is
    [p442_sol_index] in section A, which IS [eq_refl] for the old one.
    Stripped in a copy of this WHOLE file and re-run, the refusal is

      In environment
      X : obj[Sets]
      The term "eq_refl" has type
       "sol_index (Grp_Forget_solution_set_prop X) =
        sol_index (Grp_Forget_solution_set_prop X)"
      while it is expected to have type
       "sol_index (Grp_Forget_solution_set_prop X) = poly_unit"
      (cannot unify "sol_index (Grp_Forget_solution_set_prop X)" and
      "poly_unit").

    Note that the message does NOT name [FGCongIdx]: the index is printed
    unreduced, so the readback [p442_sol_prop_index] above is what carries
    the positive half of the claim and this pins only the disagreement.
    Coq renders such a message with the short names in scope, so it is
    quoted together with the import list at the head of this file. *)

Fail Example p442_sol_prop_is_not_singleton (X : Sets) :
  sol_index (Grp_Forget_solution_set_prop X) = poly_unit := eq_refl.

(** ** N12 (CONVERSION): the two applications are different terms

    [free_group_via_GAFT] and [free_group_via_GAFT_from_adjunction] inhabit
    the same type and are NOT the same term.  [GAFT] is [Qed], so neither
    reduces; what this pins is that the two are not syntactically
    identified, which is what would happen if one were defined as the
    other.  Stripped in a copy of this WHOLE file, the refusal is

      The term "eq_refl" has type "free_group_via_GAFT = free_group_via_GAFT"
      while it is expected to have type
       "free_group_via_GAFT = free_group_via_GAFT_from_adjunction"
      (cannot unify "free_group_via_GAFT" and
      "free_group_via_GAFT_from_adjunction"). *)

Fail Example p442_two_applications_differ :
  free_group_via_GAFT = free_group_via_GAFT_from_adjunction := eq_refl.

(** ** The payoff: the theorem applied at named sets

    Before this PR these lines exhibited a free group obtained from an
    adjunction that had been assumed in order to obtain it. *)

Check (Grp_Forget_solution_set_prop SetOne).
Check (Grp_Forget_solution_set_prop TwoLetters).
Check (FGCongIdx SetOne).
Check (FGCongIdx TwoLetters).
Check (`1 free_group_via_GAFT SetOne).
Check (fg_ker_idx (fg_insert TwoLetters)).
Check (fg_ker_med (fg_insert TwoLetters)).

(** ** N13 (UNIVERSE): the one price, [Set < carrier], and WHERE it lands

    The index is a sigma over a [Prop]-valued relation; the sort of [Prop]
    is [Set+1]; identifying the index universe with the carrier universe
    therefore puts the carrier strictly above [Set].  Measured, [About]
    under [Set Printing Universes]:

      free_group_via_GAFT@{u u0 u1 u2 u3} :
        ∃ F : Sets@{u0 u} ⟶ Grp@{u u0}, F ⊣ Grp_Forget@{u u u0}
      (* … Set < u0 / u0 < u … *)

      free_group_via_GAFT_from_adjunction@{u … u8} :
        ∃ F : Sets@{u1 u0} ⟶ Grp@{u u1}, F ⊣ Grp_Forget@{u u0 u1}
      (* … Set < u / u1 < u / u1 < u0 … *)

    [About Sets] gives [Sets@{o so} : Category@{so o o}], so the first slot
    is the setoid CARRIER universe; [About Grp] gives
    [Grp@{u p} : Category@{u p p}] with [Set < u] and [p < u] built in.  So
    the circular form's [Set < u] is [Grp]'s own bound on its OBJECT
    universe and is free; the unconditional form's [Set < u0] is on the
    carrier and is not.

    WHERE IT LANDS, and this is the part worth pinning rather than stating:
    NOT on the solution set and NOT on the congruence index, both of which
    are fine with the carrier at [Set] (the two controls in
    [Section SetCarrierPin] below).  It lands on the APPLICATION, because
    that is where [GAFT] identifies the index universe with the carrier.

    Stripped in a copy of this WHOLE file and re-run, the refusal is

      In environment
      Xs : obj[Sets]
      The term "Xs" has type "obj[Sets@{pcar pobj}]"
      while it is expected to have type
       "obj[Sets@{<anon> <anon>}]"
      (universe inconsistency: Cannot enforce pcar = <anon> because pcar
      < <anon>).

    where each [<anon>] is a fresh file-local universe whose printed name
    carries the stripped copy's module name and a serial number, so the
    names themselves are not reproducible and are not quoted.  The
    load-bearing half is the last line: [pcar] is [Set] by the constraint
    above, and the application wants it strictly below the index. *)

Section SetCarrierPin.

Universes pcar pobj.
Constraint pcar = Set.

Context (Xs : obj[Sets@{pcar pobj}]).

(* CONTROL 1: the non-circular solution set itself elaborates with the
   carrier at [Set]. *)
Definition p442_prop_sols_at_set_carrier : SolutionSet Grp_Forget Xs :=
  Grp_Forget_solution_set_prop Xs.

(* CONTROL 2: and so does the circular application. *)
Definition p442_circular_app_at_set_carrier : obj[Grp] :=
  `1 free_group_via_GAFT_from_adjunction Xs.

(* THE NEGATIVE: the unconditional application does not. *)
Fail Definition p442_uncond_app_at_set_carrier : obj[Grp] :=
  `1 free_group_via_GAFT Xs.

End SetCarrierPin.

(* AND IT BITES AT A NAMED IN-TREE OBJECT, which is why it is a cost and
   not a formality.  [TwoLetters] (Instance/Grp/Free.v:630) is the bool
   setoid, and [bool : Set] pins its carrier universe there.  The circular
   application applies to it; the unconditional one is refused, measured by
   stripping this [Fail] in a copy of the WHOLE file:

     The term "TwoLetters" has type "SetoidObject"
     while it is expected to have type "obj[Sets]"
     (universe inconsistency: Cannot enforce Set = <anon> because Set <
     <anon>).

   [SetOne] is NOT affected — [poly_unit] is universe-polymorphic — which
   is why the [SetOne] line above is a control and not an accident.  THIS
   IS THE HONEST STATEMENT OF WHAT THE UNCONDITIONAL APPLICATION COSTS: it
   is total over [Sets] as a polymorphic category, and it does not apply to
   a setoid whose carrier is pinned at [Set].  [Grp_Forget_solution_set_prop
   TwoLetters] above is checked and DOES elaborate, so the restriction is
   the theorem's use of the index, not the solution set's. *)

Check (`1 free_group_via_GAFT_from_adjunction TwoLetters).

Fail Definition p442_uncond_at_two_letters : obj[Grp] :=
  `1 free_group_via_GAFT TwoLetters.
