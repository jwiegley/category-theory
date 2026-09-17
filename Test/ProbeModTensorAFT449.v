Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Instance.Mod.TensorAFT.
Require Import Category.Theory.Algebra.Rig.
(* Beyond the target's own list: [Adjunction.GAFT] and [GAFT.Resize] for
   the [SolutionSet]/[SmallUpToIso] vocabulary section 10 of the target
   uses, and [Instance.Rng] for [Q_Ring], the SECOND concrete ring the
   payoff section below instantiates at. *)
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Resize.
Require Import Category.Instance.Rng.

(** * Probe for issue #449: the tensor product from the adjoint functor
      theorem (Mac Lane §V.7, book p. 128)

    The import list above is Instance/Mod/TensorAFT.v's own, verbatim, plus
    that file itself; a shorter prefix is what makes a probe pass for no
    reason.

    DISCIPLINE.  Quoted refusals below have their generated universe names
    replaced by readable ones ([u_obj], [u_Sets], [u_obj'], [u_Sets'],
    [u]): the real messages carry names like [S165.1055] that are
    file-name dependent and would not survive a rename.  The substitution
    is positional and everything else in a quoted message is verbatim.
    Every negative below is paired with a positive control
    naming the same library constants, the instrument was checked (a
    refusal expected around a command that succeeds stops the file), and
    each negative was re-run alone with its guard stripped IN A COPY OF THE
    WHOLE FILE so that the refusal kind could be read off the message
    rather than guessed.  The refusal kinds recorded are UNIVERSE (four),
    CONVERSION (two) and ARGUMENT NAME (one), beside the instrument check,
    whose refusal is a missing NAME.

    WHAT THE UNIVERSE NEGATIVES PIN.  Mac Lane's covering family -- the
    bilinear maps that span their target -- is a sigma over the OBJECTS of
    [RMod R], and [representability_theorem] demands an index at the ring's
    CARRIER universe.  Since a module's carrier sits strictly below the
    universe its objects live at, the two cannot meet.  That is a wall of
    the same FAMILY as the one Instance/Grp/FreeAFT.v reports at [Grp],
    whose donor is a universe-minimization artifact of
    Instance/Discrete.v's [DiscreteCat_Functor] and whose repair is filed
    as #1309 -- but it is NOT the same wall, and #1309 is measured not to
    lift it: applying that repair removed the literal [Set] from the
    refusals below and left the refusals themselves standing, as the
    index-universe = carrier-universe identification.
    Instance/Mod/TensorAFT.v's section 2 records that measurement.

    RECORDED CORRECTION, PR "algebraic carriers are sets" (2026-09-17).
    Two clauses of the paragraph above were true when written and are not
    now.  (i) "which it also pins to [Set]" -- the literal [Set] went with
    the annotation of [DiscreteCat_Functor], and every quoted refusal
    below has been re-measured without it.  (ii) The heading said FOUR
    universe negatives; there are now THREE, NEGATIVE 4 having become a
    positive control, plus the NEW negative 8 below, which pins the side
    condition the unconditional construction introduces.

    AND WHAT THE WALL DOES NOT STOP, which is the point of this PR.  The
    wall is about ONE index -- the sigma over objects.  A DIFFERENT
    solution set for the same functor, indexed by the [Prop]-valued
    congruences on the term module, sits AT the carrier universe and the
    theorem accepts it.  So [tensor_via_AFT] is now unconditional, and the
    payoff section below exhibits it at [Int_Ring], at [Q_Ring] and at the
    opposite ring.  NEGATIVES 1-3 are unaffected: they are statements
    about the object-indexed family, which nothing here moves. *)

(** ** Instrument check *)

(* A refusal expected around a name that is not there.  If the instrument
   were inert this line would pass silently and so would everything below
   it. *)
Fail Check zzz_no_such_constant_449.

(** ** Positive controls: every library constant a negative names *)

Section Controls.

Context {R : RingObject}.
Context (V V' : RModObject R).

Check (RMod_Complete R).
Check (Bilin_continuous V V').
Check (Bilin_PreservesImageLimit V V').
Check (tensor_esols_direct V V').
Check (tensor_esols_from_tensor V V').
Check (Bilin_PreservesWidePullbacks V V').
Check (RMod_HasWidePullbacks R).
Check (TensorMod V V').
Check (@tensor_gen R V V').
Check (tensor_repr_of_UE V V').
Check (preserves_image_of_representable (tensor_repr_of_UE V V')).
Check (@SpanningArrowsOutOf (RMod R) Sets (Bilin V V') SetsOne).

(* The three [eq_refl] readbacks of the direct solution set, as controls. *)
Example c_esol_index :
  esol_index (tensor_esols_direct V V')
    = SpanningArrowsOutOf (Bilin V V') SetsOne := eq_refl.

Example c_esol_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj (tensor_esols_direct V V') i = `1 i := eq_refl.

Example c_esol_elem (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem (tensor_esols_direct V V') i = `1 (`2 i) ttt := eq_refl.

(* The conditional solution set of Instance/Mod/Spanning.v shares that
   index on the nose.  [HWP] is passed EXPLICITLY: the exported instance
   [RMod_HasWidePullbacks] would be found by resolution and then refused at
   the application, for the universe reason that file records. *)
Example c_same_index (HWP : @HasWidePullbacks (RMod R)) :
  esol_index (@tensor_esols R V V' HWP)
    = esol_index (tensor_esols_direct V V') := eq_refl.

(* The representation read off the explicit tensor keeps [TensorMod] as its
   representing object at [eq_refl] -- the control the CONVERSION negative
   below is measured against. *)
Example c_repr_of_UE_obj :
  @repr_obj (RMod R) (Bilin V V') (tensor_repr_of_UE V V') = TensorMod V V'
  := eq_refl.

End Controls.

Section AbControls.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Check (BalBiadd N M).
Check (BalBiadd_continuous N M).
Check (BalBiadd_PreservesImageLimit N M).
Check (bal_esols_direct N M).
Check (bal_esols_from_tensor N M).
Check Ab_Complete.
Check (BalTensor N M).
Check (@bal_gen X N M).

Example c_bal_ue_obj :
  @ue_obj Ab (BalBiadd N M) (bal_UniversalElement N M) = BalTensor N M
  := eq_refl.

Example c_bal_ue_elem :
  @ue_elem Ab (BalBiadd N M) (bal_UniversalElement N M) = @bal_gen X N M
  := eq_refl.

Example c_bal_esol_index :
  esol_index (bal_esols_direct N M)
    = SpanningArrowsOutOf (BalBiadd N M) SetsOne := eq_refl.

End AbControls.

(* The two applications the negatives below sit beside, at an unconstrained
   ring: these ARE accepted, so the negatives are about the argument, not
   about the theorem being unusable. *)
Check (fun (R : RingObject) (V V' : RModObject R) => tensor_via_AFT V V').
Check (fun (R : RingObject) (V V' : RModObject R) =>
         module_tensor_universal V V').
(* the issue's verification name IS the AFT universal element, by definition *)
Example c_alias_is_ue : @module_tensor_universal = @tensor_AFT_ue := eq_refl.
Check (fun (R : RingObject) (V V' : RModObject R) =>
         tensor_via_AFT_from_tensor V V').
Check (fun (X : RingObject) (N : RModObject (Ring_op X))
           (M : RModObject X) => bal_tensor_via_AFT N M).

(** ** THE PAYOFF: the construction is unconditional, and here it is at
       three named rings

    RECORDED CORRECTION.  Every [Check] in this section would have been
    ill-typed before the PR "algebraic carriers are sets" (2026-09-17):
    [tensor_via_AFT] took a solution set as an argument, and the only
    in-tree inhabitants of that argument were the two CIRCULAR ones.  The
    file's own "NOT DELIVERED (5) NO CONCRETE WITNESS" said so.  These
    lines are what makes the removal of that clause checkable: if the
    hypothesis ever comes back, they stop compiling. *)

Section UnconditionalPayoff.

(* The tensor product of the integers with themselves as a Z-module,
   obtained from the adjoint functor theorem with NO hypothesis. *)
Check (tensor_via_AFT Int_RMod Int_RMod).
Check (module_tensor_universal Int_RMod Int_RMod).
Check (tensor_AFT_iso Int_RMod Int_RMod).
Check (tensor_AFT_ue Int_RMod Int_RMod).

(* Mac Lane's OWN p. 128 family, resized by his Lemma 2 (section 10 of the
   target), at the same ring: the second, book-faithful route. *)
Check (tensor_via_AFT_maclane Int_RMod Int_RMod).
Check (tensor_spanning_SmallUpToIso Int_RMod Int_RMod).
Check (tensor_esols_resized Int_RMod Int_RMod).

(* A SECOND ring, and a genuinely different one: the rationals. *)
Definition p449_QMod : RModObject Q_Ring := Ring_RMod Q_Ring.
Check (tensor_via_AFT p449_QMod p449_QMod).
Check (tensor_via_AFT_maclane p449_QMod p449_QMod).

(* A THIRD: the opposite ring of the integers, which is what Exercise 3's
   balanced tensor needs on the left. *)
Definition p449_OpMod : RModObject (Ring_op Int_Ring) :=
  Ring_RMod (Ring_op Int_Ring).
Check (tensor_via_AFT p449_OpMod p449_OpMod).

(* Exercise 3 at the integers, also unconditional. *)
Check (bal_tensor_via_AFT p449_OpMod Int_RMod).
Check (bal_AFT_iso p449_OpMod Int_RMod).
Check (bal_AFT_ue p449_OpMod Int_RMod).
Check (bal_esols_prop p449_OpMod Int_RMod).

End UnconditionalPayoff.

(** ** The two indices, read back at [eq_refl]

    The whole repair is one inequality between two index universes, and
    these pin WHICH two types the indices are.  The measured universe
    readbacks that go with them, [About] under [Set Printing Universes],
    are in Instance/Mod/TensorAFT.v's section 3A: the congruence index
    takes [u4 := u0], the ring's carrier universe, while
    [tensor_esols_direct]'s gives [u0 < u12].  An [About] is not a
    command a probe can guard, so the types are pinned here and the
    universes are pinned by NEGATIVE 1 (the direct family is refused) and
    by the payoff section above (the congruence family is not). *)

Section IndexReadbacks.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

Example p449_prop_index :
  esol_index (tensor_esols_prop V V') = CongIdx V V' := eq_refl.

Example p449_prop_obj (i : CongIdx V V') :
  esol_obj (tensor_esols_prop V V') i = QMod (`1 i) (`2 i) := eq_refl.

Example p449_prop_elem (i : CongIdx V V') :
  esol_elem (tensor_esols_prop V V') i = QMod_gen (`1 i) (`2 i) := eq_refl.

(* Mac Lane's Lemma 2: the SMALL index of the resized family is the same
   congruence type. *)
Example p449_maclane_small_index :
  si_carrier (tensor_spanning_SmallUpToIso V V') = CongIdx V V' := eq_refl.

Example p449_resized_index :
  esol_index (tensor_esols_resized V V') = CongIdx V V' := eq_refl.

(* And the direct family's index is still the sigma over objects -- the
   one NEGATIVE 1 refuses. *)
Example p449_direct_index :
  esol_index (tensor_esols_direct V V')
    = SpanningArrowsOutOf (Bilin V V') SetsOne := eq_refl.

End IndexReadbacks.

Section BalIndexReadbacks.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Example p449_bal_prop_index :
  esol_index (bal_esols_prop N M) = BalCongIdx N M := eq_refl.

Example p449_bal_prop_obj (i : BalCongIdx N M) :
  esol_obj (bal_esols_prop N M) i = QBal (`1 i) (`2 i) := eq_refl.

End BalIndexReadbacks.

(** ** NEGATIVE 1 (UNIVERSE): Mac Lane's covering family is refused

    RE-MEASURED 2026-09-17, after [DiscreteCat_Functor] was annotated
    (Instance/Discrete.v:81, PR "algebraic carriers are sets").  Stripped
    and re-run in a copy of the whole file, the message is now

      The term "tensor_esols_direct V V'" has type
       "ElementSolutionSet@{u_idx u_carrier u_Sets u_idx} (Bilin ... V V')"
      while it is expected to have type
       "ElementSolutionSet@{u_idx' u_carrier u_Sets' u_carrier}
          (Bilin ... V V')"
      (universe inconsistency: Cannot enforce u_idx' = u_carrier because
       u_carrier < u_idx')

    (the generated universe names are rewritten to readable ones; the
    shape, the slots and the final clause are verbatim).

    RECORDED CORRECTION.  An earlier revision quoted this as

      "ElementSolutionSet@{u_obj Set u_Sets u_obj}" against
      "ElementSolutionSet@{u_obj' Set u_Sets' Set}"
      (universe inconsistency: Cannot enforce Set = u_obj' because
       Set < u_obj')

    and glossed it "the INDEX slot (fourth) must be [Set], the ring's
    carrier universe".  THE LITERAL [Set] IS GONE; the gloss was right
    about everything else and is now stated without it: the index slot
    must be the RING'S CARRIER universe, while the index actually supplied
    is a sigma over the objects of [RMod R], one level up.  This is why
    [tensor_via_AFT] takes its solution set as a hypothesis, and the
    reason is a carrier-versus-index wall, not a [Set] floor. *)

Fail Definition n1_direct_esols_refused {R : RingObject}
  (V V' : RModObject R) : Representable (Bilin V V') :=
  representability_theorem (Bilin V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V') (tensor_esols_direct V V').

(** ** NEGATIVE 2 (UNIVERSE): the spanning-arrow route is refused too

    RE-MEASURED 2026-09-17, a SECOND time, after [Section GAFTFromSpanning]
    was widened off [Set] in the PR "algebraic carriers are sets".
    Stripped and re-run in a copy of this whole file, the message is now

      The term "RMod R" has type "Category@{u_obj u_hom u_hom}"
      while it is expected to have type "Category@{u_obj' u_hom' u_hom'}"
      (universe inconsistency: Cannot enforce u_hom = u_hom' because
       u_hom < u_obj <= u_hom')

    -- NO literal [Set] anywhere, and a longer chain in the final clause.

    TWO RECORDED CORRECTIONS, in the order they happened.

    (a) The FIRST revision of this probe quoted

      The term "RMod_Complete R" has type
       "Complete.Complete@{Set Set Set u}"
      while it is expected to have type
       "Complete.Complete@{u_obj u_obj Set u_obj}"
      (universe inconsistency: Cannot enforce Set = u_obj because
       Set < u_obj)

    and the refusal then moved EARLIER, to the ambient category argument,
    when [DiscreteCat_Functor] was annotated (Instance/Discrete.v:81).

    (b) The SECOND revision quoted the category refusal with the expected
    type written "Category@{u_obj' Set Set}" and the clause "Cannot
    enforce u_obj = u_obj' because u_obj' < u_obj", and attributed that
    remaining [Set] to [GAFT_from_spanning]'s OWN section annotation.  THE
    ATTRIBUTION WAS CORRECT AND THE ANNOTATION IS NOW GONE: the section is
    declared over bare categories and the theorem reads
    [Category@{u u0 u0}] / [Category@{u1 u2 u2}] with [u <= u0].  The
    refusal SURVIVES the widening, and the new clause says exactly why --
    the widened theorem wants objects at or below homs, and [RMod R] has
    homs strictly below objects.

    The gloss stands, with the [Set] dropped from it: [spanning_solution_
    set]'s index is at the object universe, so the discrete shape [GAFT]
    takes a limit over is too, while [RMod R]'s homs are below its
    objects.  [GAFT_from_spanning] is therefore still NOT applicable at
    [RMod R], and Instance/Mod/TensorAFT.v still delivers no adjunction --
    what it now delivers unconditionally is a REPRESENTATION, through
    [representability_theorem] and a different solution set. *)

Fail Definition n2_gaft_from_spanning_refused {R : RingObject}
  (V V' : RModObject R) (HWP : @HasWidePullbacks (RMod R)) :=
  @GAFT_from_spanning (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V').

(** ** NEGATIVE 3 (UNIVERSE): the same at [Ab], for Exercise 3

    RE-MEASURED 2026-09-17.  Stripped and re-run, the message is now

      The term "bal_esols_direct N M" has type
       "ElementSolutionSet@{u_idx u_carrier u_idx u_idx} (BalBiadd ... N M)"
      while it is expected to have type
       "ElementSolutionSet@{u_a u_b u_a u_b} (BalBiadd ... N M)"
      (universe inconsistency: Cannot enforce u_a = u_b because
       u_b < u_a)

    RECORDED CORRECTION: an earlier revision quoted the expected type as
    "ElementSolutionSet@{u_obj' Set u_obj' Set}" and the clause as
    "Cannot enforce Set = u_obj' because Set < u_obj'".  The literal [Set]
    is gone -- it was Instance/Discrete.v's minimization, repaired in the
    PR "algebraic carriers are sets" -- and the refusal is unchanged in
    substance: the first and third slots want the same level as the second
    and fourth, and the supplied index sits strictly above them.

    So Exercise 3's AFT clause is conditional for exactly the reason the
    commutative one is. *)

Fail Definition n3_bal_direct_esols_refused {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_direct N M).

(** ** Former NEGATIVE 4: the [Set] pin on the ring's carrier, now lifted

    RECORDED CORRECTION.  An earlier revision read: "NEGATIVE 4
    (UNIVERSE): the [Set] pin on the ring's carrier.  [tensor_via_AFT]
    elaborates only with the ring's carrier universe at [Set].  A ring
    declared strictly above [Set] is refused; the control immediately
    below, at an unconstrained ring, is accepted.  Stripped and re-run,
    the message is

      The term "Vu" has type "RModObject@{... pra prb prc} Ru"
      while it is expected to have type
       "RModObject@{... Set Set ... Set ...} ?R"
      (universe inconsistency: Cannot enforce Set = pra)"

    That [Set] was a universe-minimization artifact of Instance/Discrete.v's
    unannotated [DiscreteCat_Functor], reaching [representability_theorem]
    through [Complete] and [Limit].  Annotated in the PR "algebraic
    carriers are sets" (2026-09-17), Instance/Discrete.v:81, it is gone,
    and [tensor_via_AFT] elaborates over a ring whose carrier universe is
    declared strictly above [Set].  The line is kept as a positive control
    at exactly the levels that used to refuse it.

    THE WALL OF NEGATIVES 1-3 IS NOT LIFTED BY THIS.  Those three are
    carrier-versus-index refusals, and they survive with the literal [Set]
    removed from their messages; their quoted texts above were re-measured
    after the annotation by stripping each [Fail] in a copy of this whole
    file. *)

Section SetPin.

Universes pra prb prc.
Constraint Set < pra.

Context (Ru : RingObject@{pra prb prc}).
Context (Vu Vu' : RModObject Ru).

Check (tensor_via_AFT Vu Vu').

End SetPin.

Check (fun (Ru : RingObject) (V V' : RModObject Ru) => tensor_via_AFT V V').

(** ** NEGATIVE 5 (CONVERSION): the object comparison is `≅`, not [eq_refl]

    The adjoint functor theorem builds its representing object as a limit
    inside the comma category; [TensorMod] is a quotient of formal terms.
    [tensor_AFT_iso] compares them at `≅`, and that is all that holds.  The
    control is [c_repr_of_UE_obj] above, which IS [eq_refl]. *)

Fail Example n5_aft_object_not_definitional {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT_of_esols V V' E)
    = TensorMod V V' := eq_refl.

(** ** NEGATIVE 6 (CONVERSION): the circular continuity term is not the one
       delivered

    [preserves_image_of_representable (tensor_repr_of_UE V V')]
    (Adjunction/Representability/Sets.v:365) inhabits the same type as
    [Bilin_PreservesImageLimit], and is checked as a control above -- but it
    derives the theorem's hypothesis from the very tensor the theorem is
    meant to construct, which is the circularity Instance/Ab/Limit.v:57-67
    and Instance/Grp/FreeAFT.v:182-185 name.  The delivered term is a
    DIFFERENT one, built elementwise over the created limits of
    Instance/Mod/Limit.v, and this pins that the two are not the same
    term. *)

Fail Example n6_circular_route_is_a_different_term {R : RingObject}
  (V V' : RModObject R) :
  @Bilin_PreservesImageLimit R V V'
    = preserves_image_of_representable (tensor_repr_of_UE V V') := eq_refl.

(** ** NEGATIVE 7 (ARGUMENT NAME): [MGen]'s predicate is positional

    Instance/Mod/Spanning.v's [MGen] takes its predicate as an EXPLICIT
    section variable, so the constructors do not answer to it by name.  The
    control is the same application written positionally. *)

Section GenArgumentName.

Context {R : RingObject}.
Context (V V' : RModObject R).

Check (fun (a : carrier (cmon_setoid (TensorMod V V')))
           (Ha : rbl_image (@tensor_gen R V V') a) =>
         mgen_base (rbl_image (@tensor_gen R V V')) a Ha).

Fail Check (fun (a : carrier (cmon_setoid (TensorMod V V')))
                (Ha : rbl_image (@tensor_gen R V V') a) =>
              mgen_base (P := rbl_image (@tensor_gen R V V')) a Ha).

End GenArgumentName.

(** ** NEGATIVE 8 (UNIVERSE): the new side condition, [Set < carrier]

    THE ONE PRICE THE UNCONDITIONAL CONSTRUCTION PAYS, and it is pinned
    here rather than only stated.  The index is a sigma over a
    [Prop]-valued relation; the sort of [Prop] is [Set+1]; identifying the
    index universe with the ring's carrier universe therefore puts the
    carrier strictly above [Set].  A ring whose carrier universe IS [Set]
    is refused by the unconditional form and ACCEPTED by the conditional
    one, which is what makes this a side condition of the new solution set
    and not of the theorem.

    Measured, [About] under [Set Printing Universes], side by side:

      tensor_via_AFT@{…} : ∀ {R : RingObject@{u10 u2 u11}} …
      (* … Set < u2 / u2 < u0 / u2 < u1 … *)

      tensor_via_AFT_of_esols@{…} : ∀ {R : RingObject@{u13 u2 u14}} …
      (* … Set < u0 / Set < u11 / u2 < u0 / u2 < u1 / u2 < u11 … *)

    -- [u2] is the ring's carrier slot in both, and only the unconditional
    form bounds it.  Stripped and re-run in a copy of this whole file, the
    refusal is

      The term "Vs" has type "RModObject Rs" while it is expected to have
      type "obj[RMod ?R]"
      (universe inconsistency: Cannot enforce u_carrier = u_index because
       u_carrier < u_index)

    with [u_carrier] the section's own [Set]-identified universe.

    AT [Ab], EXERCISE 3 PAYS NOTHING NEW, measured the same way: the
    constraint block of [bal_tensor_via_AFT] gains exactly one line over
    [bal_tensor_via_AFT_of_esols]'s, [Set < Projections.u0], a bound on a
    stdlib constant, and NO new bound on the ring's carrier slot.  The
    [Set < u0] the two share is one the conditional already carried.  The
    asymmetry is real and is not explained here. *)

Section SetCarrierPin.

Universes pa pb pc.
Constraint pb = Set.

Context (Rs : RingObject@{pa pb pc}).
Context (Vs Vs' : RModObject Rs).

(* THE CONTROL: the conditional form elaborates at this very ring. *)
Definition p449_cond_at_set_carrier
  (E : ElementSolutionSet (Bilin Vs Vs')) : Representable (Bilin Vs Vs') :=
  tensor_via_AFT_of_esols Vs Vs' E.

(* THE NEGATIVE: the unconditional one does not. *)
Fail Definition p449_uncond_at_set_carrier :
  Representable (Bilin Vs Vs') := tensor_via_AFT Vs Vs'.

End SetCarrierPin.
