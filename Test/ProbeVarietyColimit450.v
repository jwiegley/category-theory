(** * Probe for the setoid variety's colimits by the adjoint functor
      theorem (issue #450)

    Pins the measured boundaries of Instance/Variety/Colimit.v (Mac Lane
    §V.7 Exercise 4 and §IX.1 Exercise 2, on [SVariety E]) and of
    Instance/Variety/Limit.v (completeness, and the forgetful functor's
    continuity), together with the refusal Instance/Variety/Spanning.v's
    header quotes for its [variety_solution_set].  Groups, rings, Riehl's
    presentation and disjointness are Test/ProbeAlgColimit450.v's.

    THE IMPORT LIST is Instance/Variety/Colimit.v's thirty lines verbatim
    and in order, then the three lines Instance/Variety/Limit.v adds, the
    one Instance/Variety/Free.v adds and the four
    Instance/Variety/Spanning.v adds (measured by comparing their
    [Require] lines), then Instance/Discrete.v and Instance/Two/Discrete.v
    for the shapes, then the two target modules not already listed.

    NOT DUPLICATED HERE.  That [tree_equiv] is [Prop]-valued since #450,
    and so eliminates only into [Prop], is pinned by
    Test/ProbeVarietyFree441.v's n4 ([p450_tree_equiv_elim_Type], an
    induction into a [Type]-sorted goal, beside the same script into a
    [Prop]-sorted goal as its control); that probe was extended when
    Instance/Variety/Free.v changed, and a second copy here would guard
    nothing more.

    DISCIPLINE, as in Test/ProbeAlgColimit450.v.  The instrument was
    checked both ways: the refutation of an absent name is refused for
    that reason, and wrapping the control [p450v_colim_bool] in a
    refutation, in a copy of this file, stops the build with the report
    that the guarded command had been accepted.  Every negative sits
    beside a positive control, every negative other than the name-absence
    instrument is an [Example] or a [Definition] (the instrument is a
    [Check] of a name that does not exist, which no evar can supply), and
    each was stripped of its refutation keyword in a copy of this WHOLE
    file, one at a time, and classified by its error.
    Quotations hold under this file's import list; a universe the stripped
    copy names after itself and a serial number is written <anon>.  The
    quotations are Rocq 9.1's.  Under Coq 8.20.1 every stripped copy is
    refused with the same kind, and the file compiles on Coq 8.19.2 and
    8.20.1.

    KINDS.  Six refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), CONVERSION (N1, N2)
    and UNIVERSE (N3, N4, N5).

    AN INSTRUMENT TRAP, MET AND AVOIDED.  N3 was first written inside the
    [Section] whose [Context] declares [E].  Stripped there, it was refused
    with "universe inconsistency: Cannot enforce Set = <anon>" and no
    "because" clause: [E]'s carrier universe was a section universe, and
    the refusal came from its rigidity, which refuses [Set] whatever the
    bounds.  Such a refutation would stand even with no [Set < carrier]
    anywhere.  N3, N4 and N5 are therefore top-level definitions with their
    own binders, and their stripped errors name the bound.

    N1 (CONVERSION).  The initial algebra the theorem produces is a
    different object, its carrier not the closed terms [UA.Tree S False]
    by [eq_refl] ([GAFT] is moreover [Qed], so the carrier has no readback
    at all):
      The term "eq_refl" has type "soa_obj (projT1 0) = soa_obj (projT1 0)"
      while it is expected to have type "soa_obj (projT1 0) = UA.Tree S
      False" (cannot unify "carrier (soa_obj (projT1 0))" and "UA.Tree S
      False").
    ([0] is the notation for [initial_obj].)  The controls are the same
    equation at [SVariety_Initial], where it IS [eq_refl] -- the free
    algebra on the empty set, whose carrier is the closed terms, and which
    IS [Free_Variety E] at [Sets]'s initial object by [eq_refl] -- and
    [SVariety_Initial_agrees], the isomorphism between the two.

    N2 (CONVERSION).  Mac Lane's own route to the free algebra,
    [Free_Variety_via_GAFT], agrees with Instance/Variety/Free.v's
    [Free_Variety_Functor] up to `≈` and no further:
      (cannot unify "projT1 (Free_Variety_via_GAFT E)" and
      "Free_Variety_Functor E").
    The control is [Free_Variety_via_GAFT_agrees] at exactly that
    statement as `≈`.

    N3 (UNIVERSE).  [SVariety_colim_via_GAFT E Two_Discrete] is refused:
      The term "Two_Discrete" has type "Category@{<anon> Set Set}" while it
      is expected to have type "Category@{<anon> <anon> <anon>}" (universe
      inconsistency: Cannot enforce Set = <anon> because Set < <anon>).
    The controls are [DiscreteCat bool] and [DiscreteCat (Fin.t 2)].
    This is the shape discipline the target's header states -- a shape's
    homs AT the carrier universe -- and the reason its coproduct comes
    through Structure/Limit/Finite.v's bridges.

    N4 (UNIVERSE).  At J : Category@{Set Set Set}, the control
    [Diagonal_SVariety_solution_set E D] ELABORATES, and [About] reads its
    D at [SVariety] with the carrier and hom universes at [Set] and the
    index at a universe above [Set]; [SVariety_colim_via_GAFT E J] is
    refused:
      The term "J" has type "Category@{Set Set Set}" while it is expected
      to have type "Category@{<anon> <anon> <anon>}" (universe
      inconsistency: Cannot enforce Set = <anon> because Set < <anon>).
    The second control, [p450v_gaft_partial_at_set], applies [GAFT] at
    the same diagonal to every argument BUT the solution set
    ([SVariety_Complete E] and [Continuous_PreservesImageLimit
    Diagonal_continuous]), and it is accepted too.  So the variety's
    [Set < carrier] is imposed where [GAFT] puts the solution set's index
    at the carrier universe, not by the solution set itself nor by the
    completeness or the continuity; the same attribution holds for groups
    and rings (N4 and N5 of Test/ProbeAlgColimit450.v, with the same two
    controls), and Instance/Variety/Colimit.v's header makes it.
    [soa_prop] is what keeps the kernel index carrier-sized, and the index
    of [Prop]-valued relations sits above [Set]; the bound lands on the
    carrier only once [GAFT] identifies the two.

    N5 (UNIVERSE).  [GAFT] refuses Instance/Variety/Spanning.v's
    [variety_solution_set], whose index is a Σ over the OBJECTS of
    [SVariety E] (Structure/Complete.v's size note, item 3), with the real
    completeness and continuity as its other arguments:
      The term "variety_solution_set E" has type
      "∀ X : obj[Sets@{a b}], SolutionSet@{c b c a} (SVariety_Forget E) X"
      while it is expected to have type
      "∀ d : obj[Sets@{a b}], SolutionSet@{a b d a} (SVariety_Forget E) d"
      (universe inconsistency: Cannot enforce d = a because a < e <= d).
    That is the stripped text with each <anon> renamed to one letter and
    the [SVariety_Forget] instances elided.  The first slot of
    [SolutionSet] is the index and the third the object universe of
    [SVariety E]; the spanning family repeats one universe [c] in both,
    its index being a Σ over objects, while [GAFT] wants the index AT the
    carrier [a] and the object universe at [d], and the carrier sits
    strictly below the object universe ([a < e <= d]).  The shape is the
    one Spanning.v quotes from a scratch file.  The controls: the
    congruence-indexed [SVariety_Forget_solution_set] is accepted by the
    same call, and [variety_solution_set E] itself elaborates.

    CONTROLS WITHOUT A NEGATIVE.  The route, by [eq_refl]:
    [SVariety_colim_via_GAFT E J] IS [GAFT] at the diagonal with
    [SVariety_Complete], [Continuous_PreservesImageLimit
    Diagonal_continuous] and [Diagonal_SVariety_solution_set]; its index IS
    [VCongIdx] and its members ARE the quotients [VQ_alg];
    [SVariety_coequalizers_via_GAFT] (Exercise 4) IS Finite.v's bridge over
    [SVariety_Cocomplete_via_GAFT]; [Free_Variety_via_GAFT] IS [GAFT] at
    the forgetful functor with the congruence index [FCongIdx].  §IX.1
    Exercise 2: the category is never empty ([SVariety_Terminal]); the
    emptiness of the initial algebra is [SVariety_initial_empty_iff] and
    [closed_terms_empty_iff]; "inhabited ⇒ some constant" is
    [dec_closed_term_constant] under decidable arities, and its uniform
    form implies weak excluded middle
    ([closed_term_constant_implies_WLEM]).  The Leibniz boundary is
    [leibniz_coequalizers_iff_quotients].  The non-vacuity constants at
    #440's [CommEq], a presentation built without extensionality, are
    [CommMagma_Cocartesian] and [CommMagma_coequalizers]. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.
Require Import Category.Instance.Variety.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Variety.Spanning.
Require Import Category.Instance.Variety.Colimit.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe450_variety_absent_name.

(** ** A. The headlines at their stated types, and the route by [eq_refl] *)

Section Headlines.

Context {S : UA.OpSignature} (E : UA.EqSignature S).

Check (SVariety_Complete E : @Complete (SVariety E)).
Check (SVariety_Forget_continuous E : ContinuousFunctor (SVariety_Forget E)).
Check (SVariety_colim_via_GAFT E : ∀ J : Category,
  { L : [J, SVariety E] ⟶ SVariety E & L ⊣ @Diagonal (SVariety E) J }).
Check (SVariety_Cocomplete_via_GAFT E : @Cocomplete (SVariety E)).
Check (SVariety_Cocartesian_via_GAFT E : @Cocartesian (SVariety E)).
Check (SVariety_coequalizers_via_GAFT E : HasCoequalizers (SVariety E)).
Check (SVariety_Initial_via_GAFT E : @Initial (SVariety E)).
Check (SVariety_Terminal E : @Terminal (SVariety E)).
Check (SVariety_Initial E : @Initial (SVariety E)).
Check (Free_Variety_via_GAFT E :
  { F : Sets ⟶ SVariety E & F ⊣ SVariety_Forget E }).

Example p450v_colim_is_GAFT (J : Category) :
  SVariety_colim_via_GAFT E J
    = GAFT (@Diagonal (SVariety E) J) (SVariety_Complete E)
           (Continuous_PreservesImageLimit Diagonal_continuous)
           (@Diagonal_SVariety_solution_set S E J) := eq_refl.

(* The index IS the type of cocone congruences on the term algebra. *)
Example p450v_index (J : Category) (D : J ⟶ SVariety E) :
  sol_index (Diagonal_SVariety_solution_set E D) = VCongIdx E D := eq_refl.

Example p450v_member (J : Category) (D : J ⟶ SVariety E)
  (i : VCongIdx E D) :
  sol_obj (Diagonal_SVariety_solution_set E D) i = VQ_alg E D i := eq_refl.

(* Exercise 4's coequalizers are Structure/Limit/Finite.v's bridges over
   the AFT colimits. *)
Example p450v_coequalizers_bridge :
  SVariety_coequalizers_via_GAFT E
    = HasCoequalizers_of_HasEqualizers_op
        (FinitelyComplete_HasEqualizers
           (FinitelyCocomplete_FinitelyComplete_op
              (Cocomplete_FinitelyCocomplete
                 (SVariety_Cocomplete_via_GAFT E)))) := eq_refl.

(* Mac Lane's own route to the free algebra, at the congruence index. *)
Example p450v_free_is_GAFT :
  Free_Variety_via_GAFT E
    = GAFT (SVariety_Forget E) (SVariety_Complete E)
           (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
           (SVariety_Forget_solution_set E) := eq_refl.

Example p450v_free_index (X : Sets) :
  sol_index (SVariety_Forget_solution_set E X) = FCongIdx E X := eq_refl.

(** ** N1 (CONVERSION): the AFT initial object's carrier does not reduce *)

(* CONTROL: the initial algebra IS the free algebra on the empty set... *)
Example p450v_initial_is_free :
  @initial_obj (SVariety E) (SVariety_Initial E)
    = Free_Variety E (@initial_obj Sets _) := eq_refl.

(* CONTROL: ...and its carrier IS the closed terms. *)
Example p450v_initial_carrier :
  carrier (soa_obj (`1 (@initial_obj (SVariety E) (SVariety_Initial E))))
    = UA.Tree S False := eq_refl.

(* CONTROL: the two initial objects agree, as data. *)
Check (SVariety_Initial_agrees E :
  @initial_obj (SVariety E) (SVariety_Initial E)
    ≅ @initial_obj (SVariety E) (SVariety_Initial_via_GAFT E)).

Fail Example p450v_n1_aft_initial_carrier :
  carrier (soa_obj (`1 (@initial_obj (SVariety E)
                                     (SVariety_Initial_via_GAFT E))))
    = UA.Tree S False := eq_refl.

(** ** N2 (CONVERSION): the free algebra from [GAFT] is `≈`, no more *)

(* CONTROL: the agreement that holds. *)
Check (Free_Variety_via_GAFT_agrees E :
  projT1 (Free_Variety_via_GAFT E) ≈ Free_Variety_Functor E).

Fail Example p450v_n2_aft_free_is_free :
  projT1 (Free_Variety_via_GAFT E) = Free_Variety_Functor E := eq_refl.

(** ** IX.1 Exercise 2: emptiness, and the category is never empty *)

Check (SVariety_initial_empty_iff E :
  (carrier (soa_obj (`1 (@initial_obj (SVariety E) (SVariety_Initial E))))
     → False) ↔
  ({ o : UA.operation S & UA.arity o → False } → False)).
Check (closed_terms_empty_iff S :
  (UA.Tree S False → False) ↔
  (∀ o : UA.operation S, (UA.arity o → False) → False)).
Check (@dec_closed_term_constant S :
  (∀ o : UA.operation S, (UA.arity o → False) + UA.arity o) →
  UA.Tree S False → { o : UA.operation S & UA.arity o → False }).

End Headlines.

Check (closed_term_constant_implies_WLEM :
  (∀ S : UA.OpSignature,
     UA.Tree S False → { o : UA.operation S & UA.arity o → False }) →
  ∀ P : Prop, (P → False) + ((P → False) → False)).
Check (leibniz_coequalizers_iff_quotients :
  HasCoequalizers (Variety NoEq) ↔ QuotElim).

(* Non-vacuity at a presentation built without extensionality. *)
Check (CommMagma_Cocartesian : @Cocartesian (SVariety CommEq)).
Check (CommMagma_coequalizers : HasCoequalizers (SVariety CommEq)).

(** ** N3 (UNIVERSE): [Two_Discrete] is refused as a shape

    Stated at the top level with its own binders, not in the section
    above: there [E]'s carrier universe would be a section universe, and
    the refusal would stop at that rigidity, before the [Set < carrier]
    bound it is meant to exercise. *)

(* CONTROLS: discrete two-object shapes whose homs are free. *)
Definition p450v_colim_bool {S : UA.OpSignature} (E : UA.EqSignature S) :=
  SVariety_colim_via_GAFT E (DiscreteCat bool).
Definition p450v_colim_fin2 {S : UA.OpSignature} (E : UA.EqSignature S) :=
  SVariety_colim_via_GAFT E (DiscreteCat (Fin.t 2)).

Fail Definition p450v_n3_two_discrete {S : UA.OpSignature}
  (E : UA.EqSignature S) := SVariety_colim_via_GAFT E Two_Discrete.

(** ** N4 (UNIVERSE): at a [Set] carrier the solution set elaborates and
    [GAFT] does not *)

(* CONTROL: the diagonal solution set with the shape's homs, and hence the
   algebras' carrier, at [Set]. *)
Definition p450v_sols_at_set {S : UA.OpSignature} (E : UA.EqSignature S)
  (J : Category@{Set Set Set}) (D : J ⟶ SVariety E) :=
  Diagonal_SVariety_solution_set E D.

(* CONTROL: [GAFT] at the same diagonal with every argument but the
   solution set, so that neither completeness nor continuity is what a
   [Set] carrier refuses. *)
Definition p450v_gaft_partial_at_set {S : UA.OpSignature}
  (E : UA.EqSignature S) (J : Category@{Set Set Set}) :=
  GAFT (@Diagonal (SVariety E) J) (SVariety_Complete E)
       (Continuous_PreservesImageLimit Diagonal_continuous).

Fail Definition p450v_n4_colim_at_set {S : UA.OpSignature}
  (E : UA.EqSignature S) (J : Category@{Set Set Set}) :=
  SVariety_colim_via_GAFT E J.

(** ** N5 (UNIVERSE): [GAFT] refuses the spanning solution set *)

(* CONTROL: the same call at the congruence-indexed family. *)
Definition p450v_gaft_congruences {S : UA.OpSignature}
  (E : UA.EqSignature S) :=
  GAFT (SVariety_Forget E) (SVariety_Complete E)
       (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
       (SVariety_Forget_solution_set E).

(* CONTROL: the spanning family itself elaborates. *)
Definition p450v_spanning {S : UA.OpSignature} (E : UA.EqSignature S) :=
  variety_solution_set E.

Fail Definition p450v_n5_gaft_spanning {S : UA.OpSignature}
  (E : UA.EqSignature S) :=
  GAFT (SVariety_Forget E) (SVariety_Complete E)
       (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
       (variety_solution_set E).

(** ** Guard block *)

Check @SVGen.
Check @IsVCong.
Check @VCongIdx.
Check @VQ_alg.
Check @vq_leg.
Check @vq_arr.
Check @vker.
Check @vker_cong.
Check @vker_idx.
Check @vker_med.
Check @Diagonal_SVariety_solution_set.
Check @IsFCong.
Check @FCongIdx.
Check @FQ_alg.
Check @fker_med.
Check @SVariety_Forget_solution_set.
Check @SVariety_Complete.
Check @SVariety_Forget_continuous.
Check @svariety_complete_carrier.
Check @WLEM_sig.
Check @WLEM_term.
Check @NoOp.
Check @NoEq.
Check @QuotElim.
Check @leibniz_coequalizers_give_quotients.
Check @quotients_give_leibniz_coequalizers.
Check @soa_prop.
Check @tree_equiv.
Check @variety_solution_set.
Check @Diagonal_continuous.
