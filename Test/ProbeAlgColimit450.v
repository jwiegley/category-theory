(** * Probe for the colimits of groups and rings by the adjoint functor
      theorem (issue #450)

    Pins the measured boundaries of four files: Instance/Grp/Colimit.v
    (Mac Lane §V.7 Exercise 1, §IX.1 Exercise 1), Instance/Rng/Colimit.v
    (§V.7 Exercise 2), Instance/Grp/Colimit/Presentation.v (Riehl §5.6,
    the free product as a coequalizer of free groups) and
    Theory/Subobject/Disjoint.v (the injections of a coproduct meet in the
    zero subobject), together with Adjunction/Diagonal/Limit.v's
    [Diagonal_continuous], the preservation hypothesis every one of them
    feeds to [GAFT].  The variety half of #450 has its own probe,
    Test/ProbeVarietyColimit450.v.

    THE IMPORT LIST is the union of the targets' own lists, measured by
    comparing their [Require] lines: Instance/Grp/Colimit.v's forty-one
    lines verbatim and in order (they already contain all twelve of
    Theory/Subobject/Disjoint.v's), then the one line
    Instance/Grp/Colimit/Presentation.v adds (Instance/Sets/Cocartesian.v),
    the eight Instance/Rng/Colimit.v adds and the eleven
    Adjunction/Diagonal/Limit.v adds, then Instance/Discrete.v and
    Instance/Two/Discrete.v for the shapes, then the three target modules
    not already listed.  A shorter prefix is what makes a probe pass for
    no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and wrapping the control
    [p450_grp_colim_bool] in a refutation, in a copy of this file, stops
    the build with the report that the guarded command had been accepted.
    Every negative sits beside a positive control naming the same library
    constants, and every negative other than the name-absence instrument
    is an [Example] or a [Definition], never a [Check], so that an open
    evar or a missing instance cannot satisfy it (the instrument is a
    [Check] of a name that does not exist, which no evar can supply).
    Each negative was stripped of its refutation keyword in a copy of
    this WHOLE file, one at a time, and the error read; the kind recorded
    is the kind of that error.  Rocq prints the "cannot unify"
    parenthetical with the short names in scope, so the quotations below
    hold under this file's import list; a universe the stripped copy names
    after itself and a serial number is written <anon>.  The quotations
    are Rocq 9.1's.  Under Coq 8.20.1 every stripped copy is refused with
    the same kind, and the file compiles on Coq 8.19.2 and 8.20.1.

    KINDS.  Fifteen refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), UNIVERSE (N2-N7,
    N13) and CONVERSION (N1, N8-N12, N14).

    N1 (CONVERSION).  The coproduct the adjoint functor theorem produces is
    a different object, not Instance/Grp/Pushout.v's words free product
    [Grp_free_product G H] by [eq_refl] ([GAFT] is moreover [Qed], so it
    has no readback at all):
      The term "eq_refl" has type "G + H = G + H" while it is expected to
      have type "G + H = Grp_free_product G H"
      (cannot unify "G + H" and "Grp_free_product G H").
    The control is the same equation at Pushout.v's [Grp_Cocartesian],
    where it IS [eq_refl]; [Grp_free_product_iso] (an isomorphism) and
    [Grp_coproduct_agrees] (`≈` of the two coproduct bifunctors) are what
    relate the two, and both are checked beside it.

    N2 (UNIVERSE).  [Grp_colim_via_GAFT Two_Discrete] is refused:
      The term "Two_Discrete" has type "Category@{<anon> Set Set}" while it
      is expected to have type "Category@{<anon> <anon> <anon>}" (universe
      inconsistency: Cannot enforce Set = <anon> because Set < <anon>).
    Instance/Two/Discrete.v's shape has its homs at [Set]; [Fun]
    identifies a shape's hom universe with the carrier, and the carrier
    sits strictly above [Set].  The controls are [DiscreteCat bool] and
    [DiscreteCat (Fin.t 2)], whose hom universes are free.

    N3 (UNIVERSE).  Under [Constraint jh < p], the functor category
    [[Jlow, Grp@{u p}]] for Jlow : Category@{jo jh jh} is refused at its
    formation, before any theorem is applied:
      The term "Grp" has type "Category@{u p p}" while it is expected to
      have type "Category@{<anon> jh jh}" (universe inconsistency: Cannot
      enforce p = jh because jh < p).
    The controls take J : Category@{jo p p} with [jo <= p]: the functor
    category forms and [Grp_colim_via_GAFT J] applies.  Shape homs AT the
    carrier, shape objects at or below it.

    N4, N5 (UNIVERSE).  At J : Category@{Set Set Set}, with
    D : J ⟶ Grp@{gu Set} and DR : J ⟶ Rng@{gu Set}, the diagonal solution
    sets [Diagonal_Grp_solution_set] and [Diagonal_Rng_solution_set]
    ELABORATE, and so does [GAFT] applied to everything BUT the solution
    set -- the diagonal at [Grp@{gu Set}] or [Rng@{gu Set}], [Grp_Complete]
    or [Rng_Complete], and [Continuous_PreservesImageLimit
    Diagonal_continuous] (the four controls), while [Grp_colim_via_GAFT J]
    and [Rng_colim_via_GAFT J] are each refused:
      The term "J" has type "Category@{Set Set Set}" while it is expected
      to have type "Category@{<anon> <anon> <anon>}" (universe
      inconsistency: Cannot enforce Set = <anon> because Set < <anon>).
    So at a [Set] carrier the solution set elaborates, and so does [GAFT]
    on the other arguments; what is refused is handing the one to the
    other.  [About] reads the argument each partial application still
    awaits as [SolutionSet@{Set gu gu Set}], its index slot AT the [Set]
    carrier, where the two solution-set controls read back as
    [SolutionSet@{u gu gu Set}] with [Set < u] on the index [u].  The side
    condition [Set < carrier] is [GAFT]'s, which puts its solution set's
    index at the carrier universe, and neither the solution set's, the
    completeness's nor the continuity's -- the attribution the two target
    headers make.  They quote the same application with an explicit
    universe instance, which is refused as
    "Cannot enforce Set < Set because Set = Set."; here the instance is
    left to unification, which reports the bound the other way round.

    N6, N7 (UNIVERSE).  What the adjoint functor theorem builds exists only
    above [Set] carriers, and what Riehl's construction states does not
    need to.  N6, [Grp_free_product_is_coequalizer Z2@{Set} Z2@{Set}]:
      The term "Z2" has type "GrpObject" while it is expected to have type
      "obj[Grp]" (universe inconsistency: Cannot enforce Set = <anon>
      because Set < <anon>).
    N7, [Grp_Cocartesian_via_GAFT] at the type [@Cocartesian Grp@{u Set}]:
      The term "Grp_Cocartesian_via_GAFT" has type
      "@Cocartesian Grp@{<anon> <anon>}" while it is expected to have type
      "@Cocartesian Grp@{u Set}" (universe inconsistency: Cannot enforce
      Set = <anon> because Set < <anon>).
    The controls were transplanted from the Riehl verification's scratch
    probe and re-run under this file's full import list: at [Z2@{Set}],
    [Grp_free_product_words_is_coequalizer], [Grp_coproduct_is_coequalizer]
    at any coproduct structure on [Grp@{u Set}],
    [Grp_canonical_presentation] and [Grp_riehl_e_not_monic] are accepted,
    and so is Pushout.v's [Grp_Cocartesian] at N7's very type;
    [Grp_free_product_is_coequalizer] itself is accepted at [Z2@{p}] under
    [Set < p].

    N8-N11 (CONVERSION).  Instance/Grp/Colimit/Presentation.v says each
    letter-level fact ([Grp_riehl_l_inl], [Grp_riehl_r_inl],
    [Grp_riehl_transpose_generator]) is `≈`, neither the counit nor
    [FreeGrp] on arrows computing.
    Each negative states one lemma's equation by [eq_refl], and its control
    is that lemma ascribed exactly the same equation as `≈`.  Stripped, all
    four refuse in one shape, "The term "eq_refl" has type "X = X" while it
    is expected to have type "X = Y" (cannot unify "X" and "Y")", X being
    the left-hand side unreduced and Y being, for N8,
    [fg_insert (fobj[Grp_Forget] G + fobj[Grp_Forget] H)
    (Datatypes.inl (free_group_counit G w))]; for N9,
    [fmap[FreeGrp] inl w]; for N10,
    [(fmap[Grp_Forget] f1 ▽ fmap[Grp_Forget] f2) s]; and for N11, [g].
    N8's two sides are also [Check]ed as a pair, so N8 is not a typing
    refusal in disguise, and that disguise is a real one: the Riehl
    verification's first version of N8, written without the explicit
    [Sets_Cocartesian] setoids, was refused at elaboration and passed for
    the wrong reason.  The two non-computing pieces are the counit, which
    N11 pins, and [FreeGrp] on arrows, both universal factorizations
    through the [Qed]-sealed [ump_universal_arrows] (Instance/Grp/Free.v):
    [free_group_counit] is itself transparent but is [unique_obj] of it,
    and [FreeGrp]'s arrow map is [LeftAdjointFunctorFromUniversalArrows]'s.
    N8 is refused on [FreeGrp]'s arrow map alone: [Grp_riehl_l] IS
    [FreeGrp] on an arrow, the counit stands unreduced on both of N8's
    sides, and the control [p450_n8_by_fmap_alone] closes N8's `≈` with
    [free_group_fmap_generators] and no counit fact.  N9's left side goes
    through both pieces, [Grp_riehl_r] being the counit after an arrow of
    [FreeGrp].  The control beside N11 shows that the UNIT does compute on
    a letter.

    N12 (CONVERSION).  Riehl's coproduct run on the theorem's coequalizers,
    [Grp_Cocartesian_via_riehl], is not the theorem's own coproduct by
    [eq_refl]:
      (cannot unify "@Coprod Grp Grp_Cocartesian_via_riehl G H" and
      "@Coprod Grp Grp_Cocartesian_via_GAFT G H")
    (printed with explicit arguments, the two sides both reading "G + H"
    otherwise).  The controls: its object IS the apex of the theorem's
    coequalizer of Riehl's pair, by [eq_refl], and
    [Grp_free_product_coequalizer_agrees] is the isomorphism between that
    apex and the theorem's coproduct.

    N13 (UNIVERSE).  Instance/Rng/Colimit.v's header says the initial ring
    ℤ ([Rng_Initial_Z], at [Set] carriers only) and [Rng_Initial_via_GAFT]
    cannot be stated together.  [initial_unique Rng_Initial_via_GAFT
    Rng_Initial_Z] is refused:
      The term "Rng_Initial_Z" has type "@Initial Rng@{<anon> Set}" while
      it is expected to have type "@Initial Rng@{<anon> <anon>}" (universe
      inconsistency: Cannot enforce Set = <anon> because Set < <anon>).
    The control is the group twin [initial_unique Grp_Initial_via_GAFT
    Grp_Initial], which is Instance/Grp/Colimit.v's [Grp_initial_agrees]
    and is accepted only because #450 lifted Instance/Grp.v's zero object
    off [Set].  N13 is expected to turn over if ℤ's pin is ever lifted the
    same way, and Instance/Rng/Colimit.v's header would then need a
    correction.

    N14 (CONVERSION).  Theory/Subobject/Disjoint.v's STRENGTHS: the meet
    of the two coproduct injections is the bottom subobject up to `≈`, not
    on the nose.  Stripped,
      (cannot unify "sub_meet (sub_inl x y) (sub_inr x y)" and
      "coprod_bot x y")
    which is the text that header quotes.  The control applies
    [coproduct_injections_meet_trivial] to exactly six arguments ([C],
    [Z], [CC], [PB], [x], [y]) and ascribes it its full type; that pins
    the header's "no [Cartesian] hypothesis", since a seventh binder would
    leave a partial application and refuse the ascription.

    CONTROLS WITHOUT A NEGATIVE.  The route, by [eq_refl]:
    [Grp_colim_via_GAFT J] and [Rng_colim_via_GAFT J] ARE [GAFT] at the
    diagonal with [Grp_Complete] or [Rng_Complete],
    [Continuous_PreservesImageLimit Diagonal_continuous] and the diagonal
    solution set; its index IS [DCongIdx] or [RDCongIdx]; its members ARE
    the quotients [DQ]; [DQ D (dker_idx D c h)] IS
    [QGrp (fg_ker _) (fg_ker_is_cong _)], the reduction that makes
    [dker_cocone]'s [Defined] load-bearing (the ring twin is at
    [rker_cocone]); [Grp_Cocartesian_via_GAFT] IS Structure/Limit/Finite.v's
    bridge.  Which coproduct each headline is stated at, by [eq_refl]: the
    trivial meet, the monic injection and Riehl's coequalizer theorem are
    each their generic lemma at [Grp_Cocartesian_via_GAFT], never at the
    exported words instance, and Riehl's e IS the transpose of the two
    injections.

    The zero object above [Set].  Under [Set < p] and [p < u],
    [Grp_Zero@{u p}], [Z2@{p}], the trivial meet,
    [Grp_free_product_via_GAFT_nontrivial] at [Z2@{p}] and
    [Grp_free_product_coequalizer_nontrivial] are all accepted.  HISTORY:
    before #450, [About] read [Grp_Zero@{u} : ZeroObject@{u Set}
    Grp@{u Set}] and [Z2@{u} : GrpObject@{u Set Set}] (Instance/Grp.v's
    essays above [Grp_trivial] and [bool_setoid] record both readbacks),
    and the zero object's maps at a carrier above [Set] were refused with
    "Cannot enforce Set = <carrier>" -- the refusal
    Test/ProbePushoutGrpTop.v pinned as its negatives 5 and 6, which are
    its controls 9 and 10 now.  So these lines are controls and not
    negatives because the boundary moved; they break if the pin returns.

    [Diagonal_continuous]'s binders.  At C : Category@{o h h} and
    J : Category@{jo h h} under [Constraint jo < h] it is accepted.  A
    scratch twin with the same body and no binders reads back at
    J : Category@{u4 u4 u4} and, at the same J, is refused with "Cannot
    enforce jo = h because jo < h" (measured), so the control guards the
    binders Adjunction/Diagonal/Limit.v says the colimit applications
    need. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Disjoint.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Bicartesian.Matrix.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.Diagonal.Coproduct.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Grp.FreeAFT.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Colimit.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.AFT.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Kan.Extension.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Grp.Colimit.
Require Import Category.Instance.Grp.Colimit.Presentation.
Require Import Category.Instance.Rng.Colimit.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe450_absent_name.

(** ** A. The headlines at their stated types *)

Check (Grp_colim_via_GAFT :
  ∀ J : Category, { K : [J, Grp] ⟶ Grp & K ⊣ @Diagonal Grp J }).
Check (Grp_Cocomplete_via_GAFT : @Cocomplete Grp).
Check (Grp_Cocartesian_via_GAFT : @Cocartesian Grp).
Check (Grp_HasCoequalizers_via_GAFT : HasCoequalizers Grp).
Check (Grp_Initial_via_GAFT : @Initial Grp).
Check (Rng_colim_via_GAFT :
  ∀ J : Category, { K : [J, Rng] ⟶ Rng & K ⊣ @Diagonal Rng J }).
Check (Rng_Cocomplete_via_GAFT : @Cocomplete Rng).
Check (Rng_Cocartesian_via_GAFT : @Cocartesian Rng).
Check (Rng_HasCoequalizers_via_GAFT : HasCoequalizers Rng).
Check (Rng_Initial_via_GAFT : @Initial Rng).
Check (Grp_inl_via_GAFT_Monic :
  ∀ G H : Grp, Monic (@inl Grp Grp_Cocartesian_via_GAFT G H)).
Check (Grp_inr_via_GAFT_Monic :
  ∀ G H : Grp, Monic (@inr Grp Grp_Cocartesian_via_GAFT G H)).
Check (Grp_free_product_via_GAFT_nontrivial :
  (∀ a b : carrier (grp_setoid (@Coprod Grp Grp_Cocartesian_via_GAFT Z2 Z2)),
     a ≈ b) → False).
Check (Grp_canonical_presentation : ∀ G : Grp,
  IsCoequalizer (free_group_counit (FreeGrp (Grp_Forget G)))
                (fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)))
                G (free_group_counit G)).
Check (Grp_Cocartesian_of_coequalizers :
  HasCoequalizers Grp → @Cocartesian Grp).

(** ** B. Every colimit is [GAFT] at the diagonal, read back by [eq_refl] *)

Example p450_grp_colim_is_GAFT (J : Category) :
  Grp_colim_via_GAFT J
    = GAFT (@Diagonal Grp J) Grp_Complete
           (Continuous_PreservesImageLimit Diagonal_continuous)
           (@Diagonal_Grp_solution_set J) := eq_refl.

Example p450_rng_colim_is_GAFT (J : Category) :
  Rng_colim_via_GAFT J
    = GAFT (@Diagonal Rng J) Rng_Complete
           (Continuous_PreservesImageLimit Diagonal_continuous)
           (@Diagonal_Rng_solution_set J) := eq_refl.

Section Index.

Context {J : Category}.

(* The index IS the type of cocone congruences, and the members ARE the
   quotients of the free group on the disjoint union. *)
Example p450_grp_index (D : J ⟶ Grp) :
  sol_index (Diagonal_Grp_solution_set D) = DCongIdx D := eq_refl.

Example p450_grp_member (D : J ⟶ Grp) (i : DCongIdx D) :
  sol_obj (Diagonal_Grp_solution_set D) i = DQ D i := eq_refl.

(* WHY [dker_cocone] MUST END IN [Defined]: the quotient at the kernel
   index reduces to the one [fg_ker_med] maps out of. *)
Example p450_grp_kernel_quotient (D : J ⟶ Grp) (c : Grp)
  (h : D ~{[J, Grp]}~> fobj[@Diagonal Grp J] c) :
  DQ D (dker_idx D c h)
    = QGrp (fg_ker (dflat D c h)) (fg_ker_is_cong (dflat D c h)) := eq_refl.

Example p450_rng_index (D : J ⟶ Rng) :
  sol_index (Diagonal_Rng_solution_set D) = RDCongIdx D := eq_refl.

(* The same for [rker_cocone]. *)
Example p450_rng_kernel_quotient (D : J ⟶ Rng) (c : Rng)
  (h : D ~{[J, Rng]}~> fobj[@Diagonal Rng J] c) :
  RDQ D (rker_idx D c h)
    = QRng (rng_ker (rhab D c h)) (rng_ker_is_cong (rhab D c h)) := eq_refl.

End Index.

(* The finite colimits are Structure/Limit/Finite.v's bridges. *)
Example p450_grp_cocartesian_bridge :
  Grp_Cocartesian_via_GAFT
    = FinitelyComplete_Cartesian
        (FinitelyCocomplete_FinitelyComplete_op
           Grp_FinitelyCocomplete_via_GAFT) := eq_refl.

(** ** C. Which coproduct each headline is stated at *)

Example p450_meet_at_AFT (G H : Grp) :
  Grp_free_product_meet_trivial G H
    = @coproduct_injections_meet_trivial Grp Grp_Zero
        Grp_Cocartesian_via_GAFT Grp_HasPullbacks G H := eq_refl.

Example p450_inl_monic_at_AFT (G H : Grp) :
  Grp_inl_via_GAFT_Monic G H
    = @inl_Monic Grp Grp_Zero Grp_Cocartesian_via_GAFT G H := eq_refl.

Example p450_riehl_at_AFT (G H : Grp) :
  Grp_free_product_is_coequalizer G H
    = Grp_coproduct_is_coequalizer G H Grp_Cocartesian_via_GAFT := eq_refl.

Example p450_riehl_e_is_transpose (G H : Grp) (CC : @Cocartesian Grp) :
  Grp_riehl_e G H CC
    = Grp_riehl_transpose G H (@inl Grp CC G H) (@inr Grp CC G H)
  := eq_refl.

(** ** N1 (CONVERSION): the AFT coproduct is not the words free product *)

(* CONTROL: the same statement at Instance/Grp/Pushout.v's instance. *)
Example p450_words_coprod_is_words (G H : Grp) :
  @Coprod Grp Grp_Cocartesian G H = Grp_free_product G H := eq_refl.

(* CONTROL: what does relate the two -- an isomorphism and a natural
   isomorphism, carried as data. *)
Check (fun G H : Grp => Grp_free_product_iso G H :
  @Coprod Grp Grp_Cocartesian_via_GAFT G H ≅ Grp_free_product G H).
Check (Grp_coproduct_agrees :
  @InternalCoproductFunctor Grp Grp_Cocartesian_via_GAFT
    ≈ @InternalCoproductFunctor Grp Grp_Cocartesian).

Fail Example p450_n1_aft_coprod_is_words (G H : Grp) :
  @Coprod Grp Grp_Cocartesian_via_GAFT G H = Grp_free_product G H := eq_refl.

(** ** N2 (UNIVERSE): [Two_Discrete] is refused as a shape *)

(* CONTROLS: a discrete two-object shape whose homs are free. *)
Definition p450_grp_colim_bool := Grp_colim_via_GAFT (DiscreteCat bool).
Definition p450_grp_colim_fin2 := Grp_colim_via_GAFT (DiscreteCat (Fin.t 2)).

Fail Definition p450_n2_grp_two_discrete := Grp_colim_via_GAFT Two_Discrete.

(** ** N3 (UNIVERSE): shape homs below the carrier, refused at [J, Grp] *)

Section ShapeHoms.

Universes u p jo jh.
Constraint Set < p.
Constraint p < u.
Constraint jo <= p.
Constraint jh < p.

Context (J : Category@{jo p p}) (Jlow : Category@{jo jh jh}).

(* CONTROLS: homs AT the carrier, objects at or below it. *)
Definition p450_fun_at_carrier : Category := [J, Grp@{u p}].
Definition p450_colim_at_carrier := Grp_colim_via_GAFT J.

Fail Definition p450_n3_fun_below_carrier : Category := [Jlow, Grp@{u p}].

End ShapeHoms.

(** ** N4, N5 (UNIVERSE): at [Set] carriers the solution set elaborates
    and [GAFT] does not *)

Section SetCarrier.

Universes gu.
Constraint Set < gu.

Context (J : Category@{Set Set Set}).
Context (D : J ⟶ Grp@{gu Set}) (DR : J ⟶ Rng@{gu Set}).

(* CONTROLS: the two solution sets at a [Set] carrier. *)
Definition p450_grp_sols_at_set := @Diagonal_Grp_solution_set J D.
Definition p450_rng_sols_at_set := @Diagonal_Rng_solution_set J DR.

(* CONTROLS: [GAFT] at the same diagonal with every argument but the
   solution set, so that neither completeness nor continuity is what a
   [Set] carrier refuses. *)
Definition p450_grp_gaft_partial_at_set :=
  GAFT (@Diagonal Grp@{gu Set} J) Grp_Complete
       (Continuous_PreservesImageLimit Diagonal_continuous).
Definition p450_rng_gaft_partial_at_set :=
  GAFT (@Diagonal Rng@{gu Set} J) Rng_Complete
       (Continuous_PreservesImageLimit Diagonal_continuous).

Fail Definition p450_n4_grp_colim_at_set := Grp_colim_via_GAFT J.
Fail Definition p450_n5_rng_colim_at_set := Rng_colim_via_GAFT J.

End SetCarrier.

(** ** N6, N7 (UNIVERSE): the AFT side at [Set] carriers; Riehl's side and
    the words side are accepted there *)

(* CONTROLS, transplanted from the Riehl verification's scratch probe with
   this file's full import list: every statement that does not mention
   the adjoint functor theorem holds at [Z2@{Set}]. *)
Definition p450_words_at_set :=
  Grp_free_product_words_is_coequalizer Z2@{Set} Z2@{Set}.
Definition p450_generic_at_set@{u + | Set < u +}
  (CC : @Cocartesian Grp@{u Set}) :=
  Grp_coproduct_is_coequalizer Z2@{Set} Z2@{Set} CC.
Definition p450_canonical_at_set := Grp_canonical_presentation Z2@{Set}.
Definition p450_not_monic_at_set@{u + | Set < u +}
  (CC : @Cocartesian Grp@{u Set}) := Grp_riehl_e_not_monic CC.

(* CONTROL: the AFT side above [Set]. *)
Definition p450_aft_above_set@{u p + | Set < p, p < u +} :=
  Grp_free_product_is_coequalizer Z2@{p} Z2@{p}.

Fail Definition p450_n6_aft_at_set :=
  Grp_free_product_is_coequalizer Z2@{Set} Z2@{Set}.

(* CONTROL: the words coproduct at a [Set] carrier. *)
Definition p450_words_cocartesian_at_set@{u + | Set < u +} :
  @Cocartesian Grp@{u Set} := Grp_Cocartesian.

Fail Definition p450_n7_aft_cocartesian_at_set@{u + | Set < u +} :
  @Cocartesian Grp@{u Set} := Grp_Cocartesian_via_GAFT.

(** ** N8-N11 (CONVERSION): the letter-level facts are `≈`, not [eq_refl] *)

Section Letters.

Universes u p.

Context (G H : Grp@{u p}).
Context (w : FGWord (Grp_Forget G)) (g : carrier (grp_setoid G)).
Context {z : Grp@{u p}} (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z).

Local Notation UGH :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).
Local Notation UFUGH :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget (FreeGrp (Grp_Forget G)))
                                 (Grp_Forget (FreeGrp (Grp_Forget H)))).

(* CONTROL: both sides of N8 elaborate, so N8 is not a typing refusal. *)
Check (Grp_riehl_l G H (fg_insert UFUGH (Datatypes.inl w)),
       fg_insert UGH (Datatypes.inl (free_group_counit G w))).

(* CONTROL: the `≈` that holds, at exactly N8's statement. *)
Check (Grp_riehl_l_inl G H w :
  Grp_riehl_l G H (fg_insert UFUGH (Datatypes.inl w))
    ≈ fg_insert UGH (Datatypes.inl (free_group_counit G w))).

(* CONTROL: N8's `≈` again, closed by [FreeGrp]'s arrow map on a letter
   alone, with no fact about the counit: N8 is refused on that arrow map. *)
Definition p450_n8_by_fmap_alone :
  Grp_riehl_l G H (fg_insert UFUGH (Datatypes.inl w))
    ≈ fg_insert UGH (Datatypes.inl (free_group_counit G w)) :=
  @free_group_fmap_generators UFUGH UGH
    (@cover Sets Sets_Cocartesian _ _ _ _
       (fmap[Grp_Forget] (free_group_counit G))
       (fmap[Grp_Forget] (free_group_counit H))) (Datatypes.inl w).

Fail Example p450_n8_l_at_letter :
  Grp_riehl_l G H (fg_insert UFUGH (Datatypes.inl w))
    = fg_insert UGH (Datatypes.inl (free_group_counit G w)) := eq_refl.

(* CONTROL: the `≈` at N9's statement. *)
Check (Grp_riehl_r_inl G H w :
  Grp_riehl_r G H (fg_insert UFUGH (Datatypes.inl w))
    ≈ fmap[FreeGrp]
        (@inl Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)) w).

Fail Example p450_n9_r_at_letter :
  Grp_riehl_r G H (fg_insert UFUGH (Datatypes.inl w))
    = fmap[FreeGrp]
        (@inl Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)) w
  := eq_refl.

(* CONTROL: the `≈` at N10's statement. *)
Check (fun s : UGH => Grp_riehl_transpose_generator G H f1 f2 s :
  Grp_riehl_transpose G H f1 f2 (fg_insert UGH s)
    ≈ @merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                         (fmap[Grp_Forget] f2) s).

Fail Example p450_n10_transpose_at_letter (s : UGH) :
  Grp_riehl_transpose G H f1 f2 (fg_insert UGH s)
    = @merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                         (fmap[Grp_Forget] f2) s
  := eq_refl.

(* CONTROL: the `≈` at N11's statement, the counit on a letter. *)
Check (free_group_counit_generator G g :
  free_group_counit G (fg_insert (Grp_Forget G) g) ≈ g).

Fail Example p450_n11_counit_at_letter :
  free_group_counit G (fg_insert (Grp_Forget G) g) = g := eq_refl.

(* CONTROL: the UNIT does compute on a letter; the opacity is not the
   unit's. *)
Example p450_unit_at_letter :
  @Category.Theory.Adjunction.unit _ _ _ _ free_group_adjunction
     (Grp_Forget G) g
    = fg_insert (Grp_Forget G) g := eq_refl.

End Letters.

(** ** N12 (CONVERSION): Riehl's coproduct is not the AFT coproduct *)

(* CONTROL: Riehl's coproduct object IS the apex of the theorem's
   coequalizer of her pair. *)
Example p450_riehl_obj_is_coeq (G H : Grp) :
  @Coprod Grp Grp_Cocartesian_via_riehl G H
    = `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
            (Grp_riehl_l G H) (Grp_riehl_r G H)) := eq_refl.

(* CONTROL: and the agreement with the AFT coproduct is an isomorphism. *)
Check (fun G H : Grp => Grp_free_product_coequalizer_agrees G H :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
         (Grp_riehl_l G H) (Grp_riehl_r G H))
    ≅ @Coprod Grp Grp_Cocartesian_via_GAFT G H).

Fail Example p450_n12_riehl_obj_is_aft_obj (G H : Grp) :
  @Coprod Grp Grp_Cocartesian_via_riehl G H
    = @Coprod Grp Grp_Cocartesian_via_GAFT G H := eq_refl.

(** ** N13 (UNIVERSE): the ring ℤ stays at [Set]; the trivial group moved *)

(* CONTROL: the comparison #450 made possible for groups. *)
Definition p450_grp_initial_comparison :=
  initial_unique Grp_Initial_via_GAFT Grp_Initial.

(* CONTROL: ℤ is initial at [Set] carriers. *)
Check (Rng_Initial_Z : @Initial Rng@{_ Set}).

Fail Definition p450_n13_rng_initial_comparison :=
  initial_unique Rng_Initial_via_GAFT Rng_Initial_Z.

(** ** The zero object and [Z2] above [Set]: controls, formerly refused *)

Section AboveSet.

Universes u p.
Constraint Set < p.
Constraint p < u.

Definition p450_zero_above_set : ZeroObject Grp@{u p} := Grp_Zero@{u p}.
Definition p450_z2_above_set : GrpObject@{p p p} := Z2@{p}.
Definition p450_meet_above_set (G H : Grp@{u p}) :=
  Grp_free_product_meet_trivial G H.
Definition p450_nontrivial_above_set :
  (∀ a b : carrier (grp_setoid
                      (@Coprod Grp@{u p} Grp_Cocartesian_via_GAFT
                          Z2@{p} Z2@{p})), a ≈ b) → False :=
  Grp_free_product_via_GAFT_nontrivial.
Definition p450_riehl_nontrivial_above_set :
  Monic (Grp_riehl_e Z2@{p} Z2@{p}
           (Grp_Cocartesian_via_GAFT : @Cocartesian Grp@{u p})) → False :=
  Grp_free_product_coequalizer_nontrivial.

End AboveSet.

(** ** N14 (CONVERSION): the meet of the injections is the bottom up to
    `≈`, not on the nose *)

Section Disjoint.

Context {C : Category} `{Z : @ZeroObject C} `{CC : @Cocartesian C}.
Context `{PB : @HasPullbacks C} (x y : C).

(* CONTROL: the theorem, applied to EXACTLY six arguments -- C, Z, CC,
   PB, x, y -- and ascribed its full type; a [Cartesian] binder added to
   it would leave this a partial application and refuse the ascription. *)
Check (@coproduct_injections_meet_trivial C Z CC PB x y :
  sub_meet (sub_inl x y) (sub_inr x y) ≈ coprod_bot x y).

Fail Example p450_n14_meet_is_bottom :
  sub_meet (sub_inl x y) (sub_inr x y) = coprod_bot x y := eq_refl.

End Disjoint.

(* CONTROL: at groups, the bottom's domain IS the trivial group. *)
Example p450_bottom_is_trivial (G H : Grp) :
  sub_dom (@coprod_bot Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
    = Grp_trivial := eq_refl.

(** ** The diagonal's binders: shape objects strictly below the homs *)

Section DiagonalBinders.

Universes jo h o.
Constraint jo < h.

Context (C : Category@{o h h}) (J : Category@{jo h h}).

(* CONTROL: accepted with [jo < h]; were [Diagonal_continuous] left to
   minimization, which collapses J to one level, it would be refused. *)
Definition p450_diagonal_continuous : ContinuousFunctor (@Diagonal C J) :=
  @Diagonal_continuous C J.

End DiagonalBinders.

(** ** Guard block *)

Check @Diagonal_Grp_solution_set.
Check @Diagonal_Rng_solution_set.
Check @DCongIdx.
Check @RDCongIdx.
Check @DQ.
Check @RDQ.
Check @dker_cocone.
Check @rker_cocone.
Check @Grp_coproduct_agrees.
Check @Grp_free_product_iso.
Check @Grp_free_product_iso_inl.
Check @Grp_free_product_iso_inr.
Check @Grp_initial_agrees.
Check @Grp_coequalizer_agrees_normal_closure.
Check @Grp_free_product_meet_trivial.
Check @coproduct_injections_meet_trivial.
Check @coproduct_injections_pullback_zero.
Check @Grp_coproduct_is_coequalizer.
Check @Grp_free_product_is_coequalizer.
Check @Grp_free_product_words_is_coequalizer.
Check @Grp_Cocartesian_via_riehl.
Check @Grp_free_product_coequalizer_agrees.
Check @Grp_riehl_coproduct_agrees.
Check @Grp_riehl_pair_nontrivial.
Check @Grp_riehl_e_not_monic.
Check @coequalizer_unique_along.
Check @Diagonal_continuous.
Check @Diagonal_left_adjoint_HasColimits.
