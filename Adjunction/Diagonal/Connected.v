Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Shapes.
Require Import Category.Theory.Skeleton.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Connected.Components.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Constant.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Instance.One.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Adjunction.FullFaithful.

Generalizable All Variables.

(** * The colimit functor as a left-adjoint-left-inverse of the diagonal

    nLab: https://ncatlab.org/nlab/show/connected+category
    nLab: https://ncatlab.org/nlab/show/diagonal+functor
    nLab: https://ncatlab.org/nlab/show/colimit
    nLab: https://ncatlab.org/nlab/show/reflective+subcategory
    nLab: https://ncatlab.org/nlab/show/adjoint+functor

    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
    Springer GTM 5, 1998, section IV.4, printed page 95, exercise 5.
    Read from the page image and transliterated to ASCII:

      "5. If J is a connected category and D : C -> C^J has a left
       adjoint (colimit), show that this left adjoint can be chosen to
       be a left-adjoint-left-inverse."

    (Mac Lane writes the diagonal with a capital Delta, rendered "D"
    above; C^J is the functor category, this tree's [[J, C]].)  The
    exercise sits immediately after exercise 4, the three-clause
    characterization, which the same page states as:

      "4. Given a functor G : A -> X, prove the three following
       conditions logically equivalent:
       (a) G has a left-adjoint-left-inverse.
       (b) G has a left adjoint, and is full, faithful, and injective
           on objects.
       (c) There is a full reflective subcategory Y of X and an
           isomorphism H : A =~ Y such that G = KH, where K : Y -> X is
           the insertion."

    Exercise 4 is Adjunction/LeftInverse.v and exercise 3 is
    Theory/Equivalence/Strict.v; both are CONSUMED here and neither is
    rebuilt.  Exercises 1 and 2 of the same page are other catalog
    items and are neither claimed nor attempted.

    ** 1. WHAT IS DELIVERED, AND WHICH HALF IS UNCONDITIONAL

    UNCONDITIONAL, over an arbitrary [ConnectedNonempty J] and an
    arbitrary choice [L : HasColimitsOfShape J C]:

      - [diagonal_counit_iso] : the counit of [ColimitFunctor L] ⊣ Δ
        is an isomorphism at every constant diagram.  Its inverse is
        exhibited: it is the colimit injection at the chosen object
        [cn_obj K], and no essential-uniqueness machinery is used.
      - [diagonal_FFI] : Δ satisfies clause (b) of exercise 4 -- it has
        a left adjoint and is full, faithful, and injective on objects.
      - [diagonal_RI] : clause (c), by [ffi_implies_ri].  So Δ IS an
        isomorphism of C onto a full reflective subcategory of [[J, C]].
      - [colim_diagonal_iso_Id] : [ColimitFunctor L ◯ Δ ≈ Id[C]] in
        [Functor_Setoid], i.e. a natural isomorphism.

    CONDITIONAL, on the hypothesis [ConstantColimits J C] described in
    section 2 below, together with a POINT of the shape:

      - [colimit_is_lali_of_diagonal] (the issue's pinned name) :
        [LeftAdjointLeftInverse (@Diagonal C J)], clause (a).
      - [colim_diagonal_strict_Id] : the same comparison at
        [Functor_StrictEq_Setoid], which the unconditional half does
        not reach -- its object clause is refuted at an arbitrary
        choice and pinned in the probe.

    Read that hypothesis list exactly.  Given the record, the headline
    needs NO zig-zag: the counit clause is recovered from the record's
    injection clause at ONE object of the shape
    ([constant_colimits_counit], which takes [j0] and no
    [ConnectedNonempty]).  Connectedness is what the UNCONDITIONAL half
    spends -- [colim_const_inj_agree], and through it
    [diagonal_counit_iso] and [Diagonal_Full] -- and it is also what
    makes the record's demand a reasonable one to place: section (G)
    shows the record is NOT inhabited over a disconnected shape.

    The DUAL, for limits, needs no new record: with [S := LimitFunctor]
    and left adjoint Δ, Theory/Equivalence/Strict.v's
    [LeftAdjointRightInverse S] unfolds FIELD FOR FIELD to "Δ ⊣ Lim,
    [Lim (Δ c) = c], and the unit is the cast" -- which is what a
    "right-adjoint-right-inverse of Δ" says read from the other side.
    So [diagonal_is_lari_of_limit] is stated with that record and no
    lookalike is introduced; [RightAdjointRightInverse] and its
    siblings have zero occurrences tree-wide (measured at the base
    commit: `rg -n -w 'RightAdjointRightInverse'` returns nothing, and
    the only near hits for the family are #377's own
    [LeftAdjointRightInverse]).  The unit-is-an-isomorphism half,
    [diagonal_unit_limit_iso], is UNCONDITIONAL exactly as its colimit
    mirror is.

    ** 2. THE DESIGN CRUX, AND WHY THE STRICT CLAUSE NEEDS A HYPOTHESIS

    [LeftAdjointLeftInverse G] demands [lali_obj a : L (G a) = a] at
    LEIBNIZ equality together with [lali_counit a : counit a ≈
    id_cast (lali_obj a)].  At [G := Δ] and [L := ColimitFunctor H] the
    object action is the CHOSEN colimit [colimit_apex (H Δ[J](c))],
    which over a connected shape is isomorphic to [c] -- that is
    [diagonal_counit_iso], and it is proved here without hypothesis --
    but is not [c] on the nose.  Mac Lane's "can be CHOSEN" re-chooses
    the colimit of each CONSTANT diagram to be the constant itself with
    the identity cocone.  In a proof-relevant setting a choice function
    [H : ∀ F, Colimit F] cannot inspect [F] for constancy: membership
    in the image of Δ is the type [{ c & Δ[J](c) = F }], objects of
    [[J, C]] being functor RECORDS compared at Leibniz equality, and
    nothing decides it.  This is the same obstruction
    Adjunction/LeftInverse.v records for the third leg of its own
    characterization, and it is why that leg is conditional there too.

    So the hypothesis is carried in the TYPE, as a record naming the
    choice that Mac Lane's sentence makes:

      [ConstantColimits J C] = a family of colimits [cc_colim],
      together with [cc_obj c : colim_obj cc_colim Δ[J](c) = c] and
      [cc_inj c j : colim_inj cc_colim Δ[J](c) j ≈ id_cast (eq_sym
      (cc_obj c))].

    Both extra fields are statements about the CHOSEN colimit data --
    apex and injections -- rather than about the adjunction, so the
    hypothesis can be checked directly at a candidate choice, and the
    counit clause the record does not mention is DERIVED
    ([constant_colimits_counit]).

    ** 3. THE HYPOTHESIS IS INHABITED, AND NOT ONLY DEGENERATELY

    [terminal_ConstantColimits] : if the SHAPE J has a terminal object
    then [ConstantColimits J C] holds for EVERY C, with its two PROOF
    fields at [eq_refl]/[reflexivity] (the third field is the chosen
    family [terminal_colimits] itself).  The colimit chosen is
    Structure/Limit/Initial.v's [terminal_Colimit], whose apex is
    [F (terminal_obj)] definitionally, so at [F := Δ[J](c)] the apex IS
    [c] and every injection IS [id[c]].  A category with a terminal
    object is connected ([terminal_ConnectedNonempty], consumed from
    Theory/Connected/Components.v), so the hypothesis of the exercise
    is met at the same shapes.  Witnesses: [Ordinal (S n)] through
    [Ordinal_Succ_Terminal] -- at [n := 1] a shape with two provably
    distinct objects -- and the walking arrow [_2] through
    Instance/Two/Monoidal.v's pre-existing [Two_Terminal], which is
    reused rather than rebuilt.

    DISCLOSED: over a shape with a terminal object the colimit functor
    IS evaluation at that object on objects ([colimit_is_EvalAt],
    [eq_refl]), so
    these inhabitants are the ones where the exercise's "choice" is
    forced rather than genuinely made.  NO inhabitant of
    [ConstantColimits] is exhibited at a connected shape WITHOUT a
    terminal object, and none is claimed to exist.

    ** 4. THE OBVIOUS CANDIDATE FOR AN UNCONDITIONAL LEFT ADJOINT, AND
          EXACTLY WHAT GOES WRONG WITH IT

    Since [fobj[Δ[J](c)] j] reduces to [c], the evaluation functor
    [EvalAt j0 : [J, C] ⟶ C] retracts Δ ON THE NOSE
    ([EvalAt_retracts], [eq_refl]) -- it is the one obvious candidate
    for a strict left inverse.  What it is not, in general, is a LEFT
    ADJOINT to Δ: that would say the colimit of every diagram is
    computed at [j0].  [eval_not_left_adjoint] proves this cannot be
    repaired by connectedness alone -- over the CONNECTED shape [_2]
    and the ambient [Coq], [EvalAt TwoX ⊣ Δ] is refuted.  The argument
    is uniqueness of left adjoints ([left_adjoint_iso]) against the
    colimit functor for the terminal choice, which over [_2] evaluates
    at [TwoY]; at the diagram [TwoGap] carrying [Empty_set] to [bool]
    that would give [Empty_set ≅ bool].  So the candidate is refuted at
    a shape satisfying every hypothesis of the exercise, which is what
    makes the refutation informative.

    The positive half of the same measurement is [colimit_is_EvalAt]:
    when [j0] IS terminal, evaluation at [j0] is the colimit functor on
    the nose on objects (the arrow actions do not convert, and only the
    object clause is claimed), and that is exactly the case in which
    [terminal_ConstantColimits] applies.

    ** 5. THE REGRESSION EXAMPLE: CONNECTEDNESS CANNOT BE DROPPED

    Over the two-object discrete shape [Two_Discrete], with ambient
    [Coq], the following are all refuted, for EVERY choice of colimits:

      - [two_discrete_counit_not_iso] : the counit is not invertible at
        every object.  Proved through #367's
        [right_adjoint_fully_faithful_iff_counit_iso] against
        Structure/Limit/Constant.v's [Diagonal_Two_Discrete_not_Full],
        so no property of the chosen colimits is used.
      - [two_discrete_no_ffi], [two_discrete_no_lali] : clauses (b) and
        (a) of exercise 4 both go.
      - [two_discrete_no_constant_colimits] : the hypothesis of
        section 2 is not inhabited there either.

    Structure/Limit/Constant.v had already proved both halves of
    [ConnectedNonempty] necessary for the constant (co)limit itself;
    what is added here is that the ADJUNCTION-level clauses go with
    them.

    ** 6. PRIOR ART, MEASURED AT THE BASE COMMIT

    The issue's "Current state" is stale on every donor it names.  All
    of the following exist and are consumed, not rebuilt:
    [Colimit_Diagonal_Adjunction] (Adjunction/Diagonal/Limit.v:771),
    [HasColimitsOfShape] (:365), [ColimitFunctor] (:696), [colim_unit]
    (:789), [Diagonal_Limit_Adjunction] (:527), [lim_counit] (:547);
    [const_IsAColimit] (Structure/Limit/Constant.v:533),
    [const_IsALimit] (:448), [const_cocone] (:512), [leg_zigzag]
    (:403), [Diagonal_Faithful] (:810), [Diagonal_Full] (:828),
    [Diagonal_Two_Discrete_not_Full] (:1043);
    [ConnectedNonempty] (Theory/Connected/Components.v:771),
    [terminal_ConnectedNonempty] (:836);
    [LeftAdjointLeftInverse] (Adjunction/LeftInverse.v:371),
    [LeftAdjointFFInjective] (:592), [lali_implies_ffi] (:606),
    [ffi_implies_ri] (:765), [InjectiveOnObjects] (:352);
    [LeftAdjointRightInverse] (Theory/Equivalence/Strict.v:318);
    [terminal_Colimit] (Structure/Limit/Initial.v:470),
    [initial_Limit] (:318), [Ordinal_Succ_Terminal] (:630),
    [One_Initial] (:526), [Omega_Initial] (:679);
    [Two_Terminal] (Instance/Two/Monoidal.v:95);
    [Walk] (Theory/Shapes.v:336);
    [right_adjoint_fully_faithful_iff_counit_iso]
    (Adjunction/FullFaithful.v:475);
    [strict_equiv_of_id_cast_nat] (Theory/Skeleton.v:229).

    NEW here: [EvalAt], the evaluation functor [[J, C] ⟶ C] at an
    object of the shape.  Measured by TYPE rather than by name: the
    tree's only evaluation-shaped functors out of a functor category
    are [YoEvalAt] (into [Sets]) and [One_Eval] (out of [[_1, C]]) --
    the latter IS this one's [J := _1] special case, with the same two
    data bodies, and neither is the general constant.

    ** 7. STRENGTHS, MEASURED STRICT-FIRST

    Holding at [eq_refl]: [diagonal_counit_strict] (the counit IS
    [colim_transpose_from] of the identity); [EvalAt_retracts];
    [colimit_is_EvalAt] (the OBJECT action, at a shape with a terminal
    object -- the arrow action is a conversion rejection, pinned in the
    probe, and is not claimed at any strength);
    [terminal_colimit_obj_strict] and
    [terminal_colimit_inj_strict]; [lali_left_strict] and
    [lali_obj_strict] (the produced left-adjoint-left-inverse's functor
    IS [ColimitFunctor] and its object equation IS the record's own);
    the mirrors on the limit side.

    Reaching only [≈], with the cause: [constant_colimits_counit]
    (the counit is recovered from the injections through one
    [id_cast_inv_l], so it is an equation between two morphisms and not
    a definitional unfolding); [diagonal_counit_iso]'s two laws; and
    the mirrors on the limit side, [constant_limits_unit] and
    [diagonal_unit_limit_iso]'s two laws.

    Also holding at [eq_refl], and load-bearing for the two [Defined]s
    of this file (measured by flipping each to [Qed] in a scratch copy,
    where each alone breaks the readback):
    [colim_diagonal_iso_Id_component] -- the component family of the
    natural isomorphism IS [diagonal_counit_Isomorphism] -- and
    [colim_diagonal_strict_Id_obj], whose object-equality family IS the
    record's own [cc_obj].

    REFUTED and pinned in Test/ProbeConnected378.v, in three kinds: the
    unconditional [colim_obj L Δ[J](c) = c] at an arbitrary choice (a
    CONVERSION rejection -- the apex is the chosen one and nothing
    reduces); the unconditional [colim_inj L Δ[J](c) j = id[c]], which
    is a TYPING rejection rather than a conversion one and is the
    sharper of the two, the two sides having DIFFERENT CODOMAINS until
    the apex equation is supplied; [diagonal_counit] against the leg of
    Structure/Limit/Unique.v's [colimit_unique_iso] (the same morphism
    up to [≈], two different mediator terms); and the arity rejection
    that [colimit_is_lali_of_diagonal] does not accept a bare
    [HasColimitsOfShape] in place of the record.

    ** 8. UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK

    Every constant of the general sections is over [J : Category@{jo jh
    jh}] and [C : Category@{co ch ch}] -- hom identified with proof in
    the BINDER of each, no such equation in any block -- with the
    constraint blocks carrying the single equation [jh = ch] and no
    [Set].  Two constants carry one equation more: [diagonal_FFI] and
    [diagonal_RI] also identify [ConnectedNonempty]'s own universe
    with the shape's hom level, which is [Diagonal_Full]'s doing (it
    takes the record at exactly that level; [diagonal_counit_iso],
    which consumes the same record through [leg_zigzag], does not).
    The two object universes are bounded and never identified.
    [ConstantColimits] and [ConstantLimits] present the same content
    differently: their binders read [Category@{jo jh jh} ->
    Category@{co jh jh} -> Type], writing ONE level for both hom slots,
    so a reader who checks only their blocks sees no equation and is
    wrong.

    Both identifications are the DONORS', and each has three donors
    that are sufficient ALONE in a command, probed in
    Test/ProbeConnected378.v with [Ju ⟶ Cu] accepted at the very levels
    where they are rejected -- so [Functor] is NOT among them:

      - [jh = ch] : [Fun] (the functor category itself),
        [HasColimitsOfShape], and [Diagonal].
      - hom = proof : [LeftAdjointLeftInverse], [HasColimitsOfShape],
        and [Diagonal].

    Read "three donors" as donors and NOT as three independent causes.
    [Diagonal]'s type is [C ⟶ [J, C]], so it cannot be tested apart
    from [Fun]; [LeftAdjointLeftInverse] cannot be tested apart from
    [Adjunction], which is itself rejected at hom < proof with no
    left-inverse in the command (measured); and [ConstantColimits] is
    rejected too but says nothing of its own, [HasColimitsOfShape]
    being one of its fields.  What IS measured to be independent of
    [Fun] is [HasColimitsOfShape], rejected through [Limit]: at hom
    levels declared apart [Cone F] elaborates while [Limit F] does not,
    and Structure/Limit.v requires no functor category.  So the
    underlying causes are [Fun], [Limit] and [Adjunction], and the
    three constants named above are their proxies.

    Neither identification is claimed unavoidable, and neither is
    introduced here.

    [EvalAt]'s explicit binders ARE load-bearing and were added on a
    measurement: written unannotated the same body minimizes to
    [J : Category@{u u u}], identifying the shape's OBJECT universe with
    its hom universe for no reason of its own; annotated, the only
    equation left is [jh = ch].

    EIGHT of the 79 constants carry a [Set] token, all of them in the
    concrete witness blocks: [two_ConstantColimits] and [two_lali] in
    section (D), [TwoGap] and [eval_not_left_adjoint] in section (E),
    and the four [two_discrete_*] results of section (G).  It is
    inherited from [_2] and [Two_Discrete], whose hom families are
    declared at [Set]; every general constant, [EvalAt] included,
    carries none.

    Module closure: 137 transitive in-project dependencies, excluding
    this file.  Measured per [Require], the marginal costs are
    Adjunction/FullFaithful.v 20, Structure/Limit/Constant.v 6,
    Theory/Shapes.v 2, Theory/Equivalence/Strict.v 2,
    Instance/Two/Monoidal.v 2, and ZERO for every other line.  The 20 is
    the price of section (G)'s regression example and of the #367
    cross-check, and is paid deliberately rather than by reproving that
    biconditional here.

    ** 9. WHAT IS NOT DELIVERED

      - No unconditional [LeftAdjointLeftInverse (@Diagonal C J)]:
        section 2 explains the obstruction and section 4 refutes the
        one obvious candidate, but no impossibility THEOREM is stated
        and none is claimed.
      - No inhabitant of [ConstantColimits] at a connected shape
        lacking a terminal object, and no proof that none exists.
      - No converse to [terminal_ConstantColimits], so it is not shown
        that a shape carrying such a choice must have a terminal
        object.
      - No monad or comonad from either adjunction, no uniqueness
        statement for the adjoint beyond [left_adjoint_iso] as
        consumed, no naturality of any identification in [J] or [C],
        and nothing registered as an [Instance] -- every definition
        here is a plain [Definition] or [Program Definition], since a
        chosen colimit must not become globally resolvable.
      - No relation to Structure/Limit/Constant.v's [AbsoluteLimit],
        and no cone-level preservation statement. *)

(* ------------------------------------------------------------------ *)
(** * (A) The counit at a constant diagram is invertible *)

Section ConnectedCounit.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).

(* The counit of colim ⊣ Δ read at the constant diagram on c. *)

Definition diagonal_counit (c : C) : colim_obj L Δ[J](c) ~{C}~> c :=
  @counit C ([J, C]) (ColimitFunctor L) (@Diagonal C J)
          (Colimit_Diagonal_Adjunction L) c.

Example diagonal_counit_strict (c : C) :
  diagonal_counit c = colim_transpose_from L (id{[J, C]}) := eq_refl.

(* Every triangle of the counit is an identity: the transposition takes
   the identity transformation, whose components are [fmap[Δ] id]. *)

Lemma diagonal_counit_commutes (c : C) (j : J) :
  diagonal_counit c ∘ colim_inj L Δ[J](c) j ≈ id.
Proof.
  unfold diagonal_counit.
  rewrite (colim_transpose_from_commutes L (id{[J, C]}) j).
  simpl; reflexivity.
Qed.

(* The injections of the colimit of a CONSTANT diagram all agree: the
   coherence condition reads [inj y ∘ id ≈ inj x] along every arrow, and
   [leg_zigzag] propagates that along a zig-zag.  This is the one place
   connectedness is spent in this section. *)

Lemma colim_const_inj_agree (c : C) (x y : J) :
  colim_inj L Δ[J](c) x ≈ colim_inj L Δ[J](c) y.
Proof using K.
  apply (@leg_zigzag J C c (colim_obj L Δ[J](c))
           (fun j => colim_inj L Δ[J](c) j)).
  - intros p q f; simpl.
    rewrite <- (colim_inj_coherence L Δ[J](c) f); simpl.
    now rewrite id_right.
  - exact (cn_zigzag K x y).
Qed.

(* The inverse is the injection at the chosen object.  Nothing here
   appeals to essential uniqueness of colimits: one composite is a
   triangle, the other is proved by the colimit's own uniqueness
   clause against the colimit cocone. *)

Definition diagonal_counit_inverse (c : C) :
  c ~{C}~> colim_obj L Δ[J](c) := colim_inj L Δ[J](c) (cn_obj K).

Program Definition diagonal_counit_iso (c : C) :
  IsIsomorphism (diagonal_counit c) := {|
  two_sided_inverse := diagonal_counit_inverse c
|}.
Next Obligation.
  apply (diagonal_counit_commutes c (cn_obj K)).
Qed.
Next Obligation.
  apply (colim_med_eq L
           (@Cocone_of J C Δ[J](c) (colim_obj L Δ[J](c))
              (fun j => colim_inj L Δ[J](c) j)
              (fun x y f => colim_inj_coherence L Δ[J](c) f)));
    intro j; simpl.
  - unfold diagonal_counit_inverse.
    rewrite <- comp_assoc, (diagonal_counit_commutes c j), id_right.
    apply colim_const_inj_agree.
  - apply id_left.
Qed.

Definition diagonal_counit_Isomorphism (c : C) :
  colim_obj L Δ[J](c) ≅ c := {|
  to := diagonal_counit c;
  from := diagonal_counit_inverse c;
  iso_to_from := diagonal_counit_iso_obligation_1 c;
  iso_from_to := diagonal_counit_iso_obligation_2 c
|}.

Example diagonal_counit_Isomorphism_to (c : C) :
  to (diagonal_counit_Isomorphism c) = diagonal_counit c := eq_refl.

End ConnectedCounit.

(* Naturality of the counit at constant diagrams.  This costs NO
   connectedness -- it is the naturality square of the counit, proved
   through the colimit's uniqueness clause -- and it is what upgrades
   the family of isomorphisms above to a natural one. *)

Section CounitNaturality.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).

Lemma colim_delta_nat {x y : C} (f : x ~{C}~> y) :
  diagonal_counit L y ∘ Colim_map L (fmap[@Diagonal C J] f)
    ≈ f ∘ diagonal_counit L x.
Proof.
  apply (colim_med_eq L
           (@Cocone_of J C Δ[J](x) y (fun _ : J => f)
              (fun p q g => id_right f)));
    intro j; simpl.
  - rewrite <- comp_assoc,
      (Colim_map_commutes L (fmap[@Diagonal C J] f) j).
    rewrite comp_assoc, (diagonal_counit_commutes L y j); simpl.
    now rewrite id_left.
  - rewrite <- comp_assoc, (diagonal_counit_commutes L x j).
    now rewrite id_right.
Qed.

End CounitNaturality.

Section ConnectedNatIso.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).

(* [ColimitFunctor L ◯ Δ ≈ Id[C]] as functors: a natural isomorphism,
   which is what [≈] means at [Functor_Setoid]. *)

Definition colim_diagonal_iso_Id :
  @equiv _ (@Functor_Setoid C C) (ColimitFunctor L ◯ @Diagonal C J)
         Id[C].
Proof using K.
  exists (fun c => diagonal_counit_Isomorphism L K c).
  intros x y f; simpl.
  symmetry.
  rewrite <- comp_assoc.
  rewrite <- (colim_delta_nat L f).
  rewrite comp_assoc.
  rewrite (iso_from_to (diagonal_counit_Isomorphism L K y)).
  now rewrite id_left.
Defined.

(* The [Defined] is load-bearing: with [Qed] the component family does
   not reduce and this readback is lost (measured, by flipping it in a
   scratch copy). *)

Example colim_diagonal_iso_Id_component (c : C) :
  `1 colim_diagonal_iso_Id c = diagonal_counit_Isomorphism L K c
  := eq_refl.

End ConnectedNatIso.

(* ------------------------------------------------------------------ *)
(** * (B) Clauses (b) and (c) of exercise 4, unconditionally *)

Section ConnectedFFI.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).

(* Injectivity on objects needs only an OBJECT of the shape: the object
   action of a constant functor at that object IS the constant. *)

Definition Diagonal_InjectiveOnObjects :
  InjectiveOnObjects (@Diagonal C J) :=
  fun c c' H => f_equal (fun F : [J, C] => fobj[F] (cn_obj K)) H.

Definition diagonal_FFI : LeftAdjointFFInjective (@Diagonal C J) := {|
  ffi_left := ColimitFunctor L;
  ffi_adj := Colimit_Diagonal_Adjunction L;
  ffi_full := Diagonal_Full K;
  ffi_faithful := Diagonal_Faithful (cn_obj K);
  ffi_injective := Diagonal_InjectiveOnObjects
|}.

Definition diagonal_RI : ReflectiveIsoPresentation (@Diagonal C J) :=
  ffi_implies_ri diagonal_FFI.

(* Cross-check against #367: fullness and faithfulness of Δ read off
   the invertible counit rather than off Structure/Limit/Constant.v.
   The two [Full] records are NOT compared -- their sections are
   distinct opaque terms -- so this is a second route to the same
   statement, not an identification. *)

Definition diagonal_fully_faithful_of_counit :
  (Full (@Diagonal C J) * Faithful (@Diagonal C J))%type :=
  snd (@right_adjoint_fully_faithful_iff_counit_iso
         C ([J, C]) (ColimitFunctor L) (@Diagonal C J)
         (Colimit_Diagonal_Adjunction L))
      (fun c => diagonal_counit_iso L K c).

End ConnectedFFI.

(* ------------------------------------------------------------------ *)
(** * (C) The choice Mac Lane's sentence makes, and clause (a) *)

(* The hypothesis is a statement about the CHOSEN colimit data at
   constant diagrams: its apex is the constant on the nose, and its
   injections are the corresponding cast.  Section 2 of the header
   explains why no such choice is derivable from a bare
   [HasColimitsOfShape]. *)

Record ConstantColimits (J C : Category) : Type := {
  cc_colim : HasColimitsOfShape J C;
  cc_obj (c : C) : colim_obj cc_colim Δ[J](c) = c;
  cc_inj (c : C) (j : J) :
    colim_inj cc_colim Δ[J](c) j ≈ id_cast (eq_sym (cc_obj c))
}.

Arguments cc_colim {J C} _.
Arguments cc_obj {J C} _ _.
Arguments cc_inj {J C} _ _ _.

Section ConstantChoice.

Context {J C : Category}.
Context (j0 : J).
Context (P : ConstantColimits J C).

(* The counit clause the record does not state is derived from the
   injection clause at ANY single object of the shape -- so this step
   needs a point of J and no zig-zag. *)

Lemma constant_colimits_counit (c : C) :
  diagonal_counit (cc_colim P) c ≈ id_cast (cc_obj P c).
Proof using P j0.
  rewrite <- (id_left (id_cast (cc_obj P c))).
  rewrite <- (diagonal_counit_commutes (cc_colim P) c j0).
  rewrite <- comp_assoc, (cc_inj P c j0).
  now rewrite id_cast_inv_l, id_right.
Qed.

Definition colimit_is_lali_of_diagonal :
  LeftAdjointLeftInverse (@Diagonal C J) := {|
  lali_left := ColimitFunctor (cc_colim P);
  lali_adj := Colimit_Diagonal_Adjunction (cc_colim P);
  lali_obj := cc_obj P;
  lali_counit := constant_colimits_counit
|}.

Example lali_left_strict :
  lali_left colimit_is_lali_of_diagonal = ColimitFunctor (cc_colim P)
  := eq_refl.

Example lali_obj_strict (c : C) :
  lali_obj colimit_is_lali_of_diagonal c = cc_obj P c := eq_refl.

(* Clause (a) now feeds exercise 4's cycle, all of it consumed. *)

Definition colimit_lali_ffi : LeftAdjointFFInjective (@Diagonal C J) :=
  lali_implies_ffi colimit_is_lali_of_diagonal.

Definition colimit_lali_ri : ReflectiveIsoPresentation (@Diagonal C J) :=
  lali_implies_ri colimit_is_lali_of_diagonal.

(* The comparison at STRICT functor equality, which section (A)'s
   natural isomorphism cannot reach.  The coherence square is
   [colim_delta_nat] read through the derived counit clause. *)

Definition colim_diagonal_strict_Id :
  @equiv _ (@Functor_StrictEq_Setoid C C)
         (ColimitFunctor (cc_colim P) ◯ @Diagonal C J) Id[C].
Proof using P j0.
  apply (strict_equiv_of_id_cast_nat
           (ColimitFunctor (cc_colim P) ◯ @Diagonal C J) Id[C]
           (fun c => cc_obj P c)).
  intros x y f; simpl.
  rewrite <- (constant_colimits_counit x).
  rewrite <- (constant_colimits_counit y).
  apply colim_delta_nat.
Defined.

(* Load-bearing for the same reason: the object-equality family of the
   strict comparison IS the record's own. *)

Example colim_diagonal_strict_Id_obj (c : C) :
  `1 colim_diagonal_strict_Id c = cc_obj P c := eq_refl.

End ConstantChoice.

(* ------------------------------------------------------------------ *)
(** * (D) The hypothesis is inhabited: shapes with a terminal object *)

Section TerminalShape.

Context {J C : Category}.
Context (T : @Terminal J).

Definition terminal_colimits : HasColimitsOfShape J C :=
  fun F => @terminal_Colimit J C T F.

Example terminal_colimit_obj_strict (c : C) :
  colim_obj terminal_colimits Δ[J](c) = c := eq_refl.

Example terminal_colimit_inj_strict (c : C) (j : J) :
  colim_inj terminal_colimits Δ[J](c) j = id[c] := eq_refl.

Definition terminal_ConstantColimits : ConstantColimits J C := {|
  cc_colim := terminal_colimits;
  cc_obj := fun c => eq_refl;
  cc_inj := fun c j => reflexivity _
|}.

Definition terminal_lali_of_diagonal :
  LeftAdjointLeftInverse (@Diagonal C J) :=
  colimit_is_lali_of_diagonal (@terminal_obj J T)
    terminal_ConstantColimits.

(* And such a shape satisfies the exercise's own hypothesis. *)

Definition terminal_shape_connected : ConnectedNonempty J :=
  terminal_ConnectedNonempty T.

End TerminalShape.

(** ** Evaluation at an object of the shape *)

(* The one obvious candidate for a strict left inverse of Δ, and the
   subject of section 4 of the header. *)

(* The explicit binders are LOAD-BEARING: written unannotated the same
   body minimizes to [J : Category@{u u u}], identifying the shape's
   OBJECT universe with its hom universe for no reason of its own.
   Annotated, the only equation left is [jh = ch], which is [Fun]'s. *)

Program Definition EvalAt@{jo jh co ch +} {J : Category@{jo jh jh}}
  {C : Category@{co ch ch}} (j : J) : [J, C] ⟶ C := {|
  fobj := fun F => F j;
  fmap := fun _ _ t => transform[t] j
|}.

Example EvalAt_retracts@{jo jh co ch +} {J : Category@{jo jh jh}}
  {C : Category@{co ch ch}} (j : J) (c : C) :
  fobj[@EvalAt J C j] Δ[J](c) = c := eq_refl.

(* When the object IS terminal, evaluation there is the colimit functor
   on the nose ON OBJECTS.  The two arrow actions are the colimit
   mediator and the component, different terms that do not convert; the
   strict form is refuted and pinned in the probe, and no [≈] form is
   stated. *)

Example colimit_is_EvalAt@{jo jh co ch +} {J : Category@{jo jh jh}}
  {C : Category@{co ch ch}} (T : @Terminal J) (F : [J, C]) :
  fobj[ColimitFunctor (@terminal_colimits J C T)] F
    = fobj[@EvalAt J C (@terminal_obj J T)] F := eq_refl.

(** ** Concrete witnesses *)

(* [Ordinal (S n)] has a terminal object, so it carries the choice for
   every ambient category; at [n := 1] the shape is not degenerate. *)

Definition ordinal_ConstantColimits (n : nat) (C : Category) :
  ConstantColimits (Ordinal (S n)) C :=
  @terminal_ConstantColimits (Ordinal (S n)) C (Ordinal_Succ_Terminal n).

Definition ordinal_lali (n : nat) (C : Category) :
  LeftAdjointLeftInverse (@Diagonal C (Ordinal (S n))) :=
  @terminal_lali_of_diagonal (Ordinal (S n)) C (Ordinal_Succ_Terminal n).

Theorem ordinal_two_not_degenerate :
  ord_top 1 <> ord_bot 1.
Proof. exact (ord_top_neq_bot 0). Qed.

(* The walking arrow, through the pre-existing [Two_Terminal]. *)

Definition two_ConstantColimits (C : Category) : ConstantColimits _2 C :=
  @terminal_ConstantColimits _2 C Two_Terminal.

Definition two_lali (C : Category) :
  LeftAdjointLeftInverse (@Diagonal C _2) :=
  @terminal_lali_of_diagonal _2 C Two_Terminal.

(* ------------------------------------------------------------------ *)
(** * (E) Evaluation at a NON-terminal object is not a left adjoint *)

(* The diagram over the walking arrow carrying the empty type to the
   booleans.  Built with Theory/Shapes.v's [Walk], so no functor laws
   are discharged here. *)

Definition TwoGap : _2 ⟶ Coq :=
  @Walk Coq (Empty_set : Coq) (bool : Coq)
        (fun z => match z return bool with end).

Example TwoGap_X : fobj[TwoGap] TwoX = Empty_set := eq_refl.
Example TwoGap_Y : fobj[TwoGap] TwoY = bool := eq_refl.

(* [_2] is connected and inhabited, so this refutes the candidate at a
   shape meeting every hypothesis of the exercise. *)

Theorem eval_not_left_adjoint :
  @EvalAt _2 Coq TwoX ⊣ @Diagonal Coq _2 → False.
Proof.
  intro A.
  pose proof (left_adjoint_iso (@Diagonal Coq _2) (@EvalAt _2 Coq TwoX)
                (ColimitFunctor (@terminal_colimits _2 Coq Two_Terminal))
                A
                (Colimit_Diagonal_Adjunction
                   (@terminal_colimits _2 Coq Two_Terminal))) as E.
  destruct E as [iso _].
  destruct (from (iso TwoGap) true).
Qed.

(* ------------------------------------------------------------------ *)
(** * (F) The dual: Δ is a left-adjoint-right-inverse of the limit *)

Section ConnectedUnit.

Context {J C : Category}.
Context (H : HasLimitsOfShape J C).
Context (K : ConnectedNonempty J).

Definition diagonal_limit_unit (c : C) : c ~{C}~> lim_obj H Δ[J](c) :=
  @unit ([J, C]) C (@Diagonal C J) (LimitFunctor H)
        (Diagonal_Limit_Adjunction H) c.

Lemma diagonal_unit_commutes (c : C) (j : J) :
  lim_leg H Δ[J](c) j ∘ diagonal_limit_unit c ≈ id.
Proof.
  unfold diagonal_limit_unit.
  rewrite (lim_transpose_to_commutes H (id{[J, C]}) j).
  simpl; reflexivity.
Qed.

Lemma lim_const_leg_agree (c : C) (x y : J) :
  lim_leg H Δ[J](c) x ≈ lim_leg H Δ[J](c) y.
Proof using K.
  apply (@leg_zigzag J C (lim_obj H Δ[J](c)) c
           (fun j => lim_leg H Δ[J](c) j)).
  - intros p q f; simpl.
    rewrite <- (lim_leg_coherence H Δ[J](c) f); simpl.
    now rewrite id_left.
  - exact (cn_zigzag K x y).
Qed.

Program Definition diagonal_unit_limit_iso (c : C) :
  IsIsomorphism (diagonal_limit_unit c) := {|
  two_sided_inverse := lim_leg H Δ[J](c) (cn_obj K)
|}.
Next Obligation.
  apply (lim_med_eq H
           {| vertex_obj := lim_obj H Δ[J](c)
            ; coneFrom :=
                {| vertex_map := fun j => lim_leg H Δ[J](c) j
                 ; cone_coherence := fun x y f =>
                     lim_leg_coherence H Δ[J](c) f |} |});
    intro j; simpl.
  - rewrite comp_assoc, (diagonal_unit_commutes c j), id_left.
    apply lim_const_leg_agree.
  - apply id_right.
Qed.
Next Obligation.
  apply (diagonal_unit_commutes c (cn_obj K)).
Qed.

End ConnectedUnit.

(* The dual hypothesis, and the dual headline.  Note that no new record
   is introduced for the conclusion: Theory/Equivalence/Strict.v's
   [LeftAdjointRightInverse S], read at [S := LimitFunctor], IS the
   statement that Δ is a right-inverse of the limit functor and left
   adjoint to it. *)

Record ConstantLimits (J C : Category) : Type := {
  cl_limit : HasLimitsOfShape J C;
  cl_obj (c : C) : lim_obj cl_limit Δ[J](c) = c;
  cl_leg (c : C) (j : J) :
    lim_leg cl_limit Δ[J](c) j ≈ id_cast (cl_obj c)
}.

Arguments cl_limit {J C} _.
Arguments cl_obj {J C} _ _.
Arguments cl_leg {J C} _ _ _.

Section ConstantLimitChoice.

Context {J C : Category}.
Context (j0 : J).
Context (Q : ConstantLimits J C).

Lemma constant_limits_unit (c : C) :
  diagonal_limit_unit (cl_limit Q) c ≈ id_cast (eq_sym (cl_obj Q c)).
Proof using Q j0.
  rewrite <- (id_right (id_cast (eq_sym (cl_obj Q c)))).
  rewrite <- (diagonal_unit_commutes (cl_limit Q) c j0).
  rewrite comp_assoc, (cl_leg Q c j0).
  now rewrite id_cast_inv_l, id_left.
Qed.

Definition diagonal_is_lari_of_limit :
  LeftAdjointRightInverse (LimitFunctor (cl_limit Q)) := {|
  lari_left := @Diagonal C J;
  lari_adj := Diagonal_Limit_Adjunction (cl_limit Q);
  lari_obj := cl_obj Q;
  lari_unit := constant_limits_unit
|}.

Example lari_left_strict :
  lari_left diagonal_is_lari_of_limit = @Diagonal C J := eq_refl.

Example lari_obj_strict (c : C) :
  lari_obj diagonal_is_lari_of_limit c = cl_obj Q c := eq_refl.

End ConstantLimitChoice.

(* Inhabited whenever the SHAPE has an initial object -- the mirror of
   section (D), and such a shape is connected. *)

Section InitialShape.

Context {J C : Category}.
Context (I : @Initial J).

Definition initial_limits : HasLimitsOfShape J C :=
  fun F => @initial_Limit J C I F.

Example initial_limit_obj_strict (c : C) :
  lim_obj initial_limits Δ[J](c) = c := eq_refl.

Example initial_limit_leg_strict (c : C) (j : J) :
  lim_leg initial_limits Δ[J](c) j = id[c] := eq_refl.

Definition initial_ConstantLimits : ConstantLimits J C := {|
  cl_limit := initial_limits;
  cl_obj := fun c => eq_refl;
  cl_leg := fun c j => reflexivity _
|}.

Definition initial_lari_of_limit :
  LeftAdjointRightInverse (LimitFunctor initial_limits) :=
  diagonal_is_lari_of_limit (@initial_obj J I) initial_ConstantLimits.

End InitialShape.

(* Witnesses: the point, and the infinite chain omega. *)

Definition one_ConstantLimits (C : Category) : ConstantLimits _1 C :=
  @initial_ConstantLimits _1 C One_Initial.

Definition omega_ConstantLimits (C : Category) :
  ConstantLimits Omega C :=
  @initial_ConstantLimits Omega C Omega_Initial.

Definition omega_lari (C : Category) :
  LeftAdjointRightInverse
    (LimitFunctor (@initial_limits Omega C Omega_Initial)) :=
  @initial_lari_of_limit Omega C Omega_Initial.

(* ------------------------------------------------------------------ *)
(** * (G) The regression: connectedness cannot be dropped *)

(* Every statement below is for an ARBITRARY choice of colimits over the
   two-object discrete shape, so none of them turns on which colimits
   were chosen. *)

Theorem two_discrete_counit_not_iso
  (L : HasColimitsOfShape Two_Discrete Coq) :
  (∀ c : Coq, IsIsomorphism (diagonal_counit L c)) → False.
Proof.
  intro Hiso.
  apply Diagonal_Two_Discrete_not_Full.
  exact (fst (snd (@right_adjoint_fully_faithful_iff_counit_iso
                     Coq ([Two_Discrete, Coq]) (ColimitFunctor L)
                     (@Diagonal Coq Two_Discrete)
                     (Colimit_Diagonal_Adjunction L)) Hiso)).
Qed.

Theorem two_discrete_no_ffi :
  LeftAdjointFFInjective (@Diagonal Coq Two_Discrete) → False.
Proof.
  intro B.
  exact (Diagonal_Two_Discrete_not_Full (ffi_full B)).
Qed.

Theorem two_discrete_no_lali :
  LeftAdjointLeftInverse (@Diagonal Coq Two_Discrete) → False.
Proof.
  intro P.
  exact (two_discrete_no_ffi (lali_implies_ffi P)).
Qed.

Theorem two_discrete_no_constant_colimits :
  ConstantColimits Two_Discrete Coq → False.
Proof.
  intro P.
  exact (two_discrete_no_lali
           (colimit_is_lali_of_diagonal (TwoDX : Two_Discrete) P)).
Qed.

(* And the shape is inhabited, so what goes is connectedness and not
   the point: [TwoDX] above is a genuine object of it. *)

Theorem two_discrete_objects_distinct : (TwoDX : Two_Discrete) = TwoDY
  → False.
Proof. discriminate. Qed.
