Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Abelianization.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Abelianization as a universal arrow, and the adjunction twice over

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §III.1 Exercise 3 [maclane:III.1:ex3]: the factor-commutator group
    G/[G, G] is the value at G of a left adjoint to the inclusion of
    abelian groups in groups, and the projection p_G : G → G/[G, G] is
    the universal arrow from G to that inclusion.  Riehl, "Category
    Theory in Context", Dover 2016, §4.2 Exercise ii asks for the same
    adjunction built the OTHER way, from a unit, a counit, and the two
    triangle identities proved by hand.  Both are delivered here, and
    then related.
    nLab: https://ncatlab.org/nlab/show/abelianization

    WHAT IS CONSUMED RATHER THAN REBUILT.  Instance/Grp/Abelianization.v
    already carries the whole construction, and nothing of it is
    repeated below:

      - [AbelianizationOb] (:246) — G/[G, G] as a setoid quotient: the
        SAME carrier as G under the coarser relation [abel_eq] (:207),
        so commutativity of the quotient is the generating constructor
        [inc_comm] rather than a computation;
      - [Abelianization_Functor : Grp ⟶ Ab] (:356);
      - [Ab_to_Grp : Ab ⟶ Grp] (:343) with its object part
        [Ab_to_GrpOb] (:333) — the evident inclusion, which IS the
        forgetful functor of this exercise;
      - [abel_proj] (:391) and [abel_projection] (:401), the natural
        family of projections [Id Grp ⟹ Ab_to_Grp ◯
        Abelianization_Functor] whose components are the IDENTITY on
        elements.  That transformation IS the unit of the adjunction
        below; it is used verbatim, not re-derived;
      - [hom_to_abelian_kills] (:164) — a homomorphism into an abelian
        group kills every commutator element.  That donor file's header
        calls it "the descent germ", and this file is what spends it:
        [abel_kills] is the single place where it is used, and every
        mediating morphism below factors through that one lemma.

    THE ISSUE'S "Current state" PARAGRAPH IS STALE.  It asserts that
    the tree has no categories of groups or abelian groups.  It has
    both: [Grp] (Instance/Grp.v:466) and [Ab] (Instance/Ab.v:201), each
    with a forgetful functor to [Sets] ([Grp_Forget], Instance/Grp.v:493;
    [Ab_Forget], Instance/Ab.v:217).  The abelianization functor and the
    inclusion have existed since Instance/Grp/Abelianization.v landed,
    and that file's own header records the adjunction as "close at hand"
    and "not built here".  This file builds it.

    THE TWO ROUTES, AND EXACTLY HOW THEY RELATE.  This has to be stated
    carefully, because the two routes do not even produce adjunctions of
    the SAME TYPE.

    Route one is the universal-arrow plumbing of Theory/Universal/Arrow.v
    — the route Instance/Grp/Free.v and Instance/Mod/Free.v take.
    [abelianize_universal] states the universal mapping property,
    [universal_arrow_from_UMP] packages it as
    [abelianize_universal_arrow], and then
    [LeftAdjointFunctorFromUniversalArrows] and
    [AdjunctionFromUniversalArrows] produce a functor and an adjunction
    with no further proof.  But the functor they produce is the
    generic [abelianize_left], NOT [Abelianization_Functor]: the generic
    machinery defines the action on arrows by unique factorization
    through the [Qed]-opaque [ump_universal_arrows], where the donor
    file defines it as the underlying map of the homomorphism.  So
    [abelianize_adjunction] has type [abelianize_left ⊣ Ab_to_Grp].

    Route two is [Adjunction_from_Transform]
    (Adjunction/Natural/Transformation/Universal.v:42), fed the unit
    [abel_projection], the counit [abelianize_counit] built here, and
    both triangle identities proved by hand.  It lands exactly at
    [abelianize_adjunction_via_transform : Abelianization_Functor ⊣
    Ab_to_Grp].

    The relation between them is measured at three grades, strict
    first:

      - OBJECTS AGREE ON THE NOSE.  [abelianize_left_obj] is [eq_refl]:
        [abelianize_left G] and [Abelianization_Functor G] are the same
        term.  This is what makes the comparisons below even well
        typed — a morphism out of one is a morphism out of the other.
      - ARROWS AGREE ONLY UP TO [≈].  [abelianize_left_fmap] is proved
        from the uniqueness clause of the universal property;
        [probe_left_fmap_strict] pins the [eq_refl] REFUSAL, whose cause
        is that [ump_universal_arrows] is a [Qed] Corollary, so
        [unique_obj (ump_universal_arrows …)] reduces to nothing.
        [abelianize_left_iso] packages the two facts as an isomorphism
        in the functor category [[Grp, Ab]] whose components are
        identities.
      - THE FORWARD TRANSPOSES AGREE AT LEIBNIZ EQUALITY.
        [abelianize_routes_agree]'s first component is [eq_refl] at an
        ARBITRARY G, A and f: both routes send f to [fmap[Ab_to_Grp] f ∘
        abel_proj G], the same term.  On route one this works because
        [universal_arrow_from_UMP] stores the supplied morphism as the
        second projection of the comma object it builds, so [arrow]
        reduces to [abel_proj G] ([abelianize_arrow_is_proj], [eq_refl]).
        The BACKWARD transposes agree only up to [≈], for the same
        opacity reason, and that half is proved through the uniqueness
        clause.  The whole [SetoidMorphism] records and the whole
        adjunction records do not agree even for the forward leg
        ([probe_routes_to_record]), the residue being the rebuilt
        [proper_morphism] certificates.

    THE DIAGNOSIS IS DISCRIMINATING, NOT A BLANKET APPEAL TO OPACITY.
    Theory/Adjunction.v DERIVES [unit] and [counit] as the transposes of
    identities, so what they compute to has to be checked rather than
    assumed, and the two routes come apart exactly where predicted:

      - both routes' derived UNITS compute — [abelianize_unit_computes]
        and [abelianize_unit_computes_via_transform] are both [eq_refl],
        because the unit is a FORWARD transpose and the forward
        transposes are the same term;
      - route two's derived COUNIT computes
        ([abelianize_counit_computes_via_transform], [eq_refl]) while
        route one's does not ([probe_counit_route_one]).  Same derived
        constant, same statement shape, opposite outcomes: route two's
        backward transpose is [counit ∘ fmap[F] −] with both factors
        transparent, route one's is [unique_obj (ump_universal_arrows …)]
        and is opaque.

    WHAT THE COUNIT CONCRETELY IS.  Mac Lane §IV.2's slogan for a free
    construction — the counit sends a formal combination to the actual
    combination, exhibiting an object as a quotient of the free object
    on its own elements — DOES NOT TRANSFER to this row, and the file
    declines the analogy rather than stretching it.  Abelianization is
    not free on underlying data; it is a reflector onto a subcategory
    that is already sitting inside [Grp].  Concretely, at an abelian
    group A the relation [abel_eq (Ab_to_GrpOb A)] and A's own [≈]
    coincide — that biconditional is exactly the two respectfulness
    obligations of [abelianize_counit_iso] — so the counit component is
    the IDENTITY FUNCTION on elements
    ([abelianize_counit_computes], [eq_refl]) and is INVERTIBLE
    ([abelianize_counit_iso]) — its inverse is the same identity
    function read the other way.  In words: the counit exhibits an
    abelian group as its own abelianization.  That is the opposite
    behaviour from a free-construction counit, which is a genuine
    evaluation and in general far from invertible.  [Ab_to_Grp] is
    proved full and faithful here, so the shape is exactly that of a
    reflective subcategory — but NO [Reflective] instance is claimed:
    Construction/Reflective.v is stated over Construction/Subcategory.v's
    [Sub] inclusions and [Ab_to_Grp] is not one of those, its objects
    being [AbObject] records rather than [GrpObject]s satisfying a
    predicate.

    NON-VACUITY, PROVED BY MAPPING OUT.  No induction on the
    quotienting generation [InCommutator] can yield a negative, so every
    separation below goes through a homomorphism into a concrete group.
    The witness is S₃ (Instance/Grp/TwoFunctors.v:248), the in-tree
    nonabelian group.  [abelianize_S3_identifies] shows the projection
    merges the commutator of the two generators with the unit, while the
    donor's [commutator_S3_nontrivial] shows those two elements are
    apart in S₃: the abelianization of S₃ is a PROPER quotient.  It is
    also not the trivial group, and that is shown BY EXERCISING THE
    UNIVERSAL PROPERTY rather than by inspection: [AbTwo] is ℤ/2 as an
    [AbObject], [ab_two_sign] is the sign character read into it, and
    the mediator [abelianize_med ab_two_sign] produced by
    [abelianize_universal] separates the class of the reflection from
    the class of the unit ([abelianize_S3_separates]), computing to
    [grp_two_one] by [eq_refl].

    UNIVERSES, read off the CONSTRAINT BLOCKS rather than the binders,
    for every constant this file declares.  Of the 63 named constants,
    SIX carry [Set] in a constraint block, and all six are S₃ witnesses:
    [ab_two_sign], [abelianize_S3_med_s], [abelianize_S3_med_unit],
    [abelianize_S3_separates], [abelianize_S3_factors] and the control
    [probe_ctl_sign].  The cause is located: their types mention
    [TwoFunctors.S3@{Set}], S₃ being carried on a [bool] component and
    [bool : Set].  It is NOT [AbTwo]'s doing — [AbTwo@{u u0 u1 u2 u3 u4
    u5}] has an empty [Set]-free block of its own, and neither is it
    Instance/Grp.v's [Grp_trivial]/[Grp_Zero] pin (disclosed in
    Instance/Grp/Quotient/Colimit.v), neither of which is used anywhere
    in this file.  Two further S₃ statements,
    [abelianize_S3_identifies] and [abelianize_S3_proper], display
    [Set] inside a universe INSTANCE ([abel_eq@{u u Set}]) while
    acquiring no [Set] CONSTRAINT: an instance is not a constraint.

    THE GENERAL DEVELOPMENT IS [Set]-FREE.  [abel_kills],
    [abelianize_med], [abelianize_universal],
    [abelianize_universal_arrow], [abelianize_left],
    [abelianize_adjunction], [abelianize_counit],
    [abelianize_transform], [abelianize_adjunction_via_transform],
    [abelianize_routes_agree], [abelianize_counit_iso],
    [abelianize_left_iso], [Ab_to_Grp_Full] and [Ab_to_Grp_Faithful]
    all have [Set]-free constraint blocks and are polymorphic in
    [Grp]'s and [Ab]'s universes.  No lift of the S₃ witnesses is
    attempted, and the pin is not claimed unavoidable.

    AXIOMS.  90/90 constants are closed under the global context: the
    63 the [.glob] records as [def] or [prf] after discarding the eight
    [Fail]-named entries, which name no constant, plus 27 [Program]
    obligations, which the [.glob] does not record at all and which
    have to be queried by their fully qualified names.

    NO EXPLICIT UNIVERSE INSTANCE IS WRITTEN ON ANY FUNCTOR OR
    ADJUNCTION in this file.  The number of universe binders [Functor]
    and [Adjunction] take differs between Coq 8.19/8.20 and Rocq 9.1, so
    such an annotation is not portable.  No universe fact needed
    guarding here either: all seven negatives below are CONVERSION
    failures and none is a formability (universe) one, so the universe
    findings above are MEASURED but not guarded, and the file says so
    rather than calling them pinned.

    WHAT IS NOT DELIVERED.
      - No [Reflective] instance, for the structural reason above, and
        no identification of [Ab] with a full subcategory of [Grp] in
        Construction/Subcategory.v's sense.
      - No idempotency: [Abelianization_Functor ◯ Ab_to_Grp ≅ Id[Ab]]
        follows componentwise from [abelianize_counit_iso], but the
        natural isomorphism in [[Ab, Ab]] is not assembled, and no
        [IdempotentMonad] statement is made.
      - No comparison with Construction/Reflective/Idempotent.v, and no
        Eilenberg–Moore reading.
      - No uniqueness-up-to-unique-isomorphism corollary: it would be
        [universal_arrow_unique] instantiated here, and it is not
        instantiated.
      - Nothing about the abelianization of a FREE group, so no bridge
        to Instance/Grp/Free.v and no free-abelian-group functor.
      - The universal property is not restated as a representability
        statement, and no [Representable] instance is registered.
      - The Fail probes below live IN THIS FILE rather than in a
        Test/Probe module, because this change is confined to one file;
        they are not wired into any make target.  There are SEVEN
        negatives, all of ONE KIND (conversion — each stripped once and
        confirmed to report a genuine "cannot unify"), against 23
        positive controls and one instrument check.  Every constant the
        negatives name is rename-simulated 19/19.  The fourteen donors
        ([Abelianization_Functor], [Ab_to_GrpOb], [GrpTwo], [Ab_to_Grp],
        [Grp], [Ab], [cmon_map], [cmon_setoid], [carrier], [adj], [to],
        [from], [fmap], [counit]) were renamed throughout this file,
        which is what an upstream rename would do to it; the five local
        ones ([abelianize_left], [abelianize_adjunction],
        [abelianize_adjunction_via_transform], [abelianize_counit_hom],
        [AbTwo]) were renamed at their declaration sites only.  In
        every one of the nineteen cases a POSITIVE command breaks, so
        no negative can go vacuously green. *)

(** ** The descent lemma

    Everything below factors through this one step.  [Ab_to_GrpOb A] is
    abelian by construction, so [hom_to_abelian_kills] applies to any
    homomorphism into it; cancelling the inverse turns "kills
    commutators" into "respects the quotient relation". *)

Lemma ab_is_abelian (A : AbObject) (a b : carrier (Ab_to_GrpOb A)) :
  grp_mul (Ab_to_GrpOb A) a b ≈ grp_mul (Ab_to_GrpOb A) b a.
Proof. apply cmon_plus_comm. Qed.

Lemma abel_kills {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a b : carrier G) :
  abel_eq G a b → grp_map f a ≈ grp_map f b.
Proof.
  intro Hab.
  pose proof (hom_to_abelian_kills (ab_is_abelian A) f _ Hab) as E.
  rewrite (grp_map_mul f), (grp_map_inv f) in E.
  apply (grp_cancel_r _ (grp_inv (Ab_to_GrpOb A) (grp_map f b))).
  rewrite E.
  symmetry; apply grp_mul_inv_r.
Qed.

(** The mediating homomorphism: the SAME underlying map as [f], read
    out of the quotient.  Preservation of the unit and of the operation
    are [f]'s own laws unchanged; the only new obligation is
    respectfulness, which is [abel_kills]. *)

Program Definition abelianize_med {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) : AbelianizationOb G ~{Ab}~> A := {|
  cmon_map := {| morphism := fun a : carrier G => grp_map f a |}
|}.
Next Obligation. intros G A f a b Hab; exact (abel_kills f a b Hab). Qed.
Next Obligation. intros G A f; exact (grp_map_unit f). Qed.
Next Obligation. intros G A f a b; exact (grp_map_mul f a b). Qed.

Example abelianize_med_computes {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a : carrier G) :
  cmon_map (abelianize_med f) a = grp_map f a := eq_refl.

(** ** The universal arrow

    Mac Lane §III.1 Exercise 3 proper: [abel_proj G] is universal from
    G to [Ab_to_Grp].  Existence is [abelianize_med]; the factorization
    equation is [reflexivity], both sides being the same function on
    elements; uniqueness is that [abel_proj G] is the identity on
    elements, so the equation READS as the pointwise agreement being
    asked for. *)

Theorem abelianize_universal (G : Grp) :
  ∀ (A : Ab) (f : G ~{Grp}~> Ab_to_Grp A),
    ∃! g : AbelianizationOb G ~{Ab}~> A,
      f ≈ fmap[Ab_to_Grp] g ∘ abel_proj G.
Proof.
  intros A f.
  unshelve eexists.
  - exact (abelianize_med f).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

(** Kept transparent DELIBERATELY: [unique_obj] of it is the mediator on
    the nose, so the concrete evaluations at the end of this file
    compute.  The [Qed] alternative is what makes route one's derived
    counit opaque below, and that contrast is the point. *)
Example abelianize_universal_med (G : Grp) (A : Ab)
  (f : G ~{Grp}~> Ab_to_Grp A) :
  unique_obj (abelianize_universal G A f) = abelianize_med f := eq_refl.

(** Packaged as an initial object of the comma category [=(G) ↓
    Ab_to_Grp]. *)
Definition abelianize_universal_arrow (G : Grp)
  : UniversalArrow G Ab_to_Grp :=
  universal_arrow_from_UMP G Ab_to_Grp (AbelianizationOb G) (abel_proj G)
    (abelianize_universal G).

(** The same content in the direct encoding, where the universal object
    is named rather than projected out of a comma category. *)
Program Definition abelianize_AUniversalArrow (G : Grp)
  : AUniversalArrow G Ab_to_Grp (AbelianizationOb G) := {|
  universal_arrow := abel_proj G
|}.
Next Obligation.
  intros G A f.
  unshelve eexists.
  - exact (abelianize_med f).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    symmetry; exact (Hg a).
Qed.

(** [universal_arrow_from_UMP] stores the supplied morphism as the
    second projection of the comma object it builds, so both readings
    are on the nose. *)
Example abelianize_arrow_is_proj (G : Grp) :
  @arrow _ _ G Ab_to_Grp (abelianize_universal_arrow G) = abel_proj G
  := eq_refl.

Example abelianize_arrow_obj (G : Grp) :
  @arrow_obj _ _ G Ab_to_Grp (abelianize_universal_arrow G)
    = AbelianizationOb G := eq_refl.

Example abelianize_AUniversalArrow_arrow (G : Grp) :
  @universal_arrow _ _ G Ab_to_Grp _ (abelianize_AUniversalArrow G)
    = abel_proj G := eq_refl.

(** ** Route one: the adjunction from the universal-arrow plumbing

    The functor, the adjunction and both triangle identities come out
    of Theory/Universal/Arrow.v with no further proof.  Read the type
    of [abelianize_adjunction] carefully: the LEFT ADJOINT it produces
    is the generic [abelianize_left], not [Abelianization_Functor].
    The two agree on objects definitionally and on arrows up to [≈];
    see [abelianize_left_iso] below. *)

Definition abelianize_left : Grp ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_to_Grp abelianize_universal_arrow.

Definition abelianize_adjunction : abelianize_left ⊣ Ab_to_Grp :=
  AdjunctionFromUniversalArrows Ab_to_Grp abelianize_universal_arrow.

Example abelianize_left_obj (G : Grp) :
  abelianize_left G = Abelianization_Functor G := eq_refl.

(** The arrow actions agree only up to [≈], and the proof is the
    uniqueness clause of the universal property: the generic functor's
    [fmap] is BY DEFINITION the unique factorization, and the donor's
    [fmap] satisfies the same equation. *)
Lemma abelianize_left_fmap {G H : Grp} (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f ≈ fmap[Abelianization_Functor] f.
Proof.
  apply (uniqueness (ump_universal_arrows (abelianize_universal_arrow G) _)).
  intro a; simpl; apply abel_eq_refl.
Qed.

(** The two facts assembled: an isomorphism in the functor category
    whose components are identities. *)
Program Definition abelianize_left_iso :
  @Isomorphism ([Grp, Ab]) abelianize_left Abelianization_Functor := {|
  to   := {| transform := fun G => @id Ab (Abelianization_Functor G) |};
  from := {| transform := fun G => @id Ab (Abelianization_Functor G) |}
|}.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G a; simpl.
  first [ apply abel_eq_refl
        | exact (@fmap_id _ _ abelianize_left G a)
        | exact (abel_eq_sym G _ _ (@fmap_id _ _ abelianize_left G a)) ].
Qed.
Next Obligation.
  intros G a; simpl.
  first [ apply abel_eq_refl
        | exact (@fmap_id _ _ abelianize_left G a)
        | exact (abel_eq_sym G _ _ (@fmap_id _ _ abelianize_left G a)) ].
Qed.

(** ** Route two: the counit, and the adjunction from unit and counit

    Riehl §4.2 Exercise ii.  The counit component at an abelian group A
    is the identity function on elements, read out of the coarse setoid
    [abel_eq (Ab_to_GrpOb A)] into A's own [≈].  Its one obligation is
    [abel_kills] at the identity homomorphism of [Ab_to_GrpOb A]: an
    abelian group kills its own commutators. *)

Program Definition abelianize_counit_hom (A : AbObject) :
  AbelianizationOb (Ab_to_GrpOb A) ~{Ab}~> A := {|
  cmon_map := {| morphism := fun a : carrier (cmon_setoid A) => a |}
|}.
Next Obligation.
  intros A a b Hab.
  exact (abel_kills (@id Grp (Ab_to_GrpOb A)) a b Hab).
Qed.
Next Obligation. intros A; simpl; reflexivity. Qed.
Next Obligation. intros A a b; simpl; reflexivity. Qed.

(** The counit, concretely: the identity on elements. *)
Example abelianize_counit_computes (A : AbObject)
  (a : carrier (cmon_setoid A)) :
  cmon_map (abelianize_counit_hom A) a = a := eq_refl.

(** And it is INVERTIBLE — its inverse is the same identity map read
    the other way, which is [abel_proj (Ab_to_GrpOb A)] transcribed
    into [Ab].  This is the concrete content of the counit for this
    row: an abelian group is its own abelianization.  Contrast a free
    construction, where the counit is a genuine evaluation and is in
    general nowhere near invertible. *)

Program Definition abelianize_counit_inv (A : AbObject) :
  A ~{Ab}~> AbelianizationOb (Ab_to_GrpOb A) := {|
  cmon_map := {| morphism := fun a : carrier (cmon_setoid A) => a |}
|}.
Next Obligation.
  intros A a b Hab; exact (abel_eq_of_eq (Ab_to_GrpOb A) a b Hab).
Qed.
Next Obligation. intros A; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros A a b; simpl; apply abel_eq_refl. Qed.

Program Definition abelianize_counit_iso (A : AbObject) :
  AbelianizationOb (Ab_to_GrpOb A) ≅[Ab] A := {|
  to   := abelianize_counit_hom A;
  from := abelianize_counit_inv A
|}.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A a; simpl; apply abel_eq_refl. Qed.

(** The counit as a natural transformation.  Both naturality squares
    have the identity on both legs, so both are [reflexivity]. *)
Program Definition abelianize_counit :
  Abelianization_Functor ◯ Ab_to_Grp ⟹ @Id Ab := {|
  transform := abelianize_counit_hom
|}.
Next Obligation. intros A B f a; simpl; reflexivity. Qed.
Next Obligation. intros A B f a; simpl; reflexivity. Qed.

(** The unit/counit package, with BOTH TRIANGLE IDENTITIES PROVED HERE.

    The first, [ε(FX) ∘ F(ηX) ≈ id], lives in [Ab] at
    [AbelianizationOb X]: both legs are the identity function on
    [carrier X] and the ambient relation is [abel_eq X], so the
    obligation is [abel_eq_refl].  The second, [U(εX) ∘ η(UX) ≈ id],
    lives in [Grp] at [Ab_to_GrpOb X]: both legs are again the identity
    function, but the ambient relation is X's own [≈], so the
    obligation is [reflexivity].  The two triangles are therefore
    discharged by DIFFERENT tactics, which is a reminder that they are
    equations in different categories and not one statement twice. *)
Program Definition abelianize_transform :
  Abelianization_Functor ∹ Ab_to_Grp := {|
  Transformation.unit   := abel_projection;
  Transformation.counit := abelianize_counit
|}.
Next Obligation. intros X a; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros X a; simpl; reflexivity. Qed.

Definition abelianize_adjunction_via_transform
  : Abelianization_Functor ⊣ Ab_to_Grp :=
  Adjunction_from_Transform abelianize_transform.

Example abelianize_transform_unit :
  unit[abelianize_transform] = abel_projection := eq_refl.

Example abelianize_transform_counit :
  counit[abelianize_transform] = abelianize_counit := eq_refl.

(** ** The two routes agree

    The FORWARD transposes are the same term at arbitrary arguments;
    the BACKWARD ones agree only up to [≈], the residue being the
    opacity of [ump_universal_arrows]. *)

Example abelianize_routes_agree_to (G : Grp) (A : Ab)
  (f : Abelianization_Functor G ~{Ab}~> A) :
  to (@adj _ _ _ _ abelianize_adjunction G A) f
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

Theorem abelianize_routes_agree (G : Grp) (A : Ab) :
  (∀ f : Abelianization_Functor G ~{Ab}~> A,
      to (@adj _ _ _ _ abelianize_adjunction G A) f
        = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f)
  * (∀ f : G ~{Grp}~> Ab_to_Grp A,
      from (@adj _ _ _ _ abelianize_adjunction G A) f
        ≈ from (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f).
Proof.
  split.
  - intro f; exact eq_refl.
  - intro f.
    apply (uniqueness (ump_universal_arrows (abelianize_universal_arrow G) f)).
    intro a; simpl; reflexivity.
Qed.

(** ** The derived unit and counit

    [unit] and [counit] are DERIVED in Theory/Adjunction.v as the
    transposes of the identities, so what they compute to has to be
    checked.  Both routes' units compute, and to the projection;
    route two's counit computes and route one's does not. *)

Example abelianize_unit_computes (G : Grp) (a : carrier G) :
  grp_map (@Category.Theory.Adjunction.unit _ _ _ _
             abelianize_adjunction G) a = a := eq_refl.

Example abelianize_unit_computes_via_transform (G : Grp) (a : carrier G) :
  grp_map (@Category.Theory.Adjunction.unit _ _ _ _
             abelianize_adjunction_via_transform G) a = a := eq_refl.

Example abelianize_counit_computes_via_transform (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (@Category.Theory.Adjunction.counit _ _ _ _
             abelianize_adjunction_via_transform A) a = a := eq_refl.

(** ** [Ab_to_Grp] is full and faithful

    Faithfulness is definitional — an [AbHom] IS a [CMonHom] and both
    hom-setoids compare underlying maps pointwise.  Fullness holds
    because a group homomorphism between the underlying groups of two
    abelian groups already preserves everything an [AbHom] must: the
    unit law becomes preservation of zero, the multiplication law
    preservation of the sum, and preservation of negation is
    Instance/Ab.v's theorem [ab_map_neg] rather than a further
    obligation.  Together with the adjunction and the invertible counit
    this is the shape of a reflective subcategory; see the header for
    why no [Reflective] instance is claimed. *)

Program Definition Ab_to_Grp_Faithful : Faithful Ab_to_Grp := {|
  fmap_inj := fun A B f g H => H
|}.

Program Definition Ab_to_Grp_Full : Full Ab_to_Grp := {|
  prefmap := fun A B (h : Ab_to_GrpOb A ~{Grp}~> Ab_to_GrpOb B) =>
    {| cmon_map      := grp_map h
     ; cmon_map_zero := grp_map_unit h
     ; cmon_map_plus := grp_map_mul h |}
|}.
Next Obligation. intros A B h a; simpl; reflexivity. Qed.

(** ** Non-vacuity over S₃

    Every separation below is obtained by mapping OUT of the quotient:
    no induction on the generation [InCommutator] could produce a
    negative.  The target is ℤ/2 read as an [AbObject]. *)

Program Definition AbTwo : AbObject := {|
  ab_cmon := {| cmon_setoid := grp_setoid GrpTwo
              ; cmon_zero   := grp_unit GrpTwo
              ; cmon_plus   := grp_mul GrpTwo |}
 ; ab_neg := grp_inv GrpTwo
|}.
Solve All Obligations with
  (first [ exact (grp_mul_respects GrpTwo)
         | exact (grp_mul_assoc GrpTwo)
         | exact GrpTwo_abelian
         | exact (grp_mul_unit_l GrpTwo)
         | exact (grp_inv_Proper GrpTwo)
         | exact (grp_mul_inv_l GrpTwo) ]).

(** The sign character of S₃ (Instance/Grp/Center.v:251), read into
    [Ab_to_GrpOb AbTwo].  The three fields are [s3_sign]'s own: [AbTwo]
    was built so that its setoid, zero and sum ARE [GrpTwo]'s, which is
    what makes this a re-wrapping rather than a second construction. *)
Definition ab_two_sign : S3 ~{Grp}~> Ab_to_GrpOb AbTwo :=
  Build_GrpHom S3 (Ab_to_GrpOb AbTwo)
    (grp_map s3_sign) (grp_map_unit s3_sign) (grp_map_mul s3_sign).

(** The projection MERGES: the commutator of the two generators becomes
    the unit in the abelianization. *)
Lemma abelianize_S3_identifies : abel_eq S3 (gcomm S3 S3_r S3_s) s3_unit.
Proof.
  apply (inc_resp (a := gcomm S3 S3_r S3_s)).
  - vm_compute; reflexivity.
  - apply inc_comm.
Qed.

(** …and what it merges was apart in S₃, so the abelianization of S₃ is
    a PROPER quotient.  The second half is the donor's
    [commutator_S3_nontrivial]; nothing is reproved. *)
Theorem abelianize_S3_proper :
  abel_eq S3 (gcomm S3 S3_r S3_s) s3_unit *
  (gcomm S3 S3_r S3_s ≈ s3_unit → False).
Proof.
  split.
  - exact abelianize_S3_identifies.
  - exact (snd commutator_S3_nontrivial).
Qed.

(** The quotient is not collapsed either, and this is shown BY
    EXERCISING THE UNIVERSAL PROPERTY: the mediator [abelianize_universal]
    produces out of the sign character separates the class of the
    reflection from the class of the unit.  Both values COMPUTE, the
    universal property having been left transparent. *)

Example abelianize_S3_med_s :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) S3_s
    = grp_two_one := eq_refl.

Example abelianize_S3_med_unit :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) s3_unit
    = grp_two_zero := eq_refl.

Theorem abelianize_S3_separates :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) S3_s
    ≈ cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign))
        s3_unit → False.
Proof. intro H; vm_compute in H; exact H. Qed.

(** The mediator is genuinely a homomorphism OUT of the quotient: it is
    the unique factorization of the sign character through the
    projection, and the factorization equation is the universal
    property's own. *)
Example abelianize_S3_factors (a : carrier S3) :
  grp_map ab_two_sign a
    = grp_map (fmap[Ab_to_Grp]
                 (unique_obj (abelianize_universal S3 AbTwo ab_two_sign))
                 ∘ abel_proj S3) a := eq_refl.

(** ** Boundary probes

    Each [Fail] below pins a strict identification that is REFUSED, and
    is paired with a positive control naming the same constants, so a
    rename or a definitional change breaks this file loudly instead of
    turning a negative vacuously green.  [abelianize_probe_instrument] checks
    the instrument itself.  These live here rather than in a Test/Probe
    module because this change is confined to one file; they are not
    wired into any make target. *)

Fail Example abelianize_probe_instrument : true = false := eq_refl.

(* Positive controls. *)
Example probe_ctl_left : Grp ⟶ Ab := abelianize_left.
Example probe_ctl_functor : Grp ⟶ Ab := Abelianization_Functor.
Example probe_ctl_adj : abelianize_left ⊣ Ab_to_Grp := abelianize_adjunction.
Example probe_ctl_adj_transform : Abelianization_Functor ⊣ Ab_to_Grp :=
  abelianize_adjunction_via_transform.
Example probe_ctl_fmap (G H : Grp) (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f ≈ fmap[Abelianization_Functor] f :=
  abelianize_left_fmap f.
Example probe_ctl_counit_hom (A : Ab) :
  AbelianizationOb (Ab_to_GrpOb A) ~{Ab}~> A := abelianize_counit_hom A.
Example probe_ctl_sign : S3 ~{Grp}~> Ab_to_GrpOb AbTwo := ab_two_sign.
Example probe_ctl_grptwo : GrpObject := GrpTwo.
Example probe_ctl_abtwo : AbObject := AbTwo.
Example probe_ctl_med (G : Grp) (A : Ab) (f : G ~{Grp}~> Ab_to_Grp A) :
  AbelianizationOb G ~{Ab}~> A := abelianize_med f.
Example probe_ctl_arrow (G : Grp) :
  @arrow _ _ G Ab_to_Grp (abelianize_universal_arrow G) = abel_proj G
  := eq_refl.
Example probe_ctl_aua (G : Grp) :
  AUniversalArrow G Ab_to_Grp (AbelianizationOb G) :=
  abelianize_AUniversalArrow G.
Example probe_ctl_counit_iso (A : Ab) :
  AbelianizationOb (Ab_to_GrpOb A) ≅[Ab] A := abelianize_counit_iso A.
Example probe_ctl_transform : Abelianization_Functor ∹ Ab_to_Grp :=
  abelianize_transform.
Example probe_ctl_left_iso :
  @Isomorphism ([Grp, Ab]) abelianize_left Abelianization_Functor :=
  abelianize_left_iso.
Example probe_ctl_kills {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a b : carrier G) :
  abel_eq G a b → grp_map f a ≈ grp_map f b := abel_kills f a b.
Example probe_ctl_counit_nat :
  Abelianization_Functor ◯ Ab_to_Grp ⟹ @Id Ab := abelianize_counit.
Example probe_ctl_counit_inv (A : Ab) :
  A ~{Ab}~> AbelianizationOb (Ab_to_GrpOb A) := abelianize_counit_inv A.
Example probe_ctl_full : Full Ab_to_Grp := Ab_to_Grp_Full.
Example probe_ctl_faithful : Faithful Ab_to_Grp := Ab_to_Grp_Faithful.

Example probe_control_obj (G : Grp) :
  abelianize_left G = Abelianization_Functor G := eq_refl.

Example probe_control_to (G : Grp) (A : Ab)
  (f : Abelianization_Functor G ~{Ab}~> A) :
  to (@adj _ _ _ _ abelianize_adjunction G A) f
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

Example probe_control_counit (A : Ab) (a : carrier (cmon_setoid A)) :
  cmon_map (abelianize_counit_hom A) a = a := eq_refl.

(* NEGATIVE 1 (conversion).  The two left adjoints are not the same
   functor: the arrow actions differ. *)
Fail Example probe_left_functors :
  abelianize_left = Abelianization_Functor := eq_refl.

(* NEGATIVE 2 (conversion).  Located precisely: the arrow actions.
   [ump_universal_arrows] is a [Qed] Corollary, so
   [unique_obj (ump_universal_arrows …)] reduces to nothing. *)
Fail Example probe_left_fmap_strict (G H : Grp) (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f = fmap[Abelianization_Functor] f := eq_refl.

(* NEGATIVE 3 (conversion).  The forward transposes agree as FUNCTIONS
   ([probe_control_to]) but not as whole [SetoidMorphism] records: the
   [proper_morphism] certificates are rebuilt. *)
Fail Example probe_routes_to_record (G : Grp) (A : Ab) :
  to (@adj _ _ _ _ abelianize_adjunction G A)
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) := eq_refl.

(* NEGATIVE 4 (conversion).  The backward transposes: route one's is
   the opaque unique factorization. *)
Fail Example probe_routes_from (G : Grp) (A : Ab)
  (f : G ~{Grp}~> Ab_to_Grp A) :
  from (@adj _ _ _ _ abelianize_adjunction G A) f
    = from (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

(* NEGATIVE 5 (conversion).  The DISCRIMINATING one: route one's
   derived counit does not compute, while route two's does
   ([abelianize_counit_computes_via_transform]) and the named component
   does ([probe_control_counit]).  Same derived constant, same
   statement shape. *)
Fail Example probe_counit_route_one (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (@Category.Theory.Adjunction.counit _ _ _ _
              abelianize_adjunction A) a = a := eq_refl.

(* NEGATIVE 6 (conversion).  Route two's derived counit computes on
   elements but is not the named component as a whole record: it is
   [abelianize_counit_hom A ∘ fmap[Abelianization_Functor] id]. *)
Fail Example probe_derived_counit_is_named (A : Ab) :
  @Category.Theory.Adjunction.counit _ _ _ _
    abelianize_adjunction_via_transform A = abelianize_counit_hom A
  := eq_refl.

(* NEGATIVE 7 (conversion).  [AbTwo] was built from [GrpTwo]'s own
   setoid, unit, multiplication and inverse, so the two records agree
   on every DATA field; they still do not convert, the law fields of
   [Ab_to_GrpOb] being rebuilt [Program] obligations. *)
Fail Example probe_abtwo_is_grptwo : Ab_to_GrpOb AbTwo = GrpTwo := eq_refl.
