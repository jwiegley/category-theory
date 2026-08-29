Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(** * Adjoining a basepoint: the free pointed set, its universal arrow,
      and the free-forgetful adjunction

    nLab:      https://ncatlab.org/nlab/show/pointed+set
    nLab:      https://ncatlab.org/nlab/show/free+functor
    nLab:      https://ncatlab.org/nlab/show/universal+morphism
    Wikipedia: https://en.wikipedia.org/wiki/Forgetful_functor

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, §III.1, Exercise 3, printed p. 59 --
          maclane:III.1:ex3
    Book: Mac Lane, ibid., §III.1, Definition 1 (universal arrow),
          printed p. 55 -- maclane:III.1:def1
    Book: Mac Lane, ibid., §IV.1, Theorem 2 (five equivalent
          determinations of an adjunction), printed p. 83 --
          maclane:IV.1:thm2.  The local-to-global route taken below is
          that theorem's universal-arrow clause.
    Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,
          Example 4.1.10, printed p. 135, CLAUSE (i) -- riehl:4.1:
          example10 is a fourteen-clause example listing fourteen
          forgetful functors with left adjoints, and this file delivers
          the first of them and none of the other thirteen.  Riehl names
          the free pointed set X_+ = X + {X}, taking the set X itself as
          the adjoined element; [option] takes [None] instead.  The two
          differ only in what the new point is called, and no comparison
          between them is stated (there is no set-theoretic X + {X} in
          this library to compare with).

    WHAT THIS FILE DELIVERS.  Mac Lane's §III.1 Exercise 3 asks for a
    universal arrow, from any given object, to each of FOUR forgetful
    functors: Ab ⟶ Grp, Rng ⟶ Ab, Top ⟶ Set, and Set_* ⟶ Set.  This
    file is the fourth row, the pointed one.  For a setoid X the free
    pointed set is X with one new element adjoined,

        FreePointedObject X  =  X ⊔ {∗},

    realised as [option (carrier X)] under [option_setoid]
    (Lib/Datatypes.v:211), pointed at [None]; [free_pointed_insert] is
    the insertion [Some]; and the universal property
    ([free_pointed_universal]) says every setoid map h : X ~> U Y into
    the underlying setoid of a pointed set Y extends along the insertion
    to one and only one basepoint-preserving map, namely the two-case
    match sending [Some a] to [h a] and [None] to the basepoint of Y.
    That is packaged as [free_pointed_universal_arrow] in the comma
    encoding and [free_pointed_AUniversalArrow] in the direct one, and
    assembled into [FreePointed : Sets ⟶ PointedSets] with
    [free_pointed_adjunction : FreePointed ⊣ Pointed_Forget] through the
    generic machinery of Theory/Universal/Arrow.v -- the same route
    Instance/Grp/Free.v, Instance/Mod/Free.v, Instance/Ab/Free.v and
    Instance/Mon/Free.v take.

    THE FORGETFUL FUNCTOR DID NOT EXIST, AND IS BUILT HERE.  That was
    re-verified rather than taken on trust, and the measurement is
    sharper than a bare absence claim.  The word "Forget" occurs ZERO
    times in all four pre-existing pointed-set files
    (Instance/Sets/Pointed.v and its satellites Coslice.v, Finite.v,
    Part.v).  Tree-wide, before this file there was exactly ONE functor
    whose SOURCE is [PointedSets] -- [Pointed_to_Coslice]
    (Instance/Sets/Pointed/Coslice.v:78) -- and its codomain is
    [Coslice Sets SetsOne], not [Sets]; the two functors INTO
    [PointedSets] were [Coslice_to_Pointed] (ibid.:94) and
    [Part_to_Pointed] (Instance/Sets/Pointed/Part.v:97).

    But the honest statement is weaker than "unreachable", and the
    difference is worth stating because a reviewer will find it:
    [Coslice_proj : Coslice C c ⟶ C] DOES exist
    (Instance/Cat/Pullback.v:847), so the composite
    [Coslice_proj ◯ Pointed_to_Coslice] was ASSEMBLABLE in tree.  It was
    never assembled and never named, and it is not the route taken here,
    for a dependency reason: Instance/Cat/Pullback.v is a large file
    about pullbacks in [Cat], and putting it behind every consumer of
    the pointed-set adjunction would be a poor trade for a three-line
    definition.  (The composite needs no extra hypothesis: despite
    sitting in a section that also binds [ObjUIP C], [Coslice_proj]
    discharges as [Coslice_proj {C} c], with no UIP argument -- checked,
    since the opposite would have been a substantive obstruction rather
    than a matter of weight.)

    The comparison of the two functors is NOT stated below, because
    stating it is exactly what would incur the dependency; it was
    measured out of tree instead, and what was found is recorded here as
    a MEASUREMENT and not as a proof.  Writing
    [ViaCoslice := Coslice_proj SetsOne ◯ Pointed_to_Coslice], the
    object action and the arrow action each agree with
    [Pointed_Forget]'s by [eq_refl], while the whole functor records do
    not; probing the three law fields SEPARATELY, all three are
    rejected, which is consistent with them being independently built
    opaque proof constants on the two sides ([Pointed_Forget]'s three
    [Program] obligations against [Compose]'s).  So the two agree at
    every level a consumer computes with and differ only in their
    proofs.  No [Fail] in this file names [ViaCoslice] or
    [Coslice_proj], so all of that is measured and not GUARDED.

    WHY THERE IS NO QUOTIENT, AND WHAT THAT BUYS.  The three algebraic
    rows of this same exercise all pay for a congruence.
    Instance/Ab/Free.v presents the free abelian group as an inductive
    [FATerm] of formal expressions modulo an inductive congruence
    [fa_eq] closing under the four abelian-group laws;
    Instance/Rng/Free.v does the same with [FRTerm]/[fr_eq]; and the
    abelianization row rides Instance/Grp/Abelianization.v, whose
    quotient coarsens the group's own [≈] by membership in the
    inductively generated commutator subgroup.  Adjoining
    a basepoint imposes NO equations at all -- it adds one element and
    stops -- so no congruence, no inductive relation and no
    well-definedness argument appears below.  Three consequences are
    visible in the proofs rather than merely asserted.

      (1) The carrier is a datatype the library already has:
          [option (carrier X)] under [option_setoid], which
          Lib/Datatypes.v:206-211 describes as the coproduct setoid
          1 + A.  Nothing is declared here except the pairing of that
          setoid with its basepoint.
      (2) A pointed map carries exactly ONE law, [preserves_pt], and for
          the extension that law is [reflexivity]: the mediator sends
          [None] to [pt Y] by definition.  Where the algebraic rows
          discharge one obligation per operation and per axiom, this row
          discharges one, definitionally.
      (3) Uniqueness is a two-case destruct with no induction anywhere:
          the [Some] case is the hypothesis and the [None] case is the
          competitor's own [preserves_pt].  The file contains no
          [induction] and no [Fixpoint].

    So this row is the cheapest of the four, which is what one should
    expect: "free" here adjoins a single element rather than closing
    under operations.

    THE SETOID DISCIPLINE COSTS NOTHING HERE, AND THAT IS THE
    INTERESTING COMPARISON.  Instance/Mod/Free.v's header locates, for
    the free MODULE, an obstruction that has no analogue in this row:
    the classical carrier (finitely supported functions) cannot even
    write down its basis vector without a decision procedure for the
    generating setoid's [≈], so the classical construction yields no
    adjunction at all over [Sets].  Adjoining a basepoint needs no
    decider: [option_setoid] lifts X's own [≈] and adds [None ≈ None],
    and [Some] respects [≈] on the nose.  Nothing below is conditional
    on decidability, finiteness, or choice -- the library's [∃] is
    [sigT], so the mediator produced by [ump_universal_arrows] is data.

    STRENGTHS, MEASURED STRICT-FIRST.  Every identification below was
    attempted at [eq_refl] before being stated at [≈].

      - [eq_refl]: the forgetful functor's object action
        ([free_pointed_forget_obj]); the free object's carrier and
        basepoint ([free_pointed_carrier], [free_pointed_basepoint]);
        the insertion ([free_pointed_insert_is_Some]); BOTH branches of
        the mediator ([free_pointed_extend_some_strict],
        [free_pointed_extend_none_strict]); the universal arrow
        ([free_pointed_arrow_is_insert]); the free functor's object
        action ([FreePointed_obj]); the UNIT
        ([free_pointed_unit_is_insert]); the forward transpose ⌊−⌋,
        which is RESTRICTION along the insertion
        ([free_pointed_transpose_is_adj]); the free functor's arrow
        action read as the inverse transpose
        ([free_pointed_fmap_is_from_adj]); and the two-point probe
        object of Instance/Sets/Pointed.v identified as the free pointed
        set on the one-point setoid ([PointedTwo_is_free_on_one]).

      - [≈] only: the INVERSE transpose ⌈−⌉ ([free_pointed_from_adj]),
        the COUNIT ([free_pointed_counit_evaluates]), and the free
        functor's arrow action evaluated at a generator
        ([free_pointed_fmap_some]).

    THE CAUSE OF THOSE THREE REJECTIONS IS DIAGNOSED, AND THE DIAGNOSIS
    DISCRIMINATES.  All three route through
    [unique_obj (ump_universal_arrows …)], and [ump_universal_arrows]
    (Theory/Universal/Arrow.v:139) is [Qed]-opaque, so nothing reduces
    through it.  Two controls show that this is the cause and not a
    generic property of the adjunction record.  First, the OTHER
    transpose of the SAME [Isomorphism] does reduce
    ([free_pointed_transpose_is_adj], [eq_refl]) -- so the obstruction
    is not that transposes in general fail to compute, nor a rebuilt
    [proper_morphism] certificate on the hom-setoid.  Second, and
    sharper, [free_pointed_fmap_is_from_adj] identifies
    [fmap[FreePointed] u] with ⌈insert ∘ u⌉ AT [eq_refl] -- both sides
    being literally the same opaque term -- while
    [free_pointed_fmap_some] then needs [≈].  So the block is located
    exactly at unfolding the opaque mediator and nowhere else.  Each
    rejection is GUARDED as well as measured: the three refutation
    [Fail] commands at the end of this file name [free_pointed_extend],
    [free_pointed_counit] and [FreePointed] respectively (a fourth
    [Fail] sits beside them, the scope-free instrument check, which
    refutes nothing about this development).  Each was stripped once and
    confirmed to report a genuine "cannot unify" rather than a scope,
    notation or reference error.  They cannot go vacuously green under a
    rename: every identifier occurring in a [Fail] block, other than the
    four probe names themselves, also occurs in at least one command of
    this file that must SUCCEED, so renaming any of them breaks a
    positive control here.

    UNIVERSES.  Read from the constraint blocks and not from the
    binders alone.  The two constructions whose binders are
    [SetoidObject] and [PointedSetoid] directly, rather than
    [obj[Sets]], keep every carrier universe apart from its relation
    universe: [FreePointedObject@{u u0} : SetoidObject@{u u0} →
    PointedSetoid@{u u0}], whose constraint block contains NO
    identification at all (only the bounds [u <= eq_ind.u0] and
    [u0 <= False_rect.u0] inherited from [option_setoid]'s own
    eliminations); and [free_pointed_extend@{u u0 u1 u2 u3 u4}], whose
    X sits at [SetoidObject@{u u0}] and whose Y sits at
    [PointedSetoid@{u1 u2}], four separate levels.

    The constants whose statements quantify over [X : Sets] -- that is,
    over [obj[Sets]] -- sit instead at [SetoidObject@{u0 u0}], carrier
    and relation identified; [free_pointed_insert@{u u0}] is the first
    of them.  That is NOT this file's doing and costs a consumer
    nothing: [Sets] is declared [Sets@{o so} : Category@{so o o}], so
    [obj[Sets]] IS [SetoidObject@{o o}] and the identification is what
    it means to be an object of [Sets] at all.  Likewise
    [Pointed_Forget@{u u0} : PointedSets@{u u0} ⟶ Sets@{u0 u}] carries
    [u0 < u], again [Sets]' own declaration, and no identification is
    introduced here.

    NO constant in this file carries [Set] in a universe instance or in
    a constraint -- all 66 were checked, the concrete witnesses
    included, which is why those are built over [poly_unit] and [option]
    rather than over [bool]; that was a deliberate choice and it was
    verified rather than assumed ([fpt_one@{u}] and [fpt_two@{u}] are
    [SetoidObject@{u u}]).

    ASSUMPTIONS.  All 66 constants of this module report "Closed under
    the global context".  The count is [Print Module]'s, which is 60
    source declarations plus the six [Program] obligations; note that
    the [.glob] OVERCOUNTS here, since a [Fail Definition foo] registers
    [foo] in the glob without adding a constant, and this file has four
    such.

    WHAT IS NOT DELIVERED.

      - No monad.  [Pointed_Forget ◯ FreePointed] has object action
        [option] on the nose ([free_pointed_maybe_carrier]), so this
        adjunction induces the maybe monad on [Sets] -- but no
        [@Monad Sets] instance, no Kleisli category and no
        Eilenberg-Moore comparison is built, and no statement below
        mentions [Monad].  Instance/Sets/Pointed.v's header already
        observes that pointed sets are the algebras of the maybe monad
        and that Instance/Sets/Par.v's [Part] is its Kleisli category;
        neither claim is formalized here or there.
        Theory/Coq/Maybe.v's [Maybe] monad is over the applied
        [Theory/Coq/] typeclass hierarchy on bare types, a different
        class from [Theory/Monad.v]'s, and is unrelated.
      - No smash product and no internal hom.  Instance/Sets/Pointed.v's
        relation to the smash-hom adjunction is a DIFFERENT statement
        about a DIFFERENT adjunction and nothing here addresses it.
      - No comparison with Instance/Sets/Pointed/Coslice.v's coslice
        presentation: the free pointed set is not exhibited as a
        coproduct with the terminal object, and no coslice-level
        universal arrow is stated.
      - No comparison with Instance/Sets/Pointed/Part.v: the free
        functor is not related to that file's [Part_to_Pointed], and
        nothing is said about partial maps.
      - Nothing about the other three rows of Exercise 3.  The Rng ⟶ Ab
        row's content is in tree as [FreeRngAb ⊣ Rng_Forget_Ab]
        (Instance/Rng/Free.v), filed there under Mac Lane §IV.8
        Exercise 2 rather than §III.1 Exercise 3; the Ab ⟶ Grp row is
        Instance/Grp/Abelianize.v; and for Top ⟶ Set,
        Instance/Top/Forgetful.v supplies [Top_Discrete] with
        [discrete_adj] as cross-universe hom-setoid isomorphisms, its
        header recording that the packaged [Adjunction] record is
        unformable across that universe gap -- and it contains no
        [UniversalArrow] at all (measured).  No claim is made here about
        any of the three.
      - No essential uniqueness statement specialised to this row.  The
        generic [universal_arrow_unique] (Theory/Universal/Arrow.v)
        applies verbatim and is not instantiated.
      - The insertion is proved injective and its image proved to miss
        the basepoint, but no [Monic] or [Epic] statement is made about
        it in [Sets] or in [PointedSets], and nothing is said about
        [Pointed_Forget] beyond faithfulness. *)

#[local] Obligation Tactic := idtac.

(** ** The forgetful functor Set_* ⟶ Set

    The underlying setoid of a pointed setoid, and the underlying setoid
    map of a pointed map.  Both are projections, so all three functor
    laws are [reflexivity] and faithfulness is the identity implication:
    equivalence in [PointedSets] IS pointwise equivalence of the
    underlying maps (Instance/Sets/Pointed.v:160). *)

Program Definition Pointed_Forget : PointedSets ⟶ Sets := {|
  fobj := fun X => pointed_setoid X;
  fmap := fun _ _ f => pointed_map f
|}.
Next Obligation. intros X Y f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros X a; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z f g a; simpl; reflexivity. Qed.

#[export] Program Instance Pointed_Forget_Faithful : Faithful Pointed_Forget.
Next Obligation. intros X Y f g Hfg a; exact (Hfg a). Qed.

(** ** The free pointed set X ⊔ {∗}

    The carrier is [option (carrier X)] and the setoid is
    [option_setoid] (Lib/Datatypes.v:211), which relates [Some a] to
    [Some b] exactly when a ≈ b, relates [None] to itself, and relates
    nothing across the two constructors.  The basepoint is the adjoined
    element [None].  No equation is imposed, so nothing is quotiented. *)

Definition FreePointedObject (X : SetoidObject) : PointedSetoid := {|
  pointed_setoid := {| carrier := option (carrier X) |};
  pt := Datatypes.None
|}.

(* The insertion of generators.  Its respectfulness certificate is
   [Some_respects] (Lib/Datatypes.v:231), resolved during elaboration;
   the universe measurement in the header was taken after that
   resolution, so it reports the term that is actually built. *)
Definition free_pointed_insert (X : SetoidObject) :
  X ~{Sets}~> Pointed_Forget (FreePointedObject X).
Proof.
  refine {| morphism := fun a => Datatypes.Some a |}.
Defined.

(** ** The universal property

    Every setoid map into the underlying setoid of a pointed set
    extends along the insertion to exactly one pointed map. *)

Section Extension.

Context {X : SetoidObject}.
Context {Y : PointedSetoid}.
Context (h : X ~{Sets}~> Pointed_Forget Y).

Definition fpt_ext_fun (o : carrier (FreePointedObject X)) : carrier Y :=
  match o with
  | Datatypes.Some a => h a
  | Datatypes.None   => pt Y
  end.

Program Definition fpt_ext_map :
  SetoidMorphism (pointed_setoid (FreePointedObject X))
                 (pointed_setoid Y) := {|
  morphism := fpt_ext_fun
|}.
Next Obligation.
  intros a b Hab.
  destruct a as [a|], b as [b|]; simpl in *; try contradiction.
  - now rewrite Hab.
  - reflexivity.
Qed.

(* The one law a pointed map owes, [preserves_pt], is [reflexivity]
   here: the mediator sends the adjoined point to [pt Y] by
   definition. *)
Definition free_pointed_extend : FreePointedObject X ~{PointedSets}~> Y.
Proof using X Y h.
  refine (Build_PointedMorphism (FreePointedObject X) Y fpt_ext_map _).
  simpl.
  reflexivity.
Defined.

Lemma free_pointed_extend_generators (a : carrier X) :
  free_pointed_extend (Datatypes.Some a) ≈ h a.
Proof. reflexivity. Qed.

(* Uniqueness: two cases, no induction.  The [Some] case is the
   hypothesis; the [None] case is the competitor's own [preserves_pt],
   since [None] IS the basepoint of the free object. *)
Lemma free_pointed_extend_unique
  (g : FreePointedObject X ~{PointedSets}~> Y)
  (Hg : ∀ a : carrier X, g (Datatypes.Some a) ≈ h a) :
  g ≈ free_pointed_extend.
Proof.
  intros [a|]; simpl.
  - exact (Hg a).
  - exact (preserves_pt g).
Qed.

End Extension.

Arguments fpt_ext_fun {X Y} h o.
Arguments fpt_ext_map {X Y} h.
Arguments free_pointed_extend {X Y} h.

(** The universal property in the shape [universal_arrow_from_UMP]
    consumes. *)

Theorem free_pointed_universal (X : SetoidObject) :
  ∀ (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y),
    ∃! g : FreePointedObject X ~{PointedSets}~> Y,
      h ≈ fmap[Pointed_Forget] g ∘ free_pointed_insert X.
Proof.
  intros Y h.
  unshelve eexists.
  - exact (free_pointed_extend h).
  - intro a; simpl.
    symmetry; exact (free_pointed_extend_generators h a).
  - intros g Hg o; simpl.
    symmetry; apply (free_pointed_extend_unique h g).
    intro a; symmetry; exact (Hg a).
Qed.

(** Mac Lane §III.1 Exercise 3, pointed row: the universal arrow from X
    to the forgetful functor.  By Theory/Universal/Arrow.v this IS an
    initial object of the comma category [=(X) ↓ Pointed_Forget]. *)

Definition free_pointed_universal_arrow (X : Sets)
  : UniversalArrow X Pointed_Forget :=
  universal_arrow_from_UMP X Pointed_Forget (FreePointedObject X)
    (free_pointed_insert X) (free_pointed_universal X).

(** The same content in the direct encoding, where the universal object
    is named rather than projected out of a comma category. *)

Program Definition free_pointed_AUniversalArrow (X : Sets)
  : AUniversalArrow X Pointed_Forget (FreePointedObject X) := {|
  universal_arrow := free_pointed_insert X
|}.
Next Obligation.
  intros X Y h.
  unshelve eexists.
  - exact (free_pointed_extend h).
  - intro a; simpl.
    exact (free_pointed_extend_generators h a).
  - intros g Hg o; simpl.
    symmetry; apply (free_pointed_extend_unique h g).
    intro a; exact (Hg a).
Qed.

(** ** The free-forgetful adjunction

    Mac Lane §IV.1 Theorem 2, local-to-global: the functor, the
    adjunction and both triangle identities come out of the generic
    machinery with no further proof. *)

Definition FreePointed : Sets ⟶ PointedSets :=
  LeftAdjointFunctorFromUniversalArrows Pointed_Forget
    free_pointed_universal_arrow.

Definition free_pointed_adjunction : FreePointed ⊣ Pointed_Forget :=
  AdjunctionFromUniversalArrows Pointed_Forget free_pointed_universal_arrow.

(** ** Strengths, measured strict-first

    First the [eq_refl] identifications. *)

Example free_pointed_forget_obj (X : PointedSetoid) :
  Pointed_Forget X = pointed_setoid X := eq_refl.

Example free_pointed_carrier (X : SetoidObject) :
  carrier (FreePointedObject X) = option (carrier X) := eq_refl.

Example free_pointed_basepoint (X : SetoidObject) :
  pt (FreePointedObject X) = Datatypes.None := eq_refl.

Example free_pointed_insert_is_Some (X : SetoidObject) (a : carrier X) :
  free_pointed_insert X a = Datatypes.Some a := eq_refl.

Example free_pointed_extend_some_strict (X : SetoidObject)
  (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y) (a : carrier X) :
  free_pointed_extend h (Datatypes.Some a) = h a := eq_refl.

Example free_pointed_extend_none_strict (X : SetoidObject)
  (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y) :
  free_pointed_extend h Datatypes.None = pt Y := eq_refl.

(* [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds, so no proof is involved. *)
Example free_pointed_arrow_is_insert (X : Sets) :
  @arrow _ _ X Pointed_Forget (free_pointed_universal_arrow X)
    = free_pointed_insert X := eq_refl.

Example FreePointed_obj (X : Sets) :
  FreePointed X = FreePointedObject X := eq_refl.

(** The unit.  [unit] is DERIVED in Theory/Adjunction.v (it is ⌊id⌋),
    not a field, so what it computes to has to be checked. *)

Definition free_pointed_unit (X : Sets)
  : X ~{Sets}~> Pointed_Forget (FreePointed X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_pointed_adjunction X.

Example free_pointed_unit_is_insert (X : Sets) (a : carrier X) :
  free_pointed_unit X a = Datatypes.Some a := eq_refl.

(** The forward transpose ⌊−⌋ IS restriction along the insertion, on the
    nose.  This is the control that makes the diagnosis of the three
    rejections below discriminating: one leg of this very [Isomorphism]
    does reduce. *)

Definition free_pointed_transpose {X : Sets} {Y : PointedSets}
  (g : FreePointed X ~{PointedSets}~> Y) : X ~{Sets}~> Pointed_Forget Y :=
  fmap[Pointed_Forget] g ∘ free_pointed_insert X.

Example free_pointed_transpose_is_adj (X : Sets) (Y : PointedSets)
  (g : FreePointed X ~{PointedSets}~> Y) :
  to (@adj _ _ _ _ free_pointed_adjunction X Y) g
    = free_pointed_transpose g := eq_refl.

(** The inverse transpose ⌈−⌉ is the extension, but only up to [≈]: it
    is [unique_obj (ump_universal_arrows …)], and
    [ump_universal_arrows] is [Qed]-opaque.  The first [Fail] probe at
    the end of this file names [free_pointed_extend] for exactly this. *)

Lemma free_pointed_from_adj (X : Sets) (Y : PointedSets)
  (h : X ~{Sets}~> Pointed_Forget Y) :
  from (@adj _ _ _ _ free_pointed_adjunction X Y) h
    ≈ free_pointed_extend h.
Proof.
  apply (free_pointed_extend_unique h).
  intro a.
  exact (@iso_to_from _ _ _ (@adj _ _ _ _ free_pointed_adjunction X Y) h a).
Qed.

(** Restriction to the generators is a bijection whose inverse is
    extension.  The first round trip is [reflexivity] at every
    generator. *)

Lemma free_pointed_transpose_extend {X : Sets} {Y : PointedSets}
  (h : X ~{Sets}~> Pointed_Forget Y) :
  free_pointed_transpose (free_pointed_extend h) ≈ h.
Proof. intro a; simpl; reflexivity. Qed.

Lemma free_pointed_extend_transpose {X : Sets} {Y : PointedSets}
  (g : FreePointed X ~{PointedSets}~> Y) :
  free_pointed_extend (free_pointed_transpose g) ≈ g.
Proof.
  intro o; simpl.
  symmetry; apply (free_pointed_extend_unique (free_pointed_transpose g) g).
  intro a; simpl; reflexivity.
Qed.

(** The counit.  It is the OTHER transpose, ⌈id⌉, so it does not
    compute; what is proved is that it is the identity away from the
    adjoined point and sends that point to the basepoint. *)

Definition free_pointed_counit (Y : PointedSets)
  : FreePointed (Pointed_Forget Y) ~{PointedSets}~> Y :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_pointed_adjunction Y.

Lemma free_pointed_counit_evaluates (Y : PointedSets)
  (o : carrier (Pointed_Forget Y)) :
  free_pointed_counit Y (Datatypes.Some o) ≈ o.
Proof.
  exact (free_pointed_from_adj (Pointed_Forget Y) Y id{Sets}
           (Datatypes.Some o)).
Qed.

Lemma free_pointed_counit_kills_point (Y : PointedSets) :
  free_pointed_counit Y Datatypes.None ≈ pt Y.
Proof. exact (preserves_pt (free_pointed_counit Y)). Qed.

(** The free functor's action on arrows.  It is defined by
    factorization, so the strict identification available is with the
    inverse transpose -- both sides being literally the same opaque
    term -- while its VALUE at a generator needs [≈]. *)

Example free_pointed_fmap_is_from_adj (X Y : Sets) (u : X ~{Sets}~> Y) :
  fmap[FreePointed] u
    = from (@adj _ _ _ _ free_pointed_adjunction X (FreePointed Y))
        (free_pointed_insert Y ∘ u) := eq_refl.

Lemma free_pointed_fmap_some (X Y : Sets) (u : X ~{Sets}~> Y)
  (a : carrier X) :
  fmap[FreePointed] u (Datatypes.Some a) ≈ Datatypes.Some (u a).
Proof.
  exact (free_pointed_from_adj X (FreePointed Y)
           (free_pointed_insert Y ∘ u) (Datatypes.Some a)).
Qed.

Lemma free_pointed_fmap_none (X Y : Sets) (u : X ~{Sets}~> Y) :
  fmap[FreePointed] u Datatypes.None ≈ Datatypes.None.
Proof. exact (preserves_pt (fmap[FreePointed] u)). Qed.

(** ** Naturality, in Mac Lane's §IV.1 shape

    The two clauses are the adjunction class's own fields, restated in
    the transpose's vocabulary. *)

Lemma free_pointed_naturality_in_set {X Y : Sets} {Z : PointedSets}
  (g : FreePointed Y ~{PointedSets}~> Z) (u : X ~{Sets}~> Y) :
  free_pointed_transpose (g ∘ fmap[FreePointed] u)
    ≈ free_pointed_transpose g ∘ u.
Proof. exact (@to_adj_nat_l _ _ _ _ free_pointed_adjunction X Y Z g u). Qed.

Lemma free_pointed_naturality_in_pointed {X : Sets} {Y Z : PointedSets}
  (k : Y ~{PointedSets}~> Z) (g : FreePointed X ~{PointedSets}~> Y) :
  free_pointed_transpose (k ∘ g)
    ≈ fmap[Pointed_Forget] k ∘ free_pointed_transpose g.
Proof. exact (@to_adj_nat_r _ _ _ _ free_pointed_adjunction X Y Z k g). Qed.

(** The triangle identities, inherited. *)

Corollary free_pointed_triangle_left (X : Sets) :
  free_pointed_counit (FreePointed X)
    ∘ fmap[FreePointed] (free_pointed_unit X) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ free_pointed_adjunction X). Qed.

Corollary free_pointed_triangle_right (Y : PointedSets) :
  fmap[Pointed_Forget] (free_pointed_counit Y)
    ∘ free_pointed_unit (Pointed_Forget Y) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ free_pointed_adjunction Y). Qed.

(* The composite [Pointed_Forget ◯ FreePointed] has object action
   [option].  No monad is built; see the header. *)
Example free_pointed_maybe_carrier (X : Sets) :
  carrier (Pointed_Forget (FreePointed X)) = option (carrier X) := eq_refl.

(** ** Non-vacuity

    First, two facts holding at EVERY generating setoid.  Both are
    definitional, because [option_setoid] relates nothing across the two
    constructors: the adjoined point is not in the image of the
    insertion, and the insertion is injective. *)

Theorem free_pointed_point_is_new (X : SetoidObject) (a : carrier X) :
  free_pointed_insert X a ≈ pt (FreePointedObject X) → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_insert_injective (X : SetoidObject)
  (a b : carrier X) :
  free_pointed_insert X a ≈ free_pointed_insert X b → a ≈ b.
Proof. exact (fun H => H). Qed.

(** Both facts are also visible by mapping OUT, and it is worth being
    explicit that here that is a CROSS-CHECK and not a necessity.  In
    the quotient rows of this exercise a negative can only be obtained
    by mapping out of the construction, since no induction on a
    generating congruence yields one; this row has no congruence, so the
    two theorems above are available directly.  What mapping out adds is
    that the mediator produced by the universal property COMPUTES.

    The probe objects are built over [poly_unit] and [option] rather
    than over [bool], so that no witness below pins a universe to
    [Set]. *)

Definition fpt_one : SetoidObject := {| carrier := poly_unit |}.

Definition fpt_two : SetoidObject := {| carrier := option poly_unit |}.

(** The two-point probe object of Instance/Sets/Pointed.v:352 IS the
    free pointed set on the one-point setoid -- whole record, [eq_refl].
    So the smallest object that file needed in order to detect
    monomorphisms is the free one on a single generator. *)

Example PointedTwo_is_free_on_one :
  FreePointedObject fpt_one = PointedTwo := eq_refl.

(** The free pointed set on a two-element setoid has exactly three
    elements: two generators and the adjoined point.  Exhaustiveness is
    stated at Leibniz equality, the carrier being an [option] of an
    [option] of [poly_unit]. *)

Definition fpt_gen1 : carrier (FreePointedObject fpt_two) :=
  Datatypes.Some (Datatypes.Some ttt).

Definition fpt_gen2 : carrier (FreePointedObject fpt_two) :=
  Datatypes.Some Datatypes.None.

Theorem free_pointed_two_has_three_elements
  (o : carrier (FreePointedObject fpt_two)) :
  ((o = fpt_gen1) + (o = fpt_gen2)) + (o = pt (FreePointedObject fpt_two)).
Proof.
  destruct o as [[u|]|].
  - destruct u; left; left; reflexivity.
  - left; right; reflexivity.
  - right; reflexivity.
Qed.

Theorem free_pointed_two_generators_distinct : fpt_gen1 ≈ fpt_gen2 → False.
Proof. exact (fun H => H). Qed.

(** Mapping out.  [PointedTwo] is the target; its carrier is
    [option poly_unit], which is also the carrier of [fpt_two], so the
    identity setoid map is a probe, and a constant at the free point is
    a second one. *)

Definition fpt_probe_id : fpt_two ~{Sets}~> Pointed_Forget PointedTwo :=
  id{Sets}.

Definition fpt_probe_const : fpt_two ~{Sets}~> Pointed_Forget PointedTwo.
Proof.
  refine {| morphism := fun _ => Datatypes.Some ttt |}.
  exact (fun _ _ _ => reflexivity (Datatypes.Some ttt)).
Defined.

(** The mediator computes, at Leibniz equality, on every element. *)

Example fpt_probe_id_gen1 :
  free_pointed_extend fpt_probe_id fpt_gen1 = Datatypes.Some ttt := eq_refl.

Example fpt_probe_id_gen2 :
  free_pointed_extend fpt_probe_id fpt_gen2 = Datatypes.None := eq_refl.

Example fpt_probe_id_point :
  free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two))
    = Datatypes.None := eq_refl.

Example fpt_probe_const_gen2 :
  free_pointed_extend fpt_probe_const fpt_gen2 = Datatypes.Some ttt
  := eq_refl.

Example fpt_probe_const_point :
  free_pointed_extend fpt_probe_const (pt (FreePointedObject fpt_two))
    = Datatypes.None := eq_refl.

(** Separation by mapping out.  The identity probe separates the first
    generator from both the second generator and the adjoined point; the
    constant probe separates the second generator from the adjoined
    point.  So the three elements are pairwise separated by pointed maps
    into [PointedTwo]. *)

Theorem free_pointed_gen1_gen2_separated_out :
  free_pointed_extend fpt_probe_id fpt_gen1
    ≈ free_pointed_extend fpt_probe_id fpt_gen2 → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_gen1_point_separated_out :
  free_pointed_extend fpt_probe_id fpt_gen1
    ≈ free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two))
    → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_gen2_point_separated_out :
  free_pointed_extend fpt_probe_const fpt_gen2
    ≈ free_pointed_extend fpt_probe_const (pt (FreePointedObject fpt_two))
    → False.
Proof. exact (fun H => H). Qed.

(** The identity probe's extension is NOT injective -- it must collapse
    the second generator onto the adjoined point, a pointed map having
    nowhere else to send the point.  So the extension is genuinely the
    mediator of a universal property and not an isomorphism in
    disguise. *)

Theorem free_pointed_extend_id_collapses :
  free_pointed_extend fpt_probe_id fpt_gen2
    ≈ free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two)).
Proof. reflexivity. Qed.

(** ** Guards

    Each [Fail] below was stripped once and confirmed to report a
    genuine "cannot unify", not a scope, notation or reference error,
    and each names the constant whose strictness is being refuted.  The
    instrument check is scope-free. *)

Fail Definition free_pointed_instrument_check :
  Datatypes.true = Datatypes.false := eq_refl.

Fail Example free_pointed_from_adj_is_not_strict
  (X : Sets) (Y : PointedSets) (h : X ~{Sets}~> Pointed_Forget Y) :
  from (@adj _ _ _ _ free_pointed_adjunction X Y) h
    = free_pointed_extend h := eq_refl.

Fail Example free_pointed_counit_is_not_strict
  (Y : PointedSets) (o : carrier (Pointed_Forget Y)) :
  free_pointed_counit Y (Datatypes.Some o) = o := eq_refl.

Fail Example free_pointed_fmap_is_not_strict
  (X Y : Sets) (u : X ~{Sets}~> Y) (a : carrier X) :
  fmap[FreePointed] u (Datatypes.Some a) = Datatypes.Some (u a) := eq_refl.
