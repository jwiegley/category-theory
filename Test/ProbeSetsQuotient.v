(** * Boundary probes for the quotient setoid and the Sets coequalizer

    Companion to Instance/Sets/Quotient.v, Instance/Sets/Coequalizer.v,
    Instance/Sets/Quotient/Partition.v and
    Instance/Sets/Coequalizer/Interconnect.v (issue #315; Mac Lane §III.1
    construction 4 and §III.3 remark 2 / exercise 5, Awodey §3.4-§3.5,
    Fong and Spivak §1.2.1 and §6.2.4).  Those files make five negative
    claims -- one about which route to a representation is available at
    [Sets], two universe walls, and two conversion boundaries -- pinned
    below by six [Fail] commands (the first boundary costs two) against
    twelve positive controls.  A measurement made once and written into a
    header is not guarded by anything; these are.  **If the [Fail]
    commands below stop failing, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  The instrument itself was checked -- wrapping [Fail] around a
    succeeding command reports "The command has not failed!" and aborts
    compilation -- and each negative was compiled once with the [Fail]
    stripped, to confirm the error is the intended one.  What each of the
    six strips reported is recorded beside its probe.

    THE FIVE BOUNDARIES.

    (1) THE YONEDA ROUTE TO A REPRESENTATION IS NOT AVAILABLE AT [Sets].
    Theory/Universal/Element.v's [universal_element_yoneda] is stated
    over [Yoneda_Lemma], which identifies a category's object, hom and
    proof universes; [Sets@{o so} : Category@{so o o}] has its objects
    strictly above its homs, so no instantiation exists.  This is the
    same donor restriction Test/ProbeUniversalElement.v pins at
    Instance/Coq/Nat.v's [Endos] -- a DIFFERENT category, so the two
    probes are not duplicates -- and it is why
    Instance/Sets/Quotient.v's [sets_quot_Representable] goes through the
    Yoneda-free [ue_representation].  Two positive controls: that route
    at [Sets], and the Yoneda one at a category whose three universes can
    be identified.

    (2) THE UNTRUNCATED CLASS OBJECT IS NOT AN OBJECT OF THE SAME [Sets].
    Instance/Sets/Quotient/Partition.v takes the class of an element to
    be a [Prop]-valued predicate.  That is not a stylistic choice: since
    [obj[Sets@{o so}]] is [SetoidObject@{o o}], a [Type@{o}]-valued
    predicate on the carrier has type [Type@{o+1}] and does not fit.  The
    probe must PIN THE UNIVERSE INSTANCE, because without a binder Coq
    silently uses two different [Sets] and the claim evaporates -- the
    erratum CLAUDE.md records for [Check (Cat : obj[Cat])], met here
    again.  Two positive controls: the [Prop]-valued carrier at the very
    same level, and the [Type]-valued one a level up.

    (2') THE IMPREDICATIVE PHRASING OF THE GENERATED RELATION DOES NOT
    FIT EITHER.  Awodey's §3.5 exercise 4 defines the coequalizer's
    relation as the intersection of all equivalence relations containing
    the given pairs.  Instance/Sets/Coequalizer.v's header says that
    phrasing is unavailable at [Sets]' universe and generates the
    relation inductively instead; the probe measures the claim, against a
    positive control showing that the [Prop]-valued intersection DOES
    fit.

    (3) COARSENING IS NOT CONVERSION.  Instance/Sets/Quotient.v's
    [sets_quot_finest_eq] closes by [eq_refl]: quotienting by the
    setoid's own `≈` returns the [SetoidObject] record itself.  The
    over-read to guard against is that a quotient whose relation is
    PROVABLY equivalent to `≈` does the same.  It does not:
    Instance/Sets/Coequalizer.v's [coeq_rel_diagonal] shows that the
    coequalizer of a map with itself relates exactly the `≈`-related
    points, and the object is still not the one it started from.

    (4) A COEQUALIZER IDENTIFICATION IS A DERIVATION, NOT A COMPUTATION.
    Instance/Sets/Coequalizer/Interconnect.v's header says the carrier of
    the coequalizer is the ic_port type on the nose while `≈` moves.  Both
    halves are probed: [IcP0] and [IcP1] are distinct ports (the [Fail]) and
    identified in the coequalizer (the control), so the coarsening is
    real and the carrier really did not move. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Quotient.Partition.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Sets.Coequalizer.Interconnect.

Generalizable All Variables.

(** ** (1) The Yoneda route at [Sets] *)

Section YonedaAtSets.

Context (H : Sets ⟶ Sets).
Context (r : Sets).
Context (U : AUniversalElement H r).

(** Positive control: the Yoneda-FREE route builds the representation
    at [Sets], and [Instance/Sets/Quotient.v] uses exactly it. *)
Check (ue_representation H r U).
Check (AUniversalElement_of_repr H r).

(** Negative: the Yoneda-based statement of the same correspondence is
    not formable here.  (With the [Fail] stripped, both of the two
    commands below report a universe inconsistency of the form "The term
    "H" has type "Sets@{a b} ⟶ Sets@{a b}" while it is expected to have
    type "?D ⟶ Sets@{c d}" (universe inconsistency: Cannot enforce
    b = d because b < d)" -- the strict inequality being exactly [Sets]'
    objects sitting above its homs.) *)
Fail Check (universal_element_yoneda H r).

Fail Check (universal_element_representation H r).

End YonedaAtSets.

(** Positive control for the instrument: at a category whose object, hom
    and proof universes ARE identified, the Yoneda statement elaborates.
    So the refusal above is a fact about [Sets], not about the
    constant. *)
Section YonedaSmall.

Universe u.

Context (D : Category@{u u u}).
Context (K : D ⟶ Sets).
Context (d : D).

Check (universal_element_yoneda K d).

End YonedaSmall.

(** ** (2) The untruncated class object *)

(** Positive control: the [Prop]-valued part-carrier, at a PINNED [Sets]
    universe instance. *)
Definition probe_parts_prop@{o} (A : SetoidObject@{o o}) : Type@{o} :=
  carrier A -> Prop.

(** Positive control: the [Type]-valued one exists a level up. *)
Definition probe_parts_type_up@{o o'} (A : SetoidObject@{o o}) : Type@{o'} :=
  carrier A -> Type@{o}.

(** Negative: it does not exist at the level of the carrier.  (With the
    [Fail] stripped this reports "The term "A → Type" has type
    "Type@{o+1}" while it is expected to have type "Type@{o}" (universe
    inconsistency: Cannot enforce o < o because o = o)" -- a genuine
    universe inconsistency naming the declared binder.) *)
Fail Definition probe_parts_type_same@{o} (A : SetoidObject@{o o}) : Type@{o} :=
  carrier A -> Type@{o}.

(** ... and the [Prop]-valued relation really is usable as a quotient's
    `≈` at a pinned instance, which is what [prop_rel_squash_stable]
    rests on. *)
Definition probe_prop_quotient@{o so} (A : obj[Sets@{o so}])
  (Rp : carrier A -> carrier A -> Prop) (HRp : Equivalence Rp) :
  obj[Sets@{o so}] :=
  {| carrier := carrier A ;
     is_setoid := {| equiv := Rp ; setoid_equiv := HRp |} |}.

(** ... and the impredicative phrasing Awodey's §3.5 exercise 4 uses for
    the generated relation -- the intersection of all equivalence
    relations containing the given pairs -- does not fit either, for the
    same reason: quantifying over all [crelation]s on the carrier
    quantifies over a [Type@{o+1}].  (With the [Fail] stripped this
    reports "The term "∀ R : crelation A, Equivalence R → R a b" has type
    "Type@{o+1}" while it is expected to have type "Type@{o}" (universe
    inconsistency: Cannot enforce o < o because o = o)".) *)
Fail Definition probe_intersection_type@{o} (A : SetoidObject@{o o})
  (a b : carrier A) : Type@{o} :=
  forall R : crelation@{o o} (carrier A), Equivalence R -> R a b.

(** Positive control: the [Prop]-valued intersection DOES fit, [Prop]
    being impredicative -- which is why Awodey's phrasing is available
    classically and the inductive generation is what replaces it here. *)
Definition probe_intersection_prop@{o} (A : SetoidObject@{o o})
  (a b : carrier A) : Prop :=
  forall R : carrier A -> carrier A -> Prop,
    (forall x, R x x) -> R a b.

(** ** (3) Coarsening is not conversion *)

(** Positive control: quotienting by the setoid's OWN `≈` returns the
    record, by [eq_refl]. *)
Definition probe_finest_eq (A : SetoidObject) :
  SetsQuotient A (@equiv _ A) (@setoid_equiv _ A) = A := eq_refl.

(** Negative: the coequalizer of a map with itself relates exactly the
    `≈`-related points ([coeq_rel_diagonal]) and is still not the
    codomain.  (With the [Fail] stripped this reports "cannot unify
    "SetsCoeq bool_false_map bool_false_map" and "BoolSet"" -- the two
    relations are provably interderivable and the two records are not
    convertible.) *)
Fail Definition probe_diagonal_eq :
  SetsCoeq bool_false_map bool_false_map = BoolSet := eq_refl.

(** ... while the fact the header actually claims -- that the two
    relations agree -- is a theorem, in tree. *)
Check (@coeq_rel_diagonal UnitSet BoolSet bool_false_map).

(** ** (4) Identification in a coequalizer is a derivation *)

(** Positive controls: the carrier did not move, and the two ports ARE
    identified in the coequalizer. *)
Definition probe_interconnect_carrier : carrier Interconnect = ic_port := eq_refl.

Check port_P0_P1_merged.

(** Negative: they are nevertheless distinct ports.  (With the [Fail]
    stripped this reports "cannot unify "IcP0" and "IcP1"".) *)
Fail Definition probe_ports_eq : IcP0 = IcP1 := eq_refl.

(** ... and the coequalizer does not identify everything: this is the
    mapping-out argument, in tree. *)
Check port_P0_P3_apart.
