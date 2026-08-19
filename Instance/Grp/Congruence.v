Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

(* [Category.Instance.Grp] and its satellites are required LAST, deliberately,
   for the reason [Instance/Grp/Free.v]:15-23 gives: [Construction/Deloop.v]
   also declares a record called [GrpObject], and the two names would
   otherwise collide.  With this order the unqualified [GrpObject],
   [grp_unit], [grp_mul] and [grp_inv] below are always [Instance/Grp.v]'s --
   the record [Grp] is the category of, and hence the record #313's
   [NormalSubgroup] and [QuotientGrp] are over.  Construction/Deloop.v's
   record and its projection are named in full, as
   [Category.Construction.Deloop.GrpObject] and
   [Category.Construction.Deloop.grp_monoid], on the two occasions they are
   mentioned in code (in [grp_deloop_GrpObject] and in
   [deloop_GrpObject_monoid]). *)
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Congruences on a delooped group are normal subgroups

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §II.8
    Exercise 2, printed p. 52 [maclane:II.8:ex2]; Awodey, "Category
    Theory", 2nd ed., §4.2 printed p. 83 [awodey:4.2:def-normal-subgroup]
    and §4.5 Exercise 1, printed p. 91 [awodey:4:ex1].
    nLab: https://ncatlab.org/nlab/show/normal+subgroup
    nLab: https://ncatlab.org/nlab/show/congruence
    Wikipedia: https://en.wikipedia.org/wiki/Normal_subgroup

    A group read as a one-object category has, for its hom-set, the group
    itself; a congruence on that category is therefore an equivalence
    relation on the group compatible with multiplication on both sides.
    Mac Lane's exercise is that such relations are exactly the normal
    subgroups: from N one takes "f and g differ by a member of N", and
    from a congruence one takes the class of the identity.  Quotienting
    the category then returns the delooping of the factor group, so
    Awodey's group homomorphism theorem is the universal property of the
    quotient CATEGORY read at one object.

    WHY THE INTERESTING PART IS A NAMING PROBLEM.  The tree carries TWO
    records called [GrpObject], and the exercise straddles them.
    [Construction/Deloop.v]:267 layers one on [MonObject], carrying both
    unit laws and both inverse laws as fields; that is the record
    [Deloop]'s group-case results ([Deloop_group_invertible],
    [Deloop_IsGroupoid]) are stated over.  [Instance/Grp.v]:184 declares a
    flat one with only the left-handed laws, the right-handed ones and
    respectfulness of inversion being derived; that is the record [Grp] is
    the category of, and hence the record #313's [NormalSubgroup],
    [QuotientGrp] and [hom_theorem] are over.  A statement of this
    exercise has to reach both.

    HOW THE GAP IS CLOSED, and the measured surprise: NO RECORD
    CONVERSION IS NEEDED, because the delooping of an [Instance/Grp.v]
    group is already in tree.  [Instance/Grp/Free.v]:272-295 builds
    [grp_deloop_monoid], [grp_deloop] and [grp_deloop_IsGroupoid] --
    incidentally, on its way to the free group -- and that is exactly "the
    one-object groupoid of an [Instance/Grp.v] group".  Everything below
    is stated over [grp_deloop], so the correspondence is with congruences
    on THE delooping in tree rather than on a fresh copy of it.  (The one
    bridge the tree names, [Instance/Rep.v]:176's [grp_mon], is a
    different thing: it lands in [MonObject] and drops the inverse.
    [Instance/Grp/Free.v]:91-92 says in terms that [grp_mon] is "the only
    bridge between them in tree", so no record-to-record converter existed
    at the parent commit -- and this file supplies one below, which is
    exactly what makes that sentence stale rather than a limitation.
    [Instance/Rng/MonoidRing.v]:66 is cited by Free.v's neighbours for a
    RELATED but different observation: that Rep.v "had to bridge two
    identically named [GrpObject] records with [grp_mon]", which records
    the bridge's existence, not an absence.)  What this file observes is
    that the exercise never needed the converter in the first place.

    THE CONVERSION IS SUPPLIED ANYWAY, AND MEASURED, for the readers who
    do want Construction/Deloop.v's group-case vocabulary:
    [grp_deloop_GrpObject] takes an [Instance/Grp.v] group to a
    [Category.Construction.Deloop.GrpObject], built by REUSE rather than
    by a fresh record literal -- [Structure/Groupoid.v]'s [MonInverses]
    and [GrpObject_of], which exist precisely to separate "has inverses"
    from the bundling.  It is proved NOT to be a third notion:
    [deloop_GrpObject_agrees] is [eq_refl].

    THE BRIDGE THE ISSUE'S QA CORRECTION NAMES IS A DIFFERENT ONE, and is
    deliberately not cited.  That correction directs that #255's Work item
    4 be cited as the reconciliation -- [Instance/Grp.v]'s
    [Grp_GroupObject]/[GroupObject_GrpObject].  Those relate
    [Instance/Grp.v]'s record to [Structure/Group.v]'s INTERNAL
    [GroupObject], a group object in a cartesian monoidal category, which
    is a third notion again and does not reach
    [Construction/Deloop.v]'s bare setoid record.  So it could not have
    closed this gap, and [grp_deloop_GrpObject] is supplied in its
    place.

    WHAT THE FOUR CONGRUENCE FIELDS COST: NOTHING.  [HomCongruence]
    ([Construction/Quotient.v]:296) asks for containment of `≈`, symmetry,
    transitivity and compatibility with composition.  At [grp_deloop G]
    with the relation "f * g⁻¹ lies in N" these are, in order, #313's
    [quot_rel_of_equiv], [quot_rel_sym], [quot_rel_trans] and
    [quot_rel_mul] -- four of the five [quot_rel] lemmas [QuotientGrp]'s
    own obligations consume (the fifth being [quot_rel_refl], needed there
    for the [Equivalence] and not here), applied verbatim, with no
    argument reordered and no new proof: [ns_congruence] is a record
    literal of four eta-expanded applications of those names.  The same
    reuse runs through the round trip: [ns_of_cong_of_ns]'s whole proof is
    [quot_rel_unit_iff] applied.

    ORIENTATION.  #313's [quot_rel N a b] is "a * b⁻¹ lies in N", the
    orientation [Instance/Grp/Abelianization.v]'s [abel_eq] fixed; issue
    #301's text writes the condition the other way round, "g⁻¹ * f lies in
    N".  The two agree, and [quot_rel_flip] proves it -- consuming
    NORMALITY in both directions, so the choice is not a notational one
    for a bare subgroup.

    WHAT IS DELIVERED.

      - [grp_deloop_GrpObject], the record conversion, with
        [deloop_GrpObject_agrees] ([eq_refl]) identifying its delooping
        with the tree's;
      - [ns_rel] / [ns_congruence]: the congruence of a normal subgroup,
        and [deloop_quotient] the quotient category;
      - [cong_ns]: the normal subgroup of a congruence, the class of the
        identity;
      - [ns_of_cong_of_ns] and [cong_of_ns_of_cong]: the two round trips,
        each a biconditional, packaged as [ns_cong_iso], an ISOMORPHISM OF
        SETOIDS in [Sets] between the normal subgroups of G and the
        congruences on its delooping;
      - [congruence_iff_normal]: for an arbitrary SUBGROUP S, the relation
        "f * g⁻¹ in S" is a congruence exactly when S is normal -- so the
        correspondence is with normal subgroups and not merely defined on
        them;
      - [deloop_quotient_iso]: the quotient category of the delooping is
        the delooping of #313's [QuotientGrp N], at [≅[StrictCat]];
      - [hom_theorem_via_quotient_category]: Awodey §4.5 Exercise 1 --
        #313's [hom_theorem] obtained from [Construction/Quotient.v]'s
        [QuotientLift]/[QuotientLift_unique], with the produced mediator
        identified with [quot_med] by [eq_refl] on the underlying map;
      - [kernel_ns] with [kernel_ns_iff]: Awodey §4.2's kernel clause
        given its categorical provenance -- the kernel of a group
        homomorphism is normal because the kernel congruence of a FUNCTOR
        is a congruence ([FunctorKernel_Congruence]) -- WITHOUT re-proving
        #313's [KernelNS], which is cited and left alone;
      - [coset_orientations_differ]: the two orientations of the coset
        relation are not interchangeable once normality is dropped,
        witnessed over #313's non-normal [S3_refl_sub];
      - the S3 witnesses, both signs.

    WHAT IS NOT DELIVERED.  No congruence lattice and no correspondence
    theorem (the subgroups of G/N); no functoriality of N ↦ [ns_rel N] in
    G; no comparison with [Construction/Quotient.v]'s generated congruence
    [CongClosure] (the normal closure of a subgroup is
    [Instance/Grp/Quotient/Colimit.v]'s, and no claim is made that the two
    closures agree); no CONGRUENCE or NORMAL-SUBGROUP statement over
    [Construction/Deloop.v]'s own [GrpObject], since #313's machinery is
    over [Instance/Grp.v]'s -- that record occurs in this file only in
    [grp_deloop_GrpObject]'s type and in the three constants built from
    it ([deloop_GrpObject_agrees], [deloop_GrpObject_monoid],
    [grp_deloop_IsGroupoid']), all in the conversion subsection; no monoid
    analogue -- [cong_ns] spends both inverse laws (in its
    closure-under-inverse and normality fields, and again in
    [cong_of_ns_of_cong]), so nothing below says anything about
    congruences on a delooped MONOID, and no claim is made about what they
    correspond to; and no Leibniz equality of the two categories in
    [deloop_quotient_iso].  That last one is MEASURED rather than merely
    unproved -- Test/ProbeGrpCongruence.v, negative 3, records that
    conversion rejects the identification at the current definitions --
    but it is not PROVED: no inequality is stated, here or anywhere
    (the wording follows [Theory/Universal/Arrow/Dual.v]'s).

    THE CATEGORY-LEVEL HOMOMORPHISM THEOREM EXISTS, UNDER NO SUCH NAME.
    Awodey's Exercise 1 asks for the group theorem as a SPECIALIZATION,
    which presupposes something to specialize, so the tree was searched
    before the word was used.  A case-insensitive search for the phrase
    "homomorphism theorem" over every .v file returns, outside this file's
    own prose, exactly one hit -- [Instance/Grp/Quotient.v]:572 -- and
    that is the GROUP statement.  So nothing in the tree is NAMED the
    categorical homomorphism theorem.  The STATEMENT is nevertheless
    present, as the universal property of the quotient category:
    [Construction/Quotient.v]'s [QuotientLift] (the lift),
    [QuotientLift_factors_strict] (the triangle, at [StrictCat] strength)
    and [QuotientLift_unique] (uniqueness).  So the specialization below
    is real and is not dressing up a group result as a corollary of
    nothing; what had to be checked was that the general statement was
    there, and it is.  (A phrase search is evidence about NAMING; the
    positive claim rests on reading those three constants, not on the
    grep.)

    A MEASUREMENT ABOUT THAT UNIQUENESS, disclosed because it bounds how
    much the specialization proves.  [QuotientLift_unique]'s proof is
    [exact HG]: in a quotient category the projection is the identity on
    morphisms, so "any competitor agreeing with F after the projection
    agrees with the lift" is the hypothesis restated.  Instantiated at the
    delooping that is exactly why the group-level uniqueness comes out
    with no work -- the content sits in [QuotientLift] existing at all,
    and in #313's [kills_descends].  The route below consumes exactly two
    proofs ABOUT N -- that descent lemma, and [quot_rel_refl], which
    supplies the two functor-law fields of [quot_to_deloop] and
    [deloop_to_quot] (four sites in all).  The rest is the
    homomorphism/functor dictionary ([hom_MonHom], [Deloop_map]) together
    with [Build_GrpHom']'s [grp_map_unit_from_mul], a second
    group-theoretic proof.  All three are named here so that the smallness
    claim is not read as covering more than it does; an earlier draft said
    [kills_descends] was the ONLY one, which over-read. *)

(** ** The record conversion, supplied and measured

    [Instance/Grp.v]'s group as a [Category.Construction.Deloop.GrpObject].
    The inverse operation and its two laws are packaged first as
    [Structure/Groupoid.v]'s [MonInverses] -- the record that file
    introduced to separate "this monoid has inverses" from the bundling --
    and [GrpObject_of] does the bundling.  The right inverse law is
    [Instance/Grp.v]'s DERIVED [grp_mul_inv_r], not a field. *)

Definition grp_MonInverses (H : GrpObject) : MonInverses (grp_deloop_monoid H) :=
  @Build_MonInverses (grp_deloop_monoid H)
    (grp_inv H) (grp_mul_inv_l H) (grp_mul_inv_r H).

Definition grp_deloop_GrpObject (H : GrpObject)
  : Category.Construction.Deloop.GrpObject :=
  GrpObject_of (grp_MonInverses H).

(** The conversion introduces no third delooping: the category it produces
    IS [Instance/Grp/Free.v]'s [grp_deloop H], by convertibility -- the
    [eq_refl] exception to the `≈` discipline, and the check that
    [GrpObject_of] moved fields rather than rebuilding them. *)
Example deloop_GrpObject_agrees (H : GrpObject) :
  Deloop (grp_deloop_GrpObject H) = grp_deloop H := eq_refl.

Example deloop_GrpObject_monoid (H : GrpObject) :
  Category.Construction.Deloop.grp_monoid (grp_deloop_GrpObject H)
    = grp_deloop_monoid H := eq_refl.

(** Consequently [Construction/Deloop.v]'s group-case result is available
    at an [Instance/Grp.v] group, and its chosen inverse is the group
    inverse on the nose -- as is [Instance/Grp/Free.v]'s own witness.  The
    two [IsGroupoid] structures are NOT the same term (their [IsIsomorphism]
    law fields are separately proved), which is measured rather than
    assumed: Test/ProbeGrpCongruence.v, negative 1. *)
Definition grp_deloop_IsGroupoid' (H : GrpObject) : IsGroupoid (grp_deloop H) :=
  Deloop_IsGroupoid (grp_deloop_GrpObject H).

Example grp_deloop_ginv (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid' H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

Example grp_deloop_ginv_Free (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(** ** Arithmetic of the delooping

    Every one of these is [eq_refl]; they are recorded so that the
    congruence proofs below can be read as group computations without
    unfolding [Deloop]. *)

Section DeloopArithmetic.

Context {G : GrpObject}.

(** An element of G, read as an arrow of the delooping.  Definitional in
    both directions; it exists only to give the elaborator the hom type
    when a [HomCongruence] field is applied to a group element. *)
Definition deloop_arr (a : carrier G) : ttt ~{grp_deloop G}~> ttt := a.

Example deloop_hom_type (x y : grp_deloop G) :
  (x ~{grp_deloop G}~> y) = carrier G := eq_refl.

Example deloop_id_is_unit : @id (grp_deloop G) ttt = grp_unit G := eq_refl.

Example deloop_compose_is_mul (f g : carrier G) :
  @compose (grp_deloop G) ttt ttt ttt f g = grp_mul G f g := eq_refl.

End DeloopArithmetic.

(** ** From a normal subgroup to a congruence

    The relation is #313's [quot_rel], constant in the two objects (there
    is only one).  The four [HomCongruence] fields are #313's four
    [quot_rel] lemmas, verbatim. *)

Definition ns_rel {G : GrpObject} (N : NormalSubgroup G)
  : HomRelT (grp_deloop G) := fun _ _ f g => quot_rel N f g.

(** The relation IS [quot_rel], by convertibility -- so every lemma #313
    proves about [quot_rel] is a lemma about this congruence. *)
Example ns_rel_is_quot_rel {G : GrpObject} (N : NormalSubgroup G)
  (f g : carrier G) : ns_rel N ttt ttt f g = quot_rel N f g := eq_refl.

(** Mac Lane §II.8 Exercise 2, one direction.  Kept a plain [Definition]
    rather than an [Instance], following [FunctorKernel_Congruence]'s own
    convention in [Construction/Quotient.v]:555-558: nothing new enters
    typeclass search, and the witness stays transparent. *)
Definition ns_congruence {G : GrpObject} (N : NormalSubgroup G)
  : @HomCongruence (grp_deloop G) (ns_rel N) :=
  @Build_HomCongruence (grp_deloop G) (ns_rel N)
    (fun x y f g H   => quot_rel_of_equiv N f g H)
    (fun x y f g H   => quot_rel_sym N f g H)
    (fun x y f g h H1 H2 => quot_rel_trans N f g h H1 H2)
    (fun x y z f f' g g' H1 H2 => quot_rel_mul N f f' g g' H1 H2).

(** The quotient category of the delooping.  The congruence witness is
    passed explicitly, since [ns_congruence] is not an instance. *)
Definition deloop_quotient {G : GrpObject} (N : NormalSubgroup G) : Category :=
  @Quotient (grp_deloop G) (ns_rel N) (ns_congruence N).

Definition deloop_quotient_proj {G : GrpObject} (N : NormalSubgroup G)
  : grp_deloop G ⟶ deloop_quotient N :=
  @QuotientProj (grp_deloop G) (ns_rel N) (ns_congruence N).

(** ** The orientation of the relation

    Issue #301's text states the condition as "g⁻¹ * f lies in N"; #313's
    [quot_rel], which this file reuses, states it as "f * g⁻¹ lies in N".
    They agree, and NORMALITY is what makes them agree: each direction
    conjugates the witness, by g⁻¹ one way and by g the other.  For a
    subgroup that is not normal the two are the right- and left-coset
    relations, and they can come apart -- EXHIBITED rather than proved in
    general: [coset_orientations_differ] below separates them at one pair
    over #313's non-normal [S3_refl_sub], and no claim is made that every
    non-normal subgroup separates them. *)

Lemma quot_rel_flip {G : GrpObject} (N : NormalSubgroup G) (a b : carrier G) :
  quot_rel N a b ↔ sub_mem N (grp_mul G (grp_inv G b) a).
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at N (a := grp_mul G (grp_mul G (grp_inv G b)
                                      (grp_mul G a (grp_inv G b)))
                       (grp_inv G (grp_inv G b)))).
    + rewrite (grp_inv_inv G b).
      rewrite (grp_mul_assoc G (grp_inv G b) (grp_mul G a (grp_inv G b)) b).
      rewrite (grp_mul_assoc G a (grp_inv G b) b).
      rewrite (grp_mul_inv_l G b), (grp_mul_unit_r G a).
      reflexivity.
    + exact (ns_conj N (grp_inv G b) _ K).
  - apply (sub_at N (a := grp_mul G (grp_mul G b
                                      (grp_mul G (grp_inv G b) a))
                       (grp_inv G b))).
    + rewrite <- (grp_mul_assoc G b (grp_inv G b) a).
      rewrite (grp_mul_inv_r G b), (grp_mul_unit_l G a).
      reflexivity.
    + exact (ns_conj N b _ K).
Qed.

(** Issue #301's own formula, as the congruence's relation. *)
Corollary ns_rel_flip {G : GrpObject} (N : NormalSubgroup G) (f g : carrier G) :
  ns_rel N ttt ttt f g ↔ sub_mem N (grp_mul G (grp_inv G g) f).
Proof. exact (quot_rel_flip N f g). Qed.

(** ** From a congruence to a normal subgroup: the class of the identity

    The other direction of Mac Lane's exercise.  Every field is a short
    chain of applications of the four congruence fields and their derived
    [cong_refl] -- between one and seven of them, the closure fields for
    inverse (seven) and for conjugation (six) being the long ones --
    against a unit or inverse law of G where a law is needed at all (the
    saturation and unit fields need none).  No property of the relation
    beyond the four it carries is used anywhere. *)

Section Converse.

Context {G : GrpObject}.
Context (R : HomRelT (grp_deloop G)).
Context `{HR : @HomCongruence (grp_deloop G) R}.

Definition cong_mem (a : carrier G) : Type :=
  R ttt ttt (deloop_arr a) (@id (grp_deloop G) ttt).

Program Definition cong_sub : Subgroup G := {|
  sub_mem := cong_mem
|}.
Next Obligation.                       (* ≈-saturation *)
  intros a b Hab Ha; unfold cong_mem in *.
  exact (@cong_trans (grp_deloop G) R HR ttt ttt
           (deloop_arr b) (deloop_arr a) id
           (@cong_incl (grp_deloop G) R HR ttt ttt
              (deloop_arr b) (deloop_arr a) (symmetry Hab)) Ha).
Qed.
Next Obligation.                       (* the unit *)
  unfold cong_mem; apply cong_refl.
Qed.
Next Obligation.                       (* closure under product *)
  intros a b Ha Hb; unfold cong_mem in *.
  exact (@cong_trans (grp_deloop G) R HR ttt ttt
           (deloop_arr (grp_mul G a b)) (id ∘ id) id
           (@cong_comp (grp_deloop G) R HR ttt ttt ttt
              (deloop_arr a) id (deloop_arr b) id Ha Hb)
           (@cong_incl (grp_deloop G) R HR ttt ttt (id ∘ id) id (id_left id))).
Qed.
Next Obligation.                       (* closure under inverse *)
  intros a Ha; unfold cong_mem in *.
  apply cong_sym.
  refine (@cong_trans (grp_deloop G) R HR ttt ttt id
            (deloop_arr (grp_inv G a) ∘ deloop_arr a) _ _ _).
  - exact (@cong_incl (grp_deloop G) R HR ttt ttt id
             (deloop_arr (grp_inv G a) ∘ deloop_arr a)
             (symmetry (grp_mul_inv_l G a))).
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt _
              (deloop_arr (grp_inv G a) ∘ id) _ _ _).
    + exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
               (deloop_arr (grp_inv G a)) (deloop_arr (grp_inv G a))
               (deloop_arr a) id (cong_refl _) Ha).
    + exact (@cong_incl (grp_deloop G) R HR ttt ttt
               (deloop_arr (grp_inv G a) ∘ id) (deloop_arr (grp_inv G a))
               (id_right _)).
Qed.

(** Normality is the fifth field, and it is where the congruence's
    two-sided compatibility with composition is spent: t on the left and
    t⁻¹ on the right. *)
Program Definition cong_ns : NormalSubgroup G := {|
  ns_sub := cong_sub
|}.
Next Obligation.
  intros t a Ha; simpl in *; unfold cong_mem in *.
  refine (@cong_trans (grp_deloop G) R HR ttt ttt _
            ((deloop_arr t ∘ id) ∘ deloop_arr (grp_inv G t)) id _ _).
  - exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
             (deloop_arr t ∘ deloop_arr a) (deloop_arr t ∘ id)
             (deloop_arr (grp_inv G t)) (deloop_arr (grp_inv G t))
             (@cong_comp (grp_deloop G) R HR ttt ttt ttt
                (deloop_arr t) (deloop_arr t) (deloop_arr a) id
                (cong_refl _) Ha)
             (cong_refl _)).
  - apply cong_incl.
    rewrite id_right.
    exact (grp_mul_inv_r G t).
Qed.

End Converse.

(** Membership in the recovered subgroup IS relatedness to the identity,
    by convertibility. *)
Example cong_mem_is_class_of_id {G : GrpObject} (R : HomRelT (grp_deloop G))
  `{HR : @HomCongruence (grp_deloop G) R} (a : carrier G) :
  sub_mem (@cong_ns G R HR) a = R ttt ttt (deloop_arr a) (@id (grp_deloop G) ttt)
  := eq_refl.

(** ** The two maps are mutually inverse *)

(** Normal subgroup, to congruence, and back: [quot_rel_unit_iff] is the
    whole proof, applied.  #313 stated it exactly because the projection's
    kernel had to be pinned down; here it is the round trip. *)
Lemma ns_of_cong_of_ns {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a ↔ sub_mem N a.
Proof. exact (quot_rel_unit_iff N a). Qed.

(** Congruence, to normal subgroup, and back: f ~ g precisely when
    f * g⁻¹ ~ e, since one can multiply through by g and by g⁻¹.  The
    backward direction is one application of compatibility with
    composition followed by one of containment of `≈`; the forward one
    needs a second containment step, to rewrite f as (f * g⁻¹) ∘ g before
    the composition field can be applied. *)
Lemma cong_of_ns_of_cong {G : GrpObject} (R : HomRelT (grp_deloop G))
  `{HR : @HomCongruence (grp_deloop G) R}
  (x y : grp_deloop G) (f g : carrier G) :
  ns_rel (@cong_ns G R HR) x y f g ↔ R x y f g.
Proof.
  destruct x, y; split; intro K.
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt (deloop_arr f)
              (deloop_arr (grp_mul G f (grp_inv G g)) ∘ deloop_arr g)
              (deloop_arr g) _ _).
    + apply cong_incl; simpl.
      rewrite (grp_mul_assoc G f (grp_inv G g) g),
              (grp_mul_inv_l G g), (grp_mul_unit_r G f).
      reflexivity.
    + refine (@cong_trans (grp_deloop G) R HR ttt ttt _
                (id ∘ deloop_arr g) _ _ _).
      * exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
                 (deloop_arr (grp_mul G f (grp_inv G g))) id
                 (deloop_arr g) (deloop_arr g) K (cong_refl _)).
      * apply cong_incl; apply id_left.
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt _
              (deloop_arr g ∘ deloop_arr (grp_inv G g)) id _ _).
    + exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
               (deloop_arr f) (deloop_arr g)
               (deloop_arr (grp_inv G g)) (deloop_arr (grp_inv G g))
               K (cong_refl _)).
    + apply cong_incl; exact (grp_mul_inv_r G g).
Qed.

(** ** The correspondence, packaged as a bijection of setoids

    Neither round trip is an equality of records, and neither could be
    without function extensionality together with extensionality for
    [Type]-valued families ([sub_mem] and [HomRelT] both land in [Type],
    so propositional extensionality would not reach them): a normal
    subgroup
    is a predicate carrying five proofs (four [Subgroup] closure laws and
    [ns_conj]), a congruence a relation carrying four.  The honest
    packaging is therefore a setoid isomorphism, with coextensiveness on
    the left and pointwise mutual implication on the right -- the same
    shape [Construction/Deloop/Transform.v]'s [transform_conjugator_iso]
    takes for its own correspondence, where witnesses are likewise
    compared by what they name rather than as records.  That both sides
    are objects of [Sets] is asserted by [ns_cong_iso]'s type and checked
    by the elaborator; no universe annotation was needed anywhere in this
    section.

    That the membership round trip is NOT definitional is measured, not
    inferred: Test/ProbeGrpCongruence.v, negative 2, with the positive
    control showing what it IS convertible to. *)

Section Packaging.

Context {G : GrpObject}.

(** A congruence, as data: the relation together with its four laws. *)
Definition CongData : Type :=
  { R : HomRelT (grp_deloop G) & HomCongruence R }.

Program Definition NS_Setoid : SetoidObject := {|
  carrier := NormalSubgroup G;
  is_setoid := {| equiv := fun N M =>
    (∀ a : carrier G, sub_mem N a → sub_mem M a)
      * (∀ a : carrier G, sub_mem M a → sub_mem N a) |}
|}.
Next Obligation.
  constructor.
  - intro N; split; intros a Ha; exact Ha.
  - intros N M [H1 H2]; split; assumption.
  - intros N M P [H1 H2] [H3 H4]; split; intros a Ha; auto.
Qed.

Program Definition Cong_Setoid : SetoidObject := {|
  carrier := CongData;
  is_setoid := {| equiv := fun R S =>
    ∀ (x y : grp_deloop G) (f g : x ~> y),
      (`1 R x y f g → `1 S x y f g) * (`1 S x y f g → `1 R x y f g) |}
|}.
Next Obligation.
  constructor.
  - intros R x y f g; split; intro K; exact K.
  - intros R S H x y f g; destruct (H x y f g); split; assumption.
  - intros R S T H1 H2 x y f g.
    destruct (H1 x y f g), (H2 x y f g); split; auto.
Qed.

Program Definition ns_to_cong : NS_Setoid ~{Sets}~> Cong_Setoid := {|
  morphism := fun N => existT _ (ns_rel N) (ns_congruence N)
|}.
Next Obligation.
  intros N M [H1 H2] x y f g; simpl; split; intro K.
  - exact (H1 _ K).
  - exact (H2 _ K).
Qed.

Program Definition cong_to_ns : Cong_Setoid ~{Sets}~> NS_Setoid := {|
  morphism := fun R => @cong_ns G (`1 R) (`2 R)
|}.
Next Obligation.
  intros R S H; simpl; split; intros a Ha.
  - exact (fst (H ttt ttt a (@id (grp_deloop G) ttt)) Ha).
  - exact (snd (H ttt ttt a (@id (grp_deloop G) ttt)) Ha).
Qed.

(** Mac Lane §II.8 Exercise 2, as a bijection: the normal subgroups of G
    are the congruences on its delooping. *)
Program Definition ns_cong_iso : NS_Setoid ≅[Sets] Cong_Setoid := {|
  to := ns_to_cong;
  from := cong_to_ns
|}.
Next Obligation.
  intros R x y f g; simpl.
  destruct x, y.
  exact (@cong_of_ns_of_cong G (`1 R) (`2 R) ttt ttt f g).
Qed.
Next Obligation.
  intros N; simpl; split; intros a Ha.
  - exact (fst (ns_of_cong_of_ns N a) Ha).
  - exact (snd (ns_of_cong_of_ns N a) Ha).
Qed.

End Packaging.

(** The name issue #301's Verification block asks for, supplied as an
    alias so that block resolves.  (Its module path does not: the issue
    suggests [Instance/Group/Congruence.v], and the tree has no
    [Instance/Group/] directory -- [Grp] is the category's name and #313's
    file is [Instance/Grp/Quotient.v], so this file is
    [Instance/Grp/Congruence.v].) *)
Definition congruence_normal_subgroup (G : GrpObject)
  : @NS_Setoid G ≅[Sets] @Cong_Setoid G := @ns_cong_iso G.

(** ** Normality is necessary, not merely sufficient

    #313 has seven [quot_rel] lemmas, and TWO of them apply [ns_conj]:
    [quot_rel_mul] (:316) and [quot_rel_inv] (:338), as that file's own
    comments say (":290-291" calls the first "the first of the two places
    where NORMALITY is spent").  Only the first is consumed by
    [ns_congruence] -- [HomCongruence] has no field about inverses -- and
    the other three fields draw on [quot_rel_of_equiv], [quot_rel_sym] and
    [quot_rel_trans], whose proofs apply [sub_at], [sub_unit],
    [sub_inv] and [sub_mul], and never [ns_conj].  So among the four [HomCongruence] fields it is the
    COMPOSITION field, and only that one, for which normality is at stake.
    That is read off those proofs and offered as a remark rather than as
    an in-tree theorem, since all seven are STATED over a
    [NormalSubgroup] and this file does not restate them.

    What IS proved is the converse, and it is what makes the
    correspondence a correspondence rather than "normal subgroups give
    congruences and we did not look at the others": a subgroup whose
    relation is a congruence is normal.  It is obtained by feeding that
    relation to [cong_ns] and reading its fifth field back, so no second
    normality argument is written. *)

Section Necessity.

Context {G : GrpObject}.
Context (S : Subgroup G).

Definition sub_rel : HomRelT (grp_deloop G) := fun _ _ f g => quot_rel S f g.

(** #313's [quot_rel_unit_iff] is stated over a [NormalSubgroup], though
    its proof consumes only [sub_at], [grp_inv_unit] and [grp_mul_unit_r]
    -- one [Subgroup] field and two group lemmas, none of them [ns_conj].
    Rather than weaken that file's statement, the subgroup-level form is
    stated here, with the same three steps; the normal case is #313's and
    is not re-derived. *)
Lemma sub_rel_unit_iff (a : carrier G) :
  quot_rel S a (grp_unit G) ↔ sub_mem S a.
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at S (a := grp_mul G a (grp_inv G (grp_unit G)))); [| exact K ].
    rewrite (grp_inv_unit G); apply (grp_mul_unit_r G).
  - apply (sub_at S (a := a)); [| exact K ].
    rewrite (grp_inv_unit G); symmetry; apply (grp_mul_unit_r G).
Qed.

Lemma sub_rel_congruence_normal `{HR : @HomCongruence (grp_deloop G) sub_rel} :
  ∀ t a : carrier G, sub_mem S a →
    sub_mem S (grp_mul G (grp_mul G t a) (grp_inv G t)).
Proof.
  intros t a Ha.
  apply (fst (sub_rel_unit_iff _)).
  exact (@ns_conj G (@cong_ns G sub_rel HR) t a
           (snd (sub_rel_unit_iff a) Ha)).
Qed.

End Necessity.

(** Mac Lane §II.8 Exercise 2 in the sharp form: for a subgroup, being a
    congruence and being normal are the same condition.  `↔` is Lib's
    Type-valued [iffT], so the FORWARD leg is congruence ⟹ normality and
    is [sub_rel_congruence_normal]; the BACKWARD leg is normality ⟹
    congruence and is [ns_congruence] read at the normal subgroup built
    from S.  (Consumers project with [fst] for the forward leg --
    [S3_refl_sub_no_congruence] below does.) *)
Theorem congruence_iff_normal {G : GrpObject} (S : Subgroup G) :
  (@HomCongruence (grp_deloop G) (sub_rel S))
    ↔ (∀ t a : carrier G, sub_mem S a →
         sub_mem S (grp_mul G (grp_mul G t a) (grp_inv G t))).
Proof.
  split.
  - intro HR; exact (@sub_rel_congruence_normal G S HR).
  - intro Hn.
    exact (ns_congruence (@Build_NormalSubgroup G S Hn)).
Qed.

(** ** The corollary: quotient of the delooping = delooping of the quotient

    Mac Lane's exercise closes by identifying the quotient category with
    the delooping of the factor group.  Both categories have one object,
    the elements of G as arrows, G's unit as identity and G's
    multiplication as composition -- and those FOUR fields ([obj], [hom],
    [id], [compose]) are the ones that are convertible.  (Counted among
    the TEN a [Category] record literal supplies; the class's [uhom],
    [dom] and [cod] are [:=] definitions derived from those, not data
    either construction chooses.)  The other SIX are built twice:
    [homset] (whose two [Equivalence] witnesses are
    [Quotient_equivalence] and [QuotientGrp]'s own obligation, both
    [Qed]), and with it [compose_respects], [id_left], [id_right],
    [comp_assoc] and [comp_assoc_sym], which [Quotient] assembles from
    [cong_comp]/[cong_incl] and [Deloop] from the monoid's own law fields.
    So the categories are NOT Leibniz-equal -- measured, not assumed
    (Test/ProbeGrpCongruence.v, negative 3).

    THE STRENGTH IS [StrictCat], and that is the strong reading.
    [Instance/Cat.v] gives [Cat] the hom-setoid [Functor_Setoid], which
    identifies naturally isomorphic functors, so [≅[Cat]] in this library
    is an EQUIVALENCE of categories and says strictly less; the [Cat]
    reading below is DERIVED and labelled. *)

Section Corollary.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

Definition quot_to_deloop : deloop_quotient N ⟶ grp_deloop (QuotientGrp N) :=
  Build_Functor (deloop_quotient N) (grp_deloop (QuotientGrp N))
    (fun x => x)
    (fun x y f => f)
    (fun x y f g H => H)
    (fun x => quot_rel_refl N _)
    (fun x y z f g => quot_rel_refl N _).

Definition deloop_to_quot : grp_deloop (QuotientGrp N) ⟶ deloop_quotient N :=
  Build_Functor (grp_deloop (QuotientGrp N)) (deloop_quotient N)
    (fun x => x)
    (fun x y f => f)
    (fun x y f g H => H)
    (fun x => quot_rel_refl N _)
    (fun x y z f g => quot_rel_refl N _).

(** Both functors are the identity on objects and on arrows, so both round
    trips have [eq_refl] object components. *)
Lemma deloop_quotient_round_to :
  @equiv _ (@Functor_StrictEq_Setoid (deloop_quotient N) (deloop_quotient N))
    (deloop_to_quot ◯ quot_to_deloop) (Id[deloop_quotient N]).
Proof.
  exists (fun _ => eq_refl); intros x y f; simpl; apply quot_rel_refl.
Qed.

Lemma deloop_quotient_round_from :
  @equiv _ (@Functor_StrictEq_Setoid (grp_deloop (QuotientGrp N))
              (grp_deloop (QuotientGrp N)))
    (quot_to_deloop ◯ deloop_to_quot) (Id[grp_deloop (QuotientGrp N)]).
Proof.
  exists (fun _ => eq_refl); intros x y f; simpl; apply quot_rel_refl.
Qed.

Definition deloop_quotient_iso
  : deloop_quotient N ≅[StrictCat] grp_deloop (QuotientGrp N) :=
  @Build_Isomorphism StrictCat (deloop_quotient N) (grp_deloop (QuotientGrp N))
    quot_to_deloop deloop_to_quot
    deloop_quotient_round_from deloop_quotient_round_to.

(** The weaker [Cat] reading, derived.  [≅[Cat]] IS equivalence of
    categories here; the [StrictCat] statement above is the strong one. *)
Definition deloop_quotient_Cat_iso
  : deloop_quotient N ≅[Cat] grp_deloop (QuotientGrp N) :=
  @Build_Isomorphism Cat (deloop_quotient N) (grp_deloop (QuotientGrp N))
    quot_to_deloop deloop_to_quot
    (strict_equiv_implies_fun_equiv _ _ deloop_quotient_round_from)
    (strict_equiv_implies_fun_equiv _ _ deloop_quotient_round_to).

End Corollary.

(** ** Group homomorphisms as functors between deloopings *)

Section Homomorphisms.

Context {G K : GrpObject}.

(** A group homomorphism is a monoid homomorphism of the delooped
    monoids: unit and product preservation are its two fields, and
    respectfulness is the underlying setoid morphism's. *)
Definition hom_MonHom (h : G ~{Grp}~> K)
  : MonHom (grp_deloop_monoid G) (grp_deloop_monoid K) :=
  @Build_MonHom (grp_deloop_monoid G) (grp_deloop_monoid K)
    (grp_map h) (proper_morphism (grp_map h))
    (grp_map_unit h) (grp_map_mul h).

(** ...hence a functor, by [Construction/Deloop/Transform.v]'s
    [Deloop_map]; nothing here is new, and the action on arrows is the
    homomorphism's action on elements by convertibility. *)
Definition deloop_hom (h : G ~{Grp}~> K) : grp_deloop G ⟶ grp_deloop K :=
  Deloop_map (hom_MonHom h).

Example deloop_hom_fmap (h : G ~{Grp}~> K) (a : carrier G) :
  @fmap _ _ (deloop_hom h) ttt ttt a = grp_map h a := eq_refl.

End Homomorphisms.

(** ** Awodey §4.2's kernel clause, given its categorical provenance

    #313's [KernelNS] proves directly that the kernel of a group
    homomorphism is a normal subgroup, discharging five obligations; the
    QA correction on #301 homes that clause there and asks for a citation
    here, which this is.  What is added is the REASON, which is
    categorical and costs no group-level obligation at all: the kernel
    congruence of a FUNCTOR is a congruence ([FunctorKernel_Congruence],
    Construction/Quotient.v:559), and [cong_ns] turns any congruence on
    the delooping into a normal subgroup.  Composing the two gives the
    kernel of h as a normal subgroup with no FURTHER argument about
    conjugation: [cong_ns]'s fifth obligation is that argument, made once
    and generically, and nothing kernel-specific is added to it.

    The two normal subgroups are coextensive, not identical: the
    categorical one collects the a with h a ≈ h e, #313's the a with
    h a ≈ e, and [grp_map_unit] is the one step between them (measured:
    Test/ProbeGrpCongruence.v, negative 5). *)

Section Kernel.

Context {G K : GrpObject}.
Context (h : G ~{Grp}~> K).

Definition kernel_cong : HomRelT (grp_deloop G) := FunctorKernel (deloop_hom h).

Definition kernel_ns : NormalSubgroup G :=
  @cong_ns G kernel_cong (FunctorKernel_Congruence (deloop_hom h)).

Lemma kernel_ns_iff (a : carrier G) :
  sub_mem kernel_ns a ↔ sub_mem (KernelNS h) a.
Proof.
  simpl; unfold cong_mem, kernel_cong, FunctorKernel; simpl.
  split; intro K'.
  - rewrite K'; apply (grp_map_unit h).
  - rewrite K'; symmetry; apply (grp_map_unit h).
Qed.

(** Hence the two quotients agree, through #313's own comparison. *)
Definition kernel_quot_congr
  : QuotientGrp kernel_ns ≅[Grp] QuotientGrp (KernelNS h) :=
  quot_congr kernel_ns (KernelNS h)
    (fun a => fst (kernel_ns_iff a)) (fun a => snd (kernel_ns_iff a)).

(** ...and the congruence of #313's kernel relates exactly the arrows the
    functor merges: the kernel congruence of [deloop_hom h] and the
    congruence of [KernelNS h] are the same relation up to logical
    equivalence. *)
Lemma kernel_cong_iff (f g : carrier G) :
  ns_rel (KernelNS h) ttt ttt f g ↔ kernel_cong ttt ttt f g.
Proof.
  unfold kernel_cong, FunctorKernel, ns_rel, quot_rel; simpl.
  split; intro K'.
  - apply (grp_cancel_r K (grp_inv K (grp_map h g))).
    rewrite (grp_mul_inv_r K (grp_map h g)).
    rewrite <- (grp_map_inv h g).
    rewrite <- (grp_map_mul h).
    exact K'.
  - rewrite (grp_map_mul h), (grp_map_inv h), K'.
    apply (grp_mul_inv_r K).
Qed.

End Kernel.

(** ** Awodey §4.5 Exercise 1: the group theorem, specialized from the category one

    [Construction/Quotient.v]'s [QuotientLift] is the categorical
    homomorphism theorem: a functor out of C that merges R-related arrows
    lifts through C/R, the triangle holding at [StrictCat] strength
    ([QuotientLift_factors_strict]) and the lift being unique
    ([QuotientLift_unique]).  Instantiated at the delooping with
    R = [ns_rel N] it produces #313's mediator and #313's uniqueness.  The
    only proof ABOUT N it consumes is [kills_descends] -- the computation
    that a homomorphism killing N cannot tell N-congruent elements apart;
    the rest is the dictionary of [hom_MonHom]/[Deloop_map] and
    [Build_GrpHom']'s [grp_map_unit_from_mul]. *)

Section Specialization.

Context {G K : GrpObject}.
Context (N : NormalSubgroup G).
Context (p : Kills N K).

(** The hypothesis of the categorical theorem, discharged by #313's
    descent lemma with no reshaping. *)
Definition deloop_kills
  : ∀ x y (f g : x ~{grp_deloop G}~> y), ns_rel N x y f g →
      fmap[deloop_hom (`1 p)] f ≈ fmap[deloop_hom (`1 p)] g :=
  fun x y f g H => kills_descends N p f g H.

Definition cat_lift : deloop_quotient N ⟶ grp_deloop K :=
  @QuotientLift (grp_deloop G) (ns_rel N) (ns_congruence N)
    (grp_deloop K) (deloop_hom (`1 p)) deloop_kills.

(** The lift, read back as a homomorphism out of the factor group.  The
    functor is transported along [deloop_to_quot] -- the [StrictCat]
    isomorphism's own leg -- and then read at the single hom-set;
    [Build_GrpHom'] derives unit preservation, and multiplication
    preservation IS [fmap_comp]. *)
Definition cat_med : QuotientGrp N ~{Grp}~> K :=
  @Build_GrpHom' (QuotientGrp N) K
    {| morphism := fun a =>
         @fmap _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt a
     ; proper_morphism :=
         @fmap_respects _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt |}
    (fun a b => @fmap_comp _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt ttt a b).

(** The categorical route lands on #313's mediator: the underlying maps
    are the same term.  The comparison is with [quot_med], which is a
    transparent [Program Definition]; comparing with
    [hom_theorem_factor]'s witness instead would not reduce, that routing
    through the [Qed]-opaque [hom_theorem].  The two [GrpHom] RECORDS are
    not convertible -- their law fields are separately built -- and that
    is pinned as Test/ProbeGrpCongruence.v, negative 4. *)
Example cat_med_is_quot_med (a : carrier (QuotientGrp N)) :
  grp_map cat_med a = grp_map (quot_med N p) a := eq_refl.

(** Awodey §4.5 Exercise 1.  The existence half is [QuotientLift]; the
    uniqueness half is [QuotientLift_unique], applied at the delooping's
    single object.  No group-level uniqueness argument is written. *)
Definition hom_theorem_via_quotient_category
  : ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ `1 p.
Proof.
  unshelve refine {| unique_obj := cat_med |}.
  - intro a; simpl; reflexivity.
  - intros v Hv a.
    exact (symmetry
             (@QuotientLift_unique (grp_deloop G) (ns_rel N) (ns_congruence N)
                (grp_deloop K) (deloop_hom (`1 p)) deloop_kills
                (deloop_hom v ◯ quot_to_deloop N)
                (fun _ => eq_refl)
                (fun x y f => Hv f)
                ttt ttt a)).
Defined.

Example hom_theorem_via_quotient_category_obj (a : carrier (QuotientGrp N)) :
  grp_map (unique_obj hom_theorem_via_quotient_category) a
    = grp_map (quot_med N p) a := eq_refl.

End Specialization.

(** The same statement in [hom_theorem]'s own shape, taking the killing
    hypothesis rather than the packaged [Kills].  #313's biconditional is
    NOT re-proved: only its forward direction is re-obtained, by the
    categorical route. *)
Definition hom_theorem_from_category {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hkill : ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K) :
  ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h :=
  hom_theorem_via_quotient_category N (existT _ h Hkill).

(** ** The projection functor is the delooped projection

    [QuotientProj] and #313's [quot_proj] are the same map: both are the
    identity on the underlying set, only the equivalence coarsening.  The
    arrow actions agree by convertibility; the object actions do NOT, and
    the reason is the one [Construction/Deloop/Transform.v]:282-289
    already records -- [poly_unit] has no definitional eta, so the
    constant function at [ttt] and the identity on a one-element type are
    different terms (Test/ProbeGrpCongruence.v, negative 6). *)

Example deloop_proj_fmap {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  @fmap _ _ (quot_to_deloop N ◯ deloop_quotient_proj N) ttt ttt a
    = @fmap _ _ (deloop_hom (quot_proj N)) ttt ttt a := eq_refl.

Lemma deloop_proj_fobj {G : GrpObject} (N : NormalSubgroup G)
  (x : grp_deloop G) :
  fobj[quot_to_deloop N ◯ deloop_quotient_proj N] x
    = fobj[deloop_hom (quot_proj N)] x.
Proof. destruct x; reflexivity. Qed.

(** ** Non-degeneracy over S3

    Everything above holds for every group and every normal subgroup, so
    nothing yet shows the congruence separates anything or merges
    anything.  #313's witnesses are reused rather than rebuilt: S3
    ([Instance/Grp/TwoFunctors.v]:248, the semidirect presentation over
    the decidable carrier rot * bool, proved nonabelian there), its
    rotation subgroup A3, and the reflection subgroup [S3_refl_sub], which
    #313 proves is a subgroup and is NOT normal.

    NOT [Structure/Groupoid.v]:741's [S3_Grp], although that file is
    imported here and although its S3 is already a
    [Category.Construction.Deloop.GrpObject] and already delooped
    ([deloop_S3_groupoid]).  The tree has exactly THREE presentations of
    the symmetric group: that one, [TwoFunctors.v]:248's semidirect S3 on
    rot * bool, and [Instance/Grp/Epi.v]:1605's [GrpSym3].
    [Instance/Grp/Center.v]:35-39 counts the latter two, both being
    [Instance/Grp.v] groups; [S3_Grp] is over the OTHER record and so
    falls outside that count.  #313's [A3] and [S3_refl_sub] are over
    [TwoFunctors.v]'s S3, so using [S3_Grp] would mean rebuilding both
    subgroups and both of their proofs -- the opposite of reuse. *)

(** The congruence merges: the rotation is related to the identity arrow
    (which is [s3_unit], since [grp_unit S3 = s3_unit] and
    [deloop_id_is_unit] holds by [eq_refl]). *)
Example A3_relates_rotation : ns_rel A3 ttt ttt S3_r s3_unit := eq_refl.

(** ...and separates: the reflection is not. *)
Theorem A3_separates_reflection : ns_rel A3 ttt ttt S3_s s3_unit → False.
Proof. simpl; discriminate. Qed.

(** So the projection functor is not faithful -- which is the whole point
    of a quotient category, and Fong and Spivak's "equations merge, never
    add" read at one object. *)
Theorem A3_proj_not_faithful :
  (∀ (x y : grp_deloop S3) (f g : x ~> y),
     ns_rel A3 x y f g → f ≈ g) → False.
Proof.
  intro Hf.
  pose proof (Hf ttt ttt S3_r s3_unit A3_relates_rotation) as E.
  discriminate E.
Qed.

(** The two orientations of the coset relation genuinely differ once
    normality is dropped, which is what [quot_rel_flip]'s header claims and
    this proves.  With a := s * r and b := r over the non-normal
    [S3_refl_sub]: a * b⁻¹ is the reflection and lies in it (by [eq_refl],
    the carrier being decidable), while b⁻¹ * a is a conjugate of the
    reflection and does not. *)
Definition coset_witness : carrier S3 := grp_mul S3 S3_s S3_r.

Example coset_right : sub_mem S3_refl_sub
  (grp_mul S3 coset_witness (grp_inv S3 S3_r)) := eq_refl.

Theorem coset_orientations_differ :
  sub_mem S3_refl_sub (grp_mul S3 (grp_inv S3 S3_r) coset_witness) → False.
Proof. simpl; discriminate. Qed.

(** And normality is not decoration: the reflection subgroup's relation is
    NOT a congruence on its delooping.  This is [congruence_iff_normal]
    against #313's [S3_refl_sub_not_normal], so the refutation consumes
    the whole class rather than isolating a field; which field the
    normality sits in is the remark in the necessity section above, and it
    is a remark. *)
Theorem S3_refl_sub_no_congruence :
  @HomCongruence (grp_deloop S3) (sub_rel S3_refl_sub) → False.
Proof.
  intro HR.
  exact (S3_refl_sub_not_normal
           (fst (congruence_iff_normal S3_refl_sub) HR)).
Qed.

(** The recovered normal subgroup of A3's congruence has A3's members,
    at the concrete witness: both directions, computed. *)
Example A3_round_forward :
  sub_mem (@cong_ns S3 (ns_rel A3) (ns_congruence A3)) S3_r := eq_refl.

Theorem A3_round_backward :
  sub_mem (@cong_ns S3 (ns_rel A3) (ns_congruence A3)) S3_s → False.
Proof. simpl; discriminate. Qed.
