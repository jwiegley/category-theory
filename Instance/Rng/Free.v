Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** * The free ring on an abelian group, and Mac Lane's §IV.8 Exercise 2:
      the free-ring adjunction as a composite in TWO ways

    nLab:      https://ncatlab.org/nlab/show/tensor+algebra
    nLab:      https://ncatlab.org/nlab/show/free+object
    nLab:      https://ncatlab.org/nlab/show/composition+of+adjoints
    Wikipedia: https://en.wikipedia.org/wiki/Tensor_algebra
    Wikipedia: https://en.wikipedia.org/wiki/Monoid_ring
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          GTM 5, §IV.8, Exercise 2, printed p. 104 -- maclane:IV.8:ex2
    Book: Mac Lane, ibid., §IV.8, Theorem 1 (adjoints compose) --
          the theorem the exercise is an exercise ON

    WHAT THE EXERCISE ASKS.  The free ring on a SET can be reached two
    ways.  Either take the free abelian group on the set and then the free
    ring on that abelian group (the tensor algebra), or take the free
    monoid on the set and then the monoid ring over ℤ.  Each leg is a left
    adjoint, so each composite is a left adjoint by Mac Lane's Theorem 1,
    and since left adjoints of one right adjoint are unique up to natural
    isomorphism, the two composites agree.  The delivered artifacts are
    [free_ring_via_ab], [free_ring_via_mon] and
    [free_ring_composites_agree], the last being a NATURAL ISOMORPHISM of
    the two functors -- [≈] at [Sets ⟶ Rng] IS [Functor_Setoid], i.e. a
    family of isomorphisms together with the coherence square -- and NOT
    an object-level equality, together with the unit statement
    [free_ring_composites_agree_unit].

    THE ISSUE'S "CURRENT STATE" IS BADLY STALE, AND THIS FILE SAYS SO
    RATHER THAN REPEATING IT.  #400 says "none of the three categories
    exists" and "not one of the six functors the exercise needs is
    defined".  That is false: [Grp] (Instance/Grp.v:466), [Ab]
    (Instance/Ab.v:201) and [Rng] (Instance/Rng.v:97, a [Definition]
    aliasing [Ring]) all exist, with [Ab_Forget] (Instance/Ab.v:217),
    [Rng_Forget_Ab] (Instance/Rng.v:112), [Mon_Forget]
    (Theory/Algebra/Monoid/Hom.v:93) and [Rng_Forget_Mon]
    (Instance/Rng/MonoidRing.v:226) among them, and the monoid ring
    exists WITH its adjunction ([MonoidRingFunctor],
    [zmring_adjunction], Instance/Rng/MonoidRing.v:723,:726).  The
    issue's own QA correction supersedes its work items 1-2 ("consume the
    free monoid, do not rebuild"), and that instruction was blocked by a
    CATEGORY MISMATCH: the in-tree free monoid of Instance/Coq/Monoid/Free.v
    is at [MonCoq := @Mon Coq Coq_Monoidal] (:126, :323) while the monoid
    ring's right adjoint lands in [@Mon Sets Sets_Product_Monoidal], and
    no bridge between the two exists.  Instance/Mon/Free.v was written for
    this issue precisely to close that gap, and Instance/Ab/Free.v
    supplies the other leg; NEITHER is rebuilt here, both are consumed by
    name.

    WHAT IS GENUINELY NEW HERE is therefore exactly one construction --
    [FreeRngAbObject], [FreeRngAb : Ab ⟶ Rng] and
    [free_rng_ab_adjunction : FreeRngAb ⊣ Rng_Forget_Ab] -- plus the two
    composites and their comparison.

    WHY GENERATORS AND RELATIONS, NOT ⊕ₙ A^⊗ⁿ.  The classical carrier of
    the tensor algebra is the direct sum of the tensor powers, and that
    presentation is unavailable in tree: it needs countable direct sums of
    abelian groups, i.e. [HasIndexedCoproducts Ab], which is not built --
    Instance/Ab/Coproduct.v:106 says so in terms, and the only instances of
    that class anywhere are at [Sets] and at [Cat].  The carrier here is
    instead an inductive of formal ring expressions [FRTerm] with an
    inductive congruence [fr_eq], following Instance/Rng/MonoidRing.v,
    Instance/Vect/TensorAlgebra.v, Instance/Rng/Polynomial.v and
    Instance/Ab/Tensor.v.  The design is copied and the debt is
    acknowledged; no code is shared with any of them.

    THE PRESENTATION CARRIES NO REDUNDANCY, AND THAT IS MEASURED.
    [fr_eq] has SEVENTEEN constructors: four congruence clauses (one per
    former, the generator clause saturating under A's own [≈]), the four
    abelian-group laws, the three multiplicative-monoid laws, the two
    distributive laws, the two clauses making the insertion of A a
    homomorphism of abelian groups, and symmetry and transitivity.
    Reflexivity is DERIVED ([fr_refl]), keeping the induction principle
    one case shorter everywhere it is consumed.  [RigObject] has twelve
    law fields and only TEN of them are constructors: the two annihilation
    clauses [rig_mul_zero_l] and [rig_mul_zero_r] are THEOREMS
    ([fr_mul_zero_l], [fr_mul_zero_r]), derived from distributivity and
    additive inverses through the one-line [fr_idem_zero].  So the record
    is not a zero-obligation literal, unlike Instance/Ab/Free.v's; two
    fields are paid for, deliberately, to keep the generating set
    irredundant.

    STRENGTHS, MEASURED STRICT-FIRST.  The mediator is a [Fixpoint] on
    formal expressions, so a great deal is definitional:

      - [eq_refl]: the carrier of the free ring seen through
        [Ab_Forget ◯ Rng_Forget_Ab] IS [FRTerm] and its [≈] IS [fr_eq]
        ([free_rng_ab_carrier_is_FRTerm], [free_rng_ab_equiv_is_fr_eq]);
        the insertion IS the generator former
        ([free_rng_ab_insert_is_gen]); the extension agrees with the given
        homomorphism on generators and preserves 0, 1, +, · AND negation
        definitionally ([free_rng_ab_extend_generators] and the five
        siblings, recorded at Leibniz [=] on the TARGET's carrier -- the
        convertibility exception the house style sanctions -- so the claim
        is machine-checked rather than inferred from which branch of the
        obligation tactic fired); the free functor's object part
        ([FreeRngAb_obj]); the universal arrow IS the insertion
        ([free_rng_ab_arrow_is_insert]); the UNIT is the insertion and
        hence the one-generator expression ([free_rng_ab_unit_is_insert]);
        both composites' object actions ([free_ring_via_ab_obj],
        [free_ring_via_mon_obj]); the abelian route's transpose is the
        pasted transpose ([free_ring_via_ab_transpose]); the retyping of
        the monoid route is inert on transpose and unit
        ([retype_adj_agrees], [retype_unit_agrees]); and the two
        underlying-set functors agree on objects AND on arrows
        ([rng_underlying_fobj_agree], [rng_underlying_fmap_agree]).
      - [≈] only, with the cause DIAGNOSED and DISCRIMINATED: the COUNIT.
        It is [unique_obj (ump_universal_arrows …)] and
        [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed]-opaque,
        so nothing reduces through it; [free_rng_ab_counit_evaluates] is
        what does hold.  The blame is on that one constant and not on the
        route, and the discriminating control is in the same file: the
        UNIT comes out of the SAME [AdjunctionFromUniversalArrows] and
        DOES reduce ([free_rng_ab_unit_is_insert], [eq_refl]).  Both are
        pinned -- the negative as [rng_counit_computes].
      - [≈] only: the action of [FreeRngAb] on an arrow.
        [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by
        universal factorization rather than by a formula, so
        [free_rng_ab_fmap_generators] is a theorem; the strict form is
        pinned as [rng_fmap_generator_computes].

    THE TWO RIGHT ADJOINTS, AND WHY NO TRANSPORT LEMMA WAS NEEDED.  Write
    [RngUnderlyingAb := Ab_Forget ◯ Rng_Forget_Ab] and
    [RngUnderlyingMon := Mon_Forget ◯ Rng_Forget_Mon], both [Rng ⟶ Sets].
    Four facts, measured:

      (i)   [fobj[RngUnderlyingAb] R = fobj[RngUnderlyingMon] R] by
            [eq_refl];
      (ii)  [fmap[RngUnderlyingAb] f = fmap[RngUnderlyingMon] f] by
            [eq_refl];
      (iii) [RngUnderlyingAb = RngUnderlyingMon] is REFUTED at [eq_refl] --
            [Functor] has primitive projections with eta, so record
            equality is field equality, and the three LAW fields are
            [Compose]'s obligations at different arguments;
      (iv)  consequently the composed monoid-route adjunction cannot be
            ASCRIBED against [RngUnderlyingAb] ([rng_mon_route_ascribed],
            refuted), the [Adjunction] type mentioning the whole functor
            record.

    From (iv) one expects to need a lemma transporting an adjunction along
    a natural isomorphism of its right adjoint.  NONE IS NEEDED, and that
    is the file's cheapest finding: every one of [Adjunction]'s five
    fields mentions the right adjoint ONLY through [U y] (an object) and
    [fmap[U] f] (a morphism), and by (i) and (ii) those are definitionally
    equal, so the five field TYPES are convertible even though the two
    functor records are not.  [free_ring_via_mon_adjunction_ab] is
    therefore literal field copying through [@Build_Adjunction], with no
    tactic, no isomorphism and no coherence obligation -- and
    [retype_adj_agrees] and [retype_unit_agrees] record by [eq_refl] that
    the operation is inert.

    THE COMPARISON IS BUILT TRANSPARENTLY, AND GENERALLY.  Section
    [LeftAdjointComparison] proves, for ANY two left adjoints of one right
    adjoint, that [⌈η'⌉] and [⌈η⌉] are mutually inverse and natural, so
    [left_adjoints_agree] inhabits [F ≈ F'] with NAMED components, and it
    is [Defined], so [free_ring_comparison_is_agree_component] records by
    [eq_refl] that [free_ring_comparison] IS the component of
    [free_ring_composites_agree] -- not merely an isomorphism with the
    same endpoints.  Theory/Adjunction.v's [left_adjoint_iso] (:407)
    proves the same TYPE -- [free_ring_composites_agree_via_left_adjoint_iso]
    feeds it the same two adjunctions, so that much is machine-checked --
    but it is [Qed], so no component of it reduces and none can be named,
    which is why the transparent version exists:
    [free_ring_composites_agree_unit] is a statement ABOUT
    [free_ring_comparison], and could not have been tied to an opaque
    isomorphism at all.  The two terms are NOT identified, and no such
    identification is claimed.  Two small general lemmas were needed on
    the way and are stated here rather than upstream: [to_adj_injective],
    and
    [unit_natural] -- naturality of the unit along an ARBITRARY morphism
    of D, which Theory/Adjunction.v:241's [unit_comp] does not give, that
    one stating naturality only along a morphism [x ~> U y].

    UNIVERSES: THE TWO ROUTES DO NOT HAVE THE SAME REACH, AND THE
    ASYMMETRY IS THE DONOR'S.  Read off the constraint blocks:
    [RngUnderlyingAb@{u u0} : Functor@{u u0 u0 u u0 u0}] leaves the
    carrier universe [u0] FREE (only [u0 < u], which is [Ab]'s own
    stratification), and so do [FreeRngAb], [free_rng_ab_adjunction] and
    [free_ring_via_ab].  The monoid route does not:
    [RngUnderlyingMon] and [free_ring_via_mon] are
    [Functor@{u Set Set u Set Set}] -- hom and proof universes pinned at
    [Set].  The pin is located exactly and is NOT this file's:
    [Rig_Forget_Mon] (Theory/Algebra/Rig.v:292) has source [Rig@{u Set}],
    and [Rng_Forget_Mon] is [Rig_Forget_Mon ◯ Ring_Forget_Rig].  Both are
    rejected under a declared [Constraint Set < uh] while [Rng_Forget_Ab]
    and [Rig_Forget_CMon] elaborate there.  Read that guard precisely:
    the negatives fire on the donor's literal [Set] meeting a RIGID
    declared level -- deleting the [Constraint] leaves them failing with
    the identical message, so it is INERT for them -- and what it buys is
    the positive controls' "strictly above [Set]".  The attribution is
    guarded
    and not merely asserted.  CONSEQUENCE, stated plainly: since the
    comparison needs both routes at ONE [Rng],
    [free_ring_composites_agree] instantiates the abelian route at [Set]
    and inherits the pin, so the EXERCISE is a statement about rings whose
    carriers live in [Set] even though the abelian half of it is not.  The
    pin is not repaired here and is NOT claimed unavoidable.

    NON-DEGENERACY, PROVED RATHER THAN GESTURED AT.  No induction over
    [fr_eq] can yield a negative -- every constructor concludes an
    equation -- so each refutation maps OUT into a concrete ring.  In
    general: no generator is the unit and 0 is not 1
    ([free_rng_ab_gen_not_one], [free_rng_ab_zero_not_one]), for EVERY
    abelian group, by the constant-zero probe into any ring with 1 ≉ 0.
    Concretely over ℤ: the insertion is INJECTIVE
    ([int_free_rng_gen_injective]), so ℤ genuinely embeds.  And the free
    ring on the free abelian group of rank two is NOT COMMUTATIVE
    ([free_rng_ab_not_commutative]), by mapping the two generators to the
    non-commuting matrix units of [UT2]
    (Instance/Rng/Algebras/Associative.v, the FIRST closed
    non-commutative [RingObject] in tree; [Lam2],
    Instance/Vect/TensorAlgebra.v:1240, is a second, so "only" would be
    false); both products COMPUTE, so the
    separation is [discriminate] on closed data.  That witness is not
    beside the exercise: [rng_two_gens_is_via_ab] records by [eq_refl]
    that the ring probed IS [free_ring_via_ab AbTwoGens].  Finally
    [rng_routes_convertible] is refuted, so the two composites are
    not convertible, so the isomorphism is not between a thing
    and itself.

    MEASURED BOUNDARIES.  Seven [Fail]s of TWO KINDS, kept lexically
    apart: five CONVERSION (the two functor records, the ascription, the
    two routes' objects, the counit, the arrow action) and two FORMABILITY
    (the [Set] pin, at each of [Rng_Forget_Mon] and [Rig_Forget_Mon]),
    plus a separate instrument check.  Each was stripped once and its
    failure kind read off the message.  Every constant named in a [Fail]
    is also named in a command that must SUCCEED -- four positive [Check]s
    were added for exactly that reason -- so a rename breaks this file
    instead of turning a negative vacuously green.

    118/118 constants closed under the global context, the count taken
    over the source declarations and the constructors UNION what
    [Print Module] lists (which adds the eliminators and the six [Program]
    obligations, ALL SIX of which are reachable only by fully qualified
    name).

    NOT DELIVERED, scoped:
      - no normal form for [fr_eq], hence no coefficient uniqueness, no
        decision procedure and no basis; nothing is claimed about when two
        formal expressions are equal beyond what the probes above settle;
      - no grading and no identification of [FreeRngAbObject A] with
        ⊕ₙ A^⊗ⁿ, and no comparison with Instance/Vect/TensorAlgebra.v's
        [TensorAlg] (that one is the tensor algebra of a MODULE over a
        base ring, built on a different generating structure; no map
        either way is built and none is claimed);
      - no commutative variant, so no free commutative ring and no
        relation to Instance/Rng/Polynomial.v's ℤ[x] -- in particular it
        is NOT claimed that [FreeRngAbObject ab_int] is ℤ[x];
      - the comparison is between the two COMPOSITES only: no comparison
        of [FreeRngAb ◯ FreeAb] with [MonoidRingFunctor] leg by leg, and
        no claim that either intermediate category is determined;
      - no [Set]-pin repair for [Rig_Forget_Mon], and no restatement of
        the monoid route at a free carrier universe;
      - no counit-level companion to [free_ring_composites_agree_unit];
      - [to_adj_injective] and [unit_natural] are stated here and NOT
        upstreamed to Theory/Adjunction.v. *)

#[local] Obligation Tactic := idtac.

(** ** Formal ring expressions over an abelian group *)

Section FreeRingOnAb.

Context (A : AbObject).

Inductive FRTerm : Type :=
  | fr_gen  : carrier (cmon_setoid A) → FRTerm
  | fr_zero : FRTerm
  | fr_one  : FRTerm
  | fr_plus : FRTerm → FRTerm → FRTerm
  | fr_neg  : FRTerm → FRTerm
  | fr_mul  : FRTerm → FRTerm → FRTerm.

Inductive fr_eq : FRTerm → FRTerm → Type :=
  (* congruence for each former, saturating under A's own [≈] *)
  | fre_gen {a b : carrier (cmon_setoid A)} :
      a ≈ b → fr_eq (fr_gen a) (fr_gen b)
  | fre_plus {s s' t t'} :
      fr_eq s s' → fr_eq t t' → fr_eq (fr_plus s t) (fr_plus s' t')
  | fre_neg {s s'} : fr_eq s s' → fr_eq (fr_neg s) (fr_neg s')
  | fre_mul {s s' t t'} :
      fr_eq s s' → fr_eq t t' → fr_eq (fr_mul s t) (fr_mul s' t')

  (* (0, +, -) is an abelian group *)
  | fre_add_assoc (s t u : FRTerm) :
      fr_eq (fr_plus (fr_plus s t) u) (fr_plus s (fr_plus t u))
  | fre_add_comm (s t : FRTerm) : fr_eq (fr_plus s t) (fr_plus t s)
  | fre_add_zero_l (s : FRTerm) : fr_eq (fr_plus fr_zero s) s
  | fre_neg_l (s : FRTerm) : fr_eq (fr_plus (fr_neg s) s) fr_zero

  (* (1, ·) is a monoid -- NOT assumed commutative *)
  | fre_mul_assoc (s t u : FRTerm) :
      fr_eq (fr_mul (fr_mul s t) u) (fr_mul s (fr_mul t u))
  | fre_mul_one_l (s : FRTerm) : fr_eq (fr_mul fr_one s) s
  | fre_mul_one_r (s : FRTerm) : fr_eq (fr_mul s fr_one) s

  (* · distributes over + on both sides *)
  | fre_distr_l (s t u : FRTerm) :
      fr_eq (fr_mul s (fr_plus t u)) (fr_plus (fr_mul s t) (fr_mul s u))
  | fre_distr_r (s t u : FRTerm) :
      fr_eq (fr_mul (fr_plus s t) u) (fr_plus (fr_mul s u) (fr_mul t u))

  (* the insertion of A is a homomorphism of abelian groups *)
  | fre_gen_zero : fr_eq (fr_gen (cmon_zero A)) fr_zero
  | fre_gen_plus (a b : carrier (cmon_setoid A)) :
      fr_eq (fr_gen (cmon_plus A a b)) (fr_plus (fr_gen a) (fr_gen b))

  | fre_sym {s t} : fr_eq s t → fr_eq t s
  | fre_trans {s t u} : fr_eq s t → fr_eq t u → fr_eq s u.

Lemma fr_refl (s : FRTerm) : fr_eq s s.
Proof.
  induction s.
  - exact (fre_gen (reflexivity _)).
  - exact (fre_trans (fre_sym (fre_add_zero_l fr_zero))
                     (fre_add_zero_l fr_zero)).
  - exact (fre_trans (fre_sym (fre_mul_one_l fr_one))
                     (fre_mul_one_l fr_one)).
  - exact (fre_plus IHs1 IHs2).
  - exact (fre_neg IHs).
  - exact (fre_mul IHs1 IHs2).
Qed.

Lemma fr_eq_Equivalence : Equivalence fr_eq.
Proof.
  constructor.
  - exact fr_refl.
  - exact (fun s t => fre_sym).
  - exact (fun s t u => fre_trans).
Qed.

Definition fr_Setoid : Setoid FRTerm := {|
  equiv        := fr_eq;
  setoid_equiv := fr_eq_Equivalence
|}.

(** ** The two annihilation clauses are THEOREMS, not constructors

    [RigObject] has twelve law fields; seventeen constructors above meet
    ten of them.  The remaining two -- [rig_mul_zero_l] and
    [rig_mul_zero_r] -- are derivable in the presence of additive
    inverses, so they are NOT among the constructors and the presentation
    is by a generating set that carries no redundancy.  The derivation is
    the usual one: an element equal to its own double is zero. *)

Lemma fr_idem_zero (s : FRTerm) :
  fr_eq s (fr_plus s s) → fr_eq s fr_zero.
Proof.
  intro H.
  refine (fre_sym _).
  refine (fre_trans (fre_sym (fre_neg_l s)) _).
  refine (fre_trans (fre_plus (fr_refl (fr_neg s)) H) _).
  refine (fre_trans (fre_sym (fre_add_assoc (fr_neg s) s s)) _).
  refine (fre_trans (fre_plus (fre_neg_l s) (fr_refl s)) _).
  exact (fre_add_zero_l s).
Qed.

Lemma fr_mul_zero_l (s : FRTerm) : fr_eq (fr_mul fr_zero s) fr_zero.
Proof.
  apply fr_idem_zero.
  refine (fre_trans _ (fre_distr_r fr_zero fr_zero s)).
  exact (fre_sym (fre_mul (fre_add_zero_l fr_zero) (fr_refl s))).
Qed.

Lemma fr_mul_zero_r (s : FRTerm) : fr_eq (fr_mul s fr_zero) fr_zero.
Proof.
  apply fr_idem_zero.
  refine (fre_trans _ (fre_distr_l s fr_zero fr_zero)).
  exact (fre_sym (fre_mul (fr_refl s) (fre_add_zero_l fr_zero))).
Qed.

(** ** The free ring on the abelian group A *)

Definition FreeRngAbObject : RingObject := {|
  ring_rig := {|
    rig_setoid := {| carrier := FRTerm; is_setoid := fr_Setoid |};
    rig_zero := fr_zero;
    rig_add := fr_plus;
    rig_one := fr_one;
    rig_mul := fr_mul;
    rig_add_respects := fun _ _ Hs _ _ Ht => fre_plus Hs Ht;
    rig_mul_respects := fun _ _ Hs _ _ Ht => fre_mul Hs Ht;
    rig_add_assoc := fre_add_assoc;
    rig_add_comm := fre_add_comm;
    rig_add_zero_l := fre_add_zero_l;
    rig_mul_assoc := fre_mul_assoc;
    rig_mul_one_l := fre_mul_one_l;
    rig_mul_one_r := fre_mul_one_r;
    rig_distr_l := fre_distr_l;
    rig_distr_r := fre_distr_r;
    rig_mul_zero_l := fr_mul_zero_l;
    rig_mul_zero_r := fr_mul_zero_r
  |};
  ring_neg := fr_neg;
  ring_neg_respects := fun _ _ Hs => fre_neg Hs;
  ring_neg_l := fre_neg_l
|}.

(* The carrier of the free ring, seen through BOTH forgetful routes, IS
   the type of formal ring expressions, and its [≈] IS the quotienting
   relation.  These are equations between TYPES -- the convertibility
   exception the house style sanctions. *)
Example free_rng_ab_carrier_is_FRTerm :
  carrier (Ab_Forget (Rng_Forget_Ab FreeRngAbObject)) = FRTerm := eq_refl.

(* The corresponding reading through the MONOID route is deliberately NOT
   stated here.  [Rng_Forget_Mon] is instantiable only at
   [RingObject@{Set Set _}] (the pin is [Rig_Forget_Mon]'s,
   Theory/Algebra/Rig.v:292), and a section variable's universes are fixed
   by everything stated in the section, so writing that Example here would
   confine the WHOLE free-ring construction to [Set]-sized abelian groups.
   It is stated instead in the §IV.8 section below, where the monoid route
   already carries the pin. *)

Example free_rng_ab_equiv_is_fr_eq (s t : FRTerm) :
  (@equiv _ (is_setoid (rig_setoid FreeRngAbObject)) s t) = fr_eq s t
  := eq_refl.

(** ** The insertion of the abelian group

    A group element becomes the corresponding generator.  This is a
    morphism of [Ab], not merely of [Sets]: [fre_gen_zero] and
    [fre_gen_plus] are exactly the two [CMonHom] laws, so the insertion
    costs no proof at all. *)

Definition free_rng_ab_insert : A ~{Ab}~> Rng_Forget_Ab FreeRngAbObject.
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := fr_gen |}.
    intros a b H; exact (fre_gen H).
  - exact fre_gen_zero.
  - exact fre_gen_plus.
Defined.

Example free_rng_ab_insert_is_gen (a : carrier (cmon_setoid A)) :
  cmon_map free_rng_ab_insert a = fr_gen a := eq_refl.

(** ** The ring extension of a homomorphism on generators *)

Section Extension.

Context (R : RingObject).
Context (h : A ~{Ab}~> Rng_Forget_Ab R).

Fixpoint fr_eval (t : FRTerm) : carrier (rig_setoid R) :=
  match t with
  | fr_gen a    => cmon_map h a
  | fr_zero     => rig_zero R
  | fr_one      => rig_one R
  | fr_plus s t => rig_add R (fr_eval s) (fr_eval t)
  | fr_neg s    => ring_neg R (fr_eval s)
  | fr_mul s t  => rig_mul R (fr_eval s) (fr_eval t)
  end.

(* One induction over the relation: seventeen cases, one per constructor.
   Ten are met by the corresponding law of the target ring; four are
   congruence for a former; TWO are the two [CMonHom] laws of [h] -- which
   is the only place the hypothesis that [h] is a group homomorphism
   rather than a bare function is spent -- and the last two are the target
   setoid's symmetry and transitivity. *)
Lemma fr_eval_respects (s t : FRTerm) : fr_eq s t → fr_eval s ≈ fr_eval t.
Proof.
  intro He.
  induction He as
    [ a b Hab
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' t t' _ IHs _ IHt
    | s t u | s t | s | s
    | s t u | s | s
    | s t u | s t u
    | | a b
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - exact (proper_morphism (cmon_map h) _ _ Hab).
  - exact (rig_add_respects R _ _ IHs _ _ IHt).
  - exact (ring_neg_respects R _ _ IHs).
  - exact (rig_mul_respects R _ _ IHs _ _ IHt).
  - exact (rig_add_assoc R _ _ _).
  - exact (rig_add_comm R _ _).
  - exact (rig_add_zero_l R _).
  - exact (ring_neg_l R _).
  - exact (rig_mul_assoc R _ _ _).
  - exact (rig_mul_one_l R _).
  - exact (rig_mul_one_r R _).
  - exact (rig_distr_l R _ _ _).
  - exact (rig_distr_r R _ _ _).
  - exact (cmon_map_zero h).
  - exact (cmon_map_plus h a b).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(* The extension, as a morphism of [Rng].  Five obligations:
   respectfulness of the fold, and preservation of 0, +, 1 and ·.
   Preservation of NEGATION is not among them -- in [Rng] it is the
   derived [RigHom_neg] rather than a field -- yet it holds for THIS
   homomorphism definitionally all the same, the fixpoint having a clause
   for [fr_neg].  The last four obligations are [reflexivity], the
   fixpoint's clauses BEING those four equations.  One uniform body is
   used so the proof does not depend on the order [Program] emits the
   obligations in. *)
Program Definition free_rng_ab_extend : FreeRngAbObject ~{Rng}~> R := {|
  rig_map := {| morphism := fr_eval |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

Example free_rng_ab_extend_generators (a : carrier (cmon_setoid A)) :
  rig_map free_rng_ab_extend (fr_gen a) = cmon_map h a := eq_refl.

Example free_rng_ab_extend_zero :
  rig_map free_rng_ab_extend fr_zero = rig_zero R := eq_refl.

Example free_rng_ab_extend_one :
  rig_map free_rng_ab_extend fr_one = rig_one R := eq_refl.

Example free_rng_ab_extend_plus (s t : FRTerm) :
  rig_map free_rng_ab_extend (fr_plus s t)
    = rig_add R (rig_map free_rng_ab_extend s)
                (rig_map free_rng_ab_extend t) := eq_refl.

Example free_rng_ab_extend_mul (s t : FRTerm) :
  rig_map free_rng_ab_extend (fr_mul s t)
    = rig_mul R (rig_map free_rng_ab_extend s)
                (rig_map free_rng_ab_extend t) := eq_refl.

Example free_rng_ab_extend_neg (s : FRTerm) :
  rig_map free_rng_ab_extend (fr_neg s)
    = ring_neg R (rig_map free_rng_ab_extend s) := eq_refl.

(** *** Uniqueness

    Any ring homomorphism out of the free ring agreeing with [h] on the
    generators IS the extension.  Six cases, one per former: the generator
    case is the agreement hypothesis, four are homomorphism laws of the
    competitor, and the [fr_neg] case is [RigHom_neg] -- a THEOREM of
    Theory/Algebra/Rig.v rather than a field, which is exactly the place
    that derivation earns its keep, mirroring [ab_map_neg]'s role in
    Instance/Ab/Free.v. *)
Lemma free_rng_ab_extend_unique (g : FreeRngAbObject ~{Rng}~> R)
  (Hg : ∀ a : carrier (cmon_setoid A),
          rig_map g (fr_gen a) ≈ cmon_map h a) (t : FRTerm) :
  rig_map g t ≈ fr_eval t.
Proof.
  induction t as [ a | | | t1 IHt1 t2 IHt2 | t IHt | t1 IHt1 t2 IHt2 ];
    simpl.
  - exact (Hg a).
  - exact (rig_map_zero g).
  - exact (rig_map_one g).
  - refine (transitivity (rig_map_add g t1 t2) _).
    exact (rig_add_respects R _ _ IHt1 _ _ IHt2).
  - refine (transitivity (RigHom_neg FreeRngAbObject R g t) _).
    exact (ring_neg_respects R _ _ IHt).
  - refine (transitivity (rig_map_mul g t1 t2) _).
    exact (rig_mul_respects R _ _ IHt1 _ _ IHt2).
Qed.

End Extension.

Arguments fr_eval {R} h t.
Arguments free_rng_ab_extend {R} h.

(** ** The universal property, in the shape [universal_arrow_from_UMP]
       consumes *)
Theorem free_rng_ab_universal :
  ∀ (R : RingObject) (h : A ~{Ab}~> Rng_Forget_Ab R),
    ∃! g : FreeRngAbObject ~{Rng}~> R,
      h ≈ fmap[Rng_Forget_Ab] g ∘ free_rng_ab_insert.
Proof.
  intros R h.
  unshelve eexists.
  - exact (free_rng_ab_extend h).
  - intro a; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_rng_ab_extend_unique R h g).
    intro a; symmetry; exact (Hg a).
Qed.

End FreeRingOnAb.

Arguments fr_gen {A} a.
Arguments fr_zero {A}.
Arguments fr_one {A}.
Arguments fr_plus {A} s t.
Arguments fr_neg {A} s.
Arguments fr_mul {A} s t.
Arguments fr_eq {A} s t.
Arguments fr_refl {A} s.
Arguments fre_gen {A a b} _.
Arguments fre_plus {A s s' t t'} _ _.
Arguments fre_neg {A s s'} _.
Arguments fre_mul {A s s' t t'} _ _.
Arguments fre_add_assoc {A} s t u.
Arguments fre_add_comm {A} s t.
Arguments fre_add_zero_l {A} s.
Arguments fre_neg_l {A} s.
Arguments fre_mul_assoc {A} s t u.
Arguments fre_mul_one_l {A} s.
Arguments fre_mul_one_r {A} s.
Arguments fre_distr_l {A} s t u.
Arguments fre_distr_r {A} s t u.
Arguments fre_gen_zero {A}.
Arguments fre_gen_plus {A} a b.
Arguments fre_sym {A s t} _.
Arguments fre_trans {A s t u} _ _.
Arguments fr_eval {A R} h t.
Arguments free_rng_ab_extend {A R} h.
Arguments fr_eval_respects {A} R h s t _.
Arguments free_rng_ab_extend_unique {A} R h g _ t.

(** ** The universal arrow, the free functor and the adjunction *)

Definition free_rng_ab_universal_arrow (A : Ab)
  : UniversalArrow A Rng_Forget_Ab :=
  universal_arrow_from_UMP A Rng_Forget_Ab (FreeRngAbObject A)
    (free_rng_ab_insert A) (free_rng_ab_universal A).

Program Definition free_rng_ab_AUniversalArrow (A : Ab)
  : AUniversalArrow A Rng_Forget_Ab (FreeRngAbObject A) := {|
  universal_arrow := free_rng_ab_insert A
|}.
Next Obligation.
  intros A R h.
  unshelve eexists.
  - exact (free_rng_ab_extend h).
  - intro a; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_rng_ab_extend_unique R h g).
    intro a; exact (Hg a).
Qed.

Definition FreeRngAb : Ab ⟶ Rng :=
  LeftAdjointFunctorFromUniversalArrows Rng_Forget_Ab
    free_rng_ab_universal_arrow.

Definition free_rng_ab_adjunction : FreeRngAb ⊣ Rng_Forget_Ab :=
  AdjunctionFromUniversalArrows Rng_Forget_Ab free_rng_ab_universal_arrow.

Example FreeRngAb_obj (A : Ab) : FreeRngAb A = FreeRngAbObject A := eq_refl.

Example free_rng_ab_arrow_is_insert (A : Ab) :
  @arrow _ _ A Rng_Forget_Ab (free_rng_ab_universal_arrow A)
    = free_rng_ab_insert A := eq_refl.

Definition free_rng_ab_unit (A : Ab)
  : A ~{Ab}~> Rng_Forget_Ab (FreeRngAb A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A.

Example free_rng_ab_unit_is_insert (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (free_rng_ab_unit A) a = fr_gen a := eq_refl.

Definition free_rng_ab_counit (R : Rng)
  : FreeRngAb (Rng_Forget_Ab R) ~{Rng}~> R :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_rng_ab_adjunction R.

Lemma free_rng_ab_counit_generator (R : Rng)
  (a : carrier (rig_setoid R)) :
  rig_map (free_rng_ab_counit R) (@fr_gen (Rng_Forget_Ab R) a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_rng_ab_adjunction R a).
Qed.

Theorem free_rng_ab_counit_evaluates (R : Rng)
  (t : FRTerm (Rng_Forget_Ab R)) :
  rig_map (free_rng_ab_counit R) t
    ≈ fr_eval (@id Ab (Rng_Forget_Ab R)) t.
Proof.
  apply (free_rng_ab_extend_unique R (@id Ab (Rng_Forget_Ab R))
           (free_rng_ab_counit R)).
  intro a; exact (free_rng_ab_counit_generator R a).
Qed.

Lemma free_rng_ab_fmap_generators {A B : Ab} (u : A ~{Ab}~> B)
  (a : carrier (cmon_setoid A)) :
  rig_map (fmap[FreeRngAb] u) (fr_gen a) ≈ fr_gen (cmon_map u a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_rng_ab_universal_arrow A)
              (@arrow _ _ B Rng_Forget_Ab
                 (free_rng_ab_universal_arrow B) ∘ u)) a).
Qed.

(** * Two left adjoints of one right adjoint

    A general comparison, built transparently so that its components are
    available to the unit statement below.  Theory/Adjunction.v's
    [left_adjoint_iso] proves the same [F ≈ F'] but is [Qed], so nothing
    reduces through it and no component of it can be named. *)

Section LeftAdjointComparison.

Context {C D : Category}.
Context {U : C ⟶ D}.

(* The forward transpose of an adjunction is injective, being one leg of
   an isomorphism of hom-setoids. *)
Lemma to_adj_injective {F : D ⟶ C} (AF : F ⊣ U) {x : D} {y : C}
  (f g : F x ~> y) :
  to (@adj _ _ _ _ AF x y) f ≈ to (@adj _ _ _ _ AF x y) g → f ≈ g.
Proof.
  intro H.
  refine (transitivity
            (symmetry (@to_adj_comp_law _ _ _ _ AF x y f)) _).
  refine (transitivity _ (@to_adj_comp_law _ _ _ _ AF x y g)).
  exact (@from_adj_respects _ _ _ _ AF x y _ _ H).
Qed.

(* Naturality of the unit along an ARBITRARY morphism of D.  The in-tree
   [unit_comp] (Theory/Adjunction.v:241) states naturality only along a
   morphism [x ~> U y], which is a different statement. *)
Lemma unit_natural {F : D ⟶ C} (AF : F ⊣ U) {x y : D} (u : x ~> y) :
  @Category.Theory.Adjunction.unit _ _ _ _ AF y ∘ u
    ≈ fmap[U] (fmap[F] u)
        ∘ @Category.Theory.Adjunction.unit _ _ _ _ AF x.
Proof.
  unfold Category.Theory.Adjunction.unit.
  rewrite <- (@to_adj_nat_l _ _ _ _ AF x y (F y) id u).
  rewrite <- (@to_adj_nat_r _ _ _ _ AF x (F x) (F y) (fmap[F] u) id).
  rewrite id_left, id_right.
  reflexivity.
Qed.

(* The comparison: transpose the OTHER adjunction's unit back through this
   one.  Everything below is stated with both adjunctions as explicit
   arguments, so each lemma is available at the swapped instantiation too
   -- which is what makes one round-trip argument serve for both. *)
Definition adj_left_compare {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D)
  : F x ~> F' x :=
  from (@adj _ _ _ _ AF x (F' x))
       (@Category.Theory.Adjunction.unit _ _ _ _ AF' x).

(* The comparison is compatible with the units.  This is the statement
   Mac Lane's exercise asks for beside the isomorphism of functors, and
   it is two lines: [to_adj_unit] turns [fmap[U] h ∘ η] into [⌊h⌋], and
   the comparison was DEFINED as [⌈η'⌉]. *)
Theorem adj_left_compare_unit {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D) :
  fmap[U] (adj_left_compare AF AF' x)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ AF x
    ≈ @Category.Theory.Adjunction.unit _ _ _ _ AF' x.
Proof.
  refine (transitivity
            (symmetry (@to_adj_unit _ _ _ _ AF x (F' x)
                         (adj_left_compare AF AF' x))) _).
  exact (@from_adj_comp_law _ _ _ _ AF x (F' x) _).
Qed.

(* One round-trip argument; the other round trip is this lemma at the
   swapped pair. *)
Lemma adj_left_compare_round {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D) :
  adj_left_compare AF' AF x ∘ adj_left_compare AF AF' x ≈ id[F x].
Proof.
  apply (to_adj_injective AF).
  refine (transitivity
            (@to_adj_nat_r _ _ _ _ AF x (F' x) (F x)
               (adj_left_compare AF' AF x)
               (adj_left_compare AF AF' x)) _).
  refine (transitivity
            (compose_respects _ _ (reflexivity _) _ _
               (@from_adj_comp_law _ _ _ _ AF x (F' x) _)) _).
  (* [unit] IS [⌊id⌋] by definition, so the last step is [reflexivity]. *)
  exact (adj_left_compare_unit AF' AF x).
Qed.

Definition adj_left_compare_iso {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D)
  : F x ≅ F' x := {|
  to := adj_left_compare AF AF' x;
  from := adj_left_compare AF' AF x;
  iso_to_from := adj_left_compare_round AF' AF x;
  iso_from_to := adj_left_compare_round AF AF' x
|}.

Lemma adj_left_compare_natural {F F' : D ⟶ C} (AF : F ⊣ U) (AF' : F' ⊣ U)
  {x y : D} (u : x ~> y) :
  adj_left_compare AF AF' y ∘ fmap[F] u
    ≈ fmap[F'] u ∘ adj_left_compare AF AF' x.
Proof.
  apply (to_adj_injective AF).
  refine (transitivity
            (@to_adj_nat_l _ _ _ _ AF x y (F' y)
               (adj_left_compare AF AF' y) u) _).
  refine (transitivity
            (compose_respects _ _
               (@from_adj_comp_law _ _ _ _ AF y (F' y) _)
               _ _ (reflexivity u)) _).
  refine (transitivity (unit_natural AF' u) _).
  symmetry.
  refine (transitivity
            (@to_adj_nat_r _ _ _ _ AF x (F' x) (F' y)
               (fmap[F'] u) (adj_left_compare AF AF' x)) _).
  exact (compose_respects _ _ (reflexivity _) _ _
           (@from_adj_comp_law _ _ _ _ AF x (F' x) _)).
Qed.

(* The two left adjoints are naturally isomorphic, with the comparison
   above as the family.  This is [Functor_Setoid]'s [≈] unfolded, so it
   is the same statement Theory/Adjunction.v's [left_adjoint_iso] proves
   -- built transparently here so that its components have names. *)
Definition left_adjoints_agree {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) : F ≈ F'.
Proof.
  exists (adj_left_compare_iso AF AF').
  intros x y u; simpl.
  rewrite <- comp_assoc.
  rewrite <- adj_left_compare_natural.
  rewrite comp_assoc.
  rewrite adj_left_compare_round.
  rewrite id_left.
  reflexivity.
Defined.

End LeftAdjointComparison.

(** * Mac Lane §IV.8 Exercise 2: the free ring in two ways *)

Definition RngUnderlyingAb : Rng ⟶ Sets := Ab_Forget ◯ Rng_Forget_Ab.
Definition RngUnderlyingMon : Rng ⟶ Sets := Mon_Forget ◯ Rng_Forget_Mon.

Example rng_underlying_fobj_agree (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[RngUnderlyingMon] R := eq_refl.

Example rng_underlying_fmap_agree (R S : Rng) (f : R ~> S) :
  fmap[RngUnderlyingAb] f = fmap[RngUnderlyingMon] f := eq_refl.

(** ** Route one: sets ⟶ abelian groups ⟶ rings *)

Definition free_ring_via_ab : Sets ⟶ Rng := FreeRngAb ◯ FreeAb.

Definition free_ring_via_ab_adjunction
  : free_ring_via_ab ⊣ RngUnderlyingAb :=
  Adjunction_Compose free_ab_adjunction free_rng_ab_adjunction.

(** ** Route two: sets ⟶ monoids ⟶ rings *)

Definition free_ring_via_mon : Sets ⟶ Rng :=
  MonoidRingFunctor ◯ FreeMonSets.

Definition free_ring_via_mon_adjunction
  : free_ring_via_mon ⊣ RngUnderlyingMon :=
  Adjunction_Compose free_mon_sets_adjunction zmring_adjunction.

(* Retyping the monoid route against the ABELIAN route's right adjoint is
   pure field copying: every field of [Adjunction] mentions the right
   adjoint only through [U y] and [fmap[U] f], and those agree
   definitionally, so the five field TYPES are convertible even though the
   two functor RECORDS are not. *)
Definition free_ring_via_mon_adjunction_ab
  : free_ring_via_mon ⊣ RngUnderlyingAb :=
  @Build_Adjunction Rng Sets free_ring_via_mon RngUnderlyingAb
    (@adj _ _ _ _ free_ring_via_mon_adjunction)
    (@to_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction)
    (@to_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction)
    (@from_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction)
    (@from_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction).

(** ** The two composites agree *)

Definition free_ring_composites_agree : free_ring_via_ab ≈ free_ring_via_mon
  := left_adjoints_agree free_ring_via_ab_adjunction
       free_ring_via_mon_adjunction_ab.

(* Theory/Adjunction.v's [left_adjoint_iso] inhabits the SAME type -- the
   two adjunctions are fed to it here so the claim is machine-checked
   rather than asserted.  The two terms are NOT identified: that theorem
   is [Qed], so no component of it reduces and none can be named, which
   is exactly why the transparent version above was built. *)
Example free_ring_composites_agree_via_left_adjoint_iso :
  free_ring_via_ab ≈ free_ring_via_mon :=
  left_adjoint_iso RngUnderlyingAb free_ring_via_ab free_ring_via_mon
    free_ring_via_ab_adjunction free_ring_via_mon_adjunction_ab.

Definition free_ring_comparison (X : Sets)
  : free_ring_via_ab X ~{Rng}~> free_ring_via_mon X :=
  adj_left_compare free_ring_via_ab_adjunction
    free_ring_via_mon_adjunction_ab X.

(* [left_adjoints_agree] is [Defined], so its isomorphism family reduces
   and the comparison named here IS the component of the natural
   isomorphism -- by [eq_refl], not by an argument.  This is what
   [left_adjoint_iso] could not have given. *)
Example free_ring_comparison_is_agree_component (X : Sets) :
  to (projT1 free_ring_composites_agree X) = free_ring_comparison X
  := eq_refl.

Theorem free_ring_composites_agree_unit (X : Sets) :
  fmap[RngUnderlyingAb] (free_ring_comparison X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_ab_adjunction X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction_ab X.
Proof.
  exact (adj_left_compare_unit free_ring_via_ab_adjunction
           free_ring_via_mon_adjunction_ab X).
Qed.

(** ** Readings of the two composites

    The two routes produce visibly different rings on the same generating
    setoid -- formal ring expressions over a free abelian group on one
    side, ℤ-linear combinations of words on the other -- and both object
    actions reduce.  This is a difference of TERMS; the two rings are
    provably isomorphic, and no inequality is proved anywhere.
    That they are nevertheless isomorphic is the exercise. *)

Example free_ring_via_ab_obj (X : Sets) :
  free_ring_via_ab X = FreeRngAbObject (FreeAbObject X) := eq_refl.

Example free_ring_via_mon_obj (X : Sets) :
  free_ring_via_mon X = ZMonRing (FreeMonSetsObject X) := eq_refl.

(* The retyping is inert on the unit: the two adjunctions have the SAME
   forward transpose, hence the same unit, on the nose. *)
Example retype_adj_agrees (X : Sets) (R : Rng)
  (f : free_ring_via_mon X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_mon_adjunction_ab X R) f
    = to (@adj _ _ _ _ free_ring_via_mon_adjunction X R) f := eq_refl.

Example retype_unit_agrees (X : Sets) :
  @Category.Theory.Adjunction.unit _ _ _ _
      free_ring_via_mon_adjunction_ab X
    = @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction X := eq_refl.

(** * Non-degeneracy

    Nothing below is obtained by induction on [fr_eq]: every constructor
    of that relation concludes an equation, so no induction over it can
    produce a negative.  Each refutation maps OUT of the free ring into a
    concrete ring and reads the answer off there. *)

Section NonDegeneracy.

(* The hypotheses appear only in proofs, so they must be named for the
   section to discharge them as explicit arguments -- the
   Theory/EckmannHilton.v idiom. *)
Local Set Default Proof Using "All".

Context (A : AbObject).
Context (R : RingObject).
Context (Hne : rig_one R ≈ rig_zero R → False).

(* The constant-zero map is a homomorphism of abelian groups, hence a
   legitimate probe.  Under it every generator dies and the unit does
   not, which is what separates a generator from a scalar. *)
Definition fr_zero_probe : A ~{Ab}~> Rng_Forget_Ab R.
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := fun _ => rig_zero R |}.
    intros a b Hab; reflexivity.
  - simpl; reflexivity.
  - intros a b; simpl; symmetry; exact (rig_add_zero_l R (rig_zero R)).
Defined.

(* The free ring is not the zero ring. *)
Theorem free_rng_ab_zero_not_one : fr_eq (@fr_zero A) fr_one → False.
Proof.
  intro He.
  apply Hne; symmetry.
  exact (fr_eval_respects R fr_zero_probe _ _ He).
Qed.

(* No generator is the unit -- the insertion of A does not meet the
   scalars.  True of EVERY generator of EVERY abelian group. *)
Theorem free_rng_ab_gen_not_one (a : carrier (cmon_setoid A)) :
  fr_eq (fr_gen a) (@fr_one A) → False.
Proof.
  intro He.
  apply Hne; symmetry.
  exact (fr_eval_respects R fr_zero_probe _ _ He).
Qed.

End NonDegeneracy.

Arguments fr_zero_probe A {R}.
Arguments free_rng_ab_zero_not_one A {R} Hne _.
Arguments free_rng_ab_gen_not_one A {R} Hne a _.

(** ** The integers embed in the free ring on the integers *)

Lemma int_one_not_zero : rig_one Int_Ring ≈ rig_zero Int_Ring → False.
Proof. intro H; compute in H; discriminate H. Qed.

(* [Rng_Forget_Ab Int_Ring] IS Instance/Ab/Free.v's [ab_int], so the
   identity of [Ab] is already a probe and no new homomorphism is
   needed. *)
Definition rng_int_probe : ab_int ~{Ab}~> Rng_Forget_Ab Int_Ring :=
  @id Ab ab_int.

Theorem int_free_rng_gen_injective (m n : Z) :
  fr_eq (@fr_gen ab_int m) (@fr_gen ab_int n) → m = n.
Proof. exact (fr_eval_respects Int_Ring rng_int_probe _ _). Qed.

Theorem int_free_rng_gens_distinct :
  fr_eq (@fr_gen ab_int 2%Z) (@fr_gen ab_int 3%Z) → False.
Proof. intro H; discriminate (int_free_rng_gen_injective _ _ H). Qed.

Theorem int_free_rng_gen_not_one :
  fr_eq (@fr_gen ab_int 1%Z) fr_one → False.
Proof.
  exact (free_rng_ab_gen_not_one ab_int int_one_not_zero 1%Z).
Qed.

(** ** The free ring on a free abelian group of rank two is NOT
       commutative

    The probe is the upper-triangular 2×2 integer matrices of
    Instance/Rng/Algebras/Associative.v -- the FIRST closed
    non-commutative [RingObject] in tree, [Lam2] being a second -- and
    the two generators go to its two non-commuting matrix units.  Both
    products COMPUTE, so the separation
    is [discriminate] on closed data. *)

Definition ut2_two_probe : AbTwoGens ~{Sets}~> Ab_Forget (Rng_Forget_Ab UT2).
Proof.
  unshelve refine {|
    morphism := fun b : carrier AbTwoGens =>
                  if b then ut2_e11 else ut2_e12
  |}.
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

Definition rng_ut2_probe
  : FreeAbObject AbTwoGens ~{Ab}~> Rng_Forget_Ab UT2 :=
  free_ab_extend ut2_two_probe.

Definition rng_two_gens : AbObject := FreeAbObject AbTwoGens.

Definition rng_gx : FRTerm rng_two_gens :=
  @fr_gen rng_two_gens (@fa_gen AbTwoGens true).
Definition rng_gy : FRTerm rng_two_gens :=
  @fr_gen rng_two_gens (@fa_gen AbTwoGens false).

Example rng_gxgy_computes :
  rig_map (free_rng_ab_extend rng_ut2_probe) (fr_mul rng_gx rng_gy)
    = ut2_e12 := eq_refl.

Example rng_gygx_computes :
  rig_map (free_rng_ab_extend rng_ut2_probe) (fr_mul rng_gy rng_gx)
    = ut2_zero := eq_refl.

Theorem free_rng_ab_not_commutative :
  fr_eq (fr_mul rng_gx rng_gy) (fr_mul rng_gy rng_gx) → False.
Proof.
  intro He.
  pose proof (fr_eval_respects UT2 rng_ut2_probe _ _ He) as H.
  compute in H; discriminate H.
Qed.

Theorem free_rng_ab_two_gens_distinct : fr_eq rng_gx rng_gy → False.
Proof.
  intro He.
  pose proof (fr_eval_respects UT2 rng_ut2_probe _ _ He) as H.
  compute in H; discriminate H.
Qed.

(* The object just probed IS the ab-route free ring on the two-element
   setoid, so the witness exercises the composite of the exercise and not
   a construction beside it. *)
Example rng_two_gens_is_via_ab :
  FreeRngAbObject rng_two_gens = free_ring_via_ab AbTwoGens := eq_refl.

(** ** The two-step transpose of the abelian route

    [Adjunction_Compose]'s transposes are the pasted transposes
    definitionally, so restricting a ring homomorphism out of the
    ab-route free ring to the generating SET is: restrict to the free
    abelian group, then restrict to the generators. *)
Example free_ring_via_ab_transpose (X : Sets) (R : Rng)
  (f : free_ring_via_ab X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_ab_adjunction X R) f
    = to (@adj _ _ _ _ free_ab_adjunction X (Rng_Forget_Ab R))
        (to (@adj _ _ _ _ free_rng_ab_adjunction (FreeAb X) R) f)
  := eq_refl.

(** * Measured boundaries

    Each [Fail] below was stripped once and its failure KIND read off the
    message; the two kinds are kept apart.  Every constant named in a
    [Fail] is also named in a command that must SUCCEED, so a rename
    breaks the file loudly instead of turning a negative vacuously
    green. *)

(** ** CONVERSION negatives *)

(* The two underlying-set functors agree on objects and on arrows -- both
   recorded above by [eq_refl] -- but they are NOT the same functor: the
   law fields are [Compose]'s obligations at different arguments.  Error:
   "cannot unify RngUnderlyingAb and RngUnderlyingMon". *)
Fail Example rng_underlying_records_agree :
  RngUnderlyingAb = RngUnderlyingMon := eq_refl.

(* Consequently the composed monoid-route adjunction cannot simply be
   ASCRIBED against the abelian route's right adjoint: [Adjunction]'s type
   mentions the whole functor record.  What DOES work is copying the five
   fields across ([free_ring_via_mon_adjunction_ab]), because each field
   type mentions the right adjoint only through [U y] and [fmap[U] f]. *)
Fail Definition rng_mon_route_ascribed
  : free_ring_via_mon ⊣ RngUnderlyingAb :=
  Adjunction_Compose free_mon_sets_adjunction zmring_adjunction.

(* The two composites are non-convertible terms denoting isomorphic
   rings on the same
   generating setoid, so [free_ring_composites_agree] is not an
   isomorphism between a thing and itself. *)
Fail Example rng_routes_convertible :
  free_ring_via_ab AbTwoGens = free_ring_via_mon AbTwoGens := eq_refl.

(* The UNIT computes ([free_rng_ab_unit_is_insert], above, is [eq_refl]);
   the COUNIT does not.  It is [unique_obj (ump_universal_arrows …)] and
   [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed]-opaque, so
   nothing reduces through it -- [free_rng_ab_counit_generator] states the
   [≈] that does hold.  The discriminating control is the unit: it runs
   through the SAME [AdjunctionFromUniversalArrows] and DOES reduce, so
   the cause is that one constant's opacity and not the route as such. *)
Fail Example rng_counit_computes (R : Rng) (a : carrier (rig_setoid R)) :
  rig_map (free_rng_ab_counit R) (@fr_gen (Rng_Forget_Ab R) a) = a
  := eq_refl.

(* Likewise the free functor's action on an arrow is defined by universal
   factorization rather than by a formula, so relabelling generators is
   the theorem [free_rng_ab_fmap_generators] and not a computation. *)
Fail Example rng_fmap_generator_computes {A B : Ab} (u : A ~{Ab}~> B)
  (a : carrier (cmon_setoid A)) :
  rig_map (fmap[FreeRngAb] u) (fr_gen a) = fr_gen (cmon_map u a)
  := eq_refl.

(** ** FORMABILITY negatives: the monoid route is pinned at [Set]

    [Rig_Forget_Mon] (Theory/Algebra/Rig.v:292) has source [Rig@{u Set}]:
    the rig's hom-and-proof universe is literally [Set].  [Rng_Forget_Mon]
    is [Rig_Forget_Mon ◯ Ring_Forget_Rig] and inherits it, so the whole
    monoid route -- and hence the comparison, which needs both routes at
    ONE [Rng] -- is confined to rings whose carriers live in [Set].  The
    abelian route is not: [RngUnderlyingAb@{u u0}] leaves [u0] free.  The
    pin is the DONOR's and is not repaired here; it is not claimed
    unavoidable.  Error in both cases: "Cannot enforce Set = uh". *)

(* Positive controls naming the two constants the negatives below name,
   so that renaming either breaks this file instead of turning a [Fail]
   vacuously green.  Unconstrained, these elaborate. *)
Check (Rng_Forget_Mon : Rng ⟶ MonSets).
Check (Rig_Forget_Mon : Rig ⟶ MonSets).

Section MonRouteSetPin.

Universe uo uh.
Constraint Set < uh.

(* Positive controls: the abelian route's two forgetful functors DO
   elaborate at a ring whose homs live strictly above [Set]. *)
Check (Rng_Forget_Ab : Rng@{uo uh} ⟶ Ab).
Check (Rig_Forget_CMon : Rig@{uo uh} ⟶ CMon).

Fail Check (Rng_Forget_Mon : Rng@{uo uh} ⟶ MonSets).
Fail Check (Rig_Forget_Mon : Rig@{uo uh} ⟶ MonSets).

End MonRouteSetPin.

(** ** Instrument check

    A [Fail] that must fail for a reason having nothing to do with this
    file, so that a broken [Fail] mechanism would be visible. *)
Fail Example rng_instrument_check : (0%Z = 1%Z) := eq_refl.
