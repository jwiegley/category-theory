(** * The group completion (Grothendieck group) as a left adjoint

    Riehl, "Category Theory in Context" (2nd ed.), §4.1 Example 4.1.10
    (catalogue item [riehl:4.1:example10]) lists the group completion in
    two forms: as a left adjoint [CMonoid → Ab] to the functor forgetting
    inverses, and as a left adjoint [Monoid → Group].  This file delivers
    the FIRST form in full.  What is and is not delivered of the second is
    stated precisely below; nothing here claims the general
    non-commutative construction.

    ** NOT the Grothendieck construction

    [Construction/Grothendieck.v] builds the total category of an indexed
    category — the fibration construction.  It shares only the name.  No
    definition in this file is related to it, and this file requires
    neither it nor any of its satellites.

    ** The mathematics, and why the [+ k] is necessary

    Given a commutative monoid M, the group completion K(M) has as
    elements formal differences [a - b], encoded as pairs (a, b), under

        (a, b) ~ (c, d)  iff  ∃ k, a + d + k ≈ c + b + k.

    The slack term [k] is REQUIRED, not a convenience.  Without it the
    relation reads [a + d ≈ c + b], which is transitive only when M is
    cancellative: the transitivity computation turns

        a + d + k ≈ c + b + k    and    c + f + l ≈ e + d + l

    into [a + f + (d + k + l) ≈ e + b + (d + k + l)], and cancelling the
    [d] would be exactly the cancellation law M is not assumed to have.
    [groth_naive_not_transitive] REFUTES transitivity of the slack-free
    relation over a concrete monoid, namely the booleans under
    disjunction ([rig_cmon Bool_Rig], Theory/Algebra/Rig.v's Example 5.38
    read additively), so the necessity is proved rather than argued.  The
    price is that the completion can collapse: [groth_bool_trivial] shows
    K(bool, ∨) is the one-element group, and [groth_bool_insert_collapses]
    that the insertion identifies [true] with [false] there.

    The witness [k] is DATA — the library's [∃] is [sigT] and the relation
    is written as a [sigT] directly — so no choice principle is consumed
    anywhere below, and the mediator never inspects a witness it did not
    receive.

    ** What is delivered

    - [Ab_to_CMon : Ab ⟶ CMon], the functor forgetting inverses.  It did
      not exist in tree (measured: zero hits for [Ab_to_CMon] and its
      obvious spellings).  It is very cheap because [Instance/Ab.v]
      defines [AbHom A B := CMonHom A B] as a bare [Definition] and gives
      [Ab] literally [CMon]'s identity, composition and hom-setoid: the
      arrow action is the IDENTITY function, and both functor laws are
      [reflexivity].
    - [GrothendieckObject M : AbObject], the pairs quotient.
    - [groth_insert M : M ~{CMon}~> Ab_to_CMon (GrothendieckObject M)].
    - [groth_extend] / [groth_extend_unique] / [groth_universal], the
      universal mapping property.
    - [groth_universal_arrow], [groth_AUniversalArrow], and — through
      Theory/Universal/Arrow.v's generic machinery, the route
      Instance/Ab/Free.v, Instance/Grp/Free.v and Instance/Mod/Free.v all
      take — [GrothLeft] and [grothendieck_adjunction : GrothLeft ⊣
      Ab_to_CMon].
    - [GrothendieckFunctor : CMon ⟶ Ab], built DIRECTLY with the
      computable arrow action [(a, b) ↦ (f a, f b)], and related to the
      machine-produced [GrothLeft]: the object actions agree by [eq_refl]
      ([groth_functor_obj_agrees]) and the arrow actions up to [≈]
      ([groth_fmap_agrees]).  The two are not silently identified.

    ** Riehl's second form, [Monoid → Group]: DELIVERED ELSEWHERE

    It is NOT in this file, and the paragraphs below explain why the
    construction here cannot be it.  It IS delivered, in
    Instance/Grp/Completion.v, by the presentation route of (3).
    Reason (2) is exactly why that had to be a separate
    construction rather than a reuse of this one.

    (1) CORRECTED.  An earlier revision of this header said stating the
        second form would need "a forgetful [Grp ⟶ Mon] that does not
        exist".  That was FALSE.  The bad evidence was a search for a
        category of ordinary set-level monoids that stopped at
        [Theory/Algebra/Monoid/Hom.v:83]'s [Mon] (INTERNAL monoids in a
        monoidal category) and [Construction/Deloop.v:123]'s [MonObject]
        (a bare record with no category).  An internal monoid in
        [(Sets, ∏)] IS an ordinary setoid monoid, so [MonSets] of
        Instance/Rng/MonoidRing.v:170 is a usable category of them --
        Instance/Mon/Free.v develops the free monoid over exactly it --
        and the forgetful functor is [Grp_MonSets : Grp ⟶ MonSets] at
        Instance/Rng/GroupRing.v:155.  The second form is statable.

    (2) The pairs construction is the WRONG construction there, and this
        is not a matter of proof technique.  [GrothendieckObject] produces
        an abelian group for every input — that is definitional, its
        [ab_neg] being the swap — whereas the left adjoint of
        [Group → Monoid] must produce non-abelian groups: the group
        completion of the free monoid on two letters is the free group on
        two letters, and Instance/Grp/Free.v's
        [free_group_two_generators_nonabelian] proves that group
        non-abelian.  A construction always landing in [Ab] therefore
        cannot be that adjoint.  (The in-tree lemma is CITED here, not
        re-proved, and no statement in this file depends on it.)

    (3) What the general construction needs is a presentation: the free
        group on the underlying setoid of M, quotiented by the normal
        closure of the relations identifying [ab] with [a·b] and the empty
        word with the unit.  Both halves exist in tree —
        Instance/Grp/Free.v's [FreeGrp] and Instance/Grp/Quotient/Colimit.v's
        [InNormalClosure] — so the route is available.  It is a second
        file's worth of work, is NOT attempted HERE, and nothing below
        should be read as progress toward it -- it is carried out in
        Instance/Grp/Completion.v, whose [completion_can_be_nonabelian]
        confirms the object it produces escapes (2)'s obstruction.

    ** Strengths, measured strict-first

    Strict ([eq_refl], shipped as [Example]s):

      - [Ab_to_CMon_obj], [Ab_to_CMon_fmap] — the forgetful functor's two
        actions.
      - [groth_carrier], [groth_zero], [groth_neg_computes],
        [groth_plus_computes] — the completion's underlying data.
      - [groth_insert_computes] — the insertion is [a ↦ (a, 0)].
      - [groth_extend_computes] — the mediator IS [f a - f b], on the nose.
      - [groth_arrow_is_insert] — [universal_arrow_from_UMP] stores the
        supplied morphism as the second projection of the comma object it
        builds, so the universal arrow is the insertion with no proof
        involved.
      - [GrothLeft_obj], [groth_functor_obj_agrees] — both functors' object
        actions.
      - [groth_unit_is_insert] — the UNIT computes.  [unit] is derived in
        Theory/Adjunction.v as the transpose of the identity, so this had
        to be checked rather than assumed; it is [fmap[U] id ∘ arrow] and
        [fmap[Ab_to_CMon] id] is [CMon]'s identity, so the unit is the
        insertion itself.

    Not strict.  Three refutations, each PINNED as a [Fail] probe in the
    "Measured negatives" section below (stripped once and confirmed a
    genuine "cannot unify"), each with a positive control:

      - The COUNIT does not compute.  It is
        [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
        (Theory/Universal/Arrow.v:139) is [Qed], so nothing reduces
        through it.  What holds is [≈]: [groth_counit_evaluates].  The
        probe DISCRIMINATES: the UNIT at the same adjunction does close by
        [eq_refl], so the obstruction is that one constant's opacity and
        not the adjunction packaging.
      - [fmap[GrothLeft]] does not compute either, for the same reason:
        [LeftAdjointFunctorFromUniversalArrows] defines it by universal
        factorization rather than by a formula.  This is precisely why
        [GrothendieckFunctor] is built directly, and why
        [groth_fmap_agrees] is [≈] and not [eq_refl].  Their OBJECT
        actions DO agree strictly, which is the control.
      - A pair is [≈] and not [eq_refl] to the difference of the two
        inserted elements: the completion is a QUOTIENT, and [(a, b)]
        against [(a + 0, 0 + b)] is exactly the slack the relation
        absorbs.  [groth_pair_is_difference] is the [≈] statement, and it
        is what forces the mediator.

    ** An elaboration hazard, third sighting

    [nat_to_Z] and [groth_Z_to_nat] raise TWO obligations, not three:
    instance resolution closes [proper_morphism] during elaboration
    because both of their setoids are Leibniz.  That is the hazard
    Instance/Sets/Products.v:409-424 records and Structure/Limit/Power.v
    reports a second sighting of.  It is harmless at these two witnesses
    — their carriers are [nat] and [Z], already concrete — and the
    general definitions are unaffected: [groth_insert] raises all three,
    its setoids being abstract.  Noted so the next reader is not puzzled
    by the obligation count.

    ** Universes, measured off the constraint blocks

    No explicit universe instance is written on any functor or adjunction
    here: [Functor]'s universe arity differs between Rocq 9.1 and
    Coq 8.19/8.20, so such an annotation is not portable.

      - [groth_rel@{u u0 u1 u2}] and [GrothendieckObject@{u u0 u1 u2}]
        carry NO equation in their constraint blocks — only [≤] bounds
        ([u ≤ u1], [u ≤ u2], [u0 ≤ u1], [u0 ≤ u2] and stdlib projection
        bounds).  A bound is not an identification, and these two do not
        identify anything.
      - [groth_insert], [groth_extend], [groth_universal] and everything
        downstream DO carry [u = u0] and [u = u1], collapsing the input
        [CMonObject@{u u0 u1}] to one level.  **That is [CMon]'s doing,
        not the completion's, and the attribution is PROBED rather than
        assumed**: a bare [Definition probe_hom (M : CMonObject) : Type :=
        @hom CMon M M] already elaborates at [CMonObject@{u u u}], while
        [Definition probe_obj (M : CMonObject) : Type :=
        carrier (cmon_setoid M)] leaves all three FREE.  So merely NAMING
        a [CMon] hom is what identifies them — the shape
        Instance/Grp/Pushout.v records for [Grp] — and it appears exactly
        at the first constant of this file whose type mentions a hom.
      - [Ab_to_CMon@{u u0}], [GrothendieckFunctor@{u u0}], [GrothLeft] and
        [grothendieck_adjunction] carry no equation either; their blocks
        hold [u0 < u] (which is [Sets]' own strictness) and [≤] bounds.
        The [Functor] instances read [@{u u0 u0 u u0 u0}], hom identified
        with proof — inherited from [CMon] and [Ab], which are categories
        over [Sets], and introduced nowhere here.
      - [Set] appears in exactly the two concrete witnesses one would
        expect: [groth_nat_Z_iso@{u}] is over [Set] carriers with the sole
        constraint [Set < u], and [groth_bool_trivial@{u}] carries [Set]
        in a universe INSTANCE while acquiring no [Set] constraint at all
        — an instance is not a constraint.  Nothing general in this file
        is pinned to [Set].

    ** Axioms

    91/91 constants closed under the global context — 71 source
    declarations plus 20 [Program] obligations, the count taken from
    [Print Module] rather than from the [.glob], which lists only the 71.

    ** Non-vacuity

    Proved by mapping OUT into concrete abelian groups, since no induction
    on a quotienting relation can yield a negative:

      - [groth_nat_Z_iso : GrothendieckObject groth_nat ≅[Ab] ab_Z] — the
        motivating example K(ℕ, +) ≅ ℤ, a genuine [Isomorphism] in [Ab]
        with both round trips.  [ab_Z] is Instance/Ab/Coproduct.v:264's,
        REUSED rather than redeclared.
      - [groth_nat_insert_injective] — the insertion is injective on ℕ
        (which is cancellative), so the completion does not collapse
        there, and [groth_nat_nontrivial] separates two of its elements.
      - [groth_bool_trivial] / [groth_bool_insert_collapses] — over the
        non-cancellative (bool, ∨) the completion IS trivial and the
        insertion is not injective, so the cancellative hypothesis in the
        previous item is doing work.
      - [groth_naive_not_transitive] — the slack-free relation is not
        transitive, over that same monoid.

    ** NOT delivered

    Nothing of Riehl's second form, which lives in
    Instance/Grp/Completion.v as detailed above.  Beyond that: no comparison
    with Instance/Ab/Free.v's free abelian group (a different left
    adjoint, to [Ab_Forget : Ab ⟶ Sets]); no identification of
    [Ab_to_CMon] with any composite through [Grp]; no [Grp]-level reading
    of the completion, so [Instance/Grp/Abelianization.v]'s [Ab_to_Grp] is
    neither required nor used; no exactness, no functoriality of the
    relation in M beyond [GrothendieckFunctor] itself, no naturality
    clauses of the adjunction restated in the completion's own vocabulary,
    and no normal form for the relation (so no decision procedure).
    [groth_sub_cross] is a general fact about abelian groups and is an
    upstreaming candidate for Instance/Ab/Subtract.v; it is declared here
    rather than there because this file adds no line to any existing
    file. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Ab.Coproduct.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** The functor forgetting inverses *)

(* [AbHom A B] IS [CMonHom A B] (Instance/Ab.v's bare [Definition]), and
   [Ab]'s identity, composition and hom-setoid are [CMon]'s, so the arrow
   action of the forgetful functor is the identity function and both
   functor laws hold by [reflexivity]. *)
Program Definition Ab_to_CMon : Ab ⟶ CMon := {|
  fobj := fun A => ab_cmon A;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(* Both actions are strict. *)
Example Ab_to_CMon_obj (A : AbObject) :
  fobj[Ab_to_CMon] A = ab_cmon A := eq_refl.

Example Ab_to_CMon_fmap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[Ab_to_CMon] f = f := eq_refl.

(** ** A cross-multiplication lemma for abelian groups

    [x + v ≈ u + y] gives [x - y ≈ u - v].  This is the one step where the
    completion's relation is turned into an equation between formal
    differences, and it is what makes the mediator well defined.  It is a
    general fact about abelian groups; see the NOT-delivered note. *)
Lemma groth_sub_cross (A : AbObject)
  (x y u v : carrier (cmon_setoid A)) :
  cmon_plus A x v ≈ cmon_plus A u y →
  ab_sub A x y ≈ ab_sub A u v.
Proof.
  intro H.
  apply (ab_cancel_l A (cmon_plus A y v)).
  transitivity (cmon_plus A x v).
  { rewrite (cmon_plus_assoc A y v (ab_sub A x y)).
    rewrite (cmon_plus_comm A v (ab_sub A x y)).
    rewrite <- (cmon_plus_assoc A y (ab_sub A x y) v).
    now rewrite (ab_add_sub_cancel A x y). }
  transitivity (cmon_plus A u y); [ exact H |].
  symmetry.
  rewrite (cmon_plus_comm A y v).
  rewrite (cmon_plus_assoc A v y (ab_sub A u v)).
  rewrite (cmon_plus_comm A y (ab_sub A u v)).
  rewrite <- (cmon_plus_assoc A v (ab_sub A u v) y).
  now rewrite (ab_add_sub_cancel A u v).
Qed.

(** ** The group completion of a commutative monoid *)

Section Grothendieck.

Context (M : CMonObject).

Local Notation "x ⊞ y" := (cmon_plus M x y)
  (at level 50, left associativity).

Local Notation "'MC'" := (carrier (cmon_setoid M)).

(* Elements of the completion are formal differences, encoded as pairs. *)
Definition GrothPair : Type := (MC * MC)%type.

(* The relation, with the slack term [k] the header explains.  The
   library's [∃] is [sigT], so [k] is DATA and no choice principle is
   consumed. *)
Definition groth_rel (p q : GrothPair) : Type :=
  { k : MC & fst p ⊞ snd q ⊞ k ≈ fst q ⊞ snd p ⊞ k }.

(* The slack-free relation, for the necessity argument below. *)
Definition groth_naive (p q : GrothPair) : Type :=
  fst p ⊞ snd q ≈ fst q ⊞ snd p.

Lemma groth_rel_refl (p : GrothPair) : groth_rel p p.
Proof. exists (cmon_zero M); reflexivity. Qed.

Lemma groth_rel_sym (p q : GrothPair) : groth_rel p q → groth_rel q p.
Proof. intros [k Hk]; exists k; now symmetry. Qed.

(* Three commutative-monoid rearrangements, named so that the transitivity
   argument below reads as the three rewrites it is.  Each is a
   consequence of [cmon_plus_interchange] (Instance/CMon/Biproduct.v)
   plus associativity and commutativity. *)
Lemma groth_ac1 (a d k f l : MC) :
  a ⊞ f ⊞ (d ⊞ k ⊞ l) ≈ a ⊞ d ⊞ k ⊞ (f ⊞ l).
Proof.
  rewrite (cmon_plus_interchange M a f (d ⊞ k) l).
  now rewrite <- (cmon_plus_assoc M a d k).
Qed.

Lemma groth_ac2 (c b k f l : MC) :
  c ⊞ b ⊞ k ⊞ (f ⊞ l) ≈ c ⊞ f ⊞ l ⊞ (b ⊞ k).
Proof.
  rewrite (cmon_plus_assoc M c b k).
  rewrite (cmon_plus_interchange M c (b ⊞ k) f l).
  rewrite (cmon_plus_comm M (b ⊞ k) l).
  now rewrite <- (cmon_plus_assoc M (c ⊞ f) l (b ⊞ k)).
Qed.

Lemma groth_ac3 (e d l b k : MC) :
  e ⊞ d ⊞ l ⊞ (b ⊞ k) ≈ e ⊞ b ⊞ (d ⊞ k ⊞ l).
Proof.
  rewrite (cmon_plus_assoc M e d l).
  rewrite (cmon_plus_interchange M e (d ⊞ l) b k).
  rewrite (cmon_plus_assoc M d l k).
  rewrite (cmon_plus_comm M l k).
  now rewrite <- (cmon_plus_assoc M d k l).
Qed.

(* The transitivity computation.  The produced witness is [d ⊞ k ⊞ l];
   the [d] is what a cancellative monoid would let one drop. *)
Lemma groth_rel_trans (p q r : GrothPair) :
  groth_rel p q → groth_rel q r → groth_rel p r.
Proof.
  destruct p as [a b], q as [c d], r as [e f].
  intros [k Hk] [l Hl]; simpl in *.
  exists (d ⊞ k ⊞ l); simpl.
  rewrite (groth_ac1 a d k f l).
  rewrite Hk.
  rewrite (groth_ac2 c b k f l).
  rewrite Hl.
  apply (groth_ac3 e d l b k).
Qed.

#[local] Instance groth_rel_Equivalence : Equivalence groth_rel.
Proof.
  constructor.
  - exact groth_rel_refl.
  - exact groth_rel_sym.
  - exact groth_rel_trans.
Qed.

Definition groth_setoid : SetoidObject := {|
  carrier   := GrothPair;
  is_setoid := {| equiv := groth_rel;
                  setoid_equiv := groth_rel_Equivalence |}
|}.

(** *** The group operations *)

Definition groth_zero : GrothPair := (cmon_zero M, cmon_zero M).

Definition groth_plus (p q : GrothPair) : GrothPair :=
  (fst p ⊞ fst q, snd p ⊞ snd q).

Definition groth_neg (p : GrothPair) : GrothPair := (snd p, fst p).

Lemma groth_plus_respects :
  Proper (groth_rel ==> groth_rel ==> groth_rel) groth_plus.
Proof.
  intros [a b] [a' b'] [k Hk] [c d] [c' d'] [l Hl]; simpl in *.
  exists (k ⊞ l); simpl.
  rewrite (cmon_plus_interchange M a c b' d').
  rewrite (cmon_plus_interchange M (a ⊞ b') (c ⊞ d') k l).
  rewrite Hk, Hl.
  rewrite (cmon_plus_interchange M (a' ⊞ b) k (c' ⊞ d) l).
  now rewrite (cmon_plus_interchange M a' b c' d).
Qed.

Lemma groth_neg_respects : Proper (groth_rel ==> groth_rel) groth_neg.
Proof.
  intros [a b] [a' b'] [k Hk]; simpl in *.
  exists k; simpl.
  rewrite (cmon_plus_comm M b a').
  rewrite (cmon_plus_comm M b' a).
  now symmetry.
Qed.

Lemma groth_plus_assoc (p q r : GrothPair) :
  groth_rel (groth_plus (groth_plus p q) r) (groth_plus p (groth_plus q r)).
Proof.
  destruct p as [a b], q as [c d], r as [e f].
  exists (cmon_zero M); simpl.
  now rewrite !cmon_plus_assoc.
Qed.

Lemma groth_plus_comm (p q : GrothPair) :
  groth_rel (groth_plus p q) (groth_plus q p).
Proof.
  destruct p as [a b], q as [c d].
  exists (cmon_zero M); simpl.
  now rewrite (cmon_plus_comm M a c), (cmon_plus_comm M b d).
Qed.

Lemma groth_plus_zero_l (p : GrothPair) :
  groth_rel (groth_plus groth_zero p) p.
Proof.
  destruct p as [a b].
  exists (cmon_zero M); simpl.
  now rewrite !cmon_plus_zero_l.
Qed.

Lemma groth_neg_left (p : GrothPair) :
  groth_rel (groth_plus (groth_neg p) p) groth_zero.
Proof.
  destruct p as [a b].
  exists (cmon_zero M); simpl.
  rewrite !cmon_plus_zero_r.
  rewrite cmon_plus_zero_l.
  apply cmon_plus_comm.
Qed.

Definition GrothCMon : CMonObject := {|
  cmon_setoid        := groth_setoid;
  cmon_zero          := groth_zero;
  cmon_plus          := groth_plus;
  cmon_plus_respects := groth_plus_respects;
  cmon_plus_assoc    := groth_plus_assoc;
  cmon_plus_comm     := groth_plus_comm;
  cmon_plus_zero_l   := groth_plus_zero_l
|}.

(* The completion.  [ab_neg] is the swap, so the object is abelian by
   construction -- the fact item (2) of the header's second-form
   discussion turns on. *)
Definition GrothendieckObject : AbObject := {|
  ab_cmon         := GrothCMon;
  ab_neg          := groth_neg;
  ab_neg_respects := groth_neg_respects;
  ab_neg_left     := groth_neg_left
|}.

(** *** The insertion *)

Program Definition groth_insert :
  M ~{CMon}~> Ab_to_CMon GrothendieckObject := {|
  cmon_map := {| morphism := fun a : MC => (a, cmon_zero M) |}
|}.
Next Obligation.
  intros a b Hab; exists (cmon_zero M); simpl.
  now rewrite Hab.
Qed.
Next Obligation. simpl; apply groth_rel_refl. Qed.
Next Obligation.
  intros a b; exists (cmon_zero M); simpl.
  now rewrite !cmon_plus_zero_l, !cmon_plus_zero_r.
Qed.

(** *** The universal property *)

Section Extend.

Context (A : AbObject).
Context (h : M ~{CMon}~> Ab_to_CMon A).

(* The mediator: a formal difference goes to an actual difference. *)
Definition groth_med (p : GrothPair) : carrier (cmon_setoid A) :=
  ab_sub A (cmon_map h (fst p)) (cmon_map h (snd p)).

Lemma groth_med_respects : Proper (groth_rel ==> equiv) groth_med.
Proof.
  intros [a b] [c d] [k Hk]; unfold groth_med; simpl in *.
  (* Apply h to the relation, then cancel the image of the slack term.
     [ab_cancel_l] is applied with all three arguments explicit: with the
     last two left to unification it matches the wrong pair. *)
  assert (Hh : cmon_plus A
                 (cmon_plus A (cmon_map h a) (cmon_map h d))
                 (cmon_map h k)
               ≈ cmon_plus A
                   (cmon_plus A (cmon_map h c) (cmon_map h b))
                   (cmon_map h k)).
  { rewrite <- !(cmon_map_plus h).
    now rewrite Hk. }
  assert (Hcan : cmon_plus A (cmon_map h a) (cmon_map h d)
                 ≈ cmon_plus A (cmon_map h c) (cmon_map h b)).
  { apply (ab_cancel_l A (cmon_map h k)
             (cmon_plus A (cmon_map h a) (cmon_map h d))
             (cmon_plus A (cmon_map h c) (cmon_map h b))).
    rewrite (cmon_plus_comm A (cmon_map h k)
               (cmon_plus A (cmon_map h a) (cmon_map h d))).
    rewrite (cmon_plus_comm A (cmon_map h k)
               (cmon_plus A (cmon_map h c) (cmon_map h b))).
    exact Hh. }
  apply groth_sub_cross.
  exact Hcan.
Qed.

Program Definition groth_extend : GrothendieckObject ~{Ab}~> A := {|
  cmon_map := {| morphism := groth_med |}
|}.
Next Obligation. exact groth_med_respects. Qed.
Next Obligation.
  unfold groth_med; simpl.
  rewrite (cmon_map_zero h).
  apply ab_sub_self.
Qed.
Next Obligation.
  intros [a b] [c d]; unfold groth_med; simpl.
  rewrite !(cmon_map_plus h).
  symmetry; apply ab_sub_plus.
Qed.

(* The triangle: restricting the mediator to the insertion recovers h. *)
Lemma groth_extend_insert (a : MC) :
  cmon_map groth_extend (cmon_map groth_insert a) ≈ cmon_map h a.
Proof.
  simpl; unfold groth_med; simpl.
  rewrite (cmon_map_zero h).
  apply ab_sub_zero_r.
Qed.

(* Every pair is the difference of two inserted elements.  This is what
   forces the mediator, and it is [≈] and not [eq_refl]: the two pairs
   [(a, b)] and [(a + 0, 0 + b)] are genuinely different elements of the
   underlying type, related by the quotient relation. *)
Lemma groth_pair_is_difference (a b : MC) :
  groth_rel (a, b)
    (ab_sub GrothendieckObject
       (cmon_map groth_insert a) (cmon_map groth_insert b)).
Proof.
  unfold ab_sub; simpl.
  exists (cmon_zero M); simpl.
  now rewrite !cmon_plus_zero_l, !cmon_plus_zero_r.
Qed.

Lemma groth_extend_unique (g : GrothendieckObject ~{Ab}~> A)
  (Hg : ∀ a : MC, cmon_map g (cmon_map groth_insert a) ≈ cmon_map h a)
  (p : GrothPair) :
  cmon_map g p ≈ cmon_map groth_extend p.
Proof.
  destruct p as [a b].
  rewrite (proper_morphism (cmon_map g) _ _
             (groth_pair_is_difference a b)).
  rewrite (ab_map_sub g).
  rewrite (Hg a), (Hg b).
  simpl; unfold groth_med; reflexivity.
Qed.

End Extend.

Arguments groth_med {A} h p.
Arguments groth_extend {A} h.
Arguments groth_extend_insert {A} h a.
Arguments groth_extend_unique {A} h g Hg p.

(* The universal mapping property in the shape [universal_arrow_from_UMP]
   wants: every [h : M ~> Ab_to_CMon A] factors uniquely through the
   insertion. *)
Lemma groth_universal (A : Ab) (h : M ~{CMon}~> Ab_to_CMon A) :
  ∃! g : GrothendieckObject ~{Ab}~> A,
    h ≈ fmap[Ab_to_CMon] g ∘ groth_insert.
Proof.
  unshelve eexists.
  - exact (groth_extend h).
  - intro a; simpl; symmetry; exact (groth_extend_insert h a).
  - intros g Hg p; simpl.
    symmetry; apply (groth_extend_unique h g).
    intro a; symmetry; exact (Hg a).
Qed.

End Grothendieck.

(* The in-section [Arguments] above are not preserved across [End], which
   prepends [M] to every signature, so they are re-issued here. *)
Arguments groth_med {M A} h p.
Arguments groth_extend {M A} h.
Arguments groth_extend_insert {M A} h a.
Arguments groth_extend_unique {M A} h g Hg p.

Arguments GrothPair M : clear implicits.
Arguments groth_rel {M} p q.
Arguments groth_naive {M} p q.
Arguments groth_zero M : clear implicits.
Arguments groth_plus {M} p q.
Arguments groth_neg {M} p.

(** ** Strict readings of the data *)

Example groth_carrier (M : CMonObject) :
  carrier (cmon_setoid (GrothendieckObject M))
    = (carrier (cmon_setoid M) * carrier (cmon_setoid M))%type := eq_refl.

Example groth_zero_computes (M : CMonObject) :
  cmon_zero (GrothendieckObject M) = (cmon_zero M, cmon_zero M) := eq_refl.

Example groth_plus_computes (M : CMonObject)
  (a b c d : carrier (cmon_setoid M)) :
  cmon_plus (GrothendieckObject M) (a, b) (c, d)
    = (cmon_plus M a c, cmon_plus M b d) := eq_refl.

Example groth_neg_computes (M : CMonObject)
  (a b : carrier (cmon_setoid M)) :
  ab_neg (GrothendieckObject M) (a, b) = (b, a) := eq_refl.

Example groth_insert_computes (M : CMonObject)
  (a : carrier (cmon_setoid M)) :
  cmon_map (groth_insert M) a = (a, cmon_zero M) := eq_refl.

Example groth_extend_computes (M : CMonObject) (A : AbObject)
  (h : M ~{CMon}~> Ab_to_CMon A) (a b : carrier (cmon_setoid M)) :
  cmon_map (groth_extend h) (a, b)
    = ab_sub A (cmon_map h a) (cmon_map h b) := eq_refl.

(** ** The universal arrow, the left adjoint and the adjunction *)

Definition groth_universal_arrow (M : CMon)
  : UniversalArrow M Ab_to_CMon :=
  universal_arrow_from_UMP M Ab_to_CMon (GrothendieckObject M)
    (groth_insert M) (groth_universal M).

(* The same content in the direct encoding, where the universal object is
   named rather than projected out of a comma category. *)
Program Definition groth_AUniversalArrow (M : CMon)
  : AUniversalArrow M Ab_to_CMon (GrothendieckObject M) := {|
  universal_arrow := groth_insert M
|}.
Next Obligation.
  intros M A h.
  unshelve eexists.
  - exact (groth_extend h).
  - intro a; simpl; exact (groth_extend_insert h a).
  - intros g Hg p; simpl.
    (* [AUniversalArrow]'s uniqueness field is oriented the other way
       round from the comma-packaged one, hence the [symmetry]. *)
    symmetry; apply (groth_extend_unique h g).
    intro a; exact (Hg a).
Qed.

(* The functor and the adjunction come out of the generic machinery with
   no further proof. *)
Definition GrothLeft : CMon ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_to_CMon groth_universal_arrow.

Definition grothendieck_adjunction : GrothLeft ⊣ Ab_to_CMon :=
  AdjunctionFromUniversalArrows Ab_to_CMon groth_universal_arrow.

Example GrothLeft_obj (M : CMon) :
  GrothLeft M = GrothendieckObject M := eq_refl.

(* [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds, so the universal arrow is
   the insertion on the nose. *)
Example groth_arrow_is_insert (M : CMon) :
  @arrow _ _ M Ab_to_CMon (groth_universal_arrow M) = groth_insert M
  := eq_refl.

(** ** The unit computes; the counit does not *)

Definition groth_unit (M : CMon)
  : M ~{CMon}~> Ab_to_CMon (GrothLeft M) :=
  @Category.Theory.Adjunction.unit _ _ _ _ grothendieck_adjunction M.

Example groth_unit_is_insert (M : CMon) (a : carrier (cmon_setoid M)) :
  cmon_map (groth_unit M) a = (a, cmon_zero M) := eq_refl.

Definition groth_counit (A : Ab)
  : GrothLeft (Ab_to_CMon A) ~{Ab}~> A :=
  @Category.Theory.Adjunction.counit _ _ _ _ grothendieck_adjunction A.

(* The counit routes through the [Qed]-opaque [ump_universal_arrows], so
   no [eq_refl] is available and none is claimed.  What holds is that it
   is the difference map. *)
Lemma groth_counit_generator (A : Ab)
  (a : carrier (cmon_setoid (Ab_to_CMon A))) :
  cmon_map (groth_counit A) (a, cmon_zero A) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ grothendieck_adjunction A a).
Qed.

Theorem groth_counit_evaluates (A : Ab)
  (p : GrothPair (Ab_to_CMon A)) :
  cmon_map (groth_counit A) p
    ≈ ab_sub A (fst p) (snd p).
Proof.
  destruct p as [a b].
  transitivity (cmon_map (groth_extend (@id CMon (Ab_to_CMon A)))
                  (a, b)).
  - apply (groth_extend_unique (@id CMon (Ab_to_CMon A))
             (groth_counit A)).
    intro x; exact (groth_counit_generator A x).
  - simpl; reflexivity.
Qed.

(** ** The completion as a functor, built directly

    [LeftAdjointFunctorFromUniversalArrows] defines its arrow action by
    universal factorization, so [fmap[GrothLeft]] does not compute.  The
    componentwise action does, and it is obviously a homomorphism, so the
    functor is built directly and then RELATED to the produced one rather
    than silently substituted for it. *)

Program Definition groth_map {M N : CMonObject} (f : M ~{CMon}~> N)
  : GrothendieckObject M ~{Ab}~> GrothendieckObject N := {|
  cmon_map := {| morphism := fun p : GrothPair M =>
                   (cmon_map f (fst p), cmon_map f (snd p)) |}
|}.
Next Obligation.
  intros M N f [a b] [c d] [k Hk]; simpl in *.
  exists (cmon_map f k); simpl.
  rewrite <- !(cmon_map_plus f).
  now rewrite Hk.
Qed.
Next Obligation.
  intros M N f; simpl.
  exists (cmon_zero N); simpl.
  now rewrite !(cmon_map_zero f).
Qed.
Next Obligation.
  intros M N f [a b] [c d]; simpl.
  exists (cmon_zero N); simpl.
  now rewrite !(cmon_map_plus f).
Qed.

Program Definition GrothendieckFunctor : CMon ⟶ Ab := {|
  fobj := GrothendieckObject;
  fmap := @groth_map
|}.
Next Obligation.
  intros M N f g Hfg [a b]; simpl.
  exists (cmon_zero N); simpl.
  now rewrite (Hfg a), (Hfg b).
Qed.
Next Obligation.
  intros M [a b]; simpl.
  exists (cmon_zero M); simpl; reflexivity.
Qed.
Next Obligation.
  intros M N P f g [a b]; simpl.
  exists (cmon_zero P); simpl; reflexivity.
Qed.

Example groth_functor_obj_agrees (M : CMon) :
  fobj[GrothendieckFunctor] M = fobj[GrothLeft] M := eq_refl.

Example groth_map_computes {M N : CMonObject} (f : M ~{CMon}~> N)
  (a b : carrier (cmon_setoid M)) :
  cmon_map (groth_map f) (a, b) = (cmon_map f a, cmon_map f b) := eq_refl.

(* The arrow actions agree up to [≈].  They cannot agree strictly:
   [fmap[GrothLeft]] is [unique_obj (ump_universal_arrows …)] and
   [ump_universal_arrows] is [Qed]. *)
Lemma groth_fmap_agrees {M N : CMon} (f : M ~{CMon}~> N) :
  fmap[GrothLeft] f ≈ fmap[GrothendieckFunctor] f.
Proof.
  (* [fmap[GrothLeft]] is [unique_obj] of the very factorization problem
     [groth_map f] solves, so [uniqueness] applies directly; the property
     to discharge is that [groth_map] commutes with the insertions. *)
  apply (uniqueness (ump_universal_arrows (groth_universal_arrow M)
           (@arrow _ _ N Ab_to_CMon (groth_universal_arrow N) ∘ f))).
  intro a; simpl.
  exists (cmon_zero N); simpl.
  now rewrite (cmon_map_zero f).
Qed.

(** ** Measured negatives

    Three strict identifications the header claims are unavailable, pinned
    as [Fail] probes rather than merely asserted.  Each was stripped once
    and confirmed to be a genuine "cannot unify", and each has a positive
    control above that must succeed: [groth_unit_is_insert] for the first,
    [groth_functor_obj_agrees] and [groth_map_computes] for the second,
    [groth_pair_is_difference] for the third.  The instrument check at the
    end uses a scope-free proposition. *)

(* NEGATIVE 1 (conversion).  The counit does not compute.  Its value is
   [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows] is
   [Qed], so nothing reduces through it.  This DISCRIMINATES: the unit of
   the same adjunction does close by [eq_refl] ([groth_unit_is_insert]),
   so the obstruction is that one constant's opacity and not the
   adjunction packaging. *)
Fail Example groth_counit_not_strict (A : Ab)
  (a : carrier (cmon_setoid (Ab_to_CMon A))) :
  cmon_map (groth_counit A) (a, cmon_zero A) = a := eq_refl.

(* NEGATIVE 2 (conversion).  The two functors' ARROW actions are not
   convertible, for the same reason:
   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
   factorization.  Their OBJECT actions do agree strictly
   ([groth_functor_obj_agrees]), which is what makes this a statement
   about the arrow action specifically. *)
Fail Example groth_fmap_not_strict (M N : CMon) (f : M ~{CMon}~> N) :
  fmap[GrothLeft] f = fmap[GrothendieckFunctor] f := eq_refl.

(* NEGATIVE 3 (conversion).  A pair is only [≈]-equal to the difference of
   the two inserted elements, never convertible to it: the completion is a
   QUOTIENT, and [(a, b)] against [(a + 0, 0 + b)] is exactly the slack the
   relation absorbs.  [groth_pair_is_difference] is the [≈] statement. *)
Fail Example groth_difference_not_strict (M : CMonObject)
  (a b : carrier (cmon_setoid M)) :
  (a, b) = ab_sub (GrothendieckObject M)
             (cmon_map (groth_insert M) a) (cmon_map (groth_insert M) b)
  := eq_refl.

(* Instrument check: the [Fail]s above are firing on conversion, not on a
   dead command. *)
Fail Example groth_instrument_check : true = false := eq_refl.

(** ** The slack term is necessary

    Over the booleans under disjunction -- [rig_cmon Bool_Rig], the
    additive half of Theory/Algebra/Rig.v's Example 5.38 -- the
    slack-free relation is not transitive.  The three pairs below are
    concrete and the refutation is by [discriminate]. *)

Definition groth_bool : CMonObject := rig_cmon Bool_Rig.

Theorem groth_naive_not_transitive :
  (∀ p q r : GrothPair groth_bool,
      @groth_naive groth_bool p q → @groth_naive groth_bool q r →
      @groth_naive groth_bool p r) → False.
Proof.
  intro Htrans.
  assert (H1 : @groth_naive groth_bool (false, false) (true, true)).
  { unfold groth_naive; simpl; reflexivity. }
  assert (H2 : @groth_naive groth_bool (true, true) (true, false)).
  { unfold groth_naive; simpl; reflexivity. }
  pose proof (Htrans _ _ _ H1 H2) as H3.
  unfold groth_naive in H3; simpl in H3.
  discriminate H3.
Qed.

(* And the price: with the slack term, the completion of that monoid is
   trivial -- every two pairs are related, by taking [k := true]. *)
Theorem groth_bool_trivial (p q : GrothPair groth_bool) :
  @groth_rel groth_bool p q.
Proof.
  destruct p as [a b], q as [c d].
  exists true; simpl.
  now rewrite !Bool.orb_true_r.
Qed.

Theorem groth_bool_insert_collapses :
  cmon_map (groth_insert groth_bool) true
    ≈ cmon_map (groth_insert groth_bool) false.
Proof. apply groth_bool_trivial. Qed.

(** ** K(ℕ, +) ≅ ℤ

    The motivating example.  [groth_nat] is the additive half of
    Theory/Algebra/Rig.v's [Nat_Rig]; [ab_Z] is Instance/Ab/Coproduct.v's
    ℤ, reused rather than redeclared. *)

Definition groth_nat : CMonObject := rig_cmon Nat_Rig.

(* The truncation identity that drives everything below: for every
   integer, the difference of the two truncations is the integer. *)
Lemma groth_Z_split (x : Z) :
  (Z.of_nat (Z.to_nat x) - Z.of_nat (Z.to_nat (- x)))%Z = x.
Proof.
  destruct x as [| p | p]; simpl.
  - reflexivity.
  - rewrite positive_nat_Z; lia.
  - rewrite positive_nat_Z; lia.
Qed.

Program Definition nat_to_Z : groth_nat ~{CMon}~> Ab_to_CMon ab_Z := {|
  cmon_map := {| morphism := fun n : nat => Z.of_nat n |}
|}.
(* Only TWO obligations: instance resolution closes [proper_morphism]
   during elaboration, both setoids here being Leibniz.  That is the
   hazard Instance/Sets/Products.v:409-424 records and
   Structure/Limit/Power.v reports a second sighting of; this is a third.
   It is harmless at THESE two witnesses -- their carriers are [nat] and
   [Z], so nothing is pinned that was not already concrete -- and the
   general definitions above are unaffected, [groth_insert] raising all
   three obligations because its setoids are abstract. *)
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; simpl; apply Nat2Z.inj_add. Qed.

Definition groth_nat_to_Z
  : GrothendieckObject groth_nat ~{Ab}~> ab_Z :=
  groth_extend nat_to_Z.

Program Definition groth_Z_to_nat
  : ab_Z ~{Ab}~> GrothendieckObject groth_nat := {|
  cmon_map := {| morphism := fun n : Z => (Z.to_nat n, Z.to_nat (- n)) |}
|}.
(* Two obligations again, for the same reason as [nat_to_Z]. *)
Next Obligation. simpl; apply groth_rel_refl. Qed.
Next Obligation.
  intros m n; simpl.
  exists 0%nat; simpl.
  apply Nat2Z.inj.
  rewrite !Nat2Z.inj_add.
  pose proof (groth_Z_split m) as Hm.
  pose proof (groth_Z_split n) as Hn.
  pose proof (groth_Z_split (m + n)%Z) as Hmn.
  simpl; lia.
Qed.

(* The ℕ-level identity behind the section: stated separately so that the
   isomorphism below closes by conversion rather than by hoping [simpl]
   exposes the right term. *)
Lemma groth_Z_to_nat_section (a b : nat) :
  (Z.to_nat (Z.of_nat a - Z.of_nat b) + b + 0
     = a + Z.to_nat (- (Z.of_nat a - Z.of_nat b)) + 0)%nat.
Proof.
  rewrite !Nat.add_0_r.
  apply Nat2Z.inj.
  rewrite !Nat2Z.inj_add.
  pose proof (groth_Z_split (Z.of_nat a - Z.of_nat b)%Z) as Hs.
  lia.
Qed.

Theorem groth_nat_Z_iso : GrothendieckObject groth_nat ≅[Ab] ab_Z.
Proof.
  unshelve eexists.
  - exact groth_nat_to_Z.
  - exact groth_Z_to_nat.
  - intro n; simpl; unfold groth_med, ab_sub; simpl.
    pose proof (groth_Z_split n) as Hn.
    unfold Z_eqT; lia.
  - intros [a b].
    unshelve refine (existT _ 0%nat _).
    exact (groth_Z_to_nat_section a b).
Qed.

(** ** Non-vacuity on the cancellative side *)

(* ℕ is cancellative, so the slack term buys nothing there and the
   insertion is injective -- the completion does NOT collapse. *)
Theorem groth_nat_insert_injective (a b : nat) :
  cmon_map (groth_insert groth_nat) a
    ≈ cmon_map (groth_insert groth_nat) b → a = b.
Proof.
  intros [k Hk]; simpl in Hk.
  lia.
Qed.

Theorem groth_nat_nontrivial :
  cmon_map (groth_insert groth_nat) 0%nat
    ≈ cmon_map (groth_insert groth_nat) 1%nat → False.
Proof.
  intro H.
  pose proof (groth_nat_insert_injective 0 1 H) as Heq.
  discriminate Heq.
Qed.

(* Mapping OUT: the completion of ℕ separates a negative from a positive
   formal difference, because ℤ does. *)
Example groth_nat_to_Z_computes (a b : nat) :
  cmon_map groth_nat_to_Z (a, b)
    = (Z.of_nat a - Z.of_nat b)%Z := eq_refl.

Theorem groth_nat_sign_separates :
  @groth_rel groth_nat (0%nat, 1%nat) (1%nat, 0%nat) → False.
Proof.
  intro H.
  pose proof (proper_morphism (cmon_map groth_nat_to_Z) _ _ H) as HZ.
  unfold Z_eqT in HZ; simpl in HZ.
  discriminate HZ.
Qed.
