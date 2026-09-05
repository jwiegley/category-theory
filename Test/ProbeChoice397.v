Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Two.
Require Import Category.Adjunction.Choice.

Generalizable All Variables.

(** * Boundary probe for Adjunction/Choice.v (issue #397)

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §IV.7, book p. 102, Exercise 3: in the functor category A^X let S be
    the full subcategory of the functors that have a right adjoint, and
    make R a functor S^op -> X^A by choosing one RF for each F, with
    R(sigma) the conjugate of sigma.

    Adjunction/Choice.v carries ZERO [Fail] commands by design: the
    Definition-of-Done box forbids new [make todo] hits, and an in-file
    negative renames in lockstep with the constant it guards, so it
    cannot detect a rename at all.  This file is where every refutation
    that file's prose describes is pinned.

    METHOD.  The [Require] list above mirrors Adjunction/Choice.v's
    eighteen lines character for character, adding only the target
    module itself; measured, a [diff] of the two blocks reports exactly
    that one added line.  A probe with a short prefix can fail for a
    reason it never measured, which is a FALSE PASS, so nothing is
    dropped and nothing else is added.  Each negative below was
    STRIPPED (the [Fail] removed), written into its own scratch file
    with that same full prefix, compiled ALONE, and its WHOLE error
    read; the kind recorded beside it is read off that error text and
    not off an expectation:

      CONVERSION   the error ends in an explicit "cannot unify" between
                   two inhabitants of ONE type, with no universe clause;
      TYPING       a plain "has type ... while it is expected to have
                   type", with NO "cannot unify" and no universe clause;
      FORMABILITY  the error ends "universe inconsistency: Cannot
                   enforce ...".

    TALLY.  17 [Fail] commands = 1 instrument check + 16 negatives of
    THREE kinds, told apart by the error TEXT: 7 CONVERSION (negatives
    1-7), 1 TYPING (negative 8) and 8 FORMABILITY (negatives 9-16).
    The TYPING one is discriminating: the SAME term ascribed at the
    contravariant type is accepted immediately above it
    ([p397_raf_type_control]), so what is refused is the variance and
    not the term.

    THREE FALSE-PASS SHAPES ARE AVOIDED, and ONE of the three is
    MEASURED HERE rather than taken on trust.  (i) [Fail Program
    Definition] -- negative 8's statement, written with [Program],
    is ACCEPTED, so that spelling reports "The command has not failed!"
    and guards nothing; see negative 8's own note for the obligation it
    defers.  (ii) A bodyless [Fail Example], which fails for want of a
    proof rather than for the reason claimed: every [Fail Example] here
    carries the body [eq_refl].  (iii) An X = X tautology: negative 5
    compares [LeftAdjCat C D] with [Adj C D], two distinct constants
    both written APPLIED, so the command is refused at [eq_refl] and not
    at the statement, and negative 8 compares two different types.

    VERBATIM ERROR TAILS, as read from the sixteen stripped files:

      1.  (cannot unify "RAF_via C D" and "RightAdjointFunctor C D").
      2.  (cannot unify "LI_via C D" and
           "Incl ([D, C]) (LeftAdjSub C D)").
      3.  (cannot unify "fmap[SubToAdj C D ◯ AdjToSub C D] f" and "f").
      4.  (cannot unify "fmap[AdjToSub C D ◯ SubToAdj C D] f" and "f").
      5.  (cannot unify "LeftAdjCat C D" and "Adj C D").
      6.  (cannot unify "ch_obj (ch_canonical C D) x" and "x").
      7.  (cannot unify "conj_mate (adjobj_adj (F; q))
           (adjobj_adj (F; p)) nat_id ∙ conj_mate (adjobj_adj (F; p))
           (adjobj_adj (F; q)) nat_id" and "nat_id").
      8.  The term "RightAdjointFunctor C D" has type
          "(LeftAdjCat C D)^op ⟶ [C, D]" while it is expected to have
          type "LeftAdjCat C D ⟶ [C, D]".   [no "cannot unify" clause]
      9-13. (universe inconsistency: Cannot enforce cp = ch because
            ch < cp).
      14. (universe inconsistency: Cannot enforce ah = <fresh> because
          ah < bh <= <fresh>).
      15. (universe inconsistency: Cannot enforce bh = ah because
          ah < bh).
      16. (universe inconsistency: Cannot enforce ah = bh because
          ah < bh).

    RENAME SIMULATION.  Ten constants of Adjunction/Choice.v are named
    by a negative: [RAF_via], [RightAdjointFunctor], [LI_via],
    [LeftAdjSub], [SubToAdj], [AdjToSub], [LeftAdjCat], [ch_obj],
    [ch_canonical] and [HasRightAdjoint].  Each was renamed in a SCRATCH
    COPY of that file (never in place -- a whole-file rename is a no-op
    by construction and gives a false verdict), the copy recompiled
    under a scratch module name (rc=0 in all ten, so every rename was
    real), and this file recompiled against the copy.  10/10 broke it,
    at lines 147-156, EVERY ONE a [Check] control line and NONE inside a
    [Fail].  Zero vacuous guards.  The DENOMINATOR is exactly the
    constants DECLARED IN THE TARGET that a negative names; the donors a
    negative also names -- [Opposite], [Subcategory], [Adj], [AdjObj],
    [Incl], [conj_mate], [adjobj_adj], [nat_id], and [Fun], which
    negatives 2, 11 and 15 reach through the [[_, _]] notation rather
    than by name -- are declared elsewhere and cannot be renamed in the
    target, so each is given a top-level [Check] guard instead.

    GUARD COVERAGE, measured rather than asserted.  Comment-stripping
    this file and splitting it into commands, the 17 [Fail] blocks
    mention 47 identifiers, of which 31 appear OUTSIDE every [Fail] --
    in the [Check] block below or in a control [Definition].  The
    sixteen that do not are exceptions by construction and nothing else:
    the two vernacular keywords [Fail] and [Example]; the four bound
    variables [F], [f], [p], [q]; the stdlib constructor [eq_refl]; the
    instrument's deliberately absent name; and the eight [Fail]
    command HEADS, which never enter the environment.

    MAKE TODO.  This file adds 36 hits to that target (1826 -> 1862,
    counted by leading "./path:"): the 17 refutation commands, plus 19
    lines of the prose above that name them.  That is the usual
    disclosed overshoot of a probe in this tree.  Adjunction/Choice.v
    itself contributes ZERO, measured with the target's own pattern
    anchored at that path. *)

(** ** Instrument check

    The negatives below are only as good as the harness: a name that
    exists in no file of the tree must be refused. *)

Fail Check p397_no_such_constant_anywhere.

(** ** Guard coverage: every constant a negative names, outside a Fail

    Twenty-nine [Check]s.  Eighteen are DONORS declared elsewhere in the
    tree, which the rename simulation cannot reach, so the [Check] is
    their guard (nine of them are named by a negative).  The other
    eleven are target constants: the ten a negative names, which a
    rename of any of them breaks first, plus [RightAdjChoice]. *)

Check @RightAdjointFunctor.
Check @RAF_via.
Check @LI_via.
Check @LeftAdjSub.
Check @LeftAdjCat.
Check @SubToAdj.
Check @AdjToSub.
Check @ch_obj.
Check @ch_canonical.
Check @HasRightAdjoint.
Check @RightAdjChoice.
Check @Incl.
Check @Sub.
Check @Adj.
Check @AdjObj.
Check @Fun.
Check @Opposite.
Check @Opposite_Functor.
Check @Subcategory.
Check @conj_mate.
Check @adjobj_adj.
Check @adjobj_left.
Check @adjobj_right.
Check @nat_id.
Check @AdjForgetLeft.
Check @AdjForgetRight.
Check @fmap.
Check @Functor.
Check @Adjunction.

(** ** Section A: the seven CONVERSION boundaries, and the variance

    Every negative in this section sits beside the positive controls
    Adjunction/Choice.v already ships, so what each refutation locates
    is visible rather than asserted. *)

Section Conversions.

Context (C D : Category).

(** *** Negative 1 (CONVERSION): R is #395's forgetful functor
        transported, on both ACTIONS but not as a RECORD

    Both data fields agree at [eq_refl] -- the two controls immediately
    below are Adjunction/Choice.v's own [raf_obj_via] and [raf_map_via]
    -- so the difference is confined to the three [Functor] law fields,
    which [Compose] and [Program] rebuild as their own opaque proofs.
    Stripped, the error ends (cannot unify "RAF_via C D" and
    "RightAdjointFunctor C D"). *)

Definition p397_raf_obj_control := raf_obj_via C D.
Definition p397_raf_map_control := raf_map_via C D.

Fail Example p397_raf_via_strict :
  RAF_via C D = RightAdjointFunctor C D := eq_refl.

(** *** Negative 2 (CONVERSION): the same for the FIRST forgetful
        functor against the subcategory inclusion

    Again both actions agree at [eq_refl] ([incl_obj_via],
    [incl_map_via]).  Stripped, the error ends (cannot unify
    "LI_via C D" and "Incl ([D, C]) (LeftAdjSub C D)"). *)

Definition p397_incl_obj_control := incl_obj_via C D.
Definition p397_incl_map_control := incl_map_via C D.

Fail Example p397_li_via_strict :
  LI_via C D = Incl ([D, C]) (LeftAdjSub C D) := eq_refl.

(** *** Negative 3 (CONVERSION): the Adj-side round trip is not the
        identity on ARROWS

    The OBJECT round trip is [rt_adj_obj], at [eq_refl], which is what
    makes this statement well typed at all; the composite rebuilds
    [conj_right] as the mate of [conj_left], equal to the original only
    up to `≈`.  Stripped, the error ends (cannot unify
    "fmap[SubToAdj C D ◯ AdjToSub C D] f" and "f"). *)

Definition p397_rt_adj_obj_control := rt_adj_obj C D.

Fail Example p397_rt_adj_map_strict (x y : Adj C D) (f : x ~> y) :
  fmap[SubToAdj C D ◯ AdjToSub C D] f = f := eq_refl.

(** *** Negative 4 (CONVERSION): nor is the S-side round trip

    Here the composite returns (`1 f; I) and stdlib [sigT] has no
    definitional eta (Lib/Foundation.v's [Set Primitive Projections]
    does not cover it), so this is not definitional even though [I] is
    the only inhabitant of [True].  Object round trip [rt_sub_obj] at
    [eq_refl] beside it.  Stripped, the error ends (cannot unify
    "fmap[AdjToSub C D ◯ SubToAdj C D] f" and "f"). *)

Definition p397_rt_sub_obj_control := rt_sub_obj C D.

Fail Example p397_rt_sub_map_strict (x y : LeftAdjCat C D) (f : x ~> y) :
  fmap[AdjToSub C D ◯ SubToAdj C D] f = f := eq_refl.

(** *** Negative 5 (CONVERSION): S and #395's Adj are DIFFERENT
        categories

    This is the negative that keeps [SubAdj_strict_iso] from being
    vacuous: it is an ISOMORPHISM OF CATEGORIES between two categories
    that are not the same term, S's hom being {sigma & True} and [Adj]'s
    the record [ConjPair].  The two controls beside it are the pivot
    [leftadj_obj] -- the OBJECT types DO agree, on the nose -- and the
    isomorphism itself.  Both sides are written applied, so the command
    is refused at [eq_refl] and not at the statement, and it is not an
    X = X tautology: the two heads are distinct constants.  Stripped,
    the error ends (cannot unify "LeftAdjCat C D" and "Adj C D"). *)

Definition p397_leftadj_obj_control := leftadj_obj C D.
Definition p397_strict_iso_control := SubAdj_strict_iso C D.

Fail Example p397_cats_strict : LeftAdjCat C D = Adj C D := eq_refl.

(** *** Negative 6 (CONVERSION): the canonical choice returns the same
        object only up to [sigT] eta

    All THREE projections return on the nose ([ch_canonical_left],
    [ch_canonical_right], [ch_canonical_adj]), so what is missing is
    exactly the eta rule for the stdlib pair, not any content.
    Stripped, the error ends (cannot unify
    "ch_obj (ch_canonical C D) x" and "x"). *)

Definition p397_ch_left_control := ch_canonical_left C D.
Definition p397_ch_right_control := ch_canonical_right C D.
Definition p397_ch_adj_control := ch_canonical_adj C D.

Fail Example p397_ch_canonical_strict (x : LeftAdjCat C D) :
  ch_obj (ch_canonical C D) x = (x : AdjObj C D) := eq_refl.

(** *** Negative 7 (CONVERSION): the inverse law of the membership
        isomorphism is `≈` and not [eq_refl]

    The composite of the two mates of the identity is [nat_id] only
    after [conj_mate_compose], one identity cancellation and
    [conj_mate_id]; the `≈` form is Adjunction/Choice.v's
    [raf_choice_inverse], the control below.  Stripped, the error ends
    (cannot unify "conj_mate (adjobj_adj (F; q)) (adjobj_adj (F; p))
    nat_id ∙ conj_mate (adjobj_adj (F; p)) (adjobj_adj (F; q)) nat_id"
    and "nat_id"). *)

Definition p397_inverse_weak_control := raf_choice_inverse C D.
Definition p397_choice_iso_control := choice_iso_in_Sub C D.
Definition p397_choice_to_control := raf_choice_iso_to C D.
Definition p397_choice_from_control := raf_choice_iso_from C D.

Fail Example p397_choice_inverse_strict
     (F : D ⟶ C) (p q : HasRightAdjoint F) :
  conj_mate (adjobj_adj ((F; q) : AdjObj C D))
            (adjobj_adj ((F; p) : AdjObj C D)) nat_id
    ∙ conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id
  = nat_id := eq_refl.

(** *** Negative 8 (TYPING): R is CONTRAVARIANT

    Mac Lane's R is a functor S^op -> X^A, and the delivered constant
    has exactly that type.  The control immediately below ascribes the
    SAME term at the contravariant type and is ACCEPTED, so the negative
    is discriminating and is not an X = X tautology.  Stripped, the
    error is a plain has-type mismatch with NO "cannot unify" clause and
    no universe clause.

    IT IS WRITTEN AS A [Fail Definition] AND NEVER AS A [Fail Program
    Definition], AND THAT IS MEASURED ON THIS EXACT STATEMENT rather
    than inferred: with [Program], the very same line is ACCEPTED, so
    [Fail Program Definition] reports "The command has not failed!" and
    pins nothing -- a FALSE PASS.  The mechanism was read off by
    stripping the [Fail] and asking [Obligations]: [Program] turns the
    variance mismatch into

      Obligation 1 of hazA: (((LeftAdjCat C D)^op)%category
                              = LeftAdjCat C D).

    a LEIBNIZ EQUALITY OF CATEGORIES, and the breakdown surfaces only at
    the section close, as "Unsolved obligations when closing section". *)

Definition p397_raf_type_control : Opposite (LeftAdjCat C D) ⟶ [C, D] :=
  RightAdjointFunctor C D.

Fail Definition p397_raf_covariant :
  LeftAdjCat C D ⟶ [C, D] := RightAdjointFunctor C D.

(* Two further controls this section names: the two variance readbacks
   that pin the arrow action's orientation, which no [Fail] can. *)
Definition p397_variance_control := raf_fmap_variance C D.
Definition p397_id_control := raf_id_is_conj_mate_id C D.

End Conversions.

(** ** Section B: hom = proof, FOUR independent donors

    Every constant of Adjunction/Choice.v is over categories whose hom
    and proof universes coincide, expressed by REUSING the level
    variable in the BINDER while NOT ONE of the 79 constraint blocks
    carries such an equation.  That identification is INHERITED, and
    four donors are separated below, each sufficient ALONE and each with
    no constant of the target in its command.

    [Functor] is NOT a donor, and the controls prove it in BOTH
    directions: [Du ⟶ Cu] and [Cu ⟶ Du] are both ACCEPTED at the very
    levels where all five negatives are refused.  Negative 12 is the
    sharpest of the five for that reason -- its error is reported ON
    [Fq], displaying two [@Functor] instances, the one [Fq] has at
    @{co ch cp co ch cp} against the one [Adjunction] demands, whose hom
    and proof levels are the SAME variable -- so what is refused there
    is [Adjunction]'s own shape and not [Functor]. *)

Section HomEqualsProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu Du : Category@{co ch cp}).
Context (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du).

(* CONTROLS at the declared levels. *)
Check Cu.
Check Du.
Check Fq.
Check Uq.
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => @id Cu x).
Check (fun (x y : Cu) (g g' : x ~> y) => g ≈ g').
Check (Du ⟶ Cu).
Check (Cu ⟶ Du).

(** *** Negative 9 (FORMABILITY): [Opposite] alone

    No subcategory, no functor category, no adjunction and no constant
    of the target in the command.  Stripped, the error ends "universe
    inconsistency: Cannot enforce cp = ch because ch < cp". *)

Fail Check (Opposite Cu).

(** *** Negative 10 (FORMABILITY): [Subcategory] alone

    Stripped, same tail. *)

Fail Check (Subcategory Cu).

(** *** Negative 11 (FORMABILITY): the functor CATEGORY alone

    [Du ⟶ Cu] is accepted above, so this is [Fun]'s own shape and not
    [Functor]'s.  Stripped, same tail, reported on [Du]. *)

Fail Check ([Du, Cu]).

(** *** Negative 12 (FORMABILITY): [Adjunction] alone

    Both functors are formable at these levels ([Check Fq], [Check Uq]
    above), so what is refused is the adjunction.  Stripped, same tail,
    reported ON [Fq] with the two [@Functor] instances displayed. *)

Fail Check (Fq ⊣ Uq).

(** *** Negative 13 (FORMABILITY): the delivered functor inherits it

    This is the target's own rejection; it is NOT independent of the
    four above (its body contains all of them), and is pinned so that a
    change lifting the pin at any donor is visible here.  Stripped,
    same tail. *)

Fail Check (RightAdjointFunctor Cu Du).

End HomEqualsProof.

(** ** Section C: where the two hom levels are identified

    Adjunction/Choice.v's profile is [C : Category@{o1 h h}] and
    [D : Category@{o2 h h}] -- ONE level variable in all FOUR
    hom-and-proof slots, with both OBJECT universes free.  The collapse
    of C's hom level with D's needs no adjunction and no record: the
    mere presence of functors in BOTH directions forces it, which is
    exactly the shape of an object of S (a left adjoint [D ⟶ C] paired
    with a right adjoint [C ⟶ D]), and the functor CATEGORY forces it
    independently.  The control shows the functor in the direction that
    IS formable. *)

Section TwoHomLevels.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Au : Category@{ao ah ah}).
Context (Bu : Category@{bo bh bh}).

(* CONTROLS at the declared levels. *)
Check Au.
Check Bu.
Check (fun x y : Au => x ~{Au}~> y).
Check (fun x y : Bu => x ~{Bu}~> y).
Check (Au ⟶ Bu).

(** *** Negative 14 (FORMABILITY): the reverse functor

    Stripped, the error ends "universe inconsistency: Cannot enforce
    ah = <fresh> because ah < bh <= <fresh>". *)

Fail Check (Bu ⟶ Au).

(** *** Negative 15 (FORMABILITY): the functor category, independently

    No functor pair in the command.  Stripped, the error ends "universe
    inconsistency: Cannot enforce bh = ah because ah < bh". *)

Fail Check ([Au, Bu]).

(** *** Negative 16 (FORMABILITY): the delivered functor inherits it

    Not independent of 14 and 15; pinned so a change at either donor is
    visible here.  Stripped, the error ends "universe inconsistency:
    Cannot enforce ah = bh because ah < bh". *)

Fail Check (RightAdjointFunctor Bu Au).

End TwoHomLevels.

(** ** Section D: the non-vacuity witness, named outside every Fail

    Adjunction/Choice.v's section (E) inhabits S at [C = D = _2] with a
    non-identity adjunction and shows the subcategory PROPER.  Nothing
    here is refuted; the block exists so that a rename of any of these
    breaks this file too, and so that the reader can see the witness is
    named rather than described. *)

Definition p397_two_object := two_left_adjoint_object.
Definition p397_two_value := two_raf_value.
Definition p397_two_proper := two_left_adjoint_proper.
Definition p397_two_differ := two_const_functors_differ.
Definition p397_two_not_id := two_left_adjoint_not_identity.
Definition p397_two_adj := two_const_adj.
Definition p397_independence := choice_independence.
Definition p397_equivalence := SubToAdj_Equivalence.
Definition p397_full := LeftAdjSub_Full.
