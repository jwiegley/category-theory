(** * Boundary probes for couniversal arrows

    Companion to Theory/Universal/Arrow/Dual.v and
    Theory/Universal/Arrow/Dual/Examples.v (issue #302, Mac Lane §III.1
    Definition 3).  That file makes several strength claims — some
    definitional, some only up to [≈] — and the negative side of each is
    a conversion boundary that no in-tree consumer would notice breaking.
    They are pinned here.  **If the [Fail] commands below stop failing,
    this file breaks the build.**

    Every negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  The instrument itself was checked — wrapping [Fail] around a
    succeeding command reports "The command has not failed!" and aborts
    compilation — and each negative below was compiled once with the
    [Fail] stripped, to confirm the error is the intended typing failure
    and not a syntax, scope or resolution error.

    THE FOUR BOUNDARIES.

    (1) THE COVARIANT READING IS REAL, NOT A REPACKAGING.  This is the
    claim the issue's design constraint turns on: [coarrow_obj] and
    [coarrow] are supplied by [:=] with no tactic, so the covariantly
    typed [F a ~{C}~> c] and the op-side [c ~{C^op}~> (F^op) a] are the
    same term.  Purely a positive control — the claim IS that nothing is
    rejected.

    (2) THE TERMINAL-OBJECT READING IS A THEOREM, NOT THE DEFINITION.
    [@Initial (=(c) ↓ F^op)] taken in the opposite categories is not
    convertible with [@Terminal (F ↓ =(c))]: [Comma] indexes its objects
    by an ORDERED pair of categories, so the first ranges over
    [1 ∏ D^op] and the second over [D ∏ 1], and [Product] of categories
    is not symmetric on the nose.  This is why
    [couniversal_arrow_terminal] exists as a construction rather than as
    a coercion.  The mismatch is located precisely here as well: it is
    NOT the terminal/initial axis (that conversion is free, and is a
    positive control below), and Construction/Comma.v's [Cocomma] — the
    route the issue proposed — does not close it, being neither of the
    two commas involved.

    (3) THE DUAL IS NOT THE PRIMAL.  [CouniversalArrow c F] and
    [UniversalArrow c F] are distinct types; the file is not a renaming.

    (4) THE COUNIT AGREES WITH THE COUNIVERSAL ARROW ONLY UP TO [≈].
    [AdjunctionFromCouniversalArrows] assembles by duality, and its
    object action does reduce ([right_adjoint_obj] is [eq_refl]) — but
    the transpose delivers [coarrow ∘ fmap[F] id], one [fmap_id] and one
    [id_right] short of the couniversal arrow itself. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Theory.Universal.Arrow.Dual.Examples.

Local Open Scope category_scope.

Section Probes.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {c : C}.
Context (U : CouniversalArrow c F).

(** ** (1) The covariant reading is definitional

    Positive controls.  [coarrow] has the covariant type, and IS the
    op-side [arrow] — the same term, not a transported one. *)

Check (coarrow U : F (coarrow_obj U) ~{C}~> c).

Check (eq_refl : coarrow U = @arrow (C^op) (D^op) c (Opposite_Functor F) U).

Check (eq_refl : coarrow_obj U
                   = @arrow_obj (C^op) (D^op) c (Opposite_Functor F) U).

(** The couniversal mapping property likewise: its statement mentions no
    [op], and it is the primal statement's own term. *)

Check (fun (d : D) (h : F d ~{C}~> c) =>
         eq_refl : @ump_couniversal_arrows C D c F U d h
                     = @ump_universal_arrows (C^op) (D^op) c
                         (Opposite_Functor F) U d h).

(** ** (2) The terminal-object reading is a theorem

    Positive control: the construction, and the fact that it chooses the
    couniversal object on the nose. *)

Check (couniversal_arrow_terminal U : @Terminal (F ↓ =(c))).
Check (couniversal_arrow_terminal_obj U).
Check (couniversal_arrow_of_terminal (couniversal_arrow_terminal U)
         : CouniversalArrow c F).

(** Negative: the op-side initial object is NOT that terminal object.
    (With the [Fail] stripped this reports that [arrow_initial] has type
    [@Initial (fobj[Diagonal 1] c ↓ F^op)] while [@Terminal (F ↓ =(c))] was
    expected -- a type mismatch; the target prints with its implicit argument
    elided, and the words "cannot unify" do NOT appear in this one, unlike
    the two Cocomma probes below.) *)
Fail Check (@arrow_initial (C^op) (D^op) c (Opposite_Functor F) U
              : @Terminal (F ↓ =(c))).

(** Nor are the two comma categories themselves Leibniz-equal — the
    reason for the mismatch, isolated.  (Stripped: cannot unify.) *)
Fail Check (eq_refl
              : @Comma _1 (D^op) (C^op) (@Diagonal (C^op) _1 c)
                       (Opposite_Functor F)
                  = @Comma D _1 C F (@Diagonal C _1 c)).

(** The mismatch is NOT the terminal/initial axis.  Positive control:
    a terminal object of F ↓ =(c) IS an initial object of its opposite,
    by conversion, `Initial K` being notation for `@Terminal (K^op)` and
    `(K^op)^op` being `K`. *)
Check (fun T : @Terminal (F ↓ =(c)) => terminal_is_initial_op T).
Check (fun T : @Terminal (F ↓ =(c)) => (T : @Initial ((F ↓ =(c))^op))).

(** ...and it is not closed by Construction/Comma.v's [Cocomma] either,
    which the issue proposed as the route.  Positive control first: the
    cocomma of the same two functors exists. *)
Check (@Cocomma D _1 C F (@Diagonal C _1 c) : Category).

(** Negative: it is not the comma the op-side [arrow_initial] inhabits.
    (Stripped: cannot unify [@Initial (=(c) ↓ F^op)] with
    [@Initial (F ↑ =(c))].) *)
Fail Check (@arrow_initial (C^op) (D^op) c (Opposite_Functor F) U
              : @Initial (@Cocomma D _1 C F (@Diagonal C _1 c))).

(** Negative: nor is it the opposite of F ↓ =(c) on the nose.
    (Stripped: cannot unify [F ↑ =(c)] with [(F ↓ =(c))^op].) *)
Fail Check (eq_refl : @Cocomma D _1 C F (@Diagonal C _1 c)
                        = (@Comma D _1 C F (@Diagonal C _1 c))^op).

(** ** (3) The dual is not the primal

    Positive control: both types exist, at the same arguments. *)
Check (CouniversalArrow c F : Type).
Check (UniversalArrow c F : Type).

(** Negative: and they are different.  (Stripped: cannot unify
    [CouniversalArrow c F] with [UniversalArrow c F].) *)
Fail Check (eq_refl : CouniversalArrow c F = UniversalArrow c F).

End Probes.

(** ** (4) The counit agrees only up to [≈]

    Measured at the worked example, so the probe is about a real
    adjunction and not a variable. *)

Section CounitProbe.

Context `{C : Category}.
Context `{@Cartesian C}.
Context (p : C ∏ C).

(** Positive controls: the object action of the assembled right adjoint
    reduces to the product on the nose, and the counit IS the projection
    pair up to [≈]. *)
Check (eq_refl : fobj[@product_via_couniversal_functor C _] p
                   = (fst p × snd p)).
Check (@product_via_couniversal_counit C _ p).

(** Negative: that agreement is not an [eq_refl].  (Stripped: cannot
    unify the [counit] with [proj_pair p].) *)
Fail Check (eq_refl
              : @counit (C ∏ C) C (Diagonal_Product C)
                        (@product_via_couniversal_functor C _)
                        (@product_via_couniversal C _) p
                  = @proj_pair C _ p).

End CounitProbe.

(** The instrument is not a no-op: a [Fail] on a succeeding command
    aborts compilation with "The command has not failed!".  The
    following line, uncommented, would do exactly that — it is left as a
    comment because a passing build cannot contain it.

      Fail Check (@CouniversalArrow : forall (C D : Category),
                    obj[C] -> (D ⟶ C) -> Type).

    THE [@] IS LOAD-BEARING, and an earlier revision of this very block
    got it wrong — which is worth recording, since it is precisely the
    failure mode this file exists to rule out.  Without the [@], the
    exhibit reads [Fail Check (CouniversalArrow : ...)]; [Arguments
    CouniversalArrow {C D} c F] (Theory/Universal/Arrow/Dual.v) makes
    [C] and [D] implicit, so the bare name has type
    [obj[?C] -> ?D ⟶ ?C -> Type], the ascription genuinely fails, and
    the [Fail] SUCCEEDS — silently, exit 0.  A demonstration that the
    instrument is live would then have been an instance of the
    instrument passing for the wrong reason.  With the [@] the
    ascription holds and the [Fail] aborts as advertised (measured, exit
    1).

    The controls above are the standing check that the [Fail]s are not
    passing for the wrong reason. *)
