(** * FinSet is finitely complete

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.1
    Exercise 4 (book p. 112, `maclane:V.1:ex4`): the category of finite
    sets has all finite limits.  nLab: https://ncatlab.org/nlab/show/FinSet
    and https://ncatlab.org/nlab/show/equalizer.  In this library the
    finite sets are the skeleton [FinSet] of Instance/FinSet.v — objects
    the naturals, arrows the functions [Fin.t m → Fin.t n] under pointwise
    Leibniz equality — which already had a terminal object
    ([FinSet_Terminal], the numeral [1]), binary products
    ([FinSet_Cartesian], the numeral [m * n] under the positional codec of
    Instance/FinSet/Product.v) and pullbacks ([FinSet_Pullbacks],
    Instance/FinSet/Classifier.v), but no equalizer of any kind: before
    this file no constant anywhere in the tree had type
    [HasEqualizers FinSet] (a tree-wide grep for that phrase finds nothing),
    and the string "qualizer" occurs under Instance/FinSet* exactly once,
    as prose (Instance/FinSet/Subsets.v:95).

    WHAT IS DELIVERED.
    (A) [FinSet_HasEqualizers : HasEqualizers FinSet], NATIVE and
        COMPUTING.  The equalizer of [f g : Fin.t m → Fin.t n] is the counted
        sub-object of agreement: the Boolean predicate [finset_eq_pred f g x
        := fin_eqb (f x) (g x)], its count [FinSet_equalizer_obj f g :=
        fin_countP (finset_eq_pred f g)] as the object, its un-ranking
        [FinSet_equalizer_incl := fin_select _] as the inclusion, and the
        rank [fin_rank] of a fork's values as the mediator
        ([FinSet_equalizer_med]).  The universal property
        [FinSet_IsEqualizer f g : @IsEqualizer FinSet m n f g _ _]
        (Structure/Equalizer/Fork.v's record) is closed by
        Instance/FinSet/Classifier.v's three codec lemmas [fin_select_sat],
        [fin_select_rank] and [fin_select_inj] together with [fin_eqb_eq]
        and [fin_eqb_refl]; nothing about [Fin.t] is proved here beyond
        the one-line [finset_eq_pred_true].  The construction is strictly
        simpler than [FinSet_Pullbacks]'s, which it mirrors: no pair codec
        is needed, so no [fin_unpair] layer.
    (B) [FinSet_FinitelyComplete : @FinitelyComplete FinSet], the
        quantified statement of Structure/Limit/Finite.v:611 — a [Limit]
        for EVERY functor out of EVERY [FiniteCategory]-witnessed shape, the
        reading the issue's reviewer note asks for, not a bundle of named
        shapes — as ONE application of Mac Lane §V.2 Corollary 1 in the
        form #417 landed it: [finitely_complete_from_generators
        FinSet_Terminal FinSet_Cartesian FinSet_HasEqualizers].  The
        generators are FinSet's OWN: its numeral-[1] terminal object, its
        numeral-[m * n] products and the native equalizer above.
    (C) COMPUTATION, seven [eq_refl] examples — five at one parallel pair
        [3 ⇉ 2] agreeing at exactly two points: the equalizer object is the
        numeral [2], its inclusion selects the first and third points, the
        class's chosen object reads back as [2] through [`1 (equalizer f
        g)], the mediator of a one-point fork is the second point of the
        equalizer — and the two headline conversions through the GENERAL
        machinery: the terminal object recovered from the EMPTY finite
        limit, [terminal_obj (FinitelyComplete_Terminal
        FinSet_FinitelyComplete)], IS the numeral [1] by conversion
        ([FinSet_FinitelyComplete_terminal_computes]), and the finite limit
        over the parallel-pair SHAPE [Parallel] at [APair f g] — built by
        Finite.v's [finite_limit] out of three finite products and two
        equalizers, not by the equalizer instance directly — IS the numeral
        [2] ([FinSet_FinitelyComplete_parallel_computes]).  Both are
        MEASURED against the alternative: the same two statements about the
        pullback route [finitely_complete_of_pullbacks_terminal
        FinSet_Pullbacks FinSet_Terminal] and its equalizer
        [HasEqualizers_of_HasPullbacks_Terminal FinSet_Pullbacks] are
        REFUSED at [eq_refl], [lazy] leaving a [fin_countP] over a predicate
        that tests [unique_obj (FinSet_Pullbacks_obligation_2 …)], the
        pullback UMP that [Program] closed opaquely (the probe pins both).

    RELATION TO WHAT EXISTED, AND THREE STALE PREMISES OF THE ISSUE.
    Test/ProbeFinite417.v:271 already carried a [FinSet_FinitelyComplete]
    at probe strength, by the pullback route, and its N10 records that the
    route does not compute; it is renamed there to
    [FinSet_FinitelyComplete_pb] so that this file owns the pinned name
    (the only collision over the nineteen names: one definition and three
    uses), and its N10 note now says which route it is about.  This file's
    [FinSet_FinitelyComplete_terminal_computes] is the first COMPUTING
    witness of finite completeness in the tree, which corrects
    Structure/Limit/Finite.v's "no computing witness" clause (recorded
    there as a correction, and in its docs/INDEX.md bullet).  The issue's
    "Current state" is stale on three points, each re-measured: there IS
    now a finiteness predicate on [Category] ([FiniteCategory], #417); the
    passage from the generators to all finite limits IS formalized, and the
    three places the issue cites as saying otherwise no longer do —
    Structure/Topos.v:22-51 and Structure/Regular.v:26-31 name
    [finitely_complete_of_pullbacks_terminal] as the theorem, and
    Structure/Pullback.v:255-263 and :276-278 record the reduction as PROVED in
    Structure/Pullback/Reduction.v, its :279-282 alone still scoping the
    general claim away from that file without saying where it lives — so the
    issue's "discharge the disclosure" step edits TWO sentences, each line-
    neutrally: Structure/Pullback.v:279-282, and the like-worded
    Structure/Topos/Monadic.v:170-171 ("no such statement is made anywhere in
    this library", a leftover of #417) — both now point at Finite.v's
    [FinitelyComplete], built from products and equalizers rather than by shape
    induction — and nothing in the other two files; and the premise that stood,
    "no equalizer", is the one this file answers.

    WHY NATIVE, AND WHAT IS NOT REQUIRED.  The tree already offered two
    derived equalizers for [FinSet] — [HasEqualizers_of_HasPullbacks_Terminal
    FinSet_Pullbacks] directly, and [@topos_HasEqualizers FinSet
    FinSet_Topos] through Structure/Topos/Monadic.v — and neither is
    written anywhere; both unfold to the same Awodey square over the
    opaque pullback UMP — the topos route IS the pullback-route term, read
    back at [eq_refl] in the probe — so neither computes (the pullback route
    measured above).  A native
    equalizer is what makes the general [finite_limit] REDUCE at [FinSet].
    Instance/FinSet/Pushout.v is deliberately NOT required: it re-declares
    eleven of Classifier.v's codec names at top level without requiring
    Classifier.v ([fin_eqb], [fin_eqb_refl], [fin_eqb_eq], [fin_countP],
    [fin_select], [fin_rank], [fin_select_sat], [fin_select_rank],
    [fin_pred], [fin_FS_inj], [fin_select_inj]), so a file requiring both
    gets shadowing on all eleven; its two extra lemmas [fin_rank_select]
    and [fin_rank_resp] turn out not to be needed.  No hypothesis is taken
    anywhere: [FinSet]'s decidable equality on [Fin.t] is [fin_eqb]'s, and
    every constant is closed under the global context.

    UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK OVER ALL 19 CONSTANTS.
    Ten of the nineteen carry an EMPTY universe binder (the predicate, the
    object, the inclusion, [finset_eq_pred_true], the three example maps
    and three of the examples — everything stated over [nat] and [Fin.t]
    alone); [FinSet_equalizer_med@{u}] and its example carry one free level
    and no constraint.  [FinSet_IsEqualizer@{u u0 u1 u2 u3} : … IsEqualizer@{u
    u0} …] and [FinSet_HasEqualizers@{u u0 u1 u2 u3} : HasEqualizers@{u u0}
    FinSet@{u u0 u1 u2}] carry exactly one constraint, [Set < u1], which is
    [FinSet]'s own ([FinSet@{u u0 u1 u2} : Category@{u u0 u0}] with
    [Set < u1], measured), inherited and not added.
    [FinSet_FinitelyComplete@{u u0 … u10} : FinitelyComplete@{u u0 u1 u2
    u3}] carries thirty-two constraints, among them [Set < u4] (again
    [FinSet]'s bound), the strict bounds [u1 < u], [u2 < u] and the stdlib
    caps ([Projections], [nat_rect], [case0], [caseS'], [prod_rect],
    [Logic_lemmas.equality]) that [finitely_complete_from_generators]
    and the codec bring; [FinitelyComplete@{u u0 u1 u2 u3} : Category@{u3
    u2 u2} → Type@{u}] itself pins nothing to [Set].  NO universe equation
    anywhere in the nineteen blocks; exactly SEVEN blocks carry a
    word-bounded [Set], every one as the strict lower bound [Set < _] on
    the level [FinSet]'s hom universe sits above, none as a pin.

    COUNTS.  19/19 constants closed under the global context with ZERO
    [Axioms:] lines — 10 [Definition], 1 [Lemma], 1 [Instance], 7
    [Example], no [Program] and so no generated obligation — all in the
    [make print-assumptions] gate FULLY QUALIFIED. ONE [Defined]-terminated
    proof ([FinSet_IsEqualizer]); flipped alone to [Qed] with this file and the
    probe recompiled, this file stays green and the probe breaks at ONE line,
    its universe control [Check FinSet_HasEqualizers@{_ _ _ _ _}] — the
    instance's universe instance drops from five levels to four once the proof
    is opaque — so the flip is load-bearing for nothing else and every
    conversion example survives it; it is kept [Defined] by the data
    convention, packing the mediator. Closure 73 modules excluding self,
    dominated by Structure/Limit/Finite.v's 66 (dropping that one [Require]
    leaves 36); Instance/FinSet/Classifier.v costs 4 at the margin and each of
    the other eleven [Category.*] [Require]s costs 0 (thirteen in all, each
    dropped alone). Zero collisions over the 19 names after the one rename in
    the #417 probe described above, and none over the probe's own
    [p415_]-prefixed names.

    Test/ProbeFinSetLimit415.v mirrors this file's [Require] list and carries 6
    refutation commands = 1 instrument check + 5 negatives of THREE kinds told
    apart by the error TEXT: 2 CONVERSION (the pullback route's equalizer
    object at the example pair against the numeral [2], and its terminal object
    from the empty finite limit against [1] — "cannot unify" with no universe
    clause — each beside the native route's accepted [eq_refl], the two
    terminal apexes also shown isomorphic by [terminal_unique]), 2 TYPING
    ([FinSet_HasEqualizers] ascribed at [HasEqualizers Sets], a plain has-type
    mismatch, and [FinSet_FinitelyComplete] ascribed at [Complete FinSet], a
    has-type mismatch whose unification clause compares the [FiniteCategory J]
    binder with a functor type, beside the accepted
    [Complete_FinitelyComplete]) and 1 UNIVERSE (the instance at hom-carrying
    level [Set], "Cannot enforce Set < Set", the inherited bound, beside the
    bare instance accepted) — each stripped ONE AT A TIME in a copy of the
    whole file and compiled alone with its error read; readbacks at [eq_refl]
    of the class's chosen object, inclusion and universal property against this
    file's three constants, of [FinSet_FinitelyComplete] against its [:=], and
    two more concrete counts ([0] for a pair that never agrees, [3] for a pair
    of equal maps); guard coverage measured mechanically under the plain
    tokenization — comment-stripped, every identifier token inside a
    refutation command other than the keywords and the wildcard — 19
    identifiers inside, 15 also outside, the four exceptions exhaustively the
    sort [Set] (named only by the universe negative), the two names the
    refuted [Example]s declare and the instrument's absent name;
    rename-simulated 4/4 over the target constants the negatives name,
    each rename applied in THIS file only and every break landing on a control
    [Example] of the probe, none inside a refutation command. [make todo] grows
    by 6 lines, ALL in the probe — its 6 refutation commands, no header line
    of it naming the keyword — and this file and the edited #417 probe
    contribute ZERO.

    NOT DELIVERED.  [Complete FinSet] (false as stated over this library's
    [Complete], which quantifies over every small shape; not refuted here
    either); a native coequalizer or [FinitelyCocomplete FinSet] beyond the
    pushout-route witness Test/ProbeFinite417.v keeps; any comparison of
    [finite_limit]'s chosen products with [FinSet_Cartesian]'s, or of its
    chosen equalizer with [equalizer], beyond the two computing examples;
    a bridge from [FinSet_FinitelyComplete] to [FinSet_Topos]'s
    generators; a closed formula [fin_countP (fun _ => true) = n] or
    [FinSet_equalizer_obj f f = m]; naturality of the mediator in [h];
    and nothing registered as an [Instance] except [FinSet_HasEqualizers],
    which carries no hypothesis, is the sibling of [FinSet_Pullbacks] and
    [FinSet_Cartesian], and so may safely resolve. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Classifier.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * The equalizer: the counted sub-object of agreement *)

(* The Boolean predicate "f and g agree at x", decided by the heterogeneous
   [fin_eqb] of Instance/FinSet/Classifier.v; [fin_eqb_eq] turns its [true]
   into Leibniz equality at the common index. *)
Definition finset_eq_pred {m n : nat} (f g : Fin.t m → Fin.t n) :
  Fin.t m → bool := fun x => fin_eqb (f x) (g x).

(* The equalizer object counts the agreements; the inclusion un-ranks. *)
Definition FinSet_equalizer_obj {m n : nat} (f g : Fin.t m → Fin.t n) : nat :=
  fin_countP (finset_eq_pred f g).

Definition FinSet_equalizer_incl {m n : nat} (f g : Fin.t m → Fin.t n) :
  Fin.t (FinSet_equalizer_obj f g) → Fin.t m :=
  fin_select (finset_eq_pred f g).

Lemma finset_eq_pred_true {m n : nat} (f g : Fin.t m → Fin.t n) (x : Fin.t m) :
  f x = g x → finset_eq_pred f g x = true.
Proof. intros H; unfold finset_eq_pred; rewrite H; apply fin_eqb_refl. Qed.

(* The mediator of a fork [h] ranks each value of [h], which the fork
   equation certifies to satisfy the predicate. *)
Definition FinSet_equalizer_med {m n : nat} (f g : Fin.t m → Fin.t n)
  {z : nat} (h : Fin.t z → Fin.t m) (Hh : ∀ i, f (h i) = g (h i)) :
  Fin.t z → Fin.t (FinSet_equalizer_obj f g) :=
  fun i => fin_rank (finset_eq_pred f g) (h i)
                    (finset_eq_pred_true f g (h i) (Hh i)).

Definition FinSet_IsEqualizer {m n : nat} (f g : Fin.t m → Fin.t n) :
  @IsEqualizer FinSet m n f g (FinSet_equalizer_obj f g)
    (FinSet_equalizer_incl f g).
Proof.
  unshelve refine {| fork_eq := _; eq_desc := fun z h Hh => _ |}.
  - intro i; simpl.
    apply fin_eqb_eq. exact (fin_select_sat (finset_eq_pred f g) i).
  - unshelve refine {| unique_obj := FinSet_equalizer_med f g h Hh |}.
    + intro i; simpl. exact (fin_select_rank (finset_eq_pred f g) (h i) _).
    + intros v Hv i; simpl in *.
      unfold FinSet_equalizer_med.
      apply (fin_select_inj (finset_eq_pred f g)).
      rewrite (fin_select_rank (finset_eq_pred f g) (h i)). symmetry. apply Hv.
Defined.

#[export] Instance FinSet_HasEqualizers : HasEqualizers FinSet :=
  @Build_HasEqualizers FinSet
    (fun (m n : nat) (f g : Fin.t m → Fin.t n) =>
       (FinSet_equalizer_obj f g;
        (FinSet_equalizer_incl f g; FinSet_IsEqualizer f g))).

(** * Finite completeness, by Mac Lane V.2 Corollary 1 *)

Definition FinSet_FinitelyComplete : @FinitelyComplete FinSet :=
  finitely_complete_from_generators FinSet_Terminal FinSet_Cartesian
    FinSet_HasEqualizers.

(** * Computation *)

(* A parallel pair [3 ⇉ 2] agreeing exactly at the first and third points. *)
Definition finset_eq_example_f : Fin.t 3 → Fin.t 2 := fun _ => Fin.F1.
Definition finset_eq_example_g : Fin.t 3 → Fin.t 2 :=
  fun i => match i with Fin.FS Fin.F1 => Fin.FS Fin.F1 | _ => Fin.F1 end.

Example FinSet_equalizer_obj_computes :
  FinSet_equalizer_obj finset_eq_example_f finset_eq_example_g = 2%nat
  := eq_refl.

Example FinSet_equalizer_incl_computes_0 :
  FinSet_equalizer_incl finset_eq_example_f finset_eq_example_g Fin.F1 = Fin.F1
  := eq_refl.

Example FinSet_equalizer_incl_computes_1 :
  FinSet_equalizer_incl finset_eq_example_f finset_eq_example_g (Fin.FS Fin.F1)
  = Fin.FS (Fin.FS Fin.F1)
  := eq_refl.

Example FinSet_equalizer_readback :
  `1 (@equalizer FinSet _ _ _ finset_eq_example_f finset_eq_example_g) = 2%nat
  := eq_refl.

Definition finset_eq_example_h : Fin.t 1 → Fin.t 3 :=
  fun _ => Fin.FS (Fin.FS Fin.F1).

Example FinSet_equalizer_med_computes :
  FinSet_equalizer_med finset_eq_example_f finset_eq_example_g
    finset_eq_example_h (fun _ => eq_refl) Fin.F1
  = Fin.FS Fin.F1
  := eq_refl.

(* The terminal object recovered from the EMPTY finite limit is the numeral
   [1] by conversion on this route. *)
Example FinSet_FinitelyComplete_terminal_computes :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  = 1%nat
  := eq_refl.

(* The finite limit over the parallel-pair SHAPE at the example — built by
   [finite_limit] out of three finite products and two equalizers, not by
   the equalizer instance directly — is the numeral [2] by conversion. *)
Definition finset_eq_example_diagram : Parallel ⟶ FinSet :=
  @APair FinSet 3%nat 2%nat finset_eq_example_f finset_eq_example_g.

Example FinSet_FinitelyComplete_parallel_computes :
  vertex_obj[@limit_cone Parallel FinSet finset_eq_example_diagram
    (FinSet_FinitelyComplete Parallel Parallel_FiniteCategory
       finset_eq_example_diagram)]
  = 2%nat
  := eq_refl.
