(** * Probe for the p-adic solenoid (issue #410)

    Pins the measured boundaries of the three files #410 adds for Mac
    Lane §V.1, book p. 111 (PDF p. 120), catalog item
    maclane:V.1:construction3, with the appended Riehl Example 3.6.3
    (riehl:3.6:example3).  The files are Instance/Top/Circle.v (the
    circle R/Z over the standard library's constructive Cauchy reals,
    with its p-fold maps [wrap p] and [pwrap p]), Instance/Top/
    Solenoid.v (the solenoid as the limit of the tower of circles in the
    Type-valued [Top], the pinned [solenoid_limit], and in [PTopCat]) and
    Instance/Top/Solenoid/Presentations.v (the group presentation, the
    fibre over the base point as the p-adic integers, and the covering
    property over both categories of spaces).  N1-N8 restate refusals
    #410's two builders and its review measured in scratch files
    (LABELS, below) or that the fold measured for the headers; every one
    is recorded in a target header, which cites it by its label here.
    The positive controls restate the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    Target by target, in the order the three files are named above, the
    [Require] lines each adds to those before it, in its own order, and
    then that target unless an earlier line required it.  Thirty-eight
    lines: the thirty-seven distinct [Require]s of the three targets,
    two targets among them (Circle.v and Solenoid.v), and
    Presentations.v, which no target requires.  Thirty of the lines
    name [Category] modules.  Under this list [Print Libraries] in a
    scratch file loads one hundred and fifty-six [Category] modules, the
    three targets among them, and six modules of the standard library's
    reals, all under Reals/Cauchy.  A shorter import list is what makes
    a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of
    an absent name is refused for that reason ("The reference
    p410_absent_name was not found in the current environment."), and
    each of the forty-four definitions and examples of this file that is
    not a refutation (twenty-five definitions, one of them a [Program]
    definition, and nineteen examples), wrapped in the refutation keyword
    in a copy of this WHOLE file, stops the build at that command with
    the report that the guarded command had been accepted (forty-four of
    forty-four, by a script over the copies).  Every negative other than
    that instrument is a [Definition] or an [Example], never a [Check],
    so that an open evar cannot satisfy it.  Each negative was stripped
    of its refutation keyword in a copy of this WHOLE file, one at a
    time, compiled, and its error read; each of the eight copies stops
    inside the stripped command (by the File line of its error, compared
    by a script with the command's extent).  The kind recorded is the
    kind of that error, and each negative has positive controls beside
    it.  Quotations are Rocq 9.1.1's under this file's import list, with
    the error's environment block left out; Rocq prints the "cannot
    unify" parenthetical with the short names in scope, and <1>, <2> and
    <3> stand for the universes a stripped copy names after itself and a
    serial number.  The three targets and this file also compile on Coq
    8.19.2 and 8.20.1, with no warning, overlaid on the prebuilt trees
    of this library for those versions, whose sources of the one
    thousand and ninety-six modules they hold are this tree's byte for
    byte (compared by script) but for seven, which differ from this
    tree's only by the CORRECTION (#410) comments that issue adds (one
    of them, Instance/Top/Prop.v, is in this file's closure).  Each of
    the eight stripped copies is refused there with the Rocq 9.1.1 error
    up to the serial names of universes (compared by a script): seven
    at the File line and characters of the Rocq 9.1.1 refusal, and N6
    at the whole command, the three universes its error names carrying
    the line and characters they carry under Rocq 9.1.1.

    KINDS.  Nine refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), CONVERSION (N1,
    N4, N5, N7), UNIVERSE (N2, N3, N8) and BINDING (N6): one, four,
    three and one.  A CONVERSION refusal is [eq_refl] refused with a
    "cannot unify" parenthetical; a UNIVERSE refusal is a type mismatch
    whose parenthetical is a universe inconsistency; the BINDING refusal
    is a closed universe list that does not bind the universes its body
    uses.

    LABELS.  builder-sol's scratch W1 and W2 and the review's VW1 and VW2
    are N2 and N3, and the review's VW3 is the control
    [p410_init_union_up]; builder-sol's first draft of
    [CircleTower_step] is N6; builder-pres's M1 is N7, its flipped copy
    of [tower_obj] the control [p410_tower_obj] with [p410_flip_group]
    and [p410_flip_ptop]; the review's E1 is N7's equation unfolded, and
    its F1 is N1's at the level of the reals.  N4, N5 and N8 are the
    fold's own.  The labels are not constants: each refutation carries
    its own in a comment on the line above it, the instrument's reading
    "The instrument".

    ** Instance/Top/Circle.v

    Controls: the points of [Circle] are [Circle_setoid] and the
    underlying maps of [wrap p] and [pwrap p] are [circ_mul p], at
    [eq_refl] ([p410_circle_points], [p410_wrap_map], [p410_pwrap_map]);
    [wrap 1] is the identity up to [≈] ([p410_wrap_one]); the circle's
    equality has its [PropEquiv] ([p410_circ_prop]); two points differ
    ([p410_circle_two]); the lifted points ([p410_circle_lift]).

    N1 (CONVERSION).  The header's STRENGTHS: 1·x and x are equal reals,
    not convertible terms, so [wrap_one] is [≈] only:
      (cannot unify "wrap 1 x" and "x")

    ** Instance/Top/Solenoid.v: the generic initial topology is walled

    Controls: both Type-valued forms of the initial topology of a
    nat-indexed family, one universe above the points
    ([p410_init_family_up], [p410_init_union_up]); the solenoid's own
    topology at the points' universe ([p410_solenoid_space]), the limit
    ([p410_limit]), its universal property ([p410_universal]) and the
    forgetful functor's preservation of it ([p410_forget]).

    N2, N3 (UNIVERSE).  The header's THE SOLENOID IN THE TYPE-VALUED
    [Top], the form over every family T and the form over the opens of
    the factors, at the points' universe:
      The term "∀ T : (S → Type) → Type, (∀ (n : nat) (U : X n →
      Type), IsOpen (X n) U → T (λ s : S, U (t n s))) → T V" has type
      "Type@{max(o+1,<1>)}" while it is expected to have type
      "Type@{o}" (universe inconsistency: Cannot enforce o < o because
      o = o).
      The term "∀ s : S, V s → ∃ (n : nat) (U : X n → Type), (IsOpen
      (X n) U ∧ U (t n s)) ∧ ∀ s' : S, U (t n s') → V s'" has type
      "Type@{max(Set,o+1,<1>)}" while it is expected to have type
      "Type@{o}" (universe inconsistency: Cannot enforce o < o because
      o = o).

    ** Instance/Top/Solenoid.v: the points and the towers

    Controls: the points of both limits are #408's matching strings, the
    legs its projections, the matching condition Mac Lane's, and the two
    carriers one type, at [eq_refl] ([p410_points], [p410_legs],
    [p410_compat], [p410_ppoints], [p410_carriers]); the donor's
    [tower_obj] closed [Defined] instead of [Qed], otherwise its text
    ([p410_tower_obj]), with which the point sets of the three towers
    are one setoid object at [eq_refl] ([p410_flip_ptop],
    [p410_flip_group]); [EndoTower]'s generating arrow is [id ∘ w] at
    [eq_refl] and [w] up to [≈] ([p410_endo_step],
    [p410_endo_step_equiv]); Mac Lane's tower read through [tower_step]
    under an extensible universe list ([p410_tower_step]).

    N4 (CONVERSION).  The header's THE POINTS: the two solenoids' point
    sets as setoid objects, refused only by the donor's opacity:
      (cannot unify "(lim← (UCircleTower p))%invlim" and "(lim←
      (PForget ◯ PCircleTower p))%invlim")
    N5 (CONVERSION).  The header's STRENGTHS, [endo_step] against [w]:
      (cannot unify "fmap[EndoTower X w] (omega_step n)" and "w")
    N6 (BINDING).  The header's THE TOWERS, the same readback under a
    closed universe list:
      Universes <1> <2> <3> are unbound.
    (each universe followed by the File line and characters of
    [tower_step] in the stripped copy).

    ** Instance/Top/Solenoid.v: non-vacuity and p = 1

    Controls: two points for every p ([p410_two_points]), the first
    witness of [PTop_solenoid_two_points] read back at [eq_refl], which
    its [Defined] allows ([p410_two_points_first]); the leg at stage 0
    identifies two points for 1 < p ([p410_mu0]); the solenoid at p = 1
    is isomorphic to the circle in [Top] and in [PTopCat]
    ([p410_one_iso], [p410_pone_iso]).

    ** Instance/Top/Solenoid/Presentations.v: one tower, two solenoids

    Controls: the underlying towers agree ([p410_towers_agree]); the
    group solenoid's points are the matching strings at [eq_refl]
    ([p410_group_points]); the identity isomorphism between the two
    point setoids ([p410_points_iso]); the fibre of μ_0 over 0 at
    [eq_refl] ([p410_fibre_carrier]), isomorphic in [Ab] to the p-adic
    integers ([p410_Zp_iso]), whose 1 is the unit string at [eq_refl]
    ([p410_zp_one]).

    N7 (CONVERSION).  The header's THE GROUP SOLENOID, the two setoid
    objects:
      (cannot unify "SolPoints p" and "fobj[Ab_Forget] (GSolenoid p)")

    ** Instance/Top/Solenoid/Presentations.v: the covering

    Controls: over [PTopCat], each sheet homeomorphic to the arc by the
    restriction of [pwrap p] ([p410_pcover], [p410_pcover_to]); over the
    Type-valued [Top], the ball subspace of the arc a space at the
    points' universe ([p410_tarc_space]) with the subspace's universal
    property ([p410_csub_universal]), the Prop-valued arc its squash at
    [eq_refl] ([p410_arc_squash]), each sheet homeomorphic to the arc by
    the restriction of [wrap p] ([p410_cover], [p410_cover_to]), the
    evenly covered neighbourhood ([p410_evenly]); the book's subspace
    predicate at the arc, one universe up ([p410_tsub_arc_whole]).

    N8 (UNIVERSE).  The header's THE COVERING PROPERTY, the book's
    subspace predicate supplied as the opens of a space at the points'
    universe:
      The term "tsub_open Circle (csub_setoid (tarc y)) (csub_incl_map
      (tarc y))" has type "(csub_setoid@{o} (tarc@{o} y) → Type@{o}) →
      Type@{o1}" while it is expected to have type "(csub_setoid@{o}
      (tarc@{o} y) → Type@{o}) → Type@{o}" (universe inconsistency:
      Cannot enforce o1 <= o because o < o1).

    ** The constructive reals: a readback, not a refutation

    [Print Assumptions] of [solenoid_limit], [CircleGroup],
    [Zp_fibre_iso], [wrap_sheet_iso] and [pwrap_sheet_iso], near the end
    of this file, each print "Closed under the global context": the
    circle is built on the standard library's constructive Cauchy reals,
    which carry no axiom, where the classical [R] carries
    [ClassicalDedekindReals.sig_forall_dec] (Instance/Top/Circle.v's
    header).  A [Print Assumptions] cannot refuse, so these lines are
    readbacks and guard nothing; the Makefile's print-assumptions gate
    is where closure is kept.  By the same command all forty-five
    constants of this file, the obligation of [p410_tower_obj] among
    them, are closed under the global context.

    NOT PINNED HERE.  (a) [About] readbacks as such, the headers' [Set]
    censuses and their attributions to first carriers, and the
    universes [PTop_solenoid_two_points] gains from its [Defined] body.
    (b) Flip censuses and the closure of the targets under [Print
    Assumptions]: measurements of the build rather than of commands.
    (c) The refusals of closed universe lists that Coq 8.19.2 and 8.20.1
    make and Rocq 9.1.1 does not ([open_bounded_inter], [sol_lift_cont],
    [zp_coord_respects], [pwrap_evenly_covered]): a file that compiles
    under all three cannot pin a refusal made by only two.  (d) Whether
    the Prop-valued arc is open in the Type-valued [Circle]: the targets
    do not state it, and an absence has no command.  (e) The absences
    the headers record
    (no complex numbers, no fundamental group, no topological group, no
    subspace topology on the fibre): an absence has no command.

    The guard block at the end names the three hundred and thirty-six
    constants of the three targets, so that a rename breaks this file:
    ninety-four of Instance/Top/Circle.v, seventy-eight of Instance/Top/
    Solenoid.v and one hundred and sixty-four of Instance/Top/Solenoid/
    Presentations.v.  They are exactly the entries [Print Module] gives
    for each, forty-five [Program] obligations among them; the targets
    declare no record and no inductive, so there is no constructor to
    add.  Under the full import list each short name denotes the
    target's constant ([Locate] lists it first; [Circle] and [Solenoid]
    also name modules, and [wrap] also an Ltac of the standard library),
    and the [Program] obligations, which [Import] does not make visible
    by the short name, are written with their module's last component. *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Circle.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.InverseLimit.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Solenoid.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Zp.
Require Import Category.Instance.Top.Solenoid.Presentations.

Generalizable All Variables.

Open Scope category_scope.

(** ** Instrument: the refutation keyword is live *)

(* The instrument *)
Fail Check p410_absent_name.

(** ** Instance/Top/Circle.v: the circle and its p-fold map *)

(* CONTROL: the points of the circle, the underlying maps of the two
   wrapping maps, and the wrapping map at 1 up to [≈]. *)
Example p410_circle_points@{o} : top_carrier Circle@{o} = Circle_setoid@{o}
  := eq_refl.

Example p410_wrap_map@{h o | o < h +} (p : positive) :
  continuous_map (wrap@{h o} p) = circ_mul@{o} p := eq_refl.

Example p410_pwrap_map@{o so | o < so +} (p : positive) :
  pmap (pwrap@{o so} p) = circ_mul@{o} p := eq_refl.

Definition p410_wrap_one@{h o | o < h +} :
  wrap@{h o} 1 ≈ @id Top@{h o} Circle@{o} := wrap_one.

(* N1 *)
Fail Example p410_wrap_one_point@{h o | o < h +} (x : CReal) :
  continuous_map (wrap@{h o} 1) x = x := eq_refl.

(* CONTROL: the circle's equality is propositional, the circle has two
   distinct points, and its points lift to the hom universe. *)
Definition p410_circ_prop@{o} : PropEquiv@{o o} (is_setoid Circle_setoid@{o})
  := circ_PropEquiv.

Definition p410_circle_two@{o} :
  @equiv _ Circle_setoid@{o} (inject_Q (1 # 2)) (inject_Q 0) → False :=
  circle_half_not_zero.

Definition p410_circle_lift@{h o hs | o < h, h < hs +} :
  @Isomorphism Sets@{h hs} (Setoid_Lift@{o h} Circle_setoid@{o})
    Circle_setoid@{h} := circle_lift_iso.

(** ** Instance/Top/Solenoid.v: the generic initial topology is walled *)

(* CONTROL: both Type-valued forms of the initial topology of a
   nat-indexed family, one universe above the points. *)
Definition p410_init_family_up@{o o1 | o < o1 +} (S : SetoidObject@{o o})
  (X : nat → TopSpace@{o}) (t : ∀ n, SetoidMorphism@{o o o} S (X n))
  (V : S → Type@{o}) : Type@{o1} :=
  ∀ T : (S → Type@{o}) → Type@{o},
    (∀ n (U : X n → Type@{o}), IsOpen (X n) U → T (fun s => U (t n s))) →
    T V.

Definition p410_init_union_up@{o o1 | o < o1 +} (S : SetoidObject@{o o})
  (X : nat → TopSpace@{o}) (t : ∀ n, SetoidMorphism@{o o o} S (X n))
  (V : S → Type@{o}) : Type@{o1} :=
  ∀ s, V s → { n : nat & { U : X n → Type@{o} &
     (IsOpen (X n) U * U (t n s) * ∀ s', U (t n s') → V s')%type } }.

(* N2 *)
Fail Definition p410_init_family@{o} (S : SetoidObject@{o o})
  (X : nat → TopSpace@{o}) (t : ∀ n, SetoidMorphism@{o o o} S (X n))
  (V : S → Type@{o}) : Type@{o} :=
  ∀ T : (S → Type@{o}) → Type@{o},
    (∀ n (U : X n → Type@{o}), IsOpen (X n) U → T (fun s => U (t n s))) →
    T V.

(* N3 *)
Fail Definition p410_init_union@{o} (S : SetoidObject@{o o})
  (X : nat → TopSpace@{o}) (t : ∀ n, SetoidMorphism@{o o o} S (X n))
  (V : S → Type@{o}) : Type@{o} :=
  ∀ s, V s → { n : nat & { U : X n → Type@{o} &
     (IsOpen (X n) U * U (t n s) * ∀ s', U (t n s') → V s')%type } }.

(* CONTROL: the solenoid's own topology sits at the points' universe, and
   it is the limit in [Top], characterised by its universal property. *)
Definition p410_solenoid_space@{s o so | o < so +} (p : positive) :
  TopSpace@{o} := Solenoid@{s o so} p.

Definition p410_limit@{s o so h r | o < so, o < h +} (p : positive) :
  Limit@{r s h h} (CircleTower@{s h o} p) := solenoid_limit@{s o so h r} p.

Definition p410_universal@{s o so h + | o < so, o < h +} (p : positive)
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} Z (SolPoints@{s o so} p)) :
  Continuous@{h o} Z (Solenoid@{s o so} p) g ↔
  (∀ j, Continuous@{h o} Z Circle@{o}
          (setoid_morphism_compose (sol_pr p j) g)) :=
  solenoid_universal p Z g.

Definition p410_forget@{s o so h hs + | o < so, o < h, h < hs +}
  (p : positive) :
  IsLimitCone (FCone Top_Forget@{o h hs} (sol_cone@{s o so h} p)) :=
  solenoid_forget_preserves p.

(** ** Instance/Top/Solenoid.v: the points, at [eq_refl] *)

(* CONTROL: the points of both limits are #408's matching strings, the
   legs its projections, and the matching condition Mac Lane's. *)
Example p410_points@{s o so h + | o < so, o < h +} (p : positive) :
  top_carrier (vertex_obj[@limit_cone _ _ _ (solenoid_limit@{s o so h _} p)])
  = inverse_limit (UCircleTower@{s o so} p) := eq_refl.

Example p410_legs@{s o so h + | o < so, o < h +} (p : positive) (n : nat) :
  continuous_map
    (cone_leg (@limit_cone _ _ _ (solenoid_limit@{s o so h _} p)) n)
  = tower_proj (UCircleTower@{s o so} p) n := eq_refl.

Example p410_compat@{s o so + | o < so +} (p : positive)
  (x : Sets_iprod_obj (fun n : nat => fobj[UCircleTower@{s o so} p] n)) :
  tower_compat (UCircleTower@{s o so} p) x
  = (∀ n : nat, circ_eq (CReal_mult (posR p) (x (S n))) (x n)) := eq_refl.

Example p410_ppoints@{s o so + | o < so +} (p : positive) :
  pt_carrier (PSolenoid@{s o so _} p)
  = inverse_limit (PForget@{o so} ◯ PCircleTower@{s o so} p) := eq_refl.

Example p410_carriers@{s o so + | o < so +} (p : positive) :
  carrier (SolPoints@{s o so} p)
  = carrier (pt_carrier (PSolenoid@{s o so _} p)) := eq_refl.

(* CONTROL: [Instance/Sets/InverseLimit.v]'s [tower_obj] with its
   setoid obligation closed [Defined] instead of [Qed], otherwise
   textually the donor's; with it the three towers' point sets are one
   setoid object at [eq_refl]. *)
Program Definition p410_tower_obj (F : Omega^op ⟶ Sets) : obj[Sets] := {|
  carrier   := { x : Sets_iprod_obj (fun n : nat => F n) & tower_compat F x };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  constructor.
  - intros p n; reflexivity.
  - intros p q Hpq n; symmetry; exact (Hpq n).
  - intros p q r Hpq Hqr n; transitivity (`1 q n);
    [exact (Hpq n)|exact (Hqr n)].
Defined.

Example p410_flip_ptop (p : positive) :
  p410_tower_obj (UCircleTower p) = p410_tower_obj (PForget ◯ PCircleTower p)
  := eq_refl.

Example p410_flip_group (p : positive) :
  p410_tower_obj (UCircleTower p)
  = p410_tower_obj (Ab_Forget ◯ GroupTower p) := eq_refl.

(* N4 *)
Fail Example p410_points_ptop (p : positive) :
  inverse_limit (UCircleTower p) = inverse_limit (PForget ◯ PCircleTower p)
  := eq_refl.

(** ** Instance/Top/Solenoid.v: the towers *)

(* CONTROL: the generating arrow of [EndoTower] is [id ∘ w] on the nose
   and [w] up to [≈]. *)
Example p410_endo_step {C : Category} (X : obj[C]) (w : X ~{C}~> X)
  (n : nat) : fmap[EndoTower X w] (omega_step n) = id ∘ w := eq_refl.

Definition p410_endo_step_equiv {C : Category} (X : obj[C])
  (w : X ~{C}~> X) (n : nat) : fmap[EndoTower X w] (omega_step n) ≈ w :=
  endo_step_equiv X w n.

(* N5 *)
Fail Example p410_endo_step_w {C : Category} (X : obj[C])
  (w : X ~{C}~> X) (n : nat) : fmap[EndoTower X w] (omega_step n) = w
  := eq_refl.

(* CONTROL: Mac Lane's tower read back through [tower_step] with an
   extensible universe list. *)
Example p410_tower_step@{s h o + | o < h +} (p : positive) (n : nat) :
  fmap[CircleTower@{s h o} p] (tower_step n) = id ∘ wrap p := eq_refl.

(* N6 *)
Fail Example p410_tower_step_closed@{s h o | o < h} (p : positive)
  (n : nat) : fmap[CircleTower@{s h o} p] (tower_step n) = id ∘ wrap p
  := eq_refl.

(** ** Instance/Top/Solenoid.v: non-vacuity, and p = 1 *)

(* CONTROL: two points for every p, read back through the [Defined]
   witness; the leg at stage 0 not injective for 1 < p; the solenoid at
   p = 1 isomorphic to the circle in both categories. *)
Definition p410_two_points@{s o so | o < so +} (p : positive) :
  @equiv _ (SolPoints@{s o so} p) (zero_string@{s o so} p)
    (half_string@{s o so} p) → False := solenoid_two_points p.

Example p410_two_points_first@{s o so + | o < so +} (p : positive) :
  projT1 (PTop_solenoid_two_points p) = zero_string@{s o so} p
  := eq_refl.

Definition p410_mu0@{s o so | o < so +} (p : positive) (Hp : (1 < p)%positive) :
  (sol_pr@{s o so} p 0 (unit_string p) ≈ sol_pr p 0 (zero_string p)) *
  (@equiv _ (SolPoints@{s o so} p) (unit_string p) (zero_string p) → False) :=
  (unit_string_over_zero p, unit_string_not_zero p Hp).

Definition p410_one_iso@{s o so h | o < so, o < h +} :
  @Isomorphism Top@{h o} (Solenoid@{s o so} 1) Circle@{o} := solenoid_one_iso.

Definition p410_pone_iso@{s o so r | o < so +} :
  @Isomorphism PTopCat@{o so} (PSolenoid@{s o so r} 1) PCircle@{o} :=
  PTop_solenoid_one_iso.

(** ** Instance/Top/Solenoid/Presentations.v: one tower, two solenoids *)

(* CONTROL: the underlying towers agree; the group solenoid sits on the
   same strings; the two point setoids are related by the identity
   isomorphism; the transparent copy above reads them as one. *)
Definition p410_towers_agree@{s u o so +} (p : positive) :
  PForget@{o so} ◯ PCircleTower@{s o so} p
    ≈ Ab_Forget@{u so o} ◯ GroupTower@{s u o} p := towers_agree p.

Example p410_group_points@{s u o so r | o < u, o < so +} (p : positive) :
  Ab_Forget@{u so o} (GSolenoid@{s u o so r} p)
  = inverse_limit (Ab_Forget@{u so o} ◯ GroupTower@{s u o} p) := eq_refl.

Definition p410_points_iso@{s u o so r | o < u, o < so +} (p : positive) :
  SolPoints@{s o so} p
    ≅[Sets@{o so}] Ab_Forget@{u so o} (GSolenoid@{s u o so r} p) :=
  solenoid_points_iso p.

(* N7 *)
Fail Example p410_points_group@{s u o so r | o < u, o < so +}
  (p : positive) :
  SolPoints@{s o so} p = Ab_Forget@{u so o} (GSolenoid@{s u o so r} p)
  := eq_refl.

(* CONTROL: the fibre of μ_0 over 0 is the p-adic integers, additively,
   and the p-adic 1 is the unit string. *)
Example p410_fibre_carrier@{s u o so r | o < u, o < so +} (p : positive) :
  carrier (cmon_setoid (SolFibre@{s u o so r} p))
  = { x : SolPoints@{s o so} p &
      circ_eq@{o} (sol_pr@{s o so} p 0 x) (inject_Q 0) } := eq_refl.

Definition p410_Zp_iso@{s u o so r | o < u, o < so +} (p : positive)
  (Hp : (1 < p)%positive) :
  @Isomorphism Ab@{u o} (ZpAb@{s o so} p) (SolFibre@{s u o so r} p) :=
  Zp_fibre_iso p Hp.

Example p410_zp_one@{s u o so r | o < u, o < so +} (p : positive)
  (Hp : (1 < p)%positive) :
  `1 (projT1 (cmon_map (zp_to_fibre@{s u o so r} p Hp)
                (rig_one (Zp@{o o o o so s so o so} ZComm@{o o o} (Zpos p)))))
  = `1 (unit_string@{s o so} p) := eq_refl.

(** ** Instance/Top/Solenoid/Presentations.v: the covering *)

(* CONTROL: over [PTopCat], each sheet is homeomorphic to the arc by the
   restriction of [pwrap p]. *)
Definition p410_pcover@{o so | o < so +} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) :
  @Isomorphism PTopCat@{o so} (SheetSpace@{o} p y k) (ArcSpace@{o} y) :=
  pwrap_sheet_iso p y k Hk.

Example p410_pcover_to@{o so | o < so +} (p : positive) (y : CReal)
  (k : Z) (Hk : (0 <= k < Zpos p)%Z) (b : SheetSpace@{o} p y k) :
  proj1_sig (pmap (to (pwrap_sheet_iso@{o so} p y k Hk)) b)
  = circ_mul@{o} p (proj1_sig b) := eq_refl.

(* CONTROL: over the Type-valued [Top], the ball subspace of the circle is
   a space at the points' universe, with the subspace's universal
   property; the arc is its Prop-valued twin squashed; each sheet is
   homeomorphic to the arc by the restriction of [wrap p]. *)
Definition p410_tarc_space@{o} (y : CReal) : TopSpace@{o} := TArc@{o} y.

Definition p410_csub_universal@{h o | o < h +}
  (P : Circle_setoid@{o} → Type@{o}) (Z : TopSpace@{o})
  (g : SetoidMorphism@{o o o} Z (csub_setoid@{o} P)) :
  Continuous@{h o} Z (CSub@{o} P) g ↔
  Continuous@{h o} Z Circle@{o} (setoid_morphism_compose (csub_incl_map P) g)
  := csub_universal P Z g.

Example p410_arc_squash@{o} (y x : CReal) :
  in_arc@{o} y x = inhabited (cint@{o} y (1 # 4) x) := eq_refl.

Definition p410_cover@{h o | o < h +} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) :
  @Isomorphism Top@{h o} (TSheet@{o} p y k) (TArc@{o} y) :=
  wrap_sheet_iso p y k Hk.

Example p410_cover_to@{h o | o < h +} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) (b : TSheet@{o} p y k) :
  projT1 (continuous_map (to (wrap_sheet_iso@{h o} p y k Hk)) b)
  = circ_mul@{o} p (projT1 b) := eq_refl.

Definition p410_evenly@{o} (p : positive) (y : CReal) :
  (IsOpen Circle@{o} (tarc@{o} y) * tarc@{o} y y *
   (∀ k, IsOpen Circle@{o} (tsheet@{o} p y k)) *
   (∀ k k' (z : Circle_setoid@{o}),
      tsheet@{o} p y k z → tsheet@{o} p y k' z → k = k') *
   (∀ z : Circle_setoid@{o}, tarc@{o} y (CReal_mult (posR p) z)
      ↔ { k : Z & ((0 <= k < Zpos p)%Z * tsheet@{o} p y k z)%type }))%type
  := wrap_evenly_covered p y.

(* CONTROL: the book's subspace predicate at the arc, one universe up,
   is formable, with its open whole space. *)
Definition p410_tsub_arc_whole@{o o1 | o < o1 +} (y : CReal) :
  tsub_open@{o o1} Circle@{o} (csub_setoid@{o} (tarc@{o} y))
    (csub_incl_map@{o} (tarc@{o} y)) (fun _ => poly_unit@{o}) :=
  tsub_open_whole Circle (csub_setoid (tarc y)) (csub_incl_map (tarc y)).

(* N8 *)
Fail Definition p410_tsub_arc@{o o1 | o < o1 +} (y : CReal) :
  TopSpace@{o} := {|
  top_carrier   := csub_setoid@{o} (tarc@{o} y);
  IsOpen        := tsub_open@{o o1} Circle@{o} (csub_setoid@{o} (tarc@{o} y))
                     (csub_incl_map@{o} (tarc@{o} y));
  open_respects := tsub_open_respects Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y));
  open_proper   := tsub_open_proper Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y));
  open_union    := tsub_open_union Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y));
  open_whole    := tsub_open_whole Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y));
  open_inter    := tsub_open_inter Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y))
|}.

(** ** The constructive reals: a readback, not a refutation *)

Print Assumptions solenoid_limit.
Print Assumptions CircleGroup.
Print Assumptions Zp_fibre_iso.
Print Assumptions wrap_sheet_iso.
Print Assumptions pwrap_sheet_iso.

(** ** Guard: the constants of the three targets, all closed under the global
    context *)

(* Instance/Top/Circle.v: 94 names. *)
Check cball.
Check cball_mono.
Check cball_mul.
Check cball_of_eq.
Check cball_of_rball.
Check cball_open.
Check cball_triang.
Check cint.
Check cint_balls.
Check cint_centre.
Check cint_open.
Check cint_sub.
Check circ_eq.
Check circ_eq_of_creal.
Check circ_eq_of_peq.
Check circ_eq_refl.
Check circ_eq_sym.
Check circ_eq_trans.
Check circ_eq_translate.
Check circ_eq_witness_unique.
Check circ_mul.
Check circ_peq.
Check circ_peq_of_eq.
Check circ_PropEquiv.
Check circ_q.
Check circ_setoid.
Check Circle.
Check Circle.circ_mul_obligation_1.
Check Circle.circ_q_obligation_1.
Check Circle.circ_setoid_obligation_1.
Check Circle.circle_lift_iso_obligation_1.
Check Circle.circle_lift_iso_obligation_2.
Check Circle.circle_lift_iso_obligation_3.
Check Circle.circle_lift_iso_obligation_4.
Check Circle.creal_setoid_obligation_1.
Check Circle.line_mul_obligation_1.
Check circle_half_not_zero.
Check circle_lift_iso.
Check circle_open_balls.
Check Circle_points.
Check Circle_setoid.
Check creal_inject_Q_injective.
Check creal_inject_Z_injective.
Check creal_inject_Z_mult.
Check creal_minus_self.
Check creal_setoid.
Check cround.
Check cround_ball.
Check cround_between.
Check cround_spec.
Check inject_Q_minus.
Check inject_Q_minus_int.
Check inject_Q_minus_int_inv.
Check inject_Q_pos_le.
Check line_mul.
Check line_mul_cont.
Check pcball_open.
Check PCircle.
Check pcircle_open_balls.
Check PCircle_points.
Check pline_mul_cont.
Check posR.
Check posR_nonneg.
Check PRLine.
Check prline_mul.
Check propen.
Check propen_inter.
Check propen_proper.
Check propen_respects.
Check propen_union.
Check propen_whole.
Check pwrap.
Check pwrap_map.
Check pwrap_one.
Check q_half_half.
Check q_half_pos.
Check q_scale_pos.
Check rball.
Check rball_center.
Check rball_mono.
Check rball_mul.
Check rball_of_cball.
Check RLine.
Check rline_mul.
Check RLine_setoid.
Check ropen.
Check ropen_inter.
Check ropen_proper.
Check ropen_respects.
Check ropen_union.
Check ropen_whole.
Check wrap.
Check wrap_map.
Check wrap_one.

(* Instance/Top/Solenoid.v: 78 names. *)
Check CircleTower.
Check CircleTower_step.
Check const_string_cont.
Check const_string_map.
Check endo_hom.
Check endo_hom_comp.
Check endo_hom_fmap.
Check endo_hom_id.
Check endo_hom_respects.
Check endo_hom_trans.
Check endo_step.
Check endo_step_equiv.
Check EndoTower.
Check EndoTower_map.
Check half_string.
Check half_string_coord.
Check one_compat.
Check open_bounded_inter.
Check PCircleTower.
Check PCircleTower_points.
Check PCircleTower_step.
Check pconst_string_cont.
Check pconst_string_map.
Check posR_scale.
Check ppow.
Check psol_leg.
Check PSolenoid.
Check PTop_solenoid_coarsest.
Check PTop_solenoid_forget_preserves.
Check PTop_solenoid_leg_map.
Check PTop_solenoid_limit.
Check PTop_solenoid_one_iso.
Check PTop_solenoid_open_forced.
Check PTop_solenoid_points.
Check PTop_solenoid_two_points.
Check PTop_solenoid_universal.
Check scaled_compat.
Check sol_acone.
Check sol_compat.
Check sol_cone.
Check sol_forget_med.
Check sol_leg.
Check sol_leg_cont.
Check sol_lift_cont.
Check sol_med.
Check sol_med_map.
Check sol_pr.
Check sol_tower_compat.
Check Solenoid.
Check Solenoid.const_string_map_obligation_1.
Check Solenoid.pconst_string_map_obligation_1.
Check Solenoid.sol_forget_med_obligation_1.
Check Solenoid.sol_med_map_obligation_1.
Check Solenoid.solenoid_limit_obligation_1.
Check Solenoid.solenoid_limit_obligation_2.
Check solenoid_coarsest.
Check solenoid_forget_preserves.
Check solenoid_leg_map.
Check solenoid_limit.
Check solenoid_one_iso.
Check solenoid_points.
Check solenoid_points_agree.
Check solenoid_two_points.
Check solenoid_universal.
Check SolPoints.
Check sopen.
Check sopen_inter.
Check sopen_proper.
Check sopen_respects.
Check sopen_union.
Check sopen_whole.
Check string_one_const.
Check UCircleTower.
Check unit_string.
Check unit_string_not_zero.
Check unit_string_over_zero.
Check zero_compat.
Check zero_string.

(* Instance/Top/Solenoid/Presentations.v: 164 names. *)
Check arc_shift.
Check ArcSpace.
Check circ_mul_sheet_lift.
Check circ_pow.
Check circ_pow_map.
Check CircleGroup.
Check CircleTower_points.
Check creal_fibre_add.
Check creal_recover.
Check creal_scale_back.
Check CSub.
Check csub_coarsest.
Check csub_incl.
Check csub_incl_cont.
Check csub_incl_map.
Check csub_lift_cont.
Check csub_open.
Check csub_open_inter.
Check csub_open_proper.
Check csub_open_respects.
Check csub_open_union.
Check csub_open_whole.
Check csub_setoid.
Check csub_universal.
Check dpow_ppow.
Check fibre_coord.
Check fibre_coord_spec.
Check fibre_exhaust.
Check fibre_int.
Check fibre_int_spec.
Check fibre_int_step.
Check fibre_pt.
Check fibre_pt_distinct.
Check fibre_pt_over.
Check fibre_real_base.
Check fibre_real_diff.
Check fibre_real_step.
Check fibre_real_sum.
Check fibre_real_zero.
Check fibre_to_zp.
Check fibre_to_zp_map.
Check fibre_to_zp_pt.
Check group_solenoid_points.
Check group_step_fn.
Check GroupSolenoid.
Check GroupTower.
Check GroupTower_points.
Check GroupTower_step.
Check gsol_leg.
Check gsol_leg_map.
Check gsol_neg_coord.
Check gsol_plus_coord.
Check gsol_zero_coord.
Check GSolenoid.
Check in_arc.
Check in_arc_centre.
Check in_arc_open.
Check in_arc_shift.
Check in_arc_squash.
Check in_sheet.
Check in_sheet_disjoint.
Check in_sheet_open.
Check in_sheet_preimage.
Check int_near_zero.
Check inv_p_mul.
Check inv_p_unit.
Check mul_ball.
Check p_sheet_lift.
Check Presentations.circ_pow_obligation_1.
Check Presentations.circ_pow_obligation_2.
Check Presentations.CircleGroup_obligation_1.
Check Presentations.CircleGroup_obligation_2.
Check Presentations.CircleGroup_obligation_3.
Check Presentations.CircleGroup_obligation_4.
Check Presentations.CircleGroup_obligation_5.
Check Presentations.CircleGroup_obligation_6.
Check Presentations.csub_incl_map_obligation_1.
Check Presentations.csub_setoid_obligation_1.
Check Presentations.fibre_to_zp_map_obligation_1.
Check Presentations.fibre_to_zp_obligation_1.
Check Presentations.fibre_to_zp_obligation_2.
Check Presentations.pwrap_sheet_iso_obligation_1.
Check Presentations.pwrap_sheet_iso_obligation_2.
Check Presentations.pwrap_sheet_map_obligation_1.
Check Presentations.sheet_lift_map_obligation_1.
Check Presentations.solenoid_points_iso_obligation_1.
Check Presentations.solenoid_points_iso_obligation_2.
Check Presentations.solenoid_points_iso_obligation_3.
Check Presentations.solenoid_points_iso_obligation_4.
Check Presentations.tsheet_lift_map_obligation_1.
Check Presentations.wrap_sheet_iso_obligation_1.
Check Presentations.wrap_sheet_iso_obligation_2.
Check Presentations.wrap_sheet_map_obligation_1.
Check Presentations.Zp_fibre_iso_obligation_1.
Check Presentations.Zp_fibre_iso_obligation_2.
Check Presentations.zp_to_fibre_map_obligation_1.
Check Presentations.zp_to_fibre_obligation_1.
Check Presentations.zp_to_fibre_obligation_2.
Check pspace_step_fn.
Check pwrap_evenly_covered.
Check pwrap_sheet.
Check pwrap_sheet_cont.
Check pwrap_sheet_iso.
Check pwrap_sheet_iso_to.
Check pwrap_sheet_map.
Check q_fibre_add.
Check q_fibre_base.
Check q_fibre_diff.
Check q_fibre_split.
Check q_fibre_step.
Check q_fibre_unit.
Check q_fibre_zero.
Check q_p_pos.
Check q_quarter_half.
Check q_scale_le.
Check qmin_pos.
Check sheet_index.
Check sheet_lift.
Check sheet_lift_cont.
Check sheet_lift_in.
Check sheet_lift_lip.
Check sheet_lift_map.
Check sheet_lift_mor.
Check sheet_lift_respects.
Check sheet_lift_wrap.
Check SheetSpace.
Check sol_fibre_carrier.
Check solenoid_carriers_agree.
Check solenoid_equiv_agree.
Check solenoid_points_iso.
Check SolFibre.
Check space_step_fn.
Check tarc.
Check TArc.
Check tarc_centre.
Check tarc_open.
Check towers_agree.
Check tsheet.
Check TSheet.
Check tsheet_disjoint.
Check tsheet_lift_cont.
Check tsheet_lift_in.
Check tsheet_lift_map.
Check tsheet_lift_mor.
Check tsheet_open.
Check tsheet_preimage.
Check wrap_evenly_covered.
Check wrap_sheet.
Check wrap_sheet_cont.
Check wrap_sheet_iso.
Check wrap_sheet_iso_to.
Check wrap_sheet_map.
Check zp_coord.
Check zp_coord_base.
Check zp_coord_compat.
Check zp_coord_respects.
Check Zp_fibre_iso.
Check zp_one_to_unit_string.
Check zp_string.
Check zp_to_fibre.
Check zp_to_fibre_coord.
Check zp_to_fibre_map.
Check ZpAb.
Check zres_of_eq.
