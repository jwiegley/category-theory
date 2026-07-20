(** * Universe probe: the funny monoidal structure on StrictCat is Set-pinned.

    Companion to the "Universe scope" note of Instance/StrictCat/Premonoid.v.

    [Funny_Monoidal@{u} : Monoidal@{u Set}] (Instance/StrictCat/Funny.v) fixes
    the second universe of [Monoidal] — the level of StrictCat's member
    categories — at [Set], so every carrier category reached through the
    funny monoidal structure lives in [Category@{Set Set Set}].  This file
    pins the obstruction to lifting that restriction:

      - [StrictCat@{i v j v v} : Category@{i v v}] has object type
        [Category@{v v v}]: member categories at the rigid (monomorphic)
        level [v] declared below;

      - the tensor is unproblematic: [Build_Monoidal] applied to [_1] and
        [FunnyTensor] at member level [v] is accepted ([probe_tensor_ok]);

      - supplying a unitor is what fails.  The compiled [Funny_unit_left] of
        Construction/Funny/Unitors.v carries a rigid interior [Set] level
        ([Print Funny_unit_left] shows
        [from := Funny_unit_left_from@{u0 u0 u0 Set u0 u0}]), so
        [Build_Monoidal] at member level [v] reports

          universe inconsistency: Cannot enforce Set = v

        at the [unit_left] field (first [Fail] below);

      - consequently the compiled instance does not transport: casting
        [Funny_Monoidal@{i}] to [@Monoidal StrictCat@{i v j v v}] fails with
        the same message, [Monoidal@{i Set}] against [Monoidal@{i v}]
        (second [Fail] below).

    Lifting the restriction requires re-declaring the unitors with explicit
    universe binders in Construction/Funny/Unitors.v.  If that is ever done,
    the [Fail] commands here stop failing and this file breaks the build,
    flagging that the universe-scope note in Instance/StrictCat/Premonoid.v
    can be relaxed. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.Unitors.
Require Import Category.Instance.StrictCat.Funny.
Require Import Category.Structure.Monoidal.

(** A rigid member level [v], with outer levels [i] (StrictCat's objects) and
    [j] strictly above it, as StrictCat's universe constraints require. *)
Monomorphic Universe i j v.
Monomorphic Constraint v < i.
Monomorphic Constraint v < j.

(** ** Positive control: everything up to the unitors is fine at level [v].

    The partial application supplies the carrier, the unit object and the
    tensor, so the failures below are not caused by [StrictCat], [_1] or
    [FunnyTensor] at member level [v]. *)
Definition probe_tensor_ok :=
  @Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor.

(** ** The reproduction: the unitor field is where [Set] is enforced.

    Error: The term "Funny_unit_left@{_ v}" has type "1 □ x ≅ x"
    while it is expected to have type "fobj[FunnyTensor@{..}] (1, x) ≅ x"
    (universe inconsistency: Cannot enforce Set = v). *)
Fail Check (@Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor
              (fun x : Category@{v v v} => @Funny_unit_left x)).

(** ** The compiled instance is pinned: it does not transport to level [v].

    Error: The term "Funny_Monoidal" has type "Monoidal@{i Set}"
    while it is expected to have type "Monoidal@{i v}"
    (universe inconsistency: Cannot enforce Set = v). *)
Fail Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i v j v v}).

(** ** Positive control: [Funny_Monoidal] is a well-formed [Monoidal] at its
    own universe level.  This pins the two [Fail]s above to the specific
    [Set = v] universe conflict rather than to a malformed term or a renamed
    identifier: the instance exists and type-checks, it simply does not
    transport up to level [v].  Without this control a [Fail] would pass on
    any error at all. *)
Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i Set j Set Set}).
