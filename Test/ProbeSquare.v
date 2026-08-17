(** * Boundary probes for the walking commutative square

    Companion to Instance/Square.v, Instance/Square/Product.v and
    Instance/Square/Rectangle.v (issue #300, Mac Lane §II.8 Ex. 1;
    Riehl §1.6 Examples 1.6.6 and 1.6.9).  Those files make three
    strength claims whose negative side is a universe or a typing
    boundary; measurements outside the tree would not be noticed by a
    refactor, so they are pinned here.  **If the [Fail] commands below
    stop failing, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  The instrument itself was checked — wrapping [Fail] around a
    succeeding command reports "The command has not failed!" and aborts
    compilation — and each negative was compiled once with the [Fail]
    stripped, to confirm the error is the intended one and not a syntax,
    scope or resolution failure — two [cannot unify] typing errors and,
    for the rectangle, the universe inconsistency [Cannot enforce Set =
    rh] naming the declared universe itself.

    THE THREE BOUNDARIES.

    (1) THE DONOR PIN IS GONE, and this is the probe that says so.
    Before issue #300, [Build_Quiver_Standard_Eq]
    (Construction/Free/Quiver.v) elaborated to [Quiver@{u u0 Set}] — its
    edge setoid's PROOF universe silently minimized to [Set], because it
    was built from [Corelib.Classes.CRelationClasses.eq_equivalence@{u}],
    which carries one universe binder and cannot separate the carrier's
    level from the proof level.  Since [InducedFunctor] identifies the
    target category's hom and proof universes with the quiver's, EVERY
    functor out of a free or presented category was confined to a target
    [Category@{o Set Set}].  Construction/Free/Quiver/Examples.v's header
    diagnosed exactly this and called lifting it out of scope; it is
    lifted now, and section [BigTarget] below is the guard —
    [SquareFunctor], [SquareFunctor_f], [square_universal] and the
    reverse passage, all applied at a category whose three universes are
    declared strictly above [Set].  There is no [Fail] half here: the
    claim IS that nothing is rejected, so the whole guard is a positive
    control.

    (2) [Square ≅[StrictCat] _2 ∏ _2] IS NOT AN EQUALITY OF CATEGORIES.
    Instance/Square/Product.v is explicit that the two object types are
    [SquareNode] and [TwoObj * TwoObj], distinct inductives, so no
    Leibniz equality of the [Category] records is available.  The
    negative probe is the attempted [eq_refl]; the positive control is
    the isomorphism itself, at [StrictCat] and not merely at [Cat].

    (3) THE RECTANGLE'S CONVERSE IS PINNED AT [Category@{co Set Set}],
    and its forward half is not.  Instance/Square/Rectangle.v records
    that [RectFunctor] inherits [Set] from [Theory/Shapes.v]'s
    [Functor_of_Pair] (which produces a functor out of
    [_3@{u Set Set}]) through [Construction/Cylinder.v]'s [Cyl_functor]
    (which identifies the hom and proof universes of its two
    categories), while the [Diagram] section carries no pin at all.
    Both halves are probed: the forward accessors typecheck above [Set],
    and building [RectFunctor] there is rejected. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Square.
Require Import Category.Instance.Square.Product.
Require Import Category.Instance.Square.Rectangle.

Local Open Scope category_scope.

(** ** (1) The donor pin is gone

    A target category whose three universes are declared strictly above
    [Set].  Before the lift described above, forming [SquareFunctor] at
    such a target was a universe inconsistency; it now typechecks. *)

Section BigTarget.

Universes bo bh bp.
Constraint Set < bo.
Constraint Set < bh.
Constraint Set < bp.
Constraint bh <= bp.

Context (D : Category@{bo bh bp}).
Context (S : CommutingSquare D).

(** The universal property of the presented square, applied above
    [Set].  This is the guard on the [Build_Quiver_Standard_Eq]
    generalisation. *)
Check (SquareFunctor S : Square ⟶ D).

(** ...and its action on the generators, so the guard covers the
    theorems and not only the construction. *)
Check (SquareFunctor_f S).
Check (square_universal S).

(** The reverse direction was never pinned, and still is not. *)
Context (F : Square ⟶ D).

Check (CommutingSquareOfFunctor F : CommutingSquare D).
Check (square_functor_round_strict F).

End BigTarget.

(** ** (2) The 2 × 2 identification is an isomorphism, not an equality

    Positive control: the isomorphism in [StrictCat] — the strong
    reading, [≅[Cat]] in this library being an equivalence of
    categories. *)
Check (Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2)).
Check (Square_2x2_Cat_iso : Square ≅[Cat] (_2 ∏ _2)).

(** Negative: the two categories are not Leibniz-equal, their object
    types being distinct inductives.  (With the [Fail] stripped this
    reports that [Square] and [_2 ∏ _2] cannot be unified.) *)
Fail Check (eq_refl : Square = (_2 ∏ _2)).

(** Nor are their object types.  (With the [Fail] stripped: cannot
    unify [SquareNode] with [TwoObj * TwoObj].) *)
Fail Check (eq_refl : SquareNode = (TwoObj * TwoObj)%type).

(** The instrument is not a no-op: a [Fail] on a succeeding command
    aborts compilation with "The command has not failed!".  The
    following line, uncommented, would do exactly that — it is left as
    a comment because a passing build cannot contain it.

      Fail Check (Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2)).

    The controls above are the standing check that the [Fail]s are not
    passing for the wrong reason. *)

(** ** (3) The rectangle: forward unpinned, converse pinned at [Set] *)

Section BigRectangle.

Universes ro rh rp.
Constraint Set < ro.
Constraint Set < rh.
Constraint Set < rp.
Constraint rh <= rp.

Context (E : Category@{ro rh rp}).

(** Forward half: the accessors and every commutativity statement
    typecheck at a target above [Set]. *)
Context (F : Rect ⟶ E).

Check (rect_u F).
Check (rect_left_commutes F).
Check (rect_right_commutes F).
Check (rect_outer_commutes F).
Check (rect_outer_two_ways F).
Check (rect_long_through_left F).
Check (rect_long_through_right F).

(** The pasting principle carries no pin whatever — it mentions no
    shape category. *)
Check (@paste_squares E).

(** Negative half: the converse does not reach here.  (With the [Fail]
    stripped this reports a universe inconsistency, [Set] against the
    declared [rh].) *)
Context (R : CommutingRectangle E).

Fail Check (RectFunctor R : Rect ⟶ E).

End BigRectangle.

(** Positive control for the converse: at a target whose hom and proof
    universes ARE [Set] it builds, and recovers all seven generators. *)
Section SmallRectangle.

Universe so.

Context (E : Category@{so Set Set}).
Context (R : CommutingRectangle E).

Check (RectFunctor R : Rect ⟶ E).
Check (RectFunctor_u R).
Check (RectFunctor_p R).
Check (RectFunctor_r R).

End SmallRectangle.
