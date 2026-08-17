(** * Boundary probe: what is and is not definitional in the free groupoid
      and the free group.

    Companion to Construction/Free/Groupoid.v and Instance/Grp/Free.v
    (Mac Lane §II.7 Ex. 3, Riehl §4.2 Example 4).  Those files make several
    strength claims — some things hold at Leibniz [=] or by [eq_refl], others
    only up to [≈] — and a strength claim that lives only in a header is a
    claim nothing in the build would notice losing.  This file pins the
    boundary in the manner of Test/ProbeQuiverConstructions.v and
    Test/ProbeFunnyPoly.v: **if the [Fail] commands here stop failing, this
    file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very little —
    it passes just as happily when the term is ill-typed for some unrelated
    reason, or when a name has been renamed out from under it.  So each
    negative probe is paired with a positive control which must SUCCEED, and
    the controls are the headline claims themselves.

    The instrument was checked before being trusted: wrapping [Fail] around a
    command that succeeds reports "The command has not failed!" and aborts
    compilation, so [Fail] here is not a no-op.  Each negative below was also
    run with the [Fail] stripped, and the error confirmed to be a genuine
    unification or typing failure rather than a syntax, scope or universe
    error; the diagnoses are recorded beside each probe.

    The five negatives and their causes:

      - [FreeGroupoid] is not [FreeSigned].  The two share their objects and
        their hom TYPES definitionally — that is [fg_hom_type], the positive
        control, and it is the whole content of "equations merge, and never
        add" — but the [Category] records differ in their [homset] field, so
        the categories are not convertible.  The mathematical form of the
        same fact is [free_signed_not_groupoid].

      - The inverse law holds only up to [≈].  [fginv f ∘ f] is the word
        [f] followed by its reversal, which is not the empty word until the
        cancellation congruence is applied; the positive control is
        [fginv_involutive], which DOES hold at Leibniz [=] because
        [Lib/TList.v]'s [tlist_rev_involutive] does.

      - The counit of the free-group adjunction does not compute.  It is
        [from adj id], i.e. [unique_obj (ump_universal_arrows …)], and
        [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed]-opaque, so
        no reduction is available.  The unit is on the other side of that
        boundary and DOES compute, which is the positive control
        [free_group_unit_is_insert].  Instance/Grp/Free.v says so in terms
        and states the counit only up to [≈]
        ([free_group_counit_evaluates]).

      - The generator clause of the universal property is not even WELL-TYPED
        without the object agreement in scope.  Stripped of [Fail] this one
        is a typing error rather than a unification failure: [fedgemap x y e]
        has type [edges (F x) (F y)] while the clause needs
        [fobj[K] x ~> fobj[K] y], and nothing identifies those two until
        [Hobj] is available to [hom_cast] across.  This is why
        [free_groupoid_universal] nests [Hobj] INSIDE the sigma rather than
        stating a flat generator clause beside it — the nesting is forced,
        not stylistic.

      - [Deloop] does not accept an [Instance/Grp.v] group.  There are two
        records named [GrpObject] in the tree — Construction/Deloop.v's,
        layered on [MonObject], and Instance/Grp.v's, flat — and no
        converter between them, which is exactly why Instance/Grp/Free.v
        builds [grp_deloop_monoid] by hand.  The positive control is that
        [grp_deloop] does accept one. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.

Local Open Scope category_scope.

#[local] Existing Instance edgeset.

(** ** Positive controls: the definitional claims *)

(* The hom TYPES of the free groupoid and of the free category on the signed
   quiver agree on the nose: the quotient coarsens the equivalence and
   nothing else. *)
Example control_hom_type (G : Quiver) (x y : G) :
  (x ~{FreeGroupoid G}~> y) = (x ~{FreeSigned G}~> y) := eq_refl.

(* The chosen inverse of the groupoid structure IS word reversal. *)
Example control_ginv_is_reversal (G : Quiver) (x y : G)
  (f : x ~{FreeGroupoid G}~> y) :
  ginv (FreeGroupoid_IsGroupoid G) f = fginv f := eq_refl.

(* Reversal is involutive at Leibniz [=], before any quotient. *)
Check (fun (G : Quiver) (x y : G) (f : x ~{FreeGroupoid G}~> y) =>
         fginv_involutive f : fginv (fginv f) = f).

(* The generator clause of the universal property typechecks once the object
   agreement [Hobj] is in scope, and is then conjugated by [hom_cast]. *)
Check (∀ (G : Quiver) (D : Category)
         (F : QuiverHomomorphism G (QuiverOfCat D))
         (K : FreeGroupoid G ⟶ D)
         (Hobj : ∀ x : G, fobj[K] x = @fnodes _ _ F x)
         (x y : G) (e : edges x y),
       hom_cast (Hobj x) (Hobj y) (fmap[K] (fgpos e))
         ≈ @fedgemap _ _ F x y e).

(* The free functor's object part is the word group, definitionally. *)
Example control_FreeGrp_obj (X : Sets) : FreeGrp X = FreeGrpObject X
  := eq_refl.

(* The unit of the adjunction computes to the one-letter word. *)
Example control_unit_computes (X : Sets) (a : carrier X) :
  free_group_unit X a = fg_insert X a := eq_refl.

(* [Deloop] accepts an [Instance/Grp.v] group only through the bridge. *)
Check (fun H : GrpObject => grp_deloop H).

(** ** Negative probes: these commands MUST fail *)

(* The free groupoid is not the free category on the signed quiver: the
   [homset] fields differ.  (Stripped of [Fail]: "cannot unify".) *)
Fail Example probe_groupoid_is_free_category (G : Quiver) :
  FreeGroupoid G = FreeSigned G := eq_refl.

(* The inverse law is not definitional.  (Stripped of [Fail]: "Unable to
   unify ... with ...".) *)
Fail Example probe_inverse_definitional (G : Quiver) (x y : G)
  (f : x ~{FreeGroupoid G}~> y) :
  @compose (FreeGroupoid G) x y x (fginv f) f = @id (FreeGroupoid G) x
  := eq_refl.

(* The counit does not compute.  (Stripped of [Fail]: "cannot unify",
   the offending head being the opaque [ump_universal_arrows].) *)
Fail Example probe_counit_computes (H : Grp) (w : FGWord (Grp_Forget H)) :
  free_group_counit H w = free_grp_extend (@id Sets (Grp_Forget H)) w
  := eq_refl.

(* The generator clause of the universal property is not even well-typed
   without the object agreement in scope — this is why the bundled
   [free_groupoid_universal] nests [Hobj] inside the sigma.  (Stripped of
   [Fail]: a typing error on the two sides of [≈].) *)
Fail Check (∀ (G : Quiver) (D : Category)
              (F : QuiverHomomorphism G (QuiverOfCat D))
              (K : FreeGroupoid G ⟶ D)
              (x y : G) (e : edges x y),
            fmap[K] (fgpos e) ≈ @fedgemap _ _ F x y e).

(* [Deloop] does not accept an [Instance/Grp.v] group directly: it wants a
   [MonObject], and there is no coercion.  (Stripped of [Fail]: "The term
   ... has type GrpObject while it is expected to have type MonObject".) *)
Fail Check (fun H : GrpObject => Deloop H).
