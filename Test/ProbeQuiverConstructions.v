(** * Boundary probe: what is and is not definitional in the opposite and
      product quivers.

    Companion to Construction/Free/Quiver/Constructions.v (Mac Lane §II.7
    Ex. 1).  That file's headline is that the forgetful functor preserves
    opposites and products ON THE NOSE — [QuiverOfCat (C^op) = QuiverOp
    (QuiverOfCat C)] and its product analogue hold at Leibniz equality of the
    whole [Quiver] record, by [eq_refl] — while three neighbouring statements
    reach only [≈].  Its header records that the negative side was "measured
    and found NOT to reach [eq_refl]", but the measurements themselves lived
    outside the tree, so nothing in the build would notice if a refactor moved
    the boundary.  This file pins it, in the manner of Test/ProbeFunnyPoly.v:
    **if the [Fail] commands here stop failing, this file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very little — it
    passes just as happily when the term is ill-typed for some unrelated
    reason, or when a name has been renamed out from under it.  So each
    negative probe is paired with a positive control which must SUCCEED, and
    the controls are the headline claims themselves.  A rename or a change in
    the [Quiver] record breaks the controls loudly rather than turning the
    [Fail]s vacuously green.

    The instrument was checked before being trusted: wrapping [Fail] around a
    command that succeeds reports "The command has not failed!" and aborts
    compilation, so [Fail] here is not a no-op.

    The three negatives and their causes, each diagnosed rather than merely
    observed (the diagnoses are argued in Constructions.v's header, item (5)):

      - [Forgetful_preserves_fst]/[_snd]: [Fst] and [Snd] of
        Construction/Product.v are [Program Instance]s, so their
        [fmap_respects] field is an opaque obligation (the tree runs
        [Unset Transparent Obligations], Lib/Tactics.v:36).  The node and edge
        actions do agree definitionally; it is respectfulness alone that
        blocks.

      - [QuiverSwap_invol]: the node action of the twice-swapped quiver is
        [fun x => (fst x, snd x)], and surjective pairing is not definitional
        for the standard library's [prod] — it holds on a constructor and not
        on a variable.

      - [prod_setoid]: Lib/Datatypes.v:139's global instance has exactly the
        [equiv] that Constructions.v's [edgeset_prod] spells out, but an opaque
        [setoid_equiv].  Since [Setoid] has primitive projections with eta,
        conversion compares that field, and an opaque one defeats the
        definitional agreement.  This is why [edgeset_prod] writes its
        [Equivalence] fields out by hand instead of reusing the instance —
        a deliberate non-reuse, and therefore worth guarding. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Constructions.

Local Open Scope category_scope.

(** ** Positive controls: the headline claims are definitional.

    These must SUCCEED.  They are restated here rather than cited from
    Constructions.v so that this file measures the claims independently of the
    constants that assert them. *)

Definition control_op (C : Category) :
  QuiverOfCat (C^op) = QuiverOp (QuiverOfCat C) := eq_refl.

Definition control_prod (C D : Category) :
  QuiverOfCat (C ∏ D) = QuiverProd (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

Definition control_invol (G : Quiver) : QuiverOp (QuiverOp G) = G := eq_refl.

(** ** Negative probes: the boundary.

    These must FAIL.  Each is the [eq_refl] strengthening of a statement that
    Constructions.v delivers at [≈]. *)

(* [Fst]/[Snd] are [Program Instance]s: [fmap_respects] is opaque. *)
Fail Definition probe_fst_strict (C D : Category) :
  QuiverHomomorphismOfFunctor _ _ (@Fst C D)
    = @QuiverFst (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

Fail Definition probe_snd_strict (C D : Category) :
  QuiverHomomorphismOfFunctor _ _ (@Snd C D)
    = @QuiverSnd (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

(* Surjective pairing is not definitional for [prod]. *)
Fail Definition probe_swap_invol_strict (G H : Quiver) :
  @compose QuiverCategory (QuiverProd G H) (QuiverProd H G) (QuiverProd G H)
    QuiverSwap QuiverSwap
    = @id QuiverCategory (QuiverProd G H) := eq_refl.

(** ** The [prod_setoid] non-reuse.

    [QuiverProd_alt] is [QuiverProd] with Lib/Datatypes.v's global
    [prod_setoid] in place of [edgeset_prod].  It is a perfectly good quiver —
    that definition succeeds — but the preservation lemma is then no longer
    definitional, which is the whole reason [edgeset_prod] exists. *)

Definition QuiverProd_alt (G H : Quiver) : Quiver := {|
  nodes   := (@nodes G * @nodes H)%type;
  edges   := fun x y =>
    (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type;
  edgeset := fun x y =>
    @prod_setoid _ _ (@edgeset G (fst x) (fst y)) (@edgeset H (snd x) (snd y))
|}.

Fail Definition probe_prod_setoid_strict (C D : Category) :
  QuiverOfCat (C ∏ D) = QuiverProd_alt (QuiverOfCat C) (QuiverOfCat D)
    := eq_refl.

(** ** The scoped universal property.

    Constructions.v proves [QuiverPair_unique] with LEIBNIZ hypotheses, noting
    that the [≈]-hypothesis form would need respectfulness of [QuiverPair],
    which is not proved.  [QuiverPair_eta] is likewise delivered at [≈].  Both
    weakenings are real, not defensive: the strengthenings fail. *)

Fail Definition probe_pair_eta_strict {G H K : Quiver}
  (M : QuiverHomomorphism K (QuiverProd G H)) :
  QuiverPair (@compose QuiverCategory _ _ _ QuiverFst M)
             (@compose QuiverCategory _ _ _ QuiverSnd M) = M := eq_refl.
