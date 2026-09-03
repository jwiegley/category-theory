(** * Boundary probe for the orthogonal-complement connection (#385)

    This file exists for what an in-file [Fail] cannot do: survive a
    rename.  A negative written inside the module it guards is renamed in
    lockstep with the constant it names and so stays green when that
    constant disappears; a negative written HERE breaks loudly.

    The [Require] list below is the target's own list, plus the target.  A
    short prefix is exactly what makes a probe pass for the wrong reason
    -- a missing coercion or notation can turn an intended unification
    mismatch into an "illegal application" -- so the list is mirrored
    rather than trimmed.

    ** THE NEGATIVES, BY KIND

    Six negatives plus one instrument check.  The kinds are told apart by
    the error TEXT rather than by a label, and every one was stripped ONE
    AT A TIME, compiled alone, and its whole message read.

      TYPING       a plain "has type ... while it is expected to have
                   type ...", with NO "cannot unify" and NO universe
                   clause.  Negatives 2, 3 and 4.

      CONVERSION   "cannot unify" between two inhabitants of ONE type.
                   Negatives 5 and 6.

      FORMABILITY  ends in "universe inconsistency: Cannot enforce ...".
                   Negative 7.

    Every constant a negative names also appears in a command OUTSIDE any
    [Fail], donors included -- a guard that names a constant only inside
    its own [Fail] is vacuous, and the control block below was written by
    reading the [Fail] commands rather than from memory. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Grp.Galois.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.InnerProduct.Galois.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Negative 1: the instrument *)

(* If [Fail] were inert -- a missing scope, a stray [Set Silent] -- this
   would pass and every other negative below would be worthless. *)
Fail Check probe385_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(** ** Controls for the constants the negatives name *)

Check @subset_le.
Check @subset_le_preorder.
Check @subset_le_antisym.
Check @Subsets.
Check @op_rel.
Check @op_PreOrder.
Check @Proset.
Check @GaloisConnection.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_truth.
Check @AdjointOnTheRight.
Check @AdjointOnTheLeft.
Check @PerpRel.
Check @Build_PerpRel.
Check @perp.
Check @perp_sym.
Check @perp_respects.
Check @perp_respects_iff.
Check @perp_set.
Check @perp_set_mem.
Check @perp_transpose.
Check @perp_set_antitone.
Check @perp_set_respects.
Check @perp_galois.
Check @perp_galois_l_is_r.
Check @perp_to_is_from_swapped.
Check @perp_PreOrder_l.
Check @perp_PreOrder_r.
Check @perp_unit.
Check @perp_counit.
Check @perp_unit_is_counit.
Check @perp_triple.
Check @ClosedPerp.
Check @perp_set_closed.
Check @closed_perp_iff.
Check @PerpFunctor.
Check @PerpFunctor_r.
Check @perp_adjunction.
Check @PerpOp.
Check @perp_AdjointOnTheRight.
Check @perp_aor_to.
Check @perp_aor_from.
Check @zz_setoid.
Check @zdot.
Check @ZZPerp.
Check @zz_sub.
Check @zz_e1.
Check @zz_yaxis.
Check @zz_xaxis.
Check @zz_perp_is_dot.
Check @zz_perp_e1_is_yaxis.
Check @zz_perp_yaxis_is_xaxis.
Check @zz_e1_not_ClosedPerp.
Check @zz_yaxis_ClosedPerp.
Check @zz_e1_not_self_perp.
Check @zz_axes_differ.

(* ------------------------------------------------------------------------ *)
(** ** Negatives 2-6, at an abstract setoid *)

Section AbstractBoundary.

Universe po pu.
Constraint Set < po.

Context (Xp : SetoidObject@{po po}).
Context (Pp : PerpRel@{po} Xp).

(* ---------------------------------------------------------------------- *)
(** ** Negative 2 (TYPING): the connection is antitone, not covariant *)

(* Mac Lane types the two maps as [L : P → Q^op] and [R : Q^op → P]:
   taking complements REVERSES inclusion, so the covariant record of #380
   is inhabited only once the second relation is reversed.  The control
   shows the antitone reading is the one that holds. *)

Check (perp_galois Pp
        : GaloisConnection (@subset_le@{po} Xp)
            (op_rel (@subset_le@{po} Xp))).

Fail Check (perp_galois Pp
             : GaloisConnection (@subset_le@{po} Xp)
                 (@subset_le@{po} Xp)).

(* ---------------------------------------------------------------------- *)
(** ** Negative 3 (TYPING): right-adjointness is not left-adjointness *)

(* Adjunction/Right.v:665's [right_does_not_imply_left] shows the two
   classes come apart in general.  Here the point is narrower and is a
   fact about TYPES only: the record built for one slot is not a term of
   the other slot's type.  Nothing below claims that [PerpOp] is not
   adjoint on the left; that is neither proved nor refuted anywhere. *)

Check (perp_AdjointOnTheRight Pp
        : AdjointOnTheRight (PerpOp Pp) (PerpOp Pp)).

Fail Check (perp_AdjointOnTheRight Pp
             : AdjointOnTheLeft (PerpOp Pp) (PerpOp Pp)).

(* ---------------------------------------------------------------------- *)
(** ** Negative 4 (TYPING): [L = R] is about the MAPS, not the functors *)

(* [perp_galois_l_is_r] closes by [eq_refl], so Mac Lane's [L S = R S]
   holds on the nose at the level of the two fields.  It does NOT lift to
   the two functors those fields induce: [PerpFunctor] runs from
   [Subsets X] to the reversed order and [PerpFunctor_r] the other way, so
   the two do not share a type at all and the equation between them
   cannot even be stated.  Both functors are named in the controls. *)

Check (PerpFunctor Pp
        : Subsets@{po pu} Xp ⟶ Proset@{po pu} (@perp_PreOrder_r Xp)).
Check (PerpFunctor_r Pp
        : Proset@{po pu} (@perp_PreOrder_r Xp) ⟶ Subsets@{po pu} Xp).
Check (perp_galois_l_is_r Pp).

Fail Check (PerpFunctor Pp = PerpFunctor_r Pp).

(* ---------------------------------------------------------------------- *)
(** ** Negative 5 (CONVERSION): the triple complement collapses at [≈] *)

(* [perp_triple] is an equation between OBJECTS of the power set, held at
   the carriers' own [≈]; the two sides are different terms and no
   unfolding identifies a triple composite with a single one. *)

Check (fun S => perp_triple Pp S
         : perp_set Pp (perp_set Pp (perp_set Pp S)) ≈ perp_set Pp S).

Fail Check (fun S : carrier (Powerset_Prop_obj@{po} Xp) =>
              (eq_refl : perp_set Pp (perp_set Pp (perp_set Pp S))
                           = perp_set Pp S)).

End AbstractBoundary.

(* ------------------------------------------------------------------------ *)
(** ** Negative 6 (CONVERSION): the witness identifications are at [≈] *)

(* Over ℤ² the complement of the singleton [{(1,0)}] and the second axis
   are the same SUBSET, but they are built as two different
   [SetoidMorphism] records -- one a quantified condition over a
   singleton, the other a bare coordinate equation -- so the
   identification holds at [≈] and not on the nose. *)

Check (zz_perp_e1_is_yaxis : perp_set ZZPerp zz_e1 ≈ zz_yaxis).

Fail Check (eq_refl : perp_set ZZPerp zz_e1 = zz_yaxis).

(* ------------------------------------------------------------------------ *)
(** ** Negative 7 (FORMABILITY): the carrier and relation levels coincide *)

(* [PerpRel@{o}] is declared over [SetoidObject@{o o}], so it does not
   accept a setoid whose two levels are declared apart.  Read that at its
   true strength: the rejection lands on the ARGUMENT, and [PerpRel]
   cannot be tested apart from it, its parameter type BEING
   [SetoidObject@{o o}].  Read that precisely: the record's three fields
   do NOT force the identification -- the same three fields declared over
   [SetoidObject@{o1 o2}] are accepted and apply at levels declared apart
   (measured out of tree by an audit, not pinned here) -- so the [@{o}]
   binder is a declaration CHOICE aligning the record with
   [Powerset_Prop_obj], and it is that donor, whose rejection is pinned as
   negative 6 of Test/ProbeQuantifier384.v and cited rather than repeated,
   that makes the choice unavoidable downstream.  An earlier draft said
   this negative measured an inherited shape rather than a demand of the
   record's own, which overstated what it measures.  The
   controls show the setoid, its carrier and its structure are all fine at
   these levels. *)

Section UniverseBoundary.

Universe qo qh.
Constraint qh < qo.

Context (Aq : SetoidObject@{qo qh}).

Check (carrier Aq).
Check (is_setoid Aq).
Check (Aq : Type@{qo}).

Fail Check (PerpRel Aq).

End UniverseBoundary.
