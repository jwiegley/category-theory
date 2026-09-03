(** * Boundary probe for the group-action Galois connection (#381)

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

    Seven negatives plus one instrument check.  The kinds are told apart
    by the error TEXT, not by a label, and every one was stripped ONE AT A
    TIME, compiled alone, and its whole error read.

      TYPING       a plain "has type ... while it is expected to have
                   type ...", with NO "cannot unify" and NO universe
                   clause.  Negative 2.  This is the content of Mac Lane's
                   display (1): the connection is [L X >= S], not
                   [L X <= S], so it does not inhabit the covariant
                   reading.

      CONVERSION   "cannot unify" between two inhabitants of ONE type, or
                   between two categories.  Negatives 3, 4 and 5.

      FORMABILITY  ends in "universe inconsistency: Cannot enforce ...".
                   Negatives 6, 7 and 8.  Within them the reported clause
                   separates two shapes: 6 and 7 are LEVEL rejections
                   between two DECLARED universes ("Cannot enforce qh = qo
                   because qo < qh"), while 8 reports the literal [Set]
                   ("Cannot enforce Set = ... because Set < ..."), which
                   is what makes Instance/Grp.v:1087's [Z2] unusable
                   here.

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
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.Grp.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Negative 1: the instrument *)

(* If [Fail] were inert -- a missing scope, a stray [Set Silent] -- this
   would pass and every other negative below would be worthless. *)
Fail Check probe381_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(** ** Controls for the constants the negatives name *)

Check @subset_le.
Check @subset_le_preorder.
Check @Subsets.
Check @op_rel.
Check @op_PreOrder.
Check @Proset.
Check @GaloisConnection.
Check @GrpObject.
Check @grp_setoid.
Check @MSetoidAction.
Check @act_setoid.
Check @grp_mon.
Check @Powerset_Prop_obj.
Check @Z2.
Check @AdjointOnTheRight.
Check @stab.
Check @fixed.
Check @stab_PreOrder_G.
Check @group_action_galois.
Check @group_action_adjunction.
Check @group_action_AdjointOnTheRight.
Check @stab_fixed_stab.
Check @fixed_stab_fixed.
Check @stab_Subgroup.
Check @closed_G_iff.
Check @closed_U_iff.
Check @ClosedG.
Check @ClosedU.
Check @subset_le_antisym.
Check @gal_lrl_below.
Check @gal_lrl_above.
Check @gal_closed_l_iff.
Check @StabOp.
Check @FixedOp.
Check @GalZ2.
Check @GalZ2Act.
Check @GalV4.
Check @GalV4Act.
Check @galois_two.
Check @galois_true.
Check @galois_stab_true_trivial.
Check @galois_v4_stab_proper.

(* ------------------------------------------------------------------------ *)
(** ** Negative 2 (TYPING): the connection is antitone, not covariant *)

(* Mac Lane's display (1) reads "L p >= q in Q", and the construction
   paragraph "L X >= S in Q".  Reading the second relation as plain
   inclusion instead of its reverse gives a term of the wrong TYPE: the
   error is a bare "has type ... while it is expected to have type ...",
   with no "cannot unify" and no universe clause. *)

Section AntitoneIsNotCovariant.

Universe po pgu.
Constraint Set < po.
Constraint po <= pgu.

Context (Gp : GrpObject@{po po pgu}).
Context (Ap : MSetoidAction@{po po pgu pgu pgu po po pgu}
                (grp_mon@{po po pgu} Gp)).

(* The control: the connection DOES inhabit the antitone reading. *)
Check (group_action_galois Gp Ap
        : GaloisConnection (@subset_le@{po} (act_setoid Ap))
            (op_rel (@subset_le@{po} (grp_setoid Gp)))).

Fail Check (group_action_galois Gp Ap
             : GaloisConnection (@subset_le@{po} (act_setoid Ap))
                 (@subset_le@{po} (grp_setoid Gp))).

(* ---------------------------------------------------------------------- *)
(** ** Negatives 3 and 4 (CONVERSION), stated in the same section *)

(* Idempotence of the two closure operators holds at the carriers' own
   [equiv] and NOT at [eq_refl]: the two sides are different terms, and no
   amount of unfolding identifies a triple composite with a single one. *)

Check (fun X => stab_fixed_stab Gp Ap X
         : stab (fixed (stab X)) ≈ stab X).

Fail Check (fun (X : carrier (Powerset_Prop_obj@{po} (act_setoid Ap))) =>
              (eq_refl : @stab Gp Ap (@fixed Gp Ap (@stab Gp Ap X))
                           = @stab Gp Ap X)).

Check (fun S => fixed_stab_fixed Gp Ap S
         : fixed (stab (fixed S)) ≈ fixed S).

Fail Check (fun (S : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp))) =>
              (eq_refl : @fixed Gp Ap (@stab Gp Ap (@fixed Gp Ap S))
                           = @fixed Gp Ap S)).

(* ---------------------------------------------------------------------- *)
(** ** Negative 5 (CONVERSION): the target category is the opposite one on
       its objects and its homs, but not as a whole record *)

(* The rejection is NOT at [id] or [compose]: both agree at [eq_refl], as
   does the hom-setoid's [equiv], and the four controls below say so --
   the first two are the target's own [galois_PG_obj] and [galois_PG_hom]
   restated.  What differs is the [homset] record, whose [Equivalence]
   witness is [Proset]'s opaque [Program] obligation applied at [(S, T)]
   on one side and [(T, S)] on the other, together with the rebuilt law
   fields; so the negative measures the record and not its data. *)

Check (eq_refl : obj[Proset@{po Set} (stab_PreOrder_G Gp)]
                   = obj[(Subsets@{po Set} (grp_setoid Gp))^op]).

Check (fun S T : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)) =>
         (eq_refl : (S ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> T)
                      = (S ~{(Subsets@{po Set} (grp_setoid Gp))^op}~> T))).

Check (fun S : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)) =>
         (eq_refl : @id (Proset@{po Set} (stab_PreOrder_G Gp)) S
                      = @id ((Subsets@{po Set} (grp_setoid Gp))^op) S)).

Check (fun (S T U : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)))
           (f : T ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> U)
           (g : S ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> T) =>
         (eq_refl : @compose (Proset@{po Set} (stab_PreOrder_G Gp)) S T U f g
                      = @compose ((Subsets@{po Set} (grp_setoid Gp))^op)
                                 S T U f g)).

Fail Check (eq_refl : Proset@{po Set} (stab_PreOrder_G Gp)
                        = (Subsets@{po Set} (grp_setoid Gp))^op).

End AntitoneIsNotCovariant.

(* ------------------------------------------------------------------------ *)
(** ** Negatives 6 and 7 (FORMABILITY): [Subsets] identifies the two
       universes of the setoid it is handed *)

(* Instance/Powerset.v:295 declares [Subsets (X : SetoidObject@{o o})], so
   forming the power set of a group's carrier IDENTIFIES that group's
   carrier and relation universes -- which is why the target's section
   binds [G : GrpObject@{o o gu}] with the level reused rather than
   [GrpObject@{o1 o2 gu}].  [Subsets] is the LAST of four donors that
   each force it alone: [Powerset_Prop_obj] (Instance/Sets/Powerset.v:981,
   the one the target meets first), [subset_le] and [subset_le_preorder]
   are rejected at these very levels too (measured out of tree; only
   [Subsets] is pinned here).  The controls show that naming the group's
   setoid, and the group's homs, is fine at levels declared apart: what is
   rejected is the power set, and the same for the action. *)

Section SubsetsIdentifies.

Universe qo qh qgu.
Constraint qo < qh.
Constraint qh <= qgu.

Context (Gq : GrpObject@{qo qh qgu}).
Context (Aq : MSetoidAction@{qo qh qgu qgu qgu qo qh qgu}
                (grp_mon@{qo qh qgu} Gq)).

(* Controls, at those very levels. *)
Check (grp_setoid Gq).
Check (act_setoid Aq).
Check (carrier (grp_setoid Gq)).
Check (grp_mon@{qo qh qgu} Gq).

Fail Check (Subsets (grp_setoid Gq)).

Fail Check (Subsets (act_setoid Aq)).

End SubsetsIdentifies.

(* ------------------------------------------------------------------------ *)
(** ** Negative 8 (FORMABILITY): Instance/Grp.v's [Z2] is pinned at [Set] *)

(* [Z2@{u} : GrpObject@{u Set u}] -- its relation universe is the literal
   [Set], not a parameter -- so its carrier cannot be the source of a
   [Powerset_Prop_obj], whose own [Set < o] then cannot be met.  That is
   why the target builds [GalZ2] over [eq_Setoid] instead.  The control
   shows the group itself, and its setoid, are perfectly nameable. *)

Check @Z2.
Check (grp_setoid Z2).
Check (Subsets (grp_setoid GalZ2)).

Fail Check (Subsets (grp_setoid Z2)).

(* ------------------------------------------------------------------------ *)
(** ** Positive: the two witnesses, and what they compute *)

Check (stab (A := GalZ2Act) galois_true).
Check (stab_Subgroup GalV4 GalV4Act galois_true).
Check (group_action_AdjointOnTheRight GalZ2 GalZ2Act).
Check (group_action_adjunction GalZ2 GalZ2Act).
Check (closed_G_iff GalZ2 GalZ2Act galois_true).
Check (closed_U_iff GalZ2 GalZ2Act galois_true).
Check (ClosedG GalZ2Act galois_true).
Check (ClosedU (A := GalZ2Act) galois_true).
Check (subset_le_antisym (X := galois_two)).
Check (gal_lrl_below (stab_PreOrder_U GalZ2 GalZ2Act)
         (group_action_galois GalZ2 GalZ2Act)).
Check (gal_lrl_above (stab_PreOrder_G GalZ2)
         (group_action_galois GalZ2 GalZ2Act)).
Check (gal_closed_l_iff (stab_PreOrder_U GalZ2 GalZ2Act)
         (stab_PreOrder_G GalZ2)
         (group_action_galois GalZ2 GalZ2Act)).
Check (StabOp GalZ2 GalZ2Act).
Check (FixedOp GalZ2 GalZ2Act).
Check galois_stab_true_trivial.
Check galois_v4_stab_proper.
