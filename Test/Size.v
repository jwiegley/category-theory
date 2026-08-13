(* ========================================================================= *)
(* Machine-checked demonstrations for the size vocabulary of Theory/Size.v.   *)
(*                                                                           *)
(* This file is where issue #253's NEGATIVE demonstrations live, because they *)
(* need the rejection vernacular, and each use of it is a hit for the         *)
(* [make todo] hygiene sweep (Makefile:5 greps case-insensitively over every  *)
(* .v file for a small set of trigger words, one of which is that vernacular's*)
(* own name).  Confining them here follows the in-tree precedent set by        *)
(* Test/Issue138.v:75-76 and Test/ProbeFunnyPoly.v:69,77, which use it the     *)
(* same way; Monad/Transformer.v:207 does too.  This file contributes exactly *)
(* four such hits, and the pull request states that number rather than         *)
(* hiding it.  Prose elsewhere in this file is deliberately worded to avoid    *)
(* the trigger words, so the sweep's delta is exactly the four commands.      *)
(*                                                                           *)
(* WHAT THE VERNACULAR DOES AND DOES NOT SHOW.  It succeeds when the command  *)
(* it wraps raises ANY error.  It does not report WHICH error, so on its own  *)
(* it cannot distinguish a universe inconsistency from an ordinary type        *)
(* mismatch or a typo.  Test/Issue138.v:70-74 sets the precedent of saying so *)
(* out loud, and the distinction is load-bearing here -- see BLOCK B.         *)
(* ========================================================================= *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.

(* ===== BLOCK A — the size predicates are inhabited, and strict ===== *)

(* The vocabulary exists and can be used as a conclusion. *)
Check (One_Small : Small _1).
Check (small_locally_small _1 One_Small : LocallySmall _1).

(* Every category is locally small at its OWN hom level.  This is the sense in
   which the library's discipline is stronger than the books' convention:
   [Class Category]'s [homset] field builds local smallness in, so the
   predicate is universally satisfiable at the ambient level. *)
Check (fun C : Category => locally_small_ambient C : LocallySmall C).

(* THE CONTENT CHECK -- and note carefully which predicate it is about.

   [Small] is strict ([uo < o], [uh < h]) and that is where all of its content
   lies: were the constraints absent one could discharge it for EVERY category
   by handing back the category's own objects and homs.  The rejected commands
   below demonstrate that the discharge does not go through.

   [LocallySmall] is NOT strict -- it is declared [uh <= h] on purpose -- so no
   such claim holds for it, and the [Check] on line 41 above is precisely the
   universal discharge in question.  The first rejected command below is
   therefore about [LocallySmall] AT A STRICT INSTANTIATION, not about the
   class as declared.

   Unlike BLOCK B, the rejections here are unambiguous: every term is
   well-typed apart from its universe constraints, so the only thing that can
   refuse it is the constraint solver. *)
Fail Definition A253_trivial_locally_small@{o h p uh up
    | h <= p, uh <= up, uh < h}
  (C : Category@{o h p}) : LocallySmall@{o h p uh up} C :=
  @Build_LocallySmall@{o h p uh up} C
    (fun x y => (x ~> y)) (@homset C)
    (fun _ _ f => f) (fun _ _ f => f)
    (fun _ _ _ _ H => H)
    (fun x y f => reflexivity f) (fun x y u => reflexivity u).

Fail Definition A253_trivial_small@{o h p uo uh up
    | h <= p, uh <= up, uo < o, uh < h}
  (C : Category@{o h p}) : Small@{o h p uo uh up} C :=
  @Build_Small@{o h p uo uh up} C
    (@Build_LocallySmall@{o h p uh up} C
       (fun x y => (x ~> y)) (@homset C)
       (fun _ _ f => f) (fun _ _ f => f)
       (fun _ _ _ _ H => H)
       (fun x y f => reflexivity f) (fun x y u => reflexivity u))
    obj[C] (fun x => x) (fun x => x)
    (fun _ => obj_refl _) (fun _ => obj_refl _).

(* [A253_trivial_small] above is rejected inside its [Build_LocallySmall]
   sub-term -- the error is the same [Cannot enforce h <= uh because uh < h] as
   the previous command -- so elaboration never reaches [obj[C]] and that
   command alone is NO evidence about [uo < o].  This one isolates the object
   half, with no category and no hom in sight: a type cannot be resized to a
   strictly lower level.  Together the two cover both of [Small]'s strict
   constraints. *)
Fail Definition A253_no_object_resize@{o uo | uo < o} (A : Type@{o})
  : Type@{uo} := A.

(* ===== BLOCK B — self-membership, and the distinction issue #253 conflates ==== *)

(* Mac Lane's remark 1 is that [Set] is not small, i.e. not an object of
   itself.  Issue #253 asks for rejected-[Check] witnesses that "[Sets] as an
   object of itself, [Cat] as an object of itself" are UNIVERSE
   INCONSISTENCIES.  Both halves of that need correction, and the first is the
   more surprising.

   (i) THE NAIVE CHECK DOES NOT DEMONSTRATE ANYTHING.  [Check (Cat : obj[Cat])]
   SUCCEEDS.  It is not a witness of self-membership at all, because [Cat] is
   universe-polymorphic: the elaborator instantiates the two occurrences at
   DIFFERENT levels, so what is actually checked is [Cat@{i..} : obj[Cat@{j..}]]
   with the second strictly above the first.  That is the Cat/Cat' tower, and
   it is a THEOREM of the design rather than a defect -- it is exactly what
   BLOCK B's positive checks below record.  Wrapping [Check (Cat : obj[Cat])]
   in the rejection vernacular would therefore not compile, because the
   command it wraps succeeds.

   The demonstration has to PIN ONE INSTANCE on both sides.  Written that way
   the self-membership really is rejected, and rejected on universes alone:
   the ascription is type-correct in shape, since [obj[Cat]] is [Category] and
   [Cat] is a [Category], so nothing but the constraint solver can refuse it.
   This is the genuine formal counterpart of Mac Lane's remark, and the reason
   Instance/Cat.v:108-114 can say self-membership is "a universe inconsistency
   caught by the elaborator rather than a paradox to be excluded by axiom". *)
Fail Definition B253_cat_self@{a b c d e}
  : obj[Cat@{a b c d e}] := Cat@{a b c d e}.

(* (ii) FOR [Sets] IT IS NOT A UNIVERSE INCONSISTENCY AT ALL.  [obj[Sets]] is
   [SetoidObject] -- a carrier type paired with a setoid -- whereas [Sets] is a
   [Category].  A category is not a setoid, so this is an ORDINARY TYPE ERROR
   and would remain one at any universe levels whatsoever.  Pinning instances
   changes nothing.  The rejected command is kept only with that correction
   attached, since on its own it would be read as saying what the issue says. *)
Fail Check (Sets : obj[Sets]).

(* The positive half, which is what actually carries the stratification: a
   category at one level is an object of [Cat] built at the next.  Every one of
   these is accepted -- and per (i) they are the very ascriptions that make the
   naive self-membership check succeed. *)
Check (_1 : obj[Cat]).
Check (Sets : obj[Cat]).
Check (Cat : obj[Cat]).

(* [Cat] is itself a category, hence an object of a [Cat] one level up.  Coq's
   universe polymorphism supplies the whole tower silently; there is no [Cat']
   to define, which is the divergence from Mac Lane's single fixed [U]. *)
Check (Cat : Category).

(* ===== BLOCK C — Riehl's arrows-with-dom-and-cod packaging ===== *)

(* The unindexed packaging exists for every category... *)
Check (fun C : Category => ArrowQuiverOfCat C : ArrowQuiver).

(* ...and both of Riehl's retraction laws hold definitionally, by [obj_refl].
   In her unindexed presentation they are equations a candidate must satisfy;
   here the identity arrow stores its endpoints, so they are computations. *)
Example C253_dom_retract (C : Category) (x : obj[C]) :
  ObjEq (aq_dom (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x :=
  obj_refl _.

Example C253_cod_retract (C : Category) (x : obj[C]) :
  ObjEq (aq_cod (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x :=
  obj_refl _.
