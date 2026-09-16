Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.

Generalizable All Variables.

(** * Probe for Theory/Subobject/Quotient.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.7
    Definition 3, printed p. 126.  Issue #446.  The witnesses at Sets, Grp
    and FinSet have their own probe, Test/ProbeQuotObjWitnesses446.v; this
    file guards the general theory.

    The import list above is the target file's own import list,
    unabbreviated.  A short prefix is what makes a probe pass vacuously, so
    nothing is trimmed even where a require is redundant.

    Every statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read; a refutation that holds prints nothing under
    this repo's coqc, so a whole-file rc=0 would establish only THAT each
    command does not typecheck and never WHY.  Each negative is classified
    by the error TEXT, under THIS import list:

      CONVERSION  - "The term T has type X while it is expected to have
                    type Y (cannot unify A and B)".
      INSTANCE    - an implicit argument of class type that no instance in
                    scope resolves; the discriminator is the parenthetical
                    "(no type class instance found)".  A bare [Check]
                    TOLERATES such an open evar and succeeds, printing
                    "where ?H : [...]", so every missing-instance negative
                    is a [Definition], and the accepted [Check] is kept
                    beside it as the contrast.

    The instrument check comes first: a name that does not exist, refused
    for a reason unrelated to any boundary.  Every LIBRARY constant a
    negative names appears in a positive control outside any refutation
    command, so that a rename cannot leave a negative refused for
    reference-not-found and therefore vacuously green. *)

(** ** Instrument check *)

Fail Check quot_obj_theory_446_no_such_constant.

(** ** Positive controls: every constant the negatives depend on *)

Check @QuotObj.
Check @SubObj.
Check @quot_cod.
Check @quot_epi.
Check @quot_le.
Check @quot_meet.
Check @quot_join.
Check @monic_op_iff_epic.
Check @Epic.
Check @Monic.
Check @Isomorphism.
Check @to.
Check @Cartesian.
Check @HasPushouts.
Check @HasImages.
Check @quot_equiv_iff_iso.
Check @quot_equiv_of_cod_iso.
Check @quot_le_unfold.
Check @quot_equiv_unfold.
Check @QuotObj_op_is_SubObj.

(** ** Readbacks that HOLD, at the strength stated *)

Section Readbacks.

Context {C : Category}.
Context {x : C}.

(* F1: quotient objects of the opposite category ARE subobjects, on the
   nose, because C^op^op is C by reflexivity. *)
Example p446t_op_is_sub : @QuotObj (C^op) x = @SubObj C x := eq_refl.

(* F2: the covariant reading of the order is definitional -- q ≤ r when
   the epi of q FACTORS THROUGH the epi of r, q being the coarser. *)
Example p446t_le_unfold (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }
  := eq_refl.

(* The accepted [Check] that the INSTANCE negative N5 is the contrast to:
   with no [HasPushouts C] in scope this succeeds, printing the open evar,
   which is exactly why N5 is a [Definition]. *)
Check (fun q r : QuotObj x => quot_meet q r).

End Readbacks.

(** ** Negatives *)

Section Negatives.

Context {C : Category}.
Context {x y : C}.

(* N2 -- CONVERSION.  Dropping the ^op on the left of F1: quotient objects
   of C are NOT subobjects of C.  "cannot unify QuotObj x and SubObj x". *)
Fail Definition n2 : @QuotObj C x = @SubObj C x := eq_refl.

(* N3 -- CONVERSION.  The setoid does not unfold covariantly on the nose:
   [SubObj_Setoid]'s witness at C^op is an isomorphism IN C^op, so the
   naive C-isomorphism spelling is refused, "cannot unify (q ≈ r) and
   ∃ i : quot_cod q ≅ quot_cod r, i ∘ quot_epi q ≈ quot_epi r".  The
   covariant characterization is therefore the LEMMA [quot_equiv_iff_iso]
   at ≈, while [quot_equiv_unfold] (the C^op-isomorphism spelling with the
   composition annotated) is the eq_refl. *)
Fail Definition n3 (q r : QuotObj x) :
  (q ≈ r) = { i : quot_cod q ≅ quot_cod r & to i ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

(* N4 -- CONVERSION.  The order direction: q ≤ r factors q THROUGH r and
   not the other way round.  "cannot unify" against the swapped mediator
   { k : quot_cod q ~> quot_cod r & k ∘ quot_epi q ≈ quot_epi r }. *)
Fail Definition n4 (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod q ~> quot_cod r & k ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

(* N5 -- INSTANCE, and it must be a [Definition].  The meet is conditional
   on pushouts: "Cannot infer the implicit parameter HP of quot_meet whose
   type is HasPushouts C (no type class instance found)".  The [Check] form
   above is accepted. *)
Fail Definition n5 (q r : QuotObj x) : QuotObj x := quot_meet q r.

(* N6 -- CONVERSION.  A direction swap of [monic_op_iff_epic]: its first
   projection goes from Monic in C^op to Epic in C, and the converse
   reading is refused, "cannot unify Epic f and Monic f" (printed with the
   short names in scope on both sides). *)
Fail Definition n6 (f : x ~> y) : @Epic (C^op) y x f → @Monic C x y f :=
  fst (monic_op_iff_epic f).

End Negatives.

Section NoCoimages.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x : C}.

(* N7 -- INSTANCE.  The join needs a supply of coimages: with products but
   no [HasCoimages C], "Cannot infer the implicit parameter HI of quot_join
   whose type is @HasCoimages C (no type class instance found)" -- which
   also shows that the [HasCoimages] NOTATION participates in class
   resolution. *)
Fail Definition n7 (q r : QuotObj x) : QuotObj x := quot_join q r.

End NoCoimages.
