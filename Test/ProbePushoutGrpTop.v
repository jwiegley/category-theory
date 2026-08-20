Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Pushout.

Generalizable All Variables.

(** * Probe: the strength boundary of the Grp and Top pushouts *)

(* Guard file for Instance/Grp/Pushout.v and Instance/Top/Pushout.v, in
   the Test/ProbeFunnyPoly.v convention.  Every negative is paired with a
   positive control that NAMES ITS OWN CONSTANTS, so that a rename or a
   definitional change breaks this file loudly instead of turning a [Fail]
   vacuously green.  The pairing was verified by RENAME SIMULATION: each
   negative was copied to a scratch file with one constant renamed, and
   the scratch file was confirmed to stop compiling.

   The import list is the UNION of the two targets' import lists, in
   dependency order -- a short prefix is what makes probes pass for the
   wrong reason.

   Conversion negatives ([Fail Definition ... := eq_refl]) and formability
   negatives ([Fail Check ...]) are kept in separate sections; they fail
   for different reasons and must not be read as one kind.  Each negative
   was stripped of its [Fail] once and the resulting message inspected;
   the kind is recorded beside it. *)

(** ** Instrument check

    A [Fail] that must itself fail, so that a globally broken [Fail]
    vernacular would be caught here rather than silently greening the
    negatives below. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Positive controls, and conversion negatives *)

Section GrpConversion.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).
Context {Q : GrpObject}.
Context (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q).
Context (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g).

(* CONTROL 1.  The chosen pushout's apex and first injection ARE the
   hand-built ones; the record projections reduce. *)
Definition ctl_grp_apex :
  pushout_apex (Grp_pushout f g) = AmalgamGrp f g := eq_refl.

Definition ctl_grp_in1 :
  pushout_in1 (Grp_pushout f g) = am_inj1 f g := eq_refl.

(* CONTROL 2.  The mediator's own value on the three formers reduces --
   [am_eval] is a [Fixpoint], so this is where [am_med]'s homomorphism
   laws come from. *)
Definition ctl_grp_med_unit :
  grp_map (am_med f g q1 q2 Hcomm) am_one = grp_unit Q := eq_refl.

Definition ctl_grp_med_mul (u v : AmTerm B C) :
  grp_map (am_med f g q1 q2 Hcomm) (am_mul u v)
    = grp_mul Q (grp_map (am_med f g q1 q2 Hcomm) u)
                (grp_map (am_med f g q1 q2 Hcomm) v) := eq_refl.

(* CONTROL 2b.  [pushout_med] itself is named in a control, so that
   renaming it breaks this file rather than turning NEGATIVE 1 vacuously
   green -- [Fail] catches "reference not found" just as happily as it
   catches a unification failure. *)
Definition ctl_grp_med_typed
  : pushout_apex (Grp_pushout f g) ~{Grp}~> Q :=
  pushout_med (Grp_pushout f g) Hcomm.

(* NEGATIVE 1 (conversion).  [pushout_med] does NOT reduce to [am_med].
   Stripping the [Fail] reports a unification failure between
   [unique_obj (pushout_ump ...)] and [am_med ...].  The cause is DONOR
   OPACITY and not this file's construction: Structure/Pushout.v states
   [pushout_ump] as a [Lemma ... Qed], so [unique_obj] is applied to an
   opaque constant and no amount of transparency here would help.
   Instance/Grp/Pushout.v's [Grp_pushout_med_is_am_med] is the [≈] form
   that does hold. *)
Fail Definition neg_grp_med :
  pushout_med (Grp_pushout f g) Hcomm = am_med f g q1 q2 Hcomm := eq_refl.

End GrpConversion.

Section TopConversion.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).
Context {Q : TopSpace}.
Context (q1 : B ~{Top}~> Q) (q2 : C ~{Top}~> Q).
Context (Hcomm : q1 ∘[Top] f ≈ q2 ∘[Top] g).

(* CONTROL 3.  Same reduction on the Top side. *)
Definition ctl_top_apex :
  pushout_apex (Top_pushout f g) = Pushout_Top f g := eq_refl.

Definition ctl_top_in1 :
  pushout_in1 (Top_pushout f g) = Top_po_in1 f g := eq_refl.

(* CONTROL 3b.  Names [pushout_med] and [Top_po_med], for the same
   pairing reason. *)
Definition ctl_top_med_typed
  : pushout_apex (Top_pushout f g) ~{Top}~> Q :=
  pushout_med (Top_pushout f g) Hcomm.

Definition ctl_top_med_named
  : Pushout_Top f g ~{Top}~> Q := Top_po_med f g q1 q2 Hcomm.

(* NEGATIVE 2 (conversion).  The SAME donor opacity, on the other
   substrate -- which is what shows the cause is Structure/Pushout.v's
   [Qed] rather than anything about groups. *)
Fail Definition neg_top_med :
  pushout_med (Top_pushout f g) Hcomm = Top_po_med f g q1 q2 Hcomm := eq_refl.

End TopConversion.

Section TopEmptySpan.

Context (B C : TopSpace).

Notation Ef := (top_zero B).
Notation Eg := (top_zero C).

(* CONTROL 4.  The POINTS of the empty-span pushout are the coproduct's
   points on the nose. *)
Definition ctl_top_points :
  carrier (top_carrier (Pushout_Top Ef Eg))
    = carrier (sum_carrier B C) := eq_refl.

(* NEGATIVE 3 (conversion).  The SETOIDS differ, so the two
   [SetoidObject]s are not convertible: the pushout apex compares points
   by the inductive [tp_rel], the coproduct by [sum_setoid]'s [match].
   Stripping the [Fail] reports "cannot unify
   "top_carrier (Pushout_Top Ef Eg)" and "sum_carrier B C"" -- it
   names no field; that the difference is confined to the setoid is a
   DIAGNOSIS, supported by [ctl_top_points] showing the carriers agree.
   This is what makes [Top_pushout_empty_iso] a genuine
   isomorphism rather than an identity. *)
Fail Definition neg_top_carrier :
  top_carrier (Pushout_Top Ef Eg) = sum_carrier B C := eq_refl.

(* CONTROL 4b.  Names [IsOpen] and [Sum_Top], which NEGATIVE 4 mentions
   and no other control did. *)
Definition ctl_top_sum_open (W : sum_carrier B C → Type)
  (H : IsOpen (Sum_Top B C) W) : IsOpen (Sum_Top B C) W := H.

(* NEGATIVE 4 (conversion).  The TOPOLOGIES differ too: [tp_open] carries
   a respect-the-gluing clause that [sum_open] does not.  Over the empty
   span that clause is redundant -- which is exactly what
   [Top_pushout_empty_iso] proves -- but it is not definitionally
   absent. *)
Fail Definition neg_top_topology :
  IsOpen (Pushout_Top Ef Eg) = IsOpen (Sum_Top B C) := eq_refl.

End TopEmptySpan.

(** ** Formability negatives: a donor [Set] pin, and the route around it

    [Instance/Grp.v]'s [Grp_zero_hom] is declared over
    [GrpObject@{Set Set Set}] -- a DONOR pin, of the same family that
    Instance/Grp/Quotient/Colimit.v already records for [Grp_trivial] and
    [Grp_Zero], and which confines that whole file.  It is NOT repaired
    here.  What this section establishes is that
    Instance/Grp/Pushout.v ROUTES AROUND it: the classical presentation of
    the free product as the pushout over the trivial group would inherit
    the pin, and the presentation along the CONSTANT legs does not.  The
    negatives are the donor's rejection above [Set]; the controls are this
    file's acceptance at the same level. *)

Section SetPin.

Universe bg.
Constraint Set < bg.

(* CONTROL 5.  The amalgamated product is formable strictly above [Set]:
   no [Set] pin anywhere in the pushout proper. *)
Check (fun (A B C : GrpObject@{bg bg bg})
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) => AmalgamGrp f g).

(* CONTROL 6.  So is the chosen pushout, hence [Grp_HasPushouts]. *)
Check (fun (A B C : GrpObject@{bg bg bg})
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) =>
         pushout_apex (Grp_pushout f g)).

(* CONTROL 7.  And so are the free product and its injection -- this is
   the route-around, and it is what the two negatives below are a
   contrast to.  [grp_const] is named too, being what makes it work. *)
Check (fun B C : GrpObject@{bg bg bg} => Grp_free_product B C).
Check (fun B C : GrpObject@{bg bg bg} => Grp_fp_inl B C).
Check (fun B C : GrpObject@{bg bg bg} => grp_const B C).

(* CONTROL 8.  The donor constants DO exist and ARE usable at [Set]-level
   groups; naming them here is what makes NEGATIVES 5 and 6 statements
   about the universe rather than about a missing reference. *)
Check (Grp_zero_hom Z2).
Check (Grp_zero_hom_Section Z2).

(* NEGATIVE 5 (formability).  Instance/Grp.v's map out of the trivial
   group is NOT formable above [Set].  Stripping the [Fail] reports a
   genuine universe inconsistency naming the declared level:
   "Cannot enforce Set = bg". *)
Fail Check (fun G : GrpObject@{bg bg bg} => Grp_zero_hom G).

(* NEGATIVE 6 (formability).  Hence neither is the splitting of that map,
   which is why Instance/Grp/Pushout.v records [Grp_zero_hom_Section] as
   the route NOT taken rather than building the free product on it. *)
Fail Check (fun G : GrpObject@{bg bg bg} => Grp_zero_hom_Section G).

End SetPin.
