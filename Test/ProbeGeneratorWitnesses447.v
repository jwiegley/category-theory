Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Grp.Generator.
Require Import Category.Instance.Ab.Generator.

Generalizable All Variables.

(** * Probe for the #447 witnesses: Instance/Sets/Generator.v,
      Instance/Grp/Generator.v, Instance/Ab/Generator.v

    Mac Lane §V.7 Definition 4 (p. 127), Awodey §7.2 (p. 154).  The
    general theory has its own probe, Test/ProbeGenerator447.v.

    The import list above is the UNION of the three witness files' own
    import lists, unabbreviated, in the order the Sets file uses (Theory/
    Concrete after Instance/Sets, so that the two [bool_setoid_object]s
    shadow the way they do there; no bare occurrence of that name appears
    below).

    CORRECTION (#1382): an earlier revision called N1-N5 all CONVERSION
    refusals.  N1 and N5 now hold: [Unit_Setoid]'s explicit transparent
    equivalence field replaces Rocq 9.1.1's opaque Program obligation.
    This is proof transparency, not a carrier-universe pin; the
    #22575-patched 9.1.1 stand-in already accepted both before this change.
    On both tools, stripping each remaining negative in a copy of this
    WHOLE file gives three CONVERSION refusals (N2-N4, "cannot unify")
    and one missing-name instrument, four refutation commands in all.
    The instrument check comes first, and every library constant a negative names has a
    positive control outside any refutation command.  "The empty setoid
    is not a separator" is NOT here: it is a theorem about a well-typed
    statement with no inhabitant, delivered as
    [Sets_empty_not_separates], and a refusal probe cannot express it. *)

(** ** Instrument check *)

Fail Check generator_witness_447_no_such_constant.

(** ** Positive controls *)

Check @IsSeparator.
Check @Generator.
Check @gen_index.
Check @gen_obj.
Check @Generator_of_separator.
Check @separator_iso.
Check @IsSeparator_of_Separator.
Check @Sets_Separator.
Check @Sets_unit_separates.
Check @Sets_terminal_separates.
Check @Sets_terminal_separates_by_transport.
Check @Sets_terminal_separates_from_Concrete.
Check @Sets_Generator.
Check @Sets_terminal_Generator.
Check @Sets_terminal_unit_iso.
Check @Sets_empty_not_separates.
Check @Sets_empty_not_separates_pick.
Check @Grp_free_one_separates.
Check @Grp_Generator.
Check @Ab_free_one_separates.
Check @Ab_Generator.
Check @FreeGrpObject.
Check @FreeAbObject.
Check @ab_int.
Check @unit_setoid_object.
Check @Unit_Setoid.
Check @Sets_Terminal.
Check @Sets_Initial.
Check @terminal_obj.

(** ** Readbacks that HOLD *)

(* The Generator packages are the expected one-object families, on the
   nose. *)
Example p447w_g1 : gen_index Sets_Generator = unit := eq_refl.
Example p447w_g2 : gen_obj Sets_Generator tt = unit_setoid_object := eq_refl.
Example p447w_g3 :
  gen_obj Sets_terminal_Generator tt = @terminal_obj Sets Sets_Terminal
  := eq_refl.

(* The terminal object's setoid field IS Instance/Sets.v's [Unit_Setoid];
   the singleton's is Lib/Setoid.v's [unit_setoid].  CORRECTION (#1382):
   the earlier claim that this difference refuses N1 depended on the
   opaque equivalence obligation.  With the explicit transparent field
   the two setoids convert, as N1 below checks. *)
Example p447w_t1 : @terminal_obj Sets Sets_Terminal
  = {| carrier := poly_unit ; is_setoid := Unit_Setoid |} := eq_refl.

(* The initial object's carrier is [False], on the nose. *)
Example p447w_empty : carrier (@terminal_obj (Sets^op) Sets_Initial) = False
  := eq_refl.

(* Control for N4: the free abelian group on one generator IS what the
   theorem is about. *)
Definition p447w_ab : @IsSeparator Ab (FreeAbObject unit_setoid_object) :=
  Ab_free_one_separates.

(** ** Boundary checks *)

(* N1 -- POSITIVE CONVERSION.  CORRECTION (#1382): the former refusal
   "cannot unify "1" and "unit_setoid_object"" was caused by
   [Unit_Setoid]'s opaque equivalence obligation.  Its explicit transparent
   field makes the terminal object and the singleton convert. *)
Example n1 : @terminal_obj Sets Sets_Terminal = unit_setoid_object
  := eq_refl.

(* N2 -- CONVERSION.  Separation is at ≈, not at Leibniz =:
   "cannot unify "f ∘ k = g ∘ k" and "f ∘ k ≈ g ∘ k"". *)
Fail Definition n2 :
  forall (X Y : SetoidObject) (f g : X ~{Sets}~> Y),
    (forall k : unit_setoid_object ~{Sets}~> X, f ∘ k = g ∘ k) -> f = g
  := Sets_unit_separates.

(* N3 -- CONVERSION.  The two composites swapped -- the COseparator's
   postcomposition in place of the separator's precomposition:
   "cannot unify "unit_setoid_object ~{ Sets }~> x" and
   "y ~{ Sets }~> unit_setoid_object"".  This is the quantifier exchange
   that Structure/Generator/Dual.v's bridge performs. *)
Fail Definition n3 :
  forall (X Y : SetoidObject) (f g : X ~{Sets}~> Y),
    (forall k : Y ~{Sets}~> unit_setoid_object, k ∘ f ≈ k ∘ g) -> f ≈ g
  := Sets_unit_separates.

(* N4 -- CONVERSION.  Mac Lane's ℤ is not, in tree, the free abelian
   group on one generator: "cannot unify
   "FreeAbObject unit_setoid_object ~{ Ab }~> x" and "ab_int ~{ Ab }~> x"".
   The isomorphism between them is not in tree (see the Ab header). *)
Fail Definition n4 : @IsSeparator Ab ab_int := Ab_free_one_separates.

(* N5 -- POSITIVE SEPARATION.  CORRECTION (#1382): N1's conversion now
   lets the singleton proof inhabit the terminal-object statement too.
   The former refusal was the same proof-opacity boundary, not a size
   restriction.  [Sets_terminal_separates] remains the pinned public name. *)
Definition n5 : @IsSeparator Sets (@terminal_obj Sets Sets_Terminal)
  := Sets_unit_separates.
