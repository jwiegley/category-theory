(** * Probe for Theory/WeaklyInitial.v's characterization (issue #435)

    Pins the measured boundaries of the initial-object theorem's two
    directions with negatives of two kinds, kept lexically apart: TYPING
    (N1: a weakly initial OBJECT is not a weakly initial FAMILY — the two
    notions are related by [wif_of_weakly_initial], not by conversion; N4:
    Freyd's direction does not run without the SECOND product — the
    equalizer supply is not accepted in its place; N5: a family does not
    yield a weakly initial object at a chosen index — [wif_cover] picks its
    own member per target, Riehl's distinction between weakly initial and
    jointly weakly initial) and CONVERSION (N2: the singleton family's index
    is [poly_unit] and nothing else; N3: a [Terminal] is not an [Initial],
    the [C^op] pivot made visible).  The [eq_refl] readbacks are positive
    controls: the family built from an initial object is that object, both
    biconditionals' forward halves ARE [weakly_initial_of_initial], and at
    Sets the DERIVED singleton family's index and member compute.  Every command
    binds its own category, because the pinned [Limit] hypotheses need the
    category's hom level at [Set] and a [Section] variable would fix it
    elsewhere.  Each refutation was stripped one at a time in a copy of the
    whole file; the import list mirrors the target's, plus the Sets
    satellite and Adjunction/GAFT.v for their controls.  A universe
    refutation at [Cat] was tried and does NOT refuse ([Cat]'s hom universe
    instantiates at [Set]); it is not here. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Parallel.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Theory.WeaklyInitial.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe435_absent_name.

(** ** A: TYPING — object versus family *)

(* control: a weakly initial object is a type, and a family is built from it *)
Check (fun (C : Category) (c : C) (w : WeaklyInitial c) =>
         wif_of_weakly_initial w).

(* N1 TYPING: an object is not a family *)
Fail Check (fun (C : Category) (c : C) (w : WeaklyInitial c) =>
              (w : WeaklyInitialFamily C)).

(** ** B: CONVERSION — the singleton index, and the [C^op] pivot *)

(* control: the index is the polymorphic unit *)
Example p435_index {C : Category} (I : @Initial C) :
  wif_index (weakly_initial_of_initial I) = poly_unit := eq_refl.

(* N2 CONVERSION: it is not [bool] *)
Fail Example p435_index_bool {C : Category} (I : @Initial C) :
  wif_index (weakly_initial_of_initial I) = bool := eq_refl.

(* control: the direction consumes an [Initial] *)
Check (fun (C : Category) (I : @Initial C) => weakly_initial_of_initial I).

(* N3 CONVERSION: a [Terminal] is refused where an [Initial] is expected *)
Fail Check (fun (C : Category) (T : @Terminal C) =>
              weakly_initial_of_initial T).

(** ** C: TYPING — the two products, and the index choice *)

(* control: with both products and the equalizers, Freyd's direction runs *)
Check (fun (C : Category) (W : WeaklyInitialFamily C)
           (P : Limit (DiscreteCat_Functor (wif_obj W)))
           (Pe : Limit (DiscreteCat_Functor
                          (fun _ : iprod (wif_obj W) P ~> iprod (wif_obj W) P
                           => iprod (wif_obj W) P)))
           (E : HasEqualizers C) => initial_from_weakly_initial W P Pe E).

(* N4 TYPING: the equalizer supply is not accepted in place of the second
   product *)
Fail Check (fun (C : Category) (W : WeaklyInitialFamily C)
                (P : Limit (DiscreteCat_Functor (wif_obj W)))
                (E : HasEqualizers C) => initial_from_weakly_initial W P E).

(* control: the family's product is a weakly initial object *)
Check (fun (C : Category) (W : WeaklyInitialFamily C)
           (P : Limit (DiscreteCat_Functor (wif_obj W))) =>
         weakly_initial_iprod W P).

(* N5 TYPING: a member at a chosen index is not weakly initial by the cover
   alone — [wif_cover] chooses its own index per target *)
Fail Definition p435_member_weakly_initial (C : Category)
  (W : WeaklyInitialFamily C) (i : wif_index W) : WeaklyInitial (wif_obj W i) :=
  fun x => projT2 (wif_cover W x).

(** ** D: readbacks *)

Example p435_obj {C : Category} (I : @Initial C) (u : poly_unit) :
  wif_obj (weakly_initial_of_initial I) u = @initial_obj C I := eq_refl.

Example p435_cover {C : Category} (I : @Initial C) (x : C) :
  projT2 (wif_cover (weakly_initial_of_initial I) x) = @zero C I x := eq_refl.

Example p435_iff_fst {C : Category} (Ps : FreydProducts C) (E : HasEqualizers C)
  (I : @Initial C) :
  fst (initial_iff_weakly_initial_family Ps E) I = weakly_initial_of_initial I
  := eq_refl.

Example p435_iff_complete_fst {C : Category} (HC : @Complete C)
  (E : HasEqualizers C) (I : @Initial C) :
  fst (initial_iff_weakly_initial_family_complete HC E) I
    = weakly_initial_of_initial I := eq_refl.

Check (fun (C : Category) (Ps : FreydProducts C) (E : HasEqualizers C) =>
         snd (initial_iff_weakly_initial_family Ps E)
         : WeaklyInitialFamily C → @Initial C).

(* the Sets round trip computes its family *)
Example p435_sets_index : wif_index Sets_wif = poly_unit := eq_refl.

Example p435_sets_obj (u : poly_unit) :
  wif_obj Sets_wif u = @initial_obj Sets Sets_Initial := eq_refl.

Check (Sets_roundtrip_iso
         : @initial_obj Sets Sets_initial_recovered
             ≅ @initial_obj Sets Sets_Initial).

(* the separator and the solution-set converse are present *)
Check (Parallel_ParX_not_initial : @IsInitialObj Parallel ParX → False).
Check (Parallel_ParY_not_weakly_initial : @WeaklyInitial Parallel ParY → False).
Check (@sols_of_wif).
Check (@sols_of_comma_initial).

(* the converse's own index readback lives in Adjunction/GAFT.v, whose
   comma notation this file does not import *)
Check (@sols_of_wif_index).

(** ** Guard block *)

Check @WeaklyInitial.
Check @WeaklyInitialFamily.
Check @wif_of_weakly_initial.
Check @weakly_initial_of_initial.
Check @weakly_initial_obj_of_initial.
Check @weakly_initial_iprod.
Check @FreydProducts.
Check @initial_iff_weakly_initial_family.
Check @initial_iff_weakly_initial_family_complete.
Check @initial_from_weakly_initial_complete.
Check @initial_from_weakly_initial.
Check @wif_index.
Check @wif_obj.
Check @wif_cover.
Check @IsInitialObj.
Check @Terminal.
Check @initial_obj.
Check @zero.
Check @Limit.
Check @DiscreteCat_Functor.
Check @iprod.
Check @HasEqualizers.
Check @Complete.
Check @Sets_wif.
Check @Sets_initial_characterization.
Check @Sets_initial_recovered.
Check @Sets_roundtrip_iso.
Check @Parallel_ParX_WeaklyInitial.
Check @sols_of_wif.
Check @sols_of_wif_index.
Check @sols_of_comma_initial.
Check @SolutionSet.
Check @sol_index.
Check @poly_unit.
Check bool.
Check @projT2.
