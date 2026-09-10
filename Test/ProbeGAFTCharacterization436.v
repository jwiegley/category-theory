(** * Probe for the Freyd characterization (issue #436)

    Pins the measured boundaries of Adjunction/GAFT.v's necessity direction
    and of the biconditional, with negatives of four kinds kept lexically
    apart.  FORMABILITY: n7, a [SolutionSet] has four fields and no fifth —
    there is no uniqueness clause, so "solution set" here is weak
    factorization and nothing more.  CONVERSION: n1, the direct singleton
    family and Mac Lane's route through the comma-initial object agree on
    every data field but are not the same term; n8, the member is [F d] and
    not [F (U (F d))]; n3, a general solution set is not a singleton, which
    is what makes the necessity direction's singleton a real choice; n9, the
    manufactured family at [Id : Sets ⟶ Sets] agrees with the hand-built
    [Sets_Id_SolutionSet] in index, member and arrow but is not the same
    record, the two covering witnesses differing.  TYPING: n4, the
    sufficient direction keeps all three premises — dropping continuity does
    not ascribe.  UNIVERSE: n6, the biconditional inherits [GAFT]'s pin of
    both hom universes to [Set] — which the necessity direction does NOT,
    the accepted control beside it being that same statement at a category
    with [Set] strictly below its homs.

    The [eq_refl] readbacks are positive controls: the three data fields of
    the manufactured family, the collapse of the comma route's arrow to the
    unit, the identity of the biconditional's reverse half with [GAFT], and
    the [Sets] cross-check that reverse half IS the application the tree
    already had.  Each refutation was stripped one at a time in a copy of
    the whole file; the import list mirrors the two targets'. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe436_absent_name.

(** ** A: FORMABILITY — no uniqueness is asked of a solution set *)

Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @sol_covers.

(* n7 FORMABILITY: and there is no fifth field *)
Fail Check @sol_unique.

(** ** B: CONVERSION — how far the unit family reads back *)

Section Conversion.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (d : D).

Example p436_index : sol_index (solution_set_of_adjunction A d) = poly_unit
  := eq_refl.

Example p436_obj (u : poly_unit) :
  sol_obj (solution_set_of_adjunction A d) u = F d := eq_refl.

Example p436_arr (u : poly_unit) :
  sol_arr (solution_set_of_adjunction A d) u = @unit _ _ _ _ A d := eq_refl.

(* control: Mac Lane's route collapses to the same arrow *)
Example p436_via_arr (u : poly_unit) :
  sol_arr (solution_set_of_adjunction_via_comma A d) u = @unit _ _ _ _ A d
  := eq_refl.

(* n1 CONVERSION: the two routes are nevertheless not the same term *)
Fail Example p436_routes_agree :
  solution_set_of_adjunction A d = solution_set_of_adjunction_via_comma A d
  := eq_refl.

(* n8 CONVERSION: the member is [F d], not [F (U (F d))] *)
Fail Example p436_member_is_FUF (u : poly_unit) :
  sol_obj (solution_set_of_adjunction A d) u = F (U (F d)) := eq_refl.

(* control: a solution set built from a weakly initial family keeps that
   family's index *)
Example p436_wif_index (W : WeaklyInitialFamily (=(d) ↓ U)) :
  sol_index (sols_of_wif U d W) = wif_index W := eq_refl.

(* n3 CONVERSION: so a general solution set is not a singleton *)
Fail Example p436_general_is_singleton (W : WeaklyInitialFamily (=(d) ↓ U)) :
  sol_index (sols_of_wif U d W) = poly_unit := eq_refl.

End Conversion.

(** ** C: TYPING — the sufficient direction keeps all three premises *)

Check (fun (C D : Category) (U : C ⟶ D) (comp : @Complete C)
           (cont : @PreservesImageLimit C D U)
           (sols : ∀ d : D, SolutionSet U d) => GAFT U comp cont sols).

(* n4 TYPING: completeness and a solution set alone do not ascribe *)
Fail Check (fun (C D : Category) (U : C ⟶ D) (comp : @Complete C)
                (sols : ∀ d : D, SolutionSet U d) => GAFT U comp sols).

(** ** D: UNIVERSE — the biconditional inherits GAFT's pin, the converse
        direction does not *)

Monomorphic Universes p436o p436h p436p.
Monomorphic Constraint Set < p436h.

(* control: necessity is free of the pin *)
Check (fun (Cu : Category@{p436o p436h p436p}) (Du : Category@{p436o p436h p436p})
           (F : Du ⟶ Cu) (U : Cu ⟶ Du) => @solution_set_of_adjunction Cu Du F U).

(* n6 UNIVERSE: the biconditional is refused there *)
Fail Check (fun (Cu : Category@{p436o p436h p436p})
                (Du : Category@{p436o p436h p436p})
                (U : Cu ⟶ Du) => @GAFT_iff Cu Du U).

(** ** E: readbacks, and the [Sets] cross-check *)

Example p436_rev_is_GAFT {C D : Category} (U : C ⟶ D) (comp : @Complete C)
  (cont : @PreservesImageLimit C D U) (sols : ∀ d : D, SolutionSet U d) :
  GAFT_iff_rev U comp (cont, sols) = GAFT U comp cont sols := eq_refl.

Example p436_sets_rev :
  Sets_Id_has_left = GAFT_at_Sets_Id := eq_refl.

Example p436_sets_index (d : Sets) :
  sol_index (solution_set_of_adjunction (@adj_id Sets) d)
    = sol_index (Sets_Id_SolutionSet d) := eq_refl.

Example p436_sets_obj (d : Sets) (u : poly_unit) :
  sol_obj (solution_set_of_adjunction (@adj_id Sets) d) u
    = sol_obj (Sets_Id_SolutionSet d) u := eq_refl.

Example p436_sets_arr (d : Sets) (u : poly_unit) :
  sol_arr (solution_set_of_adjunction (@adj_id Sets) d) u
    = sol_arr (Sets_Id_SolutionSet d) u := eq_refl.

(* n9 CONVERSION: the two families are not the same record — the covering
   witnesses differ *)
Fail Example p436_sets_same_record (d : Sets) :
  solution_set_of_adjunction (@adj_id Sets) d = Sets_Id_SolutionSet d
  := eq_refl.

(** ** F: guard block *)

Check @solution_set_of_adjunction.
Check @solution_set_of_adjunction_index.
Check @solution_set_of_adjunction_obj.
Check @solution_set_of_adjunction_arr.
Check @universal_arrow_of_adjunction.
Check @comma_initial_of_adjunction.
Check @solution_set_of_adjunction_via_comma.
Check @solution_set_via_comma_arr.
Check @GAFT_iff.
Check @GAFT_iff_fwd.
Check @GAFT_iff_rev.
Check @GAFT_iff_rev_is_GAFT.
Check @GAFT_iff_at_Sets_Id.
Check @Sets_Id_has_left.
Check @Sets_Id_has_left_is_GAFT_at_Sets_Id.
Check @Sets_Id_SolutionSet_of_adjunction.
Check @Sets_Id_sols_index.
Check @Sets_Id_sols_obj.
Check @Sets_Id_sols_arr.
Check @GAFT.
Check @GAFT_from_initials.
Check @GAFT_via_comma_initial.
Check @comma_initial_of_sols.
Check @sols_of_wif.
Check @SolutionSet.
Check @right_adjoint_PreservesImageLimit.
Check @Sets_Id_SolutionSet.
Check @Sets_Id_PreservesImageLimit.
Check @GAFT_at_Sets_Id.
