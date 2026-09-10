(** * Probe for Adjunction/Representability/Sets.v (issue #437)

    Pins the measured boundaries of the representability theorem with
    negatives of three kinds, kept lexically apart: CONVERSION (N1: the
    element-wise solution set of Definition 3 and the hom-shaped
    [SolutionSet] at the singleton are different records, related by
    [sols_of_esols]/[esols_of_sols] and not by conversion; N2: [HomAfter K
    1] is [Hom(1,−) ◯ K] on the nose — the accepted control — but NOT [K]
    itself, which is why [homafter_one_iso] exists); TYPING (N3: the
    theorem consumes the cone-level [PreservesImageLimit], and the
    apex-only [PreservesAllLimits] does not ascribe — GAFT's own
    distinction; N5: [HasSetsCopowers] indexes by an object of [Sets], and
    the [Type]-indexed shape the tree's copowers have does not ascribe,
    which is exactly why §V.8 Exercise 1's converse is conditional);
    UNIVERSE (N4: the theorem inherits GAFT's pin of the hom AND proof
    universes, so a category declared with them apart is refused).  The
    [eq_refl] readbacks are positive controls: both passages between the
    two solution-set forms keep index and objects, the transported
    representation keeps its object, the left-adjoint route returns the
    adjoint at the singleton, and the two [Sets] witnesses compute.  Each
    refutation was stripped one at a time in a copy of the whole file; the
    import list mirrors the target's. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.Representability.
Require Import Category.Adjunction.Representability.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe437_absent_name.

(** ** A: CONVERSION — Definition 3 against the hom-shaped solution set *)

(* control: the two passages, and the index kept on the nose *)
Check (fun (C : Category) (K : C ⟶ Sets) => @sols_of_esols C K).
Check (fun (C : Category) (K : C ⟶ Sets) => @esols_of_sols C K).

Example p437_index (C : Category) (K : C ⟶ Sets) (E : ElementSolutionSet K) :
  sol_index (sols_of_esols K E) = esol_index E := eq_refl.

(* N1 CONVERSION: the two records are not the same type *)
Fail Example p437_same_record (C : Category) (K : C ⟶ Sets) :
  ElementSolutionSet K = SolutionSet K SetsOne := eq_refl.

(* control: [HomAfter K 1] IS the composite with the points functor *)
Example p437_homafter (C : Category) (K : C ⟶ Sets) :
  HomAfter K SetsOne = Compose (fobj[Curried_Hom Sets] SetsOne) K := eq_refl.

(* N2 CONVERSION: it is not [K] itself — [homafter_one_iso] is needed *)
Fail Example p437_homafter_is_K (C : Category) (K : C ⟶ Sets) :
  HomAfter K SetsOne = K := eq_refl.

(** ** B: TYPING — the preservation class, and the copower index *)

(* control: the theorem at its stated hypotheses *)
Check (fun (C : Category) (K : C ⟶ Sets) (comp : @Complete C)
           (cont : @PreservesImageLimit C Sets K) (E : ElementSolutionSet K) =>
         representability_theorem K comp cont E).

(* N3 TYPING: the apex-only class does not ascribe where the cone-level one
   is asked for *)
Fail Check (fun (C : Category) (K : C ⟶ Sets) (comp : @Complete C)
                (cont : @PreservesAllLimits C Sets K)
                (E : ElementSolutionSet K) =>
              representability_theorem K comp cont E).

(* control: the copower hypothesis, indexed by an object of [Sets] *)
Check (fun (C : Category) => HasSetsCopowers C).

(* N5 TYPING: a [Type]-indexed family — the shape the tree's copowers have
   — is not a [HasSetsCopowers] *)
Fail Definition p437_type_copowers (C : Category)
  (cop : ∀ (b : C) (X : Type),
      Representable (HomAfter (fobj[@Curried_Hom C] b) X))
  : HasSetsCopowers C := cop.

(** ** C: UNIVERSE — the theorem inherits GAFT's pin *)

Section Formability.

Universes so sh sp.
Constraint sh < sp.

Context (Cu : Category@{so sh sp}).

(* control: the category itself is formable, and so are its homs *)
Check (@hom Cu).

(* N4 UNIVERSE: the theorem's comma-initial step identifies hom with proof,
   so it cannot be read at [Cu] *)
Fail Check (fun (K : Cu ⟶ Sets) (comp : @Complete Cu)
                (cont : @PreservesImageLimit Cu Sets K)
                (E : ElementSolutionSet K) =>
              representability_theorem K comp cont E).

End Formability.

(** ** D: readbacks *)

Example p437_esol_obj (C : Category) (K : C ⟶ Sets) (E : ElementSolutionSet K)
  (i : esol_index E) : sol_obj (sols_of_esols K E) i = esol_obj E i := eq_refl.

Example p437_esols_elem (C : Category) (K : C ⟶ Sets)
  (S : SolutionSet K SetsOne) (i : sol_index S) :
  esol_elem (esols_of_sols K S) i = sol_arr S i ttt := eq_refl.

Example p437_transport_obj (C : Category) (F G : C ⟶ Sets)
  (i : F ≅[[C, Sets]] G) (R : Representable F) :
  @repr_obj C G (Representable_transport i R) = @repr_obj C F R := eq_refl.

Example p437_left_adjoint_obj (C : Category) (K : C ⟶ Sets) (L : Sets ⟶ C)
  (A : L ⊣ K) :
  @repr_obj C K (representable_of_left_adjoint K A) = L SetsOne := eq_refl.

Example p437_sets_id_obj :
  @repr_obj Sets (@Id Sets) Sets_Id_repr_of_adjoint
    = projT1 GAFT_at_Sets_Id SetsOne := eq_refl.

Check (Sets_points_esol_obj).
Check (Sets_points_iso
         : @repr_obj Sets Sets_points Sets_points_repr ≅ SetsOne).
Check (Sets_Id_repr_iso
         : @repr_obj Sets (@Id Sets) Sets_Id_repr ≅ SetsOne).
Check (@representability_iff).
Check (@saft_representable).
Check (@left_adjoint_of_representable_Sets).

(** ** Guard block *)

Check @ElementSolutionSet.
Check @esol_index.
Check @esol_obj.
Check @esol_elem.
Check @esol_covers.
Check @sols_of_esols.
Check @esols_of_sols.
Check @representable_of_comma_initial.
Check @representability_theorem.
Check @representability_iff.
Check @Representable_transport.
Check @homafter_one_iso.
Check @representable_of_left_adjoint.
Check @continuous_of_representable.
Check @preserves_image_of_representable.
Check @saft_representable.
Check @HasSetsCopowers.
Check @homafter_whisker.
Check @left_adjoint_of_representable_Sets.
Check @comma_initial_of_sols.
Check @GAFT_via_comma_initial.
Check @SolutionSet.
Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @Representable.
Check @repr_obj.
Check @represented.
Check @HomAfter.
Check @Curried_Hom.
Check @global_element.
Check @PreservesImageLimit.
Check @PreservesAllLimits.
Check @Complete.
Check @SetsOne.
Check @Sets_points.
Check @Sets_points_repr.
Check @Sets_Id_repr.
Check @Sets_Id_repr_of_adjoint.
Check @GAFT_at_Sets_Id.
