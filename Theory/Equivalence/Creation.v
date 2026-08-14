Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Limit.

Generalizable All Variables.

(** * Equivalences create limits, and right adjoints preserve cones *)

(* nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/adjoint+functor#preservation

   [equivalence_creates_limits] (Theory/Equivalence/Limit.v:486) transports
   a limit; on its own it relates neither the apexes nor the legs, and its
   name has been ahead of its statement.  This file closes the gap in the
   strong direction, keeping the name: [equivalence_CreatesLimit] exhibits
   the existing constant as the existence datum of a genuine [CreatesLimit]
   instance (Structure/Limit/Creation.v), with the comparison supplied by
   uniqueness of limits up to cone isomorphism and the reflection clause by
   [ff_reflect_ump] — every equivalence is full and faithful, and the leg
   hypothesis discharges by [reflexivity] because the legs of [FCone] ARE
   the image legs.  No constant is renamed, so [equivalence_creates_colimits]
   (Theory/Equivalence/Limit.v:582) and every downstream user are untouched.

   The construction above does not give a strict lift: the apex
   [equivalence_creates_limits] produces is the quasi-inverse of the given
   apex, related to it only by an isomorphism.  That is the case Riehl's
   remark on Definition 3.4.7 (Category Theory in Context, 2nd ed., p. 105)
   has in mind — strict creation is not invariant under equivalence, so no
   strict witness is available for a general [F].  It is not a claim about
   every equivalence: [Id[C]] is one, and it strictly creates every limit,
   both clauses by [reflexivity].  [Id_CreatesAllLimits] below is therefore
   offered as a [CreatesLimit] witness only; the strict class is witnessed
   at generality by [EM_Forget] (Monad/Eilenberg/Moore/Limit.v).

   The cone-level reading of RAPL, [right_adjoint_PreservesLimitCone],
   lives at its natural home in Adjunction/Continuity.v. *)

(** ** Right adjoints preserve limiting cones, not merely limit apexes *)

Section EquivCreates.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(* An equivalence is (the left half of) an adjoint equivalence, hence a
   right adjoint, hence cone-level continuous. *)

Definition equivalence_PreservesLimitCone {J : Category} (K : J ⟶ C) :
  PreservesLimitCone K F :=
  right_adjoint_PreservesLimitCone
    (AdjointEquivalence_swap_adjunction (Equivalence_to_AdjointEquivalence E)) K.

(* Reflection, from full faithfulness.  The leg side condition of
   [ff_reflect_ump] (Theory/Equivalence/Limit.v:391) is [reflexivity] here
   exactly because [FCone]'s legs are the image legs. *)

Definition equivalence_ReflectsLimitCone {J : Category} (K : J ⟶ C) :
  ReflectsLimitCone K F :=
  fun M H =>
    @ff_reflect_ump C D F (Equivalence_Full E) (Equivalence_Faithful E)
      J K M (limitcone_isalimit H) (fun x => reflexivity _).

(* The naming defect of [equivalence_creates_limits], resolved by proof:
   that constant supplies the lift, and the two remaining clauses are the
   two lemmas above. *)

Definition equivalence_CreatesLimit {J : Category} (K : J ⟶ C) :
  CreatesLimit K F.
Proof using E.
  unshelve refine
    {| creates_lift := fun N HN =>
         @limit_cone _ _ _
           (equivalence_creates_limits E K (@Build_Limit J D (F ◯ K) N HN)) |}.
  - intros N HN.
    exact (limitcone_iso
             (equivalence_PreservesLimitCone K _ (limit_limitcone _)) HN).
  - exact (equivalence_ReflectsLimitCone K).
Defined.

Definition equivalence_CreatesAllLimits : CreatesAllLimits F :=
  fun J K => equivalence_CreatesLimit K.

End EquivCreates.

(** ** The identity functor creates every limit *)

Definition Id_CreatesAllLimits {C : Category} : CreatesAllLimits Id[C] :=
  equivalence_CreatesAllLimits (@EquivalenceOfCategories_Id C).
