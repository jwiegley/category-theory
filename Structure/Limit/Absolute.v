Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Two.
Require Import Category.Construction.Lift.

Generalizable All Variables.

(** * Absolute limits and colimits, at cone level *)

(* Book:   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
           §VI.6, book p. 149 (PDF p. 158), item maclane:VI.6:def2
   Book:   Riehl, "Category Theory in Context", 2nd ed., §3.4, Exercise
           3.4.vi(iii), printed p. 109 (PDF p. 129), item
           riehl:3.4:def-absolute (the issue's appended box)
   Paper:  Paré, "On absolute colimits", J. Algebra 19 (1971) 80-95
   nLab:   https://ncatlab.org/nlab/show/absolute+colimit
   nLab:   https://ncatlab.org/nlab/show/preserved+limit

   WHAT THE BOOKS SAY.  Mac Lane, after defining the absolute coequalizer
   (Structure/Coequalizer/Absolute.v): "In the same way one can define
   absolute colimits (or absolute limits) of any other type (Paré
   [1971a])."  Riehl, of the equalizer and the coequalizer of a split
   idempotent (her (i)) and of B as both the limit and the colimit of
   the diagram the idempotent defines (her (ii)): "Prove that the
   aforementioned limits and colimits are preserved by any functor.
   Co/limits with this property are called absolute co/limits."

   THE DEFINITION IS AT CONE LEVEL.  [AbsoluteLimitCone N] says that the
   image [FCone F N] of the cone [N] is a limiting cone for EVERY functor
   [F : C ⟶ D]; [AbsoluteColimitCocone N] is the same for cocones.  The
   image legs are fmap[F] of N's legs, so "preserved" is Mac Lane's §V.4
   sense, [PreservesLimitCone] of Structure/Limit/Preservation.v, and
   not the apex-only [PreservesLimit], whose legs are unconstrained
   (Construction/Comma/Limit.v's note; Structure/Limit/Preservation/
   Separation.v separates the two for one functor).  The predicates
   apply to a bundled [L : Limit K] or [L : Colimit K] through the
   coercion [limit_cone], so absoluteness is predicated of a given
   (co)limit (controls in Test/ProbeAbsolute477.v).

   THE APEX-ONLY PREDICATES THIS DOES NOT REPLACE.  Structure/Limit/
   Constant.v (#356) already declares [AbsoluteLimit G c] and
   [AbsoluteColimit G c]: for every F, the APEX F c carries SOME
   (co)limit structure of F ◯ G.  Those names being taken, the cone-level
   predicates are named like [IsLimitCone] and [PreservesLimitCone].
   The map from the cone-level reading to the apex-only one,
   [AbsoluteLimitCone_apex] and [AbsoluteColimitCocone_apex], lives in
   Constant.v, typed there by [AbsoluteLimit] and [AbsoluteColimit] by
   name; Constant.v requires this file for it, which adds six [Category]
   modules to what a [Require] of Constant.v loads (103 before, 109
   after, by [Print Libraries]).  No converse is proved and no
   separation is attempted, so the apex-only reading is not shown
   strictly weaker.

   THE CLOSURE THEORY.
     - An absolute limit is a limit: [AbsoluteLimitCone_IsLimitCone],
       the instance F := Id, as Mac Lane reads "automatically".  The
       image of N under [Id] has N's apex and legs at [eq_refl]
       ([FCone_Id_apex], [FCone_Id_leg]); only [Id ◯ K] is not [K]
       (refused at [eq_refl] in the probe), so the competing cone is
       repackaged (Preservation.v's [cone_id_comp]).
     - Absoluteness is preservation by every functor:
       [AbsoluteLimitCone_preserves] gives [PreservesLimitCone K F] for
       every F, through Structure/Limit/Comparison.v's
       [PreservesLimitCone_of_cone] (one limiting cone suffices), and
       [AbsoluteLimitCone_of_preserves] is the converse.  The colimit
       side needs that lemma's cocone twin, which the tree did not have;
       #477 adds it beside its twin, as Comparison.v's
       [PreservesColimitCocone_of_cocone], over Preservation.v's
       [FCocone_iso], itself added beside [FCone_iso].
     - It is invariant: along a cone isomorphism
       ([AbsoluteLimitCone_transport]) and hence across limiting cones of
       the same diagram ([AbsoluteLimitCone_limitcone]), so it belongs to
       the limit and not to the cone chosen to represent it.
     - It is closed under functors: the image of an absolute limit under
       any G is absolute ([AbsoluteLimitCone_image], with Preservation.v's
       [cocone_assoc_inv], added beside [cone_assoc_inv], for the colimit
       twin).
     - Each with its colimit twin.

   THE INSTANCES ARE ORDERED.  Each predicate is a family of instances,
   one per target object level (UNIVERSES), and the instances are not
   independent: through Construction/Lift.v's [LiftCat], which re-reads
   a category at higher universe levels, an instance at a target level
   implies the instance at every lower one ([AbsoluteLimitCone_down]),
   and an instance at any level at or above C's own is limiting
   ([AbsoluteLimitCone_IsLimitCone_up]); each with its colimit twin,
   through the duality maps.

   DUALITY IS TWO ONE-LINE MAPS.  [AbsoluteColimitCocone_op] and
   [AbsoluteColimitCocone_of_op] carry an absolute colimit to an absolute
   limit in the opposite and back, through Preservation.v's
   [cone_op_comp] and [cone_op_comp_inv], and are mutually inverse at
   [eq_refl] ([AbsoluteColimitCocone_of_op_op],
   [AbsoluteColimitCocone_op_of_op]).  The two predicates are not one
   term (refused at [eq_refl] in the probe): one quantifies over functors
   out of C, the other out of C^op.  The colimit side's
   [AbsoluteColimitCocone_IsColimitCocone],
   [AbsoluteColimitCocone_transport] and the colimit twins of the lifted
   readings are derived through the maps; the preservation and image
   clauses are built directly, since [FCocone F N] and [FCone F^op N] are
   cones over different functors.

   NON-VACUITY.  Absolute is strictly more than limiting: in the walking
   arrow [_2] the empty cone at [TwoY] is a limit
   ([two_terminal_IsLimitCone]) and is not absolute
   ([two_terminal_not_absolute]): the constant functor at [TwoX] sends
   it to [TwoX], which receives no arrow from [TwoY].  Dually
   [two_initial_IsColimitCocone] and [two_initial_not_absolute].

   STRENGTHS.  The four [Example]s hold at [eq_refl] and are restated in
   the probe.  Every other statement is a map between predicates; none
   is an equation between morphisms.

   UNIVERSES, by [About] on every constant.  [AbsoluteLimitCone@{jo co ch
   do u u0 u1 u2}] is over [J : Category@{jo ch ch}] and
   [C : Category@{co ch ch}] and quantifies over [D : Category@{do ch
   ch}]: every target at any object level [do], a universe OF THE
   PREDICATE, with C's hom-and-proof level.  Its sort [u] lies strictly
   above [do] and [ch] ("do < u", "ch < u"), so the predicate lives
   above the categories it quantifies over, no instance quantifies over
   every category, and the instances form the ordered family above.
     The hom level is shared, and three carriers impose it, each first
   in its own place.  (1) Preservation.v's [cone_leg] and [IsLimitCone]
   are declared over bare binders and minimize to one hom level for a
   shape and its ambient: the probe refuses [IsLimitCone N] over a
   diagram whose shape has strictly smaller hom-sets than its target
   (R7), while accepting the cones themselves (C43).  As [Cone] and
   [Functor] bound a shape's hom level by its ambient's, and [F : C ⟶ D]
   bounds D's below by C's, [IsLimitCone (FCone F N)] alone pins D's hom
   level to C's.  (2) [Compose] (Theory/Functor.v) gives its three
   categories one hom-and-proof level, and [FCone] is over [F ◯ K]: the
   probe refuses [F ◯ K] with C's homs strictly below D's while
   accepting [C ⟶ D] itself (R3, C10).  (3) For cocones,
   [Opposite_Functor] (Functor/Opposite.v) gives its source and target
   one hom level, and [Cocone F] is [Cone (F^op)] (Structure/Cone.v):
   the probe refuses [F^op] for a functor whose source has strictly
   smaller hom-sets than its target (R8).  None of the three is
   structural.  The same definitions with their binders written out
   compile with the shape's or source's hom level at or below the
   other's: [cone_leg] and [IsLimitCone] (C41, accepted where R7 is
   refused, C44), and [Opposite_Functor] (C42, with cones over it, C45);
   [Compose], over three hom levels with the same two obligation proofs,
   was measured in a scratch file and is not pinned here.  Lifting the
   cap is therefore a matter of annotating those binders tree-wide,
   which #477 does not attempt.  The cap does exclude part of Riehl's
   "any functor": the probe accepts the Yoneda embedding of C as a
   target when C's objects lie strictly below its hom-sets (C46) and
   refuses it when they lie strictly above (R11).
     The binders are written out on every constant of the predicates and
   their closure theory, and no block carries an equation; the
   non-vacuity constants leave theirs to Rocq, and [empty_shape_cocone]
   comes out over categories whose hom level is [Set] only, carrier (3)
   identifying the hom levels of [_0] and its target and [_0]'s being
   [Set].  [AbsoluteLimitCone_IsLimitCone] consumes the instance whose
   target is C's own levels, [AbsoluteLimitCone@{jo co ch co …}], which
   is what "take F := Id" means; the probe refuses it from a target
   object level above C's (R4), a pin of that lemma's signature and not
   of what the predicate yields: R4's statement is accepted through
   [AbsoluteLimitCone_IsLimitCone_up] (C22) and through
   [AbsoluteLimitCone_down] (C23), and their colimit twins likewise
   (C24, C25).  [AbsoluteLimitCone_IsLimitCone_up@{jo co ch do …}]
   carries "co <= do", and [AbsoluteLimitCone_down@{jo co ch do eo …}]
   "do <= eo", with no equation; their statements, and their colimit
   twins', name the instances of the predicate they consume and produce
   (six explicit universe instances in four constants), since a level
   bounded below by C's alone would otherwise be minimized to C's.  The
   preservation, transport and image clauses keep [do] free, the
   preservation clauses by taking the limit property as a separate
   hypothesis (consuming the [Id] instance there identified [do] with
   [co], measured).  The non-vacuity results sit at hom level [Set], the
   level of [_0] and [_2].

   STALE PREMISES, dated from gh.  The issue (filed 2026-07-23, the Riehl
   box appended 2026-07-31) says no [Absolute*] identifier exists; that
   was accurate when written and is stale since PR #1229 (merged
   2026-08-31, for #356), which added Constant.v's apex-only predicates.

   NOT DELIVERED.  Paré's theorems: the characterization of absolute
   colimits (preservation by the Yoneda embedding) and of absolute
   coequalizers by splittings.  Any separation of the cone-level and
   apex-only readings.  Absoluteness relative to a class of target
   categories, or to a universe-free reading.  The cone-level
   predicates at a target hom level other than C's, which waits on the
   annotation of the three carriers above.  Riehl's split idempotents
   (issue #957) and Beck's absolute condition (issue #484), which
   consume these predicates. *)

(** ** The two predicates *)

Definition AbsoluteLimitCone@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) : Type :=
  ∀ (D : Category@{do ch ch}) (F : C ⟶ D), IsLimitCone (FCone F N).

Definition AbsoluteColimitCocone@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cocone K) : Type :=
  ∀ (D : Category@{do ch ch}) (F : C ⟶ D), IsColimitCocone (FCocone F N).

(** ** An absolute limit is a limit *)

(* The image of N under [Id] is N on the nose, apex and legs. *)

Example FCone_Id_apex@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) : vertex_obj[FCone Id N] = vertex_obj[N] := eq_refl.

Example FCone_Id_leg@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) (x : J) : cone_leg (FCone Id N) x = cone_leg N x := eq_refl.

(* "Take F := Id": the instance whose target is C's own levels, with the
   competing cone repackaged by Preservation.v's [cone_id_comp]. *)

Definition AbsoluteLimitCone_IsLimitCone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone N) : IsLimitCone N :=
  fun M => A C Id (cone_id_comp M).

(** ** Duality: an absolute colimit is an absolute limit in the opposite *)

Definition AbsoluteColimitCocone_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) :
  @AbsoluteLimitCone (J^op) (C^op) (K^op) N :=
  fun D F M =>
    A (D^op)%category (F^op)%functor
      (@cone_op_comp_inv J C (D^op)%category K (F^op)%functor M).

Definition AbsoluteColimitCocone_of_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : @AbsoluteLimitCone (J^op) (C^op) (K^op) N) :
  AbsoluteColimitCocone N :=
  fun D F M => A (D^op)%category (F^op)%functor (cone_op_comp M).

Example AbsoluteColimitCocone_of_op_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) :
  AbsoluteColimitCocone_of_op (AbsoluteColimitCocone_op A) = A := eq_refl.

Example AbsoluteColimitCocone_op_of_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : @AbsoluteLimitCone (J^op) (C^op) (K^op) N) :
  AbsoluteColimitCocone_op (AbsoluteColimitCocone_of_op A) = A := eq_refl.

Definition AbsoluteColimitCocone_IsColimitCocone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) : IsColimitCocone N :=
  AbsoluteLimitCone_IsLimitCone (AbsoluteColimitCocone_op A).

(** ** Every instance at or above C's levels: the lift *)

(* An absolute limit at ANY target object level at or above C's is a
   limit: C is read at that level by Construction/Lift.v's [LiftCat], and
   [Lift_in C] plays the part of [Id].  The instance of the hypothesis is
   named, the target level [do] being bounded below by [co] alone. *)

Definition AbsoluteLimitCone_IsLimitCone_up@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone@{jo co ch do _ _ _ _} N) :
  IsLimitCone N.
Proof.
  intro M.
  pose (Ml := @Build_Cone J (LiftCat C) (Lift_in C ◯ K)
                (@vertex_obj _ _ _ M)
                (@Build_ACone J (LiftCat C) (@vertex_obj _ _ _ M)
                   (Lift_in C ◯ K)
                   (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) x)
                   (fun x y f =>
                      @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f))).
  pose (U := A (LiftCat C) (Lift_in C) Ml).
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - intro x. exact (unique_property U x).
  - intros v Hv. exact (uniqueness U v Hv).
Defined.

Definition AbsoluteColimitCocone_IsColimitCocone_up@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone@{jo co ch do _ _ _ _} N) :
  IsColimitCocone N :=
  AbsoluteLimitCone_IsLimitCone_up (AbsoluteColimitCocone_op A).

(* Each instance implies every lower one: a target D at a level below the
   hypothesis' is read at that level, and [Lift_after F] replaces F. *)

Definition AbsoluteLimitCone_down@{jo co ch do eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone@{jo co ch eo _ _ _ _} N) :
  AbsoluteLimitCone@{jo co ch do _ _ _ _} N.
Proof.
  intros D F M.
  pose (Ml := @Build_Cone J (LiftCat D) (Lift_after F ◯ K)
                (@vertex_obj _ _ _ M)
                (@Build_ACone J (LiftCat D) (@vertex_obj _ _ _ M)
                   (Lift_after F ◯ K)
                   (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) x)
                   (fun x y f =>
                      @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f))).
  pose (U := A (LiftCat D) (Lift_after F) Ml).
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - intro x. exact (unique_property U x).
  - intros v Hv. exact (uniqueness U v Hv).
Defined.

Definition AbsoluteColimitCocone_down@{jo co ch do eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone@{jo co ch eo _ _ _ _} N) :
  AbsoluteColimitCocone@{jo co ch do _ _ _ _} N :=
  AbsoluteColimitCocone_of_op
    (AbsoluteLimitCone_down (AbsoluteColimitCocone_op A)).

(** ** Absoluteness is preservation by every functor *)

Definition AbsoluteLimitCone_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (HN : IsLimitCone N) (A : AbsoluteLimitCone N)
  (D : Category@{do ch ch}) (F : C ⟶ D) : PreservesLimitCone K F :=
  PreservesLimitCone_of_cone F N HN (A D F).

Definition AbsoluteLimitCone_of_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (HN : IsLimitCone N)
  (P : ∀ (D : Category@{do ch ch}) (F : C ⟶ D), PreservesLimitCone K F) :
  AbsoluteLimitCone N :=
  fun D F => P D F N HN.

Definition AbsoluteColimitCocone_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (HN : IsColimitCocone N) (A : AbsoluteColimitCocone N)
  (D : Category@{do ch ch}) (F : C ⟶ D) : PreservesColimitCocone K F :=
  PreservesColimitCocone_of_cocone F N HN (A D F).

Definition AbsoluteColimitCocone_of_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (HN : IsColimitCocone N)
  (P : ∀ (D : Category@{do ch ch}) (F : C ⟶ D),
         PreservesColimitCocone K F) :
  AbsoluteColimitCocone N :=
  fun D F => P D F N HN.

(** ** Invariance: along cone isomorphisms, and across limiting cones *)

Definition AbsoluteLimitCone_transport@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cone K} (i : ConeIso N M) (A : AbsoluteLimitCone N) :
  AbsoluteLimitCone M :=
  fun D F => limitcone_transport (FCone_iso F i) (A D F).

Definition AbsoluteColimitCocone_transport@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cocone K} (i : ConeIso N M) (A : AbsoluteColimitCocone N) :
  AbsoluteColimitCocone M :=
  AbsoluteColimitCocone_of_op
    (AbsoluteLimitCone_transport i (AbsoluteColimitCocone_op A)).

(* Absoluteness belongs to the diagram's limit, not to the cone chosen to
   represent it: any other limiting cone is absolute too. *)

Definition AbsoluteLimitCone_limitcone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cone K} (HN : IsLimitCone N) (HM : IsLimitCone M)
  (A : AbsoluteLimitCone N) : AbsoluteLimitCone M :=
  AbsoluteLimitCone_transport (limitcone_iso HN HM) A.

Definition AbsoluteColimitCocone_colimitcocone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cocone K} (HN : IsColimitCocone N) (HM : IsColimitCocone M)
  (A : AbsoluteColimitCocone N) : AbsoluteColimitCocone M :=
  AbsoluteColimitCocone_transport (colimitcocone_iso HN HM) A.

(** ** Closure under functors: the image of an absolute limit is absolute *)

Definition AbsoluteLimitCone_image@{jo co ch eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {E : Category@{eo ch ch}} {K : J ⟶ C} {N : Cone K}
  (A : AbsoluteLimitCone N) (G : C ⟶ E) : AbsoluteLimitCone (FCone G N) :=
  fun D H => islimitcone_assoc (A D (H ◯ G)).

Definition AbsoluteColimitCocone_image@{jo co ch eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {E : Category@{eo ch ch}} {K : J ⟶ C} {N : Cocone K}
  (A : AbsoluteColimitCocone N) (G : C ⟶ E) :
  AbsoluteColimitCocone (FCocone G N) :=
  fun D H M => A D (H ◯ G) (cocone_assoc_inv M).

(** ** Non-vacuity: a limit and a colimit that are not absolute *)


(* Cones and cocones over a diagram of the empty shape are bare apexes. *)

Definition empty_shape_cone {C : Category} (G : _0 ⟶ C) (c : C) : Cone G.
Proof.
  unshelve refine (@Build_Cone _0 C G c _).
  unshelve econstructor; intro x; destruct x.
Defined.

Definition empty_shape_cocone {C : Category} (G : _0 ⟶ C) (c : C) :
  Cocone G.
Proof.
  unshelve refine (@Build_Cone (_0^op) (C^op) (G^op) c _).
  unshelve econstructor; intro x; destruct x.
Defined.

(* In the walking arrow [_2], [TwoY] is terminal and [TwoX] initial. *)

Definition two_into_TwoY (m : TwoObj) : TwoHom m TwoY :=
  match m with TwoX => TwoXY | TwoY => TwoIdY end.

Definition two_out_of_TwoX (m : TwoObj) : TwoHom TwoX m :=
  match m with TwoX => TwoIdX | TwoY => TwoXY end.

Definition two_terminal_IsLimitCone :
  IsLimitCone (empty_shape_cone (From_0 _2) (TwoY : _2)).
Proof.
  intro M.
  unshelve eapply Build_Unique.
  - exact (two_into_TwoY (@vertex_obj _ _ _ M)).
  - intro x; destruct x.
  - intros v _; apply Two_thin.
Defined.

Definition two_initial_IsColimitCocone :
  IsColimitCocone (empty_shape_cocone (From_0 _2) (TwoX : _2)).
Proof.
  intro M.
  unshelve eapply Build_Unique.
  - exact (two_out_of_TwoX (@vertex_obj _ _ _ M)).
  - intro x; destruct x.
  - intros v _; apply Two_thin.
Defined.

(* The constant functor at [TwoX] sends the terminal [TwoY] to [TwoX],
   which receives no arrow from [TwoY]; dually the constant functor at
   [TwoY] sends the initial [TwoX] to [TwoY]. *)

Theorem two_terminal_not_absolute :
  AbsoluteLimitCone (empty_shape_cone (From_0 _2) (TwoY : _2)) → False.
Proof.
  intro A.
  destruct (A _2 Δ[_2]((TwoX : _2))
              (empty_shape_cone (Δ[_2]((TwoX : _2)) ◯ From_0 _2)
                 (TwoY : _2)))
    as [u _ _].
  exact (TwoHom_Y_X_absurd u).
Qed.

Theorem two_initial_not_absolute :
  AbsoluteColimitCocone (empty_shape_cocone (From_0 _2) (TwoX : _2)) →
  False.
Proof.
  intro A.
  destruct (A _2 Δ[_2]((TwoY : _2))
              (empty_shape_cocone (Δ[_2]((TwoY : _2)) ◯ From_0 _2)
                 (TwoX : _2)))
    as [u _ _].
  exact (TwoHom_Y_X_absurd u).
Qed.
