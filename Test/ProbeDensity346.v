Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Elements.Kan.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Density.

Generalizable All Variables.

(** * Boundary probes for Theory/Density.v (issue #346) *)

(* WHY THIS FILE EXISTS, AND WHAT IT ADDS OVER THE IN-FILE PROBES.

   Theory/Density.v already carries four negatives with their controls.
   Those are sound, but they cannot guard the SIX constants the negatives
   name that are declared in that same file -- [DensityDiagram],
   [ElementsOp], [density_med], [density_inj], [density] and
   [PDensityDiagram].  A rename of any of them would rewrite the [Fail]
   bodies and the in-file controls IN LOCKSTEP, leaving every negative
   vacuously green while the build stayed clean.  That is the same
   instrument defect this tree records elsewhere: a rename simulation is
   meaningless for a constant declared in the file under test, and the
   remedy is to restate the boundary from OUTSIDE, where the names are
   not renamed alongside.

   This file is that outside.  It Requires Category.Theory.Density and
   names all six, so a rename upstream breaks THIS file loudly instead of
   silencing a probe.  The in-file negatives already cover the six DONOR
   constants they name ([Curried_Hom], [Curried_CoHom], [Elements_proj],
   [PElements_proj], [Cocone], [cocone_inj]) at 6/6, so between the two
   files every constant a negative names is guarded.

   If the [Fail] commands here stop failing, that is a real change in the
   development and this file breaks the build on purpose. *)

Section ProbeDensityConversion.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* CONTROL: the presheaf diagram is nameable and agrees on objects. *)
Check @PDensityDiagram.
Check (fun (c : C) (x : P c) =>
         PDensityDiagram P ((c; x) : PElements P)).

(* NEGATIVE 1, CONVERSION.  The two functor RECORDS are not equal: they
   differ in their functor-law fields, which [PElements_proj] supplies as
   opaque [Program] obligations while the composite rebuilds them.
   Stripped: "cannot unify PDensityDiagram P and
   Curried_CoHom C ◯ PElements_proj P". *)
Fail Example probe_pdd_records :
  PDensityDiagram P = Curried_CoHom C ◯ PElements_proj P := eq_refl.

End ProbeDensityConversion.

Section ProbeDensityMediator.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* CONTROLS: all four file-local names below are nameable, and the
   triangle holds at [≈]. *)
Check @DensityDiagram.
Check @ElementsOp.
Check @density.
Example probe_ctrl_diag :
  DensityDiagram K = Curried_Hom D ◯ (Elements_proj K)^op := eq_refl.
Definition probe_ctrl_commutes (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j ≈ cocone_inj M j
  := density_med_commutes K M j.

(* NEGATIVE 2, CONVERSION.  The mediating triangle is [≈] and NOT
   [eq_refl]: the mediator evaluates the competing cocone at the index
   object (e, fmap[K] g x) while the right-hand side evaluates it at j,
   and the two are reconciled only by cocone coherence at
   [Elements_lift], which is a [≈] fact.  Stripped: "cannot unify
   density_med K M ∘ density_inj K j and cocone_inj M j". *)
Fail Example probe_med_strict (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j = cocone_inj M j := eq_refl.

(* CONTROL for negative 3: the composite IS formable with the OPPOSITE of
   the projection, which is what the diagram uses. *)
Check (Curried_Hom D ◯ (Elements_proj K)^op).

(* NEGATIVE 3, TYPING -- the variance.  The diagram of representables
   cannot be indexed by [Elements K] covariantly, because [d ↦ [Hom d,─]]
   is contravariant.  Stripped: "Elements_proj K has type
   Elements K ⟶ D while it is expected to have type Elements K ⟶ D^op". *)
Fail Check (Curried_Hom D ◯ Elements_proj K).

End ProbeDensityMediator.

Section ProbeDensityUniverse.

Universe uo uh us.
Constraint uh < uo.
Constraint uh < us.

(* CONTROLS: over a category whose OBJECTS sit strictly ABOVE its homs,
   the index category and the Yoneda injection are both formable, so the
   rejection below is attributable to the DIAGRAM and not to the levels
   themselves or to the index. *)
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => ElementsOp K).
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => @yo_inj D K).

(* NEGATIVE 4, FORMABILITY (universe).  [DensityDiagram] carries
   [u <= u0] -- D's objects at or below D's homs -- and the pin enters at
   the DIAGRAM rather than at the index or at [yo_inj].  Stripped, this
   reports a universe inconsistency naming the declared levels:
   "Cannot enforce uh = _ because uh < uo <= _".  Inherited from the
   donors, NOT introduced by Theory/Density.v, and not claimed
   unavoidable. *)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              DensityDiagram K).

End ProbeDensityUniverse.

(* Instrument check: [Fail] does report an error when its command
   SUCCEEDS, so the four negatives above are genuine failures rather than
   an inert command. *)
Fail Fail Check @density.
