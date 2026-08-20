Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Elements.Kan.

Generalizable All Variables.

(** * Probes guarding Construction/Elements/Kan.v *)

(* This file pins every strict attempt that Construction/Elements/Kan.v MADE
   AND LOST, and every universe boundary its header claims, so that a later
   change which quietly makes one of them succeed — or which renames the
   constants out from under the claim — breaks the build loudly instead of
   leaving the header's prose stale.  It follows the convention of
   Test/ProbePostcompose.v and Test/ProbeQuiverConstructions.v.

   The import list is the target file's, in the target file's order, with the
   target itself appended.  That matters: a probe compiled against a short
   PREFIX of the real imports can fail for a missing-coercion or
   missing-notation reason and thereby pass VACUOUSLY.  (Instance/Field/Frac.v
   records an episode of exactly that.)  The target is Required last, so its
   names win any contest.

   TWO KINDS, KEPT LEXICALLY APART.

     CONVERSION negatives are written [Fail Definition ... := eq_refl] and say
     that two well-typed terms are not definitionally equal.

     FORMABILITY negatives are written [Fail Check] and say that a term
     cannot be elaborated at all, here always because of a universe
     constraint.

   Each negative was stripped of its [Fail] and the resulting error read; the
   diagnosis is recorded beside it.  In batch [coqc] a SUCCEEDING [Fail]
   prints nothing, so the exit code is the only signal, which is why the
   stripped run is part of the procedure and not optional.  Positive controls
   accompany each group, and the sharpest ones differ from their negative in
   exactly the disputed spot.

   Inventory: 7 conversion negatives, 3 formability negatives, 12 positive
   controls. *)

(** ** Group 1 (CONVERSION): the nat/cone round trips *)

Section RoundTripConversion.

Context {D : Category}.
Context (K : D ⟶ Sets).
Context {a : D}.
Context (tau : K ⟹ [Hom a,─]).
Context (psi : ACone a (Elements_proj K)).
Context (d : D) (x : K d).
Context (j : Elements K).

(* POSITIVE CONTROL 1.  The instrument is not rejecting everything: an
   [eq_refl] between a term and itself, in exactly the shape the negatives
   below use, is accepted. *)
Definition control_instrument :
  kan_nat_of_cone K (kan_cone_of_nat K tau)
    = kan_nat_of_cone K (kan_cone_of_nat K tau) := eq_refl.

(* POSITIVE CONTROL 2.  The DATA of round trip 1 does return on the nose:
   the component of the recovered transformation, applied to an element, is
   the original component applied to that element. *)
Definition control_rt1_applied :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau)) d x
  = @transform D Sets K ([Hom a,─]) tau d x := eq_refl.

(* NEGATIVE 1 (CONVERSION).  Round trip 1 at the WHOLE [Transform] record.
   Refuted.  [Transform] carries primitive projections with eta conversion,
   so record equality reduces to field equality, and the [naturality] and
   [naturality_sym] fields of the rebuilt transformation are the terms
   [kan_nat_naturality]/[kan_nat_naturality_sym] rather than tau's own; `≈`
   is [crelation]-valued, so there is no definitional proof irrelevance to
   close the gap.  Stripped error: "cannot unify
   kan_nat_of_cone K (kan_cone_of_nat K tau) and tau". *)
Fail Definition neg_rt1_record :
  kan_nat_of_cone K (kan_cone_of_nat K tau) = tau := eq_refl.

(* NEGATIVE 2 (CONVERSION).  Not even the component FAMILY returns, because
   each component is a [SetoidMorphism] record whose [proper_morphism] field
   is rebuilt from [kan_leg_respects].  Together with control 2 this locates
   the obstruction exactly: the underlying functions agree, the packaged
   proofs do not. *)
Fail Definition neg_rt1_family :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau))
  = @transform D Sets K ([Hom a,─]) tau := eq_refl.

(* NEGATIVE 3 (CONVERSION).  The same at a single component, so that the
   failure is not attributed to the family's outer lambda. *)
Fail Definition neg_rt1_component :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau)) d
  = @transform D Sets K ([Hom a,─]) tau d := eq_refl.

(* POSITIVE CONTROL 3.  Round trip 2's LEG returns on the nose once the
   sigma object is a literal pair. *)
Definition control_rt2_pair :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_nat K (kan_nat_of_cone K psi)) ((d; x) : Elements K)
  = @vertex_map (Elements K) D a (Elements_proj K) psi
     ((d; x) : Elements K) := eq_refl.

(* NEGATIVE 4 (CONVERSION).  The same leg at a VARIABLE object.  Refuted for
   a cause INDEPENDENT of negative 1's: the rebuilt leg family is
   [fun j => leg psi (`1 j; `2 j)], and stdlib [sigT] has no eta rule here —
   Lib/Foundation.v's [Set Primitive Projections] governs this library's own
   records, not [sigT].  This is why Kan.v's [kan_cone_nat_cone] destructs
   the pair before closing by [reflexivity], and control 3 is the same
   statement with the pair destructed. *)
Fail Definition neg_rt2_leg :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_nat K (kan_nat_of_cone K psi)) j
  = @vertex_map (Elements K) D a (Elements_proj K) psi j := eq_refl.

(* NEGATIVE 5 (CONVERSION).  Round trip 2 at the WHOLE [ACone] record.  Both
   causes above apply, and additionally the [cone_coherence] field is
   rebuilt from [kan_cone_coherence]. *)
Fail Definition neg_rt2_record :
  kan_cone_of_nat K (kan_nat_of_cone K psi) = psi := eq_refl.

End RoundTripConversion.

(** ** Group 2 (CONVERSION): the Δ bridge *)

Section DeltaConversion.

Context {D : Category}.
Context (K : D ⟶ Sets).
Context {a : D}.
Context (psi : ACone a (Elements_proj K)).
Context (theta : Δ[Elements K](a) ⟹ Elements_proj K).
Context (j : Elements K).

(* POSITIVE CONTROLS 4 and 5.  BOTH leg families of the Δ bridge return on
   the nose at a VARIABLE object — no sigma is taken apart on this route, so
   negative 4's obstruction is absent here.  These two controls are what
   makes negatives 6 and 7 informative: the only thing left to fail is the
   law fields. *)
Definition control_delta_cone_leg :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_transform K (kan_transform_of_cone K psi)) j
  = @vertex_map (Elements K) D a (Elements_proj K) psi j := eq_refl.

Definition control_delta_transform_component :
  @transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K)
     (kan_transform_of_cone K (kan_cone_of_transform K theta)) j
  = @transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K) theta j
  := eq_refl.

(* NEGATIVE 6 (CONVERSION).  Cone → Δ-transformation → cone at the WHOLE
   record.  Refuted: the [cone_coherence] field is rebuilt through
   [kan_cone_of_transform_coherence], which spends an [id_right] because
   [fmap[Δa] f] is [id] and the cone law has no such factor. *)
Fail Definition neg_delta_cone_record :
  kan_cone_of_transform K (kan_transform_of_cone K psi) = psi := eq_refl.

(* NEGATIVE 7 (CONVERSION).  The other direction, at the whole [Transform]
   record; same cause on [naturality]/[naturality_sym]. *)
Fail Definition neg_delta_transform_record :
  kan_transform_of_cone K (kan_cone_of_transform K theta) = theta := eq_refl.

End DeltaConversion.

(** ** Group 3 (FORMABILITY): objects strictly above homs *)

(* Kan.v's header states that both sides of the isomorphism force D's OBJECT
   universe to sit at or below D's HOM universe, and that the restriction
   enters at the PACKAGING rather than at the passages.  Both halves of that
   claim are pinned here. *)

Section ObjectsAboveHoms.

Universes uo uh us.
Constraint uh < uo.
Constraint uh < us.

(* NEGATIVE 8 (FORMABILITY).  The cone presheaf is not formable when D's
   objects sit strictly above its homs.  Stripped error: "universe
   inconsistency: Cannot enforce uh = _ because uh < uo <= _". *)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              KanCone K).

(* NEGATIVE 9 (FORMABILITY).  The transformation presheaf independently
   refuses at the same setting — a set of natural transformations is a family
   indexed by D's objects and must be an object of [Sets] at the hom level. *)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              KanNat K).

(* NEGATIVE 10 (FORMABILITY).  Hence the natural isomorphism itself. *)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              kan_coyoneda K).

(* POSITIVE CONTROLS 6 and 7.  AT THE VERY SAME UNIVERSE SETTING the two raw
   passages ARE formable.  These are the sharp controls: they differ from
   negatives 8-10 in exactly which constant is named, so the refusal is
   attributable to the packaging (the presheaf and the setoid of
   transformations) and not to [Elements], to [Sets], or to the section's
   constraints being unsatisfiable. *)
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) (a : D)
           (tau : K ⟹ [Hom a,─]) => kan_cone_of_nat K tau).

Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) (a : D)
           (psi : ACone a (Elements_proj K)) => kan_nat_of_cone K psi).

End ObjectsAboveHoms.

Section ObjectsBelowHoms.

Universes vo vh vs.
Constraint vo <= vh.
Constraint vh < vs.

(* POSITIVE CONTROLS 8, 9 and 10.  With the inequality the other way round
   all three constants elaborate, so negatives 8-10 are about the direction
   of that inequality and not about the [Category@{_ _ _}] annotation
   itself. *)
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) => KanCone K).
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) => KanNat K).
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) =>
         kan_coyoneda K).

End ObjectsBelowHoms.

(** ** Group 4: the delivered strengths, guarded *)

Section Delivered.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* POSITIVE CONTROLS 11 and 12.  The two claims Kan.v makes at [eq_refl]
   about the natural isomorphism being an UPGRADE of the pointwise one are
   restated here, so that a change to either definition which broke the
   identification would be caught in this file as well as in the target. *)
Definition control_to_component (a : D) :
  transform[to (kan_coyoneda K)] a = to (kan_iso_at K a) := eq_refl.

Definition control_from_component (a : D) :
  transform[from (kan_coyoneda K)] a = from (kan_iso_at K a) := eq_refl.

End Delivered.
