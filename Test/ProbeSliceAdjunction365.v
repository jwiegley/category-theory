Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Instance.Cat.Pullback.

Generalizable All Variables.

(* Boundary probe for Construction/Slice/Adjunction.v (issue #365). *)

(* This file exists for what an in-file [Fail] cannot do: an in-file
   negative is renamed in lockstep with the constant it guards, so it
   cannot detect a rename.  The [Require] list above is the target's own,
   verbatim, plus four additions that the target does not need:
   Construction/Comma.v and Construction/Opposite.v (both already in the
   target's transitive closure, named here for the route and orientation
   negatives below), Construction/Slice/Adjunction.v (the target itself)
   and Instance/Cat/Pullback.v (for the prior-art agreement checks; its
   own module closure is 39, and requiring it from the target would add
   14 modules to the target's 31 -- measured with coqdep, and the reason
   the target does not).  A short prefix of a target's imports is what
   makes a probe pass vacuously, so the mirroring is deliberate.

   TWELVE negatives of THREE KINDS, kept lexically apart, plus one
   scope-free instrument check (thirteen [Fail] commands in all).  Each was
   stripped ONE AT A TIME, with the others left intact, compiled alone,
   and its whole error read to confirm where it fires and what kind it
   is.  This repo's [coqc] emits nothing for a [Fail] that succeeds, so
   rc=0 with every [Fail] intact is the verification.

   Six FORMABILITY negatives end "universe inconsistency: Cannot enforce
   up = uh because uh < up".  Five CONVERSION negatives end "cannot
   unify" between two terms of ONE type.  The single TYPING negative
   ALSO ends "cannot unify", so the tail alone does NOT separate it: what
   separates it is that its unification mismatch is between two
   CATEGORIES -- the index arguments of the type former -- and not
   between two inhabitants of one type, with the body reporting one
   whole [Adjunction] type as found and another as expected.  The
   instrument check is itself a plain typing mismatch with no "cannot
   unify" at all. *)

(** ** Instrument check: the harness reports a genuine rejection *)

Fail Check (1 = true).

(** ** Kind 1 — FORMABILITY: hom and proof universes cannot be split *)

(* Every headline constant of the target is stated over
   [C : Category@{u u0 u0}] -- hom IDENTIFIED with proof, by reuse of one
   level variable in the BINDER -- while the constraint blocks carry no
   equation at all, only bounds.  Reading the blocks alone reports "no
   identification" and is wrong.

   The identification is INHERITED, and FIVE donors each force it ALONE.
   Below, a category whose hom universe is declared STRICTLY BELOW its
   proof universe is formable, and so are its hom-sets and identities
   (the controls); every one of [Slice], [Coslice], [Cartesian],
   [IsTerminalObj] and [IsInitialObj] is rejected at those very levels,
   each with "Cannot enforce up = uh because uh < up", and so is the
   target's own [Coslice_Proj], which inherits it from [Coslice].
   Nothing in the target introduces the identification, and none of the
   five is claimed unavoidable. *)

Section UniverseBoundary.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : Cu).

(* Controls: the category, its hom-sets and its identities all elaborate
   with the two levels declared strictly apart. *)
Check Cu.
Check (xu ~> yu).
Check (id[xu]).

(* Negative 1 (formability): the slice construction. *)
Fail Check (@Slice Cu xu).

(* Negative 2 (formability): the coslice construction. *)
Fail Check (@Coslice Cu xu).

(* Negative 3 (formability): the cartesian class -- hence also
   [Cocartesian], which is that class read at the opposite category. *)
Fail Check (@Cartesian Cu).

(* Negative 4 (formability): the object-level terminality predicate. *)
Fail Check (@IsTerminalObj Cu xu).

(* Negative 5 (formability): its initial dual. *)
Fail Check (@IsInitialObj Cu xu).

(* Negative 6 (formability): the target's own projection functor, which
   inherits the identification from [Coslice] and adds nothing. *)
Fail Check (@Coslice_Proj Cu xu).

End UniverseBoundary.

(** ** Kind 2 — CONVERSION *)

Section Conversion.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context {CA : @Cartesian C}.
Context (a : C).

(* Controls for negative 7: the unit of the delivered adjunction IS the
   right injection with one [id_left] residue in front of it, and that
   residue is exhibited literally rather than described. *)
Example ctrl_unit_residue (c : C) :
  @unit (@Coslice C a) C (Coslice_Coprod a) (Coslice_Proj a)
    (Coslice_Projection_Adjunction a) c
    = id ∘ @coslice_projection_unit C CC a c := eq_refl.

Check @coslice_unit_strict.
Check @coslice_unit_is_inr.
Check @coslice_projection_unit.

(* Negative 7 (conversion): the class-produced unit is NOT the bare
   injection on the nose.  [unit] is [⌊id⌋], and the forward transpose
   post-composes with [inr]; the identity of the coslice is carried by
   [id] of C, so what comes out is [id ∘ inr].  The [≈] form is the
   target's [coslice_unit_is_inr], one [id_left] away. *)
Fail Example neg_unit_is_inr (c : C) :
  @unit (@Coslice C a) C (Coslice_Coprod a) (Coslice_Proj a)
    (Coslice_Projection_Adjunction a) c
    = @coslice_projection_unit C CC a c := eq_refl.

(* Controls for negative 8: the slice counit carries the mirror-image
   residue, on the OTHER side. *)
Example ctrl_counit_residue (y : C) :
  @counit C (@Slice C a) (Slice_Proj a) (Slice_Prod a)
    (Slice_Projection_Adjunction a) y
    = @slice_projection_counit C CA a y ∘ id := eq_refl.

Check @slice_counit_strict.
Check @slice_counit_is_exl.
Check @slice_projection_counit.

(* Negative 8 (conversion): the class-produced counit is NOT [exl] on the
   nose.  [counit] is [⌈id⌉], and the backward transpose pre-composes
   with the given slice arrow, which here is the identity of C. *)
Fail Example neg_counit_is_exl (y : C) :
  @counit C (@Slice C a) (Slice_Proj a) (Slice_Prod a)
    (Slice_Projection_Adjunction a) y
    = @slice_projection_counit C CA a y := eq_refl.

End Conversion.

Section Orientation.

Context {C : Category}.
Context (a : C).

(* The issue says the slice statement is "one [Opposite] transport away".
   It is not, on the nose.  The OBJECT types do agree definitionally --
   both are the arrows out of [a] -- which is what makes the negative
   below a statement about the hom EQUATIONS and not about the encoding
   at large. *)
Example ctrl_orientation_objects :
  obj[@Coslice C a] = obj[Opposite (@Slice (Opposite C) a)] := eq_refl.

Check @Coslice.
Check @Slice.
Check @Opposite.

(* Negative 9 (conversion): [Coslice C a] is not [(Slice (C^op) a)^op].
   Unfolding, the opposite of the slice over C^op has homs
   [∃ f, f ∘ `2 x ≈ `2 y] where [Coslice] has [∃ f, `2 y ≈ f ∘ `2 x] --
   the same equation in the other ORIENTATION, hence a different type.
   Construction/Slice/Terminal.v:177-198 already records exactly this,
   as its reason for proving [Coslice_Initial] directly rather than
   transporting [Slice_Terminal]; the target's Block B is built directly
   for the same reason, which is also what keeps [^op] out of every
   delivered slice-side type. *)
Fail Example neg_coslice_is_op_slice :
  @Coslice C a = Opposite (@Slice (Opposite C) a) := eq_refl.

End Orientation.

Section PriorArt.

Context {C : Category}.
Context (a : C).

(* PRIOR ART.  The issue's Awodey section says of the slice domain
   functor that "the functor itself does not exist".  That is FALSE:
   Instance/Cat/Pullback.v:668 [Slice_proj] and :847 [Coslice_proj] are
   exactly this record, and Construction/Slice/Terminal.v:99 and :206
   [Slice_Forget]/[Coslice_Forget] are its specialisations to a terminal
   and an initial object.  The target rebuilds it rather than requiring
   Instance/Cat/Pullback.v, whose module closure is far heavier; the
   agreement is measured HERE, where that file is already loaded.

   Both DATA fields agree on the nose, in both handednesses. *)

Example ctrl_coslice_proj_fobj (x : @Coslice C a) :
  fobj[@Coslice_Proj C a] x = fobj[@Coslice_proj C a] x := eq_refl.

Example ctrl_coslice_proj_fmap (x y : @Coslice C a)
  (f : x ~{@Coslice C a}~> y) :
  fmap[@Coslice_Proj C a] f = fmap[@Coslice_proj C a] f := eq_refl.

Example ctrl_slice_proj_fobj (x : @Slice C a) :
  fobj[@Slice_Proj C a] x = fobj[@Slice_proj C a] x := eq_refl.

Example ctrl_slice_proj_fmap (x y : @Slice C a)
  (f : x ~{@Slice C a}~> y) :
  fmap[@Slice_Proj C a] f = fmap[@Slice_proj C a] f := eq_refl.

(* Negative 10 (conversion): the WHOLE records are not equal.  [Functor]
   has five fields; the two data fields agree by the controls above, so
   the difference is confined to the three LAW fields, which are each
   file's own opaque [Program] obligations. *)
Fail Example neg_coslice_proj_record :
  @Coslice_Proj C a = @Coslice_proj C a := eq_refl.

(* THE ISSUE'S OWN SUGGESTED ROUTE, MEASURED.  Its "Current state" says
   the projection "through [Comma_Coslice] *is* the projection of the
   exercise" -- true as a statement about categories, and the transported
   functor does exist and typecheck ([p365_via_comma] below).  But
   [Comma_Coslice] (Construction/Slice.v:181) is a [Program Instance]
   whose [to] is written [{| fobj := _; fmap := _ |}], so BOTH data fields
   of the comparison functor are [Program] obligations; nothing about the
   transported functor reduces.  Not even its OBJECT action returns the
   first projection on the nose, which is why the target rebuilds the
   three-line record instead of transporting. *)

Definition p365_via_comma : @Coslice C a ⟶ C :=
  comma_proj2 ◯ to (Comma_Coslice C a).

Check @p365_via_comma.
Check @comma_proj2.
Check @Comma_Coslice.

(* Negative 12 (conversion): the transported functor's object action is
   not the first projection on the nose, where the target's
   [Coslice_Proj] has it definitionally (control above:
   [ctrl_coslice_proj_fobj]). *)
Fail Example neg_via_comma_fobj (x : @Coslice C a) :
  fobj[p365_via_comma] x = `1 x := eq_refl.

End PriorArt.

(** ** Kind 3 — TYPING *)

Section Typing.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context (a : C).

(* Control: the adjunction has the handedness the exercise asks for --
   the coproduct functor on the LEFT, the projection on the RIGHT. *)
Check (@Coslice_Projection_Adjunction C CC a
         : Coslice_Coprod a ⊣ Coslice_Proj a).

Check @Coslice_Coprod.
Check @Coslice_Projection_Adjunction.

(* Negative 11 (typing): the other handedness is a different statement,
   and it is not merely unproved -- the ascription is rejected. *)
Fail Check (@Coslice_Projection_Adjunction C CC a
              : Coslice_Proj a ⊣ Coslice_Coprod a).

End Typing.

(** ** Controls naming every remaining delivered constant *)

Check @Cartesian.
(* [Cocartesian] is a NOTATION (Structure/Cocartesian.v:117), not a
   constant, so [Check @Cocartesian.] does not parse -- it reports a
   missing [term] after '@Cocartesian'.  It is named instead by the
   [Context {CC : @Cocartesian C}] lines above, which are succeeding
   commands and serve as its control. *)
Check @IsTerminalObj.
Check @IsInitialObj.
Check @unit.
Check @counit.
Check @Coslice_proj.
Check @Slice_proj.
Check @Coslice_Proj.
Check @Slice_Proj.
Check @Slice_Prod.
Check @Slice_Projection_Adjunction.
Check @coslice_fmap_is_cover.
Check @slice_fmap_is_split.
Check @coslice_transpose.
Check @slice_transpose.
Check @coslice_adj.
Check @slice_adj.
Check @coslice_projection_counit.
Check @slice_projection_unit.
Check @coslice_counit_strict.
Check @coslice_counit_is_merge.
Check @slice_unit_strict.
Check @slice_unit_is_fork.
Check @slice_id_obj.
Check @coslice_id_obj.
Check @slice_id_IsTerminalObj.
Check @coslice_id_IsInitialObj.
Check @slice_left_adjoint_terminal.
Check @slice_terminal_left_adjoint.
Check @slice_terminal_left_adjoint_adj.
Check @slice_proj_left_adjoint_iff_terminal.
Check @coslice_right_adjoint_initial.
Check @coslice_initial_right_adjoint.
Check @coslice_initial_right_adjoint_adj.
Check @coslice_proj_right_adjoint_iff_initial.
Check @Sets_Coslice_Projection_Adjunction.
Check @Sets_Slice_Projection_Adjunction.
Check @sets_bipoint.
Check @sets_bipoint_l.
Check @sets_bipoint_r.
Check @sets_bipoint_distinct.
Check @sets_point.
Check @sets_bipoint_const.
Check @sets_bipoint_not_terminal.
Check @sets_bipoint_not_initial.
Check @sets_slice_proj_no_left_adjoint.
Check @sets_coslice_proj_no_right_adjoint.
Check @sets_slice_proj_left_adjoint_at_terminal.
Check @sets_coslice_proj_right_adjoint_at_initial.
Check @sets_coslice_transpose_computes.
Check @sets_slice_transpose_is_fork.
Check @sets_slice_transpose_computes.
Check @sets_coslice_unit_not_iso.
Check @slice_terminal_adj.
Check @coslice_initial_adj.
Check @coslice_adj_to.
Check @coslice_adj_from.
Check @slice_adj_to.
Check @slice_adj_from.
