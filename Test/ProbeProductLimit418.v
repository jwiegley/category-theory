Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.Limit.

Generalizable All Variables.

(** * Probe: the measured boundaries of Construction/Product/Limit.v *)

(* Companion to Construction/Product/Limit.v (Mac Lane, Categories for the
   Working Mathematician, 2nd ed., §V.2 Exercise 2; Riehl, Category Theory
   in Context, §3.4 Exercise 3.4.v).  Everything that file claims at
   [eq_refl] is shipped there as an [Example], so it guards itself; what
   it cannot guard from inside are the REFUSALS its header records and the
   universe boundary a consumer meets.  Those are pinned here, from OUTSIDE
   the target, because an in-file [Fail] renames in lockstep with the
   constant it guards and so cannot detect a rename.

   SIX negatives of TWO kinds — five CONVERSION, one UNIVERSE (pinned by
   TWO [Fail] commands, the donor and the inherited refusal) — told apart
   by the error TEXT rather than by label, plus one scope-free instrument
   check: seven [Fail] commands beyond the instrument.  The kinds were read
   off the messages actually produced by stripping each [Fail] in turn.
   Note N5 in particular: it LOOKS like a typing negative (a wrong
   ascription) but its message carries a [cannot unify] clause, and a
   TYPING negative in this tree is a has-type mismatch with NO such
   clause, so it is classified as conversion.

     N1  CONVERSION  [FCone Fst (prod_cone N1 N2)] is not [N1] as a whole
                   RECORD, though its apex and every leg are [N1]'s on the
                   nose (the two controls beside it): the coherence field is
                   a rebuilt proof and [≈] is Type-valued.
     N2  CONVERSION  The apex of [prod_cone (FCone Fst N) (FCone Snd N)] is
                   [(fst n, snd n)] and not [n]: a [prod] has no
                   definitional eta.  This is why [prod_reflect] goes
                   through the cone isomorphism [prod_cone_iso], whose apex
                   isomorphism is [(id, id)] (the control).
     N3  CONVERSION  [pi_cone (fun i => FCone (PiCat_Proj D i) N)] is not
                   [N] as a whole record EITHER, although here BOTH the apex
                   and every leg are [N]'s on the nose by function eta (the
                   two controls) — so the difference is located exactly in
                   the coherence field, and [pi_cone_iso]'s apex isomorphism
                   is [iso_id].
     N4  CONVERSION  [Opposite (PiCat D)] is not [PiCat (fun i => Opposite
                   (D i))]: [PiCat]'s law fields are [Program] obligations,
                   so the two records differ in those fields although their
                   objects, homs, identities and composition agree.  The
                   control is [Product_Opposite] restated: for the BINARY
                   product the same equation closes by [eq_refl], which is
                   what makes [Product_Cocomplete] free and leaves
                   [PiCat_Cocomplete] undelivered.
     N5  CONVERSION  [Fst_PreservesLimitCone K] ascribed at
                   [PreservesLimitCone K Snd] is refused with [cannot unify
                   "Cone (Snd ◯ K)" and "Cone (Fst ◯ K)"] — the two
                   preservation types unfold to quantifications over
                   different cone types — against the correct ascription as
                   its control.  No universe clause.
     N6  UNIVERSE  At a shape whose homs are declared strictly BELOW the
                   factors' homs, the diagram [K : Ju ⟶ Cu ∏ Du] and a
                   [Cone] over it are ACCEPTED while the composite
                   [Fst ◯ K] is refused: [Compose] is declared over three
                   categories sharing ONE hom-and-proof level, and that is
                   the identification every constant of the target
                   inherits (its blocks carry [u0 = u2], [u0 = u4],
                   [u0 = u6], the shape's hom level against both factors'
                   and the product's).  [prod_cone K] is refused at the same
                   levels, firing at that composite.

   Each negative was stripped ONE AT A TIME in a copy of this WHOLE file —
   not a preamble-plus-command scratch, which would drop the [Section]'s
   [Context] and local [Universes]/[Constraint] declarations and refuse for
   a reason unrelated to the claim — compiled alone, and its whole error
   read.  Every constant a negative names also appears in a [Check] outside
   every [Fail], so a rename breaks this file loudly instead of turning a
   [Fail] vacuously green. *)

(** ** Instrument check *)

(* A name that is not in scope: if the harness were reporting [Fail]
   successes as failures, or vice versa, this line would say so. *)

Fail Check probe418_no_such_constant.

(** ** Guards: every constant a negative names, named outside every [Fail] *)

Check @prod_cone.
Check @prod_cone_iso.
Check @FCone.
Check @Fst.
Check @Snd.
Check @Compose.
Check @Cone.
Check @cone_leg.
Check @vertex_obj.
Check @pi_cone.
Check @PiCat.
Check @PiCat_Proj.
Check @Opposite.
Check @Product.
Check @Product_Opposite.
Check @PreservesLimitCone.
Check @Fst_PreservesLimitCone.
Check @Snd_PreservesLimitCone.

(** ** N1, N2: the binary pairing against its projections *)

Section BinaryRecords.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* Controls: apex and legs of the projected pairing ARE the first cone's. *)
Example probe418_ctrl_fst_apex (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  vertex_obj[FCone Fst (prod_cone K N1 N2)] = vertex_obj[N1] := eq_refl.

Example probe418_ctrl_fst_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K))
  (x : J) :
  cone_leg (FCone Fst (prod_cone K N1 N2)) x = cone_leg N1 x := eq_refl.

(* N1: CONVERSION — the whole record is not. *)
Fail Example probe418_n1 (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  FCone Fst (prod_cone K N1 N2) = N1 := eq_refl.

(* N2: CONVERSION — no eta for [prod] on the apex. *)
Fail Example probe418_n2 (N : Cone K) :
  vertex_obj[prod_cone K (FCone Fst N) (FCone Snd N)] = vertex_obj[N]
  := eq_refl.

(* Control: the cone isomorphism the target uses instead, with apex
   isomorphism [(id, id)]. *)
Example probe418_ctrl_prod_iso (N : Cone K) :
  to `1 (prod_cone_iso K N) = (id, id) := eq_refl.

End BinaryRecords.

(** ** N3: the family pairing against its projections *)

Section FamilyRecords.

Context {I : Type} {D : I → Category} {J : Category}.
Context (K : J ⟶ PiCat D).

(* Controls: apex AND legs agree on the nose, by function eta. *)
Example probe418_ctrl_pi_apex (N : Cone K) :
  vertex_obj[pi_cone K (fun i => FCone (PiCat_Proj D i) N)] = vertex_obj[N]
  := eq_refl.

Example probe418_ctrl_pi_leg (N : Cone K) (x : J) :
  cone_leg (pi_cone K (fun i => FCone (PiCat_Proj D i) N)) x = cone_leg N x
  := eq_refl.

(* N3: CONVERSION — the whole record is not; only the coherence differs. *)
Fail Example probe418_n3 (N : Cone K) :
  pi_cone K (fun i => FCone (PiCat_Proj D i) N) = N := eq_refl.

End FamilyRecords.

(** ** N4: the opposite of a set-indexed product is not a set-indexed product
       of opposites on the nose *)

(* Control: for the binary product it is — Construction/Product.v's
   [Product_Opposite], restated. *)
Example probe418_ctrl_binary_op (C D : Category) :
  Opposite (C ∏ D) = (Opposite C ∏ Opposite D) := eq_refl.

(* N4: CONVERSION. *)
Fail Example probe418_n4 {I : Type} (D : I → Category) :
  Opposite (PiCat D) = PiCat (fun i => Opposite (D i)) := eq_refl.

(** ** N5: the two projections' preservation witnesses are not interchangeable *)

Section Handedness.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* Controls. *)
Check (Fst_PreservesLimitCone K : PreservesLimitCone K Fst).
Check (Snd_PreservesLimitCone K : PreservesLimitCone K Snd).

(* N5: CONVERSION. *)
Fail Check (Fst_PreservesLimitCone K : PreservesLimitCone K Snd).

End Handedness.

(** ** N6: the universe boundary, with the functor and the cone as controls *)

Section UniverseBoundary.

Universes jo jh co ch do dh.
Constraint jh < ch.
Constraint jh < dh.

Context (Ju : Category@{jo jh jh}).
Context (Cu : Category@{co ch ch}).
Context (Du : Category@{do dh dh}).
Context (K : Ju ⟶ Cu ∏ Du).

(* Controls: the diagram and a cone over it are formable at these levels. *)
Check K.
Check (@Cone Ju (Cu ∏ Du) K).

(* N6: UNIVERSE — the donor: [Compose] wants one hom level for all three
   categories. *)
Fail Check (Fst ◯ K).

(* Inherited: [prod_cone] mentions that composite in its type. *)
Fail Check (prod_cone K).

End UniverseBoundary.
