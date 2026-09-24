Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(** * Well-poweredness feeds SAFT's subobject index *)

(* nLab:      https://ncatlab.org/nlab/show/well-powered+category
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   book p. 130, states the special adjoint functor theorem for a complete,
   well-powered category with a small cogenerating set.  Adjunction/SAFT.v
   takes the well-poweredness half as its [SubobjectIndex] record, a small
   family of monos into each object with no exhaustiveness clause; that
   file's [empty_SubobjectIndex] and [SubobjectIndex_not_exhaustive] show
   the record is strictly weaker than Structure/WellPowered.v's
   [WellPowered].  This satellite is the bridge the other way, #451:

     - [SubobjectIndex_of_WellPoweredAt] forgets a [WellPoweredAt] witness
       to a [SubobjectIndex], as a record literal: the index is [wp_index],
       and each index names the domain and mono of the subobject [wp_to]
       sends it to;
     - [WellPowered_SubobjectIndex] does so at every object;
     - [SAFT_of_WellPowered] is [SAFT] with its [WP] slot filled by it.

   The covering datum [SubobjectCover] is still asked for, and
   Adjunction/SAFT/Sets.v refutes it at the identity of [Sets] whatever
   the index is, so no well-poweredness result discharges it; SAFT.v's
   header records why.  (Since #453, well-poweredness yields the adjoint
   without the datum: Adjunction/SAFT/Characterization.v's
   [SAFT_wellpowered] takes [WellPowered] itself,
   with completeness, continuity and a cogenerating family and no
   covering datum, and returns the left adjoint; [SAFT_of_WellPowered]
   stays as the bridge for [SAFT]'s own statement, whose datum is still
   refuted at [Id[Sets]].)

   WHY A SATELLITE.  Requiring Structure/WellPowered.v from Adjunction/
   SAFT.v would put that development, with its limits, cones and wide
   pullbacks, into the closure of everything downstream of SAFT.v; here
   it is paid only by this file.  Counted over .Makefile.coq.d, excluding
   the file itself: Adjunction/SAFT.v's closure is 44 (43 before #451,
   the one added being Theory/Subobject.v, which [SubObj] needs), and
   would be 109 with the edge; Structure/Generator/Dual.v's 47 would be
   112, Adjunction/Representability/Sets.v's 100 would be 136, and
   Adjunction/GAFT/Necessity.v's 103 would be 139.  This file's own
   closure is 110.

   UNIVERSES, measured with [Set Printing Universes. About ...], stdlib
   bounds omitted:

     SubobjectIndex_of_WellPoweredAt@{u u0 u1 u2 u3} :
       WellPoweredAt@{u1 u u2 u0 u3} x → SubobjectIndex@{u1 u u0} x
       (* u0 < u3, u <= u2, u0 <= u2 *)
     WellPowered_SubobjectIndex@{o h w s t} :
       WellPowered@{o h w s t} C → ∀ x, SubobjectIndex@{w o h} x
       (* h < t, o <= s, h <= s, w <= h *)

     SAFT_of_WellPowered@{cobj dobj h w s t u u0 u1 u2} :
       ∀ ... (comp : Complete@{h h h cobj}),
       PreservesImageLimit@{cobj h dobj h u1 h u h} →
       ∀ (G : Cogenerator@{h cobj h} C) (W : WellPowered@{cobj h w s t} C),
       SubobjectCover@{u2 w h u h dobj cobj h} U comp G
         (WellPowered_SubobjectIndex@{cobj h w s t} W) → ...
       (* h < t, h < u, h < u1, cobj <= s, h <= s, w <= h, cobj <= u1,
          cobj <= u2, dobj <= u1, dobj <= u2, h <= u2 *)

   The index universe passes through unchanged, so [SAFT]'s bound on its
   [SubobjectIndex]'s index ([u3 <= h] in SAFT.v's readback) is the pin
   [w <= h] that [WellPowered] already carries, and the block of
   [SAFT_of_WellPowered] is [SAFT]'s with [u3 := w] together with
   [WellPowered]'s own.  Its binder names [WellPowered]'s [s] and [t]
   and [SAFT]'s [PreservesImageLimit]/[SubobjectCover] slot [u], and that
   is load-bearing: with only [cobj dobj h] named, minimization
   identified [t] with [u], and in a scratch section declaring [t < u]
   the wrapper was refused ("Cannot enforce t = u because t < u") where
   [SAFT] applied to [WellPowered_SubobjectIndex] was accepted; with the
   present binder both are accepted there.

   MEASUREMENTS.  Three constants ([.glob] heads), no [Program]
   obligation, all three transparent [Definition]s; each reports "Closed
   under the global context" by its fully qualified name. *)

Definition SubobjectIndex_of_WellPoweredAt {C : Category} {x : C}
  (W : WellPoweredAt x) : SubobjectIndex x :=
  {| sub_index := wp_index W ;
     SAFT.sub_dom   := fun i => Subobject.sub_dom (wp_to W i) ;
     SAFT.sub_mono  := fun i => Subobject.sub_mono (wp_to W i) ;
     sub_monic := fun i => Subobject.sub_is_monic (wp_to W i) |}.

Definition WellPowered_SubobjectIndex@{o h w s t}
  {C : Category@{o h h}} (W : WellPowered@{o h w s t} C) :
  ∀ x : C, SubobjectIndex x :=
  fun x => SubobjectIndex_of_WellPoweredAt (W x).

(* SAFT over a well-powered [C]: [WellPowered_SubobjectIndex] fills the
   [WP] slot, and the covering datum is still asked for. *)
Definition SAFT_of_WellPowered@{cobj dobj h w s t u +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h cobj} C)
  (cont : @PreservesImageLimit@{cobj h dobj h _ h u h} C D U)
  (G : Cogenerator C) (W : WellPowered@{cobj h w s t} C)
  (cover : SubobjectCover@{_ w h u h dobj cobj h} U comp G
             (WellPowered_SubobjectIndex W)) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT U comp cont G (WellPowered_SubobjectIndex W) cover.
