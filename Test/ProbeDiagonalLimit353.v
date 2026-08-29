Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Natural.Transformation.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Kan.Extension.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Two.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Opposite.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(** * Probe: the boundaries #353's two files measure

   `Adjunction/Diagonal/Limit.v` and `Theory/Equivalence/Colimit.v` between
   them record around twenty rejections and carry no [Fail] of their own. A
   measurement is not a guard: nothing in the build would notice if a donor
   changed and one of them began to succeed. **This file pins ELEVEN of
   them**, beside a control that must SUCCEED — it does NOT pin all, and an
   earlier draft of this comment claimed it did. Not pinned here, and named
   so a reader can see the gap: the dual of NEGATIVE 6 on the colimit side;
   the three law fields of the composite case individually; the coherence
   component of the round trip alone; `cone_along` against `cone_transport`;
   the transported colimit leg's `≈`-not-`=`; `Functor_Setoid` and
   `Opposite_Functor` as independent hom=proof donors; the three
   `limit_induced` donors; and `two_IsAColimit`'s `Set` pin (its twin IS
   pinned, as NEGATIVE 10).

   The import list is the UNION of the two targets' own lists, plus the two
   targets and `Instance/Cat.Opposite` (needed for the `Op` negatives). A
   probe compiled against a shorter prefix can fail for a missing-reference
   reason and read as a mathematical rejection.

   KINDS, separated by the error TEXT rather than by label:
     CONVERSION  ends `(cannot unify "X" and "Y")`
     FORMABILITY ends `(universe inconsistency: Cannot enforce ...)`
   Each negative below was stripped of its [Fail] and its whole error read.

   ONE MEASURED REJECTION IS DELIBERATELY NOT PINNED, and an earlier draft
   of this comment OVERSTATED it. The Leibniz statement
   `two_id_diagram = two_negb_diagram -> False` IS statable — `Check` on it
   returns `Prop`, so a `Fail Check` would itself fail. What `Colimit.v`
   accurately says is that it is NOT STATED, because `rewrite` cannot
   abstract over one of two universe-POLYMORPHIC constants at different
   instances (it reports the abstraction as ill-typed). What stands in its
   place is the `≈`-level `two_diagrams_differ`, which is STRICTLY STRONGER
   (two Leibniz-equal functors would have `≈`-equal arrow actions). It is
   named in a control below so a rename still breaks this file. *)

(** ** Instrument check

   Must ERROR ("The command has not failed!"), confirming a [Fail] wrapping
   a SUCCEEDING command is itself rejected. Scope: it does NOT detect a
   [Fail] that accepted everything — such a [Fail] would compile here too.
   It rules out the commoner accident, a [Fail] treated as a no-op. *)
Fail Fail Check Category.

(** ** CONVERSION — the opposite-functor calculus (Colimit.v 1, 2) *)

Section OppositeConversion.
Context {C D E : Category}.

(* NEGATIVE 1. Whole record. Stripped: `cannot unify`. *)
Fail Definition probe_op_compose (F : D ⟶ E) (G : C ⟶ D) :
  Opposite_Functor (F ◯ G)
    = Opposite_Functor F ◯ Opposite_Functor G := eq_refl.

(* CONTROLS 1: BOTH data actions agree on the nose, which is what localizes
   the failure to the three law fields. *)
Definition probe_op_compose_fobj (F : D ⟶ E) (G : C ⟶ D) (x : C) :
  fobj[Opposite_Functor (F ◯ G)] x
    = fobj[Opposite_Functor F ◯ Opposite_Functor G] x := eq_refl.

Definition probe_op_compose_fmap (F : D ⟶ E) (G : C ⟶ D)
  (x y : C) (f : y ~{C}~> x) :
  fmap[Opposite_Functor (F ◯ G)] f
    = fmap[Opposite_Functor F ◯ Opposite_Functor G] f := eq_refl.

(* NEGATIVE 2. The identity. Stripped: `cannot unify`. *)
Fail Definition probe_op_id :
  Opposite_Functor (Id[D]) = Id[Opposite D] := eq_refl.

(* CONTROL 2: its object action agrees. *)
Definition probe_op_id_fobj (x : D) :
  fobj[Opposite_Functor (Id[D])] x = fobj[Id[Opposite D]] x := eq_refl.

End OppositeConversion.

(** ** CONVERSION — `Op`'s obligation is Qed, so nothing reduces through it

   This is the PRIOR-ART correction the `Colimit.v` header records: the
   content of `Opposite_Functor_respects` already exists as
   `Op_obligation_1`, the `fmap_respects` obligation of `Op : Cat ⟶ Cat`
   (`Instance/Cat/Opposite.v:82`). What survives as a reason to have the
   transparent restatement is OPACITY and universes, both pinned here. *)

Section OpOpacity.
Context {J C : Category}.

Definition via_Op (G G' : J ⟶ C) (e : G ≈ G') :
  Opposite_Functor G ≈ Opposite_Functor G' :=
  @fmap_respects Cat Cat Op J C G G' e.

(* NEGATIVE 3. The component readback through `Op` is REJECTED (Qed). *)
Fail Definition probe_via_Op_component (G G' : J ⟶ C) (e : G ≈ G') (x : J) :
  `1 (via_Op G G' e) x = Isomorphism_Opposite (`1 e x) := eq_refl.

(* CONTROL 3: the SAME readback through the transparent restatement holds.
   Same statement, same arguments — only the route differs, which is what
   makes the opacity attribution discriminate. *)
Definition probe_respects_component (G G' : J ⟶ C) (e : G ≈ G') (x : J) :
  `1 (Opposite_Functor_respects e) x = Isomorphism_Opposite (`1 e x)
  := eq_refl.

End OpOpacity.

(** ** CONVERSION — the (A) round trip (Colimit.v 9, 10, 11)

   TWO INDEPENDENT OBSTRUCTIONS, and the controls are what separate them.
   The coherence component fails on its own (10); and `sigT` has no eta, so
   the pair would fail to close even had (10) not (11). Without control 10b
   "sigT eta" would have been a plausible SINGLE cause, and wrong. *)

Section RoundTrip.
Context {J C : Category}.

(* NEGATIVE 4. Whole record. *)
Fail Definition probe_roundtrip (G G' : J ⟶ C) (e : G ≈ G') :
  Opposite_Functor_reflects (Opposite_Functor_respects e) = e := eq_refl.

(* CONTROL 4 (= control 10b): the ISOMORPHISM-FAMILY component IS eq_refl,
   in BOTH composition orders. So the data half is provably unaffected and
   the failure is confined to the coherence half. *)
Definition probe_roundtrip_data (G G' : J ⟶ C) (e : G ≈ G') (x : J) :
  `1 (Opposite_Functor_reflects (Opposite_Functor_respects e)) x = `1 e x
  := eq_refl.

(* NEGATIVE 5. `sigT` eta, at an ARBITRARY e — the second, independent
   obstruction. *)
Fail Definition probe_sigT_eta (G G' : J ⟶ C) (e : G ≈ G') :
  existT _ (`1 e) (`2 e) = e := eq_refl.

End RoundTrip.

(** ** CONVERSION — the adjunction unit/counit (Limit.v R1, R2) *)

Section CounitConversion.
Context {J C : Category} (L : HasLimitsOfShape J C) (F : [J, C]).

(* NEGATIVE 6. The counit component is not the limit leg ON THE NOSE. *)
Fail Definition probe_counit_strict (j : J) :
  transform[lim_counit L F] j = lim_leg L F j := eq_refl.

(* CONTROL 6: with the residual identity it DOES close — which locates the
   difference at a `∘ id` and not at the leg. *)
Definition probe_counit_with_id (j : J) :
  transform[lim_counit L F] j = lim_leg L F j ∘ id := eq_refl.

End CounitConversion.

(** ** CONVERSION — the Kan comparison (Limit.v R3) *)

Section KanConversion.
Context {J C : Category} (c : C).

(* NEGATIVE 7. Whole records: rejected in the three Functor LAW fields. *)
Fail Definition probe_diag_induced :
  Δ[J](c)
    = fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c) := eq_refl.

(* CONTROLS 7: BOTH actions agree on the nose (these are the target's own
   `diagonal_is_induced_obj` / `_map`), confining the failure to the laws. *)
Definition probe_diag_induced_obj (x : J) :
  fobj[Δ[J](c)] x
    = fobj[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] x := eq_refl.

Definition probe_diag_induced_map (x y : J) (f : x ~{J}~> y) :
  fmap[Δ[J](c)] f
    = fmap[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] f := eq_refl.

End KanConversion.

(** ** CONVERSION — the empty category is not its own opposite (Limit.v R4)

   This is WHY there is no colimit dual of `Terminal_Limit`, hence no
   `HasColimitsOfShape 0 C ↔ Initial C`. The target discloses that; this
   pins the blocker. *)
Fail Definition probe_zero_op : Opposite _0 = _0 := eq_refl.

(* CONTROL: `_0` is nameable and `Opposite` applies to it. *)
Check _0.
Check (Opposite _0).

(** ** FORMABILITY — universes

   No explicit universe instance is written inside any [Fail] below: such a
   [Fail] can pass for an arity reason on another Coq version, making the
   guard vacuous with nothing noticing. *)

Section FormabilityHomProof.
Universes co ch cp.
Constraint ch < cp.
Context (Cu : Category@{co ch cp}).

(* CONTROLS: hom and object are nameable with hom and proof declared
   strictly apart, so the negatives below fire on the CONSTRAINT. *)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (obj[Cu]).

(* NEGATIVE 8. `Opposite` alone identifies hom with proof. *)
Fail Check (Opposite Cu).

End FormabilityHomProof.

(** ** FORMABILITY — the OTHER reason the transparent restatement earns its
    place, which was measured in the target and guarded NOWHERE until this
    section. The `Op` route identifies the two categories' OBJECT universes;
    the restatement keeps them apart. Controls first, so the negative is
    shown to fire on the identification and not on the section's levels. *)

Section FormabilityOpUniverses.
Universes jo jh jp co ch cp.
Constraint jo < co.
Context (Ju : Category@{jo jh jp}) (Cu : Category@{co ch cp}).

Check Ju.
Check Cu.
Check (Ju ⟶ Cu).
(* CONTROL: the transparent restatement IS formable with the two object
   levels declared strictly apart. *)
Check (@Opposite_Functor_respects Ju Cu).

(* NEGATIVE. Stripped:
     universe inconsistency: Cannot enforce co = jo because jo < co *)
Fail Check (@fmap_respects Cat Cat Op Ju Cu).

End FormabilityOpUniverses.

Section FormabilitySetPin.
Universes so sh.
Constraint Set < sh.
Context (Cs : Category@{so sh sh}).

(* CONTROL: the category is nameable with its homs strictly above `Set`. *)
Check Cs.
Check (obj[Cs]).

(* NEGATIVE 9. THE `Set` PIN, and it is the sharp one. `two_IsALimit`'s
   binder reads `∀ {C : Category@{_ Set Set}}` — the AMBIENT category's hom
   AND proof pinned to the literal `Set` — while its constraint block
   carries NO `Set =` at all. A sweep of constraint blocks for `Set =`
   returns a clean bill and is WRONG; the binder must be swept for the
   literal token. Donors: `Instance/Two.v`'s `TwoHom : ... -> Set` fixes the
   SHAPE's hom, and `IsALimit` identifies the shape's hom-and-proof with the
   ambient's. Not repaired, not claimed unavoidable. *)
Fail Check (@two_IsALimit Cs).

End FormabilitySetPin.

(** ** Controls naming every constant the negatives depend on, OUTSIDE a
    [Fail], so a rename breaks a succeeding command rather than turning a
    negative vacuously green. *)

Check @Opposite_Functor.
Check @Opposite_Functor_respects.
Check @Opposite_Functor_reflects.
Check @Opposite_Functor_Proper.
Check @Op.
Check @Isomorphism_Opposite.
Check @two_IsALimit.
Check @two_IsAColimit.
Check @two_endo.
Check @two_diagrams_differ.
Check @two_transport_moves_inj.
Check @cocone_transport.
Check @isacolimit_transport.
Check @colimit_transport.
Check @cone_along.
Check @limit_induced.
Check @colimit_induced.
Check @fun_equiv_transform.
Check @cone_along_is_cone_transport.
Check @limit_transport.

Check @HasLimitsOfShape.
Check @HasColimitsOfShape.
Check @LimitFunctor.
Check @ColimitFunctor.
Check @Diagonal_Limit_Adjunction.
Check @Colimit_Diagonal_Adjunction.
Check @limits_iff_diagonal_right_adjoint.
Check @colimits_iff_diagonal_left_adjoint.
Check @lim_counit.
Check @colim_unit.
Check @lim_counit_is_limit_leg.
Check @colim_unit_is_colimit_inj.
Check @Lim_map.
Check @Colim_map.
Check @lim_leg.
Check @colim_inj.
Check @Erase_right_adjoint_iff_Terminal.
Check @Erase_left_adjoint_iff_Initial.
Check @HasLimitsOfShape_0_iff_Terminal.
Check @lim_Ran_iso.
Check @Cocone_Natural_Transform.
Check @Cone_Natural_Transform.
Check @Sets_Diagonal_Limit_Adjunction.
Check @sets_bool_lim_two_elements.
Check @Induced.
Check @Erase.
Check @Diagonal.
