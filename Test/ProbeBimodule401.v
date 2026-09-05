Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Parameter.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.

Generalizable All Variables.

(** * Probe for Instance/Mod/Bimodule.v *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.8
   Exercise 3, book p. 104; catalog id maclane:IV.8:ex3.  The page is
   quoted verbatim in the header of Instance/Mod/Bimodule.v and is not
   repeated here.

   This file guards the strict claims of that header.  Every command
   below that is said to be refuted was STRIPPED into its own scratch
   copy carrying this file's whole prefix, compiled ALONE, and its
   complete error read; under this repo's coqc a passing [Fail] prints
   nothing, so a whole-file rc=0 alone would establish only THAT each
   command does not typecheck and never WHY.  Each negative is
   classified by the error TEXT, not by expectation:

     CONVERSION  - the message carries a "cannot unify A and B" clause
                   and no universe clause.
     TYPING      - a plain "The term T has type X while it is expected
                   to have type Y"; NO "cannot unify", no universe
                   clause.
     FORMABILITY - "(universe inconsistency: Cannot enforce ...)",
                   naming the levels the enclosing section declares.

   ** TALLY

   18 [Fail] commands = 1 instrument check + 17 negatives, in three
   kinds: SIX conversion (N1, N2, N10, N11, N16, N17), NINE typing
   (N3-N9, N12, N13) and TWO formability (N14, N15).

   ** TWO NEGATIVES MEASURE THEIR ARGUMENT AND NOT THEIR SUBJECT

   N15 names [hom_ab], and its first argument is an [AbEnriched Cu],
   which N14 has just shown is itself unformable at the declared
   levels; stripped, its error is N14's but for the line-derived level
   names, and fires on [Cu].  So [hom_ab] CANNOT be tested apart from
   [AbEnriched], and whether it identifies anything of its own is
   UNKNOWN, not refuted.  N9 is in the same position with respect to
   [Build_Bimodule]: stripped, its error fires on [M], the argument,
   and is character for character N8's, so what it establishes is
   that
   a right R-module cannot be the [bm_left] of a (ℤ,R)-bimodule — which
   is the claim — and NOT anything about [Build_Bimodule] itself.  This
   is the trap recorded for [MonoidObject] under issue #340, and it is
   stated here rather than glossed.

   ** GUARD COVERAGE, MEASURED MECHANICALLY

   Comments stripped and the file split into commands at a period
   followed by whitespace: 191 commands, of which 18 begin with [Fail];
   they mention 50 distinct identifiers, of which 40 also occur in a
   command that is NOT a [Fail].  The ten that do not are,
   exhaustively: the keyword [Fail]; [AC], bound inside N15 itself; the
   seven names of the refuted declarations ([p401_n1], [p401_n2],
   [p401_n7], [p401_n10], [p401_n11], [p401_n16], [p401_n17]), which
   never enter the environment because the commands that would have
   declared them do not typecheck; and [p401_no_such_constant_anywhere],
   the instrument's deliberately absent name.  No CONSTANT that a negative
   names is unguarded.

   ** RENAME SIMULATION

   Five constants of Instance/Mod/Bimodule.v are named inside a
   negative: [TensorWith], [HomS], [BimodTensorBimod], [RTensor] and
   [btb_left].  Each was renamed in a SCRATCH COPY of that file alone
   (the copy still compiling, zero errors) and a copy of this file
   requiring the scratch module instead was compiled.  ALL FIVE broke
   it, every one at a [Check] line of the guard block and NONE inside a
   [Fail]: [TensorWith] at line 216, [HomS] at 218,
   [BimodTensorBimod] at 236, [RTensor] at 215, [btb_left] at 237.  So
   5/5, with zero vacuous guards.

   ** THE HAZARD OF STAGE 1's FINDING 8, AND WHY IT IS BOTH

   [@TensorMod (Ring_op R) N (bimodule_right_RMod F)] TYPECHECKS for
   [F : Bimodule S R] — that is the control [p401_hazard_accepted] — and
   is the tensor of two RIGHT R-modules, balancing (n ⊲ r) ⊗ e against
   n ⊗ (e ⊲ r).  It is therefore NOT the object Exercise 3 asks for, and
   the honest refutation is of its RING: N7 shows it cannot be read as an
   object of [ModR S], where the exercise's N ⊗_R E lives.  No refutation
   of its BALANCE RULE is offered: at the only concrete ring in the tree
   the two rules coincide, ℤ being commutative, so a balance-level
   negative would not fire for the reason its comment claimed.

   ** THE VERBATIM ERROR TAILS

   (Transcribed with [o] for the composition circle, [-|] for the
   adjunction sign, [(x)] for the product of categories and [-->] for
   the functor arrow, so that this comment carries none of the glyphs
   the sources use.)

   N1  CONVERSION  (cannot unify "Ring_op (Ring_op R)" and "R").
   N2  CONVERSION  (cannot unify "ModR (Ring_op R)" and "RMod R").
   N3  TYPING      The term "bm_left E" has type "RModObject R" while it
                   is expected to have type "RModObject (Ring_op R)".
   N4  TYPING      The term "N" has type "RModObject (Ring_op R)" while
                   it is expected to have type "RModObject R".
   N5  TYPING      as N3.
   N6  TYPING      as N3.
   N7  TYPING      The term "TensorMod N (bimodule_right_RMod F)" has
                   type "RModObject (Ring_op R)" while it is expected to
                   have type "RModObject (Ring_op S)".
   N8  TYPING      The term "M" has type "RModObject (Ring_op R)" while
                   it is expected to have type "RModObject Int_Ring".
   N9  TYPING      as N8, fired at N9's ARGUMENT.
   N10 CONVERSION  (cannot unify "TensorWith E1 o TensorWith E" and
                   "TensorWith (BimodTensorBimod E E1)").
   N11 CONVERSION  (cannot unify "HomS E o HomS E1" and
                   "HomS (BimodTensorBimod E E1)").
   N12 TYPING      The term "RTensor E1 (RTensor E N)" has type
                   "RModObject (Ring_op T)" while it is expected to have
                   type "RModObject (Ring_op S)". [see the note below]
   N13 TYPING      The term "btb_left E E1" has type
                   "RModObject R" while it is expected to have type
                   "RModObject (Ring_op T)".
   N14 FORMABILITY (universe inconsistency: Cannot enforce up = uh ...).
   N15 FORMABILITY as N14, fired at N15's ARGUMENT.
   N16 CONVERSION  (cannot unify "bac_unit E E1 N" and
                   "fmap[HomS E] unit o unit").
   N17 CONVERSION  (cannot unify "bac_counit E E1 M" and
                   "counit o fmap[TensorWith E1] counit").

   N12's note: the two objects of part (c)'s comparison do NOT share a
   type at the SECOND ring, so the comparison cannot be an equality even
   before conversion is consulted; at the THIRD ring they do, and that
   reading is the [Check] beside N10, an accepted control, whose
   [eq_refl] is then refuted by N10's functor-level twin.

   ** WHAT THIS FILE DOES NOT DO

   It proves nothing new.  It contains no proof hole of any kind, no
   [Axiom], no [Parameter] and no aborted sketch; every positive control
   is a term or a [Check], never a tactic script, so nothing here can
   drift by a change in the automation. *)

(* --------------------------------------------------------------- *)
(* INSTRUMENT.  A passing [Fail] prints nothing under this repo's    *)
(* coqc, so this command establishes that [Fail] does anything.      *)
(* --------------------------------------------------------------- *)

Fail Check p401_no_such_constant_anywhere.

(* --------------------------------------------------------------- *)
(* GUARD BLOCK.  Every constant that any negative below names is     *)
(* named here OUTSIDE every [Fail], so that renaming one of them     *)
(* breaks this file at a [Check] line rather than turning a negative *)
(* vacuously green.                                                  *)
(* --------------------------------------------------------------- *)

Check @Category.
Check @Functor.
Check @Adjunction.
Check @Isomorphism.
Check @eq.
Check @obj.
Check @hom.
Check @id.
Check @compose.
Check @Compose.

Check @RingObject.
Check @Ring_op.
Check @RModObject.
Check @RModHom.
Check @RMod.
Check @ModR.
Check @Bimodule.
Check @Build_Bimodule.
Check @bm_left.
Check @bimodule_right_RMod.
Check @rm_ab.
Check @rm_smul.
Check @Int_Ring.
Check @Int_Bimodule.
Check @Ring_RMod.
Check @TensorMod.
Check @RBilinear.
Check @AbEnriched.
Check @hom_ab.
Check @Ab_AbEnriched.

Check @BalTensor.
Check @BalBiadditive.
Check @bs_gen.
Check @be_balance.
Check @bal_med.
Check @bal_hom_ext.
Check @RTensor.
Check @TensorWith.
Check @HomSObj.
Check @HomS.
Check @bimodule_tensor_hom_adjunction.
Check @BimodCat.
Check @BimodHom.
Check @BimodTensor.
Check @bimodule_parametrized_adjunction.
Check @bimodule_hom_bifunctor.
Check @RMod_AbEnriched.

Check @LTensor.
Check @LTensorWith.
Check @LHomSObj.
Check @LHomS.
Check @bimodule_left_tensor_hom_adjunction.
Check @bimodule_left_tensor_preserves_colimits.
Check @bimodule_tensor_preserves_colimits.
Check @PreservesAllColimits.

Check @BimodTensorBimod.
Check @btb_left.
Check @btb_right.
Check @bimodule_adjunction_composite.
Check @tensor_assoc_iso.
Check @ta_to.
Check @ta_from.
Check @ta_iso.
Check @adjunction_along_left_iso.
Check @aali_cell.
Check @bimodule_tensor_bimod_adjunction.
Check @bimodule_hom_composite_iso.

Check @HomAbBimod.
Check @HomAbFunctor.
Check @hab_partial_adj.
Check @bimodule_mirror_family.
Check @bimodule_two_variable_adjunction.
Check @bimodule_third_leg.
Check @mr_left.
Check @mr_right.
Check @mirror_family.
Check @mutually_right_adjoint.
Check @AdjointOnTheRight.
Check @Swap.
Check @Partial_r.
Check @Partial_l.

Check @ZRight.
Check @int_mult_bal.
Check @int_tensor_separates.

(* ================================================================= *)
(* (1) N1-N2.  [Ring_op] is not strictly involutive, so the two       *)
(*     readings of a right module are not interchangeable on the      *)
(*     nose.  Both are CONVERSION.                                    *)
(* ================================================================= *)

Section P401RingOp.

Context (R : RingObject).

(* CONTROLS: all six DATA fields of the double opposite DO agree. *)
Example p401_op_setoid :
  rig_setoid (ring_rig (Ring_op (Ring_op R))) = rig_setoid (ring_rig R)
  := eq_refl.
Example p401_op_add :
  rig_add (ring_rig (Ring_op (Ring_op R))) = rig_add (ring_rig R)
  := eq_refl.
Example p401_op_one :
  rig_one (ring_rig (Ring_op (Ring_op R))) = rig_one (ring_rig R)
  := eq_refl.
Example p401_op_zero :
  rig_zero (ring_rig (Ring_op (Ring_op R))) = rig_zero (ring_rig R)
  := eq_refl.
Example p401_op_mul :
  rig_mul (ring_rig (Ring_op (Ring_op R))) = rig_mul (ring_rig R)
  := eq_refl.
Example p401_op_neg :
  ring_neg (Ring_op (Ring_op R)) = ring_neg R := eq_refl.

(* -- N1 (CONVERSION) -- *)
Fail Example p401_n1 : Ring_op (Ring_op R) = R := eq_refl.

(* -- N2 (CONVERSION) -- *)
Fail Example p401_n2 : ModR (Ring_op R) = RMod R := eq_refl.

(* CONTROL: what IS true on the nose. *)
Example p401_modR_unfold : ModR R = RMod (Ring_op R) := eq_refl.

End P401RingOp.

(* ================================================================= *)
(* (2) N3-N7.  Instance/Mod/Tensor.v's [TensorMod] serves NEITHER     *)
(*     handedness of Exercise 3, and the one term that DOES typecheck *)
(*     computes the wrong object.  All TYPING.                        *)
(* ================================================================= *)

Section P401TensorMod.

Context (R S : RingObject).
Context (E : Bimodule R S).
Context (F : Bimodule S R).
Context (N : RModObject (Ring_op R)).

(* -- N3 (TYPING) -- *)
Fail Check (TensorMod N (bm_left E)).

(* -- N4 (TYPING) -- *)
Fail Check (@TensorMod R N (bm_left E)).

(* -- N5 (TYPING) -- *)
Fail Check (@TensorMod (Ring_op R) N (bm_left E)).

(* -- N6 (TYPING) -- *)
Fail Check (RBilinear N (bm_left E) (bm_left E)).

(* CONTROLS: [TensorMod] is fine when both factors are modules over ONE
   ring on the SAME side. *)
Check (@TensorMod R (bm_left E) (bm_left E)).
Check (@TensorMod (Ring_op R) N N).

(* CONTROL, and the HAZARD: this one IS accepted. *)
Definition p401_hazard_accepted : RModObject (Ring_op R) :=
  @TensorMod (Ring_op R) N (bimodule_right_RMod F).

(* -- N7 (TYPING).  It is a right R-module, so it is not an object of
      [ModR S], which is where Exercise 3's N ⊗_R E lives. -- *)
Fail Definition p401_n7 : RModObject (Ring_op S) :=
  @TensorMod (Ring_op R) N (bimodule_right_RMod F).

(* CONTROL: the object Exercise 3 does produce, at the same [N]. *)
Check (RTensor E N : RModObject (Ring_op S)).

End P401TensorMod.

(* ================================================================= *)
(* (3) N8-N9.  Riehl's general three-ring form is closed off: a right *)
(*     R-module is not a (ℤ,R)-bimodule in this tree.  Both TYPING.   *)
(* ================================================================= *)

Section P401Integers.

Context (R : RingObject).
Context (M : RModObject (Ring_op R)).

(* -- N8 (TYPING) -- *)
Fail Check (M : RModObject Int_Ring).

(* -- N9 (TYPING) -- *)
Fail Check (@Build_Bimodule Int_Ring R M).

(* CONTROLS: ℤ's own bimodule, and the module reading that DOES hold. *)
Check (Int_Bimodule : Bimodule Int_Ring Int_Ring).
Check (bm_left Int_Bimodule : RModObject Int_Ring).
Check (M : RModObject (Ring_op R)).

End P401Integers.

(* ================================================================= *)
(* (4) N10-N13.  Part (c)'s comparison is an isomorphism and NOTHING  *)
(*     stronger: the two functors are different records, the two      *)
(*     objects are different records, and the two module structures   *)
(*     on the tensor of two bimodules do not even share a type.       *)
(* ================================================================= *)

Section P401PartC.

Context (R S T : RingObject).
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).
Context (N : RModObject (Ring_op R)).

(* CONTROLS: the comparison exists, and its two sides DO share a type. *)
Check (tensor_assoc_iso E E1
  : (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
      ≈ TensorWith (BimodTensorBimod E E1)).
Check ((RTensor E1 (RTensor E N) : RModObject (Ring_op T))
         = RTensor (BimodTensorBimod E E1) N).

(* -- N10 (CONVERSION) -- *)
Fail Example p401_n10 :
  (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
    = TensorWith (BimodTensorBimod E E1) := eq_refl.

(* -- N11 (CONVERSION) -- *)
Fail Example p401_n11 :
  (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
    = HomS (BimodTensorBimod E E1) := eq_refl.

(* -- N16 (CONVERSION) -- Mac Lane's whiskered description of the
   composite's unit holds at ≈ ([bac_unit_whiskered]) and NOT on the nose:
   Adjunction/Compose.v:216 is a [Qed] corollary proved by rewriting. *)
Fail Example p401_n16 :
  bac_unit E E1 N
    = fmap[HomS E]
        (@unit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E1) (RTensor E N))
      ∘ @unit (ModR S) (ModR R) (TensorWith E) (HomS E)
          (bimodule_tensor_hom_adjunction E) N := eq_refl.

(* -- N17 (CONVERSION) -- the counit's twin ([bac_counit_whiskered],
   Adjunction/Compose.v:224). *)
Fail Example p401_n17 (M : RModObject (Ring_op T)) :
  bac_counit E E1 M
    = @counit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
        (bimodule_tensor_hom_adjunction E1) M
      ∘ fmap[TensorWith E1]
          (@counit (ModR S) (ModR R) (TensorWith E) (HomS E)
             (bimodule_tensor_hom_adjunction E) (HomSObj E1 M)) := eq_refl.

(* CONTROLS for N16/N17: the ≈ forms are theorems of the target. *)
Check (bac_unit_whiskered E E1 N).
Check (fun (M : RModObject (Ring_op T)) => bac_counit_whiskered E E1 M).
Check @bac_unit.
Check @bac_counit.
Check @unit.
Check @counit.
Check @fmap.

(* CONTROL: what the file DOES deliver in place of N11. *)
Check (bimodule_hom_composite_iso E E1
  : (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
      ≈ HomS (BimodTensorBimod E E1)).

(* -- N12 (TYPING).  Read at the SECOND ring the two sides of the
      comparison are not even of one type. -- *)
Fail Check (RTensor E1 (RTensor E N) : RModObject (Ring_op S)).

(* -- N13 (TYPING).  The two module structures the tensor of two
      bimodules carries are over DIFFERENT rings. -- *)
Fail Check (btb_left E E1 : RModObject (Ring_op T)).

(* CONTROLS: each on its own ring, and the ONE group they share. *)
Check (btb_left E E1 : RModObject R).
Check (btb_right E E1 : RModObject (Ring_op T)).
Example p401_btb_same_group :
  rm_ab (btb_left E E1) = rm_ab (btb_right E E1) := eq_refl.

End P401PartC.

(* ================================================================= *)
(* (5) N14-N15.  The hom-group's enrichment demands a category whose  *)
(*     hom and proof universes coincide.                              *)
(* ================================================================= *)

Section P401Univ.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).

(* CONTROLS at the DECLARED levels. *)
Check (fun (x y : Cu) => x ~{Cu}~> y).
Check (fun (x : Cu) => @id Cu x).
Check (fun (x y z : Cu) (f : y ~> z) (g : x ~> y) => f ∘ g).

(* -- N14 (FORMABILITY) -- *)
Fail Check (AbEnriched Cu).

(* -- N15 (FORMABILITY, fired at its ARGUMENT) -- *)
Fail Check (fun (AC : AbEnriched Cu) (x y : Cu) => hom_ab AC x y).

End P401Univ.

(* ================================================================= *)
(* (6) POSITIVE CONTROLS for the three headline artifacts of stage 2. *)
(* ================================================================= *)

Section P401Positives.

Context (R S T : RingObject).
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Check (bimodule_adjunction_composite E E1
  : (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1)).

Check (bimodule_left_tensor_hom_adjunction E
  : LTensorWith E ⊣ LHomS E).

Check (bimodule_tensor_preserves_colimits E
  : PreservesAllColimits (TensorWith E)).

Check (fun (M : RModObject (Ring_op S)) (N : RModObject (Ring_op R)) =>
  bimodule_third_leg M E N
    : @Isomorphism Sets
        {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
           is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |}
        {| carrier := N ~{ModR R}~> HomSObj E M;
           is_setoid := @homset (ModR R) N (HomSObj E M) |}).

End P401Positives.
