(** * Probe for the variety development (issue #440)

    Pins the measured boundaries of Mac Lane §V.6 / Awodey §9.8 as they
    are actually delivered.  Negatives of three kinds, kept lexically
    apart, each stripped one at a time in a copy of the WHOLE file with
    the error read.

    CONVERSION (each error read as "cannot unify"): n1, the root of every
    [functional_extensionality] in this development — an argument bundle
    over the EMPTY arity is not convertible to the empty match, so the
    pointwise-to-Leibniz step that [EqSignature]'s naturality fields
    demand cannot be taken by computation; n2, [clone_act_subst] is a
    genuine induction and not a definitional identity; n4,
    [GroupVariety] and [Grp] are not the same category, which is what
    Instance/Variety/GroupComparison.v's header says and all it says —
    that file ships a fully faithful comparison, not an isomorphism.

    TYPING (error read as "cannot satisfy constraint"): n3, the equations
    are NOT dropped — the naive [eq_refl] satisfaction proof for [AndOp],
    the booleans under conjunction, does not ascribe, because it would
    force [lhs e args] and [rhs e args] to be convertible.  That refutation
    alone would only refute ONE candidate term, so the substance is
    carried by a positive theorem beside it: [AndOp_not_group] proves
    that NO satisfaction proof exists, while the control above it shows
    [AndOp] is a perfectly good object of the equation-free [Algs].

    The import list contains the FULL union of the three target files'
    lists, plus the targets themselves. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Clone.
Require Import Category.Instance.Variety.GroupComparison.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(* instrument: the refutation keyword is live *)
Fail Check probe440_absent_name.

(** ** A: CONVERSION — the axiom root, and a genuine induction *)

Section BundleRoot.

Context {A B : UA.OpAlgebra UA.GroupOp}.
Context (f : UA.AlgHom A B).

(* n1 CONVERSION: the empty-arity bundle is not convertible to the empty
   match.  This single refusal is why [EqSignature]'s [lhs_natural] and
   [rhs_natural] need extensionality, hence why [GroupEq] is not
   axiom-free, hence why [GroupVariety] is not. *)
Fail Example p440_nullary_conv :
  (fun i : UA.nullary => UA.map f (match i return UA.carrier A with end))
    = (fun i : UA.nullary => match i return UA.carrier B with end) := eq_refl.

(* control: the same equation WITH extensionality is accepted, and it is
   exactly [nullary_bundle] *)
Example p440_nullary_ext :
  (fun i : UA.nullary => UA.map f (match i return UA.carrier A with end))
    = (fun i : UA.nullary => match i return UA.carrier B with end).
Proof. extensionality i; destruct i. Qed.

End BundleRoot.

Section SubstIsInduction.

Context (S : UA.OpSignature).
Context (A : SetoidAction S).
Context {m n : nat}.
Context (s : Fin.t m → DerivedOperators S n).
Context (t : DerivedOperators S m).
Context (env : Fin.t n → sact_carrier A).

(* n2 CONVERSION: substitution commutes with the action only
   propositionally — [clone_act_subst] recurses over [t], so the two
   sides are not convertible at an abstract [t]. *)
Fail Example p440_subst_conv :
  clone_act A (clone_subst s t) env
    = clone_act A t (fun i => clone_act A (s i) env) := eq_refl.

End SubstIsInduction.

(* control: the two computation rules of the action ARE definitional *)

Example p440_act_var {S : UA.OpSignature} (A : SetoidAction S) {n}
  (i : Fin.t n) (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_var i) env = env i := eq_refl.

Example p440_act_op {S : UA.OpSignature} (A : SetoidAction S) {n}
  (o : UA.operation S) (args : UA.arity o → DerivedOperators S n)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_op o args) env
    = sact_op A o (fun j => clone_act A (args j) env) := eq_refl.

(** ** B: TYPING — the equations are not dropped *)

(* The booleans under conjunction: a perfectly good operation algebra for
   the group signature, and not a group. *)
(* The constructor is applied explicitly rather than through record
   syntax: [UA.op]'s signature quantifies over the operation type of an
   as-yet-unresolved [?S], and record syntax does not fix it. *)
Definition AndOp : UA.OpAlgebra UA.GroupOp :=
  UA.Build_OpAlgebra UA.GroupOp bool
    (fun o => match o return (UA.Group_arity o → bool) → bool with
              | UA.one => fun _ => true
              | UA.mul => fun args => andb (args UA.Fst) (args UA.Snd)
              | UA.inv => fun args => args UA.Only
              end).

(* control: it IS an object of [Algs], the equation-free category *)
Example p440_and_in_algs : @UA.Algs UA.GroupOp := AndOp.

(* the positive half of n3, stronger than any refutation: NO satisfaction
   proof exists, because [false] has no inverse under conjunction *)
Theorem AndOp_not_group : satisfies UA.GroupEq AndOp → False.
Proof.
  intro H.
  pose proof (H UA.inv_left (fun _ => false)) as Hf.
  simpl in Hf.
  discriminate Hf.
Qed.

(* n3 TYPING: so the naive satisfaction proof does not ascribe *)
Fail Example p440_and_in_variety : GroupVariety :=
  (AndOp; fun e args => eq_refl).

(* control: ℤ/2 under exclusive or IS an object of the variety *)
Example p440_bool_in_variety : GroupVariety := GroupVariety_Bool.

(** ** C: CONVERSION — the variety is not the category of groups *)

(* n4 CONVERSION: [GroupVariety] and [Grp] are different categories.  What the
   development ships is the fully faithful comparison below, and the
   header says why the isomorphism is not available. *)
Fail Example p440_variety_is_grp : GroupVariety = Grp := eq_refl.

(* controls: the comparison exists and is full and faithful *)
Example p440_comparison : GroupVariety ⟶ Grp := GroupVariety_to_Grp.
Example p440_comparison_faithful : Faithful GroupVariety_to_Grp :=
  GroupVariety_to_Grp_Faithful.
Example p440_comparison_full : Functor.Full GroupVariety_to_Grp :=
  GroupVariety_to_Grp_Full.

(** ** D: readbacks

    The two presentations of a variety agree on the nose, and the
    forgetful functor's carrier is the algebra's carrier. *)

Example p440_pack_carrier {S : UA.OpSignature} {E : UA.EqSignature S}
  (A : UA.Algebra S E) :
  `1 (Variety_pack A) = UA.alg S E A := eq_refl.

Example p440_forget_carrier {S : UA.OpSignature} {E : UA.EqSignature S}
  (A : Variety E) :
  carrier (fobj[Variety_Forget E] A) = UA.carrier (`1 A) := eq_refl.

(** ** E: guard block *)

Check @satisfies.
Check @Variety_sub.
Check @Variety.
Check @Variety_Full.
Check @Variety_Incl.
Check @Variety_Incl_Faithful.
Check @Variety_pack.
Check @Variety_unpack.
Check @Variety_unpack_pack.
Check @Variety_pack_unpack.
Check @Variety_Forget.
Check @Variety_Forget_Faithful.
Check @GroupVariety.
Check @GroupVariety_Bool.
Check @magma_op.
Check magma_mul.
Check @MagmaOp.
Check @comm_eq.
Check comm_law.
Check @comm_swap.
Check @CommEq.
Check @CommMagmaVariety.
Check @DerivedOperators.
Check @clone_var.
Check @clone_op.
Check @clone_subst.
Check @clone_rename.
Check @SetoidAction.
Check @sact_carrier.
Check @sact_setoid.
Check @sact_op.
Check @sact_op_respects.
Check @sact_alg.
Check @clone_act.
Check @clone_act_var.
Check @clone_act_op.
Check @action_extends_to_clone.
Check @clone_act_subst.
Check @clone_act_rename.
Check @leibniz_action.
Check @action_extends_to_clone_leibniz.
Check @clone_act_subst_leibniz.
Check @nullary_bundle.
Check @binary_bundle.
Check @unary_bundle.
Check @alg_hom_one.
Check @alg_hom_mul.
Check @GroupVariety_obj_to_Grp.
Check @GroupVariety_hom_to_Grp.
Check @GroupVariety_to_Grp.
Check @GroupVariety_to_Grp_Faithful.
Check @GroupVariety_hom_from_Grp.
Check @GroupVariety_to_Grp_Full.
Check @UA.Algs.
Check @UA.Algebra.
Check @UA.GroupEq.
Check @Sub.
Check @Incl.
