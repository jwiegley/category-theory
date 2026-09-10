(** * Probe for Structure/Projective.v (issue #429)

    Pins the measured boundaries of the projective/injective development
    with negatives of four kinds, kept lexically apart: UNIVERSE (N1-N3: at
    a category whose hom and proof levels are declared apart, [Epic],
    [Monic] and [Projective] are all refused while the category, its homs
    and an arrow are accepted — the identification is the donors', not this
    file's); CONVERSION and TYPING (N4-N5: [Epic] in [C^op] is not [Monic]
    in [C], so [injective_extend]'s bridge [op_Epic_of_Monic] does real
    work, while the objects and homs of the duality convert); TYPING (N6: a
    Prop-valued existential over [≈] cannot be stated, [≈] being
    Type-valued — there is no "∃-statement rather than data" option, [∃]
    being [sigT]); PARSING (N7-N8: the [@Injective C] notation claims the
    token [@Injective], as [@Initial C] already claims [@Initial]).  Three
    [eq_refl] readbacks show the witnesses' lifts COMPUTE (the split epi's,
    the initial object's, the Leibniz setoid's), and are what makes those
    three [Defined] load-bearing.  Each refutation was stripped one at a
    time in a copy of the whole file; the import list mirrors the target's.
    Section E's readbacks and the guard block are positive controls. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Orthogonality.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Regular.
Require Import Category.Instance.Two.
Require Import Category.Structure.Projective.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe429_absent_name.

(** ** A: UNIVERSE — [Projective] identifies hom with proof, and the
       identification is [Epic]'s, not this file's *)

Section ProbeUniverse.

Universes vo vh vp.
Constraint vh < vp.

Context (Cu : Category@{vo vh vp}) (x y : Cu) (f : x ~{Cu}~> y).

(* controls: the category, its homs and an arrow all form here *)
Check Cu.
Check (x ~{Cu}~> y).
Check f.

(* N1, N2 UNIVERSE: the donors are already refused at these levels *)
Fail Check (@Epic Cu x y f).
Fail Check (@Monic Cu x y f).

(* N3 UNIVERSE: and so is [Projective], inheriting the identification *)
Fail Check (@Projective Cu x).

End ProbeUniverse.

(** ** B: CONVERSION — [Epic] in [C^op] is not [Monic] in [C]; the bridge
       [op_Epic_of_Monic] does real work, so [injective_extend] is not an
       [eq_refl] readback of the [C^op] accessor's hypothesis *)

Section ProbeBridge.

Context {C : Category} {a b : C} (m : a ~> b).

(* controls: both types form and the bridge exists *)
Check (@Epic (C^op) b a m).
Check (@Monic C a b m).
Check (@op_Epic_of_Monic C a b m).

(* N4 CONVERSION ("cannot unify"), N5 TYPING (a [Monic] proof offered where
   an [Epic] one is expected): the two predicates are distinct records *)
Fail Example p429_bridge_refl : @Epic (C^op) b a m = @Monic C a b m := eq_refl.
Fail Example p429_bridge_id (H : @Monic C a b m) : @Epic (C^op) b a m := H.

(* controls: the OBJECT of the duality is definitional *)
Example p429_op_op : (C^op)^op = C := eq_refl.
Example p429_hom_op : (b ~{C^op}~> a) = (a ~{C}~> b) := eq_refl.

End ProbeBridge.

(** ** C: TYPING — there is no "∃-statement rather than data" option *)

Section ProbeExists.

Context {C : Category} {a b : C}.

(* controls: [∃] and [exists] are both [sigT]; a Prop existential over a
   Prop relation forms *)
Example p429_exists_is_sigT :
  (∃ h : a ~> b, h ≈ h) = { h : a ~> b & h ≈ h } := eq_refl.
Example p429_keyword_exists_is_sigT :
  (exists h : a ~> b, h ≈ h) = { h : a ~> b & h ≈ h } := eq_refl.
Check (ex (fun n : nat => n = n)).

(* N6 TYPING: a Prop-valued existential over [≈], which is Type-valued
   ([ex] unqualified: the Prelude's constant, whose module is [Coq.] on
   8.19/8.20 and [Corelib.] on Rocq 9) *)
Fail Definition p429_prop_lift : Prop :=
  ex (fun h : a ~> b => h ≈ h).

End ProbeExists.

(** ** D: PARSING — the [@Injective C] notation claims the token
       [@Injective], as [@Initial C] already claims [@Initial] *)

Definition Injective_placeholder : nat := 0.
Definition Initial_placeholder : nat := 0.

(* controls: without the [@] both resolve *)
Check Injective_placeholder.
Check Initial_placeholder.

(* N7, N8 PARSING *)
Fail Check @Injective_placeholder.
Fail Check @Initial_placeholder.

(** ** E: readbacks *)

Section Readbacks.

Context {C : Category} (p q : C).

Example p429_inj_is_op_proj : @Injective C q = @Projective (C^op) q := eq_refl.

Example p429_cohom_is_op_hom :
  @Curried_CoHom C q = @Curried_Hom (C^op) q := eq_refl.

Example p429_hom_fmap_is_postcomp {b c : C} (g : b ~> c) (h : p ~> b) :
  fmap[[Hom p ,─]] g h = g ∘ h := eq_refl.

Check (projective_iff_hom_preserves_epi p).
Check (injective_iff_cohom_preserves_mono q).
Check (@Coprod_Projective C).
Check (@IndexedCoprod_Projective C).
Check (@sets_all_projective_entails_LEM).
Check two_projective_not_all.

(* the witnesses' lifts COMPUTE: a split epi lifts by its retraction, the
   initial object lifts by [zero] *)
Example p429_retraction_lift_is {b c : C} (g : b ~> c) (R : Retraction g)
  (f : p ~> c) : `1 (Retraction_lifts g R f) = retract ∘ f := eq_refl.

Example p429_initial_lift_is `{I : @Initial C} {b c : C} (g : b ~> c)
  (He : Epic g) (f : 0 ~> c) :
  `1 (@projective_lift C _ initial_obj_Projective b c g He f) = zero := eq_refl.

End Readbacks.

(* in Sets, the lift of a Leibniz setoid is the chosen preimage, pointwise *)
Example p429_leibniz_lift_is (T : Type) {b c : Sets} (g : b ~> c) (He : Epic g)
  (f : LeibnizSetoid T ~{Sets}~> c) (t : T) :
  `1 (@projective_lift Sets _ (Sets_Leibniz_Projective T) b c g He f) t
    = `1 (epic_implies_surjective g He (f t)) := eq_refl.

(** ** Guard block *)

Check @Projective.
Check @projective_lift.
Check @injective_extend.
Check @Epic.
Check @Monic.
Check @op_Epic_of_Monic.
Check @Curried_Hom.
Check @Curried_CoHom.
Check @Category.
Check @hom.
Check (fun C : Category => Initial C).
Check @zero.
Check Prop.
