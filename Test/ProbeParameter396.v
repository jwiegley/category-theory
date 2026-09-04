Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Construction.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Adjunction.Right.
Require Import Category.Adjunction.Parameter.

Generalizable All Variables.

(** * Boundary probe for Adjunction/Parameter.v (issue #396)

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7
    Theorem 3, book p. 102: adjunctions with a parameter.

    Adjunction/Parameter.v carries ZERO [Fail] commands by design.  Every
    strict ([eq_refl]) claim its three build increments tried and had to
    weaken to [≈] is described in that file's prose and pinned NOWHERE.
    This file is where they are pinned.

    METHOD.  This file mirrors Adjunction/Parameter.v's [Require] list
    character for character, adding only the target module itself (measured:
    [diff] of the two [Require] blocks reports exactly that one line).  A
    probe with a short prefix can fail for a reason it never measured, which
    would be a FALSE PASS, so nothing else is added and nothing dropped.
    Each negative below was stripped one at a time, the file compiled ALONE,
    and the WHOLE error read; the kind recorded beside it is read off that
    error text and not off an expectation:

      TYPING       a plain "has type ... while it is expected to have type",
                   with NO "cannot unify" clause and no universe clause;
      CONVERSION   the error ends "cannot unify";
      FORMABILITY  the error ends "universe inconsistency".

    TALLY.  21 [Fail] commands = 1 instrument check + 20 negatives of THREE
    kinds, told apart by the error TEXT: 12 CONVERSION (negatives 1-4, 6-9,
    11-14), 2 TYPING (negatives 5 and 10 — each a plain type mismatch with
    NO "cannot unify" clause and no universe clause) and 6 FORMABILITY
    (negatives 15-20).  The two TYPING ones are the discriminating pair, and
    they come out OPPOSITE ways: at negative 5 the direct ascription fails
    while the field copy beside it ([copa_swap_transport]) succeeds, whereas
    at negative 10 the field copy ITSELF fails, and it fails at a NAMED
    field.  Each sits beside a CONVERSION negative (4 and 9 respectively)
    about the very two functors being copied between.

    GUARD COVERAGE, measured rather than asserted.  The 21 [Fail] blocks
    mention 85 identifiers; 70 of them appear outside every [Fail], and the
    ones that do not include the 14 [Fail Definition] heads (which never
    enter the environment), the instrument's deliberately absent name, and
    the stdlib constructor [eq_refl], whose code occurrences all sit inside
    [Fail] blocks.

    RENAME SIMULATION.  Each of the 12 constants of Adjunction/Parameter.v
    that a negative names was renamed in THAT FILE ONLY — a whole-file
    rename is a no-op by construction and gives a false verdict — the target
    recompiled (0 errors in every case, so each rename was real) and this
    file recompiled.  12/12 broke it, every one at a [Check] control line
    (103, 105, 106, 108, 195-198, 270, 420, 421, 428) and none inside a
    [Fail].  Zero vacuous guards.  The target was then restored and verified
    byte-identical.

    A MEASUREMENT THAT DID NOT REPRODUCE, recorded rather than pinned.  The
    first build increment reported that writing a transpose with its two
    functors left implicit, [to (@adj _ _ _ _ (pa_adj PA p) x a) k], is
    rejected as a higher-order unification.  It is NOT: the [Adjunction]
    argument's own type determines both functors, and the command is
    accepted (control [p396_hou_control] below).  Naming the two functors,
    as [pa_to] and [pa_from] do, is therefore a readability decision and not
    a forced one.  Nothing is pinned for it, because there is no failure. *)

(** ** Instrument check

    This file's negatives are only as good as the harness: a name that
    exists in no file of the tree must be refused. *)

Fail Check p396_no_such_constant_anywhere.

(** ** Section A: Theorem 3's own boundaries *)

Section Theorem3Boundaries.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA : ParametrizedAdjunction F).
Context {p p' : P} (h : p' ~> p) (hop : p ~{P^op}~> p') (a : A).

(* CONTROLS.  Every constant the negatives of this section name. *)
Check @ParametrizedAdjunction.
Check @pa_right.
Check @pa_adj.
Check @pa_param_mate.
Check @pa_param_mate_universal.
Check @pa_square.
Check @parametrized_right_adjoint_bifunctor.
Check @pa_bifunctor_obj.
Check @pa_bifunctor_fmap.
Check @pa_bifunctor_fmap_param.
Check @pa_bifunctor_fmap_is_mate.
Check @pa_bifunctor_partial_r_obj.
Check @pa_bifunctor_partial_r_fmap_unfold.
Check @pa_bifunctor_partial_r_fmap.
Check @param_transform.
Check @Partial_l.
Check @Partial_r.
Check @conj_mate.
Check @conjugate_unique_right.
Check @unique_obj.
Check @unop.
Check @fmap.

(* A control for the elaboration failure that did not reproduce. *)
Definition p396_hou_control (x : X) (b : A) (k : F (x, p) ~> b) :=
  to (@adj _ _ _ _ (pa_adj PA p) x b) k.

(* Controls for negative 1: the universal exists and the mate exists. *)
Definition p396_universal := pa_param_mate_universal PA h.
Definition p396_mate := pa_param_mate PA h.

(** *** Negative 1 (CONVERSION): the universal's chosen object is not the
        mate on the nose

    [pa_param_mate_universal] is [Defined], but its body is
    [conjugate_unique_right], which Adjunction/Conjugate.v closes with
    [Qed], so the [unique_obj] field sits behind an opaque donor constant
    and nothing reduces.  Stripped, the error ends
    (cannot unify "unique_obj (pa_param_mate_universal PA h)" and
    "pa_param_mate PA h"). *)

Fail Definition p396_universal_strict :
  unique_obj (pa_param_mate_universal PA h) = pa_param_mate PA h := eq_refl.

(** *** Negative 2 (CONVERSION): the second partial functor is the given
        family in both DATA fields but not as a RECORD

    Both data fields DO agree, at [eq_refl], by the two controls just
    below; the difference is confined to the three law fields, which
    [Partial_r]'s [Program] elaboration rebuilds as its own obligations.
    Stripped, the error ends
    (cannot unify "Partial_r (parametrized_right_adjoint_bifunctor PA) p"
    and "pa_right PA p"). *)

Definition p396_partial_r_obj_control := pa_bifunctor_partial_r_obj PA p a.
Definition p396_partial_r_fmap_control {b : A} (k : a ~> b) :=
  pa_bifunctor_partial_r_fmap_unfold PA p k.

Fail Definition p396_partial_r_strict :
  Partial_r (parametrized_right_adjoint_bifunctor PA) p = pa_right PA p
  := eq_refl.

(** *** Negative 3 (CONVERSION): the pure-parameter arrow action is not the
        bare mate

    The residue is [fmap[G p'] id], and it is EXHIBITED at Leibniz equality
    by the control [pa_bifunctor_fmap_param] rather than described.
    Clearing it needs [fmap_id], an opaque law field, so only [≈] holds
    ([pa_bifunctor_fmap_is_mate]).  Stripped, the error ends
    (cannot unify "fmap[parametrized_right_adjoint_bifunctor PA] (h, id{A})"
    and "pa_param_mate PA (unop h) a"). *)

Definition p396_fmap_param_control := pa_bifunctor_fmap_param PA hop a.
Definition p396_fmap_param_weak := pa_bifunctor_fmap_is_mate PA hop a.

Fail Definition p396_fmap_param_strict :
  fmap[parametrized_right_adjoint_bifunctor PA]
      ((hop, id[a]) : (p, a) ~{P^op ∏ A}~> (p', a))
    = pa_param_mate PA (unop hop) a := eq_refl.

End Theorem3Boundaries.

(** ** Section B: the dual's boundaries *)

Section DualBoundaries.

Context {P A X : Category}.
Context {G : P^op ∏ A ⟶ X}.
Context (CA : CoParametrizedAdjunction G).
Context (p : P) (x : X) {p1 p2 : P} (k : p1 ~> p2).

(* CONTROLS. *)
Check @CoParametrizedAdjunction.
Check @pa_left.
Check @pa_coadj.
Check @copa_param_mate.
Check @parametrized_left_adjoint_bifunctor.
Check @copa_bifunctor_obj.
Check @copa_bifunctor_fmap.
Check @copa_bifunctor_fmap_param.
Check @copa_bifunctor_fmap_is_mate.
Check @copa_swap_obj.
Check @copa_swap_fmap.
Check @copa_swap_transport.
Check @copa_swap_route.
Check @Swap.
Check @Adjunction.

Definition p396_swap_obj_control (b : A) := @copa_swap_obj P A X G p b.
Definition p396_swap_fmap_control {b b' : A} (m : b ~> b') :=
  @copa_swap_fmap P A X G p b b' m.
Definition p396_swap_transport_control :=
  copa_swap_transport CA p (pa_coadj CA p).

(** *** Negative 4 (CONVERSION): [Partial_l (G ◯ Swap) p] is not
        [Partial_r G p] as a record

    Both data fields agree at [eq_refl] (the two controls above), so the
    difference is confined to the three law fields, which [Partial_l] and
    [Partial_r] rebuild as separate [Program] obligations.  This is why the
    [Swap] route needs the field-copy [copa_swap_transport].  Stripped, the
    error ends (cannot unify "Partial_l (G ◯ Swap) p" and
    "Partial_r G p"). *)

Fail Definition p396_swap_strict :
  Partial_l (G ◯ @Swap A (P^op)) p = Partial_r G p := eq_refl.

(** *** Negative 5 (TYPING): consequently the adjunction does not ascribe

    Note the KIND: this is a plain type mismatch with NO "cannot unify"
    clause, where negative 4 is a conversion one.  The transport works only
    because every [Adjunction] field mentions its left adjoint solely
    through [F x] and [fmap[F] g], both of which DO convert here. *)

Fail Definition p396_swap_ascribe :
  Partial_l (G ◯ @Swap A (P^op)) p ⊣ pa_left CA p := pa_coadj CA p.

(** *** Negative 6 (CONVERSION): the dual bifunctor's pure-parameter arrow
        action is not the bare mate

    The mirror of negative 3, with the residue [fmap[L p'] id] exhibited by
    the control [copa_bifunctor_fmap_param].  Stripped, the error ends
    (cannot unify "fmap[parametrized_left_adjoint_bifunctor CA] (id{X}, k)"
    and "copa_param_mate CA k x"). *)

Definition p396_copa_fmap_param_control :=
  @copa_bifunctor_fmap_param P A X G CA x p1 p2 k.
Definition p396_copa_fmap_param_weak :=
  @copa_bifunctor_fmap_is_mate P A X G CA x p1 p2 k.

Fail Definition p396_copa_fmap_param_strict :
  fmap[parametrized_left_adjoint_bifunctor CA]
      ((id[x], k) : (x, p1) ~{X ∏ P}~> (x, p2))
    = copa_param_mate CA k x := eq_refl.

End DualBoundaries.

(** ** Section C: the currying instance's boundaries *)

Section CurryingBoundaries.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.
Context {p p' : C} (h : p' ~> p) (a : C).
Context {x y : C} (f : x ~> y).

(* CONTROLS. *)
Check @curry_ParametrizedAdjunction.
Check @curry_pa_adj.
Check @curry_pa_right.
Check @curry_pa_to_is_curry.
Check @curry_pa_from_is_uncurry.
Check @curry_prod_functor_obj.
Check @curry_prod_functor_fmap.
Check @curry_param_mate_unfold.
Check @curry_param_mate_residue.
Check @curry_param_mate_is_closed_action.
Check @curry_param_mate_is_ihom.
Check @curry_param_mate_is_internal_hom.
Check @curry_internal_hom_fmap_unfold.
Check @curry_bifunctor_obj.
Check @curry_bifunctor_fmap.
Check @curry_natural_param.
Check @uncurry_natural_param.
Check @ihom_id_action.
Check @Prod_Functor.
Check @Exp_Functor.
Check @Curry_Adjunction.
Check @InternalHomFunctor.
Check @InternalProductFunctor.
Check @ihom.
Check @second.
Check @curry.
Check @eval.
Check @to_adj_nat_l.
Check @to_adj_nat_r.
Check @from_adj_nat_l.
Check @from_adj_nat_r.
Check @adj.
Check @Build_Adjunction.

Definition p396_curry_residue_control :=
  curry_param_mate_residue h a.
Definition p396_curry_closed_control :=
  curry_param_mate_is_closed_action h a.
Definition p396_curry_ihom_control := curry_param_mate_is_ihom h a.
Definition p396_curry_prod_obj_control := curry_prod_functor_obj p x.
Definition p396_curry_prod_fmap_control := curry_prod_functor_fmap p f.
Definition p396_curry_bifunctor_obj_control := curry_bifunctor_obj p a.
Definition p396_curry_adj_control :=
  @adj C C (Prod_Functor p) (Exp_Functor p) (Curry_Adjunction p).

(** *** Negative 7 (CONVERSION): the currying mate is not
        [curry (eval ∘ second h)] on the nose

    The control [curry_param_mate_residue] holds at [eq_refl] and exhibits
    the mate as [curry (eval ∘ ((id ∘ exl) △ (h ∘ exr)))], while [second h]
    is [exl △ (h ∘ exr)]; clearing the [id ∘ exl] needs [id_left], a law
    field.  Stripped, the error ends (cannot unify
    "pa_param_mate curry_ParametrizedAdjunction h a" and
    "curry (eval ∘ second h)"). *)

Fail Definition p396_curry_mate_closed_strict :
  pa_param_mate curry_ParametrizedAdjunction h a
    = curry (eval ∘ second h) := eq_refl.

(** *** Negative 8 (CONVERSION): nor is it the internal-hom action

    The two targets of negatives 7 and 8 are themselves [eq_refl]-equal
    (Structure/Cartesian/Closed/Natural.v's
    [ihom_is_InternalHomFunctor_fmap]), and the control
    [curry_internal_hom_fmap_unfold] pins the second one's normal form.
    Stripped, the error ends (cannot unify
    "pa_param_mate curry_ParametrizedAdjunction h a" and
    "fmap[InternalHomFunctor C] (h, id{C})"). *)

Fail Definition p396_curry_mate_ihom_strict :
  pa_param_mate curry_ParametrizedAdjunction h a
    = @fmap _ _ (InternalHomFunctor C) (p, a) (p', a) (h, id[a])
  := eq_refl.

(** *** Negative 9 (CONVERSION): [Partial_l ×(C) p] is not [Prod_Functor p]
        on arrows

    The OBJECT actions do agree, at [eq_refl] — that is the control
    [curry_prod_functor_obj] — and the arrow actions differ by exactly one
    [id_left]: [bimap f id] is [(f ∘ exl) △ (id ∘ exr)] where [first f] is
    [(f ∘ exl) △ exr].  This is why [curry_pa_adj] is built with
    [Build_Adjunction'] rather than by transporting [Curry_Adjunction].
    Stripped, the error ends (cannot unify "fmap[Partial_l ×(C) p] f" and
    "fmap[Prod_Functor p] f"). *)

Fail Definition p396_prod_functor_fmap_strict :
  fmap[Partial_l ×(C) p] f = fmap[Prod_Functor p] f := eq_refl.

(** *** Negative 10 (TYPING): the field-copy transport is rejected, and it
        is rejected AT A NAMED FIELD

    This is DISCRIMINATING rather than a bare failure: elaboration gets PAST
    [adj], which mentions [fobj] alone and [fobj] converts (the control
    [p396_curry_adj_control] above), and stops at [to_adj_nat_l], the first
    field mentioning [fmap[F] g] — exactly the action negative 9 refutes.
    That is why [curry_pa_adj] re-proves the two naturality clauses through
    one [id_left] under the transpose instead of copying fields, and it is
    the contrast with negative 5, where the field copy DOES work.  Stripped,
    the error is a plain "has type ... while it is expected to have type",
    naming [@to_adj_nat_l _ _ _ _ (Curry_Adjunction p)], with no "cannot
    unify" clause and no universe clause. *)

Fail Definition p396_curry_field_copy :
  Partial_l ×(C) p ⊣ Exp_Functor p :=
  @Build_Adjunction C C (Partial_l ×(C) p) (Exp_Functor p)
    (fun u v => @adj C C (Prod_Functor p) (Exp_Functor p)
                  (Curry_Adjunction p) u v)
    (@to_adj_nat_l   C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p))
    (@to_adj_nat_r   C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p))
    (@from_adj_nat_l C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p))
    (@from_adj_nat_r C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p)).

(** *** Negative 11 (CONVERSION): the assembled bifunctor is not
        [InternalHomFunctor] on arrows

    The OBJECT actions agree at [eq_refl] (the control
    [curry_bifunctor_obj]); the arrow actions differ because
    [InternalHomFunctor] transposes ONCE where the assembled bifunctor
    transposes TWICE, so the gap is one [curry_comp], one [id_left] and
    associativity — delivered as [curry_bifunctor_fmap] at [≈].  A record
    comparison would fail a fortiori and is not stated separately.
    Stripped, the error ends (cannot unify
    "fmap[parametrized_right_adjoint_bifunctor curry_ParametrizedAdjunction]
    (h, k)" and "fmap[InternalHomFunctor C] (h, k)"). *)

Fail Definition p396_curry_bifunctor_fmap_strict {b : C} (k : a ~> b) :
  fmap[parametrized_right_adjoint_bifunctor curry_ParametrizedAdjunction]
      ((h, k) : (p, a) ~{C^op ∏ C}~> (p', b))
    = fmap[InternalHomFunctor C] ((h, k) : (p, a) ~{C^op ∏ C}~> (p', b))
  := eq_refl.

End CurryingBoundaries.

(** ** Section D: the unit/counit presentation's boundaries *)

Section TransformBoundaries.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA : ParametrizedAdjunction F).
Context (p : P) (x : X) (a : A) (k : F (x, p) ~> a).

(* CONTROLS. *)
Check @ParametrizedAdjunctionTransform.
Check @pat_right.
Check @pat_adj.
Check @pat_of_pa.
Check @pa_of_pat.
Check @parametrized_adjunction_iff_transform.
Check @pa_pat_round_right.
Check @pat_unit_is_pa_unit.
Check @pat_counit_is_pa_counit.
Check @pa_pat_round_to.
Check @pa_pat_round_from.
Check @pa_to.
Check @pa_from.
Check @pa_unit.
Check @pa_counit.
Check @pa_triangle_left.
Check @pa_triangle_right.

Definition p396_round_right_control := pa_pat_round_right PA.
Definition p396_round_unit_control := pat_unit_is_pa_unit PA p x.
Definition p396_round_counit_control := pat_counit_is_pa_counit PA p a.
Definition p396_round_to_weak := pa_pat_round_to PA p x a k.

(** *** Negative 12 (CONVERSION): the round trip is not the identity on the
        whole record

    The family of right adjoints DOES round-trip at [eq_refl], and so do the
    unit and counit COMPONENTS — the three controls above — so the
    difference is confined to the hom-set isomorphism, which
    [Adjunction_from_Transform] rebuilds out of the transposes.  Stripped,
    the error ends (cannot unify "pa_of_pat (pat_of_pa PA)" and "PA"). *)

Fail Definition p396_pat_round_whole :
  pa_of_pat (pat_of_pa PA) = PA := eq_refl.

(** *** Negative 13 (CONVERSION): nor on the transpose

    The residue is exactly the universal-arrow rewriting ⌊f⌋ ≈ fmap[U] f ∘ η,
    which is where [Adjunction_from_Transform]'s forward map comes from;
    the [≈] form is [pa_pat_round_to], the control above.  Stripped, the
    error ends (cannot unify
    "pa_to (pa_of_pat (pat_of_pa PA)) p x a k" and "pa_to PA p x a k"). *)

Fail Definition p396_pat_round_to_strict :
  pa_to (pa_of_pat (pat_of_pa PA)) p x a k = pa_to PA p x a k := eq_refl.

End TransformBoundaries.

(** ** Section E: dinaturality is not the wedge condition

    Adjunction/Parameter.v packages the unit as a [Wedge] and states the
    elementary form as [pa_unit_dinatural], and its header records that
    Theory/Dinatural.v's hexagon does NOT fit on the nose.  That is the
    fact pinned here, with the two interderivations shipped as passing
    controls, so the deferral is measured rather than asserted.

    The source of the hexagon here is the CONSTANT bifunctor at the apex,
    which is what a wedge is (Structure/Wedge.v's own header says so), and
    it is written out inline below.  Read its cost precisely: it DOES raise
    three [Program] obligations — [Print Module] on this file lists
    [p396_const_bifunctor_obligation_1..3], where a [.glob] sweep sees none
    — but all three are discharged by the default [Obligation Tactic], so a
    following [Next Obligation] reports "No obligations remaining" and no
    proof is written for it.  Instance/Fun/Terminal.v's [Constant_Functor]
    is therefore not required, which matters because
    Adjunction/Parameter.v's own header measures its marginal cost there at
    28 modules. *)

Section DinaturalShape.

Context {C D : Category}.

Program Definition p396_const_bifunctor (w : D) : C^op ∏ C ⟶ D := {|
  fobj := fun _ => w;
  fmap := fun _ _ _ => id[w]
|}.

Context (Hf : C^op ∏ C ⟶ D).
Context (w : D) (leg : ∀ z : C, w ~> Hf (z, z)).
Context {u v : C} (f : u ~> v).

(* CONTROLS. *)
Check @Wedge.
Check @wedge_obj.
Check @wedge_map.
Check @ump_wedges.
Check @bimap.
Check @op.
Check p396_const_bifunctor.

(* The wedge condition, in Structure/Wedge.v's own spelling. *)
Definition p396_wedge_cond : Type :=
  bimap[Hf] id f ∘ leg u ≈ bimap[Hf] (op f) id ∘ leg v.

(* The dinaturality hexagon, at the constant source, whose two [bimap]
   factors are the identity of the apex. *)
Definition p396_dinat_cond : Type :=
  bimap[Hf] (op f) id ∘ leg v ∘ bimap[p396_const_bifunctor w] id f
    ≈ bimap[Hf] id f ∘ leg u ∘ bimap[p396_const_bifunctor w] (op f) id.

(* Both interderivations, as passing controls: two [id_right]s and a
   [symmetry] separate the two conditions. *)

Definition p396_wedge_to_dinat : p396_wedge_cond → p396_dinat_cond.
Proof.
  unfold p396_wedge_cond, p396_dinat_cond.
  intro E; simpl; rewrite !id_right; now symmetry.
Defined.

Definition p396_dinat_to_wedge : p396_dinat_cond → p396_wedge_cond.
Proof.
  unfold p396_wedge_cond, p396_dinat_cond.
  intro E; simpl in E; rewrite !id_right in E; now symmetry.
Defined.

(** *** Negative 14 (CONVERSION): the hexagon is not the wedge condition

    Stripped, the error ends (cannot unify "p396_dinat_cond" and
    "p396_wedge_cond"). *)

Fail Definition p396_dinat_is_wedge :
  p396_dinat_cond = p396_wedge_cond := eq_refl.

End DinaturalShape.

(** ** Section F: where hom = proof is forced

    Every constant of Adjunction/Parameter.v is over categories whose hom
    and proof universes coincide, expressed by REUSING the level variable in
    the BINDER while no constraint block carries such an equation.  That is
    INHERITED, and TWO donors are separated below, each sufficient ALONE:
    the PRODUCT of categories, with no adjunction and no functor pair in the
    command, and [Adjunction], with no product in the command.  [Functor] is
    NOT a donor — it is accepted at the very levels where both negatives are
    refused.

    A CORRECTION, measured.  The first build increment reported [Partial_l]
    as the second donor, on the strength of the command
    [fun (F : (Cu ∏ Cu) ⟶ Cu) (c : Cu) => Partial_l F c].  That command is
    indeed refused, but it is refused AT ITS ARGUMENT: negative 15 below
    shows [Cu ∏ Cu] alone is already refused at these levels, so elaboration
    never reaches [Partial_l] and the probe measured nothing about it.
    [Partial_l] cannot be tested apart from the product — its argument's
    type IS one — so it is NOT blamed here, and whether it identifies
    anything of its OWN is UNKNOWN rather than refuted. *)

Section HomEqualsProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (Fu Uu : Cu ⟶ Cu).

(* CONTROLS at the declared levels. *)
Check Cu.
Check Fu.
Check Uu.
Check (fun z : Cu => z).
Check (fun z w : Cu => z ~{Cu}~> w).
Check (fun z : Cu => id[z]).
Check (fun (z w : Cu) (g g' : z ~> w) => g ≈ g').
Check (@Functor Cu Cu).
Check @Product.
Check @Partial_l.

(** *** Negative 15 (FORMABILITY): the PRODUCT of categories alone

    No adjunction, no partial functor and no record in the command.  This is
    what makes negative 16 discriminating and what disqualifies [Partial_l]
    as a separately testable donor.  Stripped, the error ends "universe
    inconsistency: Cannot enforce cp = ch because ch < cp". *)

Fail Check (Cu ∏ Cu).

(** *** Negative 16 (FORMABILITY): [Adjunction] alone

    No product, no partial functor and no parametrized record in the
    command; the control [Check Fu] above shows both functors are formable
    at these levels, so what is refused is the adjunction.  Stripped, the
    error is REPORTED ON [Fu] and displays two [@Functor] instances — the
    one [Fu] has, at [@{co ch cp co ch cp}], against the one [Adjunction]
    demands, whose hom and proof levels are the SAME variable — and it ends
    "universe inconsistency: Cannot enforce cp = ch because ch < cp".  The
    position is what makes it discriminating: [Functor] is not being
    refused, [Adjunction]'s own shape is. *)

Fail Check (Fu ⊣ Uu).

End HomEqualsProof.

(** ** Section G: where the two hom levels are identified

    Adjunction/Parameter.v's constraint blocks carry the equation [u0 = u4],
    identifying X's and A's hom-and-proof levels while leaving all three
    OBJECT universes free.  It needs no adjunction and no record: the mere
    presence of functors in BOTH directions forces it, which is exactly the
    shape of [ParametrizedAdjunction] ([Partial_l F p : X ⟶ A] and
    [pa_right p : A ⟶ X]). *)

Section TwoHomLevels.

Universes xo xh ao ah.
Constraint xh < ah.

Context (Xu : Category@{xo xh xh}).
Context (Au : Category@{ao ah ah}).

(* CONTROLS at the declared levels, including the functor in the direction
   that IS formable. *)
Check Xu.
Check Au.
Check (fun z w : Xu => z ~{Xu}~> w).
Check (fun z w : Au => z ~{Au}~> w).
Check (Xu ⟶ Au).

(** *** Negative 17 (FORMABILITY): the reverse functor

    Stripped, the error ends "universe inconsistency: Cannot enforce
    xh = ... because xh < ah <= ...". *)

Fail Check (Au ⟶ Xu).

End TwoHomLevels.

(** ** Section H: where §F's and §H's parameter collapse is forced

    [UnitIntegrand] and everything of Adjunction/Parameter.v's §H
    additionally identify P's hom-and-proof level with X's.  TWO donors are
    separated below and each is sufficient ALONE, so the [Wedge] packaging
    costs NOTHING EXTRA — [UnitIntegrand] already pays the pin through its
    [Compose] before [Wedge] is mentioned.  The third negative is §H's, and
    it is reached BEFORE any class is formed: functors in both directions
    between P and X suffice, so [AdjointOnTheRight] is not blamed. *)

Section ParameterCollapse.

Universes po ph ao2 ah2 xo xh2.
Constraint ph < xh2.

Context (Pu : Category@{po ph ph}).
Context (Au : Category@{ao2 ah2 ah2}).
Context (Xu : Category@{xo xh2 xh2}).
Context (Hf : (Pu^op ∏ Pu) ⟶ Xu).
Context (K : (Pu^op ∏ Pu) ⟶ (Pu^op ∏ Au)).
Context (L : (Pu^op ∏ Au) ⟶ Xu).

(* CONTROLS at the declared levels: the source, the integrand's type, the
   integrand itself, both composable halves, and the formable direction of
   §H's functor pair. *)
Check Pu.
Check Au.
Check Xu.
Check (Pu^op ∏ Pu).
Check ((Pu^op ∏ Pu) ⟶ Xu).
Check Hf.
Check K.
Check L.
Check (Pu^op ⟶ Xu).
Check @AdjointOnTheRight.
Check @Compose.

(** *** Negative 18 (FORMABILITY): [Wedge] forces ph = xh

    Stripped, the error ends "universe inconsistency: Cannot enforce
    xh2 = ph because ph < xh2", reported on [Xu]. *)

Fail Check (@Wedge Pu Xu Hf).

(** *** Negative 19 (FORMABILITY): [Compose] forces the SAME identification,
        independently

    THIS IS THE DISCRIMINATING ONE: [UnitIntegrand] is a composite, so it
    already carries the pin before [Wedge] is mentioned.  Stripped, the
    error ends "universe inconsistency: Cannot enforce ph = xh2 because
    ph < xh2". *)

Fail Check (L ◯ K).

(** *** Negative 20 (FORMABILITY): §H's collapse, before any class

    [Pu^op ⟶ Xu] is accepted (the control above) and the reverse is not, so
    the identification §H's constants carry is forced by functors in both
    directions and NOT by [AdjointOnTheRight], whose own control is above.
    Stripped, the error ends "universe inconsistency: Cannot enforce
    ph = ... because ph < xh2 <= ...". *)

Fail Check (Xu^op ⟶ Pu).

End ParameterCollapse.
