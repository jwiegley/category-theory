(** * Probe for the free-algebra adjunction (issue #441)

    Pins the measured boundaries of Mac Lane §V.6's free-algebra
    construction as it is actually delivered.

    THE LOAD-BEARING CLAIM is negative and is carried by a THEOREM, not
    by a refutation command: the TERM ALGEBRA does not satisfy the equations in the
    LEIBNIZ sense.  Read that for exactly what it says — an earlier
    revision of this header went on to infer that #440's [Variety CommEq]
    "has no free object on two generators", which is FALSE and was
    refuted by construction (sorting terms into normal forms builds one).
    What the theorem shows is that the NAIVE construction does not land
    in the Leibniz variety; [free_empty_eq_leibniz] below shows the
    claim needs a qualifier even for the naive one.  The reason for the
    setoid carrier is uniformity in ⟨Ω,E⟩, and Instance/Variety/Free.v's
    header states it.
    [free_magma_not_comm_leibniz] proves that no satisfaction proof
    exists, which a refutation of one candidate term could not; the
    beside it (n1) records that the obvious attempt is refused, and the
    control above it shows the shape IS inhabited at a different algebra
    (the booleans under [xorb]).

    The second negative is also a theorem: [free_comm_not_collapsed]
    shows the congruence does not identify distinct generators, so
    [Free_Variety] is not the trivial algebra at THIS presentation.  It
    is proved by mapping into a commutative magma with
    [free_alg_ext_respects] — the respectfulness lemma the universal
    property is built from, not the universal property itself; an
    earlier revision of this sentence said the latter.

    CONVERSION: n2, the free algebra's carrier is the term type but its
    `≈` is not Leibniz [=], so the two do not convert; n3, two distinct
    terms are not convertible, which is what makes n1 a statement about
    equality rather than about elaboration.

    The import list contains the target's in full, plus the target
    itself.  (#440's [Instance/Variety] is already one of the target's
    nine, so naming it separately would double-count.) *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(* Same reason as the target's: the global [Obligation Tactic] introduces
   binders under names of its own choosing, and "o is already used" is
   what that looks like from here. *)
#[local] Obligation Tactic := idtac.

(* instrument: the refutation keyword is live *)
Fail Check probe441_absent_name.

(** ** A: why the free object cannot live in #440's Leibniz variety *)

(* A measure that reads the leftmost generator of a term, so that the
   refutation below needs no projection out of [node]'s dependent
   argument at all.  AN EARLIER REVISION JUSTIFIED IT BY SAYING THE
   INJECTION ROUTE "would produce a dependent-pair equality and want
   [Eqdep]"; measured, that is false HERE — both sides of the equation
   carry the same literal [magma_mul], so [injection] yields a
   non-dependent hypothesis and the injection proof is closed under the
   global context too.  The measure is still the more robust route,
   because it keeps working when the two operations are only
   propositionally equal, which is when [Eqdep] would genuinely be
   wanted. *)
Fixpoint first_gen (t : UA.Tree MagmaOp bool) : bool :=
  match t with
  | UA.generator _ _ b => b
  | UA.node _ _ _ k    => first_gen (k UA.Fst)
  end.

Definition sep_args (i : UA.binary) : UA.Tree MagmaOp bool :=
  match i with
  | UA.Fst => UA.generator MagmaOp bool true
  | UA.Snd => UA.generator MagmaOp bool false
  end.

(* THE THEOREM.  The term algebra over the commutative-magma signature
   does not satisfy commutativity up to Leibniz equality: [x * y] and
   [y * x] are DIFFERENT TERMS.  Hence #440's [Variety CommEq], whose
   objects are bare types with Leibniz satisfaction, has no free object
   on two generators, and the setoid carrier is forced. *)
Theorem free_magma_not_comm_leibniz :
  satisfies CommEq (UA.Free MagmaOp bool) → False.
Proof.
  intro H.
  pose proof (H comm_law sep_args) as Heq.
  apply (f_equal first_gen) in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(* n1 TYPING ("cannot satisfy constraint"): so the obvious attempt to
   place the term algebra in #440's variety is refused.  It adds
   nothing to the theorem above; it is here because a reader reaching for
   that term should meet the refusal at the point of reaching.  Note it
   refutes THAT term — the [eq_refl] satisfaction proof — and the theorem
   above is what refutes every term. *)
Fail Definition term_magma_leibniz : Variety CommEq :=
  (UA.Free MagmaOp bool; fun e args => eq_refl).

(* control: the SHAPE is inhabited — the booleans under [xorb] are a
   perfectly good object of #440's Leibniz variety, so n1 is about the
   term algebra and not about the ascription. *)

Definition BoolMagmaOp : UA.OpAlgebra MagmaOp :=
  UA.Build_OpAlgebra MagmaOp bool
    (fun (o : UA.operation MagmaOp) k => xorb (k UA.Fst) (k UA.Snd)).

Example p441_bool_in_leibniz_variety : Variety CommEq.
Proof.
  exists BoolMagmaOp.
  intros e args; destruct e; simpl.
  destruct (args UA.Fst), (args UA.Snd); reflexivity.
Defined.

(* THE QUALIFIER THE CLAIM NEEDED, in tree and cheap.  With no equations
   at all the congruence is generated by nothing, the term algebra
   satisfies the (empty) law set vacuously, and it IS an object of #440's
   Leibniz variety.  So "the free object cannot live in [Variety E]" was
   false already at the degenerate presentation, before the
   normal-form construction refuted it at a real one. *)

Definition EmptyEq : UA.EqSignature MagmaOp.
Proof.
  unshelve refine {| UA.eq := Empty_set ; UA.eq_arity := fun e => match e with end |}.
  - intros A e; destruct e.
  - intros A e; destruct e.
  - intros A B f e; destruct e.
  - intros A B f e; destruct e.
Defined.

Example free_empty_eq_leibniz : Variety EmptyEq.
Proof. exists (UA.Free MagmaOp bool); intro e; destruct e. Defined.

(** ** B: the congruence does not collapse

    Proved through the development's own universal property: map the
    free algebra into the booleans under [xor], which IS a commutative
    magma, by the identity on generators.  If the two generators were
    congruent their images would be `≈`, i.e. equal. *)

Program Definition BoolCommMagma : SetoidOpAlgebra MagmaOp := {|
  soa_obj := {| carrier := bool ; is_setoid := eq_Setoid bool |};
  soa_op  := fun (o : UA.operation MagmaOp) k => xorb (k UA.Fst) (k UA.Snd)
|}.
Next Obligation.
  intros o k1 k2 H; simpl.
  rewrite (H UA.Fst), (H UA.Snd); reflexivity.
Qed.

Program Definition BoolCommMagma_sat : ssatisfies CommEq BoolCommMagma.
Proof.
  intros e args; destruct e; simpl.
  destruct (args UA.Fst), (args UA.Snd); reflexivity.
Qed.

Definition BoolCommVariety : SVariety CommEq :=
  (BoolCommMagma; BoolCommMagma_sat).

(* The generators, as a [SetoidObject] with the discrete setoid.  Named
   [BoolGens] rather than [BoolSet], which is taken four times over
   (Instance/Sets/Quotient.v, Instance/Sets/Coequalizer.v,
   Instance/Grp/EckmannHilton.v, Test/ProbeSetsQuotient.v). *)
Definition BoolGens : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

(* No [Next Obligation] here: the identity on a discrete setoid is
   [Proper] by [Lib]'s own resolution, and adding one gets "No
   obligations remaining". *)
Definition sep_args' (i : UA.binary) : UA.Tree MagmaOp BoolGens :=
  match i with
  | UA.Fst => UA.generator MagmaOp BoolGens true
  | UA.Snd => UA.generator MagmaOp BoolGens false
  end.

Program Definition bool_generators : BoolGens ~{Sets}~> soa_obj BoolCommMagma := {|
  morphism := fun b : bool => b
|}.

Theorem free_comm_not_collapsed :
  tree_equiv CommEq BoolGens
    (UA.generator MagmaOp BoolGens true) (UA.generator MagmaOp BoolGens false) → False.
Proof.
  intro D.
  pose proof (free_alg_ext_respects CommEq BoolGens
                BoolCommVariety bool_generators _ _ D) as Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(* Non-vacuity of the congruence, so that [free_comm_not_collapsed] is a
   sharp result rather than a statement about an empty relation: the
   commutativity law DOES identify two distinct terms. *)
Example p441_congruence_identifies :
  tree_equiv CommEq BoolGens
    (UA.node MagmaOp BoolGens magma_mul sep_args')
    (UA.node MagmaOp BoolGens magma_mul (fun i => sep_args' (comm_swap i)))
  := tc_law CommEq BoolGens comm_law sep_args'.

(** ** C: CONVERSION *)

(* n2: the free algebra's carrier IS the term type, but its `≈` is the
   congruence and not Leibniz [=], so the two setoids do not convert. *)
Fail Example p441_free_setoid_is_eq :
  Tree_Setoid CommEq BoolGens = eq_Setoid (UA.Tree MagmaOp BoolGens) := eq_refl.

(* control: the CARRIER does agree on the nose *)
Example p441_free_carrier :
  carrier (soa_obj (`1 (Free_Variety CommEq BoolGens)))
    = UA.Tree MagmaOp BoolGens := eq_refl.

(* n3: the two terms n1 is about are not CONVERTIBLE.  That is weaker
   than "distinct" — non-convertibility is not disprovability — and an
   earlier revision of this comment claimed the stronger thing.  What
   establishes distinctness is [free_magma_not_comm_leibniz] above. *)
Fail Example p441_terms_convert :
  UA.node MagmaOp bool magma_mul sep_args
    = UA.node MagmaOp bool magma_mul (fun i => sep_args (comm_swap i)) := eq_refl.

(** ** D: readbacks

    The unit is the generator embedding on the nose, and the extension
    of a map along it IS Instance/Comp.v's [induced_map] — nothing is
    re-recursed. *)

Example p441_unit_is_generator (X : Sets) (x : X) :
  free_unit CommEq X x = UA.generator MagmaOp X x := eq_refl.

(* This one pins TRANSPARENCY and nothing else: [free_alg_ext]'s body IS
   the right-hand side, so it is discharged by delta and holds for as
   long as that body stands.  An earlier revision offered it as evidence
   that "nothing is re-recursed", which it is not — an independently
   written [Fixpoint] with the same clauses also converts. *)
Example p441_ext_is_induced_map (X : Sets) (A : SVariety CommEq)
  (h : X ~{Sets}~> soa_obj (`1 A)) (t : UA.Tree MagmaOp X) :
  free_alg_ext A h t = UA.induced_map MagmaOp X (soa_alg (`1 A)) h t := eq_refl.

(* This one pins the RECURSION STEP, which is what the prose was reaching
   for: the extension of a map at a node is the algebra's operation
   applied to the extensions of the arguments. *)
Example p441_ext_step (X : Sets) (A : SVariety CommEq)
  (h : X ~{Sets}~> soa_obj (`1 A)) (o : UA.operation MagmaOp)
  (k : UA.arity o → UA.Tree MagmaOp X) :
  free_alg_ext A h (UA.node MagmaOp X o k)
    = soa_op (`1 A) o (fun i => free_alg_ext A h (k i)) := eq_refl.

(* And the left adjoint's action on OBJECTS, which nothing else pinned:
   the functor built from the universal arrows really is [Free_Variety]. *)
Example p441_left_adjoint_obj (X : Sets) :
  Free_Variety_Functor CommEq X = Free_Variety CommEq X := eq_refl.

Example p441_free_op_is_node (X : Sets) (o : UA.operation MagmaOp)
  (k : UA.arity o → UA.Tree MagmaOp X) :
  soa_op (FreeSOA CommEq X) o k = UA.node MagmaOp X o k := eq_refl.

(** ** E: guard block *)

Check @SetoidOpAlgebra.
Check @soa_obj.
Check @soa_op.
Check @soa_op_respects.
Check @soa_alg.
Check @SAlgHom.
Check @salg_map.
Check @salg_respects.
Check @salg_commute.
Check @SAlgHom_Setoid.
Check @SAlg_id.
Check @SAlg_comp.
Check @SetoidAlgs.
Check @ssatisfies.
Check @SVariety_sub.
Check @SVariety.
Check @SVariety_Full.
Check @SVariety_Incl.
Check @SVariety_Forget.
Check @SVariety_Forget_Faithful.
Check @tree_equiv.
Check @tc_gen.
Check @tc_op.
Check @tc_law.
Check @tc_sym.
Check @tc_trans.
Check @tc_refl.
Check @Tree_Setoid.
Check @FreeSOA.
Check @FreeSOA_satisfies.
Check @Free_Variety.
Check @free_alg_ext.
Check @free_alg_ext_respects.
Check @free_alg_hom.
Check @free_alg_hom_unique.
Check @free_unit.
Check @FreeUA.
Check @Free_Variety_Functor.
Check @Free_Variety_adjunction.
Check @soa_prod_setoid.
Check @soa_prod.
Check @soa_prod_exl.
Check @soa_prod_exr.
Check @soa_prod_satisfies.
Check @not_equationally_definable.
Check @CommMagmaFree.
Check @CommMagmaFree_adjunction.
Check @SGroupVariety.
Check @FreeGroupOn.
Check @FreeGroup_adjunction.
Check @leibniz_soa.
Check @ring_op.
Check @RingOp.
Check rzero.
Check rone.
Check radd.
Check rmul.
Check @F2_op.
Check @F2.
Check @r_zero.
Check @r_one.
Check @r_mul.
Check @HasDivision.
Check @IsField.
Check @r_add.
Check @F2_HasDivision.
Check @F2_IsField.
Check @F2xF2_no_division.
Check @F2xF2_not_field.
Check @division_is_not_equationally_definable.
Check @fields_are_not_a_variety.
Check @Variety.
Check @CommEq.
Check @MagmaOp.
Check @BoolGens.
Check @EmptyEq.
Check @free_empty_eq_leibniz.
Check @BoolMagmaOp.
Check @BoolCommMagma.
Check @BoolCommVariety.
Check @bool_generators.
Check @first_gen.
Check @sep_args.
Check @sep_args'.
Check @p441_congruence_identifies.
Check @free_magma_not_comm_leibniz.
Check @free_comm_not_collapsed.
