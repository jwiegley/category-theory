Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.AFT.

Generalizable All Variables.

(** * Colimits of rings, from the adjoint functor theorem *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab:      https://ncatlab.org/nlab/show/Ring
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_rings
   Wikipedia: https://en.wikipedia.org/wiki/Free_product_of_associative_algebras

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7 Exercise 2 (book p. 128, PDF p. 137) asks for the coproduct of two
   rings from the adjoint functor theorem.  Mac Lane's [Rng] is the category
   of rings WITH identity, and so is this tree's: Instance/Rng.v defines
   [Rng] as Theory/Algebra/Rig.v's [Ring], unital rings and unit-preserving
   homomorphisms (the non-unital category is Instance/Rg.v's [Rg]).
   Wikipedia's "Category of rings" records that the coproduct of two rings
   exists and is, for commutative rings, the tensor product over ℤ; for
   rings in general it is a free product, which this file never describes
   element-wise.

   ** THE ISSUE'S SURVEY, MEASURED

   Issue #450 says there is "no [Rng]" (#257).  [Rng] is Instance/Rng.v,
   complete by Instance/Rng/Limit.v's [Rng_Complete], with a free ring
   obtained from [GAFT] in Instance/Rng/AFT.v.  What WAS absent, measured
   at the parent commit (e139ecfb) by [grep -rn --include='*.v'] over the
   whole tree: any [Cocartesian Rng] or [Cocartesian Ring] (pattern
   ['Cocartesian (Rng|Ring)\b'], no hit), any [HasCoequalizers Rng] (no
   hit), and any colimit of rings beyond the initial ring.  A declaration
   typed by a colimit structure on rings, the [git grep -nE] pattern
   [': *@?[A-Za-z]*(Initial|Cocartesian|Coequalizers?|Pushouts?|Cocomplete|Colimit) *[(]?(Rng|Ring|CRng)([^A-Za-z_0-9]|$)']
   at e139ecfb, hits exactly two lines: Instance/Rng.v's
   [Rng_Initial_Z], the initial ring ℤ -- the colimit of the empty
   diagram, at [Set] carriers only (NON-VACUITY, below) -- and its alias
   [roster_Rng_Initial] in Instance/Roster.v.  (Instrument check: with
   [Grp] in place of the ring names the same pattern finds
   Instance/Grp.v's [Grp_Initial] and Instance/Grp/Pushout.v's
   [Grp_HasPushouts] and [Grp_Cocartesian].)

   NAMES.  The issue suggests a module Instance/Rng/Coproduct.v, not
   used, and its verification block runs [Print Assumptions
   Rng_coproduct]; no constant of that name exists (measured: [grep -rnw
   Rng_coproduct] over the [.v] files finds only this paragraph).  The
   coproduct of two rings is this file's [Rng_Cocartesian_via_GAFT].

   ** THE ROUTE

   Exactly Instance/Grp/Colimit.v's, whose header gives the argument in
   full: for each shape J the UNIVERSES section below allows (homs at the
   carrier universe), Adjunction/GAFT.v's [GAFT] is applied to
   the diagonal Δ[J] : Rng ⟶ [J, Rng] ([Rng_colim_via_GAFT]), with
   [Rng_Complete], Adjunction/Diagonal/Limit.v's [Diagonal_continuous]
   through [Continuous_PreservesImageLimit], and a solution set at each
   diagram ([Diagonal_Rng_solution_set]); [Diagonal_left_adjoint_HasColimits]
   then reads the colimits off, and [Rng_Cocomplete_via_GAFT] assembles
   them.

   The solution set indexes [Prop]-valued congruences on
   Instance/Rng/AFT.v's term model [FRTerm] over the free abelian group
   [RGenAb] on the disjoint union [RGen] = Σ j, carrier (D j) (Leibniz
   equality).  A member ([RDCongIdx]) is a relation with a proof of
   [IsRngCoconeCong]: a ring congruence ([IsRngCongruence], Instance/Rng/
   AFT.v) that identifies the letters of `≈`-equal elements ([rcc_resp]),
   makes each insertion preserve zero, addition, one and multiplication
   ([rcc_zero], [rcc_add], [rcc_one], [rcc_mul]) and identifies each
   element with its image under the arrows of the diagram ([rcc_nat]).
   Those clauses make the insertions ring homomorphisms into the quotient
   [RDQ i] ([rdq_leg]; Theory/Algebra/Rig.v's [RigHom] carries all four
   laws as fields, and no smart constructor deriving one of them exists --
   [git grep -n "Build_RigHom'"] at the parent commit e139ecfb returns
   nothing (after #450 its one hit is this sentence) -- whereas
   the group case derives the unit law) and a cocone ([rdq_arr]).
   The covering is the kernel [rng_ker] of the cocone's extension to the
   term model ([rhab], through Instance/Ab/Free.v's [free_ab_extend]),
   which is a cocone congruence ([rker_cocone]) because the target carries
   [rig_prop]; the covering equation holds by [reflexivity], the term
   model's evaluation of an inserted letter computing to the leg.

   [rker_cocone] ENDS IN [Defined], AND MUST, for the reason
   Instance/Grp/Colimit.v gives for [dker_cocone]: measured by closing it
   with [Qed] in a copy of this file, [Diagonal_Rng_solution_set] is then
   refused with "The term "rng_ker_med (rhab c h)" has type "RigHom (QRng
   (rng_ker (rhab c h)) (rng_ker_is_cong (rhab c h))) c" while it is
   expected to have type "RDQ (rker_idx c h) ~{ Rng }~> c"" (universe
   instances elided).

   The finite colimits come from Structure/Limit/Finite.v's bridges, as in
   Instance/Grp/Colimit.v: [Rng_Cocartesian_via_GAFT] is the coproduct of
   rings Mac Lane's Exercise 2 asks for, [Rng_HasCoequalizers_via_GAFT] the
   coequalizers and [Rng_Initial_via_GAFT] the initial ring.  Read off
   the bridges' bodies (Instance/Grp/Colimit.v's FINITE COLIMITS gives
   the detail), the coproduct is the AFT pushout over the AFT initial
   object, the coequalizer is assembled from AFT pushouts and the AFT
   initial object, and the initial ring is the AFT colimit of the empty
   diagram; each of those is itself a [GAFT] colimit at a diagonal.  The
   direct reading at a discrete two-object shape or at the walking
   parallel pair is not the one used.  Nothing in
   this file is registered as an [Instance], and no other [Cocartesian Rng]
   exists in tree to be picked up by resolution.

   ** A CONTRAST WITH GROUPS

   Instance/Grp/Colimit.v proves the injections of a coproduct of groups
   monic; nothing like it is claimed here, and nothing like it holds: in
   the coproduct of ℤ/2 and ℤ/3 the common unit satisfies 2 = 0 and 3 = 0,
   hence 1 = 0, so the coproduct is the zero ring and neither injection is
   monic.  [Rng] has no zero object -- the zero ring is terminal
   (Instance/Rng.v's [Rng_Terminal_zero]) but not initial, there being no
   homomorphism from it to ℤ (Instance/Rg.v's [Rng_terminal_not_initial])
   -- and a zero object is what the group argument,
   Theory/Subobject/Disjoint.v's, needs.  The ℤ/2 ⊔ ℤ/3 computation is a
   remark, not a theorem in tree.

   ** STRENGTHS

   Nothing about a colimit object computes: [GAFT] ends in [Qed], so each
   colimit is an existence result, and every agreement with another
   construction would be an isomorphism.  No such agreement is stated.

   ** UNIVERSES, MEASURED

   By [About] under [Set Printing Universes], dropping bounds on stdlib
   globals: [Diagonal_Rng_solution_set@{u u0 u1 u2 u3}] takes
   J : Category@{u u0 u0} and D : J ⟶ Rng@{u1 u0} and returns
   [SolutionSet@{u2 u1 u1 u0}] with [u0 <= u2] and [Set < u2] on the
   index, and no [Set] bound on the carrier [u0]; [Rng_colim_via_GAFT]
   takes J : Category@{u2 u3 u3} with [u2 <= u3];
   [Rng_Cocomplete_via_GAFT] is [Cocomplete@{u u0 u u1}] with [Set < u],
   [u < u1] and [u0 <= u].  The side condition is [Set < carrier], as for
   [free_ring_via_GAFT], and it is [GAFT]'s, not the solution set's:
   [GAFT] takes its solution set's index AT the carrier universe, and
   this index sits strictly above [Set].  Measured in a scratch file
   under [Monomorphic Constraint Set < gu], at J : Category@{Set Set Set}
   and D : J ⟶ Rng@{gu Set}: [@Diagonal_Rng_solution_set J D] is
   accepted, and [Rng_colim_via_GAFT@{gu _ _ Set Set} J] is refused with
   "Universe inconsistency. Cannot enforce Set < Set because Set = Set."
   Test/ProbeAlgColimit450.v's N5 pins the refusal, with the solution set
   and [GAFT] applied to every argument but it both accepted at the same
   J as its controls.
   [Rng_Cocartesian_via_GAFT] and [Rng_HasCoequalizers_via_GAFT] add the
   strict stdlib bound carrier < [eq_rect_r.u0], inherited from
   Structure/Limit/Finite.v's [FinitelyComplete_HasPullbacks];
   [Rng_Initial_via_GAFT] does not carry it.

   ** NON-VACUITY, AND WHY THE INITIAL RING IS NOT COMPARED

   No nontrivial ring above [Set] is exhibited here.  The natural witness
   would compare [Rng_Initial_via_GAFT] with Instance/Rng.v's ℤ, but
   [About] reads [Rng_Initial_Z@{…} : @Initial Rng@{u Set}]: ℤ is initial
   only at [Set] carriers, while [Rng_colim_via_GAFT] and every colimit
   read off it need [Set < carrier] (UNIVERSES, above: the requirement is
   [GAFT]'s, the solution set itself elaborating at [Set] carriers), so
   the two cannot be stated together.  That is the same kind of donor
   pin #450 lifted for [Grp]'s zero object and [Z2] in Instance/Grp.v; it
   is not lifted for ℤ here.  Test/ProbeAlgColimit450.v's N13 pins the
   refusal of [initial_unique Rng_Initial_via_GAFT Rng_Initial_Z]; it is
   expected to turn over if ℤ's pin is ever lifted, and this paragraph
   then needs a correction.

   ** AXIOMS

   Every constant of this file reports "Closed under the global context".

   ** NOT DELIVERED

   No element-level description of the coproduct (no free product of
   rings, no normal form); no comparison with the tensor product of
   commutative rings; no comparison of the initial ring with ℤ (above);
   no statement about the injections; no explicit coequalizer as a
   quotient by a two-sided ideal (Instance/Rng/Quotient.v's quotient is not
   connected to [Rng_HasCoequalizers_via_GAFT]); nothing registered as an
   [Instance]. *)

(** ** The solution set at a diagram *)

Section RngDiagonalSolutionSet.

Context {J : Category}.
Context (D : J ⟶ Rng).

(* The generators: the disjoint union of the carriers, with Leibniz
   equality, and the free abelian group on them. *)
Definition RGen : SetoidObject :=
  {| carrier := { j : obj[J] & carrier (rig_setoid (D j)) };
     is_setoid := eq_Setoid _ |}.

Definition RGenAb : AbObject := FreeAbObject RGen.

Definition rins (j : J) (a : carrier (rig_setoid (D j))) : FRTerm RGenAb :=
  @fr_gen RGenAb (@fa_gen RGen (j; a)).

(* A congruence on the term model that makes the insertions a cocone of
   ring homomorphisms. *)
Record IsRngCoconeCong (Rq : FRTerm RGenAb → FRTerm RGenAb → Prop) : Prop := {
  rcc_rng  : IsRngCongruence Rq;
  rcc_resp : ∀ j a b, a ≈ b → Rq (rins j a) (rins j b);
  rcc_zero : ∀ j, Rq (rins j (rig_zero (D j))) (@fr_zero RGenAb);
  rcc_add  : ∀ j a b, Rq (rins j (rig_add (D j) a b))
                         (@fr_plus RGenAb (rins j a) (rins j b));
  rcc_one  : ∀ j, Rq (rins j (rig_one (D j))) (@fr_one RGenAb);
  rcc_mul  : ∀ j a b, Rq (rins j (rig_mul (D j) a b))
                         (@fr_mul RGenAb (rins j a) (rins j b));
  rcc_nat  : ∀ j k (f : j ~{J}~> k) a,
               Rq (rins k (rig_map (fmap[D] f) a)) (rins j a)
}.

Definition RDCongIdx : Type :=
  { Rq : FRTerm RGenAb → FRTerm RGenAb → Prop & IsRngCoconeCong Rq }.

Definition RDQ (i : RDCongIdx) : obj[Rng] := QRng (`1 i) (rcc_rng _ (`2 i)).

Definition rdq_leg (i : RDCongIdx) (j : J) : D j ~{Rng}~> RDQ i.
Proof.
  unshelve refine (@Build_RigHom (D j) (RDQ i)
                     {| morphism := rins j |} _ _ _ _).
  - intros a b Hab; exact (rcc_resp _ (`2 i) j a b Hab).
  - exact (rcc_zero _ (`2 i) j).
  - intros a b; exact (rcc_add _ (`2 i) j a b).
  - exact (rcc_one _ (`2 i) j).
  - intros a b; exact (rcc_mul _ (`2 i) j a b).
Defined.

Definition rdq_arr (i : RDCongIdx) :
  D ~{[J, Rng]}~> fobj[@Diagonal Rng J] (RDQ i).
Proof.
  unshelve refine (@Build_Transform' J Rng D (fobj[@Diagonal Rng J] (RDQ i))
                     (fun j => rdq_leg i j) _).
  intros j k f a; simpl.
  apply (rc_sym _ _ (rcc_rng _ (`2 i))).
  exact (rcc_nat _ (`2 i) j k f a).
Defined.

(* The covering: the kernel of a cocone's extension to the term model. *)
Section Cover.

Context (c : Rng) (h : D ~{[J, Rng]}~> fobj[@Diagonal Rng J] c).

Definition rflat : RGen ~{Sets}~> Ab_Forget (Rng_Forget_Ab c).
Proof using h.
  unshelve refine {| morphism := fun p => rig_map (transform[h] (`1 p)) (`2 p) |}.
  intros p q Hpq; simpl in Hpq; subst; reflexivity.
Defined.

Definition rhab : RGenAb ~{Ab}~> Rng_Forget_Ab c :=
  @free_ab_extend RGen (Rng_Forget_Ab c) rflat.

(* Transparent on purpose: see the header. *)
Lemma rker_cocone : IsRngCoconeCong (rng_ker rhab).
Proof using h.
  constructor.
  - exact (rng_ker_is_cong rhab).
  - intros j a b Hab; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    now rewrite Hab.
  - intros j; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_zero (transform[h] j)).
  - intros j a b; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_add (transform[h] j)).
  - intros j; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_one (transform[h] j)).
  - intros j a b; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_mul (transform[h] j)).
  - intros j k f a; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    pose proof (@naturality_sym _ _ _ _ h j k f a) as Hn; simpl in Hn.
    rewrite Hn; reflexivity.
Defined.

Definition rker_idx : RDCongIdx := (rng_ker rhab; rker_cocone).

End Cover.

Definition Diagonal_Rng_solution_set : SolutionSet (@Diagonal Rng J) D.
Proof.
  unshelve refine (@Build_SolutionSet Rng ([J, Rng]) (@Diagonal Rng J) D
                     RDCongIdx RDQ rdq_arr _).
  intros c h.
  exists (rker_idx c h).
  exists (rng_ker_med (rhab c h)).
  intros j a; simpl.
  reflexivity.
Defined.

End RngDiagonalSolutionSet.

(** ** Every colimit of rings within the shape discipline *)

Definition Rng_colim_via_GAFT (J : Category) :
  { K : [J, Rng] ⟶ Rng & K ⊣ @Diagonal Rng J } :=
  GAFT (@Diagonal Rng J) Rng_Complete
       (Continuous_PreservesImageLimit Diagonal_continuous)
       (@Diagonal_Rng_solution_set J).

Definition Rng_Cocomplete_via_GAFT : @Cocomplete Rng :=
  fun J F => Diagonal_left_adjoint_HasColimits (projT2 (Rng_colim_via_GAFT J)) F.

(** ** The coproduct of rings, coequalizers and the initial ring *)

Definition Rng_FinitelyCocomplete_via_GAFT : @FinitelyCocomplete Rng :=
  Cocomplete_FinitelyCocomplete Rng_Cocomplete_via_GAFT.

(* Mac Lane §V.7 Exercise 2. *)
Definition Rng_Cocartesian_via_GAFT : @Cocartesian Rng :=
  FinitelyComplete_Cartesian
    (FinitelyCocomplete_FinitelyComplete_op Rng_FinitelyCocomplete_via_GAFT).

Definition Rng_HasCoequalizers_via_GAFT : HasCoequalizers Rng :=
  HasCoequalizers_of_HasEqualizers_op
    (FinitelyComplete_HasEqualizers
       (FinitelyCocomplete_FinitelyComplete_op Rng_FinitelyCocomplete_via_GAFT)).

Definition Rng_Initial_via_GAFT : @Initial Rng :=
  FinitelyCocomplete_Initial Rng_FinitelyCocomplete_via_GAFT.
