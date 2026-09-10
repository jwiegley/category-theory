Require Import Coq.Lists.List.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Adjunction.Continuity.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Closed.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.FdVect.DoubleDual.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(** * The dual functor on vector spaces has no right adjoint

    Mac Lane §V.5 Exercise 2 (book p. 120, `maclane:V.5:ex2`, #433): the
    dualization functor D : Vct^op ⟶ Vct, adjoint to itself on the right,
    has no right adjoint, so it is not the left adjoint of its opposite.
    The tree has TWO readings of D over Instance/FdVect.v:223's [Vct_F F :=
    RMod (field_ring F)]: Instance/FdVect/DoubleDual.v:305's [Dual F], on
    ALL F-modules with precomposition on the nose ([dual_precompose] :288),
    and Structure/Monoidal/StarAutonomous.v:229's dual-object functor
    [dual] read at the line through Instance/Mod/Closed.v:747's
    [RMod_SymMonClosed] — here [VctDual359], the functor the issue names,
    since Structure/Monoidal/Dual.v (#359) proves it adjoint to itself on
    the right ([dual_self_adjoint_on_the_right] :441).  The exercise is
    proved for BOTH: for [Dual F] directly ([dual_functor_no_right_adjoint]
    and its corollary [dual_not_left_adjoint_of_op]) and for [VctDual359]
    by transport along the natural isomorphism [dual_iso359 : Dual F ≈
    VctDual359] ([dual359_no_right_adjoint], [dual359_not_left_adjoint_of_op]).
    The file sits beside [Dual], where the issue's placement clause puts it.

    STALE PREMISES.  The issue's "Current state" says the tree has no
    category of vector spaces and no dual functor: FALSE twice — [Vct_F] and
    [Dual] above, with [DualMod] :267, [eta] :341 and [double_dual_natural]
    :364.  It calls the dual-object functor "#359's": [dual] is
    StarAutonomous.v's (2026-07-10), and #359 added the self-adjunction.
    The two readings are different [Program] records, naturally isomorphic
    but NOT convertible (probe N1), not even objectwise (N5: the carriers of
    [VctDual359 x] and [Dual F x] coincide at [eq_refl], the packed modules
    do not — [HomMod]'s and [DualMod]'s proof fields are different opaque
    constants).  DoubleDual.v:104-109 said [Vct_F F] "lacked" a monoidal
    structure — stale since Instance/Mod/Monoidal.v and Instance/Mod/
    Closed.v (2026-08-31); repaired in place, line-neutrally.  And the
    exercise is FALSE over [FdVect F]: DoubleDual.v:609's [DualFd] is
    pointwise invertible by [double_dual_iso], mathematically an
    equivalence with adjoints on both sides (not formalized as such) — the
    statement needs infinite dimension, which is why everything here runs
    in [Vct_F F].

    THE MATHEMATICS AND ITS BOUNDARY.  A right adjoint of D would make D a
    left adjoint, hence carry colimit cocones to colimit cocones
    (Adjunction/Continuity.v:246 [left_adjoint_PreservesColimitCocone]).
    D's source is Vct^op, so a colimit there is a PRODUCT in Vct: Mac
    Lane's is the countable power F^ℕ, whose dual (F^ℕ)* would have to be
    the direct sum ⊕_ℕ F of the coordinate functionals if D preserved it.
    (The issue's own sentence, "the dual of a direct sum is a product",
    describes the OTHER direction: D does carry the direct sum ⊕_ℕ F, a
    colimit of Vct, to a product — that is the positive half below, not
    the obstruction.)  The tree has no indexed coproducts in [RMod R], and
    none is needed: the power is [PowLine := ProdMod (fun _ => VctLine)] of
    Instance/Mod/Product.v (new, #433) with coordinate projections
    [vct_coord n], packaged as [PowCocone : Cocone LineDiagram] over the
    constant discrete diagram [LineDiagram : DiscreteCat nat ⟶ Vct^op] and
    proved colimiting, [PowCocone_IsColimitCocone], by [prod_tuple] — the
    CONCRETE colimit the issue's reviewer asks for.  Its image under D is
    the cocone of coordinate functionals [D (vct_coord n) : D VctLine ~>
    D PowLine], ψ ↦ ψ ∘ coord n.  If that image were colimiting, the two
    mediators to the competing cocone [ZeroCocone] (apex: the quotient
    [SpanQuot] of D PowLine by the span [SpanCoords] of the coordinate
    functionals; legs: the quotient map [span_quot] after each
    D (vct_coord n)) — the quotient map itself and the zero map
    [vct_zero_hom], both compatible because every ψ ∘ coord n lies in the
    span ([dual_coord_in_span], the ONE place field commutativity is spent)
    — would coincide, so every functional on F^ℕ would lie in the span.
    Mac Lane's own sentence is that some functional does not; that is
    [CoordSpanProper : Type], and [dual_not_PreservesColimitCocone (H :
    CoordSpanProper)] closes the argument through Instance/Mod/Quotient.v's
    [mquot_proj_kills] and [mquot_proj_kernel]; [dual_functor_no_right_adjoint]
    is the exercise and [dual_not_left_adjoint_of_op] its corollary, both
    one-line compositions.

    WHY CONDITIONAL — analysis, not formalized.  Classically
    [CoordSpanProper F] holds for every field (Erdős–Kaplansky: the dual of
    an infinite-dimensional space has dimension |F|^dim, so countably many
    coordinates cannot span it), but it is NOT provable without choice: in
    a model of ZF + DC where every set of reals has the Baire property
    (Solovay; Shelah), every additive map ℚ^ℕ → ℚ is continuous by Pettis'
    automatic-continuity theorem, and a continuous functional on ℚ^ℕ with
    ℚ discrete vanishes on a basic neighbourhood of 0, so it is a finite
    combination of coordinates.  For F = ℚ the premise is therefore
    independent of ZF + DC, and no axiom-free witness can be built in this
    tree; docs/INHABITATION.md records the row as one that will never get a
    constructive inhabitant, unlike the "awaiting a model" rows.  Finite
    shapes give no obstruction (finite products of modules are biproducts,
    which D carries to biproducts — analysis again), so the countability is
    load-bearing here, where in Instance/Ab/FreeNotContinuous.v (#430) it
    was inert.

    THE UNCONDITIONAL HALF.  [vct_transpose f := fmap[Dual F] f ∘ eta F x]
    turns a ~> D x into x ~> D a and is an involution
    ([vct_transpose_invol], [reflexivity] after [simpl]); its
    respectfulness, the two round trips and the four naturality squares are
    closed by the tree's default tactic: [dual_vct_AdjointOnTheRight :
    AdjointOnTheRight (Dual F) (Dual F)] (Adjunction/Right.v's class),
    [dual_vct_Adjunction : (Dual F)^op ⊣ Dual F] through
    [Adjunction_of_AdjointOnTheRight], and Mac Lane's contrast
    [dual_vct_Continuous : ContinuousFunctor (Dual F)] by RAPL
    (Adjunction/Continuity.v:209 [right_adjoint_Continuous]).  The
    direction matters and the probe pins it (N3): the self-adjunction runs
    [(Dual F)^op ⊣ Dual F]; the exercise's [Dual F ⊣ (Dual F)^op] is
    exactly the ascription that is refused.

    THE FUNCTOR THE ISSUE NAMES.  [VctDual359 x] is the internal hom
    [HomMod x VctLine]; its carrier, zero, sum and scalar action coincide
    with [DualMod]'s at [eq_refl], so the identity on functionals is a
    module homomorphism each way ([to359], [from359], packaged as
    [iso359]).  [dual]'s arrow action is the closed transpose of
    evaluation, [dcur (eval' ∘ (id ⨂ f))], an OPAQUE mediator
    (StarAutonomous.v's [dcur] is the [unique_obj] of [ump_exponents], which
    at RMod is the `Qed` theorem [ump_exponents_Mod]), so it does not compute;
    [dual359_fmap_pre] identifies it with precomposition by the uniqueness
    clause [dcur_uniq], checked on the tensor's generators through
    Instance/Mod/Tensor.v's [tensor_hom_ext] by [reflexivity].  That gives
    [dual_iso359 : Dual F ≈ VctDual359] in [Fun]'s [≈] (Theory/Functor.v's
    [Functor_Setoid], a bundled natural isomorphism), and
    Theory/Adjunction.v's [adjunction_along_left_iso] (#431) turns any
    [VctDual359 ⊣ Rt] into [Dual F ⊣ Rt], so [dual359_no_right_adjoint]
    and [dual359_not_left_adjoint_of_op] follow from the refutation above.

    UNIVERSES ([About] under `Set Printing Universes`, all 41 heads).  No
    [Set] anywhere: the shape is Structure/Limit/Comparison.v:535's
    annotated [DiscreteCat_Functor'], because Instance/Discrete.v:59's
    unannotated [DiscreteCat_Functor] pins the shape's hom level to [Set]
    and no cocone in Vct^op can share it (probe N4, "Cannot enforce Set =
    …").  Every head but [vct_zero_hom] carries the two equations `u0 = u`,
    `u1 = u` identifying the three [FieldObject] levels — they arrive with
    [VctLine := Ring_RMod (field_ring F)] and with [Dual@{u u u _}] alike,
    and [vct_zero_hom], stated over bare objects of Vct, carries none.
    Strict constraints are of one kind, the field levels below the
    category's object level (`u < u2` and its renamings; the four
    list-shaped heads [span_sum], [span_sum_app], [span_sum_scale] and
    [dual_coord_in_span] state it for all three identified levels), plus
    [dual_vct_Continuous]'s shape level (`u5 < u2`) and [vct_zero_hom]'s
    second object level (`u < u3`).  Stdlib caps by FIRST carrier in file
    order: `Basics.compose` and `ID` at [VctLine] (inherited from
    Instance/FdVect.v), `prod_rect` at [vct_zero_hom], `list_rect` and
    `app` at [span_sum_app], `ListDef.Map` and `projections` at
    [span_sum_scale], `JMeq`, `eq`, `eq_ind`, `eq_ind_r`, `eq_rect_r`,
    `EqdepFacts.eq_sigT_sig_eq` and `Logic_lemmas.equality` at
    [LineDiagram] (inherited from [DiscreteCat_Functor']; the shape's hom
    is [eq]), and Specif's `Projections` at [CoordSpanProper] (a sigma
    type).

    MEASURED.  41 `.glob` heads (34 `def`, 7 `prf`) and 17 [Program]
    obligations (8 closed by hand under [Obligation Tactic := idtac] for
    [vct_zero_hom] and [SpanCoords], 9 by [cat_simpl] for the four records
    [vct_transpose_morphism], [vct_aor], [dual_vct_AdjointOnTheRight] and
    [iso359]), all 58 "Closed under the global context", zero `Axioms:`
    lines; the `make print-assumptions` gate carries the 41 heads.  Six
    `Defined`, each LOAD-BEARING (flipped to `Qed` one at a time in a copy
    of the whole file: [op_discrete_cone] stops [PowCocone_IsColimitCocone],
    [ZeroCocone] stops [dual_not_PreservesColimitCocone],
    [PowCocone_IsColimitCocone] stops the readback
    [pow_cocone_mediator_component], [to359] and [from359] stop
    [dual_iso359]'s proof, and [dual_iso359] stops the readback
    [iso359_to_component] — the two readbacks exist for that reason);
    fourteen `Qed`.  Closure 103 files excluding self (Adjunction/Right.v
    18 at the margin, Structure/Limit/Comparison.v 5, Instance/Mod/Closed.v
    2, Instance/Mod/Quotient.v 2, DoubleDual.v 1, Instance/Mod/Product.v 1,
    the other nineteen `Require`s 0; none of the 25 is droppable — each
    was removed in a copy of the file and the copy stopped compiling).
    Zero name collisions for the 41 names (`grep -rlw --include='*.v'`;
    DoubleDual.v's header mentions [dual_iso359] by design; [SpanQuot],
    [span_quot] and Product.v's [modprod_*] were chosen because
    Construction/PROP/Presentation.v:185 owns [quot] and Lib/Datatypes.v:139
    owns [prod_setoid]).  Test/ProbeDualNoRightAdjoint433.v mirrors the
    `Require` list plus Structure/Monoidal/Dual.v (the #359 control) and
    Structure/Limit/Product.v (the indexed-product readback) and carries 6
    refutation commands = 1 instrument + N1, N5 CONVERSION ([VctDual359 F =
    Dual F] at [eq_refl]: "has type VctDual359 F = VctDual359 F while it is
    expected to have type VctDual359 F = Dual F"; objectwise the same, with
    the carriers accepted beside it) + N2-N3 TYPING (the unconditional
    [∀ Rt, Dual F ⊣ Rt → False] does not ascribe; the exercise's direction
    of the self-adjunction is refused) + N4 UNIVERSE, each stripped one at
    a time in a copy of the whole file beside its accepted control; seven
    `eq_refl` readbacks; guard coverage 25/19 with six exhaustive
    exceptions (identifier tokens inside the six refutation commands /
    also named outside them, comments stripped; the exceptions are the
    refutation keyword itself, `fun`, `obj`, the two refuted Examples' own
    names and the instrument's absent name); rename-simulated 16 library
    names — [VctDual359], [Dual],
    [dual_functor_no_right_adjoint], [dual_vct_Adjunction],
    [Opposite_Functor], [Cocone], [DiscreteCat_Functor], [VctLine],
    [LineDiagram], [CoordSpanProper], [eq_refl], [False], [nat], [Vct_F],
    [carrier], [cmon_setoid] — every first break on a positive line.
    `make todo` grows by the 6 refutation lines only (2266 → 2272 over
    64b94901), so the issue's "adds no new hits" box is not met as written
    (disclosed, as in #430); the Coq 8.19 and 8.20 boxes are checked by nix
    source builds of the committed revision, which the PR records.

    NOT DELIVERED: the unconditional refutation (impossible without a
    choice principle, above); the [HasIndexedProducts (RMod R)] instance
    and indexed coproducts ⊕_I (Product.v's header); the isomorphism of the
    two duals in any form other than [Functor_Setoid]'s (no [⟹] pair, no
    [≅] in a functor category — the bundled form is what
    [adjunction_along_left_iso] consumes); a self-adjunction of
    [VctDual359] of this file's own (#359's is the probe's control);
    anything over [FdVect F], where the exercise is false; no edit to
    Instance/FdVect.v, Instance/Mod.v, Instance/Mod/Quotient.v,
    Instance/Mod/Closed.v, Structure/Monoidal/StarAutonomous.v,
    Structure/Monoidal/Dual.v, Structure/Limit/Comparison.v or
    Adjunction/Continuity.v. *)

#[local] Obligation Tactic := idtac.

Import ListNotations.

Section DualNoRightAdjoint.

Context (F : FieldObject).

Notation Vct := (Vct_F F).

(** ** The line, its countable power and the coordinate functionals *)

Definition VctLine : Vct := Ring_RMod (field_ring F).

Definition PowLine : Vct := ProdMod (fun _ : nat => VctLine).

Definition vct_coord (n : nat) : PowLine ~{Vct}~> VctLine :=
  prod_proj (fun _ : nat => VctLine) n.

Notation DP := (DualMod F PowLine).

(* The zero homomorphism between two vector spaces. *)
Program Definition vct_zero_hom (M N : Vct) : M ~{Vct}~> N := {|
  rm_hom := {| cmon_map := {| morphism := fun _ => cmon_zero N |} |}
|}.
Next Obligation. intros M N a b _; reflexivity. Qed.
Next Obligation. intros M N; reflexivity. Qed.
Next Obligation. intros M N a b; simpl; symmetry; apply cmon_plus_zero_l. Qed.
Next Obligation. intros M N r m; simpl; symmetry; apply rm_smul_zero_r. Qed.

(** ** The span of the coordinate functionals inside the dual of the power *)

(* A finite formal combination of coordinate functionals, evaluated. *)
Fixpoint span_sum (p : list (nat * carrier (cmon_setoid VctLine)))
  : carrier (cmon_setoid DP) :=
  match p with
  | nil => cmon_zero DP
  | (n, c) :: q => cmon_plus DP (rm_smul DP c (vct_coord n)) (span_sum q)
  end.

Lemma span_sum_app (p q : list (nat * carrier (cmon_setoid VctLine))) :
  span_sum (p ++ q) ≈ cmon_plus DP (span_sum p) (span_sum q).
Proof.
  intro v.
  induction p as [|[n c] p IH]; simpl.
  - symmetry; apply rig_add_zero_l.
  - rewrite IH; symmetry; apply rig_add_assoc.
Qed.

Lemma span_sum_scale (r : carrier (cmon_setoid VctLine))
  (p : list (nat * carrier (cmon_setoid VctLine))) :
  rm_smul DP r (span_sum p)
    ≈ span_sum
        (map (fun nc => (fst nc, rig_mul (ring_rig (field_ring F)) r (snd nc)))
             p).
Proof.
  intro v.
  induction p as [|[n c] p IH]; simpl.
  - apply rig_mul_zero_r.
  - rewrite rig_distr_l, IH.
    apply rig_add_respects; [| reflexivity].
    symmetry; apply rig_mul_assoc.
Qed.

(* The submodule of [DP] spanned by the coordinates: the functionals that
   ARE finite linear combinations of coordinate projections. *)
Program Definition SpanCoords : Submodule DP := {|
  smod_mem := fun phi => { p : list (nat * carrier (cmon_setoid VctLine))
                         & phi ≈ span_sum p }
|}.
Next Obligation.
  intros a b Hab [p Hp]; exists p; now rewrite <- Hab.
Qed.
Next Obligation. exists nil; simpl; reflexivity. Qed.
Next Obligation.
  intros a b [p Hp] [q Hq]; exists (p ++ q).
  rewrite span_sum_app, Hp, Hq; reflexivity.
Qed.
Next Obligation.
  intros r a [p Hp].
  exists (map (fun nc => (fst nc, rig_mul (ring_rig (field_ring F)) r (snd nc)))
              p).
  rewrite Hp; apply span_sum_scale.
Qed.

(* Every functional of the form [ψ ∘ coord n] lies in the span — the one
   place field commutativity is spent. *)
Lemma dual_coord_in_span (n : nat)
  (psi : carrier (cmon_setoid (DualMod F VctLine))) :
  smod_mem SpanCoords (cmon_map (rm_hom (fmap[Dual F] (vct_coord n))) psi).
Proof.
  exists [(n, cmon_map (rm_hom psi) (rig_one (ring_rig (field_ring F))))].
  intro v; simpl.
  rewrite rig_add_zero_r.
  transitivity (cmon_map (rm_hom psi)
                  (rm_smul VctLine (v n) (rig_one (ring_rig (field_ring F))))).
  - apply (proper_morphism (cmon_map (rm_hom psi))).
    simpl; symmetry; apply rig_mul_one_r.
  - rewrite (rm_map_smul psi (v n)).
    apply field_comm.
Qed.

(** ** The concrete colimit: the countable power, as a cocone in Vct^op *)

Definition LineDiagram : DiscreteCat nat ⟶ Vct^op :=
  DiscreteCat_Functor' (fun _ : nat => VctLine : obj[Vct^op]).

(* A family of maps out of an apex in Vct is a cocone over [LineDiagram]
   in [Vct^op]; the coherence over a discrete shape is [fmap_id]. *)
Definition op_discrete_cone (c : Vct) (pi : ∀ n : nat, c ~{Vct}~> VctLine) :
  Cocone LineDiagram.
Proof.
  unshelve refine (@Build_Cone ((DiscreteCat nat)^op) ((Vct^op)^op)
                     (LineDiagram^op) c
                     (@Build_ACone ((DiscreteCat nat)^op) ((Vct^op)^op) c
                        (LineDiagram^op) pi _)).
  intros x y e; destruct e.
  change (@eq_refl nat y) with (@id ((DiscreteCat nat)^op) y).
  rewrite fmap_id.
  apply id_left.
Defined.

Definition PowCocone : Cocone LineDiagram := op_discrete_cone PowLine vct_coord.

(* The power is the colimit of the constant diagram in [Vct^op]: the
   product's universal property, read backwards. *)
Lemma PowCocone_IsColimitCocone : IsColimitCocone PowCocone.
Proof.
  intro M.
  unshelve refine {| unique_obj := _ |}.
  - exact (prod_tuple (fun _ : nat => VctLine)
             (fun n => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) n)).
  - intros n z; reflexivity.
  - intros u Hu z n; symmetry; apply (Hu n z).
Defined.

(** ** The obstruction hypothesis, in Mac Lane's own words *)

(* Some functional on [F^ℕ] is NOT a finite linear combination of the
   coordinate projections.  Classically true (Erdős–Kaplansky); not
   provable in ZF + DC, hence a hypothesis — see the header. *)
Definition CoordSpanProper : Type :=
  { phi : carrier (cmon_setoid DP) & smod_mem SpanCoords phi → False }.

(** ** The refutation *)

Definition SpanQuot : Vct := QuotientMod SpanCoords.

Definition span_quot : Dual F PowLine ~{Vct}~> SpanQuot :=
  mquot_proj SpanCoords.

(* The competing cocone under the image diagram: the quotient by the span,
   with the composite legs. *)
Definition ZeroCocone : Cocone (Dual F ◯ LineDiagram).
Proof.
  unshelve refine (@Build_Cone ((DiscreteCat nat)^op) (Vct^op)
                     ((Dual F ◯ LineDiagram)^op) SpanQuot
                     (@Build_ACone ((DiscreteCat nat)^op) (Vct^op) SpanQuot
                        ((Dual F ◯ LineDiagram)^op)
                        (fun n => span_quot ∘ fmap[Dual F] (vct_coord n)) _)).
  intros x y e; destruct e.
  change (@eq_refl nat y) with (@id ((DiscreteCat nat)^op) y).
  rewrite fmap_id.
  apply id_left.
Defined.

(* If [Dual F] preserved the colimit, the image cocone would be colimiting,
   and two mediators to [ZeroCocone] — the quotient map and the zero map —
   would coincide; then every functional lies in the span. *)
Theorem dual_not_PreservesColimitCocone (H : CoordSpanProper) :
  PreservesColimitCocone LineDiagram (Dual F) → False.
Proof.
  intro P.
  destruct H as [phi Hphi].
  pose proof (P PowCocone PowCocone_IsColimitCocone) as HC.
  destruct (HC ZeroCocone) as [w Hw Huniq].
  assert (Hq : w ≈ span_quot) by (apply Huniq; intros n psi; reflexivity).
  assert (Hz : w ≈ vct_zero_hom (Dual F PowLine) SpanQuot).
  { apply Huniq; intros n psi.
    symmetry.
    exact (mquot_proj_kills SpanCoords _ (dual_coord_in_span n psi)). }
  apply Hphi.
  apply (fst (mquot_proj_kernel SpanCoords phi)).
  transitivity (cmon_map (rm_hom w) phi).
  - symmetry; exact (Hq phi).
  - exact (Hz phi).
Qed.

(* Mac Lane §V.5 Exercise 2: a right adjoint of [Dual F] would make it a
   left adjoint, hence carry the colimit above to a colimit. *)
Definition dual_functor_no_right_adjoint (H : CoordSpanProper)
  (Rt : Vct ⟶ Vct^op) (A : Dual F ⊣ Rt) : False :=
  dual_not_PreservesColimitCocone H
    (left_adjoint_PreservesColimitCocone A LineDiagram).

(* The corollary: [Dual F] is not the left adjoint of its opposite. *)
Definition dual_not_left_adjoint_of_op (H : CoordSpanProper)
  (A : Dual F ⊣ Opposite_Functor (Dual F)) : False :=
  dual_functor_no_right_adjoint H (Opposite_Functor (Dual F)) A.

(** ** The unconditional positive half: [Dual F] is adjoint to itself on the
       right, so it is continuous *)

(* The remaining obligations (respectfulness, the two round trips, the four
   naturality squares) are closed by the tree's default tactic. *)
#[local] Obligation Tactic := cat_simpl.

(* The transpose [a ~> D x ↦ x ~> D a]: [D f ∘ η x]. *)
Definition vct_transpose {a x : Vct} (f : a ~{Vct}~> Dual F x) :
  x ~{Vct}~> Dual F a :=
  fmap[Dual F] f ∘ eta F x.

Lemma vct_transpose_invol {a x : Vct} (f : a ~{Vct}~> Dual F x) :
  vct_transpose (vct_transpose f) ≈ f.
Proof. intros v w; simpl; reflexivity. Qed.

Program Definition vct_transpose_morphism (a x : Vct) :
  @SetoidMorphism _ (@homset Vct a (Dual F x))
                  _ (@homset Vct x (Dual F a)) := {|
  morphism := @vct_transpose a x
|}.

Program Definition vct_aor (a x : Vct) :
  @Isomorphism Sets
    {| carrier := @hom Vct a (Dual F x);
       is_setoid := @homset Vct a (Dual F x) |}
    {| carrier := @hom Vct x (Dual F a);
       is_setoid := @homset Vct x (Dual F a) |} := {|
  to   := vct_transpose_morphism a x;
  from := vct_transpose_morphism x a
|}.

Program Definition dual_vct_AdjointOnTheRight :
  @AdjointOnTheRight Vct Vct (Dual F) (Dual F) := {|
  aor := vct_aor
|}.

Definition dual_vct_Adjunction : Opposite_Functor (Dual F) ⊣ Dual F :=
  Adjunction_of_AdjointOnTheRight dual_vct_AdjointOnTheRight.

(* Mac Lane's contrast: as a right adjoint, [Dual F] carries every colimit
   of Vct to a limit; the exercise is about the other direction. *)
Definition dual_vct_Continuous : ContinuousFunctor (Dual F) :=
  right_adjoint_Continuous dual_vct_Adjunction.

(** ** The functor the issue names: StarAutonomous.v's [dual] at the line *)

(* Instance/Mod/Closed.v:747's [RMod_SymMonClosed] makes Vct symmetric
   monoidal closed, and Structure/Monoidal/StarAutonomous.v:229's [dual],
   read at the line, is the dual-object functor #359 proves self-adjoint on
   the right.  Its objects are the internal homs [HomMod x VctLine], whose
   carriers and operations coincide with [DualMod]'s on the nose; only the
   packed records differ (probe N1, N5). *)
Definition VctSMC : @SymMonClosed Vct :=
  RMod_SymMonClosed (field_ring F) (field_comm F).

Definition VctDual359 : Vct^op ⟶ Vct := @dual Vct VctSMC VctLine.

(* The identity on functionals, as a module homomorphism each way. *)
Definition to359 (x : Vct) : Dual F x ~{Vct}~> VctDual359 x.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (Dual F x) (VctDual359 x)
       (@Build_CMonHom (ab_cmon (Dual F x)) (ab_cmon (VctDual359 x))
          (@Build_SetoidMorphism _ _ _ _ (fun g => g) _) _ _) _).
  - intros g g' Hg; exact Hg.
  - intro v; reflexivity.
  - intros g h v; reflexivity.
  - intros r g v; reflexivity.
Defined.

Definition from359 (x : Vct) : VctDual359 x ~{Vct}~> Dual F x.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (VctDual359 x) (Dual F x)
       (@Build_CMonHom (ab_cmon (VctDual359 x)) (ab_cmon (Dual F x))
          (@Build_SetoidMorphism _ _ _ _ (fun g => g) _) _ _) _).
  - intros g g' Hg; exact Hg.
  - intro v; reflexivity.
  - intros g h v; reflexivity.
  - intros r g v; reflexivity.
Defined.

Program Definition iso359 (x : Vct) : Dual F x ≅[Vct] VctDual359 x := {|
  to := to359 x; from := from359 x
|}.

(* [dual]'s arrow action is the closed transpose of evaluation; by the
   uniqueness clause of the exponential's universal property it is
   precomposition, checked on the tensor's generators. *)
Lemma dual359_fmap_pre {x y : Vct} (f : y ~{Vct}~> x) :
  fmap[VctDual359] (f : x ~{Vct^op}~> y)
    ≈ to359 y ∘ fmap[Dual F] f ∘ from359 x.
Proof.
  apply (@dcur_uniq Vct VctSMC).
  refine (tensor_hom_ext _ _ _).
  intros g w; reflexivity.
Qed.

(* The natural isomorphism [Dual F ≈ VctDual359], in [Fun]'s [≈]. *)
Definition dual_iso359 : Dual F ≈ VctDual359.
Proof.
  exists (fun x : Vct^op => iso359 x).
  intros x y f.
  rewrite (dual359_fmap_pre f).
  intros g v; simpl; reflexivity.
Defined.

(* Mac Lane §V.5 Exercise 2 for the functor the issue names, by transport
   of the adjunction along the isomorphism (Theory/Adjunction.v's
   [adjunction_along_left_iso], #431). *)
Definition dual359_no_right_adjoint (H : CoordSpanProper)
  (Rt : Vct ⟶ Vct^op) (A : VctDual359 ⊣ Rt) : False :=
  dual_functor_no_right_adjoint H Rt (adjunction_along_left_iso dual_iso359 A).

Definition dual359_not_left_adjoint_of_op (H : CoordSpanProper)
  (A : VctDual359 ⊣ Opposite_Functor VctDual359) : False :=
  dual359_no_right_adjoint H (Opposite_Functor VctDual359) A.

(** ** Readbacks *)

Example vct_coord_component (n : nat) (v : carrier (cmon_setoid PowLine)) :
  cmon_map (rm_hom (vct_coord n)) v = v n := eq_refl.

Example pow_line_carrier :
  carrier (cmon_setoid PowLine) = (nat → carrier (cmon_setoid VctLine))
  := eq_refl.

Example vct_transpose_component {a x : Vct} (f : a ~{Vct}~> Dual F x)
  (v : carrier (cmon_setoid x)) (w : carrier (cmon_setoid a)) :
  cmon_map (rm_hom (cmon_map (rm_hom (vct_transpose f)) v)) w
    = cmon_map (rm_hom (cmon_map (rm_hom f) w)) v := eq_refl.

(* The isomorphism's components are the identity on functionals; this is
   what keeps [dual_iso359] transparent. *)
Example iso359_to_component (x : Vct) (g : carrier (cmon_setoid (Dual F x))) :
  cmon_map (rm_hom (to (projT1 dual_iso359 x))) g = g := eq_refl.

(* The colimit mediator computes: at a vector [z] of the competing apex it
   is the family of that cocone's legs at [z].  This is what keeps
   [PowCocone_IsColimitCocone] transparent. *)
Example pow_cocone_mediator_component (M : Cocone LineDiagram)
  (z : carrier (cmon_setoid (vertex_obj[M] : Vct))) (n : nat) :
  cmon_map (rm_hom (unique_obj (PowCocone_IsColimitCocone M))) z n
    = cmon_map (rm_hom (@vertex_map _ _ _ _ (@coneFrom _ _ _ M) n)) z
  := eq_refl.

End DualNoRightAdjoint.
