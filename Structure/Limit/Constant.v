(** * Limits and colimits of a constant diagram *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Components.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.

(* NOTATION GUARD, and it is REQUIRED here rather than defensive.  Three
   scopes declare [_ ^op] -- category, functor and adjunction -- and
   Category.Functor.Opposite opens [functor_scope], so after the Require
   block above a BINDER [{x y : J^op}] parses [J] as a functor and fails
   with "The term J has type Category while it is expected to have type
   ?C ⟶ ?D", naming neither culprit.  Measured: deleting the line below
   breaks this file at its first opposite-category binder.  Contrast
   Theory/Universal/Arrow/Dual.v, whose own guard is DEFENSIVE because
   every [C^op] there sits in an argument or ascription position, which
   [Bind Scope category_scope with Category] already rescues. *)
Open Scope category_scope.

Generalizable All Variables.

(* Book:      Mac Lane, "Categories for the Working Mathematician",
              2nd ed., §IV.2 Exercise 8, printed p. 90 (maclane:IV.2:ex8)
   nLab:      https://ncatlab.org/nlab/show/connected+category
   nLab:      https://ncatlab.org/nlab/show/constant+functor
   nLab:      https://ncatlab.org/nlab/show/diagonal+functor
   nLab:      https://ncatlab.org/nlab/show/limit
   nLab:      https://ncatlab.org/nlab/show/absolute+colimit

   Mac Lane's exercise says that if J is connected then the limit of the
   constant diagram Δ[J](c) is c itself, and dually for the colimit; so
   over a connected shape the diagonal functor is fully faithful and the
   unit of Δ ⊣ lim is an isomorphism at every object.  The four
   deliverables are

     (a) [const_IsALimit] / [const_IsAColimit] (with the cone-level
         [const_IsLimitCone] / [const_IsColimitCocone] and the bundled
         [const_Limit] / [const_Colimit]): the identity cone on c is a
         limiting cone over Δ[J](c), and the identity cocone is a
         colimiting cocone;

     (b) [const_unit_iso] / [const_counit_iso]: the unit of
         Δ[J] ⊣ [LimitFunctor] is invertible at every object, and dually
         the counit of [ColimitFunctor] ⊣ Δ[J] -- with
         [const_unit_is_med] recording that the unit IS the mediating
         map rather than merely equalling it;

     (c) [Diagonal_Full] and [Diagonal_Faithful]: the diagonal functor
         is full over a connected shape and faithful over an inhabited
         one -- the SPLIT is the point, and §4 below proves both halves
         sharp;

     (d) [const_AbsoluteLimit] / [const_AbsoluteColimit]: these limits
         are ABSOLUTE, preserved by EVERY functor out of C.

   1. A PRIOR-ART CORRECTION, ON TWO COUNTS, BOTH MEASURED.  The catalog
      issue's "Current state" section is FALSE twice over.

      FIRST, it states that no connectedness predicate exists in the
      tree and asks for the zig-zag relation to be built from scratch.
      Structure/Groupoid/Connected.v has declared [Inductive ZigZag
      {C : Category}] (:122) and [Definition Connected (C : Category)]
      (:133) for an ARBITRARY category since it was written, together
      with [zigzag_trans], [zigzag_sym], [hom_zigzag] and
      [Two_Discrete_not_connected] (:516); Theory/Connected/Components.v
      adds [ConnectedNonempty] (:771), [Zero_Connected] (:788),
      [Zero_not_ConnectedNonempty] (:792) and [connected_readings_differ]
      (:798).  All of them are CONSUMED here.  Nothing in this file
      redeclares a zig-zag, a connectedness predicate, or any of their
      closure properties, and [leg_zigzag] below is an induction OVER the
      donor's inductive type, not a second copy of it.

      SECOND, it states that there is no Δ ⊣ lim adjunction to take the
      unit of.  Adjunction/Diagonal/Limit.v supplies
      [Diagonal_Limit_Adjunction : Δ[J] ⊣ LimitFunctor] (:527) and
      [Colimit_Diagonal_Adjunction : ColimitFunctor ⊣ Δ[J]] (:771),
      together with [HasLimitsOfShape] (:363), [LimitFunctor] (:434),
      [lim_obj], [lim_leg], [lim_med], [lim_transpose_to] and the whole
      covariant colimit mirror.  Part (b) below is stated against those
      constants and builds no adjunction of its own.

      What IS absent, and is what this file supplies, was confirmed by a
      SHAPE sweep rather than a name sweep: no statement anywhere in the
      tree computes the limit or colimit of a CONSTANT diagram.  The two
      near-hits a name search returns are about a constant WEIGHT, not a
      constant diagram -- Structure/Limit/Weighted.v's [conical_weighted]
      has weight Δ[J](terminal_obj) with the DIAGRAM arbitrary, which is
      a different statement -- and Instance/One/Diagonal.v's
      [Diagonal_Unique] is a FACTORISATION (Δ[J](d) ≈ Δ(d) ◯ one)
      carrying no connectedness hypothesis and computing no limit.
      Separately, [Full (@Diagonal ...)], [Faithful (@Diagonal ...)],
      [AbsoluteLimit], [AbsoluteColimit] and the string "absolute limit"
      each had ZERO occurrences tree-wide.  (d) is genuinely new
      VOCABULARY -- [AbsoluteLimit] and [AbsoluteColimit] are introduced
      here.  (c) is not: [Full] and [Faithful] are pre-existing
      (Theory/Functor.v:332,:343), so what the zero-occurrence
      measurement shows there is a new INSTANTIATION at [Diagonal], not
      a new notion.  Prior art on absoluteness is prose in TWO files,
      not one: Structure/Coequalizer/Split.v and
      Construction/Karoubi.v:67,:70 ("Splitting an idempotent is an
      absolute colimit").

      READ (d)'s NOVELTY NARROWLY, THOUGH: the CONCEPT is prior art.
      Structure/Coequalizer/Split.v is headed "Split coequalizers are
      absolute", cites Paré 1971 and the nLab in prose, and proves
      [functor_preserves_split] together with
      [split_coequalizer_preserved].  What it does NOT do is declare a
      predicate -- its absoluteness is a property of one construction,
      stated by transporting its equational data through [fmap] -- so
      there was nothing to instantiate here and nothing here subsumes it.
      The two are related only by the shared word; §"WHAT IS NOT
      DELIVERED" records that no bridge is built.

   2. INHABITEDNESS IS LOAD-BEARING, AND THAT IS PROVED RATHER THAN
      ARGUED.  The in-tree [Connected] is the bare "any two objects are
      joined" clause with NO inhabitedness, and [Zero_Connected] shows
      the empty category satisfies it vacuously.  Over the empty shape a
      cone is a BARE APEX -- no legs, no coherence -- so the universal
      property collapses to terminality, which
      [zero_const_limit_IsTerminalObj] and [IsTerminalObj_zero_const_limit]
      prove in both directions.  Consequently
      [const_limit_not_from_bare_connected] refutes the bare-[Connected]
      reading outright: at J := [_0] and C := [_2] the object [TwoX] is
      not terminal ([TwoX_not_terminal], through [Instance/Two.v]'s own
      [TwoHom_Y_X_absurd]), so the conclusion is FALSE there while the
      hypothesis holds.

      The hypothesis is therefore [ConnectedNonempty J], and it goes in
      the statement.  #352 already separates the two readings at the
      empty shape; what is new here is that the separation BITES for
      constant limits.  A reader who wants the bare-[Connected] form
      should read [zero_const_limit_IsTerminalObj] as the missing case.

   3. WHERE EACH HYPOTHESIS IS SPENT.  [cn_obj K] and [cn_zigzag K] are
      spent at DIFFERENT points and neither substitutes for the other:
      [cn_obj K] NAMES the mediator ([limit_med (const_IsALimit K) N =
      cone_leg N (cn_obj K)], on the nose), while [cn_zigzag K] proves
      that this choice satisfies the triangle at EVERY other object.
      That is the precise sense in which connectedness alone does not
      suffice and a point alone does not either -- and both halves are
      refuted, in §4.

      The zig-zag content is factored out of the cone vocabulary
      entirely: [leg_zigzag] takes a BARE family [leg : ∀ x : J, n ~> c]
      that is constant along single arrows and concludes it is constant
      along zig-zags.  Its three cases are [zz_nil] (reflexivity alone),
      [zz_fwd] (the hypothesis at [f], then the induction hypothesis) and
      [zz_bwd] (THE SAME hypothesis at SWAPPED arguments, rewritten
      backwards) -- so the two non-trivial constructors consume one and
      the same input and there is no asymmetry to manage.  It serves the
      cone side, the cocone side, the two absolute statements and
      [Diagonal_Full], five consumers in all.

      THE COLIMIT HALF NEEDS NO [Connected (J^op)], WHICH IS FORTUNATE
      SINCE THE TREE CARRIES NO TRANSPORT OF CONNECTEDNESS TO THE
      OPPOSITE (measured: no [zigzag_op] and no [Connected_op] anywhere).
      [Connected] is declared for an ARBITRARY category, so
      [Connected (J^op)] is perfectly statable and would follow from a
      three-case induction swapping [zz_fwd] and [zz_bwd]; what is
      absent is that transport, not the statement.  [obj[J^op]] IS [obj[J]], so
      [leg_zigzag] is instantiated at the shape [J] with AMBIENT [C^op];
      the explicit [@leg_zigzag J (C^op) ...] is required, since left to
      inference the index type of [cone_leg N] makes Coq pick [J^op] and
      then the step hypothesis demands [J^op] arrows.

   4. THE TWO HALVES OF (c) ARE SEPARATED BY COMPILED COUNTEREXAMPLES.
      [Diagonal_Faithful] takes only an OBJECT of J; [Diagonal_Full]
      takes the whole of [ConnectedNonempty].  Sharpness is PARTIAL and
      the gap is named: what is refuted is the POINT for faithfulness
      and the CONNECTEDNESS half for fullness.  Nothing refutes fullness
      over a point-less shape, so the point half of [ConnectedNonempty]
      is NOT shown necessary for [Diagonal_Full].  The two
      refutations: [Diagonal_Zero_not_Faithful] refutes
      faithfulness over the
      empty shape (where [_0, Coq] has singleton hom-sets, so [id] and
      [negb] collapse), and [Diagonal_Two_Discrete_not_Full] refutes
      fullness over the inhabited but DISCONNECTED [Two_Discrete] --
      the transformation [td_split], which is [id] at one object and
      [negb] at the other, is natural there and is the image of no
      morphism.  That refutation fires against [Full]'s [prefmap] and
      [fmap_sur] directly, and [Full] demands no functoriality of
      [prefmap], so it refutes the WEAKEST reading of fullness.

      [Diagonal_Full] is delivered twice -- directly, and
      [Diagonal_Full_via_limit] through part (a)'s mediator -- and the
      two pick THE SAME preimage, recorded at [eq_refl] by
      [Diagonal_Full_routes_agree].  So the limit route is not a detour
      to a different chosen section; it is the direct one.  The two
      [Full] RECORDS are not compared, their [fmap_sur] proofs being
      distinct opaque terms.

   5. WHAT THE [Two_Discrete] REFUTATION DOES AND DOES NOT SAY.
      [two_discrete_const_not_limit] refutes that [bool], WITH ANY LEG
      FAMILY WHATSOEVER, is a limit of the constant [bool]-diagram of
      two-object discrete shape in [Coq] -- the quantification over legs
      sits inside [IsALimit], so this is the strong form.  It does NOT
      say the limit fails to exist: [td_const_IsALimit_product] builds
      it, and it is c × c.  Nor does it hold at every object:
      [td_const_IsALimit_at_unit] shows the disconnected conclusion is
      still TRUE at a terminal c, so the witness must be an object with
      c ≇ c × c, and no THIN ambient can host one (in a thin category
      c × c ≅ c always).  That is why the witness is [Coq] and the
      refutation is a pigeonhole: surjectivity of ⟨φX, φY⟩ onto
      bool × bool from bool.

   6. STRENGTHS, MEASURED STRICT-FIRST.  Every readback below names its
      subject.  Holding at [eq_refl]: [const_fobj] and [const_fmap] (the
      constant diagram's arrow action IS [id[c]], which is why every
      coherence obligation in this file closes by [id_left] rather than
      by a chase); [const_apex_strict], [const_cone_leg_strict],
      [const_leg_strict] and [const_med_strict] (the mediator IS the
      competing cone's leg at [cn_obj K]); the three colimit mirrors
      [const_cocone_inj_strict], [const_coinj_strict],
      [const_comed_strict]; [const_unit_is_transpose] and
      [const_unit_is_med] (the unit of Δ ⊣ lim IS the mediating map, not
      merely ≈ it) with [const_counit_is_transpose] dually;
      [const_two_cones_same_legs]; [const_absolute_leg_strict] and
      [const_absolute_coinj_strict]; [const_image_fobj];
      [Diagonal_Full_routes_agree]; and the non-vacuity pair
      [two_const_leg_strict], [two_const_med_strict].

      SETTLING FOR ≈, with the cause diagnosed rather than guessed --
      TWO of them, [const_unit_is_limit_unique_to] and
      [const_image_fmap_equiv].  The first:  Its strict form is
      REFUTED and pinned, and [const_two_cones_same_legs] is the
      DIAGNOSING control -- the two competing cones have the same legs
      at [eq_refl] and differ only in their [cone_coherence] proof
      terms, and [ump_limits] of an abstract [HasLimitsOfShape] reduces
      on nothing, so no conversion is available.  Also at ≈:
      [const_image_fmap_equiv], whose strict form is likewise refuted --
      [fmap[F ◯ Δ[J](c)] f] is [fmap[F] id[c]] where [fmap[Δ[J](F c)] f]
      is [id[F c]], and only [fmap_id] relates them.

   7. NEGATIVES: FIVE, OF TWO KINDS, KEPT LEXICALLY APART -- three
      CONVERSION in the body and two FORMABILITY in the closing
      [UniverseProbe] section -- each stripped once and its failure read
      off the WHOLE error message rather than the tail.

      CONVERSION.  [op_diag_strict] records that [Δ[J](c)^op] is NOT
      [Δ[J^op](c)], with [op_diag_fobj] and [op_diag_fmap] as controls
      showing BOTH DATA fields agree at [eq_refl], so the difference is
      confined to the three rebuilt law fields.  That is not a curiosity:
      [ACone n G] is not convertible for non-convertible [G], so the
      colimit half CANNOT be obtained by instantiating the limit half at
      [C^op] and [J^op], and it is built directly instead.
      [const_image_fmap] and [const_unit_is_limit_unique_to_strict] are
      the other two, both discussed in §6.

      FORMABILITY.  With the shape's hom universe declared strictly below
      both its own proof universe and the ambient's hom universe,
      [Diagonal] and [IsALimit] are each rejected ALONE and on DIFFERENT
      equations -- "Cannot enforce jh = ch" and "Cannot enforce jp = jh"
      respectively -- against four controls accepted at those very levels
      ([obj], a hom type, [ACone] and [Cone]).  So §8's "two independent
      donors" is guarded, not merely measured.

      Every constant named inside a [Fail] is also named by a succeeding
      command, so a rename breaks this file loudly rather than turning a
      guard vacuously green: [Opposite_Functor], [Diagonal], [fobj] and
      [fmap] by the two [op_diag_*] controls; [Diagonal] and [◯] again by
      [const_image_fobj] and [const_image_fmap_equiv]; and [const_unit],
      [limit_unique_to], [const_IsALimit] and [lim_alimit] by
      [const_unit_is_transpose] and [const_unit_is_limit_unique_to].

   8. UNIVERSES, READ OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK.
      [const_IsALimit@{u u0 u1 u2 u3 u4 u5}] is over
      [J : Category@{u u0 u0}] and [C : Category@{u1 u2 u2}] with the
      single equation [u0 = u2] in its block -- the SHAPE's hom-and-proof
      universe identified with the AMBIENT's -- while BOTH OBJECT
      UNIVERSES STAY FREE, bounded and never identified, and no [Set]
      appears anywhere in the general results.  Note that hom = proof in
      each category is expressed by REUSING one level in the BINDER with
      nothing in the block saying so, which is the reading trap this tree
      records repeatedly.

      [AbsoluteLimit] IS THIS FILE'S SHARPEST INSTANCE OF THAT TRAP: its
      constraint block contains NO equation at all, while its binder reads
      [J : Category@{u1 u5 u5}] and [C : Category@{u3 u5 u5}] -- one level
      reused for four slots.  A reader who checks only the block reports
      "no identification" and is wrong.

      EVERY CROSS-CATEGORY IDENTIFICATION IS INHERITED -- read that
      precisely, because ONE identification IS added here and an earlier
      revision of this paragraph denied it (see the end of this item).
      The inherited ones are measured at the DONORS' OWN SIGNATURES
      rather than inferred:
      [IsALimit@{u u0 u1 u2}] is itself declared over
      [J : Category@{u0 u1 u1}] and [C : Category@{u2 u1 u1}], and
      [Diagonal@{u u0 u1 u2 u3 u4}] over [C : Category@{u3 u4 u4}] and
      [J : Category@{u2 u4 u4}], both carrying the identification in the
      binder with no equation in the block; [ACone@{u0 u1 u2 u3 u4 u5}]
      keeps all six levels apart and is innocent.  §7's two formability
      negatives guard exactly this.  [leg_zigzag@{u u0 u1 u2}], the
      reusable core, has a LITERALLY EMPTY constraint BLOCK -- but its
      BINDER reads [C : Category@{u u2 u2}], and THAT identification is
      NOT inherited: it is this file's own minimization artifact from
      the unannotated [Context {J C : Category}], demonstrated by an
      isolating experiment -- the identical statement and proof compile
      inside a section declaring [Constraint ch < cp] over
      [Cu : Category@{co ch cp}], with a hom type accepted at those
      levels as the control.  The J-side IS inherited ([ZigZag@{u u0}]
      is declared over [Category@{u u0 u0}]).  So reading the empty
      block alone gets it wrong here, exactly as this item warns two
      paragraphs above; explicit binders would lift it and none of it
      is claimed unavoidable.

   9. AXIOMS AND COUNTS.  89/89 constants closed under the global
      context, counted by [Print Module] on the compiled module so the two
      [Program] obligations of [td_split] are included; the file declares
      no [Record], [Class] or [Inductive], so there is no unlisted
      [Build_*] constructor, and the three [Fail]ed names declare nothing.
      Read the GRADE: that is a ONE-TIME measurement of all 89, not a
      standing gate.

  10. TWO ENGINEERING FINDINGS, both recorded where they bite.  First,
      the notation guard at the head of this file is REQUIRED rather than
      defensive -- see the comment there.  Second,
      Category.Theory.Adjunction exports [unit], so the singleton probe
      object of the [Two_Discrete] refutation is spelled with Lib's
      [poly_unit]/[ttt]: written [(unit : Coq)] the ascription resolves to
      the adjunction unit and fails with a type error naming neither
      culprit.

   WHAT IS NOT DELIVERED.  The issue's own Verification block pins
   [Print Assumptions connected_limit_of_constant]; THAT NAME EXISTS
   NOWHERE IN THE TREE (measured), the delivered name being
   [const_IsALimit].  And only the FORWARD direction of item 2's
   "exactly when" is proved: nothing forces [ConnectedNonempty J] from
   invertibility of the unit.  The GENERAL (non-connected) case is NOT
   built: nothing here composes with Structure/Limit/Components.v's
   [ComponentDecomposition] / [components_IsALimit] to compute the limit
   of a constant diagram over an arbitrary shape as a product of copies
   of c indexed by π₀, and no bridge exhibits the connected case as the
   one-component instance of that file's results.
   [td_const_IsALimit_product] is the two-object discrete case done by
   hand, not an instance of anything.  No converse: it is NOT shown that
   [∀ c, IsALimit Δ[J](c) c] forces [ConnectedNonempty J], so the
   counterexamples establish one direction only.  No separation between
   the cone-level and apex-only readings, so neither is called strictly
   weaker.  Nothing is stated in [StrictCat], and no [_ ≅[Cat] _]
   constant is built.  [Diagonal] is not shown to be an EQUIVALENCE
   under any hypothesis, no [FullyFaithful] record is assembled, and no
   essential-surjectivity clause is attempted.  No absolute-limit theory
   beyond the two definitions and their two witnesses: nothing relates
   [AbsoluteLimit] to [PreservesLimit], [PreservesLimitCone],
   [ContinuousFunctor] or [CreatesLimit], no cone-level absoluteness is
   defined, split coequalizers are not related to it although
   Structure/Coequalizer/Split.v has an absoluteness notion of its own,
   and no absolute limit OTHER than the constant one is exhibited.  No
   functoriality or naturality of [const_unit] in c, so part (b) is a
   FAMILY of isomorphisms and is not packaged as a natural isomorphism
   [Id ≅ LimitFunctor ◯ Δ].  No uniqueness statement for the limiting
   cone beyond what [Structure/Limit/Unique.v] already gives.  Nothing
   about cofinality or final functors.  No notation.  No concrete
   category is shown complete by these means, and the only non-vacuity
   witness is the walking arrow. *)

(** ** The constant diagram, and the zig-zag closure that drives the file *)

(* The arrow action of a constant diagram is [id] ON THE NOSE, not merely
   ≈ it (Functor/Diagonal.v:37).  Everything below rests on this: each
   coherence triangle of a cone over Δ[J](c) reads [id ∘ ψx ≈ ψy], so one
   [id_left] collapses it to [ψx ≈ ψy], so no diagram chase occurs in
   any cone-coherence triangle.  Read that scope: the two retraction
   lemmas [const_unit_retraction] and [const_counit_retraction] DO
   chase, each running [comp_assoc] plus a leg-agreement rewrite and a
   section rewrite, and two obligations close with [cat]. *)

Example const_fobj {J C : Category} (c : C) (x : J) :
  fobj[Δ[J](c)] x = c := eq_refl.

Example const_fmap {J C : Category} (c : C) {x y : J} (f : x ~{J}~> y) :
  fmap[Δ[J](c)] f = id[c] := eq_refl.

(* The reusable core, stated for a BARE leg family rather than for a cone:
   a family constant along every single arrow is constant along every
   zig-zag.  [zz_nil] needs reflexivity alone; [zz_fwd] and [zz_bwd]
   consume ONE AND THE SAME hypothesis [H], differing only in the order of
   its arguments and the direction of the rewrite. *)

Lemma leg_zigzag {J C : Category} {n c : C} (leg : ∀ x : J, n ~{C}~> c)
  (H : ∀ (x y : J) (f : x ~{J}~> y), leg x ≈ leg y)
  {x y : J} (s : ZigZag x y) : leg x ≈ leg y.
Proof.
  induction s as [w|x' y' z' f s' IH|x' y' z' f s' IH].
  - reflexivity.
  - now rewrite (H _ _ f).
  - now rewrite <- (H _ _ f).
Qed.

(** ** Part (a), the limit: the identity cone on c is limiting *)

Section ConstantLimit.

Context {J C : Category}.
Context (c : C).

(* No [Program], and no obligation: the coherence field is literally
   [id_left (id[c])]. *)

Definition const_acone : ACone c Δ[J](c) :=
  @Build_ACone J C c Δ[J](c) (fun _ => id[c]) (fun _ _ _ => id_left (id[c])).

Definition const_cone : Cone Δ[J](c) :=
  {| vertex_obj := c ; coneFrom := const_acone |}.

(* The single mathematical step: a cone over a constant diagram has legs
   that agree along every arrow of the shape. *)

Lemma const_cone_step (N : Cone Δ[J](c)) {x y : J} (f : x ~{J}~> y) :
  cone_leg N x ≈ cone_leg N y.
Proof.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
  unfold cone_leg. rewrite <- Hc. now rewrite id_left.
Qed.

Definition const_cone_zigzag (N : Cone Δ[J](c)) {x y : J} (s : ZigZag x y) :
  cone_leg N x ≈ cone_leg N y :=
  leg_zigzag (cone_leg N) (@const_cone_step N) s.

(* [cn_obj K] NAMES the mediator; [cn_zigzag K] proves that naming
   satisfies the triangle at every other object.  Neither substitutes for
   the other -- §4 of the header refutes each hypothesis without the
   other. *)

Definition const_IsALimit (K : ConnectedNonempty J) : IsALimit Δ[J](c) c.
Proof.
  unshelve econstructor.
  - exact const_acone.
  - intro N. unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_left.
      exact (const_cone_zigzag N (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_left in Hv. symmetry. exact Hv.
Defined.

(* The cone-level and bundled readings cost nothing: Preservation.v's four
   conversions are proof-free, so both are [:=] with no tactic. *)

Definition const_IsLimitCone (K : ConnectedNonempty J) :
  IsLimitCone const_cone := @ump_limit _ _ _ _ (const_IsALimit K).

Definition const_Limit (K : ConnectedNonempty J) : Limit Δ[J](c) :=
  @Build_Limit J C Δ[J](c) const_cone
    (@ump_limit _ _ _ _ (const_IsALimit K)).

Example const_apex_strict : vertex_obj[const_cone] = c := eq_refl.

Example const_cone_leg_strict (x : J) : cone_leg const_cone x = id[c]
  := eq_refl.

Example const_leg_strict (K : ConnectedNonempty J) (x : J) :
  limit_leg (const_IsALimit K) x = id[c] := eq_refl.

Example const_med_strict (K : ConnectedNonempty J) (N : Cone Δ[J](c)) :
  limit_med (const_IsALimit K) N = cone_leg N (cn_obj K) := eq_refl.

End ConstantLimit.

(** ** Part (a), the colimit: built directly, not by op-instantiation *)

Section ConstantColimit.

Context {J C : Category}.
Context (c : C).

(* NEGATIVE 1 (conversion), with its two controls.  [Δ[J](c)^op] and
   [Δ[J^op](c)] agree in BOTH data fields at [eq_refl] and differ only in
   the three rebuilt law fields -- and since [ACone n G] is not
   convertible for non-convertible [G], that is exactly what stops the
   colimit half from being the limit half instantiated at [C^op], [J^op]. *)

Example op_diag_fobj (x : J) :
  fobj[Opposite_Functor Δ[J](c)] x = fobj[@Diagonal (C^op) (J^op) c] x
  := eq_refl.

Example op_diag_fmap {x y : J^op} (f : x ~{J^op}~> y) :
  fmap[Opposite_Functor Δ[J](c)] f = fmap[@Diagonal (C^op) (J^op) c] f
  := eq_refl.

Fail Example op_diag_strict :
  Opposite_Functor Δ[J](c) = @Diagonal (C^op) (J^op) c := eq_refl.

Definition const_acocone :
  @ACone (J^op) (C^op) c (Opposite_Functor Δ[J](c)) :=
  @Build_ACone (J^op) (C^op) c (Opposite_Functor Δ[J](c))
    (fun _ => id[c]) (fun _ _ _ => id_left (id[c])).

Definition const_cocone : Cocone Δ[J](c) :=
  @Build_Cone (J^op) (C^op) (Opposite_Functor Δ[J](c)) c const_acocone.

Lemma const_cocone_step (N : Cocone Δ[J](c)) {x y : J} (f : x ~{J}~> y) :
  cone_leg N x ≈ cone_leg N y.
Proof.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f) as Hc.
  unfold cone_leg. rewrite <- Hc. symmetry. now rewrite id_left.
Qed.

(* [obj[J^op]] IS [obj[J]], so [leg_zigzag] applies at the shape [J] with
   ambient [C^op] and NO [Connected (J^op)] is needed -- which is
   fortunate, the tree having neither [zigzag_op] nor [Connected_op].
   The explicit arguments are REQUIRED: left to inference the index type
   of [cone_leg N] makes Coq pick [J^op]. *)

Definition const_cocone_zigzag (N : Cocone Δ[J](c)) {x y : J}
  (s : ZigZag x y) : cone_leg N x ≈ cone_leg N y :=
  @leg_zigzag J (C^op) vertex_obj[N] c (cone_leg N)
    (@const_cocone_step N) x y s.

Definition const_IsAColimit (K : ConnectedNonempty J) : IsAColimit Δ[J](c) c.
Proof.
  unshelve econstructor.
  - exact const_acocone.
  - intro N. unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_right.
      exact (const_cocone_zigzag N (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_right in Hv. symmetry. exact Hv.
Defined.

Definition const_IsColimitCocone (K : ConnectedNonempty J) :
  IsColimitCocone const_cocone := @ump_limit _ _ _ _ (const_IsAColimit K).

Definition const_Colimit (K : ConnectedNonempty J) : Colimit Δ[J](c) :=
  @Build_Limit (J^op) (C^op) (Opposite_Functor Δ[J](c)) const_cocone
    (@ump_limit _ _ _ _ (const_IsAColimit K)).

Example const_cocone_inj_strict (x : J) : cocone_inj const_cocone x = id[c]
  := eq_refl.

Example const_coinj_strict (K : ConnectedNonempty J) (x : J) :
  colimit_inj (const_IsAColimit K) x = id[c] := eq_refl.

Example const_comed_strict (K : ConnectedNonempty J) (N : Cocone Δ[J](c)) :
  colimit_med (const_IsAColimit K) N = cocone_inj N (cn_obj K) := eq_refl.

End ConstantColimit.

(** ** Part (d): these limits are absolute *)

(* "Absolute limit" had ZERO occurrences tree-wide, so the notion is
   introduced here: a limit is absolute when EVERY functor out of the
   ambient category preserves it.  Stated at the apex-pinned level, which
   is what part (a) delivers; no cone-level variant is defined. *)

Definition AbsoluteLimit {J C : Category} (G : J ⟶ C) (c : C) : Type :=
  ∀ (D : Category) (F : C ⟶ D), IsALimit (F ◯ G) (F c).

Definition AbsoluteColimit {J C : Category} (G : J ⟶ C) (c : C) : Type :=
  ∀ (D : Category) (F : C ⟶ D), IsAColimit (F ◯ G) (F c).

Section Absolute.

Context {J C : Category}.
Context (c : C).

(* NEGATIVE 2 (conversion), with its control.  The image of a constant
   diagram agrees with the constant diagram on OBJECTS at [eq_refl] but
   not on ARROWS: [fmap[F ◯ Δ[J](c)] f] is [fmap[F] id[c]] where
   [fmap[Δ[J](F c)] f] is [id[F c]].  So absoluteness is not read off by
   rewriting the composite into a constant diagram; the proof repeats the
   argument with one [fmap_id] inserted. *)

Example const_image_fobj {D : Category} (F : C ⟶ D) (x : J) :
  fobj[F ◯ Δ[J](c)] x = fobj[Δ[J](F c)] x := eq_refl.

Fail Example const_image_fmap {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f = fmap[Δ[J](F c)] f := eq_refl.

Lemma const_image_fmap_equiv {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f ≈ fmap[Δ[J](F c)] f.
Proof. simpl. apply fmap_id. Qed.

Definition const_AbsoluteLimit (K : ConnectedNonempty J) :
  AbsoluteLimit Δ[J](c) c.
Proof.
  intros D F.
  unshelve econstructor.
  - unshelve econstructor.
    + intro x. exact (id[F c]).
    + intros x y f. simpl. rewrite fmap_id. now rewrite id_left.
  - intro N.
    assert (Hstep : ∀ (x y : J) (f : x ~{J}~> y),
              cone_leg N x ≈ cone_leg N y).
    { intros x y f.
      pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
      unfold cone_leg. rewrite <- Hc. simpl.
      rewrite fmap_id. now rewrite id_left. }
    unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_left.
      exact (@leg_zigzag J D vertex_obj[N] (F c) (cone_leg N)
               Hstep _ _ (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_left in Hv. symmetry. exact Hv.
Defined.

Definition const_AbsoluteColimit (K : ConnectedNonempty J) :
  AbsoluteColimit Δ[J](c) c.
Proof.
  intros D F.
  unshelve econstructor.
  - unshelve econstructor.
    + intro x. exact (id[F c]).
    + intros x y f. simpl. rewrite fmap_id. now rewrite id_left.
  - intro N.
    assert (Hstep : ∀ (x y : J) (f : x ~{J}~> y),
              @cone_leg (J^op) (D^op) _ N x ≈ @cone_leg (J^op) (D^op) _ N y).
    { intros x y f.
      pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f) as Hc.
      unfold cone_leg. rewrite <- Hc. simpl.
      rewrite fmap_id. now rewrite id_right. }
    unshelve econstructor.
    + exact (@cone_leg (J^op) (D^op) _ N (cn_obj K)).
    + intro x. simpl. rewrite id_right.
      exact (@leg_zigzag J (D^op) vertex_obj[N] (F c)
               (@cone_leg (J^op) (D^op) _ N) Hstep _ _
               (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_right in Hv. symmetry. exact Hv.
Defined.

Example const_absolute_leg_strict (K : ConnectedNonempty J)
  {D : Category} (F : C ⟶ D) (x : J) :
  limit_leg (const_AbsoluteLimit K D F) x = id[F c] := eq_refl.

Example const_absolute_coinj_strict (K : ConnectedNonempty J)
  {D : Category} (F : C ⟶ D) (x : J) :
  colimit_inj (const_AbsoluteColimit K D F) x = id[F c] := eq_refl.

End Absolute.

(** ** Part (b): the unit of Δ ⊣ lim is the mediating map, and invertible *)

Section LimitUnit.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (c : C).

Definition const_unit : c ~{C}~> lim_obj L Δ[J](c) :=
  @unit ([J, C]) C (@Diagonal C J) (LimitFunctor L)
        (Diagonal_Limit_Adjunction L) c.

(* Both identifications are [eq_refl]: the unit IS the transpose of the
   identity, and IS the mediator out of the transposed cone. *)

Example const_unit_is_transpose :
  const_unit = lim_transpose_to L (@id ([J, C]) Δ[J](c)) := eq_refl.

Example const_unit_is_med :
  const_unit = lim_med L (lim_transpose_cone (@id ([J, C]) Δ[J](c)))
  := eq_refl.

Lemma lim_leg_const_agree (x y : J) :
  lim_leg L Δ[J](c) x ≈ lim_leg L Δ[J](c) y.
Proof using J C L K c.
  exact (@const_cone_zigzag J C c (@limit_cone J C Δ[J](c) (L Δ[J](c)))
           x y (cn_zigzag K x y)).
Qed.

(* The section direction spends NO connectedness -- it is the transpose's
   own commutation law.  The zig-zag is spent exactly once, in the
   retraction, through the same [const_cone_zigzag] part (a) uses. *)

Lemma const_unit_section :
  lim_leg L Δ[J](c) (cn_obj K) ∘ const_unit ≈ id[c].
Proof.
  unfold const_unit.
  exact (lim_transpose_to_commutes L (@id ([J, C]) Δ[J](c)) (cn_obj K)).
Qed.

Lemma const_unit_retraction :
  const_unit ∘ lim_leg L Δ[J](c) (cn_obj K) ≈ id.
Proof.
  apply (lim_med_eq L (@limit_cone J C Δ[J](c) (L Δ[J](c)))); intro j.
  - transitivity (lim_leg L Δ[J](c) (cn_obj K)).
    + rewrite comp_assoc, (lim_leg_const_agree j (cn_obj K)).
      rewrite const_unit_section. now rewrite id_left.
    + exact (lim_leg_const_agree (cn_obj K) j).
  - now rewrite id_right.
Qed.

Definition const_unit_IsIsomorphism : IsIsomorphism const_unit :=
  {| two_sided_inverse := lim_leg L Δ[J](c) (cn_obj K)
   ; is_right_inverse  := const_unit_retraction
   ; is_left_inverse   := const_unit_section |}.

Definition const_unit_iso : c ≅ lim_obj L Δ[J](c) :=
  {| to := const_unit ; from := lim_leg L Δ[J](c) (cn_obj K)
   ; iso_to_from := const_unit_retraction
   ; iso_from_to := const_unit_section |}.

(* NEGATIVE 3 (conversion), with its DIAGNOSING control.  The unit is the
   canonical comparison of the two limits, but only at ≈: the two
   competing cones have the same legs at [eq_refl] and differ only in
   their [cone_coherence] proof terms, and [ump_limits] of an abstract
   [HasLimitsOfShape] reduces on nothing. *)

Fail Example const_unit_is_limit_unique_to_strict :
  const_unit = @limit_unique_to J C Δ[J](c) c (lim_obj L Δ[J](c))
                 (@const_IsALimit J C c K) (lim_alimit L Δ[J](c)) := eq_refl.

Example const_two_cones_same_legs (j : J) :
  cone_leg (lim_transpose_cone (@id ([J, C]) Δ[J](c))) j
    = cone_leg (alimit_cone (@const_IsALimit J C c K)) j := eq_refl.

Lemma const_unit_is_limit_unique_to :
  const_unit ≈ @limit_unique_to J C Δ[J](c) c (lim_obj L Δ[J](c))
                 (@const_IsALimit J C c K) (lim_alimit L Δ[J](c)).
Proof.
  symmetry.
  apply (lim_med_unique L (alimit_cone (@const_IsALimit J C c K))).
  intro j. unfold const_unit.
  exact (lim_transpose_to_commutes L (@id ([J, C]) Δ[J](c)) j).
Qed.

End LimitUnit.

(** ** Part (b), dually: the counit of colim ⊣ Δ is invertible *)

Section ColimitCounit.

Context {J C : Category}.
Context (M : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (c : C).

Definition const_counit : colim_obj M Δ[J](c) ~{C}~> c :=
  @counit C ([J, C]) (ColimitFunctor M) (@Diagonal C J)
          (Colimit_Diagonal_Adjunction M) c.

Example const_counit_is_transpose :
  const_counit = colim_transpose_from M (@id ([J, C]) Δ[J](c)) := eq_refl.

Lemma colim_inj_const_agree (x y : J) :
  colim_inj M Δ[J](c) x ≈ colim_inj M Δ[J](c) y.
Proof using J C M K c.
  exact (@const_cocone_zigzag J C c
           (@limit_cone (J^op) (C^op) _ (M Δ[J](c))) x y (cn_zigzag K x y)).
Qed.

Lemma const_counit_section :
  const_counit ∘ colim_inj M Δ[J](c) (cn_obj K) ≈ id[c].
Proof.
  unfold const_counit.
  exact (colim_transpose_from_commutes M (@id ([J, C]) Δ[J](c)) (cn_obj K)).
Qed.

Lemma const_counit_retraction :
  colim_inj M Δ[J](c) (cn_obj K) ∘ const_counit ≈ id.
Proof.
  apply (colim_med_eq M (@limit_cone (J^op) (C^op) _ (M Δ[J](c)))); intro j.
  - transitivity (colim_inj M Δ[J](c) (cn_obj K)).
    + rewrite <- comp_assoc, (colim_inj_const_agree j (cn_obj K)).
      rewrite const_counit_section. now rewrite id_right.
    + exact (colim_inj_const_agree (cn_obj K) j).
  - now rewrite id_left.
Qed.

Definition const_counit_IsIsomorphism : IsIsomorphism const_counit :=
  {| two_sided_inverse := colim_inj M Δ[J](c) (cn_obj K)
   ; is_right_inverse  := const_counit_section
   ; is_left_inverse   := const_counit_retraction |}.

Definition const_counit_iso : colim_obj M Δ[J](c) ≅ c :=
  {| to := const_counit ; from := colim_inj M Δ[J](c) (cn_obj K)
   ; iso_to_from := const_counit_section
   ; iso_from_to := const_counit_retraction |}.

End ColimitCounit.

(** ** Part (c): the diagonal is faithful on a point, full on a zig-zag *)

Section DiagonalFullyFaithful.

Context {J C : Category}.

(* Faithfulness costs only an OBJECT of J: two transformations agreeing
   everywhere agree at [j0], and their components at [j0] ARE the two
   morphisms. *)

Definition Diagonal_Faithful (j0 : J) : Faithful (@Diagonal C J).
Proof. construct. exact (X j0). Defined.

(* Naturality between two constant functors reads [id ∘ τx ≈ τy ∘ id], so
   the components agree along every arrow -- the transformation-level twin
   of [const_cone_step]. *)

Lemma const_transform_step {x y : C} (t : Δ[J](x) ⟹ Δ[J](y))
  {p q : J} (f : p ~{J}~> q) : transform[t] p ≈ transform[t] q.
Proof.
  pose proof (naturality[t] p q f) as Hn. simpl in Hn.
  rewrite id_left, id_right in Hn. exact Hn.
Qed.

Definition const_transform_zigzag {x y : C} (t : Δ[J](x) ⟹ Δ[J](y))
  {p q : J} (s : ZigZag p q) : transform[t] p ≈ transform[t] q :=
  leg_zigzag (fun j => transform[t] j) (@const_transform_step x y t) s.

Definition Diagonal_Full (K : ConnectedNonempty J) : Full (@Diagonal C J).
Proof.
  unshelve econstructor.
  - intros x y t. exact (transform[t] (cn_obj K)).
  - intros x y t j. simpl.
    exact (const_transform_zigzag t (cn_zigzag K (cn_obj K) j)).
Defined.

(* The same fullness read off part (a)'s mediator instead, through
   Structure/Cone/Const.v's [Cone_Natural_Transform]. *)

Definition Diagonal_Full_via_limit (K : ConnectedNonempty J) :
  Full (@Diagonal C J).
Proof.
  unshelve econstructor.
  - intros x y t.
    exact (limit_med (@const_IsALimit J C y K)
             {| vertex_obj := x
              ; coneFrom := fst (Cone_Natural_Transform Δ[J](y) x) t |}).
  - intros x y t j. simpl.
    pose proof (limit_med_commutes (@const_IsALimit J C y K)
      {| vertex_obj := x
       ; coneFrom := fst (Cone_Natural_Transform Δ[J](y) x) t |} j) as Hm.
    simpl in Hm. rewrite id_left in Hm. exact Hm.
Defined.

(* The two routes pick THE SAME preimage, on the nose -- so the limit
   route is not a detour to a different chosen section.  The two [Full]
   RECORDS are not compared; their [fmap_sur] proofs are distinct opaque
   terms. *)

Example Diagonal_Full_routes_agree (K : ConnectedNonempty J) (x y : C)
  (t : Δ[J](x) ⟹ Δ[J](y)) :
  @prefmap _ _ _ (Diagonal_Full_via_limit K) x y t
    = @prefmap _ _ _ (Diagonal_Full K) x y t := eq_refl.

End DiagonalFullyFaithful.

(** ** Inhabitedness is necessary: the empty shape computes a terminal
       object, not c *)

Definition zero_ACone {C : Category} (c n : C) : ACone n Δ[_0](c) :=
  @Build_ACone _0 C n Δ[_0](c)
    (fun x => match x with end) (fun x _ _ => match x with end).

Definition zero_Cone {C : Category} (c n : C) : Cone Δ[_0](c) :=
  {| vertex_obj := n ; coneFrom := zero_ACone c n |}.

(* Over [_0] a cone is a BARE APEX, so the universal property IS
   terminality -- proved in both directions. *)

Theorem zero_const_limit_IsTerminalObj {C : Category} {c : C} :
  IsALimit Δ[_0](c) c → IsTerminalObj c.
Proof.
  intros H d.
  destruct (@ump_limit _ _ _ _ H (zero_Cone c d)) as [u _ Hu].
  unshelve econstructor.
  - exact u.
  - exact I.
  - intros v _. apply Hu. intro x. destruct x.
Defined.

Theorem IsTerminalObj_zero_const_limit {C : Category} {c : C} :
  IsTerminalObj c → IsALimit Δ[_0](c) c.
Proof.
  intro T.
  unshelve econstructor.
  - exact (zero_ACone c c).
  - intro N. unshelve econstructor.
    + exact (unique_obj (T vertex_obj[N])).
    + intro x. destruct x.
    + intros v _. apply (uniqueness (T vertex_obj[N])). exact I.
Defined.

Theorem TwoX_not_terminal : IsTerminalObj (TwoX : _2) → False.
Proof.
  intro T. exact (TwoHom_Y_X_absurd (unique_obj (T (TwoY : _2)))).
Qed.

Theorem zero_const_limit_needs_inhabited :
  IsALimit Δ[_0]((TwoX : _2)) (TwoX : _2) → False.
Proof.
  intro H. exact (TwoX_not_terminal (zero_const_limit_IsTerminalObj H)).
Qed.

(* The bare in-tree [Connected] reading of part (a) is FALSE. *)

Theorem const_limit_not_from_bare_connected :
  (∀ (J C : Category) (c : C), Connected J → IsALimit Δ[J](c) c) → False.
Proof.
  intro H.
  exact (zero_const_limit_needs_inhabited
           (H _0 _2 (TwoX : _2) Zero_Connected)).
Qed.

Theorem Diagonal_Zero_not_Faithful : Faithful (@Diagonal Coq _0) → False.
Proof.
  intro F.
  assert (Hn : @id Coq bool ≈ negb).
  { apply (@fmap_inj _ _ _ F). intro x. destruct x. }
  exact (Bool.diff_true_false (Hn true)).
Qed.

(** ** Connectedness is necessary: a two-object discrete shape *)

Definition td_ACone {C : Category} {c d : C} (p q : d ~{C}~> c) :
  ACone d Δ[Two_Discrete](c).
Proof.
  unshelve econstructor.
  - intro x. destruct x; [ exact p | exact q ].
  - intros x y f. destruct f; simpl; cat.
Defined.

Definition td_Cone {C : Category} {c d : C} (p q : d ~{C}~> c) :
  Cone Δ[Two_Discrete](c) :=
  {| vertex_obj := d ; coneFrom := td_ACone p q |}.

Section TwoDiscreteRefutation.

Context (H : IsALimit Δ[Two_Discrete]((bool : Coq)) (bool : Coq)).

Definition tdX : bool → bool := limit_leg H TwoDX.
Definition tdY : bool → bool := limit_leg H TwoDY.

(* The EXISTENCE half of the universal property alone, at apex [unit] with
   constant legs, makes ⟨tdX, tdY⟩ : bool → bool × bool surjective. *)

(* [Theory/Adjunction.v] exports [unit], so the singleton probe object is
   spelled with Lib's [poly_unit]/[ttt] rather than the stdlib [unit]/[tt];
   otherwise the ascription [(unit : Coq)] resolves to the adjunction unit
   and fails with a type error naming neither culprit. *)

Lemma td_surj (a b : bool) : { z : bool & (tdX z = a) * (tdY z = b) }.
Proof using H.
  destruct (@ump_limit _ _ _ _ H
              (@td_Cone Coq (bool : Coq) (poly_unit : Coq)
                 (fun _ => a) (fun _ => b))) as [u Hu _].
  exists (u ttt).
  exact (Hu TwoDX ttt, Hu TwoDY ttt).
Defined.

(* [False] mentions no section variable, so the [Proof using] is explicit;
   the Theory/Category/Monoid.v:919 precedent. *)

Theorem td_const_not_limit : False.
Proof using H.
  destruct (td_surj true  true)  as [z1 [Ha1 Hb1]].
  destruct (td_surj true  false) as [z2 [Ha2 Hb2]].
  destruct (td_surj false true)  as [z3 [Ha3 Hb3]].
  destruct z1, z2, z3; congruence.
Qed.

End TwoDiscreteRefutation.

Definition two_discrete_const_not_limit :
  IsALimit Δ[Two_Discrete]((bool : Coq)) (bool : Coq) → False :=
  td_const_not_limit.

Theorem const_limit_not_from_point_alone :
  (∀ (J C : Category) (c : C), J → IsALimit Δ[J](c) c) → False.
Proof.
  intro H.
  exact (two_discrete_const_not_limit
           (H Two_Discrete Coq (bool : Coq) TwoDX)).
Qed.

(* What the disconnected shape computes INSTEAD: the binary product.  So
   what is refuted is quantitative, not existence. *)

Definition td_const_IsALimit_product {C : Category} `{@Cartesian C} (c : C) :
  IsALimit Δ[Two_Discrete](c) (c × c).
Proof.
  unshelve econstructor.
  - exact (td_ACone exl exr).
  - intro N. unshelve econstructor.
    + exact (cone_leg N TwoDX △ cone_leg N TwoDY).
    + intro x. destruct x; simpl; cat.
    + intros v Hv. symmetry.
      apply (snd (ump_products _ _ v)).
      split; [ exact (Hv TwoDX) | exact (Hv TwoDY) ].
Defined.

Lemma punit_irrel (a b : poly_unit) : a = b.
Proof. destruct a, b; reflexivity. Qed.

(* ... and at a terminal object the disconnected conclusion still HOLDS, so
   the refutation genuinely needs an object with c ≇ c × c.  No thin
   ambient can host one, which is why the witness above is [Coq]. *)

Definition td_const_IsALimit_at_unit :
  IsALimit Δ[Two_Discrete]((poly_unit : Coq)) (poly_unit : Coq).
Proof.
  unshelve econstructor.
  - exact (td_ACone (fun _ => ttt) (fun _ => ttt)).
  - intro N. unshelve econstructor.
    + exact (fun _ => ttt).
    + intros x y. apply punit_irrel.
    + intros v _ y. apply punit_irrel.
Defined.

(* Fullness fails over an inhabited but disconnected shape.  The witness is
   natural and is the image of no morphism; the refutation fires against
   [Full]'s [prefmap]/[fmap_sur], which demand no functoriality of
   [prefmap], so it refutes the WEAKEST reading of fullness. *)

Program Definition td_split :
  Δ[Two_Discrete]((bool : Coq)) ⟹ Δ[Two_Discrete]((bool : Coq)) := {|
  transform := fun j => match j with
                        | TwoDX => @id Coq bool
                        | TwoDY => negb
                        end
|}.
Next Obligation. destruct f; reflexivity. Qed.
Next Obligation. destruct f; reflexivity. Qed.

Theorem Diagonal_Two_Discrete_not_Full :
  Full (@Diagonal Coq Two_Discrete) → False.
Proof.
  intro F.
  pose proof (@fmap_sur _ _ _ F (bool : Coq) (bool : Coq) td_split) as Hs.
  pose proof (Hs TwoDX true) as H1.
  pose proof (Hs TwoDY true) as H2.
  simpl in H1, H2. congruence.
Qed.

(** ** Non-vacuity: the walking arrow *)

(* [Two_Connected] is Structure/Limit/Components.v:897, consumed rather
   than rebuilt. *)

Definition two_ConnectedNonempty : ConnectedNonempty _2 :=
  Build_ConnectedNonempty (TwoX : _2) Two_Connected.

Definition two_const_IsALimit {C : Category} (c : C) :
  IsALimit Δ[_2](c) c := @const_IsALimit _2 C c two_ConnectedNonempty.

Definition two_const_IsAColimit {C : Category} (c : C) :
  IsAColimit Δ[_2](c) c := @const_IsAColimit _2 C c two_ConnectedNonempty.

Definition two_const_AbsoluteLimit {C : Category} (c : C) :
  AbsoluteLimit Δ[_2](c) c :=
  @const_AbsoluteLimit _2 C c two_ConnectedNonempty.

(* The shape is not degenerate: two distinct objects, a crossing arrow, and
   provably NO arrow back -- so the zig-zag, not a single arrow, is what
   joins [TwoY] to [TwoX]. *)

Theorem two_objects_distinct : (TwoX : _2) = TwoY → False.
Proof. discriminate. Qed.

Definition two_crossing_arrow : TwoX ~{_2}~> TwoY := TwoXY.

Theorem two_no_arrow_back : (TwoY ~{_2}~> TwoX) → False.
Proof. intro f. inversion f. Qed.

Example two_const_leg_strict {C : Category} (c : C) (x : _2) :
  limit_leg (two_const_IsALimit c) x = id[c] := eq_refl.

Example two_const_med_strict {C : Category} (c : C) (N : Cone Δ[_2](c)) :
  limit_med (two_const_IsALimit c) N = cone_leg N TwoX := eq_refl.

(** ** Universe probe: the two identifications are the DONORS' *)

(* Section-local [Universes]/[Constraint] declarations do not leak past
   [End] -- the Instance/Fun/Group.v precedent, re-measured for this file
   out of tree by importing it into a scratch module that declares its own
   levels strictly apart and having that module elaborate -- so the guard
   for §8 of the header lives here rather than in a separate probe file.

   NEGATIVES 4 AND 5 (formability), with four controls.  With the shape's
   hom universe declared strictly BELOW both its own proof universe and
   the ambient's hom universe, [obj], a hom-type, [ACone] and [Cone] all
   elaborate -- so the cone vocabulary is INNOCENT -- while [Diagonal] and
   [IsALimit] are each rejected ALONE, and on DIFFERENT equations:
   [Diagonal] fails with "Cannot enforce jh = ch" (its codomain [Fun]
   identifies source and target hom levels) and [IsALimit] with "Cannot
   enforce jp = jh".  So the [u0 = u2] carried by [const_IsALimit] has two
   genuinely independent donors, neither introduced here. *)

Section UniverseProbe.

Universes jo jh jp co ch cp.
Constraint jh < jp.
Constraint jh < ch.

Context (Ju : Category@{jo jh jp}) (Cu : Category@{co ch cp}) (x : Cu).

Check (obj[Ju]).
Check (∀ a b : Ju, a ~{Ju}~> b).
Check (@ACone Ju Cu x).
Check (@Cone Ju Cu).

Fail Check (@Diagonal Cu Ju).
Fail Check (@IsALimit Ju Cu).

End UniverseProbe.
