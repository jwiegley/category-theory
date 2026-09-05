(** * The bimodule tensor-hom adjunction, and its parameter *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed., §IV.8 Exercise 3, printed p. 104 (PDF p. 113), ledger
              item `maclane:IV.8:ex3`, issue #401.  Quoted verbatim from
              the rendered scan:

                "3. Let R, S, and T be rings.
                 (a) For a bimodule _R E _S, show that − ⊗_R E : Mod_R →
                     Mod_S has a right adjoint hom_S(E, −).
                 (b) Show that this is an adjunction with parameter
                     E ∈ R-Mod-S.
                 (c) Describe the composite of this adjunction with a
                     similar adjunction Mod_S → Mod_T."

   Book:      Mac Lane, ibid., §IV.7 Theorem 3, printed pp. 101–102 —
              the right adjoints of a bifunctor's partial functors
              extend uniquely to a bifunctor contravariant in the
              parameter.  That theorem is Adjunction/Parameter.v and is
              CONSUMED here, not restated: part (b) below hands it the
              hypothesis and reads Mac Lane's G off its conclusion.
   Book:      Mac Lane, ibid., §IV.1, printed pp. 79–80 — adjunctions in
              hom-set form, which is the presentation used throughout:
              Theory/Adjunction.v's [Adjunction] record is a natural
              bijection of hom-setoids and its unit and counit are the
              derived ⌊id⌋ and ⌈id⌉.
   Book:      Riehl, "Category Theory in Context", Dover 2016, §4.4
              Example 4.4.8, printed p. 152 — the tensor over S read as
              a BICLOSED bifunctor _R Mod_S × _S Mod_T → _R Mod_T, with
              a left closure Hom_R and a right closure Hom_T.  READ HER
              PROSE WITH CARE: the sentence "making Hom_R(M,N) into an
              R-T bimodule" is at odds with her own display, which lands
              that hom in _S Mod_T; S-T is what the display says.  The
              general three-ring form is NOT built here (see WHAT IS NOT
              DELIVERED).
   Book:      Riehl, ibid., §4.6 Corollary 4.6.10, printed p. 169 — for
              an R-S bimodule M the functor M ⊗_S − is right exact,
              because it is a left adjoint.  Scoped and deferred below.
   nLab:      https://ncatlab.org/nlab/show/tensor-hom+adjunction
   nLab:      https://ncatlab.org/nlab/show/bimodule
   Wikipedia: https://en.wikipedia.org/wiki/Tensor-hom_adjunction

   HANDEDNESS, WHICH THE PAGE FIXES AND WHICH DECIDES EVERY TYPE BELOW.
   Mod_R is the category of RIGHT R-modules; the bimodule is tensored on
   the RIGHT; N ⊗_R E carries a right S-action through E's right
   S-action; hom_S(E, M) is the set of right-S-module maps E → M, made a
   right R-module through E's LEFT R-action by (f ⊲ r)(e) = f (r · e).
   In this tree a right R-module is an object of
   [ModR R := RMod (Ring_op R)] (Instance/Mod.v:712), so it IS an
   [RModObject (Ring_op R)] and its homs ARE [RModHom]s.  Do not write
   [ModR (Ring_op R) = RMod R]: [Ring_op] is not strictly involutive.

   WHAT IS DELIVERED IN THIS FILE.

     §A, the engine.  [BalTensor N M], the BALANCED tensor of a right
     X-module N and a left X-module M, as an [AbObject].  It is a new
     inductive in Instance/Ab/Tensor.v's shape — four formers
     ([bs_gen], [bs_zero], [bs_plus], [bs_neg]; no formal scalar) and a
     quotienting relation with that file's eleven constructors plus ONE
     balance rule [be_balance], (n · x) ⊗ m ≈ n ⊗ (x · m).  The rule is
     statable with no transport because
     [carrier (rig_setoid (ring_rig (Ring_op X)))] is
     [carrier (rig_setoid (ring_rig X))] on the nose, recorded as
     [bal_scalars_agree] at [eq_refl].  With it: [BalBiadditive N M A],
     the maps additive in each variable and balanced over X;
     [bal_gen], the universal one; [bal_med], the mediator, a fixpoint,
     so [bal_med_gen] is [eq_refl]; [bal_hom_ext], agreement on
     generators; [bal_med_unique]; and [bal_gen_zero_l]/[bal_gen_zero_r].
     This layer is generic — it mentions no bimodule — and both
     handednesses of Exercise 3 are meant to instantiate it.

     §B, Mac Lane part (a).  [RTensor E N : RModObject (Ring_op S)],
     whose carrier is [BalTensor N (bm_left E)] and whose right S-action
     is the mediator of (n, e) ↦ n ⊗ (e ⊲ s); [TensorWith E : ModR R ⟶
     ModR S]; [HomSObj E M : RModObject (Ring_op R)], the group of
     ModR S-maps E → M with the translated right R-action; [HomS E :
     ModR S ⟶ ModR R]; the two transposes [bth_to]/[bth_from]; the
     hom-setoid isomorphism [bth_adj]; and
     **[bimodule_tensor_hom_adjunction E : TensorWith E ⊣ HomS E]**,
     built through Theory/Adjunction.v:159's [Build_Adjunction'].

     §C, the parameter.  [BimodHom E E'], a map of the left R-modules
     commuting with the right S-action (one field of its own, the rest
     inherited through the [bh_hom] coercion); its hom-setoid, identity
     and composition; **[BimodCat R S : Category]**; [BimodTensorMap]
     and **[BimodTensor : ModR R ∏ BimodCat R S ⟶ ModR S]**;
     [bt_partial_adj E : Partial_l BimodTensor E ⊣ HomS E]; and
     **[bimodule_parametrized_adjunction :
     ParametrizedAdjunction BimodTensor]**, an inhabitant of
     Adjunction/Parameter.v:361's record with [pa_right := HomS].  From
     it, [bimodule_hom_bifunctor : (BimodCat R S)^op ∏ ModR S ⟶ ModR R]
     is Mac Lane's G, obtained as
     [parametrized_right_adjoint_bifunctor] applied — its arrow action
     in the bimodule variable is that file's [pa_param_mate] and is
     therefore FORCED by Theorem 3.  Nothing here re-proves it.

     §D, Mac Lane part (c).  The LEFT R-action on a balanced tensor
     over S — [lt_bilin_act], [lt_act], [LTensor] — is §A's engine
     instantiated on the other side and is SHARED with §E.  With it,
     [BimodTensorBimod E E1 : Bimodule R T] carries BOTH residual
     actions on ONE group: its [bm_left] is [LTensor E (bm_left E1)]
     and its right T-action is [RTensor E1 (bimodule_right_RMod E)]'s,
     the two agreeing on carriers at [eq_refl] ([btb_carriers_agree]),
     and its [bm_compat] closing on generators by [reflexivity] —
     both sides send e ⊗ e1 to (r · e) ⊗ (e1 ⊲ t).  Then
     **[bimodule_adjunction_composite E E1 :
     (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1)]**, which is
     Adjunction/Compose.v:173 applied and nothing else, with the
     composite's unit and counit read back at [eq_refl] as the DOUBLE
     generator n ⊗ e ⊗ e1 and DOUBLE evaluation f ⊗ e ⊗ e1 ↦ (f e) e1
     ([bac_unit_is_gen], [bac_counit_is_eval]) and Mac Lane's
     whiskered descriptions carried over from that file's :216/:224 —
     at ≈ only, their [eq_refl] forms refuted in the probe (N16, N17).
     The comparison is **[tensor_assoc_iso E E1]**, a natural
     isomorphism in [Functor_Setoid] whose per-object leg [ta_iso] is
     built by a mediator of a mediator in each direction; both round
     trips and the coherence square close by [reflexivity] at the
     double generators, through the two extensionality lemmas
     [ta_double_ext] and [ta_double_ext_r].  Transporting the
     composite along it needs a lemma the tree does not have —
     **[adjunction_along_left_iso]**, a functor naturally isomorphic
     to a left adjoint is a left adjoint with the SAME right adjoint —
     and that gives [bimodule_tensor_bimod_adjunction] and hence, by
     Theory/Adjunction.v:367's uniqueness of right adjoints,
     **[bimodule_hom_composite_iso : HomS E ◯ HomS E1 ≈
     HomS (BimodTensorBimod E E1)]**.  That pair IS Mac Lane's
     "describe the composite": the composite adjunction is the
     adjunction of the tensor of the two bimodules, up to natural
     isomorphism on both sides and no further.

     §E, the left-module mirror and Riehl's Corollary 4.6.10.
     [LTensorWith E : RMod S ⟶ RMod R] over §D's engine;
     [LHomSObj E M : RModObject S], the group of RMod R-maps
     [bm_left E] → M with the LEFT S-action (s · f)(e) = f (e ⊲ s), the
     mirror of §B's translation; [LHomS E : RMod R ⟶ RMod S]; and
     **[bimodule_left_tensor_hom_adjunction E : LTensorWith E ⊣
     LHomS E]**, again through [Build_Adjunction'], again with unit
     and counit at [eq_refl].  From it and Adjunction/Continuity.v:239,
     [bimodule_left_tensor_preserves_colimits], its right-module twin
     [bimodule_tensor_preserves_colimits] and the composite's
     [bimodule_tensor_bimod_preserves_colimits], each a [:=] with no
     tactic.

     §F, the second closure and the two-variable adjunction.
     [HomAbBimod N M : Bimodule R S] for a right R-module N and a
     right S-module M — the group of Ab-maps N → M with
     (r · f)(n) = f (n ⊲ r) and (f ⊲ s)(n) = (f n) ⊲ s, whose
     [bm_compat] holds POINTWISE with no law consumed —
     [HomAbFunctor N : ModR S ⟶ BimodCat R S], and
     [hab_partial_adj N : Partial_r BimodTensor N ⊣ HomAbFunctor N],
     which is exactly the mirror hypothesis Adjunction/Parameter.v:1795
     asks for.  [bimodule_mirror_family] packages it and
     **[bimodule_two_variable_adjunction]** is that file's :1978
     [mutually_right_adjoint] applied, an inhabitant of
     Adjunction/Right.v:342's own [AdjointOnTheRight]; the third leg
     with both hom-setoids written out is [bimodule_third_leg], a map
     of bimodules E → hom_Ab(N, M) being the same thing as a map of
     right R-modules N → hom_S(E, M).  With §C's [pa_adj] that is all
     three legs of Riehl's Definition 4.4.7 for [BimodTensor].

     §G, a concrete witness.  Everything instantiates at
     Instance/Mod.v:878's [Int_Bimodule] with no new algebra, and
     COMPUTES on closed integers: the right action, the unit, the
     counit, both actions of the tensor of two bimodules and both legs
     of the associativity comparison are [eq_refl] readbacks, and
     [int_tensor_separates] proves two generators distinct by mapping
     OUT through multiplication — no induction over the quotienting
     relation could produce a negative.  The stdlib identifier [Z] is
     named in no statement (six statements carry [%Z] numerals
     only): the binders go through the ring's own carrier and the
     arithmetic through its own rig laws.

   WHAT THEOREM 3 DOES NOT GIVE, AND WHY §C IS ORGANISED AS IT IS.
   [pa_adj] is typed against [Partial_l F p], so F must already be a
   bifunctor before the hypothesis can even be stated.  Functoriality of
   the tensor in the BIMODULE argument is therefore a PREREQUISITE of
   Mac Lane's Theorem 3, not an output of it; what the theorem supplies
   free is the arrow action of the RIGHT adjoint, [pa_right] being a
   bare function of objects.  [BimodTensorMap] and [bt_map_bal] pay that
   prerequisite, in the bimodule variable and in the module variable at
   once.

   THE ADJUNCTION IS BETWEEN TWO DIFFERENT MODULE CATEGORIES, AND THE
   TWO RINGS ARE UNRELATED.  The whole of §B sits under
   [Context {R S : RingObject}] with no homomorphism between them and no
   relation assumed; [TensorWith E] runs [ModR R ⟶ ModR S] and [HomS E]
   runs back.  At R = S nothing degenerates and nothing is claimed.

   NO COMMUTATIVITY, NO CENTRALITY, AND THAT IS A MEASUREMENT.  Below
   this header the tokens [Rcomm] and [rig_mul_comm] occur nowhere at
   all, and the string "commutativ" occurs exactly once, in a comment
   recording that commutativity is not spent.  The [Context]s are
   rings, bimodules and modules and nothing else — §D and §F add a
   third ring and two module variables, §E none, and no hypothesis
   relating any two rings is ever taken.  Contrast
   Instance/Mod/Closed.v:448, whose [HomMod] takes a commutativity proof
   as an EXPLICIT ARGUMENT at the signature and so cannot host
   hom_S(E, −) over a non-commutative S; and Instance/Mod/Extension.v,
   whose [CentralImage] hypothesis is spent at eight proof sites (its
   own header names a second and a third) precisely because it
   tensors two LEFT modules and bolts the second action on afterwards.
   Doing the construction bimodule-aware is what removes both.

   THE SPEND LEDGER.  Read as a ledger; each entry is the law the
   obligation actually consumes.

     [bal_med_respects]   ← one case per constructor of the relation,
                            each met by the target group's own law; the
                            balance case is [bal_balance] of β
     [bal_hom_ext]        ← [cmon_map_zero], [cmon_map_plus] and
                            Instance/Ab.v's [ab_map_neg]
     [rt_bilin_act]       balance ← **[bm_compat]**, ONE use, and
                            nothing else of the bimodule
     [rt_act_distr_r]     ← [bm_rsmul_distr_r]
     [rt_act_assoc]       ← [bm_rsmul_assoc]      (associativity ONLY)
     [rt_act_one]         ← [bm_rsmul_one]
     [rt_act_distr_l]     ← NOTHING; it is [cmon_map_plus] of the
                            mediator, supplied as a field value
     [rt_map_bal]         balance ← [rm_map_smul] of the given map
     [RTensorMap], and [TensorWith]'s three laws ← NOTHING beyond
                            [bal_hom_ext]; every generator case closes
                            by [reflexivity]
     [hs_act]             [rm_map_smul] ← **[bm_compat]**, the second
                            use in the file, then the given map's own
                            linearity
     [hs_act_distr_l]     ← NOTHING; it closes by [reflexivity]
     [hs_act_distr_r]     ← [rm_smul_distr_r] of E's left module
     [hs_act_assoc]       ← [rm_smul_assoc]       (associativity ONLY)
     [hs_act_one]         ← [rm_smul_one]
     [HomSMap]'s [rm_map_smul], and [HomS]'s [fmap_id] and [fmap_comp]
                          ← NOTHING; all three close by [reflexivity]
     [bth_to_inner]'s [rm_map_smul] ← the given map's own linearity,
                            with NO rewriting: n ⊗ (e ⊲ s) IS
                            s ·[RTensor E N] (n ⊗ e) on the nose
     [bth_to]'s [rm_map_smul] ← **[be_balance]**, the balance rule read
                            as a law: this is why the forward transpose
                            is R-linear
     [bth_from_bal]'s balance ← the given map's own R-linearity, again
                            with no rewriting, the action on
                            hom_S(E, M) being translation
     [bth_adj]'s two round trips ← NOTHING beyond [bal_hom_ext]; the
                            first closes by [reflexivity], the second
                            through it, so the bijection leaves no
                            residue on either side
     [bimodule_tensor_hom_adjunction]'s two naturality clauses ←
                            NOTHING; both close by [reflexivity]
     [bt_partial_adj]'s two naturality clauses ← NOTHING likewise
     [bimod_hom_compose]'s [bh_right] ← the two given maps' [bh_right]
     [BimodCat]'s four category laws ← NOTHING; all by [reflexivity]
     [bt_map_bal]'s balance ← [rm_map_smul] of the module map, then
                            [be_balance], then [rm_map_smul] of the
                            bimodule map
     [BimodTensorMap]'s [rm_map_smul] ← [bh_right] of the bimodule map
     [BimodTensor]'s three laws ← [bal_hom_ext]; the identity and
                            composition cases close by [reflexivity]
     [lt_bilin_act]       balance ← **[bm_compat]**, the THIRD use in
                            the file, read in the other direction
                            ([symmetry])
     [lt_act_distr_r]     ← [rm_smul_distr_r] of E's left module
     [lt_act_assoc]       ← [rm_smul_assoc]       (associativity ONLY)
     [lt_act_one]         ← [rm_smul_one]
     [lt_map_bal]         balance ← [be_balance], then the given map's
                            own S-linearity
     [btb_compat]         ← NOTHING; [bal_hom_ext] and one
                            [reflexivity] on generators
     [BimodTensorBimod]'s five right-action laws ← [RTensor]'s own,
                            each with the two arguments swapped, which
                            is the flip [bimodule_right_RMod] performs
     [ta_inner], [ta_binner] balance ← [be_balance] at the OUTER
                            tensor, the inner generator being the
                            module element it acts on
     [ta_outer], [ta_bouter] balance ← [be_balance] at the INNER one,
                            under one [bal_hom_ext]
     [ta_to], [ta_from]'s [rm_map_smul], both round trips and
     [tensor_assoc_iso]'s coherence square ← NOTHING beyond
                            [ta_double_ext]; every generator case
                            closes by [reflexivity]
     [aali_natural]       ← the given natural isomorphism's coherence
                            square and [iso_to_from]
     [adjunction_along_left_iso]'s two naturality clauses ← [A]'s own,
                            after one [aali_natural] and one
                            [comp_assoc]
     [lhs_act]'s [rm_map_smul] ← **[bm_compat]**, the FOURTH and last
                            use in the file
     [lhs_act_assoc]      ← [bm_rsmul_assoc]      (associativity ONLY)
     [lhs_act_one]        ← [bm_rsmul_one]
     [blt_to]'s [rm_map_smul] ← **[be_balance]**, the balance rule read
                            as a law, exactly as in §B
     [blt_from_bal]'s balance ← the given map's own S-linearity
     [hab_lact_assoc], [hab_ract_assoc] ← [rm_smul_assoc] of N and of
                            M, the reversal absorbed by [Ring_op]
     [hab_compat]         ← NOTHING; both sides are the same term
     [hbt_to_hom]'s [rm_map_smul] ← **[be_balance]** again
     [hbt_from_bal]'s balance ← the bimodule map's own R-linearity
     [hbt_from]'s [rm_map_smul] ← [bh_right] of the bimodule map
     [hab_partial_adj]'s two naturality clauses ← NOTHING; both close
                            by [reflexivity], as §B's and §C's do
     [int_mult_bal]       ← [rig_distr_r], [rig_distr_l] and
                            [rig_mul_assoc] of ℤ, as a record literal
                            with no obligation

   THE UNIT AND THE COUNIT ARE THE EXPECTED ONES, ON THE NOSE.
   [bth_unit_is_gen] states that the unit at N, applied to n and then to
   e, IS the generator n ⊗ e, and [bth_counit_is_eval] that the counit
   sends f ⊗ e to f e.  Both close at [eq_refl], not up to ≈.  So do
   [bth_adj_to_is_bth_to] and [bth_adj_from_is_bth_from], which pin the
   two legs of the class's own [adj] field as the named transposes.
   §D's and §E's do too: the composite's unit and counit are the
   DOUBLE generator and DOUBLE evaluation at [eq_refl], the left
   mirror's are the generator and evaluation at [eq_refl], and both
   legs of the associativity comparison return the other bracketing of
   a double generator at [eq_refl].  EVERY [Example] in the file closes
   at [eq_refl]; nowhere is a strict reading sought and settled for ≈.
   Where a strict reading is REFUTED rather than settled for is part
   (c)'s two whole-record identifications — [TensorWith E1 ◯ TensorWith
   E] against [TensorWith (BimodTensorBimod E E1)] and the two hom
   composites — which are different [Functor] records; they are pinned
   as the probe's N10 and N11, and what holds in their place is the
   natural isomorphism, which is what Mac Lane's "describe" asks for.

   AN Ab-ENRICHMENT THAT WAS ONE NEGATION AWAY.
   Instance/Mod/Coextension.v:309 records that the tree has no
   [AbEnriched (RMod R)] and only Instance/Mod.v:809's [Preadditive];
   a whole-tree search for the string "AbEnriched (RMod" returns that
   one line of prose and nothing else.  [RMod_AbEnriched] supplies it
   here in thirteen lines, over [rmod_hom_negate] (the obvious name
   [rmod_hom_neg] is taken by Instance/FdVect/DoubleDual.v:158, a
   collision Instance/Mod/Closed.v:342 also records and works around).
   The payoff is that hom_S(E, M)'s underlying group is
   Adjunction/Additive.v:485's [hom_ab] read at it, so its carrier,
   addition and zero are [RMod_Preadditive]'s own — pinned by
   [hs_group_carrier], [hs_group_plus] and [hs_group_zero] at
   [eq_refl].  It is a plain [Definition], not an [Instance]: this is a
   reading of a hom-setoid, not something resolution should search for.
   Requiring Adjunction/Additive.v costs ONE module on top of what this
   file needs anyway (measured by dropping the [Require] and rerunning
   [coqdep]).

   A RECORD-LITERAL TRAP, MET AND WORKED AROUND SEVEN TIMES.  Writing
   [{| rm_ab := …; rm_smul := … |} : RModObject (Ring_op S)] elaborates
   the scalar argument's type against S and infers the record's ring
   parameter to be S rather than [Ring_op S] — the two being
   convertible — and then asks the associativity field for the WRONG
   multiplication order.  Instance/Mod.v:762-765 records the same trap
   for [bimodule_right_RMod].  Both [RTensor] and [HomSObj] therefore
   name [@Build_RModObject] with its ring argument written out, and so
   do §D's, §E's and §F's — five [@Build_RModObject] literals in all,
   and two [@Build_Bimodule].

   FOUR MORE ELABORATION FINDINGS, ALL MET AND ALL WORKED AROUND.
   (i) [be_gen]'s two arguments do not determine its module
   parameters, so a NESTED [be_gen] — one whose own argument is a term
   built from [bm_left E] where the expected module is
   [bimodule_right_RMod E], or the reverse — must either be applied
   through [refine], so that the conclusion is unified first, or be
   given its parameters explicitly; §D writes [@be_gen S EE …] and
   [@be_add_l S EE N …] at every such site, which is stage 1's finding
   about [@be_balance] and [@bs_gen] one level in.
   (ii) [Arguments] declared INSIDE a [Section] do not survive its
   [End]: outside §C the two projections of [BimodHom] have their
   bimodule arguments EXPLICIT again, so §F restores the settings
   before its first use.
   (iii) A [Program Definition] with NO section variables in scope
   leaves its [Proper] obligation as a goal [intros] cannot enter
   ("No product even after head-reduction"), where the same shape
   inside a [Section] can be entered after the section binders; §G's
   [int_mult_bal] is a record literal instead, which is better anyway —
   every field is a rig law applied and it raises no obligation at all.
   (iv) [unit] is Theory/Adjunction.v:217's, so a witness wanting a
   placeholder type must not write it.

   WHY NOT Instance/Mod/Tensor.v's [TensorMod].  MEASURED, by four
   refutation commands run in a scratch file, each of which fired:
   [TensorMod N (bm_left E)], [@TensorMod R N (bm_left E)],
   [@TensorMod (Ring_op R) N (bm_left E)] and
   [RBilinear N (bm_left E) (bm_left E)] are all rejected, while
   [@TensorMod R (bm_left E) (bm_left E)] is accepted as a control.
   That file's tensor is over ONE ring with the same scalar acting on
   both factors and on the target, so it serves neither handedness of
   Exercise 3.  Worse, and also measured: for [F : Bimodule S R] the
   term [@TensorMod (Ring_op R) N (bimodule_right_RMod F)] IS accepted
   — it is the tensor of two RIGHT R-modules and balances
   (n ⊲ r) ⊗ e against n ⊗ (e ⊲ r), which is not what the page asks
   for.  A reader reaching for [bimodule_right_RMod] to make the types
   fit gets a silently different object.

   THE ISSUE'S "Current state" IS STALE ON EVERY COUNT IT MAKES, and
   the corrections are greps: module categories exist
   (Instance/Mod.v:281 [RMod], :712 [ModR]), the [Bimodule] record
   exists (:718) with [bimodule_right_RMod] at :760 and two witnesses at
   :866 and :878, tensor products exist (Instance/Ab/Tensor.v and
   Instance/Mod/Tensor.v), and Adjunction/Parameter.v carries Theorem 3
   with [ParametrizedAdjunction] at :361 and
   [parametrized_right_adjoint_bifunctor] at :577.  What was genuinely
   absent is narrower and is what this file adds: a search for
   [BimodCat], [BimoduleHom] or [bm_hom] over every `.v` in the tree
   returns ZERO lines outside this file, so there was no category of
   bimodules, no bimodule morphism and no setoid on them; and no tensor
   anywhere pairs a right module with a bimodule.

   MODULE PATH.  The issue suggests Instance/Module/Bimodule.v.  That
   directory does not exist (checked), every module file in the tree
   lives under Instance/Mod/, and the file is registered in _CoqProject
   after Instance/Mod/Coextension.v.  The deviation is deliberate.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK, AND THE ISOLATING
   EXPERIMENT STAGE 1 DEFERRED HAS NOW BEEN RUN — IT REFUTES THAT
   STAGE'S CONJECTURE.  Read the two halves apart, because the block
   alone gives the wrong answer for the equation-free constants and the
   right one for the rest.  Carrying NO universe equation at all —
   every entry of the block a strict [<] or a bound [<=] — are
   [BalTensor], [RTensor], [TensorWith], [BimodCat], [BimodTensor],
   [LTensor], [LTensorWith], [BimodTensorBimod], [btb_left],
   [btb_right], [ta_iso], [bimodule_third_leg], [rmod_lmul] and all
   three [*_preserves_colimits].  Carrying equations are [HomSObj]
   (four), [HomS] and [bimodule_tensor_hom_adjunction] (five),
   [LHomSObj] (five),
   [LHomS] and [bimodule_left_tensor_hom_adjunction] (six),
   [HomAbBimod] (five), [tensor_assoc_iso] (two),
   [adjunction_along_left_iso] (one), and the part-(c) composite,
   [bimodule_tensor_bimod_adjunction] and [bimodule_hom_composite_iso]
   (ten).  There is no word-bounded [Set] in the block or binder of
   any of the 440 constants; the only [Set] tokens in the whole [About]
   dump are the motive sorts of the two eliminators [bsum_rec] and
   [bs_eq_rec].

   Stage 1 conjectured that the four on [HomSObj] enter at the
   APPLICATION [hom_ab (RMod_AbEnriched (Ring_op S)) …], and that is
   FALSE.  Measured, one donor at a time: [hom_ab] alone, [AbEnriched]
   alone, [RMod] alone and [RMod_AbEnriched] alone each carry NO
   equation; and the application itself, written at TOP LEVEL with the
   two rings and the bimodule as ordinary parameters, carries none
   either.  Put the SAME body in a [Section] whose [Context] binds the
   bimodule and all four appear.  So the donor is the SECTION VARIABLE:
   a [Context] fixes its universes once, and the elaboration of the
   body then EQUATES where the same term with a parameter merely
   BOUNDS.  The file confirms it against itself — [bimodule_third_leg],
   the only §F constant declared at top level, carries no equation
   while [bimodule_two_variable_adjunction], the same machinery inside
   a [Section], carries one, and [rmod_lmul] (top level) carries none
   where [bal_gen_left] (inside a section) carries two.  Nothing is
   claimed unavoidable: rewriting §B, §E and §F without sections would
   restructure them entirely and was not attempted.  What [hom_ab] and
   [AbEnriched] DO force, in their BINDERS rather than their blocks, is
   a category whose hom and proof universes coincide; [AbEnriched]'s is
   pinned in Test/ProbeBimodule401.v as a formability negative, while
   the [hom_ab] negative there fires at its [AbEnriched] ARGUMENT, so
   [hom_ab]'s own contribution is UNKNOWN, not measured.

   AXIOMS.  440/440 constants report "Closed under the global context",
   with zero [Axioms:] lines.  The criterion: entries of [Print Module]
   sit at exactly five-space indent, giving 198 [Definition] + 220
   [Parameter] — the printer's rendering of an opaque constant, a
   display convention and not an axiom — + 2 [Inductive] + 2 [Record] =
   422, and the [Inductive] and [Record] heads WRAP onto their own
   line, so a regex anchored to the keyword AND the name on one line
   harvests neither of the four; to those add the sixteen inductive
   constructors and the two [Build_*], which [Print Module] lists only
   inside an [Inductive] body or after a [Record]'s [:=].  The
   422 include the file's [Program] obligations and the eight
   eliminators no source sweep sees.  Every one of the 440 was queried
   by fully qualified name.  The 220 [Parameter] entries are exactly
   the file's 220 [Qed] tokens, which is a cross-check on the reading
   of that display convention rather than a second measurement.

   DEFINED.  Six [Defined] tokens against 220 [Qed], and each was
   flipped ALONE to [Qed] to see which are load-bearing: THREE are —
   [bimodule_tensor_hom_adjunction], [adjunction_along_left_iso] and
   [bimodule_left_tensor_hom_adjunction], whose transparency is what
   the [eq_refl] readbacks of the unit, the counit and the transported
   transpose reduce through — and three are not
   ([bt_partial_adj], [tensor_assoc_iso], [hab_partial_adj]), kept
   [Defined] by the data convention alone.

   NAMES.  All 440 were swept whole-word against every `.v` in the tree
   before use; the sweep is clean.  Three collisions were avoided by
   construction: [rmod_hom_neg], taken as above; [HomFrom], which
   Functor/Hom/Limit.v owns and which the brief had suggested for the
   hom functor — hence [HomS] and [HomSObj]; and [unit], which
   Theory/Adjunction.v:217 owns, so §G's witnesses name no [unit] and
   the probe's control uses [nat] where a placeholder is wanted.

   CLOSURE.  93 modules, excluding the file itself, measured with
   [coqdep -sort]; the probe's is 95.  Drop-one marginals, each by
   deleting the [Require] and rerunning [coqdep]: Adjunction/Parameter
   11, Adjunction/Compose 2, Adjunction/Additive 1,
   Adjunction/Continuity 1, Instance/Mod 1, and every other [Require]
   ZERO — including Adjunction/Right and Structure/Limit/Preservation,
   which arrive with Parameter and Continuity respectively.  §D-§F cost
   six modules over stage 1's 87.  Instance/Mod/Extension.v is NOT
   required — it would add twelve more (measured: 94 to 106) through
   the Grothendieck and Displayed stack for nothing this file needs —
   and
   Instance/Mod/Closed.v is not required either.  Its TECHNIQUE (an
   action supplied by the mediator of a biadditive map) is reused; none
   of its code is.

   THE BOUNDARY PROBE.  Test/ProbeBimodule401.v carries 18 refutation
   commands = 1 instrument check + 17 negatives of THREE kinds told
   apart by the error TEXT: six CONVERSION, nine TYPING and two
   FORMABILITY.  Each was stripped ONE AT A TIME into its own scratch
   copy, compiled alone, and its whole error read; guard coverage is
   complete (50 identifiers named inside a refutation command, 40 of
   them also named outside one, the ten others being the command
   keyword, one bound variable, the seven names of the refuted
   declarations and the instrument's absent name); and the rename
   simulation is 5/5, every break landing on a [Check] line of the
   guard block.  The refutation commands live there and not here: this
   file contributes ZERO lines to the [todo] target, the probe 28.

   WHAT IS NOT DELIVERED IN THIS FILE.  The following are declared
   remainder, not claims about the mathematics.

     - Riehl's GENERAL three-ring biclosed form, _R Mod_S × _S Mod_T →
       _R Mod_T with a left closure Hom_R and a right closure Hom_T.
       What §F delivers is the second closure of [BimodTensor] at MAC
       LANE's handedness, which is the honest reading this tree can
       state: a right R-module is not a (ℤ,R)-bimodule here —
       [bm_left] demands [RModObject Int_Ring] where a right R-module
       is [RModObject (Ring_op R)] — so the ℤ-instance route is closed
       off (pinned as the probe's N8 and N9), and the one in-tree
       passage, Instance/Rng/Mod.v:675's [ZRestrict], is pinned at
       [RingObject@{Set Set Set}].
     - A finite-colimit or right-exactness vocabulary.  A whole-tree
       sweep ([right.?exact] 0 hits, [finitely-cocomplete] 3, [finite
       colimit] 3, all prose in unrelated headers) finds none, and
       the catalogue item that would supply it (#546) is OPEN, so
       Riehl's Corollary 4.6.10 is rendered as preservation of ALL
       colimits — which is STRICTLY STRONGER than right exactness and
       is not the same statement.  Corollary 4.6.9's additivity clause
       is not delivered either.
     - The one-ring tensor-hom parametrized adjunction that
       Adjunction/Parameter.v:200-231 discloses as its own follow-on.
       It compiles out of tree — twenty-two lines of substance, four
       declarations, re-verified at this commit — over [ModTensor]
       (Instance/Mod/Monoidal.v:546) and [HomMod]
       (Instance/Mod/Closed.v:448) with that file's [exp_iso_Mod],
       [cur_natural_V] and [cur_natural_X]; it is NOT shipped here,
       because it is Mac Lane's SECOND example rather than Exercise 3
       and because requiring those two modules would cost this file
       nine more (measured: 94 to 103 modules).
     - Any coherence for the tensor of two bimodules beyond the
       comparison itself: no pentagon, no unit bimodule, no bicategory
       of rings and bimodules, and no naturality of
       [tensor_assoc_iso] in E or E1 — only in the module variable,
       which is what its [Functor_Setoid] statement quantifies over.
     - Any relation between [HomAbBimod] and [HomSObj], between
       [adjunction_along_left_iso] and any other transport, or between
       the two readings of the composite's unit beyond the two
       statements that name them.
     - Limit preservation for the two hom functors.  Only the
       colimit side is read off, and only for the three left adjoints.
     - Any universe claim beyond what is measured above; in
       particular nothing is claimed unavoidable, and the section
       finding is an attribution, not a repair.
     - Nothing is registered as an [Instance] except the two the
       categorical structure needs, [bs_eq_Equivalence] and
       [BimodHom_Setoid], both [#[export]] and both resolvable
       downstream (measured in a consumer); [RMod_AbEnriched] is a plain
       [Definition] and no other construction becomes resolvable. *)

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
(* The integer witness of §G needs the [Z] scope; Theory/Algebra/Rig.v:15
   takes the same import, this is the spelling the tree uses, and on Rocq
   9.1 it emits the tree-wide "From Coq" deprecation warning, as that
   file does. *)
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(** ** A. The balanced tensor of a right module and a left module *)

Section BalancedTensor.

Context {X : RingObject}.

(* [N] is a RIGHT X-module and [M] a LEFT X-module.  The two scalar
   arguments are of the SAME type: the carrier of the opposite ring's
   additive setoid is the carrier of the ring's, on the nose, and that is
   what lets the balance rule below be stated with no transport. *)
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Local Notation XC := (carrier (rig_setoid (ring_rig X))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).
Local Notation MC := (carrier (cmon_setoid (rm_ab M))).

Example bal_scalars_agree :
  carrier (rig_setoid (ring_rig (Ring_op X)))
    = carrier (rig_setoid (ring_rig X)) := eq_refl.

(* Formal sums over the two carriers: generators, zero, sum, negation.
   There is NO formal scalar former; the result is an abelian group, and
   any residual module structure is bolted on afterwards through the
   universal property. *)
Inductive bsum : Type :=
  | bs_gen  : NC → MC → bsum
  | bs_zero : bsum
  | bs_plus : bsum → bsum → bsum
  | bs_neg  : bsum → bsum.

(* The quotienting relation: Instance/Ab/Tensor.v's eleven constructors
   plus ONE balance rule, (n · x) ⊗ m ≈ n ⊗ (x · m).  Reflexivity is
   derived. *)
Inductive bs_eq : bsum → bsum → Type :=
  | be_gen {n n' : NC} {m m' : MC} :
      n ≈ n' → m ≈ m' → bs_eq (bs_gen n m) (bs_gen n' m')
  | be_plus {s s' t t'} :
      bs_eq s s' → bs_eq t t' → bs_eq (bs_plus s t) (bs_plus s' t')
  | be_neg {s s'} : bs_eq s s' → bs_eq (bs_neg s) (bs_neg s')
  | be_assoc (s t u : bsum) :
      bs_eq (bs_plus (bs_plus s t) u) (bs_plus s (bs_plus t u))
  | be_comm (s t : bsum) : bs_eq (bs_plus s t) (bs_plus t s)
  | be_zero_l (s : bsum) : bs_eq (bs_plus bs_zero s) s
  | be_neg_l (s : bsum) : bs_eq (bs_plus (bs_neg s) s) bs_zero
  | be_add_l (n n' : NC) (m : MC) :
      bs_eq (bs_gen (cmon_plus (rm_ab N) n n') m)
            (bs_plus (bs_gen n m) (bs_gen n' m))
  | be_add_r (n : NC) (m m' : MC) :
      bs_eq (bs_gen n (cmon_plus (rm_ab M) m m'))
            (bs_plus (bs_gen n m) (bs_gen n m'))
  | be_balance (x : XC) (n : NC) (m : MC) :
      bs_eq (bs_gen (rm_smul N x n) m) (bs_gen n (rm_smul M x m))
  | be_sym {s t} : bs_eq s t → bs_eq t s
  | be_trans {s t u} : bs_eq s t → bs_eq t u → bs_eq s u.

Lemma bs_refl (s : bsum) : bs_eq s s.
Proof.
  induction s.
  - exact (be_gen (reflexivity _) (reflexivity _)).
  - exact (be_trans (be_sym (be_zero_l bs_zero)) (be_zero_l bs_zero)).
  - exact (be_plus IHs1 IHs2).
  - exact (be_neg IHs).
Qed.

Lemma bs_eq_Equivalence : Equivalence bs_eq.
Proof.
  constructor.
  - exact bs_refl.
  - exact (fun s t => be_sym).
  - exact (fun s t u => be_trans).
Qed.

Definition bs_Setoid : Setoid bsum := {|
  equiv        := bs_eq;
  setoid_equiv := bs_eq_Equivalence
|}.

(* The balanced tensor as an abelian group: every group law is a
   constructor of the relation. *)
Definition BalTensor : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := bsum; is_setoid := bs_Setoid |};
    cmon_zero := bs_zero;
    cmon_plus := bs_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => be_plus Hs Ht;
    cmon_plus_assoc := be_assoc;
    cmon_plus_comm := be_comm;
    cmon_plus_zero_l := be_zero_l
  |};
  ab_neg := bs_neg;
  ab_neg_respects := fun _ _ Hs => be_neg Hs;
  ab_neg_left := be_neg_l
|}.

(** ** Balanced biadditive maps and the universal property *)

(* A map into an abelian group, additive in each variable and balanced
   over X.  Preservation of zero and negation in each variable follows,
   as always for monoid maps between groups, and is not demanded. *)
Record BalBiadditive (A : AbObject) := {
  bal_map : NC → MC → carrier (cmon_setoid A);
  bal_respects : Proper (equiv ==> equiv ==> equiv) bal_map;
  bal_add_l (n n' : NC) (m : MC) :
    bal_map (cmon_plus (rm_ab N) n n') m
      ≈ cmon_plus A (bal_map n m) (bal_map n' m);
  bal_add_r (n : NC) (m m' : MC) :
    bal_map n (cmon_plus (rm_ab M) m m')
      ≈ cmon_plus A (bal_map n m) (bal_map n m');
  bal_balance (x : XC) (n : NC) (m : MC) :
    bal_map (rm_smul N x n) m ≈ bal_map n (rm_smul M x m)
}.

Arguments bal_map {A} _ _ _.
Arguments bal_respects {A} _.
Arguments bal_add_l {A} _ _ _ _.
Arguments bal_add_r {A} _ _ _ _.
Arguments bal_balance {A} _ _ _ _.

(* The universal balanced map: the generator former itself. *)
Definition bal_gen : BalBiadditive BalTensor :=
  @Build_BalBiadditive BalTensor bs_gen
    (fun _ _ Hn _ _ Hm => be_gen Hn Hm)
    be_add_l be_add_r be_balance.

(* The mediator: fold a formal sum through the target's operations.  It
   computes on constructors. *)
Fixpoint bal_med_fun {A : AbObject} (β : BalBiadditive A) (s : bsum) :
  carrier (cmon_setoid A) :=
  match s with
  | bs_gen n m  => bal_map β n m
  | bs_zero     => cmon_zero A
  | bs_plus s t => cmon_plus A (bal_med_fun β s) (bal_med_fun β t)
  | bs_neg s    => ab_neg A (bal_med_fun β s)
  end.

Lemma bal_med_respects {A : AbObject} (β : BalBiadditive A) (s t : bsum) :
  bs_eq s t → bal_med_fun β s ≈ bal_med_fun β t.
Proof.
  intro He; induction He; simpl.
  - exact (bal_respects β _ _ e _ _ e0).
  - exact (cmon_plus_respects A _ _ IHHe1 _ _ IHHe2).
  - exact (ab_neg_respects A _ _ IHHe).
  - exact (cmon_plus_assoc A _ _ _).
  - exact (cmon_plus_comm A _ _).
  - exact (cmon_plus_zero_l A _).
  - exact (ab_neg_left A _).
  - exact (bal_add_l β _ _ _).
  - exact (bal_add_r β _ _ _).
  - exact (bal_balance β _ _ _).
  - exact (symmetry IHHe).
  - exact (transitivity IHHe1 IHHe2).
Qed.

Program Definition bal_med {A : AbObject} (β : BalBiadditive A) :
  AbHom BalTensor A := {|
  cmon_map := {| morphism := bal_med_fun β |}
|}.
Next Obligation.
  intros A β s t He; exact (bal_med_respects β s t He).
Qed.
Next Obligation. intros A β; simpl; reflexivity. Qed.
Next Obligation. intros A β s t; simpl; reflexivity. Qed.

Example bal_med_gen {A : AbObject} (β : BalBiadditive A)
  (n : NC) (m : MC) :
  cmon_map (bal_med β) (bs_gen n m) = bal_map β n m := eq_refl.

(* Uniqueness in its consumable form: homomorphisms out of the balanced
   tensor that agree on generators agree everywhere.  The [bs_neg] case
   is Instance/Ab.v's [ab_map_neg]. *)
Lemma bal_hom_ext {A : AbObject} (f g : AbHom BalTensor A) :
  (∀ (n : NC) (m : MC),
      cmon_map f (bs_gen n m) ≈ cmon_map g (bs_gen n m)) →
  ∀ s : bsum, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen s; induction s as [n m| |s1 IHs1 s2 IHs2|s IHs].
  - exact (Hgen n m).
  - exact (transitivity (cmon_map_zero f)
             (symmetry (cmon_map_zero g))).
  - refine (transitivity (cmon_map_plus f s1 s2) _).
    refine (transitivity _ (symmetry (cmon_map_plus g s1 s2))).
    exact (cmon_plus_respects A _ _ IHs1 _ _ IHs2).
  - refine (transitivity (ab_map_neg f s) _).
    refine (transitivity _ (symmetry (ab_map_neg g s))).
    exact (ab_neg_respects A _ _ IHs).
Qed.

Lemma bal_med_unique {A : AbObject} (β : BalBiadditive A)
  (f : AbHom BalTensor A) :
  (∀ (n : NC) (m : MC),
      cmon_map f (bs_gen n m) ≈ bal_map β n m) →
  f ≈ bal_med β.
Proof.
  intros Hgen s.
  refine (bal_hom_ext f (bal_med β) _ s).
  intros n m; exact (Hgen n m).
Qed.

(* A generator with a zero coordinate is the zero of the tensor.  Both
   halves are needed downstream: the transposes of the adjunction are
   additive because of them. *)
Lemma bal_gen_zero_l (m : MC) :
  (bs_gen (cmon_zero (rm_ab N)) m : carrier (cmon_setoid BalTensor))
    ≈ cmon_zero BalTensor.
Proof.
  apply (ab_cancel_l BalTensor (bs_gen (cmon_zero (rm_ab N)) m)).
  exact (be_trans
           (be_trans
              (be_sym (be_add_l (cmon_zero (rm_ab N))
                                (cmon_zero (rm_ab N)) m))
              (be_gen (cmon_plus_zero_l (rm_ab N) (cmon_zero (rm_ab N)))
                      (reflexivity m)))
           (be_sym (cmon_plus_zero_r BalTensor
                      (bs_gen (cmon_zero (rm_ab N)) m)))).
Qed.

Lemma bal_gen_zero_r (n : NC) :
  (bs_gen n (cmon_zero (rm_ab M)) : carrier (cmon_setoid BalTensor))
    ≈ cmon_zero BalTensor.
Proof.
  apply (ab_cancel_l BalTensor (bs_gen n (cmon_zero (rm_ab M)))).
  exact (be_trans
           (be_trans
              (be_sym (be_add_r n (cmon_zero (rm_ab M))
                                  (cmon_zero (rm_ab M))))
              (be_gen (reflexivity n)
                      (cmon_plus_zero_l (rm_ab M) (cmon_zero (rm_ab M)))))
           (be_sym (cmon_plus_zero_r BalTensor
                      (bs_gen n (cmon_zero (rm_ab M)))))).
Qed.

End BalancedTensor.

Arguments bsum {X} N M.
Arguments bs_gen {X N M} n m.
Arguments bs_zero {X N M}.
Arguments bs_plus {X N M} s t.
Arguments bs_neg {X N M} s.
Arguments bs_eq {X N M} s t.
Arguments bs_refl {X N M} s.
Arguments be_gen {X N M n n' m m'} _ _.
Arguments be_plus {X N M s s' t t'} _ _.
Arguments be_neg {X N M s s'} _.
Arguments be_assoc {X N M} s t u.
Arguments be_comm {X N M} s t.
Arguments be_zero_l {X N M} s.
Arguments be_neg_l {X N M} s.
Arguments be_add_l {X N M} n n' m.
Arguments be_add_r {X N M} n m m'.
Arguments be_balance {X N M} x n m.
Arguments be_sym {X N M s t} _.
Arguments be_trans {X N M s t u} _ _.

#[export] Existing Instance bs_eq_Equivalence.
Arguments BalTensor {X} N M.
Arguments BalBiadditive {X} N M A.
Arguments bal_map {X N M A} _ _ _.
Arguments bal_respects {X N M A} _.
Arguments bal_add_l {X N M A} _ _ _ _.
Arguments bal_add_r {X N M A} _ _ _ _.
Arguments bal_balance {X N M A} _ _ _ _.
Arguments bal_gen {X N M}.
Arguments bal_med_fun {X N M A} β s.
Arguments bal_med {X N M A} β.
Arguments bal_med_gen {X N M A} β n m.
Arguments bal_hom_ext {X N M A} f g _ s.
Arguments bal_med_unique {X N M A} β f _.
Arguments bal_gen_zero_l {X} N M m.
Arguments bal_gen_zero_r {X} N M n.

(** ** B. Mac Lane part (a): − ⊗_R E and hom_S(E, −) *)

(** *** The Ab-enrichment of a module category *)

(* Instance/Mod.v supplies [rmod_hom_add] and [rmod_hom_zero] but no
   negation, and the name [rmod_hom_neg] is taken by
   Instance/FdVect/DoubleDual.v:158 (Instance/Mod/Closed.v:342 records
   the same collision and works around it with a file-local name). *)
Program Definition rmod_hom_negate {R : RingObject} {M N : RModObject R}
        (f : RModHom M N) : RModHom M N := {|
  rm_hom := ab_hom_neg (rm_hom f)
|}.
Next Obligation.
  intros R M N f r m; simpl.
  rewrite (rm_map_smul f r m).
  symmetry; apply rm_smul_neg_r.
Qed.

(* Instance/Mod/Coextension.v:308-310 records that the tree has no
   [AbEnriched (RMod R)], only Instance/Mod.v:809's [Preadditive].  It
   is one negation away, and the hom-group below is Adjunction/
   Additive.v's [hom_ab] read at it, so nothing is rebuilt.  A plain
   [Definition], not an [Instance]: this is a reading of a hom-setoid,
   not something resolution should search for. *)
Program Definition RMod_AbEnriched (R : RingObject) :
  AbEnriched (RMod R) := {|
  abenriched_preadditive := RMod_Preadditive R;
  abneg := fun M N => @rmod_hom_negate R M N
|}.
Next Obligation.
  intros R M N f g Hfg a; simpl.
  exact (ab_neg_respects N _ _ (Hfg a)).
Qed.
Next Obligation.
  intros R M N f a; simpl.
  exact (ab_neg_right N (cmon_map (rm_hom f) a)).
Qed.

Section BimoduleTensorHom.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

(** *** The right S-action on N ⊗_R E *)

(* The action of s is the mediator of (n, e) ↦ n ⊗ (e ⊲ s).  The ONLY
   law of the bimodule the balance clause consumes is [bm_compat]; no
   centrality and no commutativity appears anywhere in this section. *)
Program Definition rt_bilin_act (N : RModObject (Ring_op R)) (s : SC) :
  BalBiadditive N (bm_left E) (BalTensor N (bm_left E)) := {|
  bal_map := fun n e => bs_gen n (bm_rsmul E e s)
|}.
Next Obligation.
  intros N s n n' Hn e e' He.
  exact (be_gen Hn (bm_rsmul_respects E e e' He s s (reflexivity s))).
Qed.
Next Obligation.
  intros N s n n' e; exact (be_add_l n n' (bm_rsmul E e s)).
Qed.
Next Obligation.
  intros N s n e e'.
  exact (be_trans
           (be_gen (reflexivity n) (bm_rsmul_distr_l E e e' s))
           (be_add_r n (bm_rsmul E e s) (bm_rsmul E e' s))).
Qed.
Next Obligation.
  intros N s r n e.
  exact (be_trans
           (be_balance r n (bm_rsmul E e s))
           (be_sym (be_gen (reflexivity n) (bm_compat E r e s)))).
Qed.

Definition rt_smul (N : RModObject (Ring_op R)) (s : SC) :
  AbHom (BalTensor N (bm_left E)) (BalTensor N (bm_left E)) :=
  bal_med (rt_bilin_act N s).

Definition rt_act (N : RModObject (Ring_op R)) (s : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  carrier (cmon_setoid (BalTensor N (bm_left E))) :=
  cmon_map (rt_smul N s) x.

Example rt_act_gen (N : RModObject (Ring_op R)) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  rt_act N s (bs_gen n e) = bs_gen n (bm_rsmul E e s) := eq_refl.

(** *** The four module laws, each by agreement on generators *)

Lemma rt_act_scalar (N : RModObject (Ring_op R)) (s s' : SC) :
  s ≈ s' → ∀ x, rt_act N s x ≈ rt_act N s' x.
Proof.
  intros Hs x.
  refine (bal_hom_ext (rt_smul N s) (rt_smul N s') _ x).
  intros n e.
  exact (be_gen (reflexivity n)
           (bm_rsmul_respects E e e (reflexivity e) s s' Hs)).
Qed.

Lemma rt_act_respects (N : RModObject (Ring_op R)) :
  Proper (equiv ==> equiv ==> equiv) (rt_act N).
Proof.
  intros s s' Hs x y Hxy.
  transitivity (rt_act N s y).
  - exact (proper_morphism (cmon_map (rt_smul N s)) x y Hxy).
  - exact (rt_act_scalar N s s' Hs y).
Qed.

Lemma rt_act_distr_r (N : RModObject (Ring_op R)) (s s' : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_add (ring_rig S) s s') x
    ≈ cmon_plus (BalTensor N (bm_left E)) (rt_act N s x) (rt_act N s' x).
Proof.
  refine (bal_hom_ext (rt_smul N (rig_add (ring_rig S) s s'))
            (ab_hom_add (rt_smul N s) (rt_smul N s')) _ x).
  intros n e.
  exact (be_trans
           (be_gen (reflexivity n) (bm_rsmul_distr_r E e s s'))
           (be_add_r n (bm_rsmul E e s) (bm_rsmul E e s'))).
Qed.

(* The associativity law is stated over [Ring_op S], where the product
   [rig_mul (ring_rig (Ring_op S)) s s'] reduces to [rig_mul S s' s]; on
   generators the two sides are e ⊲ (s' s) and (e ⊲ s') ⊲ s, which is
   [bm_rsmul_assoc] verbatim.  Associativity ONLY. *)
Lemma rt_act_assoc (N : RModObject (Ring_op R)) (s s' : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_mul (ring_rig (Ring_op S)) s s') x
    ≈ rt_act N s (rt_act N s' x).
Proof.
  refine (bal_hom_ext (rt_smul N (rig_mul (ring_rig (Ring_op S)) s s'))
            (cmon_hom_compose (rt_smul N s) (rt_smul N s')) _ x).
  intros n e.
  exact (be_gen (reflexivity n) (bm_rsmul_assoc E e s' s)).
Qed.

Lemma rt_act_one (N : RModObject (Ring_op R))
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_one (ring_rig S)) x ≈ x.
Proof.
  refine (bal_hom_ext (rt_smul N (rig_one (ring_rig S)))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e.
  exact (be_gen (reflexivity n) (bm_rsmul_one E e)).
Qed.

(* N ⊗_R E as an object of [ModR S].  The constructor is named
   explicitly with its ring argument: a record literal here elaborates
   the scalar argument's type against [S] and infers the parameter to be
   [S] rather than [Ring_op S], which silently asks the associativity
   field for the WRONG multiplication order.  This is the trap
   Instance/Mod.v:762-765 records for [bimodule_right_RMod]. *)
Definition RTensor (N : RModObject (Ring_op R)) :
  RModObject (Ring_op S) :=
  @Build_RModObject (Ring_op S)
    (BalTensor N (bm_left E))
    (rt_act N)
    (rt_act_respects N)
    (fun s x y => cmon_map_plus (rt_smul N s) x y)
    (rt_act_distr_r N)
    (rt_act_assoc N)
    (rt_act_one N).

Example rt_carrier (N : RModObject (Ring_op R)) :
  rm_ab (RTensor N) = BalTensor N (bm_left E) := eq_refl.

Example rt_zero (N : RModObject (Ring_op R)) :
  cmon_zero (rm_ab (RTensor N)) = bs_zero := eq_refl.

Example rt_plus (N : RModObject (Ring_op R))
  (x y : carrier (cmon_setoid (rm_ab (RTensor N)))) :
  cmon_plus (rm_ab (RTensor N)) x y = bs_plus x y := eq_refl.

Example rt_smul_gen (N : RModObject (Ring_op R)) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  rm_smul (RTensor N) s (bs_gen n e) = bs_gen n (bm_rsmul E e s)
  := eq_refl.

(** *** The arrow action, and the functor − ⊗_R E *)

Program Definition rt_map_bal {N N' : RModObject (Ring_op R)}
  (f : RModHom N N') :
  BalBiadditive N (bm_left E) (BalTensor N' (bm_left E)) := {|
  bal_map := fun n e => bs_gen (cmon_map (rm_hom f) n) e
|}.
Next Obligation.
  intros N N' f n n' Hn e e' He.
  exact (be_gen (proper_morphism (cmon_map (rm_hom f)) n n' Hn) He).
Qed.
Next Obligation.
  intros N N' f n n' e.
  exact (be_trans
           (be_gen (cmon_map_plus (rm_hom f) n n') (reflexivity e))
           (be_add_l (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom f) n') e)).
Qed.
Next Obligation.
  intros N N' f n e e'.
  exact (be_add_r (cmon_map (rm_hom f) n) e e').
Qed.
Next Obligation.
  intros N N' f r n e.
  exact (be_trans
           (be_gen (rm_map_smul f r n) (reflexivity e))
           (be_balance r (cmon_map (rm_hom f) n) e)).
Qed.

Definition rt_map_ab {N N' : RModObject (Ring_op R)} (f : RModHom N N') :
  AbHom (BalTensor N (bm_left E)) (BalTensor N' (bm_left E)) :=
  bal_med (rt_map_bal f).

Program Definition RTensorMap {N N' : RModObject (Ring_op R)}
  (f : N ~{ModR R}~> N') : RTensor N ~{ModR S}~> RTensor N' := {|
  rm_hom := rt_map_ab f
|}.
Next Obligation.
  intros N N' f s x.
  refine (bal_hom_ext (cmon_hom_compose (rt_map_ab f) (rt_smul N s))
            (cmon_hom_compose (rt_smul N' s) (rt_map_ab f)) _ x).
  intros n e; reflexivity.
Qed.

Program Definition TensorWith : ModR R ⟶ ModR S := {|
  fobj := RTensor;
  fmap := @RTensorMap
|}.
Next Obligation.
  intros N N' f g Hfg x.
  refine (bal_hom_ext (rt_map_ab f) (rt_map_ab g) _ x).
  intros n e.
  exact (be_gen (Hfg n) (reflexivity e)).
Qed.
Next Obligation.
  intros N x.
  refine (bal_hom_ext (rt_map_ab (@id (ModR R) N))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e; reflexivity.
Qed.
Next Obligation.
  intros N N' N'' f g x.
  refine (bal_hom_ext (rt_map_ab (f ∘ g))
            (cmon_hom_compose (rt_map_ab f) (rt_map_ab g)) _ x).
  intros n e; reflexivity.
Qed.

Example tw_fobj (N : RModObject (Ring_op R)) :
  fobj[TensorWith] N = RTensor N := eq_refl.

Example tw_fmap_gen {N N' : RModObject (Ring_op R)}
  (f : N ~{ModR R}~> N') (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (fmap[TensorWith] f)) (bs_gen n e)
    = bs_gen (cmon_map (rm_hom f) n) e := eq_refl.

(** *** hom_S(E, M) and its right R-action *)

(* The underlying abelian group is Adjunction/Additive.v's [hom_ab] read
   at the enrichment above, so its carrier, zero, addition and negation
   are [RMod_Preadditive]'s own; nothing is rebuilt. *)
Definition hs_group (M : RModObject (Ring_op S)) : AbObject :=
  hom_ab (RMod_AbEnriched (Ring_op S)) EE M.

Example hs_group_carrier (M : RModObject (Ring_op S)) :
  carrier (cmon_setoid (hs_group M)) = (EE ~{ModR S}~> M) := eq_refl.

Example hs_group_plus (M : RModObject (Ring_op S)) :
  cmon_plus (hs_group M) = @rmod_hom_add (Ring_op S) EE M := eq_refl.

Example hs_group_zero (M : RModObject (Ring_op S)) :
  cmon_zero (hs_group M) = @rmod_hom_zero (Ring_op S) EE M := eq_refl.

(* The right R-action, by TRANSLATION through E's LEFT R-action:
   (f ⊲ r)(e) = f (r · e).  This is Instance/Mod/Coextension.v's idiom
   (:33), with the translating action supplied by the bimodule instead
   of by the ring's own multiplication. *)
Program Definition hs_act (M : RModObject (Ring_op S)) (r : RC)
  (f : EE ~{ModR S}~> M) : EE ~{ModR S}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom f) (rm_smul (bm_left E) r e) |} |}
|}.
Next Obligation.
  intros M r f e e' He.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_respects (bm_left E) r r (reflexivity r) e e' He)).
Qed.
Next Obligation.
  intros M r f; simpl.
  transitivity (cmon_map (rm_hom f) (cmon_zero (rm_ab (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_zero_r (bm_left E) r)).
  - exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros M r f e e'; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (rm_smul (bm_left E) r e)
                     (rm_smul (bm_left E) r e'))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_distr_l (bm_left E) r e e')).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.
Next Obligation.
  (* [rm_map_smul] for the translated map: the ONLY use of [bm_compat]
     in this block, followed by [f]'s own linearity. *)
  intros M r f s e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (bm_rsmul E (rm_smul (bm_left E) r e) s)).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (symmetry (bm_compat E r e s))).
  - exact (rm_map_smul f s (rm_smul (bm_left E) r e)).
Qed.

Example hs_act_at (M : RModObject (Ring_op S)) (r : RC)
  (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (hs_act M r f)) e
    = cmon_map (rm_hom f) (rm_smul (bm_left E) r e) := eq_refl.

Lemma hs_act_respects (M : RModObject (Ring_op S)) :
  Proper (equiv ==> equiv ==> equiv) (hs_act M).
Proof.
  intros r r' Hr f g Hfg e; simpl.
  transitivity (cmon_map (rm_hom f) (rm_smul (bm_left E) r' e)).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_respects (bm_left E) r r' Hr e e (reflexivity e))).
  - exact (Hfg _).
Qed.

Lemma hs_act_distr_l (M : RModObject (Ring_op S)) (r : RC)
  (f g : EE ~{ModR S}~> M) :
  hs_act M r (cmon_plus (hs_group M) f g)
    ≈ cmon_plus (hs_group M) (hs_act M r f) (hs_act M r g).
Proof. intro e; reflexivity. Qed.

Lemma hs_act_distr_r (M : RModObject (Ring_op S)) (r r' : RC)
  (f : EE ~{ModR S}~> M) :
  hs_act M (rig_add (ring_rig R) r r') f
    ≈ cmon_plus (hs_group M) (hs_act M r f) (hs_act M r' f).
Proof.
  intro e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (rm_smul (bm_left E) r e)
                     (rm_smul (bm_left E) r' e))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_distr_r (bm_left E) r r' e)).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.

(* Associativity ONLY: at e the two sides are f ((r' r) · e) and
   f (r' · (r · e)), and [rm_smul_assoc] of E's LEFT module is all that
   is consumed. *)
Lemma hs_act_assoc (M : RModObject (Ring_op S)) (r r' : RC)
  (f : EE ~{ModR S}~> M) :
  hs_act M (rig_mul (ring_rig (Ring_op R)) r r') f
    ≈ hs_act M r (hs_act M r' f).
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_assoc (bm_left E) r' r e)).
Qed.

Lemma hs_act_one (M : RModObject (Ring_op S)) (f : EE ~{ModR S}~> M) :
  hs_act M (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_one (bm_left E) e)).
Qed.

Definition HomSObj (M : RModObject (Ring_op S)) :
  RModObject (Ring_op R) :=
  @Build_RModObject (Ring_op R)
    (hs_group M)
    (hs_act M)
    (hs_act_respects M)
    (hs_act_distr_l M)
    (hs_act_distr_r M)
    (hs_act_assoc M)
    (hs_act_one M).

(** *** The arrow action, and the functor hom_S(E, −) *)

Program Definition hs_map_ab {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') : AbHom (hs_group M) (hs_group M') := {|
  cmon_map := {| morphism := fun f =>
    (rmod_hom_compose g f : EE ~{ModR S}~> M') |}
|}.
Next Obligation.
  intros M M' g f f' Hf e; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf e)).
Qed.
Next Obligation.
  intros M M' g e; simpl.
  exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' e; simpl.
  exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition HomSMap {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') : HomSObj M ~{ModR R}~> HomSObj M' := {|
  rm_hom := hs_map_ab g
|}.
Next Obligation. intros M M' g r f e; reflexivity. Qed.

Program Definition HomS : ModR S ⟶ ModR R := {|
  fobj := HomSObj;
  fmap := @HomSMap
|}.
Next Obligation.
  intros M M' g g' Hg f e; simpl.
  exact (Hg _).
Qed.
Next Obligation. intros M f e; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f e; reflexivity. Qed.

Example hs_fobj (M : RModObject (Ring_op S)) :
  fobj[HomS] M = HomSObj M := eq_refl.

Example hs_fmap_at {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (fmap[HomS] g)) f)) e
    = cmon_map (rm_hom g) (cmon_map (rm_hom f) e) := eq_refl.

(** *** The two transposes and the adjunction *)

Program Definition bth_to_inner {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) : EE ~{ModR S}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom g) (bs_gen n e) |} |}
|}.
Next Obligation.
  intros N M g n e e' He.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (be_gen (reflexivity n) He)).
Qed.
Next Obligation.
  intros N M g n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r N (bm_left E) n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n e e'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (bs_gen n e) (bs_gen n e'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (be_add_r n e e')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (* n ⊗ (e ⊲ s) IS s ·[RTensor N] (n ⊗ e) on the nose, so this is
     [g]'s own linearity with no rewriting. *)
  intros N M g n s e.
  exact (rm_map_smul g s (bs_gen n e)).
Qed.

Program Definition bth_to_ab {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M) :
  AbHom (rm_ab N) (hs_group M) := {|
  cmon_map := {| morphism := fun n => bth_to_inner g n |}
|}.
Next Obligation.
  intros N M g n n' Hn e; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (be_gen Hn (reflexivity e))).
Qed.
Next Obligation.
  intros N M g e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l N (bm_left E) e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n n' e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (bs_gen n e) (bs_gen n' e))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (be_add_l n n' e)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

(* The forward transpose is R-linear BECAUSE of the balance rule: at e
   the two sides are g ((r · n) ⊗ e) and g (n ⊗ (r · e)). *)
Program Definition bth_to {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M) :
  N ~{ModR R}~> HomSObj M := {|
  rm_hom := bth_to_ab g
|}.
Next Obligation.
  intros N M g r n e; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (@be_balance R N (bm_left E) r n e)).
Qed.

Program Definition bth_from_bal {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M) :
  BalBiadditive N (bm_left E) (rm_ab M) := {|
  bal_map := fun n e =>
    cmon_map (rm_hom (cmon_map (rm_hom h) n)) e
|}.
Next Obligation.
  intros N M h n n' Hn e e' He.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom h) n)) e').
  - exact (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom h) n)))
             e e' He).
  - exact (proper_morphism (cmon_map (rm_hom h)) n n' Hn e').
Qed.
Next Obligation.
  intros N M h n n' e.
  exact (cmon_map_plus (rm_hom h) n n' e).
Qed.
Next Obligation.
  intros N M h n e e'.
  exact (cmon_map_plus (rm_hom (cmon_map (rm_hom h) n)) e e').
Qed.
Next Obligation.
  (* Balance is [h]'s own R-linearity, read at e: the action on
     hom_S(E, M) is translation, so (r · h n) e IS (h n) (r · e). *)
  intros N M h r n e.
  exact (rm_map_smul h r n e).
Qed.

(* Multiplication by a scalar, as a homomorphism of the underlying
   group; the Instance/Mod/BaseChange.v:492 idiom. *)
Program Definition bth_lmul (M : RModObject (Ring_op S)) (s : SC) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M s m |}
|}.
Next Obligation.
  intros M s m m' Hm.
  exact (rm_smul_respects M s s (reflexivity s) m m' Hm).
Qed.
Next Obligation. intros M s; simpl; exact (rm_smul_zero_r M s). Qed.
Next Obligation.
  intros M s m m'; simpl; exact (rm_smul_distr_l M s m m').
Qed.

Program Definition bth_from {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M) :
  RTensor N ~{ModR S}~> M := {|
  rm_hom := bal_med (bth_from_bal h)
|}.
Next Obligation.
  intros N M h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (bth_from_bal h)) (rt_smul N s))
            (cmon_hom_compose (bth_lmul M s)
                              (bal_med (bth_from_bal h))) _ x).
  intros n e.
  exact (rm_map_smul (cmon_map (rm_hom h) n) s e).
Qed.

Example bth_to_at {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (bth_to g)) n)) e
    = cmon_map (rm_hom g) (bs_gen n e) := eq_refl.

Example bth_from_at {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (bth_from h)) (bs_gen n e)
    = cmon_map (rm_hom (cmon_map (rm_hom h) n)) e := eq_refl.

Program Definition bth_adj_to (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  {| carrier := RTensor N ~{ModR S}~> M;
     is_setoid := @homset (ModR S) (RTensor N) M |}
    ~{Sets}~>
  {| carrier := N ~{ModR R}~> HomSObj M;
     is_setoid := @homset (ModR R) N (HomSObj M) |} := {|
  morphism := fun g => bth_to g
|}.
Next Obligation. intros N M g g' Hg n e; exact (Hg _). Qed.

Program Definition bth_adj_from (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  {| carrier := N ~{ModR R}~> HomSObj M;
     is_setoid := @homset (ModR R) N (HomSObj M) |}
    ~{Sets}~>
  {| carrier := RTensor N ~{ModR S}~> M;
     is_setoid := @homset (ModR S) (RTensor N) M |} := {|
  morphism := fun h => bth_from h
|}.
Next Obligation.
  intros N M h h' Hh x.
  refine (bal_hom_ext (bal_med (bth_from_bal h))
                      (bal_med (bth_from_bal h')) _ x).
  intros n e; exact (Hh n e).
Qed.

(* Both round trips close by [reflexivity]: the forward transpose reads
   a generator and the backward one writes one, so nothing residual is
   left behind on either side. *)
Program Definition bth_adj (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  @Isomorphism Sets
    {| carrier := RTensor N ~{ModR S}~> M;
       is_setoid := @homset (ModR S) (RTensor N) M |}
    {| carrier := N ~{ModR R}~> HomSObj M;
       is_setoid := @homset (ModR R) N (HomSObj M) |} := {|
  to   := bth_adj_to N M;
  from := bth_adj_from N M
|}.
Next Obligation. intros N M h n e; reflexivity. Qed.
Next Obligation.
  intros N M g x.
  refine (bal_hom_ext (bal_med (bth_from_bal (bth_to g)))
                      (rm_hom g) _ x).
  intros n e; reflexivity.
Qed.

(* Mac Lane part (a).  Both remaining naturality obligations close by
   [reflexivity]. *)
Definition bimodule_tensor_hom_adjunction : TensorWith ⊣ HomS.
Proof.
  unshelve eapply (@Build_Adjunction' (ModR S) (ModR R) TensorWith
                     HomS bth_adj).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

(** *** Unit and counit *)

Definition bth_unit (N : RModObject (Ring_op R)) :
  N ~{ModR R}~> HomSObj (RTensor N) :=
  @unit (ModR S) (ModR R) TensorWith HomS
    bimodule_tensor_hom_adjunction N.

Definition bth_counit (M : RModObject (Ring_op S)) :
  RTensor (HomSObj M) ~{ModR S}~> M :=
  @counit (ModR S) (ModR R) TensorWith HomS
    bimodule_tensor_hom_adjunction M.

(* THE REVIEWER CHECK.  The unit IS n ↦ (e ↦ n ⊗ e) and the counit IS
   f ⊗ e ↦ f e, both on the nose. *)
Example bth_unit_is_gen (N : RModObject (Ring_op R))
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (bth_unit N)) n)) e
    = bs_gen n e := eq_refl.

Example bth_counit_is_eval (M : RModObject (Ring_op S))
  (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (bth_counit M))
      (@bs_gen R (HomSObj M) (bm_left E) f e)
    = cmon_map (rm_hom f) e := eq_refl.

Example bth_adj_to_is_bth_to (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) (g : RTensor N ~{ModR S}~> M) :
  to (@adj (ModR S) (ModR R) TensorWith HomS
        bimodule_tensor_hom_adjunction N M) g = bth_to g := eq_refl.

Example bth_adj_from_is_bth_from (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) (h : N ~{ModR R}~> HomSObj M) :
  from (@adj (ModR S) (ModR R) TensorWith HomS
          bimodule_tensor_hom_adjunction N M) h = bth_from h := eq_refl.

End BimoduleTensorHom.

(** ** C. The category of bimodules, the bifunctor, and Theorem 3 *)

Section BimoduleCategory.

Context {R S : RingObject}.

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).

(* A morphism of (R,S)-bimodules: a homomorphism of the LEFT R-modules
   that additionally commutes with the right S-action.  Nothing about
   the left action is restated — [bh_hom] is a coercion, and the record
   has exactly one field of its own. *)
Record BimodHom (E E' : Bimodule R S) := {
  bh_hom :> RModHom (bm_left E) (bm_left E');

  bh_right : ∀ m s,
    cmon_map (rm_hom bh_hom) (bm_rsmul E m s)
      ≈ bm_rsmul E' (cmon_map (rm_hom bh_hom) m) s
}.

Arguments bh_hom {E E'} _.
Arguments bh_right {E E'} _ _ _.

(* The hom-setoid: two bimodule maps agree when their underlying maps
   agree pointwise, which is Instance/Mod.v:225's [RModHom_Setoid] one
   field further in.  Neither action plays a part. *)
#[export]
Program Instance BimodHom_Setoid {E E' : Bimodule R S} :
  Setoid (BimodHom E E') := {|
  equiv := fun f g => ∀ e,
    cmon_map (rm_hom (bh_hom f)) e ≈ cmon_map (rm_hom (bh_hom g)) e
|}.
Next Obligation.
  intros E E'.
  constructor.
  - intros f e; reflexivity.
  - intros f g Hfg e; symmetry; apply Hfg.
  - intros f g h Hfg Hgh e.
    transitivity (cmon_map (rm_hom (bh_hom g)) e).
    + apply Hfg.
    + apply Hgh.
Qed.

Program Definition bimod_hom_id {E : Bimodule R S} : BimodHom E E := {|
  bh_hom := @rmod_hom_id R (bm_left E)
|}.
Next Obligation. intros E m s; simpl; reflexivity. Qed.

Program Definition bimod_hom_compose {E E' E'' : Bimodule R S}
        (f : BimodHom E' E'') (g : BimodHom E E') : BimodHom E E'' := {|
  bh_hom := rmod_hom_compose (bh_hom f) (bh_hom g)
|}.
Next Obligation.
  intros E E' E'' f g m s; simpl.
  unfold Basics.compose.
  transitivity (cmon_map (rm_hom (bh_hom f))
                  (bm_rsmul E' (cmon_map (rm_hom (bh_hom g)) m) s)).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom f))) _ _
             (bh_right g m s)).
  - exact (bh_right f (cmon_map (rm_hom (bh_hom g)) m) s).
Qed.

Lemma bimod_hom_compose_respects {E E' E'' : Bimodule R S} :
  Proper (equiv ==> equiv ==> equiv) (@bimod_hom_compose E E' E'').
Proof.
  intros f f' Hf g g' Hg e; simpl.
  unfold Basics.compose.
  transitivity (cmon_map (rm_hom (bh_hom f))
                  (cmon_map (rm_hom (bh_hom g')) e)).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom f))) _ _ (Hg e)).
  - exact (Hf _).
Qed.

Program Definition BimodCat : Category := {|
  obj     := Bimodule R S;
  hom     := BimodHom;
  homset  := fun E E' => @BimodHom_Setoid E E';
  id      := fun E => @bimod_hom_id E;
  compose := fun E E' E'' f g => @bimod_hom_compose E E' E'' f g;

  compose_respects := fun E E' E'' => @bimod_hom_compose_respects E E' E''
|}.
Next Obligation. intros E E' f e; simpl; reflexivity. Qed.
Next Obligation. intros E E' f e; simpl; reflexivity. Qed.
Next Obligation. intros E E' E'' E''' f g h e; simpl; reflexivity. Qed.
Next Obligation. intros E E' E'' E''' f g h e; simpl; reflexivity. Qed.

(* A bimodule map IS a map of the associated RIGHT S-modules, and the
   proof is its own [bh_right] field with the two arguments swapped —
   the flip that [bimodule_right_RMod] performs on the action. *)
Program Definition bimod_hom_right {E E' : Bimodule R S}
  (h : BimodHom E E') :
  bimodule_right_RMod E ~{ModR S}~> bimodule_right_RMod E' := {|
  rm_hom := rm_hom (bh_hom h)
|}.
Next Obligation. intros E E' h s m; exact (bh_right h m s). Qed.

Example bimodcat_hom (E E' : Bimodule R S) :
  (E ~{BimodCat}~> E') = BimodHom E E' := eq_refl.

Example bimodcat_id_map (E : Bimodule R S)
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  cmon_map (rm_hom (bh_hom (@id BimodCat E))) e = e := eq_refl.

(** *** The tensor as a bifunctor of both variables *)

(* Functoriality in the BIMODULE argument.  Scout B's item 1(ii): this
   is a PREREQUISITE of Mac Lane's Theorem 3, not an output of it — the
   theorem forces the arrow action of the RIGHT adjoint, and says
   nothing about the arrow action of the left one. *)
Program Definition bt_map_bal {N N' : RModObject (Ring_op R)}
  {E E' : Bimodule R S} (f : N ~{ModR R}~> N') (h : E ~{BimodCat}~> E') :
  BalBiadditive N (bm_left E) (BalTensor N' (bm_left E')) := {|
  bal_map := fun n e =>
    bs_gen (cmon_map (rm_hom f) n) (cmon_map (rm_hom (bh_hom h)) e)
|}.
Next Obligation.
  intros N N' E E' f h n n' Hn e e' He.
  exact (be_gen (proper_morphism (cmon_map (rm_hom f)) n n' Hn)
                (proper_morphism (cmon_map (rm_hom (bh_hom h))) e e' He)).
Qed.
Next Obligation.
  intros N N' E E' f h n n' e.
  exact (be_trans
           (be_gen (cmon_map_plus (rm_hom f) n n') (reflexivity _))
           (be_add_l (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom f) n')
                     (cmon_map (rm_hom (bh_hom h)) e))).
Qed.
Next Obligation.
  intros N N' E E' f h n e e'.
  exact (be_trans
           (be_gen (reflexivity _)
                   (cmon_map_plus (rm_hom (bh_hom h)) e e'))
           (be_add_r (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom (bh_hom h)) e)
                     (cmon_map (rm_hom (bh_hom h)) e'))).
Qed.
Next Obligation.
  (* The balance clause spends [f]'s linearity and then [h]'s. *)
  intros N N' E E' f h r n e.
  exact (be_trans
           (be_trans
              (be_gen (rm_map_smul f r n) (reflexivity _))
              (@be_balance R N' (bm_left E') r
                 (cmon_map (rm_hom f) n)
                 (cmon_map (rm_hom (bh_hom h)) e)))
           (be_gen (reflexivity _)
                   (symmetry (rm_map_smul (bh_hom h) r e)))).
Qed.

Program Definition BimodTensorMap {N N' : RModObject (Ring_op R)}
  {E E' : Bimodule R S} (f : N ~{ModR R}~> N') (h : E ~{BimodCat}~> E') :
  RTensor E N ~{ModR S}~> RTensor E' N' := {|
  rm_hom := bal_med (bt_map_bal f h)
|}.
Next Obligation.
  intros N N' E E' f h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (bt_map_bal f h)) (rt_smul E N s))
            (cmon_hom_compose (rt_smul E' N' s)
                              (bal_med (bt_map_bal f h))) _ x).
  intros n e; simpl.
  exact (be_gen (reflexivity _) (bh_right h e s)).
Qed.

Program Definition BimodTensor : ModR R ∏ BimodCat ⟶ ModR S := {|
  fobj := fun p => RTensor (snd p) (fst p);
  fmap := fun p q fh => BimodTensorMap (fst fh) (snd fh)
|}.
Next Obligation.
  intros [N E] [N' E'] [f h] [f' h'] [Hf Hh] x; simpl in *.
  refine (bal_hom_ext (bal_med (bt_map_bal f h))
                      (bal_med (bt_map_bal f' h')) _ x).
  intros n e.
  exact (be_gen (Hf n) (Hh e)).
Qed.
Next Obligation.
  intros [N E] x; simpl.
  refine (bal_hom_ext
            (bal_med (bt_map_bal (@id (ModR R) N) (@id BimodCat E)))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e; reflexivity.
Qed.
Next Obligation.
  intros [N E] [N' E'] [N'' E''] [f h] [f' h'] x; simpl in *.
  refine (bal_hom_ext
            (bal_med (bt_map_bal
                        (rmod_hom_compose f f') (bimod_hom_compose h h')))
            (cmon_hom_compose (bal_med (bt_map_bal f h))
                              (bal_med (bt_map_bal f' h'))) _ x).
  intros n e; reflexivity.
Qed.

Example bimod_tensor_obj (N : RModObject (Ring_op R))
  (E : Bimodule R S) :
  fobj[BimodTensor] (N, E) = RTensor E N := eq_refl.

Example bimod_tensor_partial_obj (E : Bimodule R S)
  (N : RModObject (Ring_op R)) :
  fobj[Partial_l BimodTensor E] N = RTensor E N := eq_refl.

Example bimod_tensor_partial_gen (E : Bimodule R S)
  {N N' : RModObject (Ring_op R)} (f : N ~{ModR R}~> N')
  (n : carrier (cmon_setoid (rm_ab N)))
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  cmon_map (rm_hom (fmap[Partial_l BimodTensor E] f)) (bs_gen n e)
    = bs_gen (cmon_map (rm_hom f) n) e := eq_refl.

(** *** Mac Lane part (b): the adjunction with a parameter *)

(* The partial functor at E and [TensorWith E] agree on objects and on
   generators, so the hom-setoid isomorphism of part (a) is reused
   verbatim; both naturality obligations close by [reflexivity]. *)
Definition bt_partial_adj (E : Bimodule R S) :
  Partial_l BimodTensor E ⊣ HomS E.
Proof.
  unshelve eapply (@Build_Adjunction' (ModR S) (ModR R)
                     (Partial_l BimodTensor E) (HomS E) (bth_adj E)).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

Definition bimodule_parametrized_adjunction :
  ParametrizedAdjunction BimodTensor :=
  @Build_ParametrizedAdjunction (ModR R) BimodCat (ModR S)
    BimodTensor (@HomS R S) bt_partial_adj.

Example bimod_pa_right (E : Bimodule R S) :
  pa_right bimodule_parametrized_adjunction E = HomS E := eq_refl.

Example bimod_pa_adj (E : Bimodule R S) :
  pa_adj bimodule_parametrized_adjunction E = bt_partial_adj E := eq_refl.

(* Mac Lane's G : P^op × A → X.  Its arrow action in the BIMODULE
   variable is #396's [pa_param_mate] and is therefore FORCED by
   Theorem 3; nothing here re-proves functoriality in E. *)
Definition bimodule_hom_bifunctor :
  (BimodCat)^op ∏ ModR S ⟶ ModR R :=
  parametrized_right_adjoint_bifunctor bimodule_parametrized_adjunction.

Example bimod_hom_bifunctor_obj (E : Bimodule R S)
  (M : RModObject (Ring_op S)) :
  fobj[bimodule_hom_bifunctor] (E, M) = HomSObj E M := eq_refl.

End BimoduleCategory.

Arguments BimodHom {R S} E E'.

(** ** D. Part (c): the tensor of two bimodules, and the composite *)

(* Two readings of the generator former as a homomorphism of ONE of its
   two variables.  They belong beside §A and are declared here only
   because §D is their first consumer. *)

Section BalancedGenerators.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Program Definition bal_gen_right
  (n : carrier (cmon_setoid (rm_ab N))) :
  AbHom (rm_ab M) (BalTensor N M) := {|
  cmon_map := {| morphism := fun m => bs_gen n m |}
|}.
Next Obligation.
  intros n m m' Hm; exact (be_gen (reflexivity n) Hm).
Qed.
Next Obligation. intros n; exact (bal_gen_zero_r N M n). Qed.
Next Obligation. intros n m m'; exact (be_add_r n m m'). Qed.

Program Definition bal_gen_left
  (m : carrier (cmon_setoid (rm_ab M))) :
  AbHom (rm_ab N) (BalTensor N M) := {|
  cmon_map := {| morphism := fun n => bs_gen n m |}
|}.
Next Obligation.
  intros m n n' Hn; exact (be_gen Hn (reflexivity m)).
Qed.
Next Obligation. intros m; exact (bal_gen_zero_l N M m). Qed.
Next Obligation. intros m n n'; exact (be_add_l n n' m). Qed.

End BalancedGenerators.

Arguments bal_gen_right {X} N M n.
Arguments bal_gen_left {X} N M m.

(** *** The left R-action on a balanced tensor over S *)

(* This engine is shared: §D's tensor of two bimodules and §E's
   left-module mirror are its two instantiations.  Given a bimodule
   _R E _S and a LEFT S-module N, the balanced tensor E ⊗_S N carries a
   left R-action r · (e ⊗ n) := (r · e) ⊗ n, whose balance clause is
   again [bm_compat] and nothing else. *)

Section BimoduleLeftTensor.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

Program Definition lt_bilin_act (N : RModObject S) (r : RC) :
  BalBiadditive EE N (BalTensor EE N) := {|
  bal_map := fun e n => bs_gen (rm_smul (bm_left E) r e) n
|}.
Next Obligation.
  intros N r e e' He n n' Hn.
  refine (be_gen _ Hn).
  exact (rm_smul_respects (bm_left E) r r (reflexivity r) e e' He).
Qed.
Next Obligation.
  intros N r e e' n.
  refine (be_trans _ (@be_add_l S (bimodule_right_RMod E) N
                        (rm_smul (bm_left E) r e)
                        (rm_smul (bm_left E) r e') n)).
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_distr_l (bm_left E) r e e').
Qed.
Next Obligation.
  intros N r e n n'.
  exact (@be_add_r S (bimodule_right_RMod E) N
           (rm_smul (bm_left E) r e) n n').
Qed.
Next Obligation.
  intros N r x e n.
  refine (be_trans _ (@be_balance S (bimodule_right_RMod E) N x
                        (rm_smul (bm_left E) r e) n)).
  refine (be_gen _ (reflexivity n)).
  exact (symmetry (bm_compat E r e x)).
Qed.

Definition lt_smul (N : RModObject S) (r : RC) :
  AbHom (BalTensor EE N) (BalTensor EE N) :=
  bal_med (lt_bilin_act N r).

Definition lt_act (N : RModObject S) (r : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  carrier (cmon_setoid (BalTensor EE N)) :=
  cmon_map (lt_smul N r) x.

Example lt_act_gen (N : RModObject S) (r : RC) (e : EC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  lt_act N r (@bs_gen S (bimodule_right_RMod E) N e n)
    = @bs_gen S (bimodule_right_RMod E) N
        (rm_smul (bm_left E) r e) n := eq_refl.

Lemma lt_act_scalar (N : RModObject S) (r r' : RC) :
  r ≈ r' → ∀ x, lt_act N r x ≈ lt_act N r' x.
Proof.
  intros Hr x.
  refine (bal_hom_ext (lt_smul N r) (lt_smul N r') _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_respects (bm_left E) r r' Hr e e (reflexivity e)).
Qed.

Lemma lt_act_respects (N : RModObject S) :
  Proper (equiv ==> equiv ==> equiv) (lt_act N).
Proof.
  intros r r' Hr x y Hxy.
  transitivity (lt_act N r y).
  - exact (proper_morphism (cmon_map (lt_smul N r)) x y Hxy).
  - exact (lt_act_scalar N r r' Hr y).
Qed.

Lemma lt_act_distr_r (N : RModObject S) (r r' : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_add (ring_rig R) r r') x
    ≈ cmon_plus (BalTensor EE N) (lt_act N r x) (lt_act N r' x).
Proof.
  refine (bal_hom_ext (lt_smul N (rig_add (ring_rig R) r r'))
            (ab_hom_add (lt_smul N r) (lt_smul N r')) _ x).
  intros e n.
  refine (be_trans _ (@be_add_l S (bimodule_right_RMod E) N
                        (rm_smul (bm_left E) r e)
                        (rm_smul (bm_left E) r' e) n)).
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_distr_r (bm_left E) r r' e).
Qed.

Lemma lt_act_assoc (N : RModObject S) (r r' : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_mul (ring_rig R) r r') x ≈ lt_act N r (lt_act N r' x).
Proof.
  refine (bal_hom_ext (lt_smul N (rig_mul (ring_rig R) r r'))
            (cmon_hom_compose (lt_smul N r) (lt_smul N r')) _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_assoc (bm_left E) r r' e).
Qed.

Lemma lt_act_one (N : RModObject S)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_one (ring_rig R)) x ≈ x.
Proof.
  refine (bal_hom_ext (lt_smul N (rig_one (ring_rig R)))
            (@cmon_hom_id (BalTensor EE N)) _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_one (bm_left E) e).
Qed.

(* E ⊗_S N as a LEFT R-module. *)
Definition LTensor (N : RModObject S) : RModObject R :=
  @Build_RModObject R
    (BalTensor EE N)
    (lt_act N)
    (lt_act_respects N)
    (fun r x y => cmon_map_plus (lt_smul N r) x y)
    (lt_act_distr_r N)
    (lt_act_assoc N)
    (lt_act_one N).

Example lt_carrier (N : RModObject S) :
  rm_ab (LTensor N) = BalTensor EE N := eq_refl.

Example lt_smul_gen (N : RModObject S) (r : RC) (e : EC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  rm_smul (LTensor N) r (@bs_gen S (bimodule_right_RMod E) N e n)
    = @bs_gen S (bimodule_right_RMod E) N
        (rm_smul (bm_left E) r e) n := eq_refl.

End BimoduleLeftTensor.

Arguments lt_bilin_act {R S} E N r.
Arguments lt_smul {R S} E N r.
Arguments lt_act {R S} E N r x.
Arguments LTensor {R S} E N.

(** *** The tensor of two bimodules *)

(* For _R E _S and _S E1 _T, the balanced tensor E ⊗_S E1 carries BOTH
   residual actions on ONE group: the left R-action of §D's engine and
   the right T-action of §B's, and they commute for a reason with no
   content — on a generator both sides are (r · e) ⊗ (e1 ⊲ t). *)

Section BimoduleTensorBimodule.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation TC := (carrier (rig_setoid (ring_rig T))).
Local Notation EE := (bimodule_right_RMod E).
Local Notation BTC := (BalTensor EE (bm_left E1)).

Definition btb_left : RModObject R := LTensor E (bm_left E1).
Definition btb_right : RModObject (Ring_op T) := RTensor E1 EE.

Example btb_carriers_agree : rm_ab btb_left = rm_ab btb_right := eq_refl.

Lemma btb_rsmul_respects :
  Proper (equiv ==> equiv ==> equiv)
    (fun (x : carrier (cmon_setoid BTC)) (t : TC) =>
       rm_smul btb_right t x).
Proof.
  intros x y Hxy t t' Ht.
  exact (rm_smul_respects btb_right t t' Ht x y Hxy).
Qed.

(* The ONE clause with content, and it has none: [bal_hom_ext] reduces it
   to a reflexivity on generators. *)
Lemma btb_compat (r : RC) (x : carrier (cmon_setoid BTC)) (t : TC) :
  rm_smul btb_right t (rm_smul btb_left r x)
    ≈ rm_smul btb_left r (rm_smul btb_right t x).
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (rt_smul E1 EE t)
                              (lt_smul E (bm_left E1) r))
            (cmon_hom_compose (lt_smul E (bm_left E1) r)
                              (rt_smul E1 EE t)) _ x).
  intros e e1; reflexivity.
Qed.

Definition BimodTensorBimod : Bimodule R T :=
  @Build_Bimodule R T btb_left
    (fun x t => rm_smul btb_right t x)
    btb_rsmul_respects
    (fun x y t => rm_smul_distr_l btb_right t x y)
    (fun x t t' => rm_smul_distr_r btb_right t t' x)
    (fun x t t' => rm_smul_assoc btb_right t' t x)
    (fun x => rm_smul_one btb_right x)
    btb_compat.

Example btb_bm_left : bm_left BimodTensorBimod = btb_left := eq_refl.

Example btb_carrier :
  rm_ab (bm_left BimodTensorBimod) = BalTensor EE (bm_left E1) := eq_refl.

Example btb_left_gen (r : RC)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  rm_smul (bm_left BimodTensorBimod) r
    (@bs_gen S EE (bm_left E1) e e1)
    = @bs_gen S EE (bm_left E1) (rm_smul (bm_left E) r e) e1 := eq_refl.

Example btb_right_gen (t : TC)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  bm_rsmul BimodTensorBimod (@bs_gen S EE (bm_left E1) e e1) t
    = @bs_gen S EE (bm_left E1) e (bm_rsmul E1 e1 t) := eq_refl.

End BimoduleTensorBimodule.

Arguments btb_left {R S T} E E1.
Arguments btb_right {R S T} E E1.
Arguments BimodTensorBimod {R S T} E E1.

(** *** Mac Lane part (c): the composite adjunction *)

Section BimoduleAdjunctionComposite.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation EE := (bimodule_right_RMod E).

(* Adjunction/Compose.v:173, applied.  Nothing is re-proved: the composite
   of two hom-setoid bijections is one, and all four naturality fields are
   that file's. *)
Definition bimodule_adjunction_composite :
  (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1) :=
  Adjunction_Compose (bimodule_tensor_hom_adjunction E)
                     (bimodule_tensor_hom_adjunction E1).

Definition bac_unit (N : RModObject (Ring_op R)) :
  N ~{ModR R}~> HomSObj E (HomSObj E1 (RTensor E1 (RTensor E N))) :=
  @unit (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
    (HomS E ◯ HomS E1) bimodule_adjunction_composite N.

Definition bac_counit (M : RModObject (Ring_op T)) :
  RTensor E1 (RTensor E (HomSObj E (HomSObj E1 M))) ~{ModR T}~> M :=
  @counit (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
    (HomS E ◯ HomS E1) bimodule_adjunction_composite M.

(* The composite's unit is the DOUBLE generator and its counit DOUBLE
   evaluation, both on the nose. *)
Example bac_unit_is_gen (N : RModObject (Ring_op R))
  (n : carrier (cmon_setoid (rm_ab N)))
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  cmon_map (rm_hom (cmon_map (rm_hom
     (cmon_map (rm_hom (bac_unit N)) n)) e)) e1
    = @bs_gen S (RTensor E N) (bm_left E1)
        (@bs_gen R N (bm_left E) n e) e1 := eq_refl.

Example bac_counit_is_eval (M : RModObject (Ring_op T))
  (f : EE ~{ModR S}~> HomSObj E1 M)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  cmon_map (rm_hom (bac_counit M))
      (@bs_gen S (RTensor E (HomSObj E (HomSObj E1 M))) (bm_left E1)
         (@bs_gen R (HomSObj E (HomSObj E1 M)) (bm_left E) f e) e1)
    = cmon_map (rm_hom (cmon_map (rm_hom f) e)) e1 := eq_refl.

(* Mac Lane's own description of the composite's unit and counit, read
   off Adjunction/Compose.v:216 and :224. *)
Lemma bac_unit_whiskered (N : RModObject (Ring_op R)) :
  bac_unit N
    ≈ fmap[HomS E]
        (@unit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E1) (RTensor E N))
      ∘ @unit (ModR S) (ModR R) (TensorWith E) (HomS E)
          (bimodule_tensor_hom_adjunction E) N.
Proof.
  exact (@Adjunction_Compose_unit (ModR S) (ModR R) (ModR T)
           (TensorWith E) (HomS E) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E)
           (bimodule_tensor_hom_adjunction E1) N).
Qed.

Lemma bac_counit_whiskered (M : RModObject (Ring_op T)) :
  bac_counit M
    ≈ @counit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
        (bimodule_tensor_hom_adjunction E1) M
      ∘ fmap[TensorWith E1]
          (@counit (ModR S) (ModR R) (TensorWith E) (HomS E)
             (bimodule_tensor_hom_adjunction E) (HomSObj E1 M)).
Proof.
  exact (@Adjunction_Compose_counit (ModR S) (ModR R) (ModR T)
           (TensorWith E) (HomS E) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E)
           (bimodule_tensor_hom_adjunction E1) M).
Qed.

End BimoduleAdjunctionComposite.

Arguments bimodule_adjunction_composite {R S T} E E1.

(** *** The associativity comparison, and part (c)'s conclusion *)

(* (N ⊗_R E) ⊗_S E1  ≅  N ⊗_R (E ⊗_S E1), in [ModR T].  Both legs are a
   mediator of a mediator: the outer balanced map sends (x, e1) to the
   value at x of the inner one, so every clause below is [bal_hom_ext] at
   one or two levels with a reflexivity on generators at the bottom. *)

Section TensorAssocAt.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).
Context (N : RModObject (Ring_op R)).

Local Notation EE := (bimodule_right_RMod E).
Local Notation BTB := (BimodTensorBimod E E1).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation E1C := (carrier (cmon_setoid (rm_ab (bm_left E1)))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).
Local Notation TGT := (BalTensor N (bm_left BTB)).
Local Notation SRC := (BalTensor (RTensor E N) (bm_left E1)).

(** **** Left to right *)

Program Definition ta_inner (e1 : E1C) :
  BalBiadditive N (bm_left E) TGT := {|
  bal_map := fun n e =>
    @bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1)
|}.
Next Obligation.
  intros e1 n n' Hn e e' He.
  refine (be_gen Hn _).
  exact (@be_gen S EE (bm_left E1) e e' e1 e1 He (reflexivity e1)).
Qed.
Next Obligation.
  intros e1 n n' e.
  exact (@be_add_l R N (bm_left BTB) n n'
           (@bs_gen S EE (bm_left E1) e e1)).
Qed.
Next Obligation.
  intros e1 n e e'.
  refine (be_trans _ (@be_add_r R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1)
                        (@bs_gen S EE (bm_left E1) e' e1))).
  refine (be_gen (reflexivity n) _).
  exact (@be_add_l S EE (bm_left E1) e e' e1).
Qed.
Next Obligation.
  intros e1 r n e.
  exact (@be_balance R N (bm_left BTB) r n
           (@bs_gen S EE (bm_left E1) e e1)).
Qed.

Program Definition ta_outer :
  BalBiadditive (RTensor E N) (bm_left E1) TGT := {|
  bal_map := fun x e1 => cmon_map (bal_med (ta_inner e1)) x
|}.
Next Obligation.
  intros x x' Hx e1 e1' He1.
  transitivity (cmon_map (bal_med (ta_inner e1)) x').
  - exact (proper_morphism (cmon_map (bal_med (ta_inner e1))) x x' Hx).
  - refine (bal_hom_ext (bal_med (ta_inner e1))
              (bal_med (ta_inner e1')) _ x').
    intros n e.
    refine (be_gen (reflexivity n) _).
    exact (@be_gen S EE (bm_left E1) e e e1 e1' (reflexivity e) He1).
Qed.
Next Obligation.
  intros x x' e1.
  exact (cmon_map_plus (bal_med (ta_inner e1)) x x').
Qed.
Next Obligation.
  intros x e1 e1'.
  refine (bal_hom_ext (bal_med (ta_inner
             (cmon_plus (rm_ab (bm_left E1)) e1 e1')))
            (ab_hom_add (bal_med (ta_inner e1))
                        (bal_med (ta_inner e1'))) _ x).
  intros n e.
  refine (be_trans _ (@be_add_r R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1)
                        (@bs_gen S EE (bm_left E1) e e1'))).
  refine (be_gen (reflexivity n) _).
  exact (@be_add_r S EE (bm_left E1) e e1 e1').
Qed.
Next Obligation.
  intros s x e1.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (ta_inner e1)) (rt_smul E N s))
            (bal_med (ta_inner (rm_smul (bm_left E1) s e1))) _ x).
  intros n e.
  refine (be_gen (reflexivity n) _).
  exact (@be_balance S EE (bm_left E1) s e e1).
Qed.

Program Definition ta_to : RTensor E1 (RTensor E N) ~{ModR T}~> RTensor BTB N
  := {| rm_hom := bal_med ta_outer |}.
Next Obligation.
  intros t x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer)
                              (rt_smul E1 (RTensor E N) t))
            (cmon_hom_compose (rt_smul BTB N t) (bal_med ta_outer))
            _ x).
  intros x0 e1; simpl.
  refine (bal_hom_ext (bal_med (ta_inner (bm_rsmul E1 e1 t)))
            (cmon_hom_compose (rt_smul BTB N t)
                              (bal_med (ta_inner e1))) _ x0).
  intros n e; reflexivity.
Qed.

(** **** Right to left *)

Program Definition ta_binner (n : NC) :
  BalBiadditive EE (bm_left E1) SRC := {|
  bal_map := fun e e1 =>
    @bs_gen S (RTensor E N) (bm_left E1) (@bs_gen R N (bm_left E) n e) e1
|}.
Next Obligation.
  intros n e e' He e1 e1' He1.
  refine (be_gen _ He1).
  exact (@be_gen R N (bm_left E) n n e e' (reflexivity n) He).
Qed.
Next Obligation.
  intros n e e' e1.
  refine (be_trans _ (@be_add_l S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e)
                        (@bs_gen R N (bm_left E) n e') e1)).
  refine (be_gen _ (reflexivity e1)).
  exact (@be_add_r R N (bm_left E) n e e').
Qed.
Next Obligation.
  intros n e e1 e1'.
  exact (@be_add_r S (RTensor E N) (bm_left E1)
           (@bs_gen R N (bm_left E) n e) e1 e1').
Qed.
Next Obligation.
  intros n s e e1.
  exact (@be_balance S (RTensor E N) (bm_left E1) s
           (@bs_gen R N (bm_left E) n e) e1).
Qed.

Program Definition ta_bouter :
  BalBiadditive N (bm_left BTB) SRC := {|
  bal_map := fun n y => cmon_map (bal_med (ta_binner n)) y
|}.
Next Obligation.
  intros n n' Hn y y' Hy.
  transitivity (cmon_map (bal_med (ta_binner n)) y').
  - exact (proper_morphism (cmon_map (bal_med (ta_binner n))) y y' Hy).
  - refine (bal_hom_ext (bal_med (ta_binner n))
              (bal_med (ta_binner n')) _ y').
    intros e e1.
    refine (be_gen _ (reflexivity e1)).
    exact (@be_gen R N (bm_left E) n n' e e Hn (reflexivity e)).
Qed.
Next Obligation.
  intros n n' y.
  refine (bal_hom_ext (bal_med (ta_binner (cmon_plus (rm_ab N) n n')))
            (ab_hom_add (bal_med (ta_binner n))
                        (bal_med (ta_binner n'))) _ y).
  intros e e1.
  refine (be_trans _ (@be_add_l S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e)
                        (@bs_gen R N (bm_left E) n' e) e1)).
  refine (be_gen _ (reflexivity e1)).
  exact (@be_add_l R N (bm_left E) n n' e).
Qed.
Next Obligation.
  intros n y y'.
  exact (cmon_map_plus (bal_med (ta_binner n)) y y').
Qed.
Next Obligation.
  intros r n y.
  refine (bal_hom_ext (bal_med (ta_binner (rm_smul N r n)))
            (cmon_hom_compose (bal_med (ta_binner n))
                              (lt_smul E (bm_left E1) r)) _ y).
  intros e e1.
  refine (be_gen _ (reflexivity e1)).
  exact (@be_balance R N (bm_left E) r n e).
Qed.

Program Definition ta_from : RTensor BTB N ~{ModR T}~> RTensor E1 (RTensor E N)
  := {| rm_hom := bal_med ta_bouter |}.
Next Obligation.
  intros t y.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter) (rt_smul BTB N t))
            (cmon_hom_compose (rt_smul E1 (RTensor E N) t)
                              (bal_med ta_bouter)) _ y).
  intros n y0; simpl.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (ta_binner n))
                              (rt_smul E1 EE t))
            (cmon_hom_compose (rt_smul E1 (RTensor E N) t)
                              (bal_med (ta_binner n))) _ y0).
  intros e e1; reflexivity.
Qed.

(** **** The two round trips *)

Lemma ta_to_from (y : carrier (cmon_setoid TGT)) :
  cmon_map (rm_hom ta_to) (cmon_map (rm_hom ta_from) y) ≈ y.
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer) (bal_med ta_bouter))
            (@cmon_hom_id TGT) _ y).
  intros n y0.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer)
                              (bal_med (ta_binner n)))
            (bal_gen_right N (bm_left BTB) n) _ y0).
  intros e e1; reflexivity.
Qed.

Lemma ta_from_to (x : carrier (cmon_setoid SRC)) :
  cmon_map (rm_hom ta_from) (cmon_map (rm_hom ta_to) x) ≈ x.
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter) (bal_med ta_outer))
            (@cmon_hom_id SRC) _ x).
  intros x0 e1.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter)
                              (bal_med (ta_inner e1)))
            (bal_gen_left (RTensor E N) (bm_left E1) e1) _ x0).
  intros n e; reflexivity.
Qed.

Program Definition ta_iso :
  @Isomorphism (ModR T) (RTensor E1 (RTensor E N)) (RTensor BTB N) := {|
  to   := ta_to;
  from := ta_from
|}.
Next Obligation. intros y; exact (ta_to_from y). Qed.
Next Obligation. intros x; exact (ta_from_to x). Qed.

Example ta_to_gen (n : NC) (e : EC) (e1 : E1C) :
  cmon_map (rm_hom ta_to)
      (@bs_gen S (RTensor E N) (bm_left E1)
         (@bs_gen R N (bm_left E) n e) e1)
    = @bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1)
  := eq_refl.

Example ta_from_gen (n : NC) (e : EC) (e1 : E1C) :
  cmon_map (rm_hom ta_from)
      (@bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1))
    = @bs_gen S (RTensor E N) (bm_left E1)
        (@bs_gen R N (bm_left E) n e) e1 := eq_refl.

End TensorAssocAt.

(** *** Extensionality at the double tensor, and the natural comparison *)

Section TensorAssocNatural.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation EE := (bimodule_right_RMod E).
Local Notation BTB := (BimodTensorBimod E E1).

(* Two homomorphisms out of (N ⊗_R E) ⊗_S E1 agreeing on the DOUBLE
   generators agree, and dually out of N ⊗_R (E ⊗_S E1).  Each is
   [bal_hom_ext] applied twice, the inner application through the
   one-variable readings of the generator former. *)
Lemma ta_double_ext (N : RModObject (Ring_op R)) (A : AbObject)
  (u v : AbHom (BalTensor (RTensor E N) (bm_left E1)) A) :
  (∀ n e e1,
      cmon_map u (@bs_gen S (RTensor E N) (bm_left E1)
                    (@bs_gen R N (bm_left E) n e) e1)
        ≈ cmon_map v (@bs_gen S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e) e1)) →
  ∀ x, cmon_map u x ≈ cmon_map v x.
Proof.
  intros H x.
  refine (bal_hom_ext u v _ x).
  intros x0 e1.
  refine (bal_hom_ext
            (cmon_hom_compose u
               (bal_gen_left (RTensor E N) (bm_left E1) e1))
            (cmon_hom_compose v
               (bal_gen_left (RTensor E N) (bm_left E1) e1)) _ x0).
  intros n e; exact (H n e e1).
Qed.

Lemma ta_double_ext_r (N : RModObject (Ring_op R)) (A : AbObject)
  (u v : AbHom (BalTensor N (bm_left BTB)) A) :
  (∀ n e e1,
      cmon_map u (@bs_gen R N (bm_left BTB) n
                    (@bs_gen S EE (bm_left E1) e e1))
        ≈ cmon_map v (@bs_gen R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1))) →
  ∀ y, cmon_map u y ≈ cmon_map v y.
Proof.
  intros H y.
  refine (bal_hom_ext u v _ y).
  intros n y0.
  refine (bal_hom_ext
            (cmon_hom_compose u (bal_gen_right N (bm_left BTB) n))
            (cmon_hom_compose v (bal_gen_right N (bm_left BTB) n))
            _ y0).
  intros e e1; exact (H n e e1).
Qed.

(* THE COMPARISON.  [≈] at a functor category is Theory/Functor.v:149's
   [Functor_Setoid]: a family of isomorphisms together with the coherence
   square, and both halves are supplied here. *)
Definition tensor_assoc_iso :
  (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
    ≈ TensorWith (BimodTensorBimod E E1).
Proof.
  exists (fun N => ta_iso E E1 N).
  intros N N' f x.
  refine (ta_double_ext N _
            (rm_hom (fmap[TensorWith E1 ◯ TensorWith E] f))
            (rm_hom (from (ta_iso E E1 N')
                     ∘ fmap[TensorWith BTB] f
                     ∘ to (ta_iso E E1 N))) _ x).
  intros n e e1; reflexivity.
Defined.

End TensorAssocNatural.

Arguments tensor_assoc_iso {R S T} E E1.

(** *** Transporting an adjunction along an isomorphism of left adjoints *)

(* A functor naturally isomorphic to a left adjoint is a left adjoint,
   with the SAME right adjoint.  Nothing of this shape exists in the tree
   — Theory/Adjunction.v:367 and :407 run the other way (from two
   adjunctions to an isomorphism), Theory/Equivalence/Adjunction.v:105
   transports along an EQUIVALENCE OF CATEGORIES rather than along a
   2-cell, and Theory/Functor.v:535's [transport_adjunction] is a
   Type-level transport of a relation along an equality of indices, not
   an adjunction at all.  It belongs beside Theory/Adjunction.v and is
   declared here because part (c) is its first consumer. *)

Section AdjunctionAlongIso.

Context {C D : Category}.
Context {F F' : D ⟶ C}.
Context {G : C ⟶ D}.
Context (Hiso : F ≈ F').
Context (A : F' ⊣ G).

Definition aali_cell (x : D) : F x ≅ F' x := projT1 Hiso x.

Lemma aali_natural {x y : D} (g : x ~> y) :
  fmap[F] g ∘ from (aali_cell x) ≈ from (aali_cell y) ∘ fmap[F'] g.
Proof.
  rewrite (projT2 Hiso x y g).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (aali_cell x)).
  now rewrite id_right.
Qed.

Definition aali_to (x : D) (y : C) (f : F x ~> y) : x ~> G y :=
  to (@adj C D F' G A x y) (f ∘ from (aali_cell x)).

Definition aali_from (x : D) (y : C) (g : x ~> G y) : F x ~> y :=
  from (@adj C D F' G A x y) g ∘ to (aali_cell x).

Lemma aali_to_from (x : D) (y : C) (g : x ~> G y) :
  aali_to x y (aali_from x y g) ≈ g.
Proof.
  unfold aali_to, aali_from.
  rewrite <- comp_assoc.
  rewrite (iso_to_from (aali_cell x)).
  rewrite id_right.
  exact (@from_adj_comp_law C D F' G A x y g).
Qed.

Lemma aali_from_to (x : D) (y : C) (f : F x ~> y) :
  aali_from x y (aali_to x y f) ≈ f.
Proof.
  unfold aali_to, aali_from.
  rewrite (@to_adj_comp_law C D F' G A x y (f ∘ from (aali_cell x))).
  rewrite <- comp_assoc.
  rewrite (iso_from_to (aali_cell x)).
  now rewrite id_right.
Qed.

Program Definition aali_iso (x : D) (y : C) :
  @Isomorphism Sets
    {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
    {| carrier := @hom D x (G y); is_setoid := @homset D x (G y) |} := {|
  to   := {| morphism := aali_to x y |};
  from := {| morphism := aali_from x y |}
|}.
Next Obligation.
  intros x y f f' Hf; unfold aali_to.
  now rewrite Hf.
Qed.
Next Obligation.
  intros x y g g' Hg; unfold aali_from.
  now rewrite Hg.
Qed.
Next Obligation. intros x y g; exact (aali_to_from x y g). Qed.
Next Obligation. intros x y f; exact (aali_from_to x y f). Qed.

Definition adjunction_along_left_iso : F ⊣ G.
Proof using A C D F F' G Hiso.
  unshelve eapply (@Build_Adjunction' C D F G aali_iso).
  - intros x y z f g; simpl; unfold aali_to.
    rewrite <- comp_assoc.
    rewrite (aali_natural g).
    rewrite comp_assoc.
    exact (@to_adj_nat_l C D F' G A x y z (f ∘ from (aali_cell y)) g).
  - intros x y z f g; simpl; unfold aali_to.
    rewrite <- comp_assoc.
    exact (@to_adj_nat_r C D F' G A x y z f (g ∘ from (aali_cell x))).
Defined.

Example aali_to_is_transpose (x : D) (y : C) (f : F x ~> y) :
  to (@adj C D F G adjunction_along_left_iso x y) f
    = to (@adj C D F' G A x y) (f ∘ from (aali_cell x)) := eq_refl.

End AdjunctionAlongIso.

Arguments aali_cell {C D F F'} Hiso x.
Arguments adjunction_along_left_iso {C D F F' G} Hiso A.

(** *** Mac Lane's "describe the composite" *)

Section BimoduleCompositeConclusion.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

(* The composite adjunction IS the adjunction of the tensor of the two
   bimodules, up to the natural isomorphism above — on the left by
   transport, and then on the right by uniqueness of right adjoints. *)
Definition bimodule_tensor_bimod_adjunction :
  TensorWith (BimodTensorBimod E E1) ⊣ (HomS E ◯ HomS E1) :=
  adjunction_along_left_iso
    (symmetry (tensor_assoc_iso E E1))
    (bimodule_adjunction_composite E E1).

Definition bimodule_hom_composite_iso :
  (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
    ≈ HomS (BimodTensorBimod E E1) :=
  right_adjoint_iso (TensorWith (BimodTensorBimod E E1))
    (HomS E ◯ HomS E1) (HomS (BimodTensorBimod E E1))
    bimodule_tensor_bimod_adjunction
    (bimodule_tensor_hom_adjunction (BimodTensorBimod E E1)).

(* The transported transpose is the composite's own, precomposed with
   the comparison; on a generator the comparison is [ta_from]. *)
Example btba_to_is_transposed (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op T))
  (g : RTensor (BimodTensorBimod E E1) N ~{ModR T}~> M) :
  to (@adj (ModR T) (ModR R) (TensorWith (BimodTensorBimod E E1))
        (HomS E ◯ HomS E1) bimodule_tensor_bimod_adjunction N M) g
    = to (@adj (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
            (HomS E ◯ HomS E1) (bimodule_adjunction_composite E E1) N M)
        (g ∘ from (aali_cell (symmetry (tensor_assoc_iso E E1)) N))
  := eq_refl.

End BimoduleCompositeConclusion.

Arguments bimodule_tensor_bimod_adjunction {R S T} E E1.
Arguments bimodule_hom_composite_iso {R S T} E E1.

(** ** E. The left-module mirror, and Riehl's Corollary 4.6.10 *)

(* Riehl, "Category Theory in Context", §4.6 Corollary 4.6.10, printed
   p. 169: for an R-S bimodule M the functor M ⊗_S − is right exact,
   because Corollary 4.6.9 makes a left adjoint between abelian
   categories right exact.  The adjunction it needs is the LEFT-module
   one, S-Mod ⇄ R-Mod, and it is §B read on the other side: the same
   balanced tensor of §A, with the residual action taken from E's LEFT
   R-module structure and the hom-module translated through E's RIGHT
   S-action. *)

(* Multiplication by a scalar as an endomorphism of the underlying
   group, over an ARBITRARY ring.  [bth_lmul] of §B is its instance at
   an opposite ring, and is left as it stands. *)
Program Definition rmod_lmul {X : RingObject} (M : RModObject X)
  (x : carrier (rig_setoid (ring_rig X))) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M x m |}
|}.
Next Obligation.
  intros X M x m m' Hm.
  exact (rm_smul_respects M x x (reflexivity x) m m' Hm).
Qed.
Next Obligation. intros X M x; simpl; exact (rm_smul_zero_r M x). Qed.
Next Obligation.
  intros X M x m m'; simpl; exact (rm_smul_distr_l M x m m').
Qed.

Section BimoduleLeftTensorHom.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

(** *** The functor E ⊗_S − *)

Program Definition lt_map_bal {N N' : RModObject S} (f : RModHom N N') :
  BalBiadditive EE N (BalTensor EE N') := {|
  bal_map := fun e n => bs_gen e (cmon_map (rm_hom f) n)
|}.
Next Obligation.
  intros N N' f e e' He n n' Hn.
  refine (be_gen He _).
  exact (proper_morphism (cmon_map (rm_hom f)) n n' Hn).
Qed.
Next Obligation.
  intros N N' f e e' n.
  exact (@be_add_l S EE N' e e' (cmon_map (rm_hom f) n)).
Qed.
Next Obligation.
  intros N N' f e n n'.
  refine (be_trans _ (@be_add_r S EE N' e
                        (cmon_map (rm_hom f) n)
                        (cmon_map (rm_hom f) n'))).
  refine (be_gen (reflexivity e) _).
  exact (cmon_map_plus (rm_hom f) n n').
Qed.
Next Obligation.
  intros N N' f x e n.
  refine (be_trans (@be_balance S EE N' x e (cmon_map (rm_hom f) n)) _).
  refine (be_gen (reflexivity e) _).
  exact (symmetry (rm_map_smul f x n)).
Qed.

Definition lt_map_ab {N N' : RModObject S} (f : RModHom N N') :
  AbHom (BalTensor EE N) (BalTensor EE N') :=
  bal_med (lt_map_bal f).

Program Definition LTensorMap {N N' : RModObject S}
  (f : N ~{RMod S}~> N') : LTensor E N ~{RMod R}~> LTensor E N' := {|
  rm_hom := lt_map_ab f
|}.
Next Obligation.
  intros N N' f r x.
  refine (bal_hom_ext
            (cmon_hom_compose (lt_map_ab f) (lt_smul E N r))
            (cmon_hom_compose (lt_smul E N' r) (lt_map_ab f)) _ x).
  intros e n; reflexivity.
Qed.

Program Definition LTensorWith : RMod S ⟶ RMod R := {|
  fobj := LTensor E;
  fmap := @LTensorMap
|}.
Next Obligation.
  intros N N' f g Hfg x.
  refine (bal_hom_ext (lt_map_ab f) (lt_map_ab g) _ x).
  intros e n.
  refine (be_gen (reflexivity e) _).
  exact (Hfg n).
Qed.
Next Obligation.
  intros N x.
  refine (bal_hom_ext (lt_map_ab (@id (RMod S) N))
            (@cmon_hom_id (BalTensor EE N)) _ x).
  intros e n; reflexivity.
Qed.
Next Obligation.
  intros N N' N'' f g x.
  refine (bal_hom_ext (lt_map_ab (f ∘ g))
            (cmon_hom_compose (lt_map_ab f) (lt_map_ab g)) _ x).
  intros e n; reflexivity.
Qed.

Example ltw_fobj (N : RModObject S) : fobj[LTensorWith] N = LTensor E N
  := eq_refl.

Example ltw_fmap_gen {N N' : RModObject S} (f : N ~{RMod S}~> N')
  (e : EC) (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (rm_hom (fmap[LTensorWith] f))
      (@bs_gen S EE N e n)
    = @bs_gen S EE N' e (cmon_map (rm_hom f) n) := eq_refl.

(** *** hom_R(E, M) and its left S-action *)

Definition lhs_group (M : RModObject R) : AbObject :=
  hom_ab (RMod_AbEnriched R) (bm_left E) M.

Example lhs_group_carrier (M : RModObject R) :
  carrier (cmon_setoid (lhs_group M)) = (bm_left E ~{RMod R}~> M)
  := eq_refl.

(* (s · f)(e) = f (e ⊲ s): translation through the RIGHT action, the
   mirror of §B's (f ⊲ r)(e) = f (r · e). *)
Program Definition lhs_act (M : RModObject R) (s : SC)
  (f : bm_left E ~{RMod R}~> M) : bm_left E ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom f) (bm_rsmul E e s) |} |}
|}.
Next Obligation.
  intros M s f e e' He.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (bm_rsmul_respects E e e' He s s (reflexivity s))).
Qed.
Next Obligation.
  intros M s f; simpl.
  transitivity (cmon_map (rm_hom f) (cmon_zero (rm_ab (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_zero_r (bimodule_right_RMod E) s)).
  - exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros M s f e e'; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (bm_rsmul E e s) (bm_rsmul E e' s))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_distr_l E e e' s)).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.
Next Obligation.
  (* the ONLY use of [bm_compat] in this block *)
  intros M s f r e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (bm_left E) r (bm_rsmul E e s))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_compat E r e s)).
  - exact (rm_map_smul f r (bm_rsmul E e s)).
Qed.

Example lhs_act_at (M : RModObject R) (s : SC)
  (f : bm_left E ~{RMod R}~> M) (e : EC) :
  cmon_map (rm_hom (lhs_act M s f)) e
    = cmon_map (rm_hom f) (bm_rsmul E e s) := eq_refl.

Lemma lhs_act_respects (M : RModObject R) :
  Proper (equiv ==> equiv ==> equiv) (lhs_act M).
Proof.
  intros s s' Hs f g Hfg e; simpl.
  transitivity (cmon_map (rm_hom f) (bm_rsmul E e s')).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_respects E e e (reflexivity e) s s' Hs)).
  - exact (Hfg _).
Qed.

Lemma lhs_act_distr_l (M : RModObject R) (s : SC)
  (f g : bm_left E ~{RMod R}~> M) :
  lhs_act M s (cmon_plus (lhs_group M) f g)
    ≈ cmon_plus (lhs_group M) (lhs_act M s f) (lhs_act M s g).
Proof. intro e; reflexivity. Qed.

Lemma lhs_act_distr_r (M : RModObject R) (s s' : SC)
  (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_add (ring_rig S) s s') f
    ≈ cmon_plus (lhs_group M) (lhs_act M s f) (lhs_act M s' f).
Proof.
  intro e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (bm_rsmul E e s) (bm_rsmul E e s'))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_distr_r E e s s')).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.

Lemma lhs_act_assoc (M : RModObject R) (s s' : SC)
  (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_mul (ring_rig S) s s') f
    ≈ lhs_act M s (lhs_act M s' f).
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (bm_rsmul_assoc E e s s')).
Qed.

Lemma lhs_act_one (M : RModObject R) (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_one (ring_rig S)) f ≈ f.
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _ (bm_rsmul_one E e)).
Qed.

Definition LHomSObj (M : RModObject R) : RModObject S :=
  @Build_RModObject S
    (lhs_group M)
    (lhs_act M)
    (lhs_act_respects M)
    (lhs_act_distr_l M)
    (lhs_act_distr_r M)
    (lhs_act_assoc M)
    (lhs_act_one M).

Program Definition lhs_map_ab {M M' : RModObject R}
  (g : M ~{RMod R}~> M') : AbHom (lhs_group M) (lhs_group M') := {|
  cmon_map := {| morphism := fun f =>
    (rmod_hom_compose g f : bm_left E ~{RMod R}~> M') |}
|}.
Next Obligation.
  intros M M' g f f' Hf e; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf e)).
Qed.
Next Obligation.
  intros M M' g e; simpl; exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' e; simpl; exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition LHomSMap {M M' : RModObject R}
  (g : M ~{RMod R}~> M') : LHomSObj M ~{RMod S}~> LHomSObj M' := {|
  rm_hom := lhs_map_ab g
|}.
Next Obligation. intros M M' g s f e; reflexivity. Qed.

Program Definition LHomS : RMod R ⟶ RMod S := {|
  fobj := LHomSObj;
  fmap := @LHomSMap
|}.
Next Obligation. intros M M' g g' Hg f e; simpl; exact (Hg _). Qed.
Next Obligation. intros M f e; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f e; reflexivity. Qed.

End BimoduleLeftTensorHom.

(** *** The left-module tensor-hom adjunction *)

Section BimoduleLeftAdjunction.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

Program Definition blt_to_inner {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) :
  bm_left E ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom g) (@bs_gen S EE N e n) |} |}
|}.
Next Obligation.
  intros N M g n e e' He.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen S EE N e e' n n He (reflexivity n)).
Qed.
Next Obligation.
  intros N M g n; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (BalTensor EE N))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l EE N n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n e e'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor EE N)
                     (@bs_gen S EE N e n) (@bs_gen S EE N e' n))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_l S EE N e e' n)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (* (r · e) ⊗ n IS r ·[LTensor] (e ⊗ n) on the nose. *)
  intros N M g n r e.
  exact (rm_map_smul g r (@bs_gen S EE N e n)).
Qed.

Program Definition blt_to_ab {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M) :
  AbHom (rm_ab N) (lhs_group E M) := {|
  cmon_map := {| morphism := fun n => blt_to_inner g n |}
|}.
Next Obligation.
  intros N M g n n' Hn e; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen S EE N e e n n' (reflexivity e) Hn).
Qed.
Next Obligation.
  intros N M g e; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (BalTensor EE N))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r EE N e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n n' e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor EE N)
                     (@bs_gen S EE N e n) (@bs_gen S EE N e n'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_r S EE N e n n')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

(* The forward transpose is S-linear BECAUSE of the balance rule. *)
Program Definition blt_to {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M) : N ~{RMod S}~> LHomSObj E M := {|
  rm_hom := blt_to_ab g
|}.
Next Obligation.
  intros N M g s n e; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (symmetry (@be_balance S EE N s e n)).
Qed.

Program Definition blt_from_bal {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M) :
  BalBiadditive EE N (rm_ab M) := {|
  bal_map := fun e n => cmon_map (rm_hom (cmon_map (rm_hom h) n)) e
|}.
Next Obligation.
  intros N M h e e' He n n' Hn.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom h) n)) e').
  - exact (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom h) n)))
             e e' He).
  - exact (proper_morphism (cmon_map (rm_hom h)) n n' Hn e').
Qed.
Next Obligation.
  intros N M h e e' n.
  exact (cmon_map_plus (rm_hom (cmon_map (rm_hom h) n)) e e').
Qed.
Next Obligation.
  intros N M h e n n'.
  exact (cmon_map_plus (rm_hom h) n n' e).
Qed.
Next Obligation.
  (* Balance is [h]'s own S-linearity read at e. *)
  intros N M h s e n.
  exact (symmetry (rm_map_smul h s n e)).
Qed.

Program Definition blt_from {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M) : LTensor E N ~{RMod R}~> M := {|
  rm_hom := bal_med (blt_from_bal h)
|}.
Next Obligation.
  intros N M h r x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (blt_from_bal h))
                              (lt_smul E N r))
            (cmon_hom_compose (rmod_lmul M r)
                              (bal_med (blt_from_bal h))) _ x).
  intros e n.
  exact (rm_map_smul (cmon_map (rm_hom h) n) r e).
Qed.

Example blt_to_at {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (blt_to g)) n)) e
    = cmon_map (rm_hom g) (@bs_gen S EE N e n) := eq_refl.

Example blt_from_at {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (blt_from h)) (@bs_gen S EE N e n)
    = cmon_map (rm_hom (cmon_map (rm_hom h) n)) e := eq_refl.

Program Definition blt_adj (N : RModObject S) (M : RModObject R) :
  @Isomorphism Sets
    {| carrier := LTensor E N ~{RMod R}~> M;
       is_setoid := @homset (RMod R) (LTensor E N) M |}
    {| carrier := N ~{RMod S}~> LHomSObj E M;
       is_setoid := @homset (RMod S) N (LHomSObj E M) |} := {|
  to   := {| morphism := fun g => blt_to g |};
  from := {| morphism := fun h => blt_from h |}
|}.
Next Obligation. intros N M g g' Hg n e; exact (Hg _). Qed.
Next Obligation.
  intros N M h h' Hh x.
  refine (bal_hom_ext (bal_med (blt_from_bal h))
                      (bal_med (blt_from_bal h')) _ x).
  intros e n; exact (Hh n e).
Qed.
Next Obligation. intros N M h n e; reflexivity. Qed.
Next Obligation.
  intros N M g x.
  refine (bal_hom_ext (bal_med (blt_from_bal (blt_to g)))
                      (rm_hom g) _ x).
  intros e n; reflexivity.
Qed.

Definition bimodule_left_tensor_hom_adjunction :
  LTensorWith E ⊣ LHomS E.
Proof using E R S.
  unshelve eapply (@Build_Adjunction' (RMod R) (RMod S)
                     (LTensorWith E) (LHomS E) blt_adj).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

Definition blt_unit (N : RModObject S) :
  N ~{RMod S}~> LHomSObj E (LTensor E N) :=
  @unit (RMod R) (RMod S) (LTensorWith E) (LHomS E)
    bimodule_left_tensor_hom_adjunction N.

Definition blt_counit (M : RModObject R) :
  LTensor E (LHomSObj E M) ~{RMod R}~> M :=
  @counit (RMod R) (RMod S) (LTensorWith E) (LHomS E)
    bimodule_left_tensor_hom_adjunction M.

Example blt_unit_is_gen (N : RModObject S)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (blt_unit N)) n)) e
    = @bs_gen S EE N e n := eq_refl.

Example blt_counit_is_eval (M : RModObject R)
  (f : bm_left E ~{RMod R}~> M) (e : EC) :
  cmon_map (rm_hom (blt_counit M))
      (@bs_gen S EE (LHomSObj E M) e f)
    = cmon_map (rm_hom f) e := eq_refl.

End BimoduleLeftAdjunction.

(** *** Riehl 4.6.10, at the strength the tree can state *)

(* Riehl's conclusion is right exactness; a whole-tree sweep for
   right-exactness or finite-colimit vocabulary returns three lines, all
   prose in unrelated headers, so there is no [RightExact] and no
   [PreservesFiniteColimits] to inhabit.  What IS available is
   Structure/Limit/Preservation.v:647's [PreservesAllColimits] through
   Adjunction/Continuity.v:239, and preservation of ALL colimits is
   STRICTLY STRONGER than right exactness — it is not the same
   statement, and the difference is disclosed rather than glossed.
   Riehl's Corollary 4.6.9 additivity clause is NOT delivered. *)

Definition bimodule_left_tensor_preserves_colimits
  {R S : RingObject} (E : Bimodule R S) :
  PreservesAllColimits (LTensorWith E) :=
  left_adjoint_preserves_colimits (bimodule_left_tensor_hom_adjunction E).

Definition bimodule_tensor_preserves_colimits
  {R S : RingObject} (E : Bimodule R S) :
  PreservesAllColimits (TensorWith E) :=
  left_adjoint_preserves_colimits (bimodule_tensor_hom_adjunction E).

(* The composite of part (c) is a left adjoint too, so it preserves all
   colimits by the same one-line reading. *)
Definition bimodule_tensor_bimod_preserves_colimits
  {R S T : RingObject} (E : Bimodule R S) (E1 : Bimodule S T) :
  PreservesAllColimits (TensorWith (BimodTensorBimod E E1)) :=
  left_adjoint_preserves_colimits (bimodule_tensor_bimod_adjunction E E1).

(* [Arguments] declared inside a [Section] do not survive its [End], so
   §C's two settings for the projections of [BimodHom] are gone outside
   it; they are restored here, before §F's first use. *)
Arguments bh_hom {R S E E'} b.
Arguments bh_right {R S E E'} b m s.

(** ** F. The second closure, and the two-variable adjunction *)

(* Riehl, "Category Theory in Context", §4.4 Definition 4.4.7: a
   two-variable adjunction is a triple F : A × B → C, G : A^op × C → B,
   H : B^op × C → A with C(F(a,b),c) ≅ B(b,G(a,c)) ≅ A(a,H(b,c)).  For
   [BimodTensor] the first leg is §C's [bimodule_parametrized_adjunction]
   and the bifunctor G is [bimodule_hom_bifunctor]; what is added here is
   the SECOND closure, the right adjoint of ⊗ in the MODULE variable, and
   with it the third leg through Adjunction/Parameter.v:1978's
   [mutually_right_adjoint].

   The second closure of a bimodule tensor is again a BIMODULE: for a
   right R-module N and a right S-module M the abelian group of group
   homomorphisms N → M carries a left R-action (r · f)(n) = f (n ⊲ r) and
   a right S-action (f ⊲ s)(n) = (f n) ⊲ s, and these commute for a
   reason with no content — both sides send n to (f (n ⊲ r)) ⊲ s. *)

Section HomAbBimodule.

Context {R S : RingObject}.

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).

Context (N : RModObject (Ring_op R)).
Context (M : RModObject (Ring_op S)).

Definition hab_group : AbObject :=
  hom_ab Ab_AbEnriched (rm_ab N) (rm_ab M).

Example hab_group_carrier :
  carrier (cmon_setoid hab_group) = (rm_ab N ~{Ab}~> rm_ab M) := eq_refl.

Program Definition hab_lact (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n => cmon_map f (rm_smul N r n) |}
|}.
Next Obligation.
  intros r f n n' Hn.
  exact (proper_morphism (cmon_map f) _ _
           (rm_smul_respects N r r (reflexivity r) n n' Hn)).
Qed.
Next Obligation.
  intros r f; simpl.
  transitivity (cmon_map f (cmon_zero (rm_ab N))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_zero_r N r)).
  - exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros r f n n'; simpl.
  transitivity (cmon_map f
                  (cmon_plus (rm_ab N) (rm_smul N r n) (rm_smul N r n'))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_l N r n n')).
  - exact (cmon_map_plus f _ _).
Qed.

Program Definition hab_ract (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n => rm_smul M s (cmon_map f n) |}
|}.
Next Obligation.
  intros f s n n' Hn.
  exact (rm_smul_respects M s s (reflexivity s) _ _
           (proper_morphism (cmon_map f) n n' Hn)).
Qed.
Next Obligation.
  intros f s; simpl.
  transitivity (rm_smul M s (cmon_zero (rm_ab M))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_zero f)).
  - exact (rm_smul_zero_r M s).
Qed.
Next Obligation.
  intros f s n n'; simpl.
  transitivity (rm_smul M s
                  (cmon_plus (rm_ab M) (cmon_map f n) (cmon_map f n'))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_plus f n n')).
  - exact (rm_smul_distr_l M s _ _).
Qed.

Lemma hab_lact_respects : Proper (equiv ==> equiv ==> equiv) hab_lact.
Proof.
  intros r r' Hr f g Hfg n; simpl.
  transitivity (cmon_map f (rm_smul N r' n)).
  - exact (proper_morphism (cmon_map f) _ _
             (rm_smul_respects N r r' Hr n n (reflexivity n))).
  - exact (Hfg _).
Qed.

Lemma hab_lact_distr_l (r : RC) (f g : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact r (cmon_plus hab_group f g)
    ≈ cmon_plus hab_group (hab_lact r f) (hab_lact r g).
Proof. intro n; reflexivity. Qed.

Lemma hab_lact_distr_r (r r' : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_add (ring_rig R) r r') f
    ≈ cmon_plus hab_group (hab_lact r f) (hab_lact r' f).
Proof.
  intro n; simpl.
  transitivity (cmon_map f
                  (cmon_plus (rm_ab N) (rm_smul N r n) (rm_smul N r' n))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_r N r r' n)).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma hab_lact_assoc (r r' : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_mul (ring_rig R) r r') f ≈ hab_lact r (hab_lact r' f).
Proof.
  intro n; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_assoc N r' r n)).
Qed.

Lemma hab_lact_one (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro n; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_one N n)).
Qed.

Definition hab_left : RModObject R :=
  @Build_RModObject R hab_group hab_lact hab_lact_respects
    hab_lact_distr_l hab_lact_distr_r hab_lact_assoc hab_lact_one.

Lemma hab_ract_respects : Proper (equiv ==> equiv ==> equiv) hab_ract.
Proof.
  intros f g Hfg s s' Hs n; simpl.
  exact (rm_smul_respects M s s' Hs _ _ (Hfg n)).
Qed.

Lemma hab_ract_distr_l (f g : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  hab_ract (cmon_plus hab_group f g) s
    ≈ cmon_plus hab_group (hab_ract f s) (hab_ract g s).
Proof. intro n; simpl; exact (rm_smul_distr_l M s _ _). Qed.

Lemma hab_ract_distr_r (f : rm_ab N ~{Ab}~> rm_ab M) (s s' : SC) :
  hab_ract f (rig_add (ring_rig S) s s')
    ≈ cmon_plus hab_group (hab_ract f s) (hab_ract f s').
Proof. intro n; simpl; exact (rm_smul_distr_r M s s' _). Qed.

Lemma hab_ract_assoc (f : rm_ab N ~{Ab}~> rm_ab M) (s s' : SC) :
  hab_ract f (rig_mul (ring_rig S) s s')
    ≈ hab_ract (hab_ract f s) s'.
Proof. intro n; simpl; exact (rm_smul_assoc M s' s _). Qed.

Lemma hab_ract_one (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_ract f (rig_one (ring_rig S)) ≈ f.
Proof. intro n; simpl; exact (rm_smul_one M _). Qed.

(* The compatibility law holds POINTWISE, with no law of either module
   consumed: both sides send n to (f (n ⊲ r)) ⊲ s. *)
Lemma hab_compat (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  hab_ract (hab_lact r f) s ≈ hab_lact r (hab_ract f s).
Proof. intro n; reflexivity. Qed.

Definition HomAbBimod : Bimodule R S :=
  @Build_Bimodule R S hab_left hab_ract hab_ract_respects
    hab_ract_distr_l hab_ract_distr_r hab_ract_assoc hab_ract_one
    hab_compat.

Example hab_bimod_left_at (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M)
  (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (rm_smul (bm_left HomAbBimod) r f) n
    = cmon_map f (rm_smul N r n) := eq_refl.

Example hab_bimod_right_at (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (bm_rsmul HomAbBimod f s) n
    = rm_smul M s (cmon_map f n) := eq_refl.

End HomAbBimodule.

Arguments hab_group {R S} N M.
Arguments hab_left {R S} N M.
Arguments HomAbBimod {R S} N M.

(** *** The second closure as a functor, and the mirror adjunction *)

Section HomAbFunctorSection.

Context {R S : RingObject}.
Context (N : RModObject (Ring_op R)).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).

Program Definition hab_map_ab {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') :
  RModHom (hab_left N M) (hab_left N M') := {|
  rm_hom := {| cmon_map := {| morphism := fun f =>
    (cmon_hom_compose (rm_hom g) f : rm_ab N ~{Ab}~> rm_ab M') |} |}
|}.
Next Obligation.
  intros M M' g f f' Hf n; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf n)).
Qed.
Next Obligation.
  intros M M' g n; simpl; exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' n; simpl; exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation. intros M M' g r f n; reflexivity. Qed.

Program Definition HomAbMap {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') :
  HomAbBimod N M ~{@BimodCat R S}~> HomAbBimod N M' := {|
  bh_hom := hab_map_ab g
|}.
Next Obligation.
  intros M M' g f s n; simpl.
  exact (rm_map_smul g s (cmon_map f n)).
Qed.

Program Definition HomAbFunctor : ModR S ⟶ @BimodCat R S := {|
  fobj := HomAbBimod N;
  fmap := @HomAbMap
|}.
Next Obligation.
  intros M M' g g' Hg f n; simpl; exact (Hg _).
Qed.
Next Obligation. intros M f n; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f n; reflexivity. Qed.

Example hab_functor_obj (M : RModObject (Ring_op S)) :
  fobj[HomAbFunctor] M = HomAbBimod N M := eq_refl.

(** *** The bijection: bimodule maps into hom_Ab(N, M) *)

Program Definition hbt_to_inner {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M)
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n =>
    cmon_map (rm_hom g) (@bs_gen R N (bm_left E) n e) |}
|}.
Next Obligation.
  intros E M g e n n' Hn.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen R N (bm_left E) n n' e e Hn (reflexivity e)).
Qed.
Next Obligation.
  intros E M g e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l N (bm_left E) e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros E M g e n n'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (@bs_gen R N (bm_left E) n e)
                     (@bs_gen R N (bm_left E) n' e))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_l R N (bm_left E) n n' e)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition hbt_to_hom {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M) :
  RModHom (bm_left E) (hab_left N M) := {|
  rm_hom := {| cmon_map := {| morphism := fun e => hbt_to_inner g e |} |}
|}.
Next Obligation.
  intros E M g e e' He n; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen R N (bm_left E) n n e e' (reflexivity n) He).
Qed.
Next Obligation.
  intros E M g n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r N (bm_left E) n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros E M g e e' n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (@bs_gen R N (bm_left E) n e)
                     (@bs_gen R N (bm_left E) n e'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_r R N (bm_left E) n e e')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (* R-linearity of the transpose IS the balance rule, again. *)
  intros E M g r e n; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (symmetry (@be_balance R N (bm_left E) r n e)).
Qed.

Program Definition hbt_to {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M) :
  E ~{@BimodCat R S}~> HomAbBimod N M := {|
  bh_hom := hbt_to_hom g
|}.
Next Obligation.
  intros E M g e s n; simpl.
  exact (rm_map_smul g s (@bs_gen R N (bm_left E) n e)).
Qed.

Program Definition hbt_from_bal {E : Bimodule R S}
  {M : RModObject (Ring_op S)}
  (h : E ~{@BimodCat R S}~> HomAbBimod N M) :
  BalBiadditive N (bm_left E) (rm_ab M) := {|
  bal_map := fun n e =>
    cmon_map (cmon_map (rm_hom (bh_hom h)) e) n
|}.
Next Obligation.
  intros E M h n n' Hn e e' He.
  transitivity (cmon_map (cmon_map (rm_hom (bh_hom h)) e) n').
  - exact (proper_morphism (cmon_map (cmon_map (rm_hom (bh_hom h)) e))
             n n' Hn).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom h))) e e' He n').
Qed.
Next Obligation.
  intros E M h n n' e.
  exact (cmon_map_plus (cmon_map (rm_hom (bh_hom h)) e) n n').
Qed.
Next Obligation.
  intros E M h n e e'.
  exact (cmon_map_plus (rm_hom (bh_hom h)) e e' n).
Qed.
Next Obligation.
  intros E M h r n e.
  exact (symmetry (rm_map_smul (bh_hom h) r e n)).
Qed.

Program Definition hbt_from {E : Bimodule R S}
  {M : RModObject (Ring_op S)}
  (h : E ~{@BimodCat R S}~> HomAbBimod N M) :
  RTensor E N ~{ModR S}~> M := {|
  rm_hom := bal_med (hbt_from_bal h)
|}.
Next Obligation.
  intros E M h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (hbt_from_bal h)) (rt_smul E N s))
            (cmon_hom_compose (rmod_lmul M s)
                              (bal_med (hbt_from_bal h))) _ x).
  intros n e.
  exact (bh_right h e s n).
Qed.

Program Definition hab_adj (E : Bimodule R S)
  (M : RModObject (Ring_op S)) :
  @Isomorphism Sets
    {| carrier := RTensor E N ~{ModR S}~> M;
       is_setoid := @homset (ModR S) (RTensor E N) M |}
    {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
       is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |} := {|
  to   := {| morphism := fun g => hbt_to g |};
  from := {| morphism := fun h => hbt_from h |}
|}.
Next Obligation. intros E M g g' Hg e n; exact (Hg _). Qed.
Next Obligation.
  intros E M h h' Hh x.
  refine (bal_hom_ext (bal_med (hbt_from_bal h))
                      (bal_med (hbt_from_bal h')) _ x).
  intros n e; exact (Hh e n).
Qed.
Next Obligation. intros E M h e n; reflexivity. Qed.
Next Obligation.
  intros E M g x.
  refine (bal_hom_ext (bal_med (hbt_from_bal (hbt_to g)))
                      (rm_hom g) _ x).
  intros n e; reflexivity.
Qed.

Definition hab_partial_adj :
  Partial_r (@BimodTensor R S) N ⊣ HomAbFunctor.
Proof using N R S.
  unshelve eapply (@Build_Adjunction' (ModR S) (@BimodCat R S)
                     (Partial_r (@BimodTensor R S) N) HomAbFunctor
                     hab_adj).
  - intros E E' M f g e n; reflexivity.
  - intros E M M' f g e n; reflexivity.
Defined.

End HomAbFunctorSection.

Arguments HomAbFunctor {R S} N.

(** *** All three legs of Riehl's Definition 4.4.7 *)

(* The mirror hypothesis of Adjunction/Parameter.v:1795 is a family
   [∀ x, Partial_r F x ⊣ H x], which is exactly what §F has just built;
   [mirror_family] packages it, and [mutually_right_adjoint] (:1978) then
   supplies Riehl's Proposition 4.4.6(iii) — her Exercise 4.4.ii — as an
   inhabitant of Adjunction/Right.v:342's own [AdjointOnTheRight].  With
   §C's [pa_adj] that is all three legs of Definition 4.4.7 for
   [BimodTensor]. *)

Section BimoduleTwoVariable.

Context {R S : RingObject}.

Definition bimodule_mirror_family :
  ParametrizedAdjunction
    ((@BimodTensor R S) ◯ @Swap (@BimodCat R S) (ModR R)) :=
  mirror_family (@BimodTensor R S) (fun N => HomAbFunctor N)
    (fun N => hab_partial_adj N).

Definition bimodule_two_variable_adjunction
  (M : RModObject (Ring_op S)) :
  AdjointOnTheRight
    (mr_left (@bimodule_parametrized_adjunction R S) M)
    (mr_right bimodule_mirror_family M) :=
  mutually_right_adjoint (@bimodule_parametrized_adjunction R S)
    bimodule_mirror_family M.

Example btv_left_obj (M : RModObject (Ring_op S)) (E : Bimodule R S) :
  mr_left (@bimodule_parametrized_adjunction R S) M E = HomSObj E M
  := eq_refl.

Example btv_right_obj (M : RModObject (Ring_op S))
  (N : RModObject (Ring_op R)) :
  mr_right bimodule_mirror_family M N = HomAbBimod N M := eq_refl.

End BimoduleTwoVariable.

(* Riehl's third leg, with its two hom-setoids written out: a map of
   bimodules E → hom_Ab(N, M) is the same thing as a map of right
   R-modules N → hom_S(E, M).  The term is the class's own [aor]. *)
Definition bimodule_third_leg {R S : RingObject}
  (M : RModObject (Ring_op S)) (E : Bimodule R S)
  (N : RModObject (Ring_op R)) :
  @Isomorphism Sets
    {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
       is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |}
    {| carrier := N ~{ModR R}~> HomSObj E M;
       is_setoid := @homset (ModR R) N (HomSObj E M) |} :=
  @aor (@BimodCat R S) (ModR R)
    (mr_left (@bimodule_parametrized_adjunction R S) M)
    (mr_right (@bimodule_mirror_family R S) M)
    (bimodule_two_variable_adjunction M) E N.

(** ** G. A concrete witness at a named pair of rings *)

(* Instance/Mod.v:866's [Ring_Bimodule] makes every ring an
   (R,R)-bimodule over itself and :878's [Int_Bimodule] is that at ℤ, so
   the whole development instantiates with no new algebra.  Everything
   below COMPUTES: the actions, the unit, the counit and both legs of the
   associativity comparison reduce on closed integers.  The stdlib
   identifier [Z] is never named (only the [%Z] numerals carry the
   scope) — the binders go through the ring's own carrier and the
   arithmetic through its own rig laws — so this section adds no [Require]
   to the file. *)

Section IntegerWitness.

Local Notation ZC := (carrier (rig_setoid (ring_rig Int_Ring))).

(* ℤ read as a RIGHT ℤ-module, i.e. as an object of [ModR Int_Ring]. *)
Definition ZRight : RModObject (Ring_op Int_Ring) :=
  bimodule_right_RMod Int_Bimodule.

Local Notation ZG := (@bs_gen Int_Ring ZRight (bm_left Int_Bimodule)).

Example z_tensor_smul_gen (a b s : ZC) :
  rm_smul (RTensor Int_Bimodule ZRight) s (ZG a b)
    = ZG a (rig_mul (ring_rig Int_Ring) b s) := eq_refl.

Example z_tensor_smul_computes :
  rm_smul (RTensor Int_Bimodule ZRight) 5%Z (ZG 2%Z 3%Z) = ZG 2%Z 15%Z
  := eq_refl.

Example z_tensor_unit_computes :
  cmon_map (rm_hom (cmon_map (rm_hom
      (bth_unit Int_Bimodule ZRight)) 2%Z)) 3%Z = ZG 2%Z 3%Z := eq_refl.

Example z_tensor_counit_computes :
  cmon_map (rm_hom (bth_counit Int_Bimodule ZRight))
      (@bs_gen Int_Ring (HomSObj Int_Bimodule ZRight)
         (bm_left Int_Bimodule) (@id (ModR Int_Ring) ZRight) 7%Z)
    = 7%Z := eq_refl.

(* Multiplication is balanced and biadditive, so it descends; it is what
   SEPARATES two generators, since no induction over the quotienting
   relation could produce a negative. *)
(* Every field is a rig law of ℤ applied, so the record literal raises no
   obligation at all: multiplication is biadditive by distributivity and
   balanced by associativity. *)
Definition int_mult_bal :
  BalBiadditive ZRight (bm_left Int_Bimodule) (ring_ab Int_Ring) :=
  @Build_BalBiadditive Int_Ring ZRight (bm_left Int_Bimodule)
    (ring_ab Int_Ring)
    (rig_mul (ring_rig Int_Ring))
    (rig_mul_respects (ring_rig Int_Ring))
    (fun a a' b => rig_distr_r (ring_rig Int_Ring) a a' b)
    (fun a b b' => rig_distr_l (ring_rig Int_Ring) a b b')
    (fun x a b => rig_mul_assoc (ring_rig Int_Ring) a x b).

Example int_mult_gen (a b : ZC) :
  cmon_map (bal_med int_mult_bal) (ZG a b)
    = rig_mul (ring_rig Int_Ring) a b := eq_refl.

Lemma int_tensor_separates :
  (ZG 1%Z 1%Z
     : carrier (cmon_setoid (rm_ab (RTensor Int_Bimodule ZRight))))
    ≈ ZG 1%Z 2%Z → False.
Proof.
  intro H.
  pose proof (bal_med_respects ZRight (bm_left Int_Bimodule)
                int_mult_bal _ _ H) as Hm.
  simpl in Hm; discriminate Hm.
Qed.

(** *** The tensor of two bimodules, and the comparison, at ℤ *)

Local Notation ZZ := (BimodTensorBimod Int_Bimodule Int_Bimodule).
Local Notation ZGG :=
  (@bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
     (bm_left Int_Bimodule)).

Example z_btb_left_computes :
  rm_smul (bm_left ZZ) 2%Z (ZGG 3%Z 5%Z) = ZGG 6%Z 5%Z := eq_refl.

Example z_btb_right_computes :
  bm_rsmul ZZ (ZGG 3%Z 5%Z) 2%Z = ZGG 3%Z 10%Z := eq_refl.

Example z_assoc_to_computes (a b c : ZC) :
  cmon_map (rm_hom (ta_to Int_Bimodule Int_Bimodule ZRight))
      (@bs_gen Int_Ring (RTensor Int_Bimodule ZRight)
         (bm_left Int_Bimodule) (ZG a b) c)
    = @bs_gen Int_Ring ZRight (bm_left ZZ) a (ZGG b c) := eq_refl.

Example z_assoc_from_computes (a b c : ZC) :
  cmon_map (rm_hom (ta_from Int_Bimodule Int_Bimodule ZRight))
      (@bs_gen Int_Ring ZRight (bm_left ZZ) a (ZGG b c))
    = @bs_gen Int_Ring (RTensor Int_Bimodule ZRight)
        (bm_left Int_Bimodule) (ZG a b) c := eq_refl.

(** *** The left-module mirror, and the second closure, at ℤ *)

Example z_ltensor_smul_gen (a b r : ZC) :
  rm_smul (LTensor Int_Bimodule (Ring_RMod Int_Ring)) r
      (@bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
         (Ring_RMod Int_Ring) a b)
    = @bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
        (Ring_RMod Int_Ring) (rig_mul (ring_rig Int_Ring) r a) b
  := eq_refl.

Example z_hab_left_computes (f : rm_ab ZRight ~{Ab}~> rm_ab ZRight)
  (r n : ZC) :
  cmon_map (rm_smul (bm_left (HomAbBimod ZRight ZRight)) r f) n
    = cmon_map f (rig_mul (ring_rig Int_Ring) n r) := eq_refl.

Example z_hab_right_computes (f : rm_ab ZRight ~{Ab}~> rm_ab ZRight)
  (s n : ZC) :
  cmon_map (bm_rsmul (HomAbBimod ZRight ZRight) f s) n
    = rig_mul (ring_rig Int_Ring) (cmon_map f n) s := eq_refl.

End IntegerWitness.
