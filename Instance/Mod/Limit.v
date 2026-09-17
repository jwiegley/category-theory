Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Mod.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Limits of R-modules are created by the forgetful functor to [Ab] *)

(* Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
             §V.7 Construction 1, book p. 128 (PDF p. 137)
             [maclane:V.7:construction1] -- the first premise of the
             construction ("K-Mod is small-complete")
             §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)
             -- the creation argument itself
             §V.6 Theorem 2, book pp. 125-126 -- Freyd's GAFT, the theorem
             Construction 1 feeds
   nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
   nLab: https://ncatlab.org/nlab/show/Mod
   nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_modules
   Riehl: Category Theory in Context, §5.6 Example 5.6.8

   Mac Lane's §V.7 Construction 1 obtains the tensor product of modules
   from the adjoint functor theorem rather than from generators and
   relations.  The theorem it invokes needs three things of the bilinear-
   maps functor's source: that the source is small-complete, that the
   functor is continuous, and that it has a solution set.  THIS FILE
   DELIVERS THE FIRST, and nothing else: [RMod_Complete], "K-Mod is
   small-complete", together with the continuity of both forgetful
   functors, which the second premise will be checked against.  The
   bilinear-maps functor [Bilin] (Instance/Mod/Tensor.v:784), its
   continuity, the solution set and the adjoint-functor-theorem
   application are all elsewhere -- see NOT DELIVERED.

   ** THE ROUTE: ONE LEVEL UP FROM [Ab], NOT TWO DOWN TO [Sets]

   [RMod_Forget_Ab R] (Instance/Mod.v:300) STRICTLY CREATES every limit,
   and the completeness of [RMod R] is read off from the completeness of
   [Ab] rather than of [Sets].  Given a limiting cone [L] of abelian
   groups over the underlying diagram, there is exactly one scalar action
   on its apex making every projection a module homomorphism
   ([mlim_smul_unique], Mac Lane's §V.1 Theorem 2 in this instance), the
   resulting cone lies over [L] ON THE NOSE ([mlim_over_obj] and
   [mlim_over_legs] are both [eq_refl], because [RMod_Forget_Ab]'s object
   map is the [rm_ab] projection and its morphism map is [rm_hom]), it is
   limiting ([mlim_created]), and a cone of modules whose image is
   limiting is itself limiting ([rmod_reflects]).  Packaged with
   Structure/Limit/Creation.v's own classes --
   [RMod_Forget_Ab_StrictlyCreatesLimit], [RMod_Forget_Ab_CreatesLimit],
   [RMod_Forget_Ab_StrictlyCreatesLimits] and
   [RMod_Forget_Ab_creates_limits] -- from which the corollaries follow by
   application: [RMod_Complete] (Mac Lane's §V.1 Theorem 3),
   [RMod_Forget_Ab_creates_continuous], [RMod_Forget_Ab_PreservesAllLimits]
   and [RMod_Forget_Ab_reflects_limits].

   WHY THAT IS THE RIGHT LEVEL, AND WHAT IT COSTS.  A module is an abelian
   group with an action: Instance/Mod.v:112's [RModObject] EXTENDS
   Instance/Ab.v's [AbObject] by [rm_smul] with [rm_smul_respects] and
   four laws, and [rm_ab] is a coercion.  So exactly ONE operation is
   lifted here -- the action -- where the [Ab] template lifts three
   ([cmon_plus], [cmon_zero], [ab_neg]) and Instance/Grp/Limit.v lifts
   three as well.  The apex's abelian group is not constructed at all:
   [LimitMod]'s [rm_ab] IS [vertex_obj[L]], which is what makes
   [mlim_over_obj] hold by [eq_refl] rather than by an isomorphism.

   AND IT IS CHEAPER THAN THAT SUGGESTS, because the action is built as a
   MEDIATOR IN [Ab] rather than as a function on the carrier.  For a fixed
   scalar [r] the family [fun a => r · (leg j a)] is a homomorphism of
   abelian groups at every [j] -- additive by [rm_smul_distr_l], unital by
   Instance/Mod.v:163's [rm_smul_zero_r] -- and coherent by
   [rm_map_smul], so it is a cone in [Ab] over the same diagram
   ([mlim_smul_cone]).  Its mediator [mlim_smul_map] is by construction an
   [Ab]-morphism, and therefore [mlim_smul_distr_l] -- distributivity over
   addition of vectors -- is not proved here at all: it is
   [cmon_map_plus (mlim_smul_map r)], one citation.  The same remark makes
   respectfulness in the SECOND argument free.  The other four clauses
   ([mlim_smul_respects] in its first argument, [mlim_smul_distr_r],
   [mlim_smul_assoc], [mlim_smul_one]) are three lines each: apply joint
   monicity, rewrite the defining triangle [mlim_smul_triangle], apply the
   law in [K j].

   ** THE ENGINE IS BORROWED, NOT COPIED -- THE ONE PLACE THIS FILE
      DEPARTS FROM ITS TEMPLATE

   Every law below rests on [mlim_ext]: two elements of the apex agreeing
   at every leg are equal.  In [Sets] that is proved from the mediator's
   uniqueness with constant maps as probes (Instance/Ab/Limit.v:292's
   [absets_limit_ext]).  In [Ab] the constant maps are not homomorphisms,
   so THAT ARGUMENT DOES NOT TRANSPOSE, and no elementwise joint-monicity
   lemma for [Ab] is proved here either.  Instead the statement is
   transported: [Ab_Forget] preserves limiting cones
   (Instance/Ab/Limit.v:764's [Ab_Forget_creates_continuous], which comes
   from creation and so from [Sets_Complete] alone), so [mlim_sets_limit]
   turns the [Ab]-limit into a [Sets]-limit on the same carrier and
   [absets_limit_ext] applies to it unchanged.  [mrefl_ext] is the same
   move for the reflection half.

   That is a deliberate contrast with the template.  Instance/Ab/Limit.v's
   header discloses that its four generic [Sets] lemmas are
   Instance/Grp/Limit.v's reproved character-for-character under different
   names, and calls factoring them into Instance/Sets/Complete.v the right
   repair.  This file adds no fifth copy: it consumes
   [absets_limit_ext] by importing Instance/Ab/Limit.v, which it must
   import anyway for [Ab_Complete].  The repair the [Ab] header asks for
   is still NOT done -- see NOT DELIVERED -- but the debt is not grown.

   ** THE TWO FORGETFUL FUNCTORS, AND WHY A BRIDGE STANDS BETWEEN THEM

   Instance/Mod.v declares two forgetful functors, [RMod_Forget_Ab] at
   :300 and [RMod_Forget] at :308, and its header records that the second
   is taken directly through the underlying setoid rather than as the
   composite of the first with [Ab_Forget].  Measured here, that record is
   exact on both sides.  The object and morphism parts DO agree
   definitionally -- [rmod_forget_obj_agrees] and
   [rmod_forget_map_agrees] are [eq_refl] -- while the two functor RECORDS
   do not: [RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R] by [eq_refl] is
   refused with "cannot unify \"RMod_Forget R\" and
   \"Ab_Forget ◯ RMod_Forget_Ab R\"", the three law fields being opaque.

   The consequence is that Structure/Limit/Preservation.v:686's
   [continuous_compose] gives [RMod_Forget_composite_continuous :
   ContinuousFunctor (Ab_Forget ◯ RMod_Forget_Ab R)] and NOT continuity of
   [RMod_Forget]: ascribing it is refused with "cannot unify
   \"Cone.Cone (RMod_Forget R ◯ K)\" and
   \"Cone.Cone (Ab_Forget ◯ RMod_Forget_Ab R ◯ K)\"".  So the composite
   lemma IS used -- the question the task put -- and one three-line bridge
   stands beside it: [rmod_abcone_of] repackages a cone over
   [RMod_Forget R ◯ K] as a cone over the composite, field by field,
   exactly as Structure/Limit/Preservation.v:447's [cone_assoc] repackages
   across functor associativity and for exactly the same reason (the
   fields are convertible, the record types are not).
   [RMod_Forget_creates_continuous] is then a term with no tactic in it,
   and [RMod_Forget_PreservesAllLimits] follows.

   ** THE HEADLINE SENTENCE IS MACHINE-CHECKED AT [eq_refl], NOT ARGUED

   At the limits [RMod_Complete] chooses -- [Ab_Complete] over
   [Sets_Complete], hence the compatible families of
   Instance/Sets/Complete.v:144 -- the created module is the
   COORDINATEWISE one on the nose.  [rmod_complete_carrier],
   [rmod_complete_plus], [rmod_complete_zero], [rmod_complete_neg],
   [rmod_complete_smul] and [rmod_complete_leg] are six [eq_refl]
   Examples, at an ARBITRARY ring, an ARBITRARY shape and an ARBITRARY
   diagram of modules.  The fifth is the one that is not inherited from
   the [Ab] file: it says the created ACTION is computed componentwise,
   [`1 (r · a) d = r ·[K d] (`1 a d)], and it survives even though
   [RMod_Complete]'s chosen limit reaches its mediator through
   [creates_limiting] and hence through a cone transport.  Nothing in
   these six is specific to a witness category, and no isomorphism is
   interposed; this file therefore needs no concrete witness to be
   non-vacuous, and builds none.

   ** ON THE HOUSE RULE THAT MORPHISMS ARE COMPARED WITH [≈]

   FOURTEEN statements here write [=] -- the [eq_refl]-witnessed
   [Example]s and [Definition]s outside comments, thirteen of them on one
   [:= eq_refl] line and [mlim_over_obj] with its witness on the next --
   and each does so because both sides are the SAME TERM.  Five compare
   MORPHISMS -- [mlim_over_legs], [rmod_fcone_leg], [rmod_lift_legs],
   [rmod_forget_map_agrees] and [rmod_complete_leg].  They record Mac
   Lane's [F σ = τ] at full strength, which is strictly stronger than the
   [≈] the [StrictLift] clause asks for; every law, every proof and the
   [slift_legs] clause consumed by [rmod_strict_lift] use [≈].  Five
   compare OBJECTS -- [mlim_over_obj], [rmod_fcone_apex],
   [rmod_lift_apex], [rmod_forget_obj_agrees] and
   [rmod_complete_carrier] -- and four compare ELEMENTS --
   [rmod_complete_plus], [rmod_complete_zero], [rmod_complete_neg] and
   [rmod_complete_smul].  Objects and elements are the discipline's
   sanctioned exception.

   ** WHAT WAS IN TREE BEFORE, MEASURED

   Measured on the worktree this file was written against, over all 1016
   other [.v] files by [grep -rlw]: [RMod_Complete],
   [RMod_Forget_Ab_creates], [RMod_Forget_Preserves] and
   [RMod_Forget_reflects] each returned ZERO hits, and so did
   [Complete (RMod], so no completeness, creation, preservation or
   reflection statement about [RMod R] or either forgetful functor
   existed.  Instance/Mod/Product.v has the one product ([ProdMod] at
   :121) and records at :46 that the [HasIndexedProducts (RMod R)]
   instance itself was deliberately not attempted, the universe
   negotiation being left to the issue that needs the class.  That
   decision is untouched and remains correct: the creation route reaches
   completeness without any [HasIndexedProducts] or [HasEqualizers]
   instance at [RMod R], because [creates_limits_Complete] transports the
   whole of [Ab]'s completeness at once.  Nothing here supplies those two
   classes -- see NOT DELIVERED.

   ONE THING THIS FILE IS THE FIRST TO DO, measured by reading every
   occurrence of [creates_limits_Complete] outside Test/ and looking at
   which completeness it is handed.  Three applications name a constant,
   and all three name [Sets_Complete]: Instance/Grp/Limit.v:692,
   Instance/Ab/Limit.v:750 and Instance/Rng/Limit.v:925.  Every other
   application takes its base completeness as a HYPOTHESIS instead --
   Construction/Arrow/Limit.v:427, Construction/Comma/Creation.v:740,
   Construction/Reflective/Limit.v:542,
   Construction/Subcategory/Creation.v:168,
   Construction/Slice/Creation.v:117, :143 and :341,
   Instance/Cat/Creation.v:755, Instance/Fun/Creation.v:559 and
   Monad/Eilenberg/Moore/Limit.v:439, several of them through a derived
   completeness such as [Product_Complete HC HC] or
   [Functor_Category_Complete HX], but none of them naming a constant.
   [RMod_Complete] is therefore the first application in the tree whose
   base is a NAMED completeness other than [Sets_Complete], stacking two
   creation results; the smallness discipline is still [Sets_Complete]'s,
   arriving one indirection further away.  The claim is about this
   application, not about novelty of the machinery, all of which is
   Structure/Limit/Creation.v's.

   ** UNIVERSES, measured off BOTH binder and block over all 68 constants

   The 68 are the 62 declaration heads (46 [def], 16 [prf] in the [.glob])
   plus the six [Program] obligations, read back with
   [Set Printing Universes] and [About].  ZERO word-bounded [Set]
   occurrences anywhere.  CORRECTION, PR "algebraic carriers are sets"
   (2026-09-17).  This read "That is worth saying because the consumer
   this file exists for does meet one", and cited a solution set
   elaborated at [SolutionSet@{Set …}] out of Instance/Discrete.v:59's
   unannotated [DiscreteCat_Functor].  That artifact was repaired at
   Instance/Discrete.v:81 and the literal [Set] is gone.  The cost the
   consumer meets now is a different and smaller one, [Set < carrier],
   measured at Instance/Grp/FreeAFT.v:127-146; nothing here narrows
   anything to [Set], and the disclosure is owed at the application.

   [RMod_Complete@{u u0 u1 u2 u3 u4} :
    ∀ R : RingObject@{u u3 u4}, Complete@{u u u u0}], with [u < u0] and
   [u < u1] and no block equation, which is [Ab_Complete@{u u0 u1} :
   Complete@{u u u u0}] ([u < u0], [u < u1]) and [Sets_Complete]'s
   discipline unchanged, one ring parameter wider.  SEVENTEEN of the 68
   carry no block equation at all, including every top-level corollary
   ([RMod_Complete], [RMod_Forget_Ab_creates_limits],
   [RMod_Forget_Ab_creates_continuous], [RMod_Forget_composite_continuous],
   [RMod_Forget_creates_continuous], [RMod_Forget_Ab_lifts_limits],
   [RMod_lift_cone_unique], the four preservation/reflection readbacks and
   the four [rmod_fcone_*]/[rmod_forget_*] ones).

   THE EQUATIONS THE SECTION CONSTANTS CARRY ARE THE CONTEXT'S, NOT THIS
   FILE'S, and that was measured by isolation rather than guessed: a
   trivial [Example ctx_only : L = L := eq_refl] placed inside the same
   [Context {R} {J} (K) (L)] ALREADY carries [u = u3] together with the
   three strict constraints [u < u4], [u < u5], [u < u7] and the stdlib
   caps [Basics.compose.u0/u1/u2] and [ID.u0].  Here [u] is the ring's
   carrier universe, which [RMod R]'s hom-and-proof universe is
   identified with, and [u3] is the shape's hom-and-proof universe; the
   three strict constraints are the module carrier level below the levels
   of the categories it is stated in, the same shape Instance/Mod/
   Product.v records for its own four constants stated inside [RMod R].

   EXACTLY ONE FURTHER IDENTIFICATION APPEARS, and it enters at one named
   place.  THIRTY-THREE constants additionally carry [u = u2] (and
   [u = u6] or [u = u7], relabellings of the [Limit]'s own level): [u2] is
   the SHAPE'S OBJECT universe.  Isolated the same way, the probe
   [limitcone_isalimit (Ab_Forget_creates_continuous J ...)] -- which is
   [mlim_sets_limit], nothing more -- already carries all three.  The
   donor is therefore [Ab_Complete]'s type [Complete@{u u u u0}]: the
   [Complete] of Structure/Complete.v:115 quantifies over shapes whose
   object, hom and proof universes coincide, so anything that consumes
   [Ab_Forget_creates_continuous] inherits that identification.  It is
   [Sets_Complete]'s own shape, arriving through [Ab_Complete], and is not
   narrowed here.  This is the same sentence Instance/Ab/Limit.v records
   about its own [ab_complete_*] readbacks and Instance/Rng/Limit.v about
   its twelve.

   ** STATUS: axiom-free

   [Print Assumptions] reports "Closed under the global context" for ALL
   68 constants -- the 62 heads and the six obligations -- with zero
   [Axioms:] lines; the obligations answer only to their qualified names
   ([Category.Instance.Mod.Limit.mlim_hom_obligation_1] and the rest).
   All 68 are registered in the Makefile's [make print-assumptions] gate
   block, one [Print Assumptions Category.Instance.Mod.Limit.<name>] line
   each, so the report above is re-run by that target rather than only by
   the scratch file it was first measured with.

   ** MEASURED

   62 [.glob] declaration heads (46 [def], 16 [prf]) and six [Program]
   obligations; the obligation list came from
   [strings Instance/Mod/Limit.vo] filtered on [_obligation_], with the
   junk digit prefix stripped -- four of the six appear ONLY prefixed
   ([5mlim_hom_obligation_1], [5mlim_med_obligation_1],
   [6mrefl_hom_obligation_1], [9mlim_smul_fn_obligation_1]) -- and
   [Print Module Category.Instance.Mod.Limit] lists exactly the same 68
   names, neither side carrying one the other lacks.  All 68 are "Closed
   under the global context" (see STATUS).  Universes: see UNIVERSES; zero
   word-bounded [Set].

   Counted BY TOKEN over the whole file with the criterion
   [grep -o 'Qed\.'] and [grep -o 'Defined\.'] -- the trailing period is
   what keeps the words used in this paragraph out of the count -- the
   numbers are 22 proof terminators of the first kind and THREE of the
   second.  Two of the three transparent ones are LOAD-BEARING, each shown
   so by making it opaque in a copy of the WHOLE file and naming what
   stops.  [mlim_created] flipped
   stops [RMod_Forget_Ab_StrictlyCreatesLimit]'s [screates_limiting]
   clause, which needs [ump_limit] of it to be convertible with the strict
   lift's own cone.  [RMod_Forget_Ab_StrictlyCreatesLimit] flipped stops
   [rmod_lift_apex], whose [eq_refl] then has the wrong type.  The third,
   [rmod_reflects], is NOT load-bearing in this file -- flipped to [Qed]
   the file still compiles, measured -- and is kept transparent only to
   match its template [ab_reflects] (Instance/Ab/Limit.v:656) and to leave
   the reflection witness computable for a downstream consumer.  Said
   plainly so no later reader takes its [Defined] for a measured
   requirement.

   [Require] discipline: 15 imports, closure 53 files excluding this one
   (iterated [coqdep], counting only paths that exist in the worktree).
   At the margin only two carry anything of their own --
   Instance/Mod.v 6 files, Instance/Ab/Limit.v 1 -- and the other 13 cost
   0, being reached through those two.  NONE of the 15 is droppable: each
   was deleted in turn from a copy and the file was recompiled, and each
   deletion stops the build.  Two imports that the first draft carried,
   Theory/Isomorphism.v and Instance/Rng.v, were droppable by that test
   and are gone.

   Zero DECLARATION-HEAD COLLISIONS: none of the 68 names is declared
   anywhere else, measured by scanning every one of the 1017 other
   [.glob] files in the tree for a [def]/[prf]/[ind]/[constr]/[scheme]/
   [inst] head equal to one of them (file list from [find], fed through
   [xargs], so no [.gitignore] traversal rule applies), with
   [Ab_Complete] as the positive control (declared in
   Instance/Ab/Limit.glob, one file) and a nonexistent name as the
   negative.  MENTIONS are a different count and are not zero: over the
   1021 other [.v] files, exactly four mention any of the 68 names --
   Test/ProbeModLimit449.v 36 of them, Instance/Mod/TensorAFT.v 2 (in
   code and in header prose), Test/ProbeModTensorAFT449.v 1 and
   Instance/Mod/Spanning.v 1 (header prose).

   ** NOT DELIVERED

   The tensor product, and every other part of §V.7 Construction 1 beyond
   its first premise.  No continuity of Instance/Mod/Tensor.v:784's
   [Bilin V V'], no solution set, no application of Adjunction/GAFT.v, and
   no universal element obtained that way; Instance/Mod/Tensor.v:826's
   [tensor_UniversalElement] is built by generators and relations and is
   neither used nor compared here.  In particular NOTHING here says the
   tensor product exists, and nothing here is circular with it: the only
   inputs are [Sets_Complete] and Instance/Ab/Limit.v.

   No [HasIndexedProducts (RMod R)] and no [HasEqualizers (RMod R)]
   instance.  These are not gaps the creation route leaves: they are the
   generators one would need on the OTHER route to completeness, and
   [creates_limits_Complete] does not ask for them.  The universe
   negotiation Instance/Mod/Product.v:46 declines is therefore still
   declined, and still open for whichever issue wants the classes
   themselves.

   No colimits and no cocompleteness for [RMod R] (Instance/Mod/
   Coproduct.v has the binary biproduct [RMod_Biproducts] and is not
   touched), and no claim that [RMod_Forget_Ab] creates or preserves any
   colimit.  No
   comparison of the created product with Instance/Mod/Product.v's
   [ProdMod], which would go through a discrete diagram and so through
   Instance/Discrete.v's unannotated [DiscreteCat_Functor].  No
   monadicity statement and no comparison functor, so nothing here says
   [RMod R] IS an Eilenberg-Moore category over [Ab].  No whole-record
   uniqueness statement "[M = LimitMod] for any module [M] on that
   group": [mlim_smul_unique] settles the action, which is all Mac Lane's
   Theorem 2 needs here since the group is not lifted, but the record
   statement would need a Leibniz equality of [rm_ab] and a transport in
   the type of [rm_smul].  No signature-generic statement covering [Grp],
   [Ab], [Rng] and [RMod] at once; the four-lemma duplication
   Instance/Ab/Limit.v discloses between itself and Instance/Grp/Limit.v
   is not repaired here, only not extended.  No right modules: everything
   is stated for [RMod R], and [ModR R] (Instance/Mod.v:712) inherits it
   only
   by being [RMod (Ring_op R)], which is not spelled out.  NOTHING is
   registered as an [Instance] -- a chosen limit must not become globally
   resolvable.  The [eq_refl] readbacks are NOT guarded only by being
   [Example]s here: Test/ProbeModLimit449.v accompanies this file,
   carrying this file's own fifteen [Require]s plus this file plus the two
   the probe itself needs, and restates all fourteen of them as [p449_r1]
   through [p449_r14] from library constants alone, beside four measured
   boundaries [p449_f1] through [p449_f4] -- all four CONVERSION, each
   followed by the term or the positive half that DOES stand there -- and
   an instrument check.  What no probe guards is the universe census and
   the [Defined] transparency measurements above, which rest on being
   re-run.

   ** HOW AN ELEMENT OF A CREATED LIMIT MODULE IS REPRESENTED

   Recorded for whoever checks a functor's continuity elementwise against
   these limits.  At [RMod_Complete R J K] the carrier is
   [Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))]
   ([rmod_complete_carrier], [eq_refl]), whose elements are the dependent
   pairs of Instance/Sets/Complete.v:136: a family [x : ∀ d : J, carrier
   (K d)] paired with a proof that [fmap[K] f (x d) ≈ x d'] for every
   [f : d ~> d'].  Projection is [`1 p d]; two elements are equivalent
   exactly when their families are pointwise equivalent, the proof
   component playing no part.  Every operation is componentwise at
   [eq_refl]: [`1 (a + b) d], [`1 0 d], [`1 (- a) d] and [`1 (r · a) d]
   are [`1 a d + `1 b d], [0], [- (`1 a d)] and [r · (`1 a d)] in [K d]
   ([rmod_complete_plus], [rmod_complete_zero], [rmod_complete_neg],
   [rmod_complete_smul]), and the leg at [d] IS
   [Sets_limit_leg _ d] ([rmod_complete_leg]).  At an abstract [L] rather
   than the chosen one, the corresponding facts are the triangles
   [mlim_smul_triangle] and [mcar_med_commutes] together with
   [mlim_ext]. *)

Section ModLift.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).
Context (L : Limit (RMod_Forget_Ab R ◯ K)).

Definition mlim_leg (j : J) : vertex_obj[L] ~{Ab}~> rm_ab (K j) :=
  limit_leg (limit_is_alimit L) j.

Lemma mlim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  cmon_map (rm_hom (fmap[K] f)) (cmon_map (mlim_leg x) a)
    ≈ cmon_map (mlim_leg y) a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

(* The engine, borrowed rather than reproved.  Constant maps are not
   homomorphisms, so Instance/Ab/Limit.v:292's argument does not transpose
   to [Ab] directly; instead [Ab_Forget] carries the limiting cone down to
   [Sets] on the same carrier, where that lemma applies verbatim.  The
   witness is Instance/Ab/Limit.v:764, which comes from creation and so
   from [Sets_Complete] alone -- no adjunction is presupposed anywhere in
   this chain. *)

Definition mlim_sets_limit :=
  limitcone_isalimit
    (Ab_Forget_creates_continuous J (RMod_Forget_Ab R ◯ K)
       (@limit_cone _ _ _ L) (limit_limitcone L)).

Lemma mlim_ext (x y : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  (∀ j : J, cmon_map (mlim_leg j) x ≈ cmon_map (mlim_leg j) y) → x ≈ y.
Proof. exact (absets_limit_ext mlim_sets_limit x y). Qed.

(** ** The scalar action *)

(* For a fixed scalar [r], multiplication by [r] after the leg at [j] is an
   [Ab]-morphism -- additive by [rm_smul_distr_l], unital by
   Instance/Mod.v:163's [rm_smul_zero_r] -- and these assemble into a cone
   in [Ab] over the same diagram.  Taking the action to be that cone's
   MEDIATOR, rather than a bare function on the carrier, is what makes
   distributivity over vector addition and respectfulness in the second
   argument citations instead of proofs. *)

Program Definition mlim_smul_fn (r : carrier (rig_setoid (ring_rig R)))
  (j : J) :
  cmon_setoid (ab_cmon vertex_obj[L]) ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun a => rm_smul (K j) r (cmon_map (mlim_leg j) a) |}.
Next Obligation.
  intros r j a b Hab.
  now rewrite Hab.
Qed.

Program Definition mlim_smul_leg (r : carrier (rig_setoid (ring_rig R)))
  (j : J) : vertex_obj[L] ~{Ab}~> (RMod_Forget_Ab R ◯ K) j :=
  {| cmon_map := mlim_smul_fn r j |}.
Next Obligation.
  intros r j; simpl.
  rewrite cmon_map_zero.
  apply rm_smul_zero_r.
Qed.
Next Obligation.
  intros r j a b; simpl.
  rewrite cmon_map_plus.
  apply rm_smul_distr_l.
Qed.

Lemma mlim_smul_coherence (r : carrier (rig_setoid (ring_rig R)))
  {x y : J} (f : x ~{J}~> y) :
  fmap[RMod_Forget_Ab R ◯ K] f ∘ mlim_smul_leg r x ≈ mlim_smul_leg r y.
Proof.
  intro a; simpl.
  rewrite (rm_map_smul (fmap[K] f)).
  now rewrite mlim_leg_coherence.
Qed.

Definition mlim_smul_cone (r : carrier (rig_setoid (ring_rig R))) :
  Cone (RMod_Forget_Ab R ◯ K) :=
  @Build_Cone J Ab (RMod_Forget_Ab R ◯ K) vertex_obj[L]
    (@Build_ACone J Ab vertex_obj[L] (RMod_Forget_Ab R ◯ K)
       (mlim_smul_leg r) (@mlim_smul_coherence r)).

Definition mlim_smul_map (r : carrier (rig_setoid (ring_rig R))) :
  vertex_obj[L] ~{Ab}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (mlim_smul_cone r).

Definition mlim_smul (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  carrier (cmon_setoid (ab_cmon vertex_obj[L])) :=
  cmon_map (mlim_smul_map r) a.

Lemma mlim_smul_triangle (r : carrier (rig_setoid (ring_rig R))) (j : J)
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  cmon_map (mlim_leg j) (mlim_smul r a)
    ≈ rm_smul (K j) r (cmon_map (mlim_leg j) a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (mlim_smul_cone r) j a).
Qed.

(** ** The module laws, by joint monicity of the legs *)

Lemma mlim_smul_respects : Proper (equiv ==> equiv ==> equiv) mlim_smul.
Proof.
  intros r r' Hr a a' Ha.
  apply mlim_ext; intro j.
  rewrite !mlim_smul_triangle.
  rewrite Hr.
  now rewrite (proper_morphism (cmon_map (mlim_leg j)) a a' Ha).
Qed.

Lemma mlim_smul_distr_l (r : carrier (rig_setoid (ring_rig R)))
  (a b : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul r (cmon_plus vertex_obj[L] a b)
    ≈ cmon_plus vertex_obj[L] (mlim_smul r a) (mlim_smul r b).
(* Not proved: the mediator is an [Ab]-morphism, so this IS its
   [cmon_map_plus] clause. *)
Proof. exact (cmon_map_plus (mlim_smul_map r) a b). Qed.

Lemma mlim_smul_distr_r (r s : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_add (ring_rig R) r s) a
    ≈ cmon_plus vertex_obj[L] (mlim_smul r a) (mlim_smul s a).
Proof.
  apply mlim_ext; intro j.
  rewrite mlim_smul_triangle.
  rewrite (cmon_map_plus (mlim_leg j)).
  rewrite !mlim_smul_triangle.
  apply rm_smul_distr_r.
Qed.

Lemma mlim_smul_assoc (r s : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_mul (ring_rig R) r s) a ≈ mlim_smul r (mlim_smul s a).
Proof.
  apply mlim_ext; intro j.
  rewrite !mlim_smul_triangle.
  apply rm_smul_assoc.
Qed.

Lemma mlim_smul_one (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_one (ring_rig R)) a ≈ a.
Proof.
  apply mlim_ext; intro j.
  rewrite mlim_smul_triangle.
  apply rm_smul_one.
Qed.

(** ** The lifted module *)

(* The abelian group is not constructed: [rm_ab] IS the apex of [L].  That
   is the whole reason [mlim_over_obj] below is [eq_refl]. *)

Definition LimitMod : RModObject R :=
  {| rm_ab            := vertex_obj[L]
   ; rm_smul          := mlim_smul
   ; rm_smul_respects := mlim_smul_respects
   ; rm_smul_distr_l  := mlim_smul_distr_l
   ; rm_smul_distr_r  := mlim_smul_distr_r
   ; rm_smul_assoc    := mlim_smul_assoc
   ; rm_smul_one      := mlim_smul_one |}.

(** ** The legs are module homomorphisms *)

Program Definition mlim_hom (j : J) : RModHom LimitMod (K j) :=
  {| rm_hom := mlim_leg j |}.
Next Obligation. intros j r m; apply mlim_smul_triangle. Qed.

Lemma mlim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ mlim_hom x ≈ mlim_hom y.
Proof. intro a; exact (mlim_leg_coherence f a). Qed.

Definition mlim_cone : Cone K :=
  @Build_Cone J (RMod R) K LimitMod
    (@Build_ACone J (RMod R) LimitMod K mlim_hom (@mlim_hom_coherence)).

(** ** Strictness: the lifted cone lies over [L] on the nose *)

Definition mlim_over_obj : RMod_Forget_Ab R LimitMod = vertex_obj[L] :=
  eq_refl.

Definition mlim_over_legs (j : J) :
  fmap[RMod_Forget_Ab R] (cone_leg mlim_cone j) = mlim_leg j := eq_refl.

(** ** The lifted cone is limiting *)

Definition mcar_med (N : Cone K) :
  rm_ab vertex_obj[N] ~{Ab}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone (RMod_Forget_Ab R) N).

Lemma mcar_med_commutes (N : Cone K) (j : J)
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mlim_leg j) (cmon_map (mcar_med N) a)
    ≈ cmon_map (rm_hom (cone_leg N j)) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L)
           (FCone (RMod_Forget_Ab R) N) j a).
Qed.

Lemma mcar_med_smul (N : Cone K) (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mcar_med N) (rm_smul vertex_obj[N] r a)
    ≈ mlim_smul r (cmon_map (mcar_med N) a).
Proof.
  apply mlim_ext; intro j.
  rewrite mcar_med_commutes, mlim_smul_triangle, mcar_med_commutes.
  apply (rm_map_smul (cone_leg N j)).
Qed.

Program Definition mlim_med (N : Cone K) :
  vertex_obj[N] ~{RMod R}~> LimitMod := {| rm_hom := mcar_med N |}.
Next Obligation. intros N r m; apply mcar_med_smul. Qed.

Definition mlim_created : IsALimit K LimitMod.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ mlim_cone |}.
  intro N.
  unshelve refine {| unique_obj := mlim_med N |}.
  - intros j a.
    exact (mcar_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L)
             (FCone (RMod_Forget_Ab R) N) (rm_hom v) Hv a).
Defined.

(** ** Uniqueness of the lifted action (Mac Lane's §V.1 Theorem 2) *)

(* The whole of the uniqueness clause AT THIS LEVEL: the abelian group is
   inherited on the nose rather than lifted, so the "exactly one structure
   making every projection a homomorphism" has ONE component here where
   the [Ab] template has three.  Note what is consumed -- only that the
   candidate satisfies the leg conditions, NO law of it -- so the
   statement is sharper than "any module structure on the apex making the
   projections homomorphisms is this one". *)

Lemma mlim_smul_unique
  (s : carrier (rig_setoid (ring_rig R)) →
       carrier (cmon_setoid (ab_cmon vertex_obj[L])) →
       carrier (cmon_setoid (ab_cmon vertex_obj[L])))
  (Hs : ∀ (j : J) r a,
     cmon_map (mlim_leg j) (s r a)
       ≈ rm_smul (K j) r (cmon_map (mlim_leg j) a))
  (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  s r a ≈ mlim_smul r a.
Proof.
  apply mlim_ext; intro j.
  now rewrite Hs, mlim_smul_triangle.
Qed.

End ModLift.

(** * Reflection: a cone of modules whose image is limiting is limiting *)

Section ModReflect.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone (RMod_Forget_Ab R) M)).

Definition mrefl_med (N : Cone K) :
  rm_ab vertex_obj[N] ~{Ab}~> rm_ab vertex_obj[M] :=
  limit_med (limitcone_isalimit HM) (FCone (RMod_Forget_Ab R) N).

Lemma mrefl_med_commutes (N : Cone K) (j : J)
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (rm_hom (cone_leg M j)) (cmon_map (mrefl_med N) a)
    ≈ cmon_map (rm_hom (cone_leg N j)) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM)
           (FCone (RMod_Forget_Ab R) N) j a).
Qed.

Definition mrefl_sets_limit :=
  limitcone_isalimit
    (Ab_Forget_creates_continuous J (RMod_Forget_Ab R ◯ K)
       (FCone (RMod_Forget_Ab R) M) HM).

Lemma mrefl_ext (x y : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[M])))) :
  (∀ j : J, cmon_map (rm_hom (cone_leg M j)) x
              ≈ cmon_map (rm_hom (cone_leg M j)) y) → x ≈ y.
Proof using All. exact (absets_limit_ext mrefl_sets_limit x y). Qed.

Lemma mrefl_med_smul (N : Cone K) (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mrefl_med N) (rm_smul vertex_obj[N] r a)
    ≈ rm_smul vertex_obj[M] r (cmon_map (mrefl_med N) a).
Proof using All.
  apply mrefl_ext; intro j.
  rewrite mrefl_med_commutes.
  rewrite (rm_map_smul (cone_leg N j)).
  rewrite (rm_map_smul (cone_leg M j)).
  now rewrite mrefl_med_commutes.
Qed.

Program Definition mrefl_hom (N : Cone K) :
  vertex_obj[N] ~{RMod R}~> vertex_obj[M] := {| rm_hom := mrefl_med N |}.
Next Obligation. intros N r m; apply mrefl_med_smul. Qed.

Definition rmod_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := mrefl_hom N |}.
  - intros j a.
    exact (mrefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM)
             (FCone (RMod_Forget_Ab R) N) (rm_hom v) Hv a).
Defined.

End ModReflect.

(** * [RMod_Forget_Ab] strictly creates every limit *)

Section ModStrictlyCreates.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

Definition rmod_strict_lift (N : Cone (RMod_Forget_Ab R ◯ K))
  (HN : IsLimitCone N) : StrictLift K (RMod_Forget_Ab R) N :=
  @Build_StrictLift J (RMod R) Ab K (RMod_Forget_Ab R) N
    (mlim_cone K (@Build_Limit J Ab (RMod_Forget_Ab R ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition RMod_Forget_Ab_StrictlyCreatesLimit :
  StrictlyCreatesLimit K (RMod_Forget_Ab R).
Proof.
  unshelve refine {| screates := rmod_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (mlim_created K (@Build_Limit J Ab (RMod_Forget_Ab R ◯ K) N HN))).
  - intros M HM.
    exact (rmod_reflects K M HM).
Defined.

Definition RMod_Forget_Ab_CreatesLimit : CreatesLimit K (RMod_Forget_Ab R) :=
  StrictlyCreatesLimit_CreatesLimit RMod_Forget_Ab_StrictlyCreatesLimit.

End ModStrictlyCreates.

Definition RMod_Forget_Ab_StrictlyCreatesLimits (R : RingObject) :
  StrictlyCreatesLimits (RMod_Forget_Ab R) :=
  fun J K => RMod_Forget_Ab_StrictlyCreatesLimit K.

Definition RMod_Forget_Ab_creates_limits (R : RingObject) :
  CreatesAllLimits (RMod_Forget_Ab R) :=
  fun J K => RMod_Forget_Ab_CreatesLimit K.

Definition RMod_Forget_Ab_reflects_limits {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) : ReflectsLimitCone K (RMod_Forget_Ab R) :=
  creates_reflects_limits (RMod_Forget_Ab_CreatesLimit K).

Definition RMod_lift_cone_unique {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) (N : Cone (RMod_Forget_Ab R ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone (RMod_Forget_Ab R) M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (RMod_Forget_Ab_StrictlyCreatesLimit K) N HN M i.

(** * The image of a cone of modules is the underlying cone of groups *)

Example rmod_fcone_apex {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) :
  vertex_obj[FCone (RMod_Forget_Ab R) N] = rm_ab vertex_obj[N] := eq_refl.

Example rmod_fcone_leg {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) (j : J) :
  cone_leg (FCone (RMod_Forget_Ab R) N) j = rm_hom (cone_leg N j) := eq_refl.

(** * Mac Lane's Theorem 2: the lifting half *)

Definition RMod_Forget_Ab_lifts_limits {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) (L : Limit (RMod_Forget_Ab R ◯ K)) : Limit K :=
  creates_limit_lift (RMod_Forget_Ab_CreatesLimit K) L.

Example rmod_lift_apex {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (vertex_obj[RMod_Forget_Ab_lifts_limits K L])
    = vertex_obj[L] := eq_refl.

Example rmod_lift_legs {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R]
    (cone_leg (@limit_cone _ _ _ (RMod_Forget_Ab_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(** * Corollaries: [RMod R] is complete, and both forgetful functors are
      continuous *)

Definition RMod_Complete (R : RingObject) : @Complete (RMod R) :=
  creates_limits_Complete (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_Ab_creates_continuous (R : RingObject) :
  ContinuousFunctor (RMod_Forget_Ab R) :=
  creates_limits_continuous (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_Ab_PreservesAllLimits (R : RingObject) :
  PreservesAllLimits (RMod_Forget_Ab R) :=
  creates_limits_PreservesAllLimits (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_composite_continuous (R : RingObject) :
  ContinuousFunctor (Ab_Forget ◯ RMod_Forget_Ab R) :=
  continuous_compose (RMod_Forget_Ab_creates_continuous R)
    Ab_Forget_creates_continuous.

(* Instance/Mod.v's header says [RMod_Forget] agrees with the composite on
   objects and morphisms but is not the same record.  Both halves, read
   back.  The negative half is not stated as an [Example] -- it is a
   refusal, quoted in the header with its exact text. *)

Example rmod_forget_obj_agrees {R : RingObject} (M : RMod R) :
  RMod_Forget R M = (Ab_Forget ◯ RMod_Forget_Ab R) M := eq_refl.

Example rmod_forget_map_agrees {R : RingObject} {M N : RMod R}
  (f : M ~{RMod R}~> N) :
  fmap[RMod_Forget R] f = fmap[Ab_Forget ◯ RMod_Forget_Ab R] f := eq_refl.

Section ModForgetCone.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

(* The repackaging bridge: same apex, same legs, same coherence proof, a
   different record type.  Structure/Limit/Preservation.v:447's
   [cone_assoc] is the same move across functor associativity. *)

Definition rmod_abcone_of (N : Cone (RMod_Forget R ◯ K)) :
  Cone ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K) :=
  @Build_Cone J Sets ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K)
    (@vertex_obj _ _ _ N)
    (@Build_ACone J Sets (@vertex_obj _ _ _ N)
       ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

End ModForgetCone.

Definition RMod_Forget_creates_continuous (R : RingObject) :
  ContinuousFunctor (RMod_Forget R) :=
  fun J K N HN M =>
    RMod_Forget_composite_continuous R J K N HN (rmod_abcone_of K M).

Definition RMod_Forget_PreservesAllLimits (R : RingObject) :
  PreservesAllLimits (RMod_Forget R) :=
  Continuous_PreservesAllLimits (RMod_Forget_creates_continuous R).

(** * "Limits of modules are computed componentwise", literally *)

(* At the limits [RMod_Complete] chooses -- [Ab_Complete] over
   [Sets_Complete], hence the compatible families of
   Instance/Sets/Complete.v -- the created module is the coordinatewise
   one ON THE NOSE: carrier, addition, zero, negation, SCALAR ACTION and
   every projection are all [eq_refl], at an arbitrary ring, an arbitrary
   shape and an arbitrary diagram of modules.  The fifth is the one with
   no counterpart in the template, and it holds even though the chosen
   limit reaches its mediator through [creates_limiting]. *)

Section RModComputed.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

Example rmod_complete_carrier :
  cmon_setoid (ab_cmon (rm_ab (vertex_obj[RMod_Complete R J K])))
    = Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) := eq_refl.

Example rmod_complete_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (cmon_plus (rm_ab (vertex_obj[RMod_Complete R J K])) a b) d
    = cmon_plus (rm_ab (K d)) (`1 a d) (`1 b d) := eq_refl.

Example rmod_complete_zero (d : J) :
  `1 (cmon_zero (rm_ab (vertex_obj[RMod_Complete R J K]))) d
    = cmon_zero (rm_ab (K d)) := eq_refl.

Example rmod_complete_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (ab_neg (rm_ab (vertex_obj[RMod_Complete R J K])) a) d
    = ab_neg (rm_ab (K d)) (`1 a d) := eq_refl.

Example rmod_complete_smul (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (rm_smul (vertex_obj[RMod_Complete R J K]) r a) d
    = rm_smul (K d) r (`1 a d) := eq_refl.

Example rmod_complete_leg (d : J) :
  cmon_map (rm_hom (cone_leg (@limit_cone _ _ _ (RMod_Complete R J K)) d))
    = Sets_limit_leg (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) d := eq_refl.

End RModComputed.
