Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Identity.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Pos.
Require Import Category.Instance.Proset.Monotone.

Generalizable All Variables.

(** * The discrete-poset adjunction: the identity monad over propositional
      setoids, the truncation monad over [Sets], and [Pos_Forget] not
      monadic *)

(* Awodey, "Category Theory", Carnegie Mellon pre-print of the 1st ed.
     (September 2005), §10.3, printed p. 278 (PDF p. 287), read from the
     page image: "An example of a right adjoint that is not monadic is the
     forgetful functor from posets, U : Pos → Sets.  Its left adjoint F is
     the discrete poset functor.  For any set X, therefore, one has as the
     unit the identity function X = UF(X).  The reader can easily show
     that the Eilenberg-Moore category for T = 1_Sets is then just Sets
     itself" (catalog id awodey:10.3:example-pos-not-monadic).
   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §VI.3, book p. 144 (PDF p. 153), runs the same argument for the
     discrete topology; that example is Instance/Top/Monadicity.v's.
   nLab: https://ncatlab.org/nlab/show/monadic+functor
   nLab: https://ncatlab.org/nlab/show/propositional+truncation
   Library: the standard library's Logic/IndefiniteDescription.v

   BACKGROUND.  Awodey's example has the shape of Mac Lane's.  A set
   carries exactly one discrete order, so the unit of the adjunction is
   the identity, the induced monad is the identity monad, its algebras are
   the sets, and the comparison functor is the forgetful functor itself.
   That functor is not full: the identity of a two-element set is monotone
   from the discrete order to the chain false ≤ true, and not back.  So
   the comparison is not an equivalence and U is not monadic.  Awodey
   leaves the argument to the reader.  This file gives one, in two
   settings, because over this library's [Sets] the induced monad is not
   provably the identity monad without an axiom (below).

   THE READING IMPLEMENTED.  Awodey's Sets has a propositional equality.
   The tree's [Sets] (Instance/Sets.v) is Bishop sets, whose ≈ is
   [Type]-valued.  Instance/Pos.v's [PosetObject] has a [Prop]-valued
   order and antisymmetry into ≈, so every poset's setoid is
   propositional ([pos_PropEquiv]: x ≈ y exactly when x ≤ y and y ≤ x).
   A discrete poset that kept the carrier and ≈ of a setoid S would
   therefore supply a [PropEquiv] on S (Lib/Setoid/Propositional.v); an
   arbitrary object of [Sets] has none in the tree, and a [PropEquiv] on
   every object at once is interderivable with the principle
   [SetsTruncElim] below ([all_PropEquiv_trunc], [trunc_all_PropEquiv]),
   itself interderivable with ∀ A, inhabited A → A ([trunc_choice],
   [choice_trunc]).  So the discrete poset changes the ≈ of its setoid:
   [PosDisc S] compares by [inhabited (x ≈ y)].  Two readings follow, and
   both are built.
     - Over propositional setoids.  Instance/Sets/Propositional/Full.v's
       full subcategory [PropSets] is the reading of Awodey's Sets taken
       here.  [PosDiscP], ordered by the setoid's own [pequiv], is left
       adjoint to [PosPForget], which is [Pos_Forget] factored through
       [PropSets].  The unit is the identity function, as on the page, and
       the induced monad is isomorphic to the identity monad in #468's
       [Monads PropSets] with identity components, UNCONDITIONALLY
       ([MPosP_Id_iso]).
     - Over the tree's [Sets].  The discrete poset is [PosDiscP] after the
       reflector [PropSets_trunc] of [Sets] onto [PropSets], on objects and on
       arrows at [eq_refl] ([PosDisc_obj], [PosDisc_map]); the functor
       equation is refused, structurally past the standard library (R19).  The
       induced monad is the monad of that reflection, the truncation of ≈
       ([MPos_trunc_iso]), and not the identity; its functor agrees with the
       reflection's on objects and arrows at [eq_refl] ([TPos_fobj],
       [TPos_fmap]), and the functor equation is refused only through the
       opacity of the tree's own [Qed] proofs (R16; STRENGTHS below).  It is
       isomorphic to the identity monad EXACTLY WHEN ∀ A : Type@{c}, inhabited
       A → A ([MPos_Id_iff]); even a bare morphism of monads into the identity
       monad gives that principle, from this monad ([MPos_to_Id_trunc]) or
       from the monad of any left adjoint of [Pos_Forget]
       ([any_adj_to_Id_trunc]).  The principle is consistent with
       axiom-free Coq and believed independent of it.  It is consistent,
       argued: the axiom
       [constructive_indefinite_description] of the standard library's
       Logic/IndefiniteDescription.v gives it, as fun A h => proj1_sig
       (constructive_indefinite_description (fun _ : A => True) (match h with
       inhabits a => ex_intro _ a I end)); that term compiles, and [Print
       Assumptions] on it lists that axiom alone, so it is not shipped: no
       constant here depends on an axiom.  It follows from informative
       excluded middle, the tree's [IEM@{c}] written out ([choice_of_IEM]), so
       [MPos_IEM_Id_iso] is an in-tree closed conditional; and it is
       interderivable, level for level, with Instance/Sets/Classifier/
       OneLevel.v's [Untruncate@{c}] written out ([untr_of_choice],
       [choice_of_untr]; both written-out hypotheses are those constants at
       [eq_refl], control C53). CORRECTION (#1349): those two are
       Instance/Sets/Propositional/Full.v's now, moved there unchanged.
       It is not provable without an axiom, by a
       normal-form argument, sketched here and not proved in-tree.  A closed
       proof, every constant unfolded, opaque ones included, would normalize
       to λ A h. t with t : A in the context A : Type@{c}, h : inhabited A. As
       A is a variable type, t is neither an abstraction nor a constructor, so
       it is neutral, headed by A, by h or by an eliminator.  A is not an
       inhabitant of A.  An elimination of h returns in [Prop] or [SProp],
       which A is not (the refusal R10 of the probe, "Incorrect elimination"),
       so a spine from h to A must pass through a proposition with singleton
       elimination eliminated into [Type] (e.g. False, eq, True, and, Acc).
       False has no proof in that context: substituting unit for A and
       inhabits tt for h would give a closed proof of False.  The case of eq
       is where the sketch stops: a branch after matching on an equation
       X = A has type P X, not A, so it turns on which equations between A
       and inhabitable types are derivable, which this sketch does not
       settle (nor Acc's functional argument).  So the unprovability is
       argued, not established.  Cf. the HoTT book, IAS 2013, Exercise 3.11,
       for the univalent counterpart.
   Neither reading corrects the page.  Over the tree's [Sets] "the unit
   the identity function X = UF(X)" holds of carriers and functions
   ([TPos_carrier], [MPos_ret]) and is refused of setoids (R4 in the
   probe); over [PropSets] it holds of setoids ([TPosP_setoid]) and is
   refused only of the [PropEquiv] witness, which [PosPForget] recomputes
   from the order (R7, R12).

   IN-TREE CONNECTIONS.
     - Instance/Pos.v: [Pos], [Pos_Forget] and [PosetObject]; its header
       states antisymmetry at the setoid level, which is what forces the
       truncation above.
     - Instance/Sets/Propositional/Full.v: [PropSets], [PropSets_lift] (so
       [PosPForget]), the reflection [PropSets_trunc_Incl] and its bundle
       [PropSets_Reflective], from which Construction/Reflective/ Monadic.v's
       [Reflective_Monadic] gives [PropSets_Incl_Monadic]. [Pos_Forget] is
       [PropSets_Incl] after [PosPForget], on objects and arrows at [eq_refl]
       and ≈ as functors (the functor equation is refused, structurally past
       the standard library: R18): the first factor is monadic (for the
       truncation monad), the second induces the identity monad and is not
       monadic ([PosPForget_not_Monadic]).  Since #1349 that file also
       holds [SquashSetoid], which [trunc_choice] reads, and
       [untr_of_choice] and [choice_of_untr], moved there.
     - Monad/Identity.v ([IdMonad], [IdMonad_EM_equivalence]), #468's
       Monad/Morphism.v ([MonadHom], [Monads]), Monad/Comparison.v
       ([Adjunction_Induced_Monad], [Monadic]); the non-monadicity uses
       Monad/Monadicity/BeckObjects.v's [em_forget_reflects_isos] and
       Theory/Equivalence/FullFaithful.v's [Equivalence_Full], as
       Instance/Top/Monadicity.v does; the chain is ordered by
       Instance/Proset/Monotone.v's [bool_le].
     - Instance/Top/Monadicity.v is Mac Lane's example over [PTopCat]: a
       topology imposes no antisymmetry, so there the discrete space keeps
       its setoid, and the functor, unit and multiplication of the monad
       are the identity at [eq_refl] on objects and arrows.

   WHAT IS HERE.
     - [pos_PropEquiv]; [PosPForget], with [Pos_Forget_factor_obj],
       [Pos_Forget_factor_map] and [Pos_Forget_factor].
     - Over [PropSets]: [PosDiscPObj], [PosDiscP_fmap], [PosDiscP], the
       transposes [posdiscP_from] and [posdiscP_to], [posdiscP_iso] and
       the adjunction [PosDiscP_PosPForget]; [TPosP] and [MPosP] with the
       readbacks [TPosP_setoid], [TPosP_fmap], [TPosP_pequiv], [MPosP_ret]
       and [MPosP_join]; [TPosP_to_id], [id_to_TPosP], the morphisms of
       monads [MPosP_to_Id] and [Id_to_MPosP] with their component
       readbacks, and [MPosP_Id_iso]; [PropSets_EM_Id_equivalence], the
       Eilenberg-Moore sentence for T = 1 at [PropSets].
     - Over [Sets]: [PosDiscObj] (with [PosDiscObj_le]), [PosDisc] (with
       [PosDisc_obj], [PosDisc_map]), [posdisc_from], [posdisc_to],
       [posdisc_iso] and the adjunction [PosDisc_Pos_Forget]; [TPos] and
       [MPos] with [TPos_fobj], [TPos_fmap], [TPos_carrier], [TPos_equiv],
       [MPos_ret] and [MPos_join]; the truncation monad: [TPos_to_trunc],
       [trunc_to_TPos], [MPos_to_trunc], [trunc_to_MPos] and
       [MPos_trunc_iso]; the identity monad: [id_to_TPos] and [Id_to_MPos]
       (unconditional), [SetsTruncElim] (every setoid of [Sets] eliminates
       its own truncation), [MPos_to_Id_trunc] (any morphism of monads
       MPos → IdMonad gives it), [TPos_to_id], [MPos_to_Id] and
       [MPos_Id_iso] (under it), [choice_setoid], [trunc_choice],
       [choice_trunc] and [MPos_Id_iff]; [all_PropEquiv_trunc] and
       [trunc_all_PropEquiv] (a [PropEquiv] on every object of [Sets]);
       [any_adj_to_Id_trunc] (every left adjoint of [Pos_Forget] whose
       [Adjunction] record sits at that lemma's universe instance, the
       strict slot at so);
       [untr_of_choice], [choice_of_untr], [choice_of_IEM] and
       [MPos_IEM_Id_iso] (the principle under the tree's other names).
       CORRECTION (#1349): [choice_setoid] is now
       Instance/Sets/Propositional/Full.v's [SquashSetoid], by
       definition, and [untr_of_choice] and [choice_of_untr] moved to that
       file.
     - Not monadic: [bool_le_antisym], [BoolDiscPos], [BoolChainPos],
       [bool_disc_to_chain], [no_bool_chain_to_disc], [Pos_Forget_not_Full],
       [Pos_Forget_not_ReflectsIsos], [Pos_Forget_not_Monadic] and
       [PosPForget_not_Monadic]; the two negations of [Monadic] hold for
       every adjunction, since the proof is by conservativity.  The
       contrast is [PropSets_Incl_Monadic].

   THE ISSUE'S PREMISES, dated.  Issue #469 was filed on 2026-07-23.  The
   appended Awodey box's "(needs the category of posets from #641)" was
   accurate when filed and has been met since PR #1076 (merged
   2026-08-13).  Its "the induced monad computed to be the identity" is
   delivered over [PropSets] ([MPosP_Id_iso]) and, over the tree's
   [Sets], as the characterization [MPos_Id_iff]: a stated deviation.

   STRENGTHS.  By [eq_refl]: [Pos_Forget_factor_obj],
   [Pos_Forget_factor_map], [TPosP_setoid], [TPosP_fmap], [TPosP_pequiv],
   [MPosP_ret], [MPosP_join], [MPosP_to_Id_component],
   [Id_to_MPosP_component], [PosDiscObj_le], [PosDisc_obj], [PosDisc_map],
   [TPos_fobj], [TPos_fmap], [TPos_carrier], [TPos_equiv], [MPos_ret] and
   [MPos_join].  Up to ≈: [Pos_Forget_factor], in Theory/Functor.v's
   [Functor_Setoid], and the inverse laws of [MPosP_Id_iso],
   [MPos_trunc_iso], [MPos_Id_iso] and [MPos_IEM_Id_iso].

   Refused, each read in a copy of the whole of Test/ProbeMonadicity469.v
   with that one command unguarded, and pinned there with its controls:
   the setoid equation fobj[TPos] S = S (R4) and its cause, the ≈ of
   fobj[TPos] S against that of S (R11); the functor equation
   TPos = Id[Sets] (R5); the unit ret S = id (R6), refused at the type of
   id, fobj[TPos] S not converting with S; over [PropSets], the object
   equation at a pair (S; P) (R7) and its cause, the recomputed [pequiv]
   against that of P (R12), and the same equation at a variable object
   (R20); TPosP = Id[PropSets] (R8); the two monads as equal objects of
   [Monads PropSets] (R9); TPos = PropSets_Incl ◯ PropSets_trunc (R16);
   (TPos; MPos) and the monad of the reflection [PropSets_trunc_Incl] as
   equal objects of [Monads Sets] (R17); the functor equation
   PropSets_Incl ◯ PosPForget = Pos_Forget (R18), so [Pos_Forget_factor]
   is ≈ and no more; and PosDisc = PosDiscP ◯ PropSets_trunc (R19).  R6
   is a type mismatch at [id], a consequence of R4, with no "cannot
   unify" parenthetical; R10, the naive elimination of the truncation
   that [SetsTruncElim] supplies, is refused by the sort discipline
   ("Incorrect elimination"); the other thirteen are conversion refusals
   ("cannot unify").  R8, R9 and R20 compare a variable object with a
   rebuilt pair, and Coq's [sigT] has no η: a variable of [PropSets] does
   not convert with (projT1 X; projT2 X) (R21), where a [SetoidObject], a
   record with primitive projections, does convert with its rebuilt
   record (C52).

   CAUSES.  R16 is OPACITY of the tree's own [Qed] proofs.  It is
   refused in the tree and ACCEPTED in the copy of the dependency closure
   described next.  Three further copies of that copy each make one group
   of obligations opaque again, as in the tree, and rebuild what depends
   on it: [Compose]'s two [Next Obligation]s and its automatically solved
   one (Theory/Functor.v), [Incl]'s (Construction/Subcategory.v), and
   [Pos_Forget]'s three (Instance/Pos.v).  R16 is refused in each of the
   three, with the tree's text (checked by [About] on
   [Compose_obligation_1] to [Compose_obligation_3], [Incl_obligation_1]
   and [Pos_Forget_obligation_1] in each copy: opaque in exactly its own
   group, and all opaque in the tree).  So each group alone keeps TPos
   and the reflection's functor apart, [PosDisc]'s proof fields copying
   [PropSets_trunc]'s.  The other conversion refusals stand in that
   copy, each stripped of its refutation keyword in a copy of the whole
   probe with its universe annotations removed (the copies of the two
   files there have none) and with R16 blanked in the copies of the
   commands that follow it, each refused inside its own command with the
   tree's text.  R4, R5, R7 to R9, R11, R12, R20 and R21 are STRUCTURAL:
   the two sides differ in their data (a truncated ≈, a recomputed
   witness), or one is stuck on a variable of a [sigT], which has no η;
   R21 names no constant of the tree.  R17 to R19 are STRUCTURAL past the
   standard library: their data converts (R16 and the unit of R17 are
   accepted there, and C44, C49 hold in the tree), and the normal forms of
   the proof fields behind R18 and R19 ([fmap_respects] and [fmap_id],
   read by [Eval cbv] there) contain the standard library's opaque
   [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1], the residue
   Instance/Top/Monadicity.v's header records for its R1; for R17, the
   join's function converts there and the join as a setoid morphism is
   refused, and the normal form of [MPos]'s join properness field (read
   by [Eval cbv] there) contains that obligation four times, the
   reflection's none.  The copy: [Transparent Obligations] set and
   every [Qed] turned into [Defined], obligations included (checked by
   [About] on them), in the copy of the dependency closure made for
   Instance/Top/Monadicity.v, whose header names the four files it keeps
   as they are, extended by the ten modules this file adds, all ten
   turned.  The copies of this file and Instance/Sets/Propositional/
   Full.v there are earlier versions, whose constants in these statements
   are unchanged here, with their universe annotations removed, because a
   [Defined] proof exposes universes of its body that the binders here do
   not name.  Every control of the probe before its guard block is
   accepted there too.

   Thirty proofs end [Defined] (counted by token); closing each alone
   [Qed] in a copy of the two files and an earlier version of the probe,
   all but four stop something: [MPosP_Id_iso], [MPos_trunc_iso],
   [MPos_Id_iso] and [MPos_Id_iff] are [Defined] by the data convention
   only, and no control added to the probe since reads through any of
   the four.  CORRECTION (#1349): twenty-nine, by token, [choice_setoid]
   being a definition by [:=] now, of [SquashSetoid], which is [Defined]
   in Instance/Sets/Propositional/Full.v and load-bearing there for
   [trunc_choice] (that file's STRENGTHS).

   UNIVERSES, read off [About]; stdlib caps (compose, ID, Projections,
   projections, prod_rect, Logic_lemmas.equality, and eq_ind, whose first
   carrier is the [rewrite] in [no_bool_chain_to_disc]) left out, and the [+]
   is for them.  [c] is the carriers and homs, [so] the objects of [Sets] and
   [PropSets], [po] the objects of [Pos], and [p0] to [p3] the four auxiliary
   levels of [Pos@{po p0 p1 p2 p3 c}], whose objects are [PosetObject@{c c p0
   p1 p2 p3}]; [Pos_Forget@{po so p0 p2 p1 p3 c}]. Every block that mentions
   [Sets] or [PropSets] carries c < so, and every block where [Pos] occurs
   carries [Pos]'s own block c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c
   <= p0 and c <= p1.  [Set] occurs only as Set < p2, as Set < w in
   [pos_PropEquiv@{w c cp p0 p1 p2 p3}] ([PropEquivObj]'s own bound, w the
   level of the property, cp the proof level of the setoid; the callers take w
   := so and cp := c), and as Set < so and Set < po, which c < so and c < po
   imply.  The further levels: [s] is [Compose]'s strict level (c < s) in
   [TPos], [TPosP] and the readbacks through a composite; [a] and [r] are the
   free levels of the [Adjunction] records of [PosDisc_Pos_Forget] (or
   [PosDiscP_PosPForget]) and [PropSets_trunc_Incl], left by
   [Build_Adjunction']; [m1] and [m2] are [Monads@{so c m1 m2}]'s, with so and
   c below both; [any_adj_to_Id_trunc] names [s], the strict level of the
   [Compose] in the type of [Adjunction_Induced_Monad] (left unnamed it is
   instantiated at so, measured), and [a], its adjunction's free level;
   [untr_of_choice], [choice_of_untr] and [choice_of_IEM] bind c alone, with
   an empty block on Rocq 9.1.1 (their [+] is for the global levels that
   [inhabited] and [sum] carry on Coq 8.19.2 and 8.20.1); the negations of
   monadicity state [Monadic@{m m0 m1 po m3 c so m6}] with exactly [Monadic]'s
   own block there, so they hold at every value of its levels that
   [Pos_Forget] leaves free, the carrier c included (left unnamed, it is
   pinned to [Set], measured); [PropSets_Incl_Monadic] states [Monadic@{m so
   m1 so m3 c so r}], whose last level is the witness adjunction's own, so it
   is r.  No block has an equation.  On Coq 8.19.2 and 8.20.1 the named levels
   and their blocks are the same, and the [+] also covers eq.u0, sigT.u0,
   sigT.u1, inhabited.u0 and, in [choice_of_IEM], sum.u0 (measured by [About]
   there).  CORRECTION (#1349): [untr_of_choice] and [choice_of_untr] are
   Instance/Sets/Propositional/Full.v's now, with the same blocks (by
   [About] before and after); [choice_setoid], now [SquashSetoid] by definition,
   [trunc_choice] and [MPos_Id_iff] keep theirs on Rocq 9.1.1, the
   refutation in [trunc_choice] chosen for that (its comment).  On Coq
   8.19.2 and 8.20.1 those three gain c <= sum.u1, the level
   [SquashSetoid]'s [squash_rel] carries there, which their [+] covers
   (by [About] in overlays of master with this change and of this tree,
   which agree).

   NOT DELIVERED.  The Eilenberg-Moore category of [MPos] is not shown
   equivalent to [PropSets]: it would follow from [MPos_trunc_iso],
   Construction/Reflective/Monadic.v's [Reflective_EM_Equivalence] and
   #468's [mh_EM], and is not composed.  The comparison functors of the
   two adjunctions are not read back (Instance/Top/Monadicity.v does that
   for [PTopCat]).  For [MPosP] itself only the identity monad's
   Eilenberg-Moore equivalence is instantiated.  No in-tree statement
   says that ∀ A, inhabited A → A is unprovable; that is metatheory. *)

(** ** Posets are propositional, and [Pos_Forget] factors through [PropSets] *)

Definition pos_PropEquiv@{w c cp p0 p1 p2 p3 |
  Set < w, Set < p2, c <= w, cp <= w, c <= p0, c <= p1, cp <= p1,
  p2 <= p0, p3 <= p1}
  (P : PosetObject@{c cp p0 p1 p2 p3}) :
  PropEquivObj@{w c cp} (pos_setoid P).
Proof.
  unshelve refine {| pequiv := fun x y => pos_le P x y /\ pos_le P y x |}.
  - intros x y [H1 H2]. exact (pos_antisym P x y H1 H2).
  - intros x y E. split.
    + apply (proj1 (pos_le_respects P x x (reflexivity x) x y E)).
      apply pos_refl.
    + apply (proj1 (pos_le_respects P x y E x x (reflexivity x))).
      apply pos_refl.
Defined.

Definition PosPForget@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Pos@{po p0 p1 p2 p3 c} ⟶ PropSets@{c so} :=
  PropSets_lift@{po c c so} Pos_Forget@{po so p0 p2 p1 p3 c}
    pos_PropEquiv@{so c c p0 p1 p2 p3}.

Example Pos_Forget_factor_obj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (P : Pos@{po p0 p1 p2 p3 c}) :
  fobj[PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3}] P
    = fobj[Pos_Forget@{po so p0 p2 p1 p3 c}] P := eq_refl.

Example Pos_Forget_factor_map@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (P Q : Pos@{po p0 p1 p2 p3 c}) (f : P ~{Pos@{po p0 p1 p2 p3 c}}~> Q) :
  fmap[PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3}] f
    = fmap[Pos_Forget@{po so p0 p2 p1 p3 c}] f := eq_refl.

Definition Pos_Forget_factor@{c so po p0 p1 p2 p3 s a b |
  c < so, c < s, c < b, po <= a, po <= b, c <= a, so <= a, c < po, Set < p2,
  p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @equiv _ (@Functor_Setoid@{a b po s so c} Pos@{po p0 p1 p2 p3 c} Sets@{c so})
    (PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3})
    Pos_Forget@{po so p0 p2 p1 p3 c} :=
  PropSets_lift_Incl@{po c so s a b} Pos_Forget@{po so p0 p2 p1 p3 c}
    pos_PropEquiv@{so c c p0 p1 p2 p3}.

(** ** The discrete poset on a propositional setoid *)

Definition PosDiscPObj@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (X : PropSets@{c so}) : PosetObject@{c c p0 p1 p2 p3} := {|
  pos_setoid := projT1 X;
  pos_le := @pequiv _ _ (projT2 X);
  pos_le_respects := @pequiv_Proper _ _ (projT2 X);
  pos_refl := fun x => pequiv_from x x (reflexivity x);
  pos_trans := fun x y z H K =>
    pequiv_from x z (transitivity (pequiv_to x y H) (pequiv_to y z K));
  pos_antisym := fun x y H _ => pequiv_to x y H
|}.

Definition PosDiscP_fmap@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X Y : PropSets@{c so}} (f : X ~{PropSets@{c so}}~> Y) :
  MonoHom@{p0 p1 p2 p3 p1 p3 c} (PosDiscPObj@{c so p0 p1 p2 p3} X)
    (PosDiscPObj@{c so p0 p1 p2 p3} Y).
Proof.
  refine (@Build_MonoHom (PosDiscPObj@{c so p0 p1 p2 p3} X)
            (PosDiscPObj@{c so p0 p1 p2 p3} Y) (projT1 f) _).
  intros x y H. simpl in *.
  exact (pequiv_from _ _ (proper_morphism (projT1 f) x y (pequiv_to x y H))).
Defined.

Definition PosDiscP@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  PropSets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c}.
Proof.
  unshelve refine (@Build_Functor PropSets@{c so} Pos@{po p0 p1 p2 p3 c}
                     PosDiscPObj@{c so p0 p1 p2 p3}
                     (fun X Y f => PosDiscP_fmap@{c so p0 p1 p2 p3} f)
                     _ _ _).
  - intros X Y f g E x. exact (E x).
  - intros X x. simpl. reflexivity.
  - intros X Y Z f g x. simpl. reflexivity.
Defined.

Definition posdiscP_from@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X : PropSets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (g : X ~{PropSets@{c so}}~> PosPForget@{c so po p0 p1 p2 p3} P) :
  PosDiscP@{c so po p0 p1 p2 p3} X ~{Pos@{po p0 p1 p2 p3 c}}~> P.
Proof.
  refine (@Build_MonoHom (PosDiscPObj@{c so p0 p1 p2 p3} X) P (projT1 g) _).
  intros x y H. simpl in *.
  apply (proj1 (pos_le_respects P (projT1 g x) (projT1 g x) (reflexivity _)
                  (projT1 g x) (projT1 g y)
                  (proper_morphism (projT1 g) x y (pequiv_to x y H)))).
  apply pos_refl.
Defined.

Definition posdiscP_to@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {X : PropSets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (k : PosDiscP@{c so po p0 p1 p2 p3} X ~{Pos@{po p0 p1 p2 p3 c}}~> P) :
  X ~{PropSets@{c so}}~> PosPForget@{c so po p0 p1 p2 p3} P.
Proof. exists (mono_fn k). exact I. Defined.

#[local] Obligation Tactic := idtac.

Program Definition posdiscP_iso@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (X : PropSets@{c so}) (P : Pos@{po p0 p1 p2 p3 c}) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom Pos@{po p0 p1 p2 p3 c}
                    (PosDiscP@{c so po p0 p1 p2 p3} X) P ;
       is_setoid := @homset Pos@{po p0 p1 p2 p3 c}
                      (PosDiscP@{c so po p0 p1 p2 p3} X) P |}
    {| carrier := @hom PropSets@{c so} X
                    (PosPForget@{c so po p0 p1 p2 p3} P) ;
       is_setoid := @homset PropSets@{c so} X
                      (PosPForget@{c so po p0 p1 p2 p3} P) |} := {|
  to   := {| morphism := fun k => posdiscP_to@{c so po p0 p1 p2 p3} k |};
  from := {| morphism := fun g => posdiscP_from@{c so po p0 p1 p2 p3} g |}
|}.
Next Obligation. intros X P k k' H x; exact (H x). Qed.
Next Obligation. intros X P g g' H x; exact (H x). Qed.
Next Obligation. intros X P g x; reflexivity. Qed.
Next Obligation. intros X P k x; reflexivity. Qed.

Definition PosDiscP_PosPForget@{c so po p0 p1 p2 p3 a |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c} PropSets@{c so}
    PosDiscP@{c so po p0 p1 p2 p3} PosPForget@{c so po p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_Adjunction'@{po c c so c c a so} _ _
                     PosDiscP@{c so po p0 p1 p2 p3}
                     PosPForget@{c so po p0 p1 p2 p3}
                     posdiscP_iso@{c so po p0 p1 p2 p3} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(** ** Over [PropSets] the induced monad is the identity monad *)

Definition TPosP@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  PropSets@{c so} ⟶ PropSets@{c so} :=
  PosPForget@{c so po p0 p1 p2 p3} ◯ PosDiscP@{c so po p0 p1 p2 p3}.

Definition MPosP@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  @Monad PropSets@{c so} TPosP@{c so po p0 p1 p2 p3 s} :=
  Adjunction_Induced_Monad PosDiscP_PosPForget@{c so po p0 p1 p2 p3 a}.

Example TPosP_setoid@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X) = projT1 X := eq_refl.

Example TPosP_fmap@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X Y : PropSets@{c so}) (f : X ~{PropSets@{c so}}~> Y) :
  projT1 (fmap[TPosP@{c so po p0 p1 p2 p3 s}] f) = projT1 f := eq_refl.

Example TPosP_pequiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) (x y : carrier (projT1 X)) :
  @pequiv _ _ (projT2 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X)) x y
    = (@pequiv _ _ (projT2 X) x y /\ @pequiv _ _ (projT2 X) y x)
  := eq_refl.

Example MPosP_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (@ret _ _ MPosP@{c so po p0 p1 p2 p3 s a} X) = id := eq_refl.

Example MPosP_join@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (X : PropSets@{c so}) :
  projT1 (@join _ _ MPosP@{c so po p0 p1 p2 p3 s a} X) = id := eq_refl.

Definition TPosP_to_id@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  TPosP@{c so po p0 p1 p2 p3 s} ⟹ Id[PropSets@{c so}].
Proof.
  unshelve refine (Build_Transform' (F:=TPosP@{c so po p0 p1 p2 p3 s})
                     (G:=Id[PropSets@{c so}]) (fun X => _) _).
  - exists id. exact I.
  - intros X Y f x; simpl. reflexivity.
Defined.

Definition id_to_TPosP@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Id[PropSets@{c so}] ⟹ TPosP@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[PropSets@{c so}])
                     (G:=TPosP@{c so po p0 p1 p2 p3 s}) (fun X => _) _).
  - exists id. exact I.
  - intros X Y f x; simpl. reflexivity.
Defined.

Definition MPosP_to_Id@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} MPosP@{c so po p0 p1 p2 p3 s a}
    (IdMonad@{so c} PropSets@{c so}).
Proof.
  unshelve refine {| mh_transform := TPosP_to_id@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; reflexivity.
Defined.

Definition Id_to_MPosP@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (IdMonad@{so c} PropSets@{c so})
    MPosP@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := id_to_TPosP@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; reflexivity.
Defined.

Example MPosP_to_Id_component@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (X : PropSets@{c so}) :
  projT1 (transform[mh_transform MPosP_to_Id@{c so po p0 p1 p2 p3 s a}] X)
    = id := eq_refl.

Example Id_to_MPosP_component@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} (X : PropSets@{c so}) :
  projT1 (transform[mh_transform Id_to_MPosP@{c so po p0 p1 p2 p3 s a}] X)
    = id := eq_refl.

Definition MPosP_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  @Isomorphism (Monads@{so c m1 m2} PropSets@{c so})
    (existT _ TPosP@{c so po p0 p1 p2 p3 s} MPosP@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[PropSets@{c so}] (IdMonad@{so c} PropSets@{c so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} PropSets@{c so})
    (existT _ TPosP@{c so po p0 p1 p2 p3 s} MPosP@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[PropSets@{c so}] (IdMonad@{so c} PropSets@{c so}))
    MPosP_to_Id@{c so po p0 p1 p2 p3 s a}
    Id_to_MPosP@{c so po p0 p1 p2 p3 s a} _ _);
    intros x z; simpl; reflexivity.
Defined.

(* Awodey's "the Eilenberg-Moore category for T = 1_Sets is then just Sets
   itself", over [PropSets]: Monad/Identity.v's [IdMonad_EM_equivalence]
   at [PropSets]. *)
Definition PropSets_EM_Id_equivalence@{c so s e | c < so, c < s, so <= e +} :
  EquivalenceOfCategories
    (@EM_Forget@{so c s e} PropSets@{c so} Id[PropSets@{c so}]
       (IdMonad@{so c} PropSets@{c so})) :=
  IdMonad_EM_equivalence@{so c s e} PropSets@{c so}.

(** ** Over [Sets] the discrete poset truncates *)

Definition PosDiscObj@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} (S : Sets@{c so}) :
  PosetObject@{c c p0 p1 p2 p3} :=
  PosDiscPObj@{c so p0 p1 p2 p3} (PropSets_trunc@{c so} S).

Example PosDiscObj_le@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) (x y : carrier S) :
  pos_le (PosDiscObj@{c so p0 p1 p2 p3} S) x y = inhabited (x ≈ y)
  := eq_refl.

Definition PosDisc@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Sets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c}.
Proof.
  unshelve refine (@Build_Functor Sets@{c so} Pos@{po p0 p1 p2 p3 c}
                     PosDiscObj@{c so p0 p1 p2 p3}
                     (fun S T f => PosDiscP_fmap@{c so p0 p1 p2 p3}
                                     (fmap[PropSets_trunc@{c so}] f))
                     _ _ _).
  - intros S T f g E x. exact (inhabits (E x)).
  - intros S x. simpl. exact (inhabits (reflexivity x)).
  - intros S T U f g x. simpl. exact (inhabits (reflexivity _)).
Defined.

Example PosDisc_obj@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) :
  fobj[PosDisc@{c so po p0 p1 p2 p3}] S
    = fobj[PosDiscP@{c so po p0 p1 p2 p3}] (fobj[PropSets_trunc@{c so}] S)
  := eq_refl.

Example PosDisc_map@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S T : Sets@{c so}) (f : S ~{Sets@{c so}}~> T) :
  fmap[PosDisc@{c so po p0 p1 p2 p3}] f
    = fmap[PosDiscP@{c so po p0 p1 p2 p3}] (fmap[PropSets_trunc@{c so}] f)
  := eq_refl.

Definition posdisc_from@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {S : Sets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (g : S ~{Sets@{c so}}~> Pos_Forget@{po so p0 p2 p1 p3 c} P) :
  PosDisc@{c so po p0 p1 p2 p3} S ~{Pos@{po p0 p1 p2 p3 c}}~> P.
Proof.
  unshelve refine (@Build_MonoHom (PosDiscObj@{c so p0 p1 p2 p3} S) P
                     (@Build_SetoidMorphism _ _ _ _ (fun x => g x) _) _).
  - intros x y H. simpl in *.
    apply (@pequiv_elim_inhabited _ _ (pos_PropEquiv@{so c c p0 p1 p2 p3} P)).
    destruct H as [H]. exact (inhabits (proper_morphism g x y H)).
  - intros x y H. simpl in *. destruct H as [H].
    apply (proj1 (pos_le_respects P (g x) (g x) (reflexivity _) (g x) (g y)
                    (proper_morphism g x y H))).
    apply pos_refl.
Defined.

Definition posdisc_to@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  {S : Sets@{c so}} {P : Pos@{po p0 p1 p2 p3 c}}
  (k : PosDisc@{c so po p0 p1 p2 p3} S ~{Pos@{po p0 p1 p2 p3 c}}~> P) :
  S ~{Sets@{c so}}~> Pos_Forget@{po so p0 p2 p1 p3 c} P.
Proof.
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => mono_fn k x) _).
  intros x y H. exact (proper_morphism (mono_fn k) x y (inhabits H)).
Defined.

Program Definition posdisc_iso@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) (P : Pos@{po p0 p1 p2 p3 c}) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom Pos@{po p0 p1 p2 p3 c}
                    (PosDisc@{c so po p0 p1 p2 p3} S) P ;
       is_setoid := @homset Pos@{po p0 p1 p2 p3 c}
                      (PosDisc@{c so po p0 p1 p2 p3} S) P |}
    {| carrier := @hom Sets@{c so} S (Pos_Forget@{po so p0 p2 p1 p3 c} P) ;
       is_setoid := @homset Sets@{c so} S
                      (Pos_Forget@{po so p0 p2 p1 p3 c} P) |} := {|
  to   := {| morphism := fun k => posdisc_to@{c so po p0 p1 p2 p3} k |};
  from := {| morphism := fun g => posdisc_from@{c so po p0 p1 p2 p3} g |}
|}.
Next Obligation. intros S P k k' H x; exact (H x). Qed.
Next Obligation. intros S P g g' H x; exact (H x). Qed.
Next Obligation. intros S P g x; reflexivity. Qed.
Next Obligation. intros S P k x; reflexivity. Qed.

Definition PosDisc_Pos_Forget@{c so po p0 p1 p2 p3 a |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c} Sets@{c so}
    PosDisc@{c so po p0 p1 p2 p3} Pos_Forget@{po so p0 p2 p1 p3 c}.
Proof.
  unshelve refine (@Build_Adjunction'@{po c c so c c a so} _ _
                     PosDisc@{c so po p0 p1 p2 p3}
                     Pos_Forget@{po so p0 p2 p1 p3 c}
                     posdisc_iso@{c so po p0 p1 p2 p3} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(** ** Over [Sets] the induced monad is the truncation monad *)

Definition TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Sets@{c so} ⟶ Sets@{c so} :=
  Pos_Forget@{po so p0 p2 p1 p3 c} ◯ PosDisc@{c so po p0 p1 p2 p3}.

Definition MPos@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  @Monad Sets@{c so} TPos@{c so po p0 p1 p2 p3 s} :=
  Adjunction_Induced_Monad PosDisc_Pos_Forget@{c so po p0 p1 p2 p3 a}.

Example TPos_fobj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  fobj[TPos@{c so po p0 p1 p2 p3 s}] S
    = fobj[PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}] S := eq_refl.

Example TPos_fmap@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S T : Sets@{c so}) (f : S ~{Sets@{c so}}~> T) :
  fmap[TPos@{c so po p0 p1 p2 p3 s}] f
    = fmap[PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}] f := eq_refl.

Example TPos_carrier@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  carrier (fobj[TPos@{c so po p0 p1 p2 p3 s}] S) = carrier S := eq_refl.

Example TPos_equiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) (x y : carrier S) :
  @equiv _ (is_setoid (fobj[TPos@{c so po p0 p1 p2 p3 s}] S)) x y
    = inhabited (x ≈ y) := eq_refl.

Example MPos_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  @Sets.morphism _ _ _ _ (@ret _ _ MPos@{c so po p0 p1 p2 p3 s a} S)
    = (fun x : carrier S => x) := eq_refl.

Example MPos_join@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (S : Sets@{c so}) :
  @Sets.morphism _ _ _ _ (@join _ _ MPos@{c so po p0 p1 p2 p3 s a} S)
    = (fun x : carrier S => x) := eq_refl.

Definition TPos_to_trunc@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  TPos@{c so po p0 p1 p2 p3 s} ⟹ PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}.
Proof.
  unshelve refine (Build_Transform' (F:=TPos@{c so po p0 p1 p2 p3 s})
                     (G:=PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
                     (fun S => id) _).
  intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition trunc_to_TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  PropSets_Incl@{c so} ◯ PropSets_trunc@{c so} ⟹ TPos@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform'
                     (F:=PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
                     (G:=TPos@{c so po p0 p1 p2 p3 s}) (fun S => id) _).
  intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition MPos_to_trunc@{c so po p0 p1 p2 p3 s a r |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a}
    (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r}).
Proof.
  unshelve refine {| mh_transform := TPos_to_trunc@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition trunc_to_MPos@{c so po p0 p1 p2 p3 s a r |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r})
    MPos@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := trunc_to_TPos@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition MPos_trunc_iso@{c so po p0 p1 p2 p3 s a r m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ (PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
       (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ (PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
       (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r}))
    MPos_to_trunc@{c so po p0 p1 p2 p3 s a r}
    trunc_to_MPos@{c so po p0 p1 p2 p3 s a r} _ _);
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

(** ** Over [Sets], when the induced monad is the identity *)

Definition id_to_TPos@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  Id[Sets@{c so}] ⟹ TPos@{c so po p0 p1 p2 p3 s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[Sets@{c so}])
                     (G:=TPos@{c so po p0 p1 p2 p3 s}) (fun S => _) _).
  - unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => x) _).
    intros x y H. exact (inhabits H).
  - intros S T f x; simpl. exact (inhabits (reflexivity _)).
Defined.

Definition Id_to_MPos@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +} :
  MonadHom@{so c} (IdMonad@{so c} Sets@{c so}) MPos@{c so po p0 p1 p2 p3 s a}.
Proof.
  unshelve refine {| mh_transform := id_to_TPos@{c so po p0 p1 p2 p3 s} |};
    intros x z; simpl; exact (inhabits (reflexivity _)).
Defined.

Definition SetsTruncElim@{c so | c < so +} : Type@{so} :=
  ∀ (S : Sets@{c so}) (x y : carrier S), inhabited (x ≈ y) → x ≈ y.

Lemma MPos_to_Id_trunc@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (θ : MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a}
         (IdMonad@{so c} Sets@{c so})) : SetsTruncElim@{c so}.
Proof.
  intros S x y H.
  pose proof (@mh_ret _ _ _ _ _ θ S x) as Hx. simpl in Hx.
  pose proof (@mh_ret _ _ _ _ _ θ S y) as Hy. simpl in Hy.
  refine (transitivity (symmetry Hx) (transitivity _ Hy)).
  exact (@proper_morphism _ _ _ _ (transform[mh_transform θ] S) x y H).
Qed.

Definition TPos_to_id@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (Htrunc : SetsTruncElim@{c so}) :
  TPos@{c so po p0 p1 p2 p3 s} ⟹ Id[Sets@{c so}].
Proof.
  unshelve refine (Build_Transform' (F:=TPos@{c so po p0 p1 p2 p3 s})
                     (G:=Id[Sets@{c so}]) (fun S => _) _).
  - unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => x) _).
    intros x y H. exact (Htrunc S x y H).
  - intros S T f x; simpl. reflexivity.
Defined.

Definition MPos_to_Id@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (Htrunc : SetsTruncElim@{c so}) :
  MonadHom@{so c} MPos@{c so po p0 p1 p2 p3 s a} (IdMonad@{so c} Sets@{c so}).
Proof.
  unshelve refine
    {| mh_transform := TPos_to_id@{c so po p0 p1 p2 p3 s} Htrunc |};
    intros x z; simpl; reflexivity.
Defined.

Definition MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +}
  (Htrunc : SetsTruncElim@{c so}) :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so}))
    (MPos_to_Id@{c so po p0 p1 p2 p3 s a} Htrunc)
    Id_to_MPos@{c so po p0 p1 p2 p3 s a} _ _);
    intros x z; simpl; [ reflexivity | exact (inhabits (reflexivity _)) ].
Defined.

(* [choice_setoid] is Instance/Sets/Propositional/Full.v's [SquashSetoid]
   since #1349, which unified the two: [bool] with x ≈ y the sum
   (x = y) + A.  The [+] allows the cap c <= sum.u1 that [SquashSetoid]
   carries on Coq 8.19.2 and 8.20.1 (the header's UNIVERSES). *)
Definition choice_setoid@{c | +} (A : Type@{c}) : SetoidObject@{c c} :=
  SquashSetoid@{c} A.

(* The setoid read here, [choice_setoid A], has [true ≈ false] the sum of
   A with [true = false], refuted by the standard library's
   [true <> false] in an empty match.  [discriminate] would add
   c <= False_rect.u0 to this block and to [MPos_Id_iff]'s (read by
   [About]); the empty match leaves the block as it was on Rocq 9.1.1
   (the header's UNIVERSES for Coq 8.19.2 and 8.20.1). *)
Lemma trunc_choice@{c so | c < so +} (Htrunc : SetsTruncElim@{c so})
  (A : Type@{c}) : inhabited A → A.
Proof.
  intros H.
  destruct (Htrunc (choice_setoid@{c} A) true false
              (match H with inhabits a => inhabits (inr a) end)) as [e|a].
  - exact (match Bool.diff_true_false e with end).
  - exact a.
Qed.

Lemma choice_trunc@{c so | c < so +}
  (G : ∀ A : Type@{c}, inhabited A → A) : SetsTruncElim@{c so}.
Proof. intros S x y. exact (G (x ≈ y)). Qed.

Definition MPos_Id_iff@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  iffT (@Isomorphism (Monads@{so c m1 m2} Sets@{c so})
          (existT _ TPos@{c so po p0 p1 p2 p3 s}
             MPos@{c so po p0 p1 p2 p3 s a})
          (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})))
       (∀ A : Type@{c}, inhabited A → A).
Proof.
  split.
  - intros Hiso.
    exact (trunc_choice@{c so}
             (MPos_to_Id_trunc@{c so po p0 p1 p2 p3 s a} (to Hiso))).
  - intros G.
    exact (MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2}
             (choice_trunc@{c so} G)).
Defined.

(* A [PropEquiv] on every object of [Sets] is the principle again, in both
   directions. *)
Definition all_PropEquiv_trunc@{c so | c < so +}
  (P : ∀ X : Sets@{c so}, PropEquivObj@{so c c} X) : SetsTruncElim@{c so} :=
  fun S x y H => @pequiv_elim_inhabited _ _ (P S) x y H.

Definition trunc_all_PropEquiv@{c so | c < so +}
  (T : SetsTruncElim@{c so}) (X : Sets@{c so}) : PropEquivObj@{so c c} X :=
  @PropEquiv_of_relation (carrier X) (is_setoid X)
    (fun x y => inhabited (x ≈ y)) (fun x y H => T X x y H)
    (fun x y H => inhabits H).

(* Not only [PosDisc]: a morphism of monads to the identity monad from the
   monad of ANY left adjoint of [Pos_Forget] gives the principle, since the
   poset F S is propositional ([pos_PropEquiv]) and the unit carries x ≈ y
   into it.  "Any" is at this lemma's universe instance: the [Adjunction]
   record's strict slot is so, not a level of its own. *)
Lemma any_adj_to_Id_trunc@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1 +}
  (F : Sets@{c so} ⟶ Pos@{po p0 p1 p2 p3 c})
  (A : @Adjunction@{po c c so c c c c so c a} Pos@{po p0 p1 p2 p3 c}
         Sets@{c so} F Pos_Forget@{po so p0 p2 p1 p3 c})
  (θ : MonadHom@{so c}
         (@Adjunction_Induced_Monad@{po c so c so a s} _ _ _ _ A)
         (IdMonad@{so c} Sets@{c so})) :
  SetsTruncElim@{c so}.
Proof.
  intros S x y H.
  pose proof (@mh_ret _ _ _ _ _ θ S x) as Hx. simpl in Hx.
  pose proof (@mh_ret _ _ _ _ _ θ S y) as Hy. simpl in Hy.
  refine (transitivity (symmetry Hx) (transitivity _ Hy)).
  apply (@proper_morphism _ _ _ _ (transform[mh_transform θ] S)).
  apply (@pequiv_elim_inhabited _ _
           (pos_PropEquiv@{so c c p0 p1 p2 p3} (F S))).
  destruct H as [H]. constructor.
  exact (@proper_morphism _ _ _ _
           (@ret _ _ (Adjunction_Induced_Monad A) S) x y H).
Qed.

(* The principle under the tree's other names for it, written unfolded so
   that this file needs no further [Require]: the hypothesis of
   [choice_of_untr] is Instance/Sets/Classifier/OneLevel.v's
   [Untruncate@{c}] and that of [choice_of_IEM] its [IEM@{c}], each by
   [eq_refl] (control C53 of Test/ProbeMonadicity469.v).
   Instance/Top/Components.v (#462) already states the same links under
   its own names: its [Untruncate_unsquash] has the statement of
   [choice_of_untr], its [unsquash_Untruncate] is the untruncated form of
   [untr_of_choice], and its [SquashSetoid] is the idea of
   [choice_setoid] below; this file does not require that topology file.
   CORRECTION (#1349): unified on the maintainer's decision.
   [untr_of_choice] and [choice_of_untr] moved, names, binders and terms
   unchanged, to Instance/Sets/Propositional/Full.v, which this file
   requires, and Components.v derives its two constants from them;
   [SquashSetoid] moved there too, and [choice_setoid] is now
   [SquashSetoid] by definition.
*)
Definition choice_of_IEM@{c | +} (E : ∀ P : Type@{c}, P + (P → False)) :
  ∀ A : Type@{c}, inhabited A → A :=
  fun A h => match E A with
             | inl a => a
             | inr N => match (match h with inhabits a => N a end) with end
             end.

(* Under informative excluded middle the induced monad IS the identity
   monad, up to isomorphism in [Monads Sets]. *)
Definition MPos_IEM_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +}
  (E : ∀ P : Type@{c}, P + (P → False)) :
  @Isomorphism (Monads@{so c m1 m2} Sets@{c so})
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[Sets@{c so}] (IdMonad@{so c} Sets@{c so})) :=
  MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2}
    (choice_trunc@{c so} (choice_of_IEM@{c} E)).

(** ** Not monadic *)

Lemma bool_le_antisym@{} (x y : bool) :
  bool_le x y → bool_le y x → x = y.
Proof.
  destruct x, y; unfold bool_le; intros H K; try reflexivity.
  - exact (eq_sym (H eq_refl)).
  - exact (K eq_refl).
Qed.

Definition BoolDiscPos@{c p0 p1 p2 p3 |
  Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  : PosetObject@{c c p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_PosetObject bool_setoid_object@{c c} (@eq bool)
                     _ (fun x => eq_refl) (fun x y z H1 H2 => eq_trans H1 H2)
                     (fun x y H _ => H)).
  intros x x' Hx y y' Hy. cbn in Hx, Hy. destruct Hx, Hy.
  exact (conj (fun h => h) (fun h => h)).
Defined.

Definition BoolChainPos@{c p0 p1 p2 p3 |
  Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  PosetObject@{c c p0 p1 p2 p3}.
Proof.
  unshelve refine (@Build_PosetObject bool_setoid_object@{c c} bool_le
                     _ (fun x H => H) (fun x y z H K e => K (H e))
                     bool_le_antisym).
  intros x x' Hx y y' Hy. cbn in Hx, Hy. destruct Hx, Hy.
  exact (conj (fun h => h) (fun h => h)).
Defined.

Definition bool_disc_to_chain@{c po p0 p1 p2 p3 |
  c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  BoolDiscPos@{c p0 p1 p2 p3} ~{Pos@{po p0 p1 p2 p3 c}}~>
    BoolChainPos@{c p0 p1 p2 p3}.
Proof.
  refine (@Build_MonoHom BoolDiscPos@{c p0 p1 p2 p3}
            BoolChainPos@{c p0 p1 p2 p3} setoid_morphism_id _).
  intros x y H e. cbn in H. destruct H. exact e.
Defined.

Lemma no_bool_chain_to_disc@{c po p0 p1 p2 p3 |
  c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (g : BoolChainPos@{c p0 p1 p2 p3} ~{Pos@{po p0 p1 p2 p3 c}}~>
         BoolDiscPos@{c p0 p1 p2 p3}) :
  (∀ b : bool, mono_fn g b = b) → False.
Proof.
  intros Hg.
  assert (H : mono_fn g false = mono_fn g true)
    by (apply (mono_le g); intro e; discriminate e).
  rewrite (Hg false), (Hg true) in H. discriminate H.
Qed.

Lemma Pos_Forget_not_Full@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  Functor.Full Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros HF.
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} setoid_morphism_id)).
  intro b.
  exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
           BoolDiscPos@{c p0 p1 p2 p3} setoid_morphism_id b).
Qed.

Lemma Pos_Forget_not_ReflectsIsos@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +} :
  ReflectsIsos Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros R.
  assert (If : @IsIsomorphism Sets@{c so} _ _
                 (fmap[Pos_Forget@{po so p0 p2 p1 p3 c}]
                    bool_disc_to_chain@{c po p0 p1 p2 p3})).
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ R _ _ _ If) as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3} g). intro b. exact (Hr b).
Qed.

Lemma Pos_Forget_not_Monadic@{c so po p0 p1 p2 p3 m m0 m1 m3 m6 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1,
  c < m0, po <= m, po <= m1, c <= m, c <= m1, c <= m3,
  so <= m, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 po m3 c so m6} Pos_Forget@{po so p0 p2 p1 p3 c} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{c so} _ _
                   (fmap[EM_Forget _]
                      (fmap[K] bool_disc_to_chain@{c po p0 p1 p2 p3})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
             BoolDiscPos@{c p0 p1 p2 p3} g b).
  - exact (Hr b).
Qed.

Lemma PosPForget_not_Monadic@{c so po p0 p1 p2 p3 m m0 m1 m3 m6 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0, c <= p1,
  c < m0, po <= m, po <= m1, c <= m, c <= m1, c <= m3,
  so <= m, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 po m3 c so m6} PosPForget@{c so po p0 p1 p2 p3} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism PropSets@{c so} _ _
                   (fmap[EM_Forget _]
                      (fmap[K] bool_disc_to_chain@{c po p0 p1 p2 p3})))
  end.
  { unshelve econstructor;
      [ exists setoid_morphism_id; exact I | intro b; reflexivity
      | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_bool_chain_to_disc@{c po p0 p1 p2 p3}
           (@prefmap _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
              BoolDiscPos@{c p0 p1 p2 p3} g)).
  intro b. transitivity (projT1 (t_alg_hom[g]) b).
  - exact (@fmap_sur _ _ _ HF BoolChainPos@{c p0 p1 p2 p3}
             BoolDiscPos@{c p0 p1 p2 p3} g b).
  - exact (Hr b).
Qed.

Definition PropSets_Incl_Monadic@{c so r m m1 m3 |
  c < so, so <= m1, so <= m3, c <= m1, c <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m so m1 so m3 c so r} PropSets_Incl@{c so} :=
  Reflective_Monadic PropSets_Reflective@{c so r}.
