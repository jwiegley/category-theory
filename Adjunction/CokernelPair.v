Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The cokernel pair is left adjoint to the equalizer *)

(* nLab:      https://ncatlab.org/nlab/show/cokernel+pair
   nLab:      https://ncatlab.org/nlab/show/equalizer
   nLab:      https://ncatlab.org/nlab/show/regular+monomorphism
   nLab:      https://ncatlab.org/nlab/show/arrow+category
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   Mac Lane, "Categories for the Working Mathematician", Springer GTM 5,
   2nd ed., §IV.2 Exercise 10 (book p. 90): in a category with cokernel
   pairs and equalizers, sending an arrow to its cokernel pair is a
   functor from the ARROW category to the category of PARALLEL PAIRS,
   and it is LEFT ADJOINT to sending a parallel pair to its equalizing
   arrow.

   Both endpoints are already in the tree and neither is rebuilt here.
   An object of the arrow category [Arrow C] (Construction/Arrow.v:131,
   the comma [Id[C] ↓ Id[C]]) is a triple (a, b; f) with f : a ~> b, and
   a morphism (a,b;f) ~> (a',b';f') is a pair (h1, h2) with the square
   f' ∘ h1 ≈ h2 ∘ f, two such being identified when their COMPONENTS
   agree, the square proof being irrelevant to ≈.  A parallel pair in C
   is an object of the functor category [[Parallel, C]] over
   Instance/Parallel.v:80's walking parallel pair -- the site
   Adjunction/Diagonal/Finite.v:709's [EqualizerFunctor] already uses --
   and a morphism of parallel pairs is a [Transform], its naturality at
   the two non-identity arrows being exactly the two squares.

   ------------------------------------------------------------------
   ** What is delivered

     - [CokernelPairFunctor : Arrow C ⟶ [Parallel, C]] under
       [HasPushouts C], and [EqualizerArrowFunctor : [Parallel, C] ⟶
       Arrow C] under [HasEqualizers C].  Both functor laws and
       [fmap_respects] are PROVED for each -- none is discharged by a
       [Program] default.  Each of the six splits into a cheap branch
       (a component equation, or [fmap_id]) and one appeal to a
       universal property's uniqueness clause: the three on the
       cokernel-pair side spend [ckp_fmap_Y_unique], which is
       Theory/Morphisms/CokernelPair.v:455's [ckp_med_unique]
       specialized to this file's mediator, and the three on the
       equalizer side spend [eqa_fmap1_unique], which is the
       [uniqueness] of Structure/Equalizer/Fork.v:58's [eq_desc].
     - [CokernelPair_Equalizer_Adjunction : CokernelPairFunctor ⊣
       EqualizerArrowFunctor], built with Theory/Adjunction.v:159's
       [Build_Adjunction'] (the hom-setoid isomorphism plus TWO
       naturality clauses; the full [Class Adjunction] at :133 wants
       four, and [Build_Adjunction'] derives the other two).
     - The unit and counit by name -- [cokernel_pair_unit] and
       [cokernel_pair_counit] -- since the exercise is really about
       them, together with their comparison against the class-produced
       [unit]/[counit] at both grades (see "strengths" below).
     - The characterization the exercise's content amounts to:
       [unit_iso_iff_regular], the unit at A is an isomorphism exactly
       when the arrow of A is an equalizer of its own cokernel pair.
       Both directions are proved.  With it, [split_mono_regular]: a
       split monomorphism IS an equalizer of its cokernel pair, hence
       [split_mono_unit_iso].
     - A non-vacuity pair at [Sets]: the unit at the collapse
       [bool → 1] is NOT an isomorphism, and the unit at the inclusion
       [1 → bool] IS one, with that arrow proved not itself an
       isomorphism so the positive case is not degenerate.

   ------------------------------------------------------------------
   ** What is CONSUMED rather than rebuilt

   THE ISSUE'S "Current state" IS STALE.  It reports that there is no
   cokernel-pair construction at all; there has been one since #323.
   Theory/Morphisms/CokernelPair.v:409 declares

       cokernel_pair `{HasPushouts C} (f : x ~> y) : IsPushout f f
         := pushout f f

   with the accessor family [ckp_obj] (:428), [ckp_left]/[ckp_right]
   (:432/:433), [ckp_commutes] (:436), [ckp_ump] (:440), [ckp_med]
   (:444), [ckp_med_left]/[ckp_med_right] (:447/:451),
   [ckp_med_unique] (:455) and [ckp_med_eq] (:460).  Every one of
   [cokernel_pair], [ckp_obj], [ckp_left], [ckp_right], [ckp_commutes],
   [ckp_med], [ckp_med_left], [ckp_med_right] and [ckp_med_unique] is
   used below and none is re-declared; the raw
   [pushout_apex]/[pushout_in1]/[pushout_ump] family of
   Structure/Pushout.v:47-125 that those accessors wrap is NOT used
   directly anywhere in this file, so the ckp_* spelling is the one
   taken.  From Structure/Equalizer/Fork.v the class [HasEqualizers]
   (:68), the record [IsEqualizer] (:52) with [fork_eq] (:55) and
   [eq_desc] (:58), and [equalizer_monic] (:83) are likewise consumed.
   A consumer holding the limit-shaped hypothesis instead converts with
   Adjunction/Diagonal/Finite.v:734's
   [HasLimitsOfShape_HasEqualizers]; it is cited, not rebuilt, and this
   file does not require that module.

   ------------------------------------------------------------------
   ** Prior art, measured by TYPE SHAPE

   No declaration head in the tree has type [Arrow _ ⟶ [Parallel, _]] or
   [[Parallel, _] ⟶ Arrow _].  Criterion and measurement, stated
   exactly because the counts moved twice under audit: the single-line
   grep '@?Arrow <ident> ⟶' returns FOUR heads out of the arrow category
   (Construction/Comma/Diagram.v:230/:231 [Arrow_dom]/[Arrow_cod] into
   C; Construction/Displayed/Codomain.v:309 into a total category;
   Theory/Shapes.v:429 [Fun_of_Arrow] into [[_2, C]]), and the grep
   '⟶ @?Arrow' returns TWENTY-TWO lines into it: thirteen in
   Construction/Arrow/Functor.v and nine elsewhere, six of the nine being
   declaration heads -- Theory/Shapes.v:414 [Arrow_of_Fun], Construction/
   Comma/Diagram.v:266 [Comma_to_Arrow], Construction/Cylinder/Arrow.v:81,
   Instance/Cat/Pullback.v:677/:856 [Slice_Arrow]/[Coslice_Arrow], and
   Construction/Displayed/Codomain.v:289 -- and none of the twenty-six
   mentions [Parallel].  The two [FreeWalkingArrow ⟶ FreeParallelPair]
   lines a looser grep also returns are not among them: they match on the
   substrings rather than on the categories.  Read that as a statement
   about DECLARED TYPES, not about meaning: it does not rule out an
   equivalent functor phrased another way.  Adjunction/Diagonal/
   Finite.v:709's [EqualizerFunctor : [Parallel, C] ⟶ C] is the
   object-only half of the right adjoint here, and
   Structure/Regular.v:46's [kernel_pair] is the dual construction at
   object level with no functoriality.

   ------------------------------------------------------------------
   ** MEASURED rather than asserted

   (1) THE COMPARISON WITH [EqualizerFunctor] IS NOT DELIVERED, AND THE
   REASON WAS MEASURED RATHER THAN GUESSED.  The two take DIFFERENT
   hypotheses ([HasEqualizers C] here, [HasLimitsOfShape Parallel C]
   there), so there is no common statement without a bridge.  Supplying
   the bridge does not repair it: in a scratch file out of tree, with
   [HEfromL := HasLimitsOfShape_HasEqualizers L] in scope,

       Definition cmp (G : Parallel ⟶ C) :
         @eqa_obj C HEfromL G = fobj[EqualizerFunctor L] G := eq_refl.

   is REJECTED, with "cannot unify "eqa_obj G" and
   "fobj[EqualizerFunctor L] G"" -- a CONVERSION failure -- while both
   sides typecheck at the same type [Parallel ⟶ C → obj[C]].  The two
   are two independently chosen equalizers and nothing in the tree
   equates them.  That check is not shipped because requiring
   Adjunction/Diagonal/Finite.v would add 36 modules to this file's
   49-module transitive Require closure (measured over the tree's own
   [coqdep] graph).  What IS shipped is the type-shape tie:
   [eqa_dom_functor := Arrow_dom ◯ EqualizerArrowFunctor] has the same
   type [[Parallel, C] ⟶ C], and [eqa_dom_functor_obj] records by
   [eq_refl] that its object action is [eqa_obj].

   (2) THE [HasEqualizers Sets] ROUTE WAS CHOSEN ON A CLOSURE
   MEASUREMENT, AND THE BRIEF'S UNIVERSE REASON DOES NOT HOLD UP.
   Three routes exist.  Measured on the tree's [coqdep] graph against
   this file's other 41 modules of requirements as a base, they add:
   8 modules for Structure/Pullback/Reduction.v:654's
   [HasEqualizers_of_HasPullbacks_Terminal] fed
   Instance/Sets/Pullback.v's [Sets_HasPullbacks] and
   Instance/Sets.v:253's [Sets_Terminal]; 25 for
   Adjunction/GAFT/Sets.v:175's [Sets_HasEqualizers]; 40 for
   Adjunction/Diagonal/Finite.v:1129's [DiagSets_HasEqualizers].  The
   reduction route is taken.  It is ALSO universe-clean, but so is the
   GAFT one, and the contrary suggestion is corrected here rather than
   repeated: measured with [About], [Sets_HasEqualizers@{u u0}]'s
   constraint block is [u0 < u] plus seven [<=] bounds and contains NO
   [Set] -- the [Set] pin that file's header discloses concerns [GAFT]
   and [GAFT_at_Sets_Id], not this constant.  So the deciding reason is
   closure size alone.  Instance/Sets/Pullback.v:74-84 records the
   companion measurement, that reading a PULLBACK off the reduction
   gives the wrong description; nothing analogous applies here, since
   this file never inspects the chosen equalizer.

   (3) UNIVERSES, measured with [Set Printing Universes. About ...] on
   the delivered constants.  [CokernelPair_Equalizer_Adjunction@{u u0 u1
   u2 u3 u4 u5}] is over [C : Category@{u u0 u0}] -- hom identified with
   proof, expressed by REUSING the level variable in the BINDER -- while
   its constraint block contains NO EQUATION AT ALL: every entry is [<]
   or [<=], and there is no [Set] in either binder or block.  The
   identification is INHERITED and has FOUR donors, each rejected ALONE
   under a declared [Constraint ch < cp] with the hom type [x ~> y] and
   [id] accepted at those very levels: [Arrow], [[Parallel, _]],
   [HasPushouts] and [HasEqualizers].  All four are pinned as
   formability negatives in the probe section at the foot of this file;
   each error reads "Cannot enforce cp = ch because ch < cp".  Read
   "four donors" as four sufficient causes, not as four independent
   ones: whether they share an upstream cause is not established.  None
   is claimed unavoidable.

   ------------------------------------------------------------------
   ** Strengths, graded strict-first

   HOLDING AT [eq_refl] (each shipped as an [Example]): the three
   readbacks of the equalizer object of a parallel pair
   ([eqa_ob_dom]/[eqa_ob_cod]/[eqa_ob_mor]); the two legs of a cokernel
   pair read off the diagram it forms ([ckp_pair_one]/[ckp_pair_two]);
   the object action of [eqa_dom_functor]; the SECOND component of the
   unit ([ckp_unit_snd_strict], where the class-produced unit and the
   named one are the identity on the nose); the ParX component of the
   counit ([ckp_counit_X_strict]); and the two [Sets] arrows read out of
   their arrow-category objects.

   REJECTED AT [eq_refl] AND PINNED, each beside a passing control:
   the FIRST component of the unit, and the ParY component of the
   counit.  Both fall back to [≈] and both residues are exhibited rather
   than described.  The class-produced unit is [⌊id⌋], and the identity
   of [[Parallel, C]] is [nat_id], whose component is [fmap[F] id]
   (Theory/Natural/Transformation.v:220) -- which at [ckp_pair A] and
   [ParX] DOES reduce to [id], which is why the second component is
   strict; but the first component is then the equalizer descent of
   [id ∘ ar_mor A] against the named unit's descent of [ar_mor A],
   two different arguments carrying two different fork proofs, so only
   [≈] holds.  Dually the class counit is [⌈id⌉], whose ParY component
   is the cokernel-pair mediator of [par_one G ∘ id, par_two G ∘ id]
   against the named one's mediator of [par_one G, par_two G].  Both
   [≈] forms are proved: [ckp_class_unit_agrees] and
   [ckp_class_counit_agrees].

   ------------------------------------------------------------------
   ** Counts, with their criteria

   108/108 constants closed under the global context, each queried by
   its fully qualified name.  The 108 are the 92 names the [.glob]
   records as declarations -- it lists 94, of which two are the names
   of the two [Fail Example] commands, which declare nothing and never
   reach the environment -- plus the 16 [Program] obligations that no
   [.glob] sweep sees.  The file declares no [Record], [Class] or
   [Inductive], so it has no fields and no [Build_*] constant needing a
   separate sweep.

   Negatives: SEVEN [Fail] commands = SIX negatives of TWO KINDS plus
   one instrument check.  Two are CONVERSION (the strict unit and
   counit components above; each error ends "cannot unify" with no
   universe clause) and four are FORMABILITY (the four universe donors;
   each ends "universe inconsistency: Cannot enforce cp = ch because
   ch < cp").  Each was stripped one at a time, compiled alone, and its
   whole error read to confirm its kind.  The instrument check is a
   reference-not-found, so a [Fail] that has gone vacuous is
   distinguishable from one still firing.

   Every name declared below was swept tree-wide, word-anchored, before
   landing, and THREE COLLISIONS WERE FOUND AND RENAMED AWAY: [par_one]
   and [par_two] are taken by Instance/Proset/Transform.v:537-538 and
   again by Theory/Natural/Transformation/Arrows.v:434-435 (in both
   cases a NAMED ARROW of [Parallel], not this file's [fmap[G]] of one),
   and became [parallel_leg1]/[parallel_leg2]; [SetsEq] is taken by
   Adjunction/Diagonal/Finite.v:1099 for a [HasLimitsOfShape Parallel
   Sets], and became [SetsEqualizers].  Neither of those two modules is
   in this file's Require closure, but [make print-assumptions] loads
   many modules into ONE scope, which is where a shared name silently
   audits the wrong constant.

   ------------------------------------------------------------------
   ** NOT DELIVERED

     - No [RegularMono] class.  The tree has [RegularEpi]
       (Structure/Regular.v:54) and no dual, and this file declares no
       new record, class or inductive at all; the regularity conclusion
       is the bare [IsEqualizer]-valued abbreviation
       [RegularCokernelPair], a [Definition].
     - No comparison of [EqualizerArrowFunctor] with
       Adjunction/Diagonal/Finite.v's [EqualizerFunctor], for the
       measured reason in (1) above; the type-shape tie
       [eqa_dom_functor] is all that is shipped.
     - No monad or comonad from the adjunction, no algebras, and no
       idempotency statement.
     - No dual: nothing is said about the kernel pair and the
       coequalizer, and no functor [Arrow C ⟶ [Parallel, C]] by kernel
       pairs is built.
     - Nothing is proved about which arrows of [Sets] are regular
       monomorphisms in general -- the positive [Sets] witness goes
       through [split_mono_regular], and "monic implies regular in
       Sets" is neither proved nor refuted here.
     - The [Sets] pushout is Instance/Sets/Pushout.v's five-constructor
       inductive closure and the chosen equalizer is a nested pullback,
       so NO element of either apex is computed anywhere below: the two
       [Sets] results are proved by universal properties and by mapping
       OUT (through [collapse_not_monic] and [pick_true_not_epic]),
       never by evaluating a constructor.  The only [eq_refl]s in the
       [Sets] section read the two arrows back out of the arrow objects.
     - No naturality of the unit/counit identifications in A or G
       beyond what the adjunction itself supplies, and no uniqueness
       statement for either functor.
     - No instance registration: [CokernelPairFunctor],
       [EqualizerArrowFunctor] and the adjunction are plain
       [Definition]s, and [SetsEqualizers] is exported to resolution
       only [#[local]]ly inside the witness section. *)

(** ** Reading the two endpoint categories *)

Section Endpoints.

Context {C : Category}.

(* Objects and morphisms of the arrow category, named.  An object of
   [Arrow C] is a triple (a, b; f); a morphism is a pair of components
   together with the comma square, which [ar_square] reads back with
   the two [fmap[Id]]s already gone, [Id]'s arrow action being the
   identity function. *)

Definition ar_dom (A : @Arrow C) : C := fst (`1 A).
Definition ar_cod (A : @Arrow C) : C := snd (`1 A).
Definition ar_mor (A : @Arrow C) : ar_dom A ~> ar_cod A := `2 A.

Definition ar_fst {A B : @Arrow C} (u : A ~> B) : ar_dom A ~> ar_dom B :=
  fst (`1 u).
Definition ar_snd {A B : @Arrow C} (u : A ~> B) : ar_cod A ~> ar_cod B :=
  snd (`1 u).

Lemma ar_square {A B : @Arrow C} (u : A ~> B) :
  ar_mor B ∘ ar_fst u ≈ ar_snd u ∘ ar_mor A.
Proof. exact (`2 u). Qed.

(* The two legs of the parallel pair a functor out of [Parallel] names. *)

Definition parallel_leg1 (G : Parallel ⟶ C) : G ParX ~> G ParY :=
  fmap[G] (true; ParOne).
Definition parallel_leg2 (G : Parallel ⟶ C) : G ParX ~> G ParY :=
  fmap[G] (false; ParTwo).

(* Every endomorphism of a [Parallel] object is the identity, because
   the false-tagged homs at equal endpoints are uninhabited.  These are
   what let naturality over [Parallel] be discharged at an ARBITRARY
   target functor, where a diagram assembled by [APair] would reduce. *)

Lemma par_hom_id_X (k : ParX ~{Parallel}~> ParX) : k ≈ id.
Proof.
  destruct k as [[|] k]; simpl.
  - reflexivity.
  - destruct (ParHom_Id_false_absurd _ k).
Qed.

Lemma par_hom_id_Y (k : ParY ~{Parallel}~> ParY) : k ≈ id.
Proof.
  destruct k as [[|] k]; simpl.
  - reflexivity.
  - destruct (ParHom_Id_false_absurd _ k).
Qed.

Lemma par_fmap_idX (G : Parallel ⟶ C) (k : ParX ~{Parallel}~> ParX) :
  fmap[G] k ≈ id.
Proof. rewrite (par_hom_id_X k); apply fmap_id. Qed.

Lemma par_fmap_idY (G : Parallel ⟶ C) (k : ParY ~{Parallel}~> ParY) :
  fmap[G] k ≈ id.
Proof. rewrite (par_hom_id_Y k); apply fmap_id. Qed.

End Endpoints.

(** ** The cokernel-pair functor *)

Section CokernelPairFunctor.

Context {C : Category}.
Context `{HP : @HasPushouts C}.

(* The chosen cokernel pair of the arrow underlying an object of
   [Arrow C], and its two legs.  Nothing here is new: [cokernel_pair],
   [ckp_obj], [ckp_left] and [ckp_right] are consumed verbatim. *)

Definition ckp_of (A : @Arrow C) : IsPushout (ar_mor A) (ar_mor A) :=
  cokernel_pair (ar_mor A).

Definition ckp_u (A : @Arrow C) : ar_cod A ~> ckp_obj (ckp_of A) :=
  ckp_left (ckp_of A).
Definition ckp_v (A : @Arrow C) : ar_cod A ~> ckp_obj (ckp_of A) :=
  ckp_right (ckp_of A).

Definition ckp_pair (A : @Arrow C) : Parallel ⟶ C :=
  APair (ckp_u A) (ckp_v A).

Lemma ckp_uv_commutes (A : @Arrow C) :
  ckp_u A ∘ ar_mor A ≈ ckp_v A ∘ ar_mor A.
Proof. exact (ckp_commutes (ckp_of A)). Qed.

(* The arrow action.  At [ParX] it is the codomain component of the
   comma morphism; at [ParY] it is the cokernel-pair mediator, whose
   cocone condition is the comma square followed by [ckp_commutes] at
   the target arrow. *)

Lemma ckp_fmap_cocone {A B : @Arrow C} (u : A ~> B) :
  (ckp_u B ∘ ar_snd u) ∘ ar_mor A ≈ (ckp_v B ∘ ar_snd u) ∘ ar_mor A.
Proof.
  rewrite <- !comp_assoc.
  rewrite <- !(ar_square u).
  rewrite !comp_assoc.
  now rewrite (ckp_commutes (ckp_of B)).
Qed.

Definition ckp_fmap_Y {A B : @Arrow C} (u : A ~> B)
  : ckp_obj (ckp_of A) ~> ckp_obj (ckp_of B) :=
  ckp_med (ckp_of A) (ckp_fmap_cocone u).

Lemma ckp_fmap_Y_left {A B : @Arrow C} (u : A ~> B) :
  ckp_fmap_Y u ∘ ckp_u A ≈ ckp_u B ∘ ar_snd u.
Proof. exact (ckp_med_left (ckp_of A) (ckp_fmap_cocone u)). Qed.

Lemma ckp_fmap_Y_right {A B : @Arrow C} (u : A ~> B) :
  ckp_fmap_Y u ∘ ckp_v A ≈ ckp_v B ∘ ar_snd u.
Proof. exact (ckp_med_right (ckp_of A) (ckp_fmap_cocone u)). Qed.

Lemma ckp_fmap_Y_unique {A B : @Arrow C} (u : A ~> B)
      (w : ckp_obj (ckp_of A) ~> ckp_obj (ckp_of B)) :
  w ∘ ckp_u A ≈ ckp_u B ∘ ar_snd u ->
  w ∘ ckp_v A ≈ ckp_v B ∘ ar_snd u -> ckp_fmap_Y u ≈ w.
Proof. exact (ckp_med_unique (ckp_of A) (ckp_fmap_cocone u) w). Qed.

Definition ckp_comp {A B : @Arrow C} (u : A ~> B) (z : ParObj)
  : fobj[ckp_pair A] z ~> fobj[ckp_pair B] z :=
  match z with
  | ParX => ar_snd u
  | ParY => ckp_fmap_Y u
  end.

(* Naturality IS the mediator's two triangles: at the true-tagged arrow
   it is [ckp_fmap_Y_left], at the false-tagged one
   [ckp_fmap_Y_right].  Both endomorphism cases reduce because [APair]
   returns an identity at equal endpoints whatever the tag. *)

Lemma ckp_natural {A B : @Arrow C} (u : A ~> B) (z w : ParObj)
      (k : z ~{Parallel}~> w) :
  fmap[ckp_pair B] k ∘ ckp_comp u z ≈ ckp_comp u w ∘ fmap[ckp_pair A] k.
Proof.
  destruct z, w; simpl.
  - now rewrite id_left, id_right.
  - destruct k as [[|] k]; simpl.
    + now rewrite ckp_fmap_Y_left.
    + now rewrite ckp_fmap_Y_right.
  - destruct (ParHom_Y_X_absurd _ (projT2 k)).
  - now rewrite id_left, id_right.
Qed.

Definition ckp_transform {A B : @Arrow C} (u : A ~> B)
  : ckp_pair A ⟹ ckp_pair B :=
  @Build_Transform' Parallel C (ckp_pair A) (ckp_pair B)
                    (ckp_comp u) (@ckp_natural A B u).

#[local] Obligation Tactic := idtac.

(* All three obligations are proved, none defaulted: [fmap_respects],
   [fmap_id] and [fmap_comp] each reduce at [ParX] to a component
   equation and at [ParY] to one appeal to [ckp_fmap_Y_unique]. *)

Program Definition CokernelPairFunctor : @Arrow C ⟶ [Parallel, C] := {|
  fobj := ckp_pair ;
  fmap := fun A B u => ckp_transform u
|}.
Next Obligation.
  intros A B u v [Hd Hc] z; destruct z; simpl.
  - exact Hc.
  - apply ckp_fmap_Y_unique.
    + now rewrite ckp_fmap_Y_left, Hc.
    + now rewrite ckp_fmap_Y_right, Hc.
Qed.
Next Obligation.
  intros A z; destruct z; simpl.
  - reflexivity.
  - apply ckp_fmap_Y_unique; now rewrite id_left, id_right.
Qed.
Next Obligation.
  intros A B D u v z; destruct z; simpl.
  - reflexivity.
  - apply ckp_fmap_Y_unique.
    + unfold ar_snd; simpl.
      rewrite <- comp_assoc.
      rewrite ckp_fmap_Y_left.
      rewrite comp_assoc.
      rewrite ckp_fmap_Y_left.
      unfold ar_snd; simpl.
      now rewrite <- comp_assoc.
    + unfold ar_snd; simpl.
      rewrite <- comp_assoc.
      rewrite ckp_fmap_Y_right.
      rewrite comp_assoc.
      rewrite ckp_fmap_Y_right.
      unfold ar_snd; simpl.
      now rewrite <- comp_assoc.
Qed.

End CokernelPairFunctor.

(** ** The equalizer functor into the arrow category *)

Section EqualizerArrowFunctor.

Context {C : Category}.
Context `{HE : @HasEqualizers C}.

(* The chosen equalizer of the parallel pair a functor names, unpacked
   from [HasEqualizers]' sigma. *)

Definition eqa_data (G : Parallel ⟶ C) :=
  equalizer (parallel_leg1 G) (parallel_leg2 G).

Definition eqa_obj (G : Parallel ⟶ C) : C := `1 (eqa_data G).
Definition eqa_arr (G : Parallel ⟶ C) : eqa_obj G ~> G ParX :=
  `1 (`2 (eqa_data G)).
Definition eqa_wit (G : Parallel ⟶ C)
  : IsEqualizer (parallel_leg1 G) (parallel_leg2 G) (eqa_obj G) (eqa_arr G)
  := `2 (`2 (eqa_data G)).

(* The equalizing arrow, read as an object of the arrow category. *)

Definition eqa_ob (G : Parallel ⟶ C) : @Arrow C :=
  ((eqa_obj G, fobj[G] ParX); eqa_arr G).

Example eqa_ob_dom (G : Parallel ⟶ C) : ar_dom (eqa_ob G) = eqa_obj G
  := eq_refl.
Example eqa_ob_cod (G : Parallel ⟶ C) : ar_cod (eqa_ob G) = fobj[G] ParX
  := eq_refl.
Example eqa_ob_mor (G : Parallel ⟶ C) : ar_mor (eqa_ob G) = eqa_arr G
  := eq_refl.

(* The comma square of a morphism into [eqa_ob G], read with [eqa_arr G]
   in place of [ar_mor (eqa_ob G)].  The two are the same term, so this
   is [ar_square] accepted by conversion. *)
Lemma ar_square_eqa {A : @Arrow C} {G : Parallel ⟶ C}
      (w : A ~{@Arrow C}~> eqa_ob G) :
  eqa_arr G ∘ ar_fst w ≈ ar_snd w ∘ ar_mor A.
Proof. exact (ar_square w). Qed.

Lemma eqa_fork {G : Parallel ⟶ C} {z : C} (h : z ~> G ParX)
      (Hh : parallel_leg1 G ∘ h ≈ parallel_leg2 G ∘ h) :
  eqa_arr G ∘ unique_obj (eq_desc (eqa_wit G) h Hh) ≈ h.
Proof. exact (unique_property (eq_desc (eqa_wit G) h Hh)). Qed.

Lemma eqa_uniq {G : Parallel ⟶ C} {z : C} (h : z ~> G ParX)
      (Hh : parallel_leg1 G ∘ h ≈ parallel_leg2 G ∘ h)
      (w : z ~> eqa_obj G) :
  eqa_arr G ∘ w ≈ h -> unique_obj (eq_desc (eqa_wit G) h Hh) ≈ w.
Proof. intro Hw; exact (uniqueness (eq_desc (eqa_wit G) h Hh) w Hw). Qed.

(* The arrow action: the codomain component is the transformation at
   [ParX], the domain component its descent across the target
   equalizer.  The fork condition is naturality on both sides of the
   source's own [fork_eq]. *)

Lemma eqa_fmap_cond {G G' : Parallel ⟶ C} (t : G ⟹ G') :
  parallel_leg1 G' ∘ (transform[t] ParX ∘ eqa_arr G)
    ≈ parallel_leg2 G' ∘ (transform[t] ParX ∘ eqa_arr G).
Proof.
  unfold parallel_leg1, parallel_leg2.
  rewrite !comp_assoc.
  rewrite !(naturality t).
  rewrite <- !comp_assoc.
  now rewrite (fork_eq (eqa_wit G)).
Qed.

Definition eqa_fmap1 {G G' : Parallel ⟶ C} (t : G ⟹ G')
  : eqa_obj G ~> eqa_obj G' :=
  unique_obj (eq_desc (eqa_wit G') (transform[t] ParX ∘ eqa_arr G)
                      (eqa_fmap_cond t)).

Lemma eqa_fmap1_commutes {G G' : Parallel ⟶ C} (t : G ⟹ G') :
  eqa_arr G' ∘ eqa_fmap1 t ≈ transform[t] ParX ∘ eqa_arr G.
Proof. exact (eqa_fork _ (eqa_fmap_cond t)). Qed.

Lemma eqa_fmap1_unique {G G' : Parallel ⟶ C} (t : G ⟹ G')
      (w : eqa_obj G ~> eqa_obj G') :
  eqa_arr G' ∘ w ≈ transform[t] ParX ∘ eqa_arr G -> eqa_fmap1 t ≈ w.
Proof. exact (eqa_uniq _ (eqa_fmap_cond t) w). Qed.

Definition eqa_fmap {G G' : Parallel ⟶ C} (t : G ⟹ G')
  : eqa_ob G ~{@Arrow C}~> eqa_ob G' :=
  ((eqa_fmap1 t, transform[t] ParX); eqa_fmap1_commutes t).

#[local] Obligation Tactic := idtac.

(* Again all three obligations are proved: the codomain component is
   componentwise, and the domain component is one appeal to
   [eqa_fmap1_unique] each time. *)

Program Definition EqualizerArrowFunctor : [Parallel, C] ⟶ @Arrow C := {|
  fobj := eqa_ob ;
  fmap := fun G G' t => eqa_fmap t
|}.
Next Obligation.
  intros G G' s t Hst; split; simpl.
  - apply eqa_fmap1_unique.
    rewrite eqa_fmap1_commutes.
    now rewrite (Hst ParX).
  - exact (Hst ParX).
Qed.
Next Obligation.
  intros G; split; simpl.
  - apply eqa_fmap1_unique.
    unfold nat_id; simpl.
    now rewrite fmap_id, id_left, id_right.
  - unfold nat_id; simpl.
    now rewrite fmap_id.
Qed.
Next Obligation.
  intros G G' G'' t s; split; simpl.
  - apply eqa_fmap1_unique.
    rewrite comp_assoc, eqa_fmap1_commutes.
    rewrite <- comp_assoc, eqa_fmap1_commutes.
    now rewrite comp_assoc.
  - reflexivity.
Qed.

(* The type-shape tie to Adjunction/Diagonal/Finite.v:709's
   [EqualizerFunctor : [Parallel, C] ⟶ C].  This has the same type; the
   two are NOT compared, for the reason measured in the header. *)

Definition eqa_dom_functor : [Parallel, C] ⟶ C :=
  Arrow_dom ◯ EqualizerArrowFunctor.

Example eqa_dom_functor_obj (G : Parallel ⟶ C) :
  fobj[eqa_dom_functor] G = eqa_obj G := eq_refl.

End EqualizerArrowFunctor.

(** ** The adjunction *)

Section CokernelPairAdjunction.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context `{HE : @HasEqualizers C}.

(* The parallel pair a cokernel pair names IS its two legs, on the
   nose: these are what make the fork and cocone conditions below
   statable in the [ckp_u]/[ckp_v] vocabulary. *)

Example ckp_pair_one (A : @Arrow C) :
  fmap[ckp_pair A] (true; ParOne) = ckp_u A := eq_refl.
Example ckp_pair_two (A : @Arrow C) :
  fmap[ckp_pair A] (false; ParTwo) = ckp_v A := eq_refl.

(* Both sides of the transposition say the same thing about an arrow
   [h : ar_cod A ~> G ParX], namely that [h ∘ ar_mor A] forks the pair
   of G.  Going right, that is naturality plus [ckp_commutes]; going
   left, it is the comma square plus [fork_eq]. *)

Lemma ckpadj_fork {A : @Arrow C} {G : Parallel ⟶ C} (t : ckp_pair A ⟹ G) :
  parallel_leg1 G ∘ (transform[t] ParX ∘ ar_mor A)
    ≈ parallel_leg2 G ∘ (transform[t] ParX ∘ ar_mor A).
Proof.
  unfold parallel_leg1, parallel_leg2.
  rewrite !comp_assoc.
  rewrite !(naturality t).
  rewrite ckp_pair_one, ckp_pair_two.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | apply ckp_uv_commutes ].
Qed.

Lemma ckpadj_cocone {A : @Arrow C} {G : Parallel ⟶ C}
      (w : A ~{@Arrow C}~> eqa_ob G) :
  (parallel_leg1 G ∘ ar_snd w) ∘ ar_mor A
    ≈ (parallel_leg2 G ∘ ar_snd w) ∘ ar_mor A.
Proof.
  rewrite <- !comp_assoc.
  rewrite <- !(ar_square_eqa w).
  rewrite (comp_assoc (parallel_leg1 G) (eqa_arr G) (ar_fst w)).
  rewrite (comp_assoc (parallel_leg2 G) (eqa_arr G) (ar_fst w)).
  now rewrite (fork_eq (eqa_wit G)).
Qed.

(* Right: the equalizer descent of the [ParX] component along the
   arrow of A, paired with that component. *)

Definition ckpadj_to {A : @Arrow C} {G : Parallel ⟶ C}
           (t : ckp_pair A ⟹ G) : A ~{@Arrow C}~> eqa_ob G :=
  ((unique_obj (eq_desc (eqa_wit G) (transform[t] ParX ∘ ar_mor A)
                        (ckpadj_fork t)),
    transform[t] ParX);
   eqa_fork _ (ckpadj_fork t)).

(* Left: the codomain component, together with the cokernel-pair
   mediator of the two legs of G precomposed with it. *)

Definition ckpadj_from_Y {A : @Arrow C} {G : Parallel ⟶ C}
           (w : A ~{@Arrow C}~> eqa_ob G)
  : ckp_obj (ckp_of A) ~> fobj[G] ParY :=
  ckp_med (ckp_of A) (ckpadj_cocone w).

Definition ckpadj_from_comp {A : @Arrow C} {G : Parallel ⟶ C}
           (w : A ~{@Arrow C}~> eqa_ob G) (z : ParObj)
  : fobj[ckp_pair A] z ~> fobj[G] z :=
  match z with
  | ParX => ar_snd w
  | ParY => ckpadj_from_Y w
  end.

Lemma ckpadj_from_natural {A : @Arrow C} {G : Parallel ⟶ C}
      (w : A ~{@Arrow C}~> eqa_ob G) (z z' : ParObj)
      (k : z ~{Parallel}~> z') :
  fmap[G] k ∘ ckpadj_from_comp w z
    ≈ ckpadj_from_comp w z' ∘ fmap[ckp_pair A] k.
Proof.
  destruct z, z'; simpl.
  - rewrite (par_fmap_idX G k).
    now rewrite id_left, id_right.
  - destruct k as [[|] k]; simpl;
      [ pose proof (ParHom_inv true ParX ParY k) as Hk
      | pose proof (ParHom_inv false ParX ParY k) as Hk ];
      simpl in Hk; subst k.
    + symmetry; exact (ckp_med_left (ckp_of A) (ckpadj_cocone w)).
    + symmetry; exact (ckp_med_right (ckp_of A) (ckpadj_cocone w)).
  - destruct (ParHom_Y_X_absurd _ (projT2 k)).
  - rewrite (par_fmap_idY G k).
    now rewrite id_left, id_right.
Qed.

Definition ckpadj_from {A : @Arrow C} {G : Parallel ⟶ C}
           (w : A ~{@Arrow C}~> eqa_ob G) : ckp_pair A ⟹ G :=
  @Build_Transform' Parallel C (ckp_pair A) G
                    (ckpadj_from_comp w) (@ckpadj_from_natural A G w).

(* Both round trips are one appeal to a uniqueness clause each: the
   comma square for the equalizer side, naturality for the
   cokernel-pair side. *)

Lemma ckpadj_to_from {A : @Arrow C} {G : Parallel ⟶ C}
      (w : A ~{@Arrow C}~> eqa_ob G) : ckpadj_to (ckpadj_from w) ≈ w.
Proof.
  split; simpl.
  - apply eqa_uniq.
    exact (ar_square_eqa w).
  - reflexivity.
Qed.

Lemma ckpadj_from_to {A : @Arrow C} {G : Parallel ⟶ C}
      (t : ckp_pair A ⟹ G) : ckpadj_from (ckpadj_to t) ≈ t.
Proof.
  intro z; destruct z; simpl.
  - reflexivity.
  - apply (ckp_med_unique (ckp_of A) (ckpadj_cocone (ckpadj_to t))).
    + symmetry; exact (naturality t ParX ParY (true; ParOne)).
    + symmetry; exact (naturality t ParX ParY (false; ParTwo)).
Qed.

#[local] Obligation Tactic := idtac.

Program Definition ckpadj_iso (A : @Arrow C) (G : Parallel ⟶ C) :
  @Isomorphism Sets
    {| carrier   := @hom ([Parallel, C]) (ckp_pair A) G
     ; is_setoid := @homset ([Parallel, C]) (ckp_pair A) G |}
    {| carrier   := @hom (@Arrow C) A (eqa_ob G)
     ; is_setoid := @homset (@Arrow C) A (eqa_ob G) |} := {|
  to   := {| morphism := ckpadj_to |};
  from := {| morphism := ckpadj_from |}
|}.
Next Obligation.
  intros A G t t' Ht; split; simpl.
  - apply eqa_uniq.
    rewrite eqa_fork.
    now rewrite (Ht ParX).
  - exact (Ht ParX).
Qed.
Next Obligation.
  intros A G w w' Hw z; destruct z; simpl.
  - exact (snd Hw).
  - apply (ckp_med_unique (ckp_of A) (ckpadj_cocone w)).
    + rewrite (ckp_med_left (ckp_of A) (ckpadj_cocone w')).
      now rewrite (snd Hw).
    + rewrite (ckp_med_right (ckp_of A) (ckpadj_cocone w')).
      now rewrite (snd Hw).
Qed.
Next Obligation. intros A G w; apply ckpadj_to_from. Qed.
Next Obligation. intros A G t; apply ckpadj_from_to. Qed.

(* Mac Lane §IV.2 Exercise 10.  [Build_Adjunction'] takes the
   hom-setoid isomorphism plus the two forward naturality clauses and
   derives the two inverse-transpose ones. *)

Program Definition CokernelPair_Equalizer_Adjunction
  : CokernelPairFunctor ⊣ EqualizerArrowFunctor :=
  @Build_Adjunction' ([Parallel, C]) (@Arrow C)
                     CokernelPairFunctor EqualizerArrowFunctor
                     ckpadj_iso _ _.
Next Obligation.
  intros x y z f g; split; simpl.
  - apply eqa_uniq.
    rewrite (comp_assoc (eqa_arr z) _ (ar_fst g)).
    rewrite eqa_fork.
    rewrite (comp_assoc_sym (transform[f] ParX) (ar_mor y) (ar_fst g)).
    rewrite (ar_square g).
    now rewrite (comp_assoc (transform[f] ParX) (ar_snd g) (ar_mor x)).
  - reflexivity.
Qed.
Next Obligation.
  intros x y z f g; split; simpl.
  - apply eqa_uniq.
    rewrite (comp_assoc (eqa_arr z) (eqa_fmap1 f) _).
    rewrite eqa_fmap1_commutes.
    rewrite (comp_assoc_sym (transform[f] ParX) (eqa_arr y) _).
    rewrite eqa_fork.
    now rewrite (comp_assoc (transform[f] ParX) (transform[g] ParX)
                            (ar_mor x)).
  - reflexivity.
Qed.

(** ** The unit and the counit, by name *)

(* Mac Lane's comparison of f into the equalizer of its cokernel pair:
   the descent of [ar_mor A] across that equalizer, paired with the
   identity. *)

Definition ckp_unit_med (A : @Arrow C)
  : ar_dom A ~> eqa_obj (ckp_pair A) :=
  unique_obj (eq_desc (eqa_wit (ckp_pair A)) (ar_mor A)
                      (ckp_uv_commutes A)).

Lemma ckp_unit_med_commutes (A : @Arrow C) :
  eqa_arr (ckp_pair A) ∘ ckp_unit_med A ≈ ar_mor A.
Proof.
  exact (eqa_fork (G:=ckp_pair A) (ar_mor A) (ckp_uv_commutes A)).
Qed.

Lemma ckp_unit_med_unique (A : @Arrow C)
      (w : ar_dom A ~> eqa_obj (ckp_pair A)) :
  eqa_arr (ckp_pair A) ∘ w ≈ ar_mor A -> ckp_unit_med A ≈ w.
Proof.
  exact (eqa_uniq (G:=ckp_pair A) (ar_mor A) (ckp_uv_commutes A) w).
Qed.

Program Definition cokernel_pair_unit (A : @Arrow C)
  : A ~{@Arrow C}~> eqa_ob (ckp_pair A) :=
  ((ckp_unit_med A, id[ar_cod A]); _).
Next Obligation.
  intros A.
  simpl.
  rewrite id_left.
  exact (ckp_unit_med_commutes A).
Qed.

(* The coequalizing comparison: the identity, together with the
   cokernel-pair mediator of the two legs of G, whose cocone condition
   is [fork_eq] for the chosen equalizer of G. *)

Definition ckpc_comp (G : Parallel ⟶ C) (z : ParObj)
  : fobj[ckp_pair (eqa_ob G)] z ~> fobj[G] z :=
  match z with
  | ParX => id[fobj[G] ParX]
  | ParY => ckp_med (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))
  end.

Lemma ckpc_natural (G : Parallel ⟶ C) (z z' : ParObj)
      (k : z ~{Parallel}~> z') :
  fmap[G] k ∘ ckpc_comp G z ≈ ckpc_comp G z' ∘ fmap[ckp_pair (eqa_ob G)] k.
Proof.
  destruct z, z'; simpl.
  - rewrite (par_fmap_idX G k).
    now rewrite id_left, id_right.
  - destruct k as [[|] k]; simpl;
      [ pose proof (ParHom_inv true ParX ParY k) as Hk
      | pose proof (ParHom_inv false ParX ParY k) as Hk ];
      simpl in Hk; subst k; rewrite id_right.
    + symmetry.
      exact (ckp_med_left (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))).
    + symmetry.
      exact (ckp_med_right (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))).
  - destruct (ParHom_Y_X_absurd _ (projT2 k)).
  - rewrite (par_fmap_idY G k).
    now rewrite id_left, id_right.
Qed.

Definition cokernel_pair_counit (G : Parallel ⟶ C)
  : ckp_pair (eqa_ob G) ⟹ G :=
  @Build_Transform' Parallel C (ckp_pair (eqa_ob G)) G
                    (ckpc_comp G) (ckpc_natural G).

(** ** The named unit and counit against the class-produced ones *)

Definition ckp_class_unit (A : @Arrow C) :=
  @unit ([Parallel, C]) (@Arrow C) CokernelPairFunctor
        EqualizerArrowFunctor CokernelPair_Equalizer_Adjunction A.

Definition ckp_class_counit (G : Parallel ⟶ C) :=
  @counit ([Parallel, C]) (@Arrow C) CokernelPairFunctor
          EqualizerArrowFunctor CokernelPair_Equalizer_Adjunction G.

(* Strict where it holds.  [nat_id]'s component is [fmap[F] id], which
   at [ckp_pair A] and [ParX] reduces to [id], so the codomain
   component of the unit and the [ParX] component of the counit are
   Leibniz-equal to the named ones. *)

Example ckp_unit_snd_strict (A : @Arrow C) :
  snd `1 (ckp_class_unit A) = snd `1 (cokernel_pair_unit A) := eq_refl.

Example ckp_counit_X_strict (G : Parallel ⟶ C) :
  transform[ckp_class_counit G] ParX
    = transform[cokernel_pair_counit G] ParX := eq_refl.

(* And REJECTED where it does not, each beside the passing [≈] control
   proved just below.  The residues: the class unit's domain component
   descends [id ∘ ar_mor A] where the named one descends [ar_mor A],
   and the class counit's [ParY] component mediates
   [parallel_leg1 G ∘ id, parallel_leg2 G ∘ id] where the named one
   mediates [parallel_leg1 G, parallel_leg2 G]. *)

Fail Example ckp_unit_fst_strict (A : @Arrow C) :
  fst `1 (ckp_class_unit A) = fst `1 (cokernel_pair_unit A) := eq_refl.

Fail Example ckp_counit_Y_strict (G : Parallel ⟶ C) :
  transform[ckp_class_counit G] ParY
    = transform[cokernel_pair_counit G] ParY := eq_refl.

Theorem ckp_class_unit_agrees (A : @Arrow C) :
  ckp_class_unit A ≈ cokernel_pair_unit A.
Proof.
  split; simpl.
  - apply eqa_uniq.
    simpl.
    rewrite id_left.
    exact (ckp_unit_med_commutes A).
  - reflexivity.
Qed.

Theorem ckp_class_counit_agrees (G : Parallel ⟶ C) :
  ckp_class_counit G ≈ cokernel_pair_counit G.
Proof.
  intro z; destruct z; simpl.
  - reflexivity.
  - apply (ckp_med_unique (ckp_of (eqa_ob G))
                          (ckpadj_cocone (@id (@Arrow C) (eqa_ob G)))).
    + rewrite (ckp_med_left (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))).
      now rewrite id_right.
    + rewrite (ckp_med_right (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))).
      now rewrite id_right.
Qed.

End CokernelPairAdjunction.

(** ** When the unit is an isomorphism *)

(* The content of the exercise: the unit at A is invertible exactly
   when the arrow of A is already an equalizer of its own cokernel
   pair -- a regular monomorphism.  The tree has [RegularEpi]
   (Structure/Regular.v:54) and no dual, and none is declared here: the
   conclusion is the bare [IsEqualizer]-valued abbreviation below. *)

Section Regularity.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context `{HE : @HasEqualizers C}.

(* An equalizer transported along an isomorphism of its apex is again
   one.  Stated for an arbitrary parallel pair; nothing about cokernel
   pairs enters. *)

Lemma IsEqualizer_along_iso {x y q d : C} {u v : x ~> y} {e : q ~> x}
      (E : IsEqualizer u v q e) (k : d ~> q) (K : IsIsomorphism k)
      {m : d ~> x} (Hm : e ∘ k ≈ m) : IsEqualizer u v d m.
Proof.
  construct.
  - rewrite <- Hm.
    rewrite !comp_assoc.
    now rewrite (fork_eq E).
  - exists (two_sided_inverse ∘ unique_obj (eq_desc E h Hh)).
    + rewrite comp_assoc.
      rewrite <- Hm.
      rewrite (comp_assoc_sym e k two_sided_inverse).
      rewrite is_right_inverse, id_right.
      exact (unique_property (eq_desc E h Hh)).
    + intros w Hw.
      rewrite <- (id_left w).
      rewrite <- is_left_inverse.
      rewrite (comp_assoc_sym two_sided_inverse k w).
      apply compose_respects; [ reflexivity | ].
      apply (uniqueness (eq_desc E h Hh)).
      rewrite (comp_assoc e k w), Hm.
      exact Hw.
Qed.

Definition RegularCokernelPair (A : @Arrow C) : Type :=
  IsEqualizer (ckp_u A) (ckp_v A) (ar_dom A) (ar_mor A).

Theorem unit_med_iso_regular (A : @Arrow C)
        (K : IsIsomorphism (ckp_unit_med A)) : RegularCokernelPair A.
Proof.
  exact (IsEqualizer_along_iso (eqa_wit (ckp_pair A)) (ckp_unit_med A) K
                               (ckp_unit_med_commutes A)).
Qed.

Corollary unit_med_iso_Monic (A : @Arrow C)
          (K : IsIsomorphism (ckp_unit_med A)) : Monic (ar_mor A).
Proof. exact (equalizer_monic _ _ (unit_med_iso_regular A K)). Qed.

Theorem regular_unit_med_iso (A : @Arrow C) (E : RegularCokernelPair A)
  : IsIsomorphism (ckp_unit_med A).
Proof.
  unshelve econstructor.
  - exact (unique_obj (eq_desc E (eqa_arr (ckp_pair A))
                               (fork_eq (eqa_wit (ckp_pair A))))).
  - apply (equalizer_monic _ _ (eqa_wit (ckp_pair A))).
    rewrite (comp_assoc (eqa_arr (ckp_pair A))).
    rewrite ckp_unit_med_commutes.
    rewrite (unique_property (eq_desc E (eqa_arr (ckp_pair A))
                                     (fork_eq (eqa_wit (ckp_pair A))))).
    now rewrite id_right.
  - apply (equalizer_monic _ _ E).
    rewrite (comp_assoc (ar_mor A)).
    rewrite (unique_property (eq_desc E (eqa_arr (ckp_pair A))
                                     (fork_eq (eqa_wit (ckp_pair A))))).
    rewrite ckp_unit_med_commutes.
    now rewrite id_right.
Qed.

(* Passing between the domain component and the whole comma morphism.
   The codomain component of the unit is the identity, so nothing is
   needed in that slot; the square for the inverse comes from
   [ckp_unit_med_commutes]. *)

Lemma arrow_iso_fst {A B : @Arrow C} {w : A ~{@Arrow C}~> B}
      (K : IsIsomorphism w) : IsIsomorphism (ar_fst w).
Proof.
  unshelve econstructor.
  - exact (ar_fst (@two_sided_inverse (@Arrow C) A B w K)).
  - exact (fst (@is_right_inverse (@Arrow C) A B w K)).
  - exact (fst (@is_left_inverse (@Arrow C) A B w K)).
Qed.

#[local] Obligation Tactic := idtac.

Program Definition unit_iso_of_med_iso (A : @Arrow C)
        (K : IsIsomorphism (ckp_unit_med A))
  : IsIsomorphism (cokernel_pair_unit A) :=
  {| two_sided_inverse :=
       ((@two_sided_inverse C _ _ (ckp_unit_med A) K, id[ar_cod A]); _) |}.
Next Obligation.
  intros A K; simpl.
  rewrite id_left.
  rewrite <- (ckp_unit_med_commutes A).
  rewrite (comp_assoc_sym (eqa_arr (ckp_pair A)) (ckp_unit_med A) _).
  now rewrite is_right_inverse, id_right.
Qed.
Next Obligation.
  intros A K; split; simpl.
  - exact is_right_inverse.
  - now rewrite id_left.
Qed.
Next Obligation.
  intros A K; split; simpl.
  - exact is_left_inverse.
  - now rewrite id_left.
Qed.

Theorem unit_iso_iff_regular (A : @Arrow C) :
  IsIsomorphism (cokernel_pair_unit A) ↔ RegularCokernelPair A.
Proof.
  split.
  - intro K; exact (unit_med_iso_regular A (arrow_iso_fst K)).
  - intro E; exact (unit_iso_of_med_iso A (regular_unit_med_iso A E)).
Qed.

(* Split monomorphisms are regular.  The retraction r gives a competing
   pair (id, f ∘ r) on the codomain, whose mediator m out of the
   cokernel pair turns the equalizing hypothesis on h into
   h ≈ f ∘ (r ∘ h); uniqueness is then left-cancellation by f, which a
   retraction supplies. *)

Lemma split_retract_cocone {A : @Arrow C} {r : ar_cod A ~> ar_dom A}
      (Hr : r ∘ ar_mor A ≈ id) :
  id[ar_cod A] ∘ ar_mor A ≈ (ar_mor A ∘ r) ∘ ar_mor A.
Proof.
  rewrite id_left.
  rewrite (comp_assoc_sym (ar_mor A) r (ar_mor A)).
  now rewrite Hr, id_right.
Qed.

Definition split_retract_med {A : @Arrow C} {r : ar_cod A ~> ar_dom A}
           (Hr : r ∘ ar_mor A ≈ id) : ckp_obj (ckp_of A) ~> ar_cod A :=
  ckp_med (ckp_of A) (split_retract_cocone Hr).

Theorem split_mono_regular {A : @Arrow C} {r : ar_cod A ~> ar_dom A}
        (Hr : r ∘ ar_mor A ≈ id) : RegularCokernelPair A.
Proof.
  construct.
  - exact (ckp_uv_commutes A).
  - exists (r ∘ h).
    + rewrite (comp_assoc (ar_mor A) r h).
      rewrite <- (ckp_med_right (ckp_of A) (split_retract_cocone Hr)).
      rewrite (comp_assoc_sym (split_retract_med Hr) (ckp_v A) h).
      rewrite <- Hh.
      rewrite (comp_assoc (split_retract_med Hr) (ckp_u A) h).
      rewrite (ckp_med_left (ckp_of A) (split_retract_cocone Hr)).
      now rewrite id_left.
    + intros w Hw.
      rewrite <- Hw.
      rewrite (comp_assoc r (ar_mor A) w).
      now rewrite Hr, id_left.
Qed.

Corollary split_mono_unit_iso {A : @Arrow C} {r : ar_cod A ~> ar_dom A}
          (Hr : r ∘ ar_mor A ≈ id)
  : IsIsomorphism (cokernel_pair_unit A).
Proof.
  exact (unit_iso_of_med_iso A (regular_unit_med_iso A
                                 (split_mono_regular Hr))).
Qed.

End Regularity.

(** ** Non-vacuity at Sets *)

Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Pushout.

Section SetsWitness.

(* The cheapest of the three in-tree routes to [HasEqualizers Sets];
   see the header for the closure measurement.  The definition is plain;
   it is the [Existing Instance] below that is [#[local]], so resolution
   in this section finds it without exporting a second inhabitant. *)

Definition SetsEqualizers : @HasEqualizers Sets :=
  @HasEqualizers_of_HasPullbacks_Terminal Sets Sets_Terminal
                                          Sets_HasPullbacks.

#[local] Existing Instance SetsEqualizers.

(* Instance/Sets.v:563 and :367's two-element and one-element setoids,
   with
   the collapse onto the point and the inclusion of the point.  Neither
   object nor arrow is rebuilt here. *)

Definition ArrCollapse : @Arrow Sets :=
  ((bool_setoid_object, unit_setoid_object); collapse).

Definition ArrPick : @Arrow Sets :=
  ((unit_setoid_object, bool_setoid_object); pick_true).

Example sets_arr_collapse_mor : ar_mor ArrCollapse = collapse := eq_refl.
Example sets_arr_pick_mor : ar_mor ArrPick = pick_true := eq_refl.

(* NEGATIVE.  The collapse is not monic (Instance/Sets.v:591 probes it
   with the two maps out of the one-element setoid), and the unit can
   only be invertible at a monomorphism.  Nothing about the chosen
   pushout or the chosen equalizer of Sets is computed: the argument
   runs entirely through the universal properties and then out through
   an existing refutation. *)

Theorem sets_collapse_unit_not_iso :
  IsIsomorphism (cokernel_pair_unit ArrCollapse) -> False.
Proof.
  intro K.
  apply collapse_not_monic.
  exact (unit_med_iso_Monic ArrCollapse (arrow_iso_fst K)).
Qed.

(* POSITIVE.  The inclusion of the point is split by the collapse
   (Instance/Sets.v:577's [collapse_pick]), hence regular, hence its
   unit is invertible. *)

Theorem sets_pick_regular : RegularCokernelPair ArrPick.
Proof. exact (split_mono_regular (A:=ArrPick) (r:=collapse) collapse_pick). Qed.

Theorem sets_pick_unit_iso :
  IsIsomorphism (cokernel_pair_unit ArrPick).
Proof. exact (snd (unit_iso_iff_regular ArrPick) sets_pick_regular). Qed.

(* And the positive case is not degenerate: the arrow itself is not an
   isomorphism, since it misses [false] and so is not epic
   (Instance/Sets.v:603). *)

Theorem sets_pick_not_iso : IsIsomorphism pick_true -> False.
Proof.
  intro K.
  apply pick_true_not_epic.
  exact (iso_to_epic (IsIsoToIso pick_true K)).
Qed.

End SetsWitness.

(** ** Universe probe *)

(* The four donors of the hom-and-proof identification carried by
   [CokernelPair_Equalizer_Adjunction], each rejected ALONE at levels
   declared strictly apart, against controls accepted at those very
   levels.  Section-local [Universes]/[Constraint] declarations do not
   leak past [End]; Instance/Fun/Group.v is the in-tree precedent for
   carrying such a probe inside a library file. *)

Section UniverseProbe.

Universes co ch cp.
Constraint ch < cp.
Context {Cu : Category@{co ch cp}}.
Context (cx cy : Cu).

(* Controls: the hom type and an identity DO elaborate at these
   levels, so the rejections below are about the four donors. *)
Check (cx ~{Cu}~> cy).
Check (@id Cu cx).

(* Each of the four fails with
   "universe inconsistency: Cannot enforce cp = ch because ch < cp". *)
Fail Check (@Arrow Cu).
Fail Check ([Parallel, Cu]).
Fail Check (@HasPushouts Cu).
Fail Check (@HasEqualizers Cu).

End UniverseProbe.

(* Instrument check: a command that fails for a reason having nothing
   to do with universes, so that a [Fail] which has become vacuous is
   distinguishable from one that still fires. *)
Fail Check ckp_no_such_constant.
