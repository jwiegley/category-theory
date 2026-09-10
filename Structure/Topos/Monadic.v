Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* See the note in Structure/Topos/Power.v: [Category.Functor.Opposite]
   opens [functor_scope], so [category_scope] is reopened here. *)
Open Scope category_scope.

(* Monadicity of the power-object functor: Paré's theorem.

   nLab:      https://ncatlab.org/nlab/show/Pare%27s+theorem
   nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem
   Paper:     Paré, "Colimits in topoi", Bulletin of the American
              Mathematical Society 80 (1974), pp. 556-561

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.10,
   book p. 107 (`maclane:IV.10:remark2`):

     "The axioms for a topos have many useful consequences. For exam-
      ples, every topos has all finite colimits."

   and the Appendix, book p. 290 (`maclane:App.1:remark2`), on the same
   axioms:

     "These axioms for a topos then hold for the category of sets. They
      have a number of strong consequences. For example, they give all
      finite cate- gorical products and pullbacks, as well as all finite
      coproducts, including an initial object 0, the empty set."

   Neither passage carries a proof, and neither does Awodey §8.8 nor
   Seven Sketches §7.2.1 (both quoted in Structure/Topos/Colimits.v).
   The proof is Paré's, via monadicity of P; Mac Lane-Moerdijk, the usual
   reference, was not available, so the argument here was reconstructed
   and CHECKED BY COMPILATION.

   THIS FILE PROVES `power_object_monadic : Monadic PowF` by CONSUMING the
   in-tree crude monadicity theorem, Monad/Monadicity/Crude.v's
   [crude_monadicity], rather than reproving any monadicity theorem.  Its
   three hypotheses are discharged here as:

     (a) [op_HasReflexiveCoequalizers] -- reflexive coequalizers in C^op,
         which is three applications of pre-existing reductions;
     (b) [pow_PreservesReflexiveCoequalizers] -- the substantial half;
     (c) [PowF_ReflectsIsos] -- through balancedness.

   Beck's precise theorem ([Monad/Monadicity/Beck.v], whose hypothesis is
   [CreatesUSplitCoequalizers]) should ALSO apply, since the image pair is not
   merely P-split but SPLIT -- an ARGUMENT and not a compiled check, that route
   not having been built; it is not taken because creation would need the
   comparison isomorphism and the reflection clause on top of exactly the same
   split data, so the crude form is strictly cheaper here.

   WHAT WAS ABSENT BEFORE THIS FILE.  Every search below was re-run over the
   whole tree with these five new files EXCLUDED, and the counts are what that
   measurement returned, not what a plan predicted.  "A topos is balanced": 119
   case-insensitive hits for "balanced" across 18 files and none about a topos
   -- they are the balanced monoidal categories and twists of
   Structure/Monoidal/*, the balanced tensors and balanced laws of
   Instance/Mod/*, and the balancedness of [Sets], [Set_*], [Met] and [C, D]
   (asserted, denied or deferred there), with Instance/Two.v REFUTING it for 2,
   plus [Par_BalancedMonoidal] in Instance/Coq/Par.v, the module-tensor probe
   Test/ProbeModTensor.v and one header mention in Adjunction/Unitalization.v --
   and NOT ONE of those 18 files so much as mentions [ElementaryTopos], which is
   the sharper check.  "Every mono in a topos is regular": the name
   [RegularMono] occurs on exactly ONE line outside these files, in
   Adjunction/CokernelPair.v, which says in terms that the tree has no such
   class; the only other .v mentions of a regular monomorphism are two more
   prose lines of that file and one comment in Theory/Morphisms.v.  The
   singleton map: the 4 hits for [singleton_map] are two declarations and their
   two uses in Instance/Sets/Powerset.v, about setoid power sets and not about
   toposes.  [PowFunctor], [PowF], [Pow_Functor], [pow_reflects_isos],
   [pow_monadic] and [power_object]: zero files each.  So balancedness, the
   singleton map and P's faithfulness are new here by those searches; the direct
   image and Beck-Chevalley are new AT THE LEVEL OF SUBOBJECTS in an arbitrary
   category, since the tree's existing [DirectImage] (Instance/Powerset.v) and
   [beck_chevalley_exists]/[beck_chevalley_forall]
   (Instance/Powerset/Quantifier.v) are about power sets of a setoid and neither
   is stated for [SubObj].

   THE HARD STEP IS §E, AND ITS SHAPE IS BETTER THAN FEARED.  Unfolded at
   U := P, the crude hypothesis asks: given f, g : b ⇉ a in E with a
   common RETRACTION r, and ANY equalizer e : k ~> b of the pair, show
   P e : P b ~> P k is a coequalizer of P f, P g.  The triple
   (P f, P g, P e) is a genuine SPLIT coequalizer, and
   Structure/Coequalizer/Split.v's [SplitCoequalizer] record wants exactly
   the four equations the argument produces:

     law1  P e ∘ P f ≈ P e ∘ P g   -- contravariant functoriality
                                      plus the equalizer's [fork_eq];
     law2  P e ∘ ∃_e ≈ id          -- [pow_ex_mono] at m := e;
     law3  P f ∘ ∃_f ≈ id          -- [pow_ex_mono] at m := f;
     law4  P g ∘ ∃_f ≈ ∃_e ∘ P e   -- [pow_bc], Beck-Chevalley.

   THE DIRECT IMAGE NEEDS NO IMAGE FACTORIZATION, and that is why the
   step is tractable at all: ∃ is taken only along a MONO, so
   [second m ∘ (membership mono)] is already a mono and its characteristic
   map exists outright.  Epi-mono factorization in a topos is a separate
   obligation and is NOT built here.

   §D's [IsPullback_sym], [second_pullback], [first_second_pullback] and
   [bc_mono] use no classifier -- the first mentions nothing beyond
   [IsPullback], the next two only the cartesian structure, and [bc_mono] only
   chosen pullbacks and [SubObj] -- yet all four carry an [ElementaryTopos C]
   argument in their types, because this section's
   [Set Default Proof Using "All"] discharges the whole context into every
   [Qed]-closed lemma; a move to Theory/Morphisms/Stability.v beside
   [pullback_paste] (or, for [bc_mono], to Theory/Subobject/Functor.v beside
   [sub_reindex]) would first shed that argument.  They are kept here to avoid a
   wide rebuild, and this sentence is the record of the debt.

   Of this file's two [Defined] tokens, [pow_split_coequalizer] is LOAD-BEARING
   -- flipped alone to [Qed], [pow_PreservesReflexiveCoequalizers] no longer
   typechecks -- and [PowF_Faithful] is not: flipped alone, this file,
   Structure/Topos/Colimits.v and the probe all compile unchanged. *)

Section ToposMonadic.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

#[local] Set Default Proof Using "All".

(** ** (A) Finite completeness, and reflexive coequalizers in C^op *)

(* Mac Lane's finite-limit half, at the level of the four elementary
   generators.  Equalizers are DERIVED from the terminal object and pullbacks by
   Structure/Pullback/Reduction.v's Awodey square, which builds the products it
   needs from those two ([Cartesian_of_HasPullbacks_Terminal]) rather than
   consuming the class's own [topos_cartesian]; the class carries the other
   three as fields. *)
Definition topos_HasEqualizers : @HasEqualizers C :=
  HasEqualizers_of_HasPullbacks_Terminal topos_pullbacks.

(* The appended Seven Sketches checkbox, at generator level: terminal
   object, binary products, pullbacks, equalizers.  NO finite-shape
   induction is performed here, so this is NOT a [Limit]-shaped "all finite
   limits"; that statement is Structure/Limit/Finite.v's [FinitelyComplete].

   That checkbox asks this to close a reduction Structure/Topos.v's header
   "records as not formalized"; the premise is stale -- since #326 that header
   says the reduction and its converse ARE formalized.  What it records as not
   done is the finite-shape induction, and that is still not done:
   [topos_finitely_complete] is at generator level. *)
Definition topos_finitely_complete :
  @Terminal C * @Cartesian C * @HasPullbacks C * @HasEqualizers C :=
  (topos_terminal, topos_cartesian, topos_pullbacks, topos_HasEqualizers).

(* A reflexive pair in C^op is a CO-reflexive pair in C, and a coequalizer
   in C^op is an equalizer in C.  Both readings are definitional, so the
   whole of Crude.v's first hypothesis is three pre-existing reductions.
   [(C^op)^op = C] by reflexivity is what makes the middle line typecheck. *)
Definition op_HasCoequalizers : @HasCoequalizers (C^op) :=
  @HasCoequalizers_of_HasEqualizers_op (C^op) topos_HasEqualizers.

Definition op_HasReflexiveCoequalizers : HasReflexiveCoequalizers (C^op) :=
  @HasCoequalizers_HasReflexiveCoequalizers (C^op) op_HasCoequalizers.

(* The monad of the self-adjunction, P ◯ P^op.  Declared here rather than
   in Structure/Topos/Power.v because [Adjunction_Induced_Monad] costs
   that file +6 modules of closure, while this file requires Crude.v --
   and hence Comparison.v -- anyway. *)
Definition pow_monad : @Monad C (PowF ◯ Opposite_Functor PowF) :=
  @Adjunction_Induced_Monad (C^op) C (Opposite_Functor PowF) PowF
    pow_adjunction.

(** ** (B) Balancedness, the singleton map, and reflection of isos *)

(* A topos is balanced.  The classifying square of a MONIC epi forces its
   characteristic map down to [truth ∘ one], after which the identity
   lies over truth and factors through f. *)
Theorem topos_balanced {x y : C} (f : x ~> y) (Mf : Monic f) (Ef : Epic f) :
  IsIsomorphism f.
Proof.
  pose proof (char_pullback f Mf) as PB.
  assert (Hc : char f Mf ≈ truth ∘ one).
  { apply (epic (Epic := Ef)).
    rewrite (is_pullback_commutes PB).
    rewrite <- comp_assoc.
    now rewrite (one_unique (one ∘ f) one). }
  destruct (is_pullback_ump PB y id one) as [u [Hu1 Hu2] Huniq].
  { rewrite id_right, Hc; reflexivity. }
  unshelve refine {| two_sided_inverse := u |}.
  - exact Hu1.
  - apply (monic (Monic := Mf)).
    rewrite comp_assoc, Hu1, id_left, id_right.
    reflexivity.
Qed.

Definition topos_diag (x : C) : x ~> x × x := id △ id.

Lemma diag_Monic (x : C) : Monic (topos_diag x).
Proof.
  apply sections_are_monic.
  unshelve refine {| section := exl |}.
  unfold topos_diag; cat.
Qed.

(* The singleton map: the transpose of the characteristic map of the
   diagonal, i.e. x ↦ {x}. *)
Definition sing (x : C) : x ~> Pow x :=
  curry (char (topos_diag x) (diag_Monic x)).

Lemma sing_Monic (x : C) : Monic (sing x).
Proof.
  constructor; intros z u v Huv.
  pose proof (char_pullback (topos_diag x) (diag_Monic x)) as PB.
  assert (Hun : char (topos_diag x) (diag_Monic x) ∘ first u
                ≈ char (topos_diag x) (diag_Monic x) ∘ first v).
  { unfold sing in Huv.
    apply curry_inj.
    rewrite <- !curry_comp_l.
    exact Huv. }
  assert (Hq : char (topos_diag x) (diag_Monic x) ∘ (v △ u) ≈ truth ∘ one).
  { transitivity (char (topos_diag x) (diag_Monic x) ∘ (u △ u)).
    - rewrite <- (id_right (v △ u)).
      transitivity ((char (topos_diag x) (diag_Monic x) ∘ first v)
                      ∘ (id △ u)).
      + rewrite <- comp_assoc.
        apply compose_respects; [reflexivity|].
        unfold first; unfork.
      + rewrite <- Hun, <- comp_assoc.
        apply compose_respects; [reflexivity|].
        unfold first; unfork.
    - transitivity (char (topos_diag x) (diag_Monic x)
                      ∘ (topos_diag x ∘ u)).
      + apply compose_respects; [reflexivity|].
        unfold topos_diag; unfork.
      + rewrite comp_assoc, (is_pullback_commutes PB), <- comp_assoc.
        now rewrite (one_unique (one ∘ u) one). }
  destruct (is_pullback_ump PB z (v △ u) one Hq) as [w [Hw1 _] _].
  transitivity w.
  - rewrite <- (exr_fork v u), <- Hw1.
    unfold topos_diag; unfork.
  - rewrite <- (exl_fork v u), <- Hw1.
    unfold topos_diag; unfork.
Qed.

(* The diagonal is a SYMMETRIC relation, so its characteristic map is
   invariant under [swap]; hence the singleton is its own [flip]. *)
Lemma char_diag_swap (x : C) :
  char (topos_diag x) (diag_Monic x) ∘ swap
    ≈ char (topos_diag x) (diag_Monic x).
Proof.
  apply char_unique.
  pose proof (char_pullback (topos_diag x) (diag_Monic x)) as PB.
  assert (Hsd : swap ∘ topos_diag x ≈ topos_diag x)
    by (unfold topos_diag; unfork).
  constructor.
  - rewrite <- comp_assoc, Hsd.
    exact (is_pullback_commutes PB).
  - intros Q q1 q2 Hq.
    destruct (is_pullback_ump PB Q (swap ∘ q1) q2) as [w [Hw1 Hw2] Hwu].
    { rewrite comp_assoc; exact Hq. }
    unshelve refine {| unique_obj := w |}.
    + split; [| exact Hw2].
      rewrite <- (id_left q1), <- swap_invol, <- comp_assoc, <- Hw1.
      rewrite comp_assoc, Hsd; reflexivity.
    + intros v [Hv1 Hv2].
      apply Hwu; split; [| exact Hv2].
      rewrite <- Hv1, comp_assoc, Hsd; reflexivity.
Qed.

Lemma flip_sing (x : C) : flip (sing x) ≈ sing x.
Proof.
  unfold flip, sing.
  rewrite uncurry_curry.
  now rewrite char_diag_swap.
Qed.

(* P IS FAITHFUL, AND THE PROOF USES STEP TWO RATHER THAN THE ADJUNCTION
   MACHINERY.  From [flip_pow_comp] at p := sing a, precomposing the
   singleton with an arrow is [flip] of its P-image postcomposed with the
   singleton; [sing_Monic] then cancels.  (Adjunction/FullFaithful.v's
   counit criterion [right_adjoint_faithful_iff_counit_epic] is NOT used:
   it would cost a Require, and this route needs only step two.) *)
#[export] Instance PowF_Faithful : Faithful PowF.
Proof.
  constructor; intros a0 b0 f g Hfg.
  apply (monic (Monic := sing_Monic a0)).
  assert (Ef : sing a0 ∘ f ≈ flip (fmap[PowF] f ∘ sing a0))
    by (rewrite flip_pow_comp, flip_sing; reflexivity).
  assert (Eg : sing a0 ∘ g ≈ flip (fmap[PowF] g ∘ sing a0))
    by (rewrite flip_pow_comp, flip_sing; reflexivity).
  rewrite Ef, Eg.
  unfold flip.
  now rewrite Hfg.
Defined.

(* Carrying [IsIsomorphism] between C and C^op is a permutation of the
   three fields.  The tree's own copy of this permutation is
   Theory/Morphisms/CokernelPair.v's [IsIsomorphism_of_op] /
   [op_IsIsomorphism_of].  Requiring that module would cost this file exactly
   ONE module of closure (measured with coqdep: its closure minus this file's is
   that module alone), so the thirteen-line duplication below is a choice about
   coupling and not about cost; it is recorded here rather than defended. *)
Definition IsIso_of_op {a b : C} (h : b ~> a)
  (I : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h I)
    (@is_left_inverse (C^op) a b h I)
    (@is_right_inverse (C^op) a b h I).

Definition op_IsIso_of {a b : C} (h : b ~> a)
  (I : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h I)
    (@is_left_inverse C b a h I)
    (@is_right_inverse C b a h I).

(* P REFLECTS ISOMORPHISMS: the image is monic and epic, faithfulness
   reflects both into C^op, the duality quartet of
   Theory/Morphisms/Duality.v exchanges them in C, and balancedness
   concludes. *)
#[export] Instance PowF_ReflectsIsos : ReflectsIsos PowF.
Proof.
  constructor; intros a0 b0 f Hiso.
  pose proof (iso_to_monic (IsIsoToIso _ Hiso)) as Mi.
  pose proof (iso_to_epic  (IsIsoToIso _ Hiso)) as Ei.
  simpl in Mi, Ei.
  pose proof (faithful_reflects_monic PowF f Mi) as Mf.
  pose proof (faithful_reflects_epic  PowF f Ei) as Ef.
  apply op_IsIso_of.
  apply topos_balanced.
  - exact (@Monic_of_op_Epic C b0 a0 f Ef).
  - exact (@Epic_of_op_Monic C b0 a0 f Mf).
Qed.

(** ** (C) The direct image along a mono *)

(* [second] of a mono is a mono: read both components off the product. *)
Lemma second_Monic {u x z : C} (m : u ~> x) (M : Monic m) :
  Monic (@second C _ u x z m).
Proof.
  constructor; intros w p q Hpq.
  assert (H1 : exl ∘ p ≈ exl ∘ q).
  { rewrite <- (exl_second (z:=z) m), <- !comp_assoc, Hpq; reflexivity. }
  assert (H2 : exr ∘ p ≈ exr ∘ q).
  { apply (monic (Monic := M)).
    rewrite !comp_assoc, <- !(exr_second m), <- !comp_assoc, Hpq;
      reflexivity. }
  rewrite <- (id_left p), <- (id_left q), <- fork_exl_exr,
          <- !fork_comp, H1, H2; reflexivity.
Qed.

(* Pushing a subobject forward along a MONO is just composing the two
   monos -- no image factorization is needed, and none is available. *)
Definition sub_push {x y : C} (n : y ~> x) (N : Monic n) (s : SubObj y)
  : SubObj x :=
  {| sub_dom := sub_dom s
   ; sub_mono := n ∘ sub_mono s
   ; sub_is_monic := monic_compose N (sub_is_monic s) |}.

Lemma sub_push_respects {x y : C} (n : y ~> x) (N : Monic n)
      (s s' : SubObj y) (Hs : s ≈ s') :
  sub_push n N s ≈ sub_push n N s'.
Proof.
  destruct Hs as [i Hi].
  exists i; simpl.
  rewrite <- comp_assoc.
  now rewrite Hi.
Qed.

(* Reindexing a pushed subobject along the same mono returns it. *)
Lemma sub_reindex_push {x y : C} (n : y ~> x) (N : Monic n) (s : SubObj y) :
  sub_reindex n (sub_push n N s) ≈ s.
Proof.
  apply (sub_reindex_transport n (sub_push n N s) s id).
  constructor.
  - simpl; cat.
  - simpl; intros Q q1 q2 Hq.
    unshelve refine {| unique_obj := q2 |}.
    + split; [| cat].
      apply (monic (Monic := N)).
      rewrite Hq, comp_assoc; reflexivity.
    + intros w [Hw1 Hw2]; simpl in *.
      now rewrite <- Hw2; cat.
Qed.

(* The membership subobject of Pow x × x, and its characteristic map. *)
Definition pow_mem (x : C) : SubObj (Pow x × x) :=
  sub_reindex eval truth_subobject.

Lemma char_mem (x : C) : char_sub (pow_mem x) ≈ eval.
Proof. exact (classifier_char_roundtrip eval). Qed.

(* Classification is injective on subobjects: pull truth back on both
   sides and use the round trip twice. *)
Lemma char_sub_inj {x : C} (s s' : SubObj x) :
  char_sub s ≈ char_sub s' → s ≈ s'.
Proof.
  intros Hc.
  transitivity (sub_reindex (char_sub s) truth_subobject).
  - symmetry; apply classifier_pullback_roundtrip.
  - transitivity (sub_reindex (char_sub s') truth_subobject).
    + apply sub_reindex_respects_mor; exact Hc.
    + apply classifier_pullback_roundtrip.
Qed.

(* Evaluation intertwines the P-image of m on the left with m on the
   right: the substitution law for the membership relation. *)
Lemma eval_pow_square {u x : C} (m : u ~> x) :
  eval ∘ first (fmap[PowF] m) ≈ eval ∘ second m.
Proof.
  rewrite eval_first.
  simpl.
  rewrite uncurry_curry, id_left.
  reflexivity.
Qed.

(* The same square one level up, on membership subobjects. *)
Lemma mem_pow_square {u x : C} (m : u ~> x) :
  sub_reindex (first (fmap[PowF] m)) (pow_mem u)
    ≈ sub_reindex (second m) (pow_mem x).
Proof.
  apply char_sub_inj.
  rewrite !char_reindex, !char_mem.
  apply eval_pow_square.
Qed.

(* THE DIRECT IMAGE along a mono m: classify the pushed membership
   relation and transpose. *)
Definition ex_mono {u x : C} (m : u ~> x) (M : Monic m) : Pow u ~> Pow x :=
  curry (char_sub (sub_push (second m) (second_Monic m M) (pow_mem u))).

(* THE RETRACTION LAW: P m splits the direct image along m. *)
Theorem pow_ex_mono {u x : C} (m : u ~> x) (M : Monic m) :
  fmap[PowF] m ∘ ex_mono m M ≈ id.
Proof.
  unfold ex_mono.
  rewrite pow_precompose.
  rewrite <- char_reindex.
  rewrite (char_sub_respects _ _
             (sub_reindex_push (second m) (second_Monic m M) (pow_mem u))).
  rewrite char_mem.
  apply curry_eval.
Qed.

(** ** (D) Pullback plumbing and Beck-Chevalley *)

Lemma IsPullback_sym {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y} :
  IsPullback f g P p1 p2 → IsPullback g f P p2 p1.
Proof.
  intros HP; constructor.
  - symmetry; exact (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    destruct (is_pullback_ump HP Q q2 q1 (symmetry Hq)) as [u [U1 U2] Uu].
    unshelve refine {| unique_obj := u |}.
    + split; assumption.
    + intros v [V1 V2]; apply Uu; split; assumption.
Qed.

(* A pullback square multiplied on the left by a fixed object stays a
   pullback. *)
Lemma second_pullback {b a k : C} {f g : b ~> a} {p1 p2 : k ~> b}
      (HP : IsPullback f g k p1 p2) (z : C) :
  IsPullback (@second C _ b a z f) (@second C _ b a z g)
             (z × k) (second p1) (second p2).
Proof.
  constructor.
  - rewrite <- !second_comp.
    now rewrite (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    assert (Hl : exl ∘ q1 ≈ exl ∘ q2).
    { transitivity (exl ∘ (second f ∘ q1)).
      - rewrite comp_assoc, exl_second; reflexivity.
      - rewrite Hq, comp_assoc, exl_second; reflexivity. }
    assert (Hr : f ∘ (exr ∘ q1) ≈ g ∘ (exr ∘ q2)).
    { transitivity (exr ∘ (second f ∘ q1)).
      - rewrite !comp_assoc, exr_second; reflexivity.
      - rewrite Hq, !comp_assoc, exr_second; reflexivity. }
    destruct (is_pullback_ump HP Q (exr ∘ q1) (exr ∘ q2) Hr)
      as [v [V1 V2] Vu].
    unshelve refine {| unique_obj := (exl ∘ q1) △ v |}.
    + split; unfold second.
      * rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite V1.
        rewrite <- (id_left q1) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
      * rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite V2, Hl.
        rewrite <- (id_left q2) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
    + intros w [W1 W2].
      assert (Ew : exr ∘ w ≈ v).
      { symmetry; apply Vu; split.
        - rewrite <- W1, !comp_assoc, exr_second; reflexivity.
        - rewrite <- W2, !comp_assoc, exr_second; reflexivity. }
      assert (El : exl ∘ w ≈ exl ∘ q1).
      { rewrite <- W1, !comp_assoc, exl_second; reflexivity. }
      rewrite <- (id_left w), <- fork_exl_exr, <- fork_comp, El, Ew.
      reflexivity.
Qed.

(* [first] of one arrow and [second] of another form a pullback square in
   the product, with NO monicity hypothesis on either: the two act in
   independent coordinates.  This is the square Beck-Chevalley is applied
   to on the right-hand side of [pow_bc]. *)
Lemma first_second_pullback {z w u x : C} (phi : z ~> w) (m : u ~> x) :
  IsPullback (@first C _ z w x phi) (@second C _ u x w m)
             (z × u) (@second C _ u x z m) (@first C _ z w u phi).
Proof.
  constructor.
  - unfold first, second; unfork.
  - intros Q q1 q2 Hq.
    assert (Hl : phi ∘ (exl ∘ q1) ≈ exl ∘ q2).
    { transitivity (exl ∘ (first phi ∘ q1)).
      - rewrite !comp_assoc, exl_first; reflexivity.
      - rewrite Hq, comp_assoc, exl_second; reflexivity. }
    assert (Hr : exr ∘ q1 ≈ m ∘ (exr ∘ q2)).
    { transitivity (exr ∘ (first phi ∘ q1)).
      - rewrite comp_assoc, exr_first; reflexivity.
      - rewrite Hq, !comp_assoc, exr_second; reflexivity. }
    unshelve refine {| unique_obj := (exl ∘ q1) △ (exr ∘ q2) |}.
    + split.
      * unfold second.
        rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite <- Hr.
        rewrite <- (id_left q1) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
      * unfold first.
        rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite Hl.
        rewrite <- (id_left q2) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
    + intros v [V1 V2].
      assert (El : exl ∘ v ≈ exl ∘ q1).
      { rewrite <- V1, comp_assoc, exl_second; reflexivity. }
      assert (Er : exr ∘ v ≈ exr ∘ q2).
      { rewrite <- V2, comp_assoc, exr_first; reflexivity. }
      rewrite <- (id_left v), <- fork_exl_exr, <- fork_comp, El, Er.
      reflexivity.
Qed.

(* BECK-CHEVALLEY at the level of subobjects, for a pushforward along a
   MONO: reindexing a pushed subobject along the other leg of a pullback square
   is pushing forward the reindexed one.  Eight lines of [pullback_paste]. *)
Lemma bc_mono {X Y Z K : C} {F : X ~> Z} {G : Y ~> Z}
      {p1 : K ~> X} {p2 : K ~> Y}
      (HP : IsPullback F G K p1 p2) (MF : Monic F) (M2 : Monic p2)
      (R : SubObj X) :
  sub_reindex G (sub_push F MF R) ≈ sub_push p2 M2 (sub_reindex p1 R).
Proof.
  apply (sub_reindex_transport G (sub_push F MF R)
           (sub_push p2 M2 (sub_reindex p1 R))
           (pullback_snd p1 (sub_mono R) (pullback p1 (sub_mono R)))).
  apply IsPullback_sym.
  exact (pullback_paste HP
           (IsPullback_sym
              (pullback_is_pullback p1 (sub_mono R)
                 (pullback p1 (sub_mono R))))).
Qed.

(* A co-reflexive parallel pair -- one with a common RETRACTION -- has its
   equalizer as the pullback of the pair against itself, with BOTH legs
   the equalizing map.  This is where co-reflexivity is spent. *)
Lemma coreflexive_equalizer_pullback {a b k : C} {f g : b ~> a}
      {r : a ~> b} (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id)
      {e : k ~> b} (HE : IsEqualizer f g k e) :
  IsPullback f g k e e.
Proof.
  constructor.
  - exact (fork_eq HE).
  - intros Q q1 q2 Hq.
    assert (Hq12 : q1 ≈ q2).
    { rewrite <- (id_left q1), <- Hf, <- comp_assoc, Hq,
              comp_assoc, Hg, id_left; reflexivity. }
    assert (Hfork : f ∘ q1 ≈ g ∘ q1).
    { rewrite Hq, Hq12; reflexivity. }
    destruct (eq_desc HE q1 Hfork) as [u Hu Huniq].
    unshelve refine {| unique_obj := u |}.
    + split.
      * exact Hu.
      * rewrite Hu; exact Hq12.
    + intros v [V1 V2]; apply Huniq; exact V1.
Qed.

(* THE BECK-CHEVALLEY LAW FOR P, [SplitCoequalizer]'s fourth field.  Both
   sides are transposes; [pow_precompose] and [curry_comp_l] reduce them
   to characteristic maps, [char_reindex] turns those into subobjects, and
   the two [bc_mono] applications meet at [mem_pow_square]. *)
Theorem pow_bc {a b k : C} {f g : b ~> a} {e : k ~> b}
      (Mf : Monic f) (Me : Monic e) (HP : IsPullback f g k e e) :
  fmap[PowF] g ∘ ex_mono f Mf ≈ ex_mono e Me ∘ fmap[PowF] e.
Proof.
  unfold ex_mono.
  rewrite pow_precompose.
  transitivity (curry (char_sub (sub_push (second e) (second_Monic e Me)
                                   (pow_mem k)) ∘ first (fmap[PowF] e))).
  - apply curry_respects.
    rewrite <- !char_reindex.
    apply char_sub_respects.
    transitivity (sub_push (second e) (second_Monic e Me)
                    (sub_reindex (second e) (pow_mem b))).
    + exact (bc_mono (second_pullback HP (Pow b))
               (second_Monic f Mf) (second_Monic e Me) (pow_mem b)).
    + transitivity (sub_push (second e) (second_Monic e Me)
                      (sub_reindex (first (fmap[PowF] e)) (pow_mem k))).
      * apply sub_push_respects.
        symmetry.
        apply mem_pow_square.
      * symmetry.
        exact (bc_mono
                 (IsPullback_sym (first_second_pullback (fmap[PowF] e) e))
                 (second_Monic e Me) (second_Monic e Me) (pow_mem k)).
  - symmetry.
    apply curry_comp_l.
Qed.

(** ** (E) The split coequalizer, and monadicity *)

(* Contravariant functoriality of P, in the orientation the laws want:
   [P e ∘ P f] is [P (f ∘ e)], with both composites read in C.  Stated as
   a lemma because [Program] and [simpl] unfold [fmap[PowF]] to its
   [curry] normal form, after which [fmap_comp] no longer matches. *)
Lemma pow_fmap_comp {a b k : C} (f : b ~> a) (e : k ~> b) :
  fmap[PowF] e ∘ fmap[PowF] f ≈ fmap[PowF] (f ∘ e).
Proof. symmetry; exact (@fmap_comp (C^op) C PowF a b k e f). Qed.

(* THE HEART OF THE ARGUMENT.  For a co-reflexive pair f, g : b ⇉ a with
   common retraction r, and any equalizer e of the pair, the P-images form
   a SPLIT coequalizer: the two direct images ∃_e and ∃_f are the two
   sections the record asks for, and its four laws are exactly
   functoriality, [pow_ex_mono] twice, and [pow_bc].  Co-reflexivity is
   spent in TWO places: both halves at [coreflexive_equalizer_pullback],
   which turns the equalizer into the pullback square Beck-Chevalley
   needs, and the retraction of f alone at [sections_are_monic], which
   makes f a mono so that the direct image ∃_f exists at all.

   Built with [unshelve refine] rather than [Program] deliberately: the
   obligation statements [Program] generates have [fmap[PowF]] unfolded to
   its [curry] normal form, and neither [fmap_comp] nor [pow_ex_mono] then
   matches. *)
Definition pow_split_coequalizer
  {a b k : C} {f g : b ~> a} {r : a ~> b}
  (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id)
  {e : k ~> b} (HE : IsEqualizer f g k e) :
  SplitCoequalizer (fmap[PowF] f) (fmap[PowF] g).
Proof.
  unshelve refine {| scoeq_obj := Pow k
                   ; scoeq_e   := fmap[PowF] e
                   ; scoeq_s   := ex_mono e (equalizer_monic f g HE)
                   ; scoeq_t   := ex_mono f (@sections_are_monic C b a f
                                    {| section := r
                                     ; section_comp := Hf |}) |}.
  - (* law1: P e coforks the image pair *)
    rewrite !pow_fmap_comp.
    now rewrite (fork_eq HE).
  - (* law2: ∃_e splits P e *)
    apply pow_ex_mono.
  - (* law3: ∃_f splits P f *)
    apply pow_ex_mono.
  - (* law4: Beck-Chevalley *)
    apply (pow_bc _ _ (coreflexive_equalizer_pullback Hf Hg HE)).
Defined.

(* Crude monadicity's second hypothesis.  In C^op a reflexive pair is a
   CO-reflexive pair of C and a coequalizer is an equalizer, both
   definitionally; [IsEqualizer_op_of_IsCoequalizer] read at C^op is the
   field repackaging that makes the conversion available to [Monic e]
   through [equalizer_monic].  The obligation quantifies over ANY
   coequalizer of the pair, not a chosen one, and the argument is uniform
   in e. *)
Definition pow_PreservesReflexiveCoequalizers :
  PreservesReflexiveCoequalizers PowF :=
  fun a b f g RP k e HC =>
    split_coequalizer_is_coequalizer _ _
      (pow_split_coequalizer (refl_section_f RP) (refl_section_g RP)
         (@IsEqualizer_op_of_IsCoequalizer (C^op) a b f g k e HC)).

(* The equivalence C^op ≃ EM(P ◯ P^op), CONSUMED from Crude.v. *)
Definition pow_equivalence :
  EquivalenceOfCategories (EM_Comparison pow_adjunction) :=
  crude_monadicity pow_adjunction op_HasReflexiveCoequalizers
    pow_PreservesReflexiveCoequalizers PowF_ReflectsIsos.

(* PARÉ'S THEOREM: the power-object functor is monadic. *)
Definition power_object_monadic : Monadic PowF :=
  (Opposite_Functor PowF; (pow_adjunction; pow_equivalence)).

End ToposMonadic.
