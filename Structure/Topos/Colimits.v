Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Terminal.
Require Import Category.Theory.Equivalence.Pullback.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* [Category.Functor.Opposite] opens [functor_scope], and
   [Category.Theory.Monad], which has no [Open Scope] of its own, carries it in
   by requiring that module; after either Require a bare [C^op] on a CATEGORY
   parses as [Opposite_Functor C] and is rejected with "The term C has type
   Category while it is expected to have type ?C ⟶ ?D".  Reopening
   [category_scope] restores the reading this file wants.  A second hazard, met
   while building [EM_Terminal]: a [{| t_alg := … |}] record literal needs
   [Category.Monad.Algebra] REQUIRED EXPLICITLY -- requiring only
   [Category.Monad.Eilenberg.Moore], which uses the record, reports "t_alg: Not
   a projection". *)
Open Scope category_scope.

(* EVERY ELEMENTARY TOPOS HAS FINITE COLIMITS.

   nLab:      https://ncatlab.org/nlab/show/topos
   nLab:      https://ncatlab.org/nlab/show/Pare%27s+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Topos
   Paper:     Paré, "Colimits in topoi", Bulletin of the American
              Mathematical Society 80 (1974), pp. 556-561

   THREE BOOKS STATE THIS IN FOUR PLACES AND NONE OF THEM PROVES IT.

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.10,
   book p. 107 (`maclane:IV.10:remark2`), closes the topos section with:

     "The axioms for a topos have many useful consequences. For exam-
      ples, every topos has all finite colimits."

   The Appendix "Foundations", §App.1, book p. 290
   (`maclane:App.1:remark2`), singles out the initial object:

     "These axioms for a topos then hold for the category of sets. They
      have a number of strong consequences. For example, they give all
      finite cate- gorical products and pullbacks, as well as all finite
      coproducts, including an initial object 0, the empty set."

   Awodey, "Category Theory" (1st ed., Carnegie Mellon pre-print,
   September 2005), §8.8, printed p. 210
   (`awodey:8.8:remark-topos-properties`), immediately after Definition
   8.16:

     "This compact definition proves to be amazingly rich in
      consequences: it can be shown for instance that topoi also have all
      finite colimits and that every slice category of a topos is again a
      topos. We refer the reader to the books by Mac Lane and Moerdijk,
      Johnstone, and McLarty for information on topoi, and here just give
      an example (albeit one the covers a very large number of cases)."

   Fong and Spivak, "Seven Sketches in Compositionality", §7.2.1, printed
   p. 225 (`7sketches:7.2.1:remark-topos-properties`):

     "Although we will not prove it in this book, toposes are categories
      that are similar to Set in many ways. Here are some facts that are
      true of any topos E:
         1. E has all limits,
         2. E has all colimits,
         3. E is cartesian closed,
         4. E has epi-mono factorizations,
         5. E has a subobject classifier 1 --true--> Ω."

   Mac Lane-Moerdijk, the reference Mac Lane §IV.10 and Awodey both send the
   reader to (the Appendix page and Seven Sketches name none), was NOT available
   here.  The proof below is Paré's, RECONSTRUCTED and CHECKED BY COMPILATION.

   THE ROUTE, in one paragraph.  The contravariant power-object functor
   P = Ω^(−) : E^op ⟶ E is self-adjoint on the right through the
   cartesian-closed [flip], with no subobject classifier consumed at that
   step (Structure/Topos/Power.v).  It is MONADIC: reflexive coequalizers
   in E^op are three lines of pre-existing reductions, P is faithful
   through the singleton map, P reflects isomorphisms because a topos is
   balanced, and P carries the equalizer of a co-reflexive pair to a SPLIT
   coequalizer -- direct image along a mono (no image factorization) for
   the two sections, Beck-Chevalley by pullback pasting for the fourth
   law.  Crude monadicity is then CONSUMED (Structure/Topos/Monadic.v's
   [power_object_monadic], through Monad/Monadicity/Crude.v's
   [crude_monadicity]).  So E^op is equivalent to the Eilenberg-Moore
   category of P ◯ P^op, whose terminal object and pullbacks are built
   here on the carriers and transported back along the equivalence.  In
   E^op a terminal object is an INITIAL object of E, a binary product is a
   COPRODUCT, an equalizer is a COEQUALIZER and a pullback is a PUSHOUT --
   all four by NOTATION or by a pre-existing one-line bridge.

   WHY THE ELEMENTARY ROUTE AND NOT THE [Limit] ROUTE.  The universe fact behind
   it is a MEASUREMENT, pinned in Test/ProbeToposColimits405.v; the conclusion
   drawn from it is an inference.  [Terminal_Limit] (Structure/Limit/Terminal.v)
   and [Cartesian_Limit] (Structure/Limit/Cartesian.v) are stated over
   [Category@{u Set Set}]: they pin the ambient category's hom AND proof
   universes to the literal [Set].  Going through them would have made "every
   elementary topos has finite colimits" a theorem about Set-homed toposes only
   -- an inference from those two refusals and not a compiled comparison, since
   the [Limit] route was not built.  So no [Cone], [Limit], [Colimit] or
   [Cocomplete] token occurs outside a comment in Structure/Topos/Power.v,
   Structure/Topos/Monadic.v, Theory/Equivalence/Pullback.v or this file --
   MEASURED, and with one stated exception: the module path
   [Category.Structure.Limit.Preservation] appears in one [Require] of
   Structure/Topos/Monadic.v, where it supplies [ReflectsIsos] and no limit
   vocabulary at all.  Correspondingly no [Cocomplete] claim is made: the
   theorem is exactly the four elementary generator records, packaged as
   [topos_has_finite_colimits].

   WHAT IS NEW TO THE TREE BEYOND THE ISSUE'S ASK.  A topos is balanced; the
   singleton map and its monicity; the direct image along a mono and its
   retraction law; Beck-Chevalley for subobjects along a pullback square; the
   power functor, its self-adjointness and its monadicity; pullbacks transported
   along an equivalence of categories (Theory/Equivalence/Pullback.v -- MEASURED
   with the five new files excluded, a whole-tree search for the six names
   [Terminal_transport], [Initial_transport], [Cartesian_transport],
   [Cocartesian_transport], [HasEqualizers_transport] and
   [HasPullbacks_transport] returns 8 lines, all in
   Theory/Equivalence/Terminal.v, naming [Terminal_transport],
   [Initial_transport] and their two object readbacks; read that as a NAME
   search, since other structures ARE carried across an equivalence under other
   names -- Instance/Proset/Limit.v's [Complete_equivalence_invariant] and
   [Cocomplete_equivalence_invariant], Theory/Equivalence/Monoidal.v's
   [Transported_Monoidal], Theory/Equivalence/Adjunction.v's
   [Transported_Adjunction] -- so what is new is the PULLBACK case, not the
   pattern); and, at the instance level, the FIRST [HasCoequalizers FinSet] the
   tree has ever had (in Test/ProbeToposColimits405.v -- no .v file declares a
   constant of that type, and the only two .v hits for the phrase
   [HasCoequalizers FinSet] elsewhere are NOT-DELIVERED notes in
   Instance/Sets/Coequalizer.v and Instance/Sets/Coequalizer/Interconnect.v
   about what those two files do not build, which therefore do not go stale).

   NO CONSTANT DECLARED HERE IS REGISTERED AS AN [Instance].  A chosen colimit
   must not become globally resolvable: the delivered constants are plain
   [Definition]s (with [Example]s, [Lemma]s and one [Program Definition] beside
   them), so a consumer passes the topos explicitly, exactly as
   Instance/FinSet/Topos.v's [FinSet_Topos] is passed explicitly.  The one
   registration below is the [Existing Instance pow_monad] of the section
   preamble, declared local to this section and there only so that [t_alg],
   [ret] and [join] resolve.

   NOT DELIVERED.  No [Cocomplete] and no infinite colimits.  No
   [Limit]/[Colimit]-shaped statement and no finite-shape induction -- both the
   colimit theorem and Structure/Topos/Monadic.v's [topos_finitely_complete] are
   at GENERATOR level, and a [Limit K]-for-every-finite-shape-J statement is
   still not claimed anywhere in this library.  No image factorization and no
   direct image along a general arrow (only along monos).  No route through
   Beck's precise theorem.  No naturality of any identification.  No [eq_refl]
   readback at FinSet: the agreement with FinSet's computable colimits is
   delivered at [≅]; the [eq_refl] form for the initial object is pinned as a
   CONVERSION refusal in the probe (the coproduct and pushout readbacks are
   delivered at [≅] only, and no [eq_refl] form of them is attempted); and its
   cause is NOT isolated -- the derived object is the quasi-inverse
   [Crude_Inverse] at [EM_Terminal]'s object ([topos_Initial_obj] reads that
   back at [eq_refl]), i.e. the reflexive coequalizer Monad/Monadicity/Crude.v
   chooses through [op_HasReflexiveCoequalizers] and [topos_HasEqualizers], a
   chain that never consumes [PowF_ReflectsIsos] ([Crude_Inverse] takes no
   [ReflectsIsos] argument at all; in Crude.v [refl] enters only
   [crude_theta_iso] and one [Proof using]), and no experiment names the
   constant that blocks the reduction.  No second concrete topos.  Nothing about
   slices of a topos (Awodey's other half), nor about epi-mono factorization
   (Seven Sketches' clause 4), both of which are separate obligations.

   Of this file's five [Defined] tokens, [em_pb_fst], [em_pb_snd] and
   [EM_Pullback] are LOAD-BEARING -- each flipped alone to [Qed] breaks the
   file, [em_pb_fst] and [em_pb_snd] at [EM_Pullback]'s own commuting-square
   obligation and [EM_Pullback] at its first readback, [EM_Pullback_carrier] --
   and [EM_Terminal]'s two data obligations are not, the file compiling
   unchanged with either flipped alone; the flip was run per token. *)

Section ToposColimits.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

Local Notation TT := (PowF ◯ Opposite_Functor PowF).
Local Notation EMT := (@EilenbergMoore C TT pow_monad).

(* The monad is not a registered instance -- a chosen monad structure
   must not become globally resolvable -- so it is made available to
   [t_alg], [ret] and [join] locally, for this section only. *)
#[local] Existing Instance pow_monad.

(** ** (A) The terminal algebra *)

(* The terminal object of C carries a unique algebra structure, and every
   algebra map into it is unique, both by [one_unique]. *)
Program Definition EM_Terminal : @Terminal EMT := {|
  terminal_obj := (@terminal_obj C _; _)
|}.
Next Obligation.
  unshelve refine {| t_alg := one |}; apply one_unique.
Defined.
Next Obligation.
  unshelve refine {| t_alg_hom := one |}; apply one_unique.
Defined.
Next Obligation.
  destruct f, g; simpl; apply one_unique.
Qed.

(** ** (B) Pullbacks of algebras, computed on carriers *)

Section EMPullback.

Context {xa ya za : EMT}.
Context (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za).

Definition em_pb : Pullback (t_alg_hom[FF]) (t_alg_hom[GG]) :=
  @pullback C _ _ _ _ (t_alg_hom[FF]) (t_alg_hom[GG]).

Definition em_pb_carrier : C := Pull _ _ em_pb.
Definition em_pb_p1 : em_pb_carrier ~> ``xa := pullback_fst _ _ em_pb.
Definition em_pb_p2 : em_pb_carrier ~> ``ya := pullback_snd _ _ em_pb.

(* The two candidate actions on the carriers form a cone over the target
   algebra: each algebra square turns [t_alg_hom] past the action, and the
   pullback square then equates the two T-images. *)
Lemma em_pb_cone :
  t_alg_hom[FF] ∘ (t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1)
    ≈ t_alg_hom[GG] ∘ (t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2).
Proof.
  rewrite !comp_assoc.
  rewrite !t_alg_hom_commutes.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [reflexivity|].
  apply fmap_respects.
  exact (pullback_commutes _ _ em_pb).
Qed.

Definition em_pb_action : TT em_pb_carrier ~> em_pb_carrier :=
  unique_obj (ump_pullbacks _ _ em_pb _
                (t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1)
                (t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2)
                em_pb_cone).

Lemma em_pb_action_1 :
  em_pb_p1 ∘ em_pb_action ≈ t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1.
Proof.
  exact (fst (unique_property
    (ump_pullbacks _ _ em_pb _ _ _ em_pb_cone))).
Qed.

Lemma em_pb_action_2 :
  em_pb_p2 ∘ em_pb_action ≈ t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2.
Proof.
  exact (snd (unique_property
    (ump_pullbacks _ _ em_pb _ _ _ em_pb_cone))).
Qed.

(* Both algebra laws are checked leg by leg through joint monicity; the
   unit law spends [fmap_ret] and [t_id], the action law [fmap_comp],
   [t_action] and [join_fmap_fmap]. *)
Lemma em_pb_t_id : em_pb_action ∘ ret ≈ id.
Proof.
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite comp_assoc, em_pb_action_1, <- comp_assoc, <- fmap_ret,
            comp_assoc, t_id, id_left, id_right.
    reflexivity.
  - rewrite comp_assoc, em_pb_action_2, <- comp_assoc, <- fmap_ret,
            comp_assoc, t_id, id_left, id_right.
    reflexivity.
Qed.

Lemma em_pb_t_action :
  em_pb_action ∘ fmap[TT] em_pb_action ≈ em_pb_action ∘ join.
Proof.
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite !comp_assoc, em_pb_action_1, <- !comp_assoc, <- fmap_comp,
            em_pb_action_1, fmap_comp, comp_assoc, t_action,
            <- !comp_assoc, join_fmap_fmap, !comp_assoc.
    reflexivity.
  - rewrite !comp_assoc, em_pb_action_2, <- !comp_assoc, <- fmap_comp,
            em_pb_action_2, fmap_comp, comp_assoc, t_action,
            <- !comp_assoc, join_fmap_fmap, !comp_assoc.
    reflexivity.
Qed.

Definition em_pb_algebra : TAlgebra TT em_pb_carrier := {|
  t_alg    := em_pb_action ;
  t_id     := em_pb_t_id ;
  t_action := em_pb_t_action
|}.

Definition em_pb_alg_obj : EMT := (em_pb_carrier; em_pb_algebra).

Definition em_pb_fst : em_pb_alg_obj ~{EMT}~> xa.
Proof.
  unshelve refine {| t_alg_hom := em_pb_p1 |}.
  exact em_pb_action_1.
Defined.

Definition em_pb_snd : em_pb_alg_obj ~{EMT}~> ya.
Proof.
  unshelve refine {| t_alg_hom := em_pb_p2 |}.
  exact em_pb_action_2.
Defined.

(* The mediator of a competing cone of algebras is the carrier mediator;
   that it is an algebra map is again checked leg by leg. *)
Lemma em_pb_med_commutes (q : EMT) (q1 : q ~{EMT}~> xa)
      (q2 : q ~{EMT}~> ya)
      (Hq : t_alg_hom[FF] ∘ t_alg_hom[q1] ≈ t_alg_hom[GG] ∘ t_alg_hom[q2]) :
  unique_obj (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1]) (t_alg_hom[q2]) Hq)
    ∘ t_alg[projT2 q]
  ≈ em_pb_action ∘ fmap[TT]
      (unique_obj (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1])
                     (t_alg_hom[q2]) Hq)).
Proof.
  pose proof (unique_property
    (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1]) (t_alg_hom[q2]) Hq))
    as [M1 M2].
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite comp_assoc.
    change (pullback_fst _ _ em_pb) with em_pb_p1.
    rewrite M1, (t_alg_hom_commutes (TAlgebraHom := q1)).
    rewrite comp_assoc, em_pb_action_1, <- !comp_assoc, <- !fmap_comp.
    now rewrite M1.
  - rewrite comp_assoc.
    change (pullback_snd _ _ em_pb) with em_pb_p2.
    rewrite M2, (t_alg_hom_commutes (TAlgebraHom := q2)).
    rewrite comp_assoc, em_pb_action_2, <- !comp_assoc, <- !fmap_comp.
    now rewrite M2.
Qed.

(* Built with [unshelve refine] rather than [Program] so that the
   competing cone and its commuting witness are named by [intros] rather
   than by [Program]'s numbering. *)
Definition EM_Pullback : Pullback FF GG.
Proof.
  unshelve refine {| Pull         := em_pb_alg_obj
                   ; pullback_fst := em_pb_fst
                   ; pullback_snd := em_pb_snd |}.
  - (* the square commutes: it is the carrier square *)
    exact (pullback_commutes _ _ em_pb).
  - (* the universal property: the carrier mediator, made an algebra map
       by [em_pb_med_commutes]; uniqueness is the carrier's, since a
       morphism of EMT is determined by its underlying arrow *)
    intros q q1 q2 Hq.
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine {| t_alg_hom := unique_obj
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq) |}.
      apply em_pb_med_commutes.
    + exact (unique_property
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq)).
    + intros v Hv.
      exact (uniqueness
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq)
        t_alg_hom[v] Hv).
Defined.

End EMPullback.

Definition EM_HasPullbacks : @HasPullbacks EMT :=
  {| pullback := fun x y z F G => EM_Pullback F G |}.

(** ** (C) Transport back, and the four shapes *)

(* The equivalence read backwards: EM(P ◯ P^op) ≃ C^op. *)
Definition pow_equivalence_sym :
  @EquivalenceOfCategories EMT (C^op)
    (@quasi_inverse (C^op) EMT (EM_Comparison pow_adjunction)
       pow_equivalence) :=
  @EquivalenceOfCategories_sym (C^op) EMT (EM_Comparison pow_adjunction)
    pow_equivalence.

(* [@Initial C] IS [@Terminal (C^op)], so the terminal algebra transports
   straight to an initial object of the topos. *)
Definition topos_Initial : @Initial C :=
  Terminal_transport pow_equivalence_sym EM_Terminal.

Definition topos_HasPullbacks_op : @HasPullbacks (C^op) :=
  HasPullbacks_transport pow_equivalence_sym EM_HasPullbacks.

(* [@Cocartesian C] IS [@Cartesian (C^op)], and the terminal object of
   C^op is the initial object just built. *)
Definition topos_Cocartesian : @Cocartesian C :=
  @Cartesian_of_HasPullbacks_Terminal (C^op) topos_Initial
    topos_HasPullbacks_op.

Definition topos_HasEqualizers_op : @HasEqualizers (C^op) :=
  @HasEqualizers_of_HasPullbacks_Terminal (C^op) topos_Initial
    topos_HasPullbacks_op.

Definition topos_HasCoequalizers : @HasCoequalizers C :=
  @HasCoequalizers_of_HasEqualizers_op C topos_HasEqualizers_op.

Definition topos_HasPushouts : @HasPushouts C :=
  HasPushouts_of_HasPullbacks_op topos_HasPullbacks_op.

(* MAC LANE §IV.10 REMARK 2, at generator level: initial object, binary
   coproducts, coequalizers, pushouts. *)
Definition topos_has_finite_colimits :
  @Initial C * @Cocartesian C * @HasCoequalizers C * @HasPushouts C :=
  (topos_Initial, topos_Cocartesian, topos_HasCoequalizers,
   topos_HasPushouts).

(** ** (D) Readbacks *)

(* The initial object IS the quasi-inverse's image of the terminal
   algebra, and the terminal algebra's carrier IS the terminal object of
   the topos -- both on the nose. *)
Example topos_Initial_obj :
  @initial_obj C topos_Initial
    = @quasi_inverse (C^op) EMT (EM_Comparison pow_adjunction)
        pow_equivalence (@terminal_obj EMT EM_Terminal) := eq_refl.

Example EM_Terminal_carrier :
  ``(@terminal_obj EMT EM_Terminal) = @terminal_obj C _ := eq_refl.

(* A pullback of algebras is the pullback of the carriers, with both
   projections the carrier projections. *)
Example EM_Pullback_carrier {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  ``(Pull FF GG (EM_Pullback FF GG)) = em_pb_carrier FF GG := eq_refl.

Example EM_Pullback_fst {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  t_alg_hom[pullback_fst FF GG (EM_Pullback FF GG)]
    = em_pb_p1 FF GG := eq_refl.

Example EM_Pullback_snd {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  t_alg_hom[pullback_snd FF GG (EM_Pullback FF GG)]
    = em_pb_p2 FF GG := eq_refl.

(* The pushout is the transported pullback read in C^op, with no second
   construction interposed. *)
Example topos_HasPushouts_is_op {x y z : C} (f : x ~> y) (g : x ~> z) :
  @pushout C topos_HasPushouts x y z f g
    = @pullback (C^op) topos_HasPullbacks_op y z x f g := eq_refl.

(* The four components of the headline are the four records built above. *)
Example topos_has_finite_colimits_fst :
  fst (fst (fst topos_has_finite_colimits)) = topos_Initial := eq_refl.

Example topos_has_finite_colimits_snd :
  snd (fst (fst topos_has_finite_colimits)) = topos_Cocartesian := eq_refl.

Example topos_has_finite_colimits_thd :
  snd (fst topos_has_finite_colimits) = topos_HasCoequalizers := eq_refl.

Example topos_has_finite_colimits_fth :
  snd topos_has_finite_colimits = topos_HasPushouts := eq_refl.

End ToposColimits.
