Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Regular.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

(** * Pullbacks in [Sets] *)

(* nLab:      https://ncatlab.org/nlab/show/pullback
   nLab:      https://ncatlab.org/nlab/show/kernel+pair
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   Mac Lane, "Categories for the Working Mathematician" 2nd ed., Springer
   GTM 5 1998, §III.4 Exercise 1 (p. 72) -- the pullback in Set is the set
   of pairs on which the two legs agree, with the evident projections --
   and §III.4 Exercise 6 (p. 72), the kernel pair: the pullback of f along
   itself, which is the equivalence relation "f x = f x'"
   ([maclane:III.4:ex1], [maclane:III.4:ex6]).  Awodey, "Category Theory"
   2nd ed., Oxford Logic Guides 52 2010, §5.2 gives the same construction
   and, in Example 5.9, the case that makes it useful: pulling a subset
   inclusion V ↪ B back along f : A ⟶ B is taking the preimage
   {a | f a ∈ V} ([awodey:5.2:example9]).  Riehl, "Category Theory in
   Context", Dover 2016, §3.2 Example 3.2.9 records that a pullback IS the
   equalizer of the two composites out of the binary product
   ([riehl:3.2:example9]).

   WHAT WAS MISSING

   [HasPullbacks] (Structure/Pullback.v:215) had exactly ONE inhabitant
   for a concrete category, [FinSet_Pullbacks] (Instance/FinSet/
   Classifier.v:264) -- measured by [rg -n "HasPullbacks" -g '*.v' .]
   over the whole tree, whose other hits are the class itself, prose, the
   generic conditionals [HasPullbacks_of_Cartesian_HasEqualizers]
   (Structure/Pullback/Reduction.v:269), [HasPullbacks_op_of_HasPushouts]
   (Structure/Pushout.v:158) and [codomain_cleaving_pullbacks]
   (Construction/Displayed/Codomain.v:232) -- THREE, an earlier revision
   named two -- the two [*_of_HasPullbacks_Terminal] constants named for
   it, the class FIELDS [regular_pullbacks] (Structure/Regular.v:68)
   and [topos_pullbacks] (Structure/Topos.v:130), and hypothesis
   binders.
   None of those is a concrete inhabitant, so the headline is unaffected;
   the enumeration is corrected because it was offered as exhaustive.
   [Sets] had no pullbacks at all.  What it did have is [sets_char_pullback]
   (Instance/Sets/Classifier.v:226), and that is a different statement: it
   proves ONE particular square -- the classifying square of a given mono
   -- to be a pullback, it says nothing about arbitrary cospans, and it is
   stated over [Sets@{so sso}], one universe above the [Sets@{o so}] whose
   objects it is about.

   Nor did any concrete category carry the kernel pair.  [kernel_pair]
   (Structure/Regular.v:46) is [pullback f f]; the only in-tree constant
   built from it at a fixed category is [image_kernel_pair]
   (Structure/Regular/Factorization.v:128), and that sits under
   [Context (R : Regular C)] (:125), a class with no instance anywhere:
   searching [Regular] tree-wide, then discarding [RegularEpi], the
   [regular_*] field names and the von-Neumann-regularity vocabulary,
   leaves only [Require]s of Structure/Regular.v and that one binder.
   The [Instance/*/Regular.v] files are about the von Neumann regularity
   of ARROWS (Theory/Morphisms.v:336), a different notion sharing the
   word.

   THE DERIVATION ROUTE: MEASURED, AND NOT TAKEN

   Since jwiegley/category-theory#326 landed, [Sets] has had all the
   ingredients for a pullback to be read off a reduction:
   [Sets_Cartesian] (Instance/Sets/Cartesian.v:32), [Sets_HasEqualizers]
   (Adjunction/GAFT/Sets.v:175), and
   [HasPullbacks_of_Cartesian_HasEqualizers].  That route was tried before
   this file was written, and it produces an apex in the WRONG
   DESCRIPTION -- not an opaque one, a transparent one that unfolds to
   something else.  [Sets_HasEqualizers] is [Complete_HasEqualizers
   Sets_Complete], so its equalizer is the limit of the walking parallel
   pair as Instance/Sets/Complete.v:193 builds it, and with

     Definition Derived : @HasPullbacks Sets :=
       @HasPullbacks_of_Cartesian_HasEqualizers Sets _ Sets_HasEqualizers.
     Definition DerObj : Sets := Pull f g (@pullback Sets Derived _ _ _ f g).

   in scope, BOTH of the following elaborate as written:

     (* accepted: *)
     Definition derived_is_limit_obj :
       DerObj = Sets_limit_obj (APair (f ∘ exl) (g ∘ exr)) := eq_refl.
     (* rejected: *)
     Definition strict_obj : DerObj = sets_pb_obj f g := eq_refl.

   the second with "cannot unify "DerObj" and "sets_pb_obj f g"".  So the
   derived apex IS, on the nose, the setoid of COMPATIBLE FAMILIES over
   the walking parallel pair: a dependent function on [ParObj] paired with
   a constraint quantified over every arrow of [Parallel].  An element of
   it is not a pair, and the agreement condition is not one equation.
   Deliverable (B) IS the claim that this object is the relation setoid,
   and (D)'s comparison map and mediator are written on pairs, so both
   would have had to be conducted through that encoding.  Scope that
   honestly: (C)'s headline would NOT have been affected, since
   [equalizer_of_pullback] applies to any [IsPullback] whatever its apex
   -- only (C)'s elementwise readings would move.  The construction here
   is therefore DIRECT, and #326's reduction is consumed the other way
   round, in (C), to say what the directly-built pullback is as an
   equalizer.

   That measurement is NOT pinned in this file, and the reason is
   dependency weight rather than doubt: stating it needs
   [Adjunction/GAFT/Sets.v], which would put the whole GAFT closure behind
   every consumer of pullbacks in [Sets].  It belongs in a Test/ probe.
   The fragment above reproduces in a scratch file that requires, beyond
   this file's own imports, Instance/Sets/Complete.v, Instance/Parallel.v,
   Structure/Limit.v, Adjunction/GAFT.v and Adjunction/GAFT/Sets.v.

   A STALE NOTE CORRECTED

   The issue text behind this file says Riehl's "the pullback is the
   equalizer" is stated nowhere in the tree and is recorded as a known gap
   at Structure/Topos.v:23.  That is not what that file says now, and the
   correction runs in both directions.  Structure/Topos.v:23 says only
   that the topos class "deliberately do[es] not add equalizers", and
   :25-33 says in terms that the reduction and its converse "ARE
   formalized", naming [equalizer_of_pullback]
   (Structure/Pullback/Reduction.v:287).  So the GENERIC theorem exists
   and this file does not supply it.  What did not exist is any
   INSTANTIATION at a concrete category: searching [IsEqualizer] tree-wide
   turns up, outside Structure/ and Test/, only [matr_IsEqualizer_op]
   (Instance/Matr/Coequalizer.v:328), which is the opposite-category
   reading of a matrix COequalizer and not a pullback square at all.  (C)
   below is the first place a pullback in a named category is exhibited as
   an equalizer.

   WHAT IS BUILT

   (A) [sets_pb_obj f g] is the sub-setoid of the product carrier cut out
       by the agreement condition: elements are pairs [(p; w)] with
       [w : f (fst p) ≈ g (snd p)], and two are identified when their
       underlying pairs are -- the witness plays no part, the discipline
       Instance/Sets/Complete.v uses and there attributes to
       Instance/Sets/End.v.  With
       [sets_pb_fst], [sets_pb_snd] and the mediator [sets_pb_med] this
       gives [Sets_IsPullback], [Sets_Pullback] and the registered
       instance [Sets_HasPullbacks].  The mediator's agreement witness is
       the competing square's own commuting equation read at a point, so
       nothing is chosen and no quotient is formed.

   (B) [sets_ker f] is [sets_pb_obj f f], the relation setoid
       {(u, v) | f u ≈ f v}.  Structure/Regular.v's [kernel_pair] IS that
       object with those two projections, recorded by [eq_refl] in
       [sets_kernel_pair_obj], [sets_kernel_pair_fst] and
       [sets_kernel_pair_snd].  The equivalence-relation reading is given
       AS ARROWS, in the standard internal form: [sets_ker_refl] is the
       diagonal [a ~> R] splitting both projections, [sets_ker_sym] is the
       swap [R ~> R] exchanging them, and [sets_ker_trans] goes out of
       [sets_ker_comp], the object of composable pairs -- which is itself
       a pullback, of [sets_ker_snd] along [sets_ker_fst], recorded by
       [eq_refl] in [sets_ker_comp_is_pullback].  All six leg equations
       are proved.  No internal-equivalence-relation CLASS is inhabited,
       because the tree has none; the six equations are stated directly.

   (C) [sets_pullback_is_equalizer] is Riehl's statement: the agreement
       subset, with the pairing of its two projections, is an
       [IsEqualizer] of [f ∘ exl] and [g ∘ exr].  It is
       [equalizer_of_pullback] applied to (A) -- an application of #326's
       theorem, not a second proof -- and [sets_equalizer_is_pullback]
       runs the reduction back the other way.

   (E) Non-vacuity.  NOTE THE ORDER: this paragraph is narrated before (D)
       although the code runs (A)(B)(C)(D)(E), so the witnesses named here
       that belong to the preimage section -- [even_preimage],
       [choose_factors], [sets_preimage_criterion] and
       [constThree_does_not_factor] -- are forward references to the
       paragraph below.  [graph_even] is the pullback of [Nat.even] along the
       identity of [bool], so its agreement subset is the graph of
       [Nat.even]; two of its elements are exhibited, a third pair is
       shown excluded, and the mediator out of [NatSet] evaluates on
       closed input.  [sets_ker evenM] identifies 0 and 2, and
       [even_ker_not_diagonal] proves the relation is therefore NOT the
       diagonal; the symmetry and transitivity arrows are evaluated on
       it, [(0,2)] composing with [(2,4)] to give [(0,4)].
       [even_preimage] is the preimage of [{true}], with 4 in it and 3
       provably not; [choose_factors] factors a non-constant map through
       it, [sets_preimage_criterion] carries that factorization
       downstairs and the result evaluates, and
       [constThree_does_not_factor] refutes the other case.

   (D) [sets_preimage f S] is the preimage of a subset along f, and
       [sets_preimage_IsPullback] is Awodey's Example 5.9.  A subset is a
       [Type]-valued predicate on the carrier saturated under [≈]
       ([SubsetOf]); a SINGLE such subset stays at the universe of the
       carriers, and it is the setoid of ALL [Type]-valued subsets that
       must move up a level (Instance/Sets/Powerset.v's [Powerset_obj]),
       which is why that file is neither needed nor required here.  The
       elementwise criterion is [sets_preimage_criterion]: t factors
       through the preimage exactly when f ∘ t factors through the
       subset, an [iffT] whose two
       directions are genuine constructions (forward composes with the
       comparison map, backward transports a membership witness along the
       downstairs factorization).  [FactorsThrough] is a [sigT], so the
       factoring map is data.

   STRENGTHS, MEASURED STRICT-FIRST

   Closing by [eq_refl]:
     - [Sets_Pullback_obj]/[_fst]/[_snd]: the bundled [Pullback] record's
       apex and projections are the three constants of (A);
     - [sets_kernel_pair_obj]/[_fst]/[_snd] and
       [sets_ker_comp_is_pullback], as described in (B);
     - [sets_preimage_mem]: membership in the preimage IS membership
       downstream;
     - [even_med_is_ump]: the mediator that [ump_pullbacks] hands back at
       the concrete cospan of (E) is [sets_pb_med] on the nose.  SCOPE
       THIS ONE HONESTLY: it is listed under (E) but carries NO
       non-vacuity content, because the GENERAL statement -- the same
       equation at an arbitrary cospan, apex and commuting witness --
       also holds by [eq_refl] (measured).  So the concrete instance
       demonstrates nothing the general fact would not, and would hold at
       degenerate cospans too.  The general form is the one a consumer
       wants and it is NOT stated here; adding it is left open rather
       than slipped in;
     - [sets_equalizer_round_fst_pointwise]/[_snd_pointwise]: projecting
       out of the pairing recovers the projection POINTWISE on carriers;
     - the [Example]s of (E): each is either an element of an agreement
       subset exhibited with an [eq_refl] agreement witness, or an
       equation between carriers closed by [eq_refl].

   Holding only up to [≈], with the strict form refuted (each attempted
   before the [≈] form was accepted; the refutations are measured here and
   ALL THREE are pinned in Test/ProbeSetsPullback333.v -- an earlier
   revision pinned only two and left this first one guarded nowhere while
   calling it measured):
     - [sets_equalizer_round_fst]/[_snd] as MORPHISMS: the two
       [SetoidMorphism] records agree on their underlying functions (that
       is the pointwise [eq_refl] above) and differ in the rebuilt
       [proper_morphism] certificate, so
       [exl ∘ sets_pb_pair = sets_pb_fst f g := eq_refl] is rejected;
     - [sets_pb_pair_computes]: the equalizing map sends an element to its
       underlying pair only up to [≈], since [sets_pb_pair u] is
       [(fst `1 u, snd `1 u)] and stdlib [prod] has no definitional eta --
       [sets_pb_pair f g u = `1 u := eq_refl] is rejected.  This is the
       same absence of surjective pairing that
       Construction/Free/Quiver/Constructions.v records for [QuiverSwap].

   UNIVERSES, READ OFF THE CONSTRAINT BLOCKS

   [Sets_HasPullbacks@{u u0} : HasPullbacks@{u u0} Sets@{u0 u}] carries
   [u0 < u] -- which is [Sets]'s own declaration constraint -- together
   with bounds on the stdlib donors [Basics.compose], [Projections],
   [ID] and the distinct lowercase [projections] family ([u0 <=
   projections.u0], [u0 <= projections.u1]) -- FOUR, an earlier revision
   named three.  There is no identification and no [Set] anywhere.  The
   multi-object statements do identify universes, but only because their
   objects are objects of ONE [Sets]: [Sets_IsPullback] and
   [sets_pullback_is_equalizer] read [u = u1], [u0 = u2], [u0 = u4] --
   x, y and z living in one and the same [Sets] -- and the
   two-object [sets_preimage_IsPullback] reads [u = u1], [u0 = u2].
   [SubsetOf@{u u0 u1}] leaves the MEMBERSHIP universe [u0] free; it is
   forming [sub_obj] that bounds it by the carrier universe, and the
   bound is [u1 <= u0] in that constant's own block.  The concrete
   witnesses of (E) are polymorphic too -- [NatSet@{u u0}] has [u0 < u],
   five stdlib donor bounds and no identification -- because they are over
   [eq_Setoid] (Lib/Setoid.v:65), which is universe-polymorphic, rather
   than by resolving [eq_equivalence] at an unannotated binder.

   ZERO AXIOMS.  All 103 constants of this file report "Closed under the
   global context".  Enumerated as the 95 names the [.glob] records under
   [def], [prf], [inst], [proj] and [rec], plus the 7 [_obligation_]
   constants that [Print Module] lists and the [.glob] does not, plus
   [Build_SubsetOf], which appears in neither.

   WHAT IS NOT DELIVERED -- scoped to this file, no claim about the tree

     - The [Top] half of Mac Lane's Exercise 1 (the pullback of two
       continuous maps, with the subspace topology) is NOT built.  It is
       host-category-gated on jwiegley/category-theory#259 and is recorded
       here as the natural extension rather than as an obstruction: the
       carrier construction would be this one, and what is missing is the
       topology side.
     - No [Complete]-style packaging: nothing here relates
       [Sets_HasPullbacks] to [Sets_Complete] (Instance/Sets/Complete.v:193)
       or to [Sets_HasEqualizers], and in particular the pullback built
       here is NOT proved isomorphic to the derived one.  The two are
       isomorphic by [pullback_unique], but that composition is not
       performed and the comparison map is not named.
     - No [Regular Sets], no [HasCoequalizers]-based coequalizer of a
       kernel pair, and so no statement that a surjection is the
       coequalizer of its kernel pair.
     - No internal-equivalence-relation class, hence no theorem that
       [sets_ker] is one; (B) gives the six leg equations and stops.  No
       quotient by a kernel pair is formed and nothing here is related to
       Instance/Sets/Quotient.v.
     - Nothing about wide pullbacks, pullback pasting, or stability; those
       are Theory/Morphisms/Stability.v's, generically, and are not
       instantiated here.
     - [SubsetOf] is a local convenience, not a subobject theory: it is
       not related to Theory/Subobject.v, not shown to be the same as
       Instance/Sets/Powerset.v's subsets, and [sub_incl] is proved
       [Monic] but no converse (every mono is such an inclusion) is
       claimed.
     - The mediator of (D)'s pullback is not compared with (A)'s; the two
       constructions are independent, and no isomorphism between
       [sub_obj (sets_preimage f S)] and [sets_pb_obj f (sub_incl S)] is
       built.
     - No [Fail] probe of any kind lives here. *)

(* ====================================================================== *)
(** * (A) The agreement sub-setoid                                        *)

Section SetsPullback.

Context {x y z : Sets}.
Context (f : x ~{Sets}~> z) (g : y ~{Sets}~> z).

(* An element of the pullback is a pair of elements on which f and g
   agree.  The agreement witness is carried alongside the pair rather
   than quotiented away, exactly as the compatibility constraint is in
   Instance/Sets/Complete.v. *)
Definition sets_pb_carrier : Type :=
  { p : carrier x * carrier y & @equiv _ z (f (fst p)) (g (snd p)) }.

(* Two elements are identified when the underlying pairs are: the
   agreement witness plays no part. *)
Definition sets_pb_equiv : crelation sets_pb_carrier :=
  fun u v => (@equiv _ x (fst `1 u) (fst `1 v) *
              @equiv _ y (snd `1 u) (snd `1 v))%type.

Lemma sets_pb_equivalence : Equivalence sets_pb_equiv.
Proof.
  constructor.
  - intros u; split; reflexivity.
  - intros u v [H1 H2]; split; symmetry; assumption.
  - intros u v w [H1 H2] [K1 K2]; split.
    + transitivity (fst `1 v); assumption.
    + transitivity (snd `1 v); assumption.
Qed.

Definition sets_pb_obj : Sets :=
  {| carrier   := sets_pb_carrier
   ; is_setoid := {| equiv        := sets_pb_equiv
                   ; setoid_equiv := sets_pb_equivalence |} |}.

Program Definition sets_pb_fst : sets_pb_obj ~{Sets}~> x :=
  {| morphism := fun u => fst `1 u |}.
Next Obligation. intros u v H; exact (fst H). Qed.

Program Definition sets_pb_snd : sets_pb_obj ~{Sets}~> y :=
  {| morphism := fun u => snd `1 u |}.
Next Obligation. intros u v H; exact (snd H). Qed.

Lemma sets_pb_commutes : f ∘ sets_pb_fst ≈ g ∘ sets_pb_snd.
Proof. intros u; exact (`2 u). Qed.

(* The mediator out of a competing square: bundle the two legs at a
   point, the agreement witness being the competing square's own
   commuting equation read at that point. *)
Program Definition sets_pb_med {Q : Sets}
        (q1 : Q ~{Sets}~> x) (q2 : Q ~{Sets}~> y)
        (Hq : f ∘ q1 ≈ g ∘ q2) : Q ~{Sets}~> sets_pb_obj :=
  {| morphism := fun e => ((q1 e, q2 e); Hq e) |}.
Next Obligation.
  intros e e' H.
  exact (proper_morphism q1 e e' H, proper_morphism q2 e e' H).
Qed.

Definition Sets_IsPullback :
  IsPullback f g sets_pb_obj sets_pb_fst sets_pb_snd.
Proof.
  constructor.
  - exact sets_pb_commutes.
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + exact (sets_pb_med q1 q2 Hq).
    + split; intros e; reflexivity.
    + intros v [Hv1 Hv2] e; split; symmetry; [exact (Hv1 e)|exact (Hv2 e)].
Defined.

Definition Sets_Pullback : Pullback f g :=
  is_pullback_pullback Sets_IsPullback.

(* The bundled record's apex and projections are the three constants
   above, on the nose. *)
Definition Sets_Pullback_obj : Pull f g Sets_Pullback = sets_pb_obj := eq_refl.
Definition Sets_Pullback_fst :
  pullback_fst f g Sets_Pullback = sets_pb_fst := eq_refl.
Definition Sets_Pullback_snd :
  pullback_snd f g Sets_Pullback = sets_pb_snd := eq_refl.

End SetsPullback.

#[export] Instance Sets_HasPullbacks : HasPullbacks Sets :=
  {| pullback := @Sets_Pullback |}.

(* ====================================================================== *)
(** * (B) The kernel pair (Mac Lane §III.4 Exercise 6)                    *)

Section KernelPair.

Context {a b : Sets}.
Context (f : a ~{Sets}~> b).

(* The relation setoid {(u, v) | f u ≈ f v}, which is the agreement
   sub-setoid of (A) taken at the cospan (f, f). *)
Definition sets_ker : Sets := sets_pb_obj f f.

Definition sets_ker_fst : sets_ker ~{Sets}~> a := sets_pb_fst f f.
Definition sets_ker_snd : sets_ker ~{Sets}~> a := sets_pb_snd f f.

(* Structure/Regular.v's generic [kernel_pair] IS that relation setoid,
   with those two projections, on the nose. *)
Definition sets_kernel_pair_obj :
  Pull f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker := eq_refl.

Definition sets_kernel_pair_fst :
  pullback_fst f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker_fst
  := eq_refl.

Definition sets_kernel_pair_snd :
  pullback_snd f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker_snd
  := eq_refl.

(* Membership, both ways. *)
Definition sets_ker_pair (u v : carrier a) (H : @equiv _ b (f u) (f v)) :
  carrier sets_ker := ((u, v); H).

Lemma sets_ker_related (w : carrier sets_ker) :
  @equiv _ b (f (sets_ker_fst w)) (f (sets_ker_snd w)).
Proof. exact (`2 w). Qed.

(** ** The equivalence-relation laws, exhibited as arrows *)

(* Reflexivity: the diagonal a ~> R, splitting both projections. *)
Program Definition sets_ker_refl : a ~{Sets}~> sets_ker :=
  {| morphism := fun u => ((u, u); reflexivity (f u)) |}.
Next Obligation. intros u v H; exact (H, H). Qed.

Lemma sets_ker_refl_fst : sets_ker_fst ∘ sets_ker_refl ≈ id[a].
Proof. intros u; reflexivity. Qed.

Lemma sets_ker_refl_snd : sets_ker_snd ∘ sets_ker_refl ≈ id[a].
Proof. intros u; reflexivity. Qed.

(* Symmetry: the swap R ~> R, exchanging the two projections. *)
Program Definition sets_ker_sym : sets_ker ~{Sets}~> sets_ker :=
  {| morphism := fun w => ((snd `1 w, fst `1 w); symmetry (`2 w)) |}.
Next Obligation. intros w w' H; exact (snd H, fst H). Qed.

Lemma sets_ker_sym_fst : sets_ker_fst ∘ sets_ker_sym ≈ sets_ker_snd.
Proof. intros w; reflexivity. Qed.

Lemma sets_ker_sym_snd : sets_ker_snd ∘ sets_ker_sym ≈ sets_ker_fst.
Proof. intros w; reflexivity. Qed.

(* Transitivity needs the object of composable pairs, which is itself a
   pullback: the pullback of [sets_ker_snd] along [sets_ker_fst]. *)
Definition sets_ker_comp : Sets := sets_pb_obj sets_ker_snd sets_ker_fst.

Definition sets_ker_comp_is_pullback :
  Pull sets_ker_snd sets_ker_fst
       (@pullback Sets Sets_HasPullbacks _ _ _ sets_ker_snd sets_ker_fst)
  = sets_ker_comp := eq_refl.

Definition sets_ker_comp_fst : sets_ker_comp ~{Sets}~> sets_ker :=
  sets_pb_fst sets_ker_snd sets_ker_fst.
Definition sets_ker_comp_snd : sets_ker_comp ~{Sets}~> sets_ker :=
  sets_pb_snd sets_ker_snd sets_ker_fst.

Lemma sets_ker_trans_related (w : carrier sets_ker_comp) :
  @equiv _ b (f (fst `1 (fst `1 w))) (f (snd `1 (snd `1 w))).
Proof.
  transitivity (f (snd `1 (fst `1 w))).
  - exact (`2 (fst `1 w)).
  - transitivity (f (fst `1 (snd `1 w))).
    + exact (proper_morphism f _ _ (`2 w)).
    + exact (`2 (snd `1 w)).
Qed.

Program Definition sets_ker_trans : sets_ker_comp ~{Sets}~> sets_ker :=
  {| morphism := fun w => ((fst `1 (fst `1 w), snd `1 (snd `1 w));
                           sets_ker_trans_related w) |}.
Next Obligation. intros w w' H; exact (fst (fst H), snd (snd H)). Qed.

Lemma sets_ker_trans_fst :
  sets_ker_fst ∘ sets_ker_trans ≈ sets_ker_fst ∘ sets_ker_comp_fst.
Proof. intros w; reflexivity. Qed.

Lemma sets_ker_trans_snd :
  sets_ker_snd ∘ sets_ker_trans ≈ sets_ker_snd ∘ sets_ker_comp_snd.
Proof. intros w; reflexivity. Qed.

End KernelPair.

(* ====================================================================== *)
(** * (C) The pullback IS the equalizer (Riehl §3.2 Example 3.2.9)        *)

Section PullbackAsEqualizer.

Context {x y z : Sets}.
Context (f : x ~{Sets}~> z) (g : y ~{Sets}~> z).

(* The equalizing map into the product: the two projections paired. *)
Definition sets_pb_pair : sets_pb_obj f g ~{Sets}~> (x × y)%object :=
  (sets_pb_fst f g △ sets_pb_snd f g).

Definition sets_pullback_is_equalizer :
  IsEqualizer (f ∘ exl) (g ∘ exr) (sets_pb_obj f g) sets_pb_pair :=
  equalizer_of_pullback (Sets_IsPullback f g).

(* And back: reading that equalizer as a pullback through the same
   reduction returns the projections composed with the pairing. *)
Definition sets_equalizer_is_pullback :
  IsPullback f g (sets_pb_obj f g) (exl ∘ sets_pb_pair) (exr ∘ sets_pb_pair) :=
  pullback_of_equalizer f g sets_pullback_is_equalizer.

Lemma sets_equalizer_round_fst : exl ∘ sets_pb_pair ≈ sets_pb_fst f g.
Proof. intros u; reflexivity. Qed.

Lemma sets_equalizer_round_snd : exr ∘ sets_pb_pair ≈ sets_pb_snd f g.
Proof. intros u; reflexivity. Qed.

(* Measured strict-first: the round trip holds POINTWISE at Leibniz
   equality on the carriers, and only at `≈` as MORPHISMS -- the two
   [SetoidMorphism] records differ in their rebuilt [proper_morphism]
   certificate.  See the header for the refutation. *)
Example sets_equalizer_round_fst_pointwise (u : carrier (sets_pb_obj f g)) :
  (exl ∘ sets_pb_pair) u = sets_pb_fst f g u := eq_refl.

Example sets_equalizer_round_snd_pointwise (u : carrier (sets_pb_obj f g)) :
  (exr ∘ sets_pb_pair) u = sets_pb_snd f g u := eq_refl.

(* Elementwise: the equalizing map sends an element of the agreement
   subset to its underlying pair, and that pair equalizes the two
   composites. *)
Lemma sets_pb_pair_computes (u : carrier (sets_pb_obj f g)) :
  @equiv _ (x × y)%object (sets_pb_pair u) (`1 u).
Proof. split; reflexivity. Qed.

Lemma sets_pb_pair_equalizes (u : carrier (sets_pb_obj f g)) :
  @equiv _ z ((f ∘ exl) (sets_pb_pair u)) ((g ∘ exr) (sets_pb_pair u)).
Proof. exact (`2 u). Qed.

End PullbackAsEqualizer.

(* ====================================================================== *)
(** * (D) Pulling a subset back is taking the preimage (Awodey Ex. 5.9)   *)

(* A subset of a setoid B: a Type-valued predicate on its carrier that is
   saturated under `≈`.  A single subset stays at the universe of the
   carriers; it is the setoid of ALL subsets that must move up a level,
   and that object is not formed here (Instance/Sets/Powerset.v). *)
Record SubsetOf (B : Sets) : Type := {
  sub_mem : carrier B -> Type;
  sub_mem_resp : ∀ p q : carrier B, @equiv _ B p q -> sub_mem p -> sub_mem q
}.

Arguments sub_mem {B} _ _.
Arguments sub_mem_resp {B} _ {p q} _ _.

Section Subset.

Context {B : Sets}.
Context (S : SubsetOf B).

Lemma sub_obj_equivalence :
  Equivalence (fun u v : { p : carrier B & sub_mem S p } =>
                 @equiv _ B `1 u `1 v).
Proof.
  constructor.
  - intros u; reflexivity.
  - intros u v H; symmetry; exact H.
  - intros u v w H K; transitivity (`1 v); assumption.
Qed.

(* The subset as an object of [Sets]: elements of B together with a
   membership witness, compared by their underlying elements. *)
Definition sub_obj : Sets :=
  {| carrier   := { p : carrier B & sub_mem S p }
   ; is_setoid := {| equiv        := fun u v => @equiv _ B `1 u `1 v
                   ; setoid_equiv := sub_obj_equivalence |} |}.

(* CORRECTED, and the correction matters because the original named the
   wrong mechanism.  An earlier revision said "[Program] raises no
   obligation here -- instance resolution closes [proper_morphism] during
   elaboration -- which is the shape Instance/Sets/Products.v:409-424
   records as a universe-pinning hazard".  That is FALSE: the [Program]
   form DOES raise one, [sub_incl_obligation_1] (measured by elaborating
   it and reading [Print]).  Products.v:409-424 defines its hazard as the
   definition raising NO obligation AT ALL, so this site is not an
   instance of that shape and the transplanted sentence was wrong twice.
   What survives is the CONCLUSION, which is independently measured: both
   forms were
   elaborated side by side and print the same binder
   [sub_incl@{u u0 u1} : ∀ {B : obj[Sets@{u0 u}]}, ...] with a
   character-for-character identical constraint block, so the hand-supplied
   certificate below is uniformity, not a repair. *)
Definition sub_incl : sub_obj ~{Sets}~> B.
Proof.
  unshelve refine {| morphism := fun u => `1 u |}.
  intros u v H; exact H.
Defined.

Lemma sub_incl_Monic : Monic sub_incl.
Proof. constructor; intros Z u v H e; exact (H e). Qed.

End Subset.

Arguments sub_obj {B} _.
Arguments sub_incl {B} _.

(* Factoring a map through a given map, as data (the tree's ∃ is sigT,
   so the factoring map is data and nothing is chosen). *)
Definition FactorsThrough {Z W V : Sets} (m : W ~{Sets}~> V)
           (h : Z ~{Sets}~> V) : Type :=
  { k : Z ~{Sets}~> W & m ∘ k ≈ h }.

Section Preimage.

Context {A B : Sets}.
Context (f : A ~{Sets}~> B) (S : SubsetOf B).

(* The preimage {p | f p ∈ S}. *)
Definition sets_preimage : SubsetOf A.
Proof using All.
  unshelve refine {| sub_mem := fun p => sub_mem S (f p) |}.
  intros u v Huv Hm.
  exact (sub_mem_resp S (proper_morphism f u v Huv) Hm).
Defined.

(* Membership in the preimage IS membership downstream, definitionally. *)
Definition sets_preimage_mem (p : carrier A) :
  sub_mem sets_preimage p = sub_mem S (f p) := eq_refl.

(* The comparison over the cospan: an element of the preimage maps to its
   image, which carries the same membership witness. *)
Program Definition sets_preimage_over :
  sub_obj sets_preimage ~{Sets}~> sub_obj S :=
  {| morphism := fun u => (f `1 u; `2 u) |}.
Next Obligation. intros u v H; exact (proper_morphism f _ _ H). Qed.

(* The preimage square is a pullback. *)
Definition sets_preimage_IsPullback :
  IsPullback f (sub_incl S) (sub_obj sets_preimage)
             (sub_incl sets_preimage) sets_preimage_over.
Proof.
  constructor.
  - intros u; reflexivity.
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + unshelve refine {| morphism := fun e => (q1 e; _) |}.
      * exact (sub_mem_resp S (symmetry (Hq e)) (`2 (q2 e))).
      * intros e e' H; exact (proper_morphism q1 e e' H).
    + split; intros e; [reflexivity|exact (Hq e)].
    + intros v [Hv1 Hv2] e; symmetry; exact (Hv1 e).
Defined.

(** ** The elementwise criterion *)

(* Awodey's criterion: t factors through the preimage exactly when
   f ∘ t factors through the subset. *)
Lemma sets_preimage_criterion {Z : Sets} (t : Z ~{Sets}~> A) :
  FactorsThrough (sub_incl sets_preimage) t ↔
  FactorsThrough (sub_incl S) (f ∘ t).
Proof.
  split.
  - intros [k Hk].
    exists (sets_preimage_over ∘ k).
    intros e; exact (proper_morphism f _ _ (Hk e)).
  - intros [j Hj].
    unshelve refine (_; _).
    + unshelve refine {| morphism := fun e => (t e; _) |}.
      * exact (sub_mem_resp S (Hj e) (`2 (j e))).
      * intros e e' H; exact (proper_morphism t e e' H).
    + intros e; reflexivity.
Defined.

End Preimage.

(* ====================================================================== *)
(** * (E) Non-vacuity: pullbacks in [Sets] that compute                   *)

(* Two discrete setoids, over [eq_Setoid] of Lib/Setoid.v so that `≈` is
   Leibniz equality on the carriers and the equations below are genuine
   computations rather than instances of a coarse relation. *)
Definition NatSet : Sets :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Definition BoolSet : Sets :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition evenM : NatSet ~{Sets}~> BoolSet.
Proof.
  unshelve refine {| morphism := Nat.even |};
  try (intros n m H; rewrite H; reflexivity).
Defined.

Definition idB : BoolSet ~{Sets}~> BoolSet.
Proof.
  unshelve refine {| morphism := fun c : bool => c |};
  try (intros c c' H; exact H).
Defined.

(** ** A cospan whose agreement subset is the graph of [Nat.even] *)

(* The pullback of [evenM] along [idB]: pairs (n, c) with even n = c. *)
Definition graph_even : Sets := sets_pb_obj evenM idB.

Example graph_even_3 : carrier graph_even := ((3%nat, false); eq_refl).
Example graph_even_4 : carrier graph_even := ((4%nat, true); eq_refl).

Example graph_even_3_fst :
  sets_pb_fst evenM idB graph_even_3 = 3%nat := eq_refl.
Example graph_even_3_snd :
  sets_pb_snd evenM idB graph_even_3 = false := eq_refl.

(* (3, true) is NOT in the agreement subset: no witness can be supplied. *)
Lemma graph_even_excludes_3_true :
  @equiv _ BoolSet (evenM 3%nat) (idB true) → False.
Proof. discriminate. Qed.

(** ** The mediator computes *)

Lemma even_square : evenM ∘ id[NatSet] ≈ idB ∘ evenM.
Proof. intros n; reflexivity. Qed.

Definition even_med : NatSet ~{Sets}~> graph_even :=
  sets_pb_med evenM idB id[NatSet] evenM even_square.

(* The mediator produced by the universal property IS that map. *)
Definition even_med_is_ump :
  unique_obj (ump_pullbacks evenM idB (Sets_Pullback evenM idB)
                            NatSet id[NatSet] evenM even_square)
  = even_med := eq_refl.

Example even_med_5_fst :
  sets_pb_fst evenM idB (even_med 5%nat) = 5%nat := eq_refl.
Example even_med_5_snd :
  sets_pb_snd evenM idB (even_med 5%nat) = false := eq_refl.
Example even_med_6_snd :
  sets_pb_snd evenM idB (even_med 6%nat) = true := eq_refl.

(** ** The kernel pair of [evenM] is not the diagonal *)

Example even_ker_02 : carrier (sets_ker evenM) := ((0%nat, 2%nat); eq_refl).

Example even_ker_02_fst : sets_ker_fst evenM even_ker_02 = 0%nat := eq_refl.
Example even_ker_02_snd : sets_ker_snd evenM even_ker_02 = 2%nat := eq_refl.

(* So the relation genuinely identifies two distinct elements. *)
Lemma even_ker_not_diagonal :
  @equiv _ NatSet (sets_ker_fst evenM even_ker_02)
                  (sets_ker_snd evenM even_ker_02) → False.
Proof. discriminate. Qed.

(* The symmetry arrow moves it, and the reflexivity arrow does not land
   on it. *)
Example even_ker_sym_02_fst :
  sets_ker_fst evenM (sets_ker_sym evenM even_ker_02) = 2%nat := eq_refl.

Example even_ker_refl_0_snd :
  sets_ker_snd evenM (sets_ker_refl evenM 0%nat) = 0%nat := eq_refl.

(* And the transitivity arrow composes (0,2) with (2,4) to give (0,4). *)
Example even_ker_24 : carrier (sets_ker evenM) := ((2%nat, 4%nat); eq_refl).

Example even_ker_composable : carrier (sets_ker_comp evenM) :=
  ((even_ker_02, even_ker_24); eq_refl).

Example even_ker_trans_fst :
  sets_ker_fst evenM (sets_ker_trans evenM even_ker_composable) = 0%nat
  := eq_refl.

Example even_ker_trans_snd :
  sets_ker_snd evenM (sets_ker_trans evenM even_ker_composable) = 4%nat
  := eq_refl.

(** ** The preimage of a subset *)

Definition TrueSub : SubsetOf BoolSet.
Proof.
  refine (Build_SubsetOf BoolSet (fun c : bool => c = true) _).
  intros u v Huv Hm; rewrite <- Huv; exact Hm.
Defined.

(* The preimage of {true} along [evenM] is the set of even naturals. *)
Definition even_preimage : SubsetOf NatSet := sets_preimage evenM TrueSub.

Example even_preimage_4 : carrier (sub_obj even_preimage) := (4%nat; eq_refl).

Lemma even_preimage_excludes_3 : sub_mem even_preimage 3%nat → False.
Proof. discriminate. Qed.

(* A non-constant map into the preimage, and the criterion carrying it
   downstairs. *)
Definition chooseM : BoolSet ~{Sets}~> NatSet.
Proof.
  unshelve refine {| morphism := fun c : bool => if c then 4%nat else 2%nat |};
  try (intros c c' H; rewrite H; reflexivity).
Defined.

Definition choose_factors :
  FactorsThrough (sub_incl even_preimage) chooseM.
Proof.
  unshelve refine (_; _).
  - unshelve refine {| morphism := fun c : bool => (chooseM c; _) |}.
    all: try (intros c c' H; rewrite H; reflexivity).
    all: try (destruct c; reflexivity).
  - intros c; reflexivity.
Defined.

Definition choose_factors_downstairs :
  FactorsThrough (sub_incl TrueSub) (evenM ∘ chooseM) :=
  fst (sets_preimage_criterion evenM TrueSub chooseM) choose_factors.

Example choose_downstairs_true :
  `1 (`1 choose_factors_downstairs true) = true := eq_refl.

Example choose_downstairs_false :
  `1 (`1 choose_factors_downstairs false) = true := eq_refl.

(* The criterion is not vacuous in the negative direction either: the
   constant 3 does not factor through the preimage. *)
Definition constThree : BoolSet ~{Sets}~> NatSet.
Proof.
  unshelve refine {| morphism := fun _ : bool => 3%nat |};
  try (intros c c' H; reflexivity).
Defined.

Lemma constThree_does_not_factor :
  FactorsThrough (sub_incl even_preimage) constThree → False.
Proof.
  intros [k Hk].
  pose proof (`2 (k true)) as Hm.
  pose proof (Hk true) as He.
  simpl in He, Hm.
  rewrite He in Hm.
  discriminate.
Qed.
