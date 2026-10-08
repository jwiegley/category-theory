Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.

Generalizable All Variables.

(** * Quotient groups as coequalizers, split under the forgetful functor *)

(* Book:   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
           §VI.6 "Split Coequalizers", book p. 150 (PDF p. 159), the
           example after the Corollary, item maclane:VI.6:remark2, read
           from the page image
   nLab:   https://ncatlab.org/nlab/show/split+coequalizer
   nLab:   https://ncatlab.org/nlab/show/quotient+group
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_group
   Wikipedia: https://en.wikipedia.org/wiki/Semidirect_product

   WHAT THE BOOK SAYS.  "Let N ◁ G be any normal subgroup of G and form
   the semidirect product G ×₀ N, which has elements the pairs ⟨x, n⟩ for
   x ∈ G, n ∈ N with the (evidently associative) multiplication
   ⟨x, n⟩⟨y, m⟩ = ⟨xy, (y⁻¹ny)m⟩.  Then G ×₀ N ⇉ G → G/N is a fork, where
   p is the usual projection to the quotient group G/N, while
   ∂₀⟨x, n⟩ = x, ∂₁⟨x, n⟩ = xn.  Moreover, in this fork p is clearly the
   coequalizer of ∂₀ and ∂₁.  This fork is not in general split, but if
   we apply the standard forgetful functor U: Grp→Set, the resulting fork
   in Set is split.  Take s to be a function sending each coset (element
   of G/N) to a representative element in G, while tx = ⟨x, x⁻¹(spx)⟩."

   WHAT IS HERE.
     - [SemidirectGrp N] is G ×₀ N: pairs ⟨x, n⟩ whose n carries its
       membership witness, compared by the setoid and [PropEquiv] of
       Instance/Grp.v's direct product [Grp_product G (SubgroupGrp N)]
       ([SemidirectGrp_setoid], at [eq_refl]) and multiplied by the
       book's formula ([sdp_mul]).  Its unit ⟨e, e⟩ and inverse
       ⟨x⁻¹, x n⁻¹ x⁻¹⟩, which the book does not print, are [sdp_unit]
       and [sdp_inv].  ∂₀ and ∂₁ are [semidirect_d0] and [semidirect_d1].
     - With no hypothesis: p coforks the pair ([semidirect_cofork]); a
       homomorphism coforks it exactly when it kills N
       ([semidirect_cofork_iff_kills]); p is its coequalizer
       ([quot_proj_IsCoequalizer]), the descent being
       Instance/Grp/Quotient.v's mediator [quot_med], the universal
       property of #313; the U-image is a fork ([semidirect_U_cofork]);
       and the pair is reflexive, x ↦ ⟨x, e⟩ being a common section in
       Grp ([semidirect_refl], [semidirect_reflexive]).
     - The splitting after U, as a biconditional.  A [Transversal N] is
       a choice of a representative in each coset: a map of setoids out
       of U(G/N), with the UNTRUNCATED witness [quot_rel N (s a) a].
       [Grp_U_split_iff_transversal]: the U-image pair has a split
       coequalizer if and only if N has a transversal.  One way is the
       book's splitting, [transversal_split], with e = U p, s the
       transversal and t x = ⟨x, x⁻¹(s p x)⟩ ([transversal_t]); the
       other, [split_transversal], reads the transversal s ∘ e off ANY
       split coequalizer of the U-image pair, its t certifying the
       cosets.  So, given a transversal, U carries p to a coequalizer
       ([transversal_U_IsCoequalizer]), indeed to an absolute one
       ([transversal_U_AbsoluteCoequalizer], Structure/Coequalizer/
       Absolute.v).
     - Whether U preserves p at all, as a biconditional:
       [Grp_U_IsCoequalizer_iff_untruncates], U p is a coequalizer in
       Sets if and only if the coset relation untruncates
       ([CosetUntruncates]: inhabited (quot_rel N a b) → quot_rel N a b),
       the test object being the untruncated quotient
       ([quot_rel_object]); a transversal untruncates
       ([transversal_untruncates]), and so does the untruncation
       principle ∀ S, inhabited S → S at N's membership level
       ([choice_untruncates]).
     - UNCONDITIONAL ALTERNATIVE, attempted and delivered: U corestricted
       to PropSets carries p to a coequalizer (not a split one).  Every
       group carries [grp_prop], so [Grp_Forget] factors through
       Instance/Sets/Propositional/Full.v's [PropSets] by its
       [PropSets_lift] ([Grp_ForgetP]), a factorization Full.v lists as
       not built.  In [PropSets] every test object's `≈` is
       propositional, the truncated coset witness eliminates into it
       (Lib/Setoid/Propositional.v's [pequiv_elim_inhabited]), and U p
       is a coequalizer there with no hypothesis
       ([PropSets_quot_IsCoequalizer]).  In [Sets] the coequalizer of
       the U-image pair is, with no hypothesis, the UNTRUNCATED quotient
       ([quot_rel_IsCoequalizer]), of which U(G/N) is the truncation: U p
       is a coequalizer in [Sets] exactly when that truncation inverts,
       which is the biconditional above.
     - Split in Grp itself, as a biconditional:
       [Grp_split_iff_hom_transversal], the pair has a split coequalizer
       in Grp if and only if p has a homomorphic section with
       untruncated coset witnesses ([HomTransversal]), t being then a
       homomorphism ([hom_transversal_t]).
     - Witnesses.  Transversals at N = G ([TotalNS_transversal], the
       unit), at N trivial ([TrivialNS_transversal], the identity) and
       at A₃ ◁ S₃ ([A3_transversal], (i, b) ↦ (rot0, b), over
       Instance/Grp/TwoFunctors.v's decidable S₃); the last is a
       homomorphism, so S₃/A₃ splits in Grp ([S3_A3_Grp_split]).  The
       book's "not in general split", at a witness:
       [Z4_two_not_split_in_Grp], for Z/4 over {0, 2} ([Z4], [Z4_two],
       built here): a homomorphic section sends 1 to an odd u (its coset
       witness), hence 2 = 1 + 1 to u + u = 2, while 2 ≡ 0 sends it to
       the image of 0, which is 0.  [Z4] is new because the tree has no
       Z/4 (a grep of the .v files for z4 or Z/4 finds this file and its
       probe only); Z/2, of which it has three copies (Instance/Grp.v's
       [Z2], Instance/Grp/Epi.v's [GrpTwo], Instance/Grp/Galois.v's
       [GalZ2]), projects onto its quotients by its trivial and its total
       subgroup with homomorphic sections, the identity and the unit map;
       and [Int_Plus_Grp] (Construction/Deloop/Functors.v) and [Z3_Grp]
       (Structure/Groupoid.v) are objects of Construction/Deloop.v's
       [GrpObject] record, not of Instance/Grp.v's.
     - The taboos below, at N_P and N_S ◁ Z/2 ([NP], [NS]).

   THE CONSTRUCTIVE QUESTION.  The book's s chooses a representative in
   each coset.  U(G/N) is G's carrier under the TRUNCATION of quot_rel
   (Instance/Grp/Quotient.v's [quot_setoid]), so a section of U p is a
   map constant on cosets up to G's `≈`, and t, whose second component
   is an element of N, needs its coset witness untruncated: that pair is
   a [Transversal].  Asked of every N, the splitting is a constructive
   taboo.  At N_P ◁ Z/2, over Instance/Grp.v's [Z2] ([NP]: all of Z/2
   when P holds and trivial when it does not, its membership the Prop
   [or P (a = false)]), a transversal is a decision of P
   ([NP_transversal_decides], [NP_decides_transversal]), so Mac Lane's
   unconditional "the resulting fork in Set is split" decides every
   proposition, P + (P → False) ([U_split_taboo]), and the mere
   existence of a transversal gives the Prop [or P (P → False)]
   ([NP_inhabited_transversal_lem]).  Instance/Sets/Regular.v runs this
   argument for the splitting principle of [Sets]: [sets_coarse] is bool
   coarsened by a proposition, a splitting of [sets_coarsen] decides it
   ([sets_coarsen_retraction_dec]), and [blanket_splitting_entails_LEM]
   concludes; its header records that Coq's intuitionistic logic proves
   neither conclusion.  Untruncation does not imply a transversal
   constructively: it holds at N_P outright ([NP_untruncates], so U p is
   a coequalizer in Sets there, [NP_U_IsCoequalizer]), while a
   transversal decides P ([untruncation_transversal_taboo]).
   Untruncation for every N is the untruncation principle
   ∀ S, inhabited S → S at the membership level: the principle gives it
   ([choice_untruncates]), and at N_S ◁ Z/2 ([NS], membership
   (a = 0) + S for a type S) untruncation is a choice out of
   [inhabited S] ([NS_untruncates_chooses]), so U's preservation of p
   at every N_S gives the principle ([U_preserves_untruncates]).
   Instance/Sets/Propositional/Full.v's [untr_of_choice] and
   [choice_of_untr] make the principle interderivable, level for level,
   with Instance/Sets/Classifier/OneLevel.v's [Untruncate]
   (Test/ProbeQuotient479.v's C19 and C20 compose them at a membership
   level below the carrier).

   MONADICITY.  Any crude-monadicity route for groups over Sets needs
   untruncation: the pair being reflexive, U's preservation of reflexive
   coequalizers, hypothesis 2 of Monad/Monadicity/Crude.v, entails the
   untruncation principle at Grp's carrier level
   ([Grp_Forget_crude_untruncates]).  Factoring the algebraic forgetful
   functors through [PropSets], where U preserves these coequalizers
   with no hypothesis, is a follow-up issue (#1369).  Crude.v costs
   this file eleven modules of closure ([Print Libraries]: 95 without
   it, 106 with it), all already in the closure of Instance/Mon/
   Presentation.v, which requires Crude.v itself.

   THE RING TWIN.  Instance/Rng/Coequalizer.v repeats this file's
   Sets-level part for ideals: the transversal and its splittings, the
   untruncation biconditional and the two unconditional coequalizers.
   The twins are deliberate.  What they share depends only on a setoid
   with a [PropEquiv], a [Type]-valued equivalence coarser than its `≈`
   and a kernel-pair presentation of that relation, and a layer over
   those would redo both files' universe annotations; it is not built,
   so its size is not measured.  Instance/Variety's setoid algebras are
   no route, building an [EqSignature] carrying
   [functional_extensionality_dep] (docs/AXIOMS.md).  The generic parts
   are stated once, in tree: [quot_rel_object] and [quot_rel_proj] ARE
   Instance/Sets/Quotient.v's [SetsQuotient] and [sets_quot_proj] at G's
   setoid, [quot_rel_IsCoequalizer]'s descent is its [sets_quot_med]
   with [sets_quot_med_commutes] and [sets_quot_med_unique], and the
   [PropSets] descent is [pequiv_elim_inhabited].  Instance/Sets/
   Coequalizer.v's [sets_rel_IsCoequalizer] (Mac Lane §III.3 Exercise
   5) coequalizes the two projections of [SetsRelObj], not this pair,
   so it does not give [quot_rel_IsCoequalizer] by instantiation.

   STRENGTHS.  At [eq_refl]: the multiplication is the book's formula
   ([sdp_mul_fst], [sdp_mul_snd]); ∂₀ and ∂₁ ([semidirect_d0_fun],
   [semidirect_d1_fun]); the descent IS [quot_med]
   ([quot_proj_IsCoequalizer_desc]); the splitting's object, e, s and
   both components of t, the second x⁻¹(s p x)
   ([transversal_split_obj], [transversal_split_e],
   [transversal_split_s], [transversal_split_t_fst],
   [transversal_split_t_snd]); law 3 of each splitting, ∂₀ (t x) = x,
   pointwise ([transversal_split_law3], [hom_transversal_Grp_split_law3]);
   the round trip transversal → splitting → transversal
   ([transversal_round_trip]); the S₃ values ([A3_transversal_fun],
   [S3_A3_Grp_split_s]).  At ≈ only: the group laws of G ×₀ N and laws
   1, 2 and 4 of each splitting.  Law 4, ∂₁ (t x) = x(x⁻¹(s p x))
   against s p x, is refused at [eq_refl] (Test/ProbeQuotient479.v, R1),
   the cancellation being a law of a variable G.  The cofork in G/N is a
   truncation by construction.

   UNIVERSES, by [About] on each of the 93 gated names (a script).  The
   construction binds G : GrpObject@{u u0 u1} with its three levels
   free.  The rest binds G : GrpObject@{p p p} in the binder, the shape
   of [Grp@{u p}]'s objects, and N : NormalSubgroup@{u p p p} G: the two
   sections declare [p] and write the binder out because a section's
   free G put the identification in the constraint blocks as two
   equations ("u = u0", "u = u1", measured on a draft's [semidirect_d0]
   and [semidirect_d1]), and the eleven readbacks of the pair and its
   splittings outside them write it with the bound,
   @{p u + | u <= p +}: with bare binders, minimization identified u
   with p in each (measured on [semidirect_d0_fun] and eight others),
   where the probe's C17 now accepts [transversal_split_e] below the
   carrier.  No block carries an equation.  Every name generic in N
   that mentions the pair, a splitting of it, t or the untruncated
   quotient carries "u <= p", N's membership level at or below the
   carrier level, first at [semidirect_d0]: an element of G ×₀ N
   carries a membership witness, and the pair lives in [Grp@{_ p}].
   [Transversal], [CosetUntruncates], [transversal_untruncates],
   [choice_untruncates] and [HomTransversal] carry no such bound, nor
   does [SemidirectGrp] (the probe's R2 refuses ∂₀ at a membership
   level above the carrier; C5 and C14 accept the other two there).
   The names at a particular subgroup take its levels:
   [NP_U_IsCoequalizer], [U_split_taboo] and
   [U_preserves_untruncates] put the membership level of N_P or N_S at
   Z/2's carrier level, which ∂₀ allows.  [quot_rel_object] is annotated
   at [SetoidObject@{p p}], whose relation level it reaches by
   "u <= p"; unannotated it was a [SetoidObject@{p u}], and
   [quot_rel_proj], which reads it as an object of [Sets], carried
   "p = u" (measured); built on [SetsQuotient] and [sets_quot_proj] at
   [grp_setoid G], both keep their signatures.  [Grp_ForgetP] keeps the
   object levels of [Grp] and [PropSets] apart, as [Grp_Forget] keeps
   those of [Grp] and [Sets], [PropSets_quot_IsCoequalizer] names them
   (go, so), and [NP_decides_transversal] names Z/2's level: left to
   Rocq, minimization had identified the two object levels in each of
   the first two and put the third at [Set].  [Grp_ForgetP@{go p so}]
   is the one explicit universe instance this file writes of a
   constant of its own, whose binder is closed at three levels (three
   on Coq 8.19.2 and 8.20.1 as well); every other one is of a
   constant from outside this development.  [Set] appears only as
   [Grp]'s own [Set < u] on its object level and [PropSets]'s
   [Set < so], as z4's own sort ([z4 : Set], and [z4_rec] over
   z4 → Set), and in the five S₃ names, which inherit
   Instance/Grp/TwoFunctors.v's [S3@{u} : GrpObject@{u Set Set}] (R3
   refuses the S₃/A₃ splitting in [Grp@{u p}] above [Set]);
   [Z4@{p} : GrpObject@{p p p}] lifts z4 to every level, and its
   refutation is accepted above [Set] (C6).
   [transversal_U_AbsoluteCoequalizer] names its target levels xo xh
   ("p <= xh"): left to Rocq, minimization set the target's hom level
   to p, as Absolute.v records for [split_coequalizer_absolute], whose
   further level above xh it inherits.  On Coq 8.19.2 and 8.20.1
   ([About] in a build of the files' closure and the probe under each)
   each of the 93 names binds as many levels as on Rocq 9.1.1, no block
   carries an equation, and [Set] occurs in the same seven types, the
   five S₃ names, [z4] and [z4_rec].

   STALE PREMISES, dated from gh.  The issue (filed 2026-07-23) says the
   tree has no category Grp or Rng and no normal-subgroup, semidirect
   or quotient machinery, CMon being the only algebraic category among
   Instance/: accurate when filed (Theory/Algebra/Monoid/Hom.v's [Mon],
   from PR #191, merged 2026-07-07, is not under Instance/), stale since
   PR #1053 (merged 2026-08-12, #255, Instance/Grp.v), PR #1091 (merged
   2026-08-14, #257, Instance/Rng.v) and PR #1166 (merged 2026-08-19,
   #313, Instance/Grp/Quotient.v).  No semidirect product of
   groups was built before this file: [git grep -i semidirect] over the
   other .v files finds eleven lines, each in a comment, and S₃'s
   "semidirect presentation" in TwoFunctors.v is a multiplication on
   rot × bool, not a construction.

   NOT DELIVERED.  A transversal, or the untruncation of the coset
   relation, for every N: the taboos above.  The identification of
   G ×₀ N with the kernel pair of p, ⟨x, n⟩ ↦ (x, xn).  The section's
   Exercise 2 (contractible pairs).  A choice of coequalizers in Grp from
   this construction: only the pairs (∂₀, ∂₁) are coequalized here, as
   Instance/Grp/Quotient/Colimit.v coequalizes the pairs (f, 0).  The
   shared Sets-level layer of the ring twin (above). *)

(** ** Two cancellations, right-associated *)

Lemma grp_mul_cancel_inv (G : GrpObject) (a b : carrier G) :
  grp_mul G a (grp_mul G (grp_inv G a) b) ≈ b.
Proof.
  rewrite <- grp_mul_assoc, grp_mul_inv_r.
  apply grp_mul_unit_l.
Qed.

Lemma grp_inv_mul_cancel (G : GrpObject) (a b : carrier G) :
  grp_mul G (grp_inv G a) (grp_mul G a b) ≈ b.
Proof.
  rewrite <- grp_mul_assoc, grp_mul_inv_l.
  apply grp_mul_unit_l.
Qed.

Section Semidirect.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

(* Conjugation by an inverse, y⁻¹ n y, as Mac Lane writes it: the normality
   field conjugates t n t⁻¹, here at t = y⁻¹. *)
Lemma ns_conj_inv (y n : carrier G) :
  sub_mem N n →
  sub_mem N (grp_mul G (grp_mul G (grp_inv G y) n) y).
Proof.
  intro Hn.
  apply (sub_at N (a := grp_mul G (grp_mul G (grp_inv G y) n)
                          (grp_inv G (grp_inv G y)))).
  - rewrite (grp_inv_inv G y); reflexivity.
  - exact (ns_conj N (grp_inv G y) n Hn).
Qed.

(** ** Mac Lane's semidirect product G ×₀ N *)

Definition sdp_carrier : Type := (carrier G * sub_carrier N)%type.

(* ⟨x, n⟩⟨y, m⟩ = ⟨xy, (y⁻¹ n y) m⟩. *)
Definition sdp_mul (p q : sdp_carrier) : sdp_carrier :=
  (grp_mul G (fst p) (fst q),
   @existT (carrier G) (sub_mem N)
     (grp_mul G (grp_mul G (grp_mul G (grp_inv G (fst q)) (`1 (snd p)))
                   (fst q))
        (`1 (snd q)))
     (sub_mul N _ _ (ns_conj_inv (fst q) _ (`2 (snd p))) (`2 (snd q)))).

Definition sdp_unit : sdp_carrier :=
  (grp_unit G, @existT (carrier G) (sub_mem N) (grp_unit G) (sub_unit N)).

(* ⟨x, n⟩⁻¹ = ⟨x⁻¹, x n⁻¹ x⁻¹⟩. *)
Definition sdp_inv (p : sdp_carrier) : sdp_carrier :=
  (grp_inv G (fst p),
   @existT (carrier G) (sub_mem N)
     (grp_mul G (grp_mul G (fst p) (grp_inv G (`1 (snd p))))
        (grp_inv G (fst p)))
     (ns_conj N (fst p) _ (sub_inv N _ (`2 (snd p))))).

Definition SemidirectGrp : GrpObject.
Proof using G N.
  unshelve notypeclasses refine {|
    grp_setoid := grp_setoid (Grp_product G (SubgroupGrp N));
    grp_unit := sdp_unit;
    grp_mul := sdp_mul;
    grp_inv := sdp_inv;
    grp_prop := grp_prop (Grp_product G (SubgroupGrp N))
  |}.
  - intros [x [n Hn]] [x' [n' Hn']] [Hx Hnn] [y [m Hm]] [y' [m' Hm']] [Hy Hmm].
    simpl in *.
    split; simpl.
    + now rewrite Hx, Hy.
    + now rewrite Hnn, Hy, Hmm.
  - intros [x [n Hn]] [y [m Hm]] [z [k Hk]].
    split; simpl.
    + apply grp_mul_assoc.
    + rewrite (grp_inv_mul G y z).
      rewrite !grp_mul_assoc.
      rewrite (grp_mul_cancel_inv G z).
      reflexivity.
  - intros [x [n Hn]].
    split; simpl.
    + apply grp_mul_unit_l.
    + rewrite !grp_mul_assoc.
      rewrite grp_mul_unit_l.
      apply grp_inv_mul_cancel.
  - intros [x [n Hn]].
    split; simpl.
    + apply grp_mul_inv_l.
    + rewrite !grp_mul_assoc.
      rewrite (grp_inv_mul_cancel G x).
      rewrite (grp_inv_mul_cancel G x).
      apply grp_mul_inv_l.
Defined.

End Semidirect.

(* U corestricted to the propositional setoids: every group carries
   [grp_prop], so [Grp_Forget] factors through Instance/Sets/Propositional/
   Full.v's [PropSets] by its [PropSets_lift], a factorization that file
   lists as not built.  The binder keeps the object levels of [Grp] and of
   [PropSets] apart, as [Grp_Forget] keeps those of [Grp] and [Sets]. *)
Definition Grp_ForgetP@{u p so | p < so +} : Grp@{u p} ⟶ PropSets@{p so} :=
  PropSets_lift Grp_Forget (fun G => grp_prop G).

(* The pair, the coequalizer and the splitting live in [Grp], whose objects
   are [GrpObject@{p p p}]; the binder says so, rather than leaving the
   identification to the constraint block. *)

Section SemidirectPair.

Universe p.

Context {G : GrpObject@{p p p}}.
Context (N : NormalSubgroup G).

(** ** The parallel pair ∂₀, ∂₁ : G ×₀ N ⇉ G *)

(* ∂₀⟨x, n⟩ = x. *)
Definition semidirect_d0 : SemidirectGrp N ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (@Build_GrpHom' (SemidirectGrp N) G
       {| morphism := fun p : sdp_carrier N => fst p |} _).
  - intros p q Hpq; exact (fst Hpq).
  - intros p q; reflexivity.
Defined.

(* ∂₁⟨x, n⟩ = xn. *)
Definition semidirect_d1 : SemidirectGrp N ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (@Build_GrpHom' (SemidirectGrp N) G
       {| morphism := fun p : sdp_carrier N => grp_mul G (fst p) (`1 (snd p)) |}
       _).
  - intros [x [n Hn]] [y [m Hm]] [Hxy Hnm]; simpl in *.
    now rewrite Hxy, Hnm.
  - intros [x [n Hn]] [y [m Hm]]; simpl.
    rewrite !grp_mul_assoc.
    rewrite (grp_mul_cancel_inv G y).
    reflexivity.
Defined.

(** ** The projection coforks the pair, and is its coequalizer *)

(* x and xn are congruent, with the witness untruncated. *)
Lemma semidirect_quot_rel (x n : carrier G) :
  sub_mem N n → quot_rel N x (grp_mul G x n).
Proof.
  intro Hn; unfold quot_rel.
  apply (sub_at N (a := grp_mul G (grp_mul G x (grp_inv G n)) (grp_inv G x))).
  - rewrite (grp_inv_mul G x n).
    rewrite grp_mul_assoc.
    reflexivity.
  - exact (ns_conj N x _ (sub_inv N _ Hn)).
Qed.

Lemma semidirect_cofork :
  quot_proj N ∘ semidirect_d0 ≈ quot_proj N ∘ semidirect_d1.
Proof.
  intros [x [n Hn]]; simpl.
  constructor; exact (semidirect_quot_rel x n Hn).
Qed.

Lemma semidirect_cofork_kills {K : GrpObject} (h : G ~{Grp}~> K) :
  h ∘ semidirect_d0 ≈ h ∘ semidirect_d1 →
  ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K.
Proof.
  intros Hh a Ha.
  pose proof (Hh (grp_unit G, @existT (carrier G) (sub_mem N) a Ha)) as E.
  simpl in E.
  transitivity (grp_map h (grp_mul G (grp_unit G) a)).
  - apply (proper_morphism (grp_map h)).
    symmetry; apply grp_mul_unit_l.
  - rewrite <- E.
    apply (grp_map_unit h).
Qed.

Lemma kills_semidirect_cofork {K : GrpObject} (h : G ~{Grp}~> K) :
  (∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K) →
  h ∘ semidirect_d0 ≈ h ∘ semidirect_d1.
Proof.
  intros Hk [x [n Hn]]; simpl.
  rewrite (grp_map_mul h), (Hk n Hn).
  symmetry; apply grp_mul_unit_r.
Qed.

Definition semidirect_cofork_iff_kills {K : GrpObject} (h : G ~{Grp}~> K) :
  h ∘ semidirect_d0 ≈ h ∘ semidirect_d1
    ↔ (∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K) :=
  (semidirect_cofork_kills h, kills_semidirect_cofork h).

(* The descent is the quotient's own mediator [quot_med], at the element of
   [Kills N] the cofork provides. *)
Definition quot_proj_IsCoequalizer :
  IsCoequalizer semidirect_d0 semidirect_d1 (QuotientGrp N) (quot_proj N).
Proof.
  unshelve econstructor.
  - exact semidirect_cofork.
  - intros K h Hh.
    exact {| unique_obj :=
               quot_med N (existT _ h (semidirect_cofork_kills h Hh));
             unique_property :=
               quot_med_commutes N (existT _ h (semidirect_cofork_kills h Hh));
             uniqueness :=
               quot_med_unique N (existT _ h (semidirect_cofork_kills h Hh)) |}.
Defined.

(* The U-image is a fork, with no hypothesis: the image of the cofork. *)
Lemma semidirect_U_cofork :
  fmap[Grp_Forget] (quot_proj N) ∘ fmap[Grp_Forget] semidirect_d0
    ≈ fmap[Grp_Forget] (quot_proj N) ∘ fmap[Grp_Forget] semidirect_d1.
Proof. intro p; exact (semidirect_cofork p). Qed.

(* The pair is reflexive: x ↦ ⟨x, e⟩ is a homomorphism that both ∂₀ and
   ∂₁ retract. *)
Definition semidirect_refl : G ~{Grp}~> SemidirectGrp N.
Proof.
  unshelve notypeclasses refine
    (@Build_GrpHom' G (SemidirectGrp N)
       {| morphism := fun x : carrier G =>
            (x, @existT (carrier G) (sub_mem N) (grp_unit G) (sub_unit N))
          : carrier (SemidirectGrp N) |} _).
  - intros x y Hxy; split; simpl; [ exact Hxy | reflexivity ].
  - intros x y; split; simpl; [ reflexivity |].
    rewrite !grp_mul_unit_r.
    symmetry; apply grp_mul_inv_l.
Defined.

Definition semidirect_reflexive : ReflexivePair semidirect_d0 semidirect_d1.
Proof.
  exists semidirect_refl.
  - intro x; simpl; reflexivity.
  - intro x; simpl; apply grp_mul_unit_r.
Defined.

(** ** Transversals, and the splitting after the forgetful functor *)

(* A transversal of N: a map choosing in each coset a representative,
   read as a map of setoids out of U(G/N) (so constant on cosets, up to
   G's `≈`), together with an UNTRUNCATED witness that the representative
   lies in the coset it represents. *)
Record Transversal := {
  transversal_map :
    fobj[Grp_Forget] (QuotientGrp N) ~{Sets}~> fobj[Grp_Forget] G;
  transversal_coset : ∀ a : carrier G, quot_rel N (transversal_map a) a
}.

(* The coset witness, conjugated into the orientation Mac Lane's t needs:
   x⁻¹ (s x) ∈ N. *)
Lemma transversal_coset_inv (T : Transversal) (x : carrier G) :
  sub_mem N (grp_mul G (grp_inv G x) (transversal_map T x)).
Proof.
  apply (sub_at N (a := grp_mul G (grp_mul G (grp_inv G x)
                                      (grp_mul G (transversal_map T x)
                                         (grp_inv G x)))
                          (grp_inv G (grp_inv G x)))).
  - rewrite !grp_mul_assoc.
    rewrite (grp_mul_inv_r G (grp_inv G x)).
    rewrite grp_mul_unit_r.
    reflexivity.
  - exact (ns_conj N (grp_inv G x) _ (transversal_coset T x)).
Qed.

(* Mac Lane's t x = ⟨x, x⁻¹(s p x)⟩. *)
Definition transversal_t (T : Transversal) :
  fobj[Grp_Forget] G ~{Sets}~> fobj[Grp_Forget] (SemidirectGrp N).
Proof.
  unshelve refine {| morphism := fun x : carrier G =>
    (x, @existT (carrier G) (sub_mem N)
          (grp_mul G (grp_inv G x)
             (transversal_map T (grp_map (quot_proj N) x)))
          (transversal_coset_inv T x)) |}.
  intros x y Hxy; split; simpl.
  - exact Hxy.
  - apply grp_mul_respects.
    + exact (grp_inv_respects_law G _ _ Hxy).
    + apply (proper_morphism (transversal_map T)).
      exact (proper_morphism (grp_map (quot_proj N)) _ _ Hxy).
Defined.

(* From a transversal, the U-image fork is split, with e = U p. *)
Definition transversal_split (T : Transversal) :
  SplitCoequalizer (fmap[Grp_Forget] semidirect_d0)
                   (fmap[Grp_Forget] semidirect_d1).
Proof.
  unshelve refine
    {| scoeq_obj := fobj[Grp_Forget] (QuotientGrp N)
     ; scoeq_e   := fmap[Grp_Forget] (quot_proj N)
     ; scoeq_s   := transversal_map T
     ; scoeq_t   := transversal_t T |}.
  - exact semidirect_U_cofork.
  - intro a; simpl.
    constructor; exact (transversal_coset T a).
  - intro x; simpl; reflexivity.
  - intro x; simpl.
    apply grp_mul_cancel_inv.
Defined.

(* Any map out of U G that coforks the U-image pair is constant on cosets,
   given the coset witness untruncated: a ~ b is read off the element
   ⟨b, b⁻¹ a⟩ of G ×₀ N. *)
Lemma U_cofork_descends {Z : obj[Sets]} (h : fobj[Grp_Forget] G ~{Sets}~> Z)
  (Hh : h ∘ fmap[Grp_Forget] semidirect_d0 ≈ h ∘ fmap[Grp_Forget] semidirect_d1)
  (a b : carrier G) :
  quot_rel N a b → h a ≈ h b.
Proof.
  intro Hab.
  assert (Hm : sub_mem N (grp_mul G (grp_inv G b) a)).
  { apply (sub_at N (a := grp_mul G (grp_mul G (grp_inv G b)
                                       (grp_mul G a (grp_inv G b)))
                           (grp_inv G (grp_inv G b)))).
    - rewrite !grp_mul_assoc.
      rewrite (grp_mul_inv_r G (grp_inv G b)).
      rewrite grp_mul_unit_r.
      reflexivity.
    - exact (ns_conj N (grp_inv G b) _ Hab). }
  pose proof (Hh (b, @existT (carrier G) (sub_mem N) _ Hm)) as E.
  simpl in E.
  transitivity (h (grp_mul G b (grp_mul G (grp_inv G b) a))).
  - apply (proper_morphism h).
    symmetry; apply grp_mul_cancel_inv.
  - symmetry; exact E.
Qed.

(* Conversely, ANY split coequalizer of the U-image pair yields a
   transversal: s ∘ e chooses the representatives, and t certifies them. *)

Definition split_transversal
  (S : SplitCoequalizer (fmap[Grp_Forget] semidirect_d0)
                        (fmap[Grp_Forget] semidirect_d1)) : Transversal.
Proof.
  unshelve refine
    {| transversal_map :=
         {| morphism := fun a : carrier G => scoeq_s S (scoeq_e S a) |} |}.
  - intros a b Hab.
    apply (@pequiv_to _ _ (grp_prop G)).
    change (inhabited (quot_rel N a b)) in Hab.
    destruct Hab as [Hab].
    apply (@pequiv_from _ _ (grp_prop G)).
    apply (proper_morphism (scoeq_s S)).
    exact (U_cofork_descends (scoeq_e S) (scoeq_law1 S) a b Hab).
  - intro a; simpl.
    pose proof (scoeq_law3 S a) as E3.
    pose proof (scoeq_law4 S a) as E4.
    simpl in E3, E4.
    destruct (scoeq_t S a) as [x' [n Hn]]; simpl in E3, E4.
    unfold quot_rel.
    apply (sub_at N (a := grp_mul G (grp_mul G a n) (grp_inv G a))).
    + rewrite <- E4, E3.
      reflexivity.
    + exact (ns_conj N a n Hn).
Defined.

(* Mac Lane's claim, made exact: the U-image of the pair has a split
   coequalizer if and only if N has a transversal. *)
Definition Grp_U_split_iff_transversal :
  SplitCoequalizer (fmap[Grp_Forget] semidirect_d0)
                   (fmap[Grp_Forget] semidirect_d1) ↔ Transversal :=
  (split_transversal, transversal_split).

(* Hence, given a transversal, U carries the coequalizer p to a
   coequalizer, indeed to an absolute one. *)
Definition transversal_U_IsCoequalizer (T : Transversal) :
  IsCoequalizer (fmap[Grp_Forget] semidirect_d0)
    (fmap[Grp_Forget] semidirect_d1)
    (fobj[Grp_Forget] (QuotientGrp N)) (fmap[Grp_Forget] (quot_proj N)) :=
  split_coequalizer_is_coequalizer _ _ (transversal_split T).

Definition transversal_U_AbsoluteCoequalizer@{xo xh +} (T : Transversal) :
  AbsoluteCoequalizer@{_ _ xo xh _} (fmap[Grp_Forget] semidirect_d0)
    (fmap[Grp_Forget] semidirect_d1)
    (fobj[Grp_Forget] (QuotientGrp N)) (fmap[Grp_Forget] (quot_proj N)) :=
  split_coequalizer_absolute (transversal_split T).

(** ** Whether U preserves the coequalizer: exactly when cosets untruncate *)

(* U(G/N) compares by the TRUNCATED relation; a coequalizer in Sets must
   descend into setoids whose `≈` need not be propositional, and the test
   case is the untruncated quotient itself. *)
Definition CosetUntruncates : Type :=
  ∀ a b : carrier G, inhabited (quot_rel N a b) → quot_rel N a b.

(* The untruncated quotient is Instance/Sets/Quotient.v's [SetsQuotient] of
   G's setoid by [quot_rel], and its projection is [sets_quot_proj]. *)
Definition quot_rel_object : SetoidObject@{p p} :=
  SetsQuotient (grp_setoid G) (quot_rel N)
    {| Equivalence_Reflexive := quot_rel_refl N
     ; Equivalence_Symmetric := quot_rel_sym N
     ; Equivalence_Transitive := quot_rel_trans N |}.

Definition quot_rel_proj : fobj[Grp_Forget] G ~{Sets}~> quot_rel_object :=
  sets_quot_proj (grp_setoid G) (quot_rel N) _ (quot_rel_of_equiv N).

Lemma quot_rel_proj_cofork :
  quot_rel_proj ∘ fmap[Grp_Forget] semidirect_d0
    ≈ quot_rel_proj ∘ fmap[Grp_Forget] semidirect_d1.
Proof. intros [x [n Hn]]; exact (semidirect_quot_rel x n Hn). Qed.

(* With no hypothesis, the coequalizer in Sets of the U-image pair is the
   UNTRUNCATED quotient: the descent is Instance/Sets/Quotient.v's mediator
   [sets_quot_med] at the map's [U_cofork_descends]. *)
Definition quot_rel_IsCoequalizer :
  IsCoequalizer (fmap[Grp_Forget] semidirect_d0)
    (fmap[Grp_Forget] semidirect_d1) quot_rel_object quot_rel_proj.
Proof.
  unshelve econstructor.
  - exact quot_rel_proj_cofork.
  - intros Z h Hh.
    exact {| unique_obj :=
               sets_quot_med (quot_rel N) _
                 (existT _ h (U_cofork_descends h Hh));
             unique_property :=
               sets_quot_med_commutes (quot_rel N) _ (quot_rel_of_equiv N)
                 (existT _ h (U_cofork_descends h Hh));
             uniqueness :=
               sets_quot_med_unique (quot_rel N) _ (quot_rel_of_equiv N)
                 (existT _ h (U_cofork_descends h Hh)) |}.
Defined.

Lemma U_IsCoequalizer_untruncates
  (E : IsCoequalizer (fmap[Grp_Forget] semidirect_d0)
         (fmap[Grp_Forget] semidirect_d1)
         (fobj[Grp_Forget] (QuotientGrp N))
         (fmap[Grp_Forget] (quot_proj N))) :
  CosetUntruncates.
Proof.
  intros a b Hab.
  pose (D := coeq_desc E quot_rel_proj quot_rel_proj_cofork).
  pose proof (unique_property D) as Hu.
  pose proof (proper_morphism (unique_obj D) a b Hab) as Hab'.
  apply (quot_rel_trans N a (unique_obj D a)).
  - apply quot_rel_sym; exact (Hu a).
  - apply (quot_rel_trans N _ (unique_obj D b)); [ exact Hab' | exact (Hu b) ].
Qed.

Definition untruncates_U_IsCoequalizer (D : CosetUntruncates) :
  IsCoequalizer (fmap[Grp_Forget] semidirect_d0)
    (fmap[Grp_Forget] semidirect_d1)
    (fobj[Grp_Forget] (QuotientGrp N)) (fmap[Grp_Forget] (quot_proj N)).
Proof.
  unshelve econstructor.
  - exact semidirect_U_cofork.
  - intros Z h Hh.
    unshelve eapply Build_Unique.
    + refine {| morphism := fun a : carrier G => h a |}.
      intros a b Hab.
      exact (U_cofork_descends h Hh a b (D a b Hab)).
    + intro x; reflexivity.
    + intros v Hv x; symmetry; exact (Hv x).
Defined.

Definition Grp_U_IsCoequalizer_iff_untruncates :
  IsCoequalizer (fmap[Grp_Forget] semidirect_d0)
    (fmap[Grp_Forget] semidirect_d1)
    (fobj[Grp_Forget] (QuotientGrp N)) (fmap[Grp_Forget] (quot_proj N))
    ↔ CosetUntruncates :=
  (U_IsCoequalizer_untruncates, untruncates_U_IsCoequalizer).

(* A transversal untruncates the cosets, directly: a ~ s a ≈ s b ~ b. *)
Lemma transversal_untruncates (T : Transversal) : CosetUntruncates.
Proof.
  intros a b Hab.
  assert (Hs : transversal_map T a ≈ transversal_map T b)
    by exact (proper_morphism (transversal_map T) a b Hab).
  apply (quot_rel_trans N a (transversal_map T a)).
  - apply quot_rel_sym; exact (transversal_coset T a).
  - apply (quot_rel_trans N _ (transversal_map T b)).
    + exact (quot_rel_of_equiv N _ _ Hs).
    + exact (transversal_coset T b).
Qed.

(* So does the untruncation principle, at N's membership level. *)
Definition choice_untruncates
  (C : ∀ S : Type, inhabited S → S) : CosetUntruncates :=
  fun a b w => C _ w.

(** ** Unconditionally: U into the propositional setoids preserves p *)

(* In [PropSets] every test object's `≈` is propositional, so the
   truncated coset witness eliminates into it ([pequiv_elim_inhabited]):
   U corestricted to [PropSets] carries p to a coequalizer, with no
   hypothesis.  It is not a split one: the splitting is the taboo below.
   The binder names the object levels of [Grp] and [PropSets], which
   minimization had identified. *)
Definition PropSets_quot_IsCoequalizer@{go so +} :
  IsCoequalizer (fmap[Grp_ForgetP@{go p so}] semidirect_d0)
    (fmap[Grp_ForgetP@{go p so}] semidirect_d1)
    (fobj[Grp_ForgetP@{go p so}] (QuotientGrp N))
    (fmap[Grp_ForgetP@{go p so}] (quot_proj N)).
Proof.
  unshelve econstructor.
  - exact semidirect_U_cofork.
  - intros Z h Hh.
    unshelve eapply Build_Unique.
    + unshelve eexists; [ | exact I ].
      unshelve refine (@Build_SetoidMorphism _ _ _ _
                         (fun a : carrier G => projT1 h a) _).
      intros a b Hab.
      apply (@pequiv_elim_inhabited _ _ (projT2 Z)).
      change (inhabited (quot_rel N a b)) in Hab.
      destruct Hab as [Hab].
      constructor.
      exact (U_cofork_descends (projT1 h) Hh a b Hab).
    + intro x; reflexivity.
    + intros v Hv x; symmetry; exact (Hv x).
Defined.

End SemidirectPair.

Arguments transversal_map {G N} _.
Arguments transversal_coset {G N} _ _.

(** ** Readbacks *)

Example sdp_mul_fst {G : GrpObject} (N : NormalSubgroup G)
  (p q : carrier (SemidirectGrp N)) :
  fst (grp_mul (SemidirectGrp N) p q) = grp_mul G (fst p) (fst q) := eq_refl.

Example sdp_mul_snd {G : GrpObject} (N : NormalSubgroup G)
  (p q : carrier (SemidirectGrp N)) :
  `1 (snd (grp_mul (SemidirectGrp N) p q))
    = grp_mul G (grp_mul G (grp_mul G (grp_inv G (fst q)) (`1 (snd p)))
                   (fst q))
        (`1 (snd q)) := eq_refl.

(* G ×₀ N is compared exactly as the direct product G × N. *)
Example SemidirectGrp_setoid {G : GrpObject} (N : NormalSubgroup G) :
  grp_setoid (SemidirectGrp N) = grp_setoid (Grp_product G (SubgroupGrp N))
  := eq_refl.

(* The readbacks of the pair bind N's membership level u apart from the
   carrier level p, with the pair's own bound, as the section constants
   do; left to minimization, the bare binders identified the two. *)

Example semidirect_d0_fun@{p u + | u <= p +} {G : GrpObject@{p p p}}
  (N : NormalSubgroup@{u p p p} G) (x : carrier (SemidirectGrp N)) :
  grp_map (semidirect_d0 N) x = fst x := eq_refl.

Example semidirect_d1_fun@{p u + | u <= p +} {G : GrpObject@{p p p}}
  (N : NormalSubgroup@{u p p p} G) (x : carrier (SemidirectGrp N)) :
  grp_map (semidirect_d1 N) x = grp_mul G (fst x) (`1 (snd x)) := eq_refl.

Example quot_proj_IsCoequalizer_desc@{p u + | u <= p +}
  {G K : GrpObject@{p p p}} (N : NormalSubgroup@{u p p p} G)
  (h : G ~{Grp}~> K)
  (Hh : h ∘ semidirect_d0 N ≈ h ∘ semidirect_d1 N) :
  unique_obj (coeq_desc (quot_proj_IsCoequalizer N) h Hh)
    = quot_med N (existT _ h (semidirect_cofork_kills N h Hh)) := eq_refl.

Example transversal_split_obj@{p u + | u <= p +} {G : GrpObject@{p p p}}
  {N : NormalSubgroup@{u p p p} G} (T : Transversal N) :
  scoeq_obj (transversal_split N T) = fobj[Grp_Forget] (QuotientGrp N)
  := eq_refl.

Example transversal_split_e@{p u + | u <= p +} {G : GrpObject@{p p p}}
  {N : NormalSubgroup@{u p p p} G} (T : Transversal N) :
  scoeq_e (transversal_split N T) = fmap[Grp_Forget] (quot_proj N) := eq_refl.

Example transversal_split_s@{p u + | u <= p +} {G : GrpObject@{p p p}}
  {N : NormalSubgroup@{u p p p} G} (T : Transversal N) :
  scoeq_s (transversal_split N T) = transversal_map T := eq_refl.

Example transversal_split_t_fst@{p u + | u <= p +} {G : GrpObject@{p p p}}
  {N : NormalSubgroup@{u p p p} G} (T : Transversal N) (x : carrier G) :
  fst (scoeq_t (transversal_split N T) x) = x := eq_refl.

Example transversal_split_t_snd@{p u + | u <= p +} {G : GrpObject@{p p p}}
  {N : NormalSubgroup@{u p p p} G} (T : Transversal N) (x : carrier G) :
  `1 (snd (scoeq_t (transversal_split N T) x))
    = grp_mul G (grp_inv G x) (transversal_map T (grp_map (quot_proj N) x))
  := eq_refl.

(* Law 3 of the splitting, ∂₀ ∘ t = 1, holds pointwise by conversion. *)
Example transversal_split_law3@{p u + | u <= p +} {G : GrpObject@{p p p}}
  {N : NormalSubgroup@{u p p p} G} (T : Transversal N) (x : carrier G) :
  grp_map (semidirect_d0 N) (scoeq_t (transversal_split N T) x) = x
  := eq_refl.

(* The round trip transversal → splitting → transversal returns the same
   choice of representatives. *)
Example transversal_round_trip@{p u + | u <= p +} {G : GrpObject@{p p p}}
  {N : NormalSubgroup@{u p p p} G} (T : Transversal N) (a : carrier G) :
  transversal_map (split_transversal N (transversal_split N T)) a
    = transversal_map T a := eq_refl.

(** ** Split in Grp itself: exactly when p has a homomorphic section *)

Section SplitInGrp.

Universe p.

Context {G : GrpObject@{p p p}}.
Context (N : NormalSubgroup G).

(* A homomorphic transversal: a section of p in Grp, with the untruncated
   witness that s a lies in the coset of a. *)
Definition HomTransversal : Type :=
  { s : QuotientGrp N ~{Grp}~> G
  & ∀ a : carrier G, quot_rel N (grp_map s a) a }.

(* Its underlying transversal. *)
Definition hom_transversal_transversal (H : HomTransversal) : Transversal N :=
  {| transversal_map := fmap[Grp_Forget] (`1 H)
   ; transversal_coset := `2 H |}.

(* t is a homomorphism as soon as s is. *)
Lemma hom_transversal_t_mul (H : HomTransversal) (x y : carrier G) :
  transversal_t N (hom_transversal_transversal H) (grp_mul G x y)
    ≈ grp_mul (SemidirectGrp N)
        (transversal_t N (hom_transversal_transversal H) x)
        (transversal_t N (hom_transversal_transversal H) y).
Proof.
  split; simpl.
  - reflexivity.
  - transitivity (grp_mul G (grp_inv G (grp_mul G x y))
                    (grp_mul G (grp_map (`1 H) x) (grp_map (`1 H) y))).
    + apply grp_mul_respects; [ reflexivity | exact (grp_map_mul (`1 H) x y) ].
    + rewrite (grp_inv_mul G x y).
      rewrite !grp_mul_assoc.
      rewrite (grp_mul_cancel_inv G y).
      reflexivity.
Qed.

Definition hom_transversal_t (H : HomTransversal) :
  G ~{Grp}~> SemidirectGrp N :=
  @Build_GrpHom' G (SemidirectGrp N)
    (transversal_t N (hom_transversal_transversal H))
    (hom_transversal_t_mul H).

Definition hom_transversal_Grp_split (H : HomTransversal) :
  SplitCoequalizer (semidirect_d0 N) (semidirect_d1 N).
Proof.
  unshelve refine
    (@Build_SplitCoequalizer Grp _ _ (semidirect_d0 N) (semidirect_d1 N)
       (QuotientGrp N) (quot_proj N) (`1 H) (hom_transversal_t H) _ _ _ _).
  - exact (semidirect_cofork N).
  - intro a; simpl.
    constructor; exact (`2 H a).
  - intro x; simpl; reflexivity.
  - intro x; simpl.
    apply grp_mul_cancel_inv.
Defined.

(* Conversely, a split coequalizer in Grp splits after U, and the
   transversal [split_transversal] reads off it is s ∘ e, a composite of
   homomorphisms. *)
Definition Grp_split_hom_transversal
  (S : SplitCoequalizer (semidirect_d0 N) (semidirect_d1 N)) :
  HomTransversal.
Proof.
  pose (T := split_transversal N (functor_preserves_split Grp_Forget _ _ S)).
  unshelve eexists.
  - unshelve refine (@Build_GrpHom' (QuotientGrp N) G (transversal_map T) _).
    intros a b; simpl.
    transitivity (grp_map (scoeq_s S)
                    (grp_mul (scoeq_obj S) (grp_map (scoeq_e S) a)
                       (grp_map (scoeq_e S) b))).
    + apply (proper_morphism (grp_map (scoeq_s S))).
      apply (grp_map_mul (scoeq_e S)).
    + apply (grp_map_mul (scoeq_s S)).
  - exact (transversal_coset T).
Defined.

Definition Grp_split_iff_hom_transversal :
  SplitCoequalizer (semidirect_d0 N) (semidirect_d1 N) ↔ HomTransversal :=
  (Grp_split_hom_transversal, hom_transversal_Grp_split).

End SplitInGrp.

(* Its law 3 holds pointwise by conversion, t being the same map. *)
Example hom_transversal_Grp_split_law3@{p u + | u <= p +}
  {G : GrpObject@{p p p}} {N : NormalSubgroup@{u p p p} G}
  (H : HomTransversal N) (x : carrier G) :
  grp_map (semidirect_d0 N)
    (grp_map (scoeq_t (hom_transversal_Grp_split N H)) x) = x := eq_refl.

(** ** Witnesses *)

(* N = G: every coset is G, represented by the unit. *)
Definition TotalNS_transversal (G : GrpObject) : Transversal (TotalNS G).
Proof.
  unshelve refine
    (@Build_Transversal G (TotalNS G)
       {| morphism := fun _ : carrier G => grp_unit G |} _).
  - intros a b _; reflexivity.
  - intro a; exact ttt.
Defined.

(* N trivial: every element represents its own coset. *)
Definition TrivialNS_transversal (G : GrpObject) : Transversal (TrivialNS G).
Proof.
  unshelve refine
    (@Build_Transversal G (TrivialNS G)
       {| morphism := fun a : carrier G => a |} _).
  - intros a b Hab.
    apply (@pequiv_to _ _ (grp_prop G)).
    change (inhabited (quot_rel (TrivialNS G) a b)) in Hab.
    destruct Hab as [Hab].
    apply (@pequiv_from _ _ (grp_prop G)).
    exact (fst (quot_trivial_iff G a b) Hab).
  - intro a; exact (grp_mul_inv_r G a).
Defined.

(* A3 in S3: the reflection part alone, (i, b) ↦ (rot0, b). *)
Definition A3_transversal : Transversal A3.
Proof.
  unshelve refine
    (@Build_Transversal S3 A3
       {| morphism := fun a : carrier S3 => ((rot0, snd a) : carrier S3) |} _).
  - intros [i b] [j c] Hab.
    change (inhabited (quot_rel A3 (i, b) (j, c))) in Hab.
    change ((rot0, b) = (rot0, c)).
    destruct Hab as [Hab].
    destruct i, j, b, c; simpl in Hab; try discriminate; reflexivity.
  - intros [i b]; destruct i, b; reflexivity.
Defined.

(* It is a homomorphism, so S3/A3 splits in Grp itself. *)
Definition A3_hom_transversal : HomTransversal A3.
Proof.
  unshelve eexists.
  - unshelve refine
      (@Build_GrpHom' (QuotientGrp A3) S3 (transversal_map A3_transversal) _).
    intros [i b] [j c]; destruct i, j, b, c; reflexivity.
  - exact (transversal_coset A3_transversal).
Defined.

Definition S3_A3_Grp_split :
  SplitCoequalizer (semidirect_d0 A3) (semidirect_d1 A3) :=
  hom_transversal_Grp_split A3 A3_hom_transversal.

(** ** A fork that is not split in Grp: Z/4 over 2Z/4 *)

Inductive z4 : Set := z4_0 | z4_1 | z4_2 | z4_3.

Definition z4_add (a b : z4) : z4 :=
  match a, b with
  | z4_0, b => b
  | a, z4_0 => a
  | z4_1, z4_1 => z4_2 | z4_1, z4_2 => z4_3 | z4_1, z4_3 => z4_0
  | z4_2, z4_1 => z4_3 | z4_2, z4_2 => z4_0 | z4_2, z4_3 => z4_1
  | z4_3, z4_1 => z4_0 | z4_3, z4_2 => z4_1 | z4_3, z4_3 => z4_2
  end.

Definition z4_neg (a : z4) : z4 :=
  match a with
  | z4_0 => z4_0 | z4_1 => z4_3 | z4_2 => z4_2 | z4_3 => z4_1
  end.

Definition Z4@{p} : GrpObject@{p p p}.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := z4 ; is_setoid := eq_Setoid@{p} z4 |};
    grp_unit := z4_0;
    grp_mul  := z4_add;
    grp_inv  := z4_neg;
    grp_prop := eq_PropEquiv@{p} z4
  |}.
  - intros x y Hxy u v Huv; simpl in *; subst; reflexivity.
  - intros [] [] []; reflexivity.
  - intros []; reflexivity.
  - intros []; reflexivity.
Defined.

Definition z4_even (a : z4) : bool :=
  match a with z4_0 | z4_2 => true | _ => false end.

Definition Z4_two : NormalSubgroup Z4.
Proof.
  unshelve refine
    {| ns_sub := {| sub_mem := fun a : carrier Z4 => z4_even a = true |} |}.
  - intros a b Hab Ha; simpl in *; subst; exact Ha.
  - reflexivity.
  - intros [] [] Ha Hb; simpl in *; try discriminate; reflexivity.
  - intros [] Ha; simpl in *; try discriminate; reflexivity.
  - intros [] [] Ha; simpl in *; try discriminate; reflexivity.
Defined.

(* A homomorphic section would send 1 to an odd element u (its coset
   witness), hence 2 = 1 + 1 to u + u = 2, while 2 ≡ 0 forces it to the
   image of 0, which is 0. *)
Theorem Z4_two_not_split_in_Grp :
  SplitCoequalizer (semidirect_d0 Z4_two) (semidirect_d1 Z4_two) → False.
Proof.
  intro S.
  destruct (Grp_split_hom_transversal Z4_two S) as [s Hs].
  pose proof (Hs z4_1) as H1.
  pose proof (grp_map_mul s z4_0 z4_0) as H00.
  pose proof (grp_map_mul s z4_1 z4_1) as H11.
  assert (H20 : grp_map s z4_2 ≈ grp_map s z4_0).
  { apply (proper_morphism (grp_map s)).
    constructor; reflexivity. }
  revert H1 H00 H11 H20.
  simpl.
  generalize (grp_map s z4_0) (grp_map s z4_1) (grp_map s z4_2).
  intros v0 v1 v2 H1 H00 H11 H20.
  destruct v0, v1, v2; simpl in *; discriminate.
Qed.

(** ** Readbacks of the witnesses *)

Example A3_transversal_fun (a : carrier S3) :
  transversal_map A3_transversal a = (rot0, snd a) := eq_refl.

Example S3_A3_Grp_split_s (a : carrier S3) :
  grp_map (scoeq_s S3_A3_Grp_split) a = (rot0, snd a) := eq_refl.

(** ** Constructive taboos: the splitting, and untruncation for every N *)

(* N_P ◁ Z/2, over Instance/Grp.v's [Z2]: all of Z/2 when P holds and
   trivial when it does not, with the Prop-valued membership P or a = 0.
   It is written [or], not [∨], which Lib/Foundation.v makes the type
   [sum]: with it the untruncation at N_P would not hold outright. *)
Definition NP (P : Prop) : NormalSubgroup Z2.
Proof.
  unshelve refine
    {| ns_sub := {| sub_mem := fun a : carrier Z2 => or P (a = false) |} |}.
  - intros a b Hab Ha; simpl in *; subst; exact Ha.
  - right; reflexivity.
  - intros a b Ha Hb; simpl in *.
    destruct Ha as [Ha|Ha]; [ left; exact Ha |].
    destruct Hb as [Hb|Hb]; [ left; exact Hb |].
    right; subst; reflexivity.
  - intros a Ha; simpl in *; exact Ha.
  - intros t a Ha; simpl in *.
    destruct Ha as [Ha|Ha]; [ left; exact Ha |].
    right; subst; destruct t; reflexivity.
Defined.

(* The coset relation at N_P is already a proposition: it untruncates
   outright, so U carries p to a coequalizer in Sets there. *)
Lemma NP_untruncates (P : Prop) : CosetUntruncates (NP P).
Proof. intros a b H; unfold quot_rel; simpl; destruct H as [H]; exact H. Qed.

Definition NP_U_IsCoequalizer (P : Prop) :
  IsCoequalizer (fmap[Grp_Forget] (semidirect_d0 (NP P)))
    (fmap[Grp_Forget] (semidirect_d1 (NP P)))
    (fobj[Grp_Forget] (QuotientGrp (NP P)))
    (fmap[Grp_Forget] (quot_proj (NP P))) :=
  untruncates_U_IsCoequalizer (NP P) (NP_untruncates P).

(* A transversal of N_P decides P: it is constant on Z/2 when P holds,
   and its two values lie in the cosets of 0 and 1. *)
Definition NP_transversal_decides (P : Prop) (T : Transversal (NP P)) :
  (P + (P → False))%type.
Proof.
  pose proof (transversal_coset T false) as H0.
  pose proof (transversal_coset T true) as H1.
  assert (Hs : P → transversal_map T false = transversal_map T true).
  { intro p; apply (proper_morphism (transversal_map T) false true).
    constructor; unfold quot_rel; simpl; left; exact p. }
  unfold quot_rel in H0, H1; simpl in H0, H1.
  revert H0 H1 Hs.
  generalize (transversal_map T false) (transversal_map T true).
  intros v0 v1 H0 H1 Hs.
  destruct v0, v1; simpl in H0, H1;
    first [ right; intro p; specialize (Hs p); discriminate
          | left; destruct H0 as [p|e]; [ exact p | discriminate ]
          | left; destruct H1 as [p|e]; [ exact p | discriminate ] ].
Defined.

(* And a decision of P gives one: the unit map if P, the identity if not.
   The binder names Z/2's level, which minimization had put at [Set]. *)
Definition NP_decides_transversal@{p +} (P : Prop)
  (d : (P + (P → False))%type) : @Transversal Z2@{p} (NP P).
Proof.
  destruct d as [p|np].
  - unshelve refine (@Build_Transversal Z2 (NP P)
                       {| morphism := fun _ : carrier Z2 => false |} _).
    + intros a b _; reflexivity.
    + intro a; unfold quot_rel; simpl; left; exact p.
  - unshelve refine (@Build_Transversal Z2 (NP P)
                       {| morphism := fun a : carrier Z2 => a |} _).
    + intros a b H; simpl in *.
      change (inhabited (or P (xorb a b = false))) in H.
      change (a = b).
      destruct H as [[H|H]]; [ contradiction |].
      destruct a, b; simpl in H; try discriminate; reflexivity.
    + intro a; unfold quot_rel; simpl; right; destruct a; reflexivity.
Defined.

(* Mac Lane's unconditional "the resulting fork in Set is split" decides
   every proposition, as Instance/Sets/Regular.v's
   [blanket_splitting_entails_LEM] does for its splitting principle. *)
Definition U_split_taboo :
  (∀ P : Prop, SplitCoequalizer (fmap[Grp_Forget] (semidirect_d0 (NP P)))
                                (fmap[Grp_Forget] (semidirect_d1 (NP P)))) →
  ∀ P : Prop, (P + (P → False))%type :=
  fun H P => NP_transversal_decides P (split_transversal (NP P) (H P)).

(* Untruncation does not give a transversal constructively: it holds at
   N_P outright, while a transversal decides P. *)
Definition untruncation_transversal_taboo :
  (∀ P : Prop, CosetUntruncates (NP P) → Transversal (NP P)) →
  ∀ P : Prop, (P + (P → False))%type :=
  fun H P => NP_transversal_decides P (H P (NP_untruncates P)).

(* Even the mere existence of a transversal decides P propositionally. *)
Lemma NP_inhabited_transversal_lem (P : Prop) :
  inhabited (Transversal (NP P)) → or P (P → False).
Proof.
  intros [T]; destruct (NP_transversal_decides P T) as [p|np];
    [ left; exact p | right; exact np ].
Qed.

(* N_S ◁ Z/2 for a type S: membership (a = 0) + S.  The coset relation's
   untruncation there is a choice out of [inhabited S]. *)
Definition NS (S : Type) : NormalSubgroup Z2.
Proof.
  unshelve refine
    {| ns_sub := {| sub_mem := fun a : carrier Z2 => sum (a = false) S |} |}.
  - intros a b Hab Ha; simpl in *; subst; exact Ha.
  - left; reflexivity.
  - intros a b Ha Hb; simpl in *.
    destruct Ha as [Ha|Ha]; [| right; exact Ha ].
    destruct Hb as [Hb|Hb]; [| right; exact Hb ].
    left; subst; reflexivity.
  - intros a Ha; simpl in *; exact Ha.
  - intros t a Ha; simpl in *.
    destruct Ha as [Ha|Ha]; [| right; exact Ha ].
    left; subst; destruct t; reflexivity.
Defined.

Definition NS_untruncates_chooses (S : Type) (D : CosetUntruncates (NS S)) :
  inhabited S → S.
Proof.
  intro i.
  assert (H : inhabited (quot_rel (NS S) true false)).
  { destruct i as [s]; constructor; unfold quot_rel; simpl; right; exact s. }
  pose proof (D true false H) as K.
  unfold quot_rel in K; simpl in K.
  destruct K as [K|s]; [ discriminate | exact s ].
Defined.

(* So U preserves p at every N_S only under the untruncation principle. *)
Definition U_preserves_untruncates :
  (∀ S : Type,
     IsCoequalizer (fmap[Grp_Forget] (semidirect_d0 (NS S)))
       (fmap[Grp_Forget] (semidirect_d1 (NS S)))
       (fobj[Grp_Forget] (QuotientGrp (NS S)))
       (fmap[Grp_Forget] (quot_proj (NS S)))) →
  ∀ S : Type, inhabited S → S :=
  fun H S =>
    NS_untruncates_chooses S (U_IsCoequalizer_untruncates (NS S) (H S)).

(* The pair being reflexive, U's preservation of reflexive coequalizers,
   hypothesis 2 of Monad/Monadicity/Crude.v, entails that principle too. *)
Definition Grp_Forget_crude_untruncates :
  PreservesReflexiveCoequalizers Grp_Forget → ∀ S : Type, inhabited S → S :=
  fun H S =>
    NS_untruncates_chooses S
      (U_IsCoequalizer_untruncates (NS S)
         (H _ _ _ _ (semidirect_reflexive (NS S)) _ _
            (quot_proj_IsCoequalizer (NS S)))).
