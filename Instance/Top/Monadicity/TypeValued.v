Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.

Generalizable All Variables.

(** * The underlying-set functor of the Type-valued [Top] is not monadic *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §VI.3, book p. 144 (PDF p. 153), read from the page image: for the
     forgetful functor G : Top → Set and its left adjoint D, the discrete
     space, the comparison functor "is not an isomorphism, and not even
     an equivalence" (catalog id maclane:VI.3:remark1).
   nLab: https://ncatlab.org/nlab/show/monadic+functor

   WHAT THIS FILE IS.  Instance/Top/Monadicity.v states Mac Lane's remark
   over Instance/Top/Prop.v's Prop-valued [PTopCat], where the discrete
   space is a left adjoint as an [Adjunction] record.  This file states
   what of it is formable over the tree's own Type-valued [Top]
   (Instance/Top.v): that its underlying-set functor is not monadic,
   [Top_Forget_not_Monadic].

   WHAT IS NOT FORMABLE, AND WHY THE NEGATION IS.  [Top_Forget] goes from
   [Top@{h o}], whose homs sit at [h] above the points at [o], to the
   lifted [Sets@{h so}], while [Top_Discrete] comes from the unlifted
   [Sets@{o so}]; an [Adjunction] record asks both functors to share one
   [Sets], so [Top_Discrete ⊣ Top_Forget] is unformable at every universe
   assignment (Instance/Top/Forgetful.v's header;
   Test/ProbeUniversalArrows312.v pins the refusal).  With it go the
   induced monad and the comparison functor.  [Monadic Top_Forget]
   (Monad/Comparison.v) is formable all the same: [Top@{h o}] and
   [Sets@{h so}] share the hom level [h], and [Monadic] quantifies over
   left adjoints out of [Sets@{h so}], not over [Top_Discrete].  So its
   negation is a statement here.

   THE PROOF is Instance/Top/Monadicity.v's, by conservativity.  An
   equivalence K is full (Theory/Equivalence/FullFaithful.v's
   [Equivalence_Full]) and the forgetful functor of any Eilenberg-Moore
   category reflects isomorphisms (Monad/Monadicity/BeckObjects.v's
   [em_forget_reflects_isos]).  The identity of [bool] from Instance/
   Top.v's [Bool_Discrete] to its [TwoPoint_Indiscrete] is continuous
   ([top_bool_to_indisc]); its image under K is an algebra map whose
   underlying function is an isomorphism of [Sets], so it has an inverse
   algebra map, and fullness brings that inverse back to a continuous map
   from [TwoPoint_Indiscrete] to [Bool_Discrete] that is the identity on
   points.  [no_top_indisc_to_bool] refutes one: it would make the
   identity continuous, which Instance/Top.v's
   [indiscrete_to_discrete_id_not_continuous] refutes.

   STRENGTH, AND WHAT IT DOES NOT SAY.  [Top_Forget_not_Monadic] holds
   for every left adjoint and every adjunction.  No left adjoint of
   [Top_Forget] is in the tree, and whether one exists at these
   universes is not settled here, so over [Top] the statement may hold
   for want of an adjunction; it is the [PTopCat] form,
   Instance/Top/Monadicity.v's [PForget_not_Monadic], whose adjunction
   part is inhabited ([PDisc_PForget]).  All three constants close with
   [Qed] or are plain terms; the file has no readback.

   UNIVERSES, read off [About] on Rocq 9.1.1; stdlib caps (compose, ID,
   projections, Projections, Logic_lemmas.equality, eq_ind_r, eq_rect_r
   and prod_rect; the first carrier of eq_ind_r is Instance/Top.v's
   [indiscrete_to_discrete_id_not_continuous], that of eq_rect_r the
   [rewrite] in [no_top_indisc_to_bool]) left out.
   [top_bool_to_indisc@{o h}] and [no_top_indisc_to_bool@{o h}]: o < h,
   [Top@{h o}]'s own.  [Top_Forget_not_Monadic@{o h so m m0 m1 m3 m6}]
   states [Monadic@{m m0 m1 h m3 h so m6}], whose block it carries in
   full (h < m0, h and so below m, h below m1 and m3, so below m3, m1
   and m3 below m), with o < h and h < so from [Top_Forget@{o h so}].
   No [Set] and no equation occur.

   NOT DELIVERED.  The induced monad and the comparison functor over
   [Top] (unformable, above); any left adjoint of [Top_Forget], or a
   proof that there is none. *)

(* The identity of [bool], continuous from the discrete space to the
   indiscrete one (Instance/Top.v's [into_indiscrete_continuous]). *)
Definition top_bool_to_indisc@{o h | o < h +} :
  Bool_Discrete@{o} ~{Top@{h o}}~> TwoPoint_Indiscrete@{o} :=
  @Build_ContinuousMorphism Bool_Discrete@{o} TwoPoint_Indiscrete@{o}
    setoid_morphism_id
    (into_indiscrete_continuous Bool_Discrete@{o} bool_setoid_object@{o o}
       setoid_morphism_id).

(* No continuous map back is the identity on points: it would make the
   identity continuous, which Instance/Top.v's
   [indiscrete_to_discrete_id_not_continuous] refutes. *)
Lemma no_top_indisc_to_bool@{o h | o < h +}
  (g : TwoPoint_Indiscrete@{o} ~{Top@{h o}}~> Bool_Discrete@{o}) :
  (∀ b : bool, continuous_map g b = b) → False.
Proof.
  intros Hg.
  apply (@indiscrete_to_discrete_id_not_continuous@{h o}).
  intros U HU.
  apply (open_respects TwoPoint_Indiscrete@{o}
           (fun x => U (continuous_map g x))).
  - intro x; simpl. rewrite (Hg x). split; intro u; exact u.
  - exact (continuity g U HU).
Qed.

Lemma Top_Forget_not_Monadic@{o h so m m0 m1 m3 m6 |
  o < h, h < so, h < m0, so <= m, h <= m1, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 h m3 h so m6} Top_Forget@{o h so} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{h so} _ _
                   (fmap[EM_Forget _] (fmap[K] top_bool_to_indisc@{o h})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_top_indisc_to_bool
           (@prefmap _ _ _ HF TwoPoint_Indiscrete@{o} Bool_Discrete@{o} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF TwoPoint_Indiscrete@{o} Bool_Discrete@{o} g b).
  - exact (Hr b).
Qed.
