Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Omega.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Cocomplete.

Generalizable All Variables.

(** * The ω-chain colimit in [Sets] *)

(* nLab:      https://ncatlab.org/nlab/show/sequential+colimit
   nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Direct_limit

   Riehl, "Category Theory in Context", Dover 2016, §3.1 Example 3.1.26 --
   the colimit of an increasing chain of sets is their union.  Mac Lane,
   "Categories for the Working Mathematician" 2nd ed., Springer GTM 5
   1998, §V.1 Exercise 8 asks for the general statement, all small
   colimits; that is Instance/Sets/Cocomplete.v's [Sets_Cocomplete], and
   this file only READS it at the ω-shape.  Riehl's phrasing is honoured
   literally: the chain colimit is stated as a [Colimit] over
   Construction/Chain.v's shape, obtained by INSTANTIATING the general
   witness, and no second construction is written -- the bodies of
   [Sets_Omega_Colimit] and [Sets_Chain_Colimit] are applications of
   [Sets_Cocomplete] and nothing else.

   WHAT IS HERE

   [Sets_Omega_Colimit] gives a [Colimit G] for an ARBITRARY diagram
   [G : Omega ⟶ Sets] over the ordinal ω (Instance/Omega.v), and
   [Sets_Chain_Colimit] specialises it to [Chain F], the initial-algebra
   chain [0 ~> F 0 ~> F² 0 ~> ...] of an endofunctor of [Sets]
   (Construction/Chain.v).  That second constant is exactly the argument
   [adamek_cocomplete] (Theory/Adamek/Corollaries.v:59-66) forms as
   [CC _ (Chain F)], so it is the ω-colimit Adámek's theorem consumes.

   The apex and the legs are read off by conversion: the carrier is the
   sum [{ n : nat & G n }] over the stages ([Sets_omega_carrier],
   [Sets_chain_carrier]), the leg at [n] is the [n]th injection
   ([Sets_omega_inj_at]), and the produced colimit's apex is the quotient
   object of Instance/Sets/Cocomplete.v ([Sets_omega_apex]) -- all four at
   [eq_refl].

   THE UNION READING, AND EXACTLY HOW FAR IT GOES

   "The colimit is the union" is two statements about the generated
   relation, and only ONE of them is proved here.

   SUFFICIENCY, proved: [omega_colim_of_stage] -- if [x : G m] and
   [y : G n] have images that agree at some common later stage [k], then
   they are identified in the colimit.  The proof is three constructors of
   [colim_rel] chained by [cr_trans]: glue [x] up to [k], apply [cr_point]
   to the hypothesis there, and glue [y] back down.  [omega_colim_step] is
   the one-step corollary a reader wants first.

   NECESSITY, *not* proved: nothing here shows the converse, that two
   colimit-identified elements must already agree at a common later stage.
   Without it the union reading is one-directional, and in particular the
   legs are NOT shown injective for a chain of injective connecting maps
   -- which is the content of calling the colimit a union rather than a
   quotient of a sum.  No inclusion-cone statement in that sense is made.

   The reason it is left undone, so that a later attempt starts informed.
   The converse needs a directedness merge -- given agreement at [k₁] and
   at [k₂], push both to a common bound -- and that step compares
   [fmap[G] p] with [fmap[G] p'] for two order proofs [p p' : le_t n k].
   [Omega]'s hom-setoid is [Morphism_equality] (Instance/Omega.v:75),
   strict Leibniz equality of [le_t] derivations, so [fmap_respects] gives
   nothing unless [p = p'].  The lemma supplying [p = p'] ALREADY EXISTS:
   [le_t_irr {m n} (f g : le_t m n) : f = g] at Instance/Ordinal.v:223,
   axiom-free by UIP on [nat], in a file that itself requires
   Instance/Omega.v and reuses that very [le_t].  So the deferral is a
   SCOPE choice about how much of the ω-reading to build here, NOT a
   missing lemma, and a later attempt should start from that constant.
   An earlier draft said instead that "Instance/Omega.v declares [le_t]
   with no uniqueness lemma, so that would have to be proved first, by
   dependent elimination.  That was judged substantial".  The file-local
   absence is real; the inference drawn from it was wrong, and it would
   have sent a later reader to re-derive a lemma the tree already has.

   UNIVERSES, FROM THE CONSTRAINT BLOCKS

   The two constants sit at different strengths and the difference is
   entirely inherited.

     Sets_Omega_Colimit@{u u0 u1} :
       ∀ G : Functor@{u u0 u0 u1 u0 u0}, Colimit@{u0 u u0 u1} G
       (* u u0 u1 |= u0 < u1   u <= u0   ... *)

   is FREE: it keeps [Sets_Cocomplete]'s own [ud <= uo], so [Omega]'s
   objects sit at or below [Sets]' carrier universe and nothing is pinned.

     Sets_Chain_Colimit@{u} :
       ∀ F : Functor@{u Set Set u Set Set},
         Colimit@{Set Set Set u} (Chain F)
       (* u |= Set < False_rect.u0   Set < u *)

   is PINNED: it is a statement about [Sets@{Set u}], setoids whose
   carriers live in [Set].  The cause is measured and is not this file's.
   [Chain@{u u0 u1}] (Construction/Chain.v:64) has result type
   [Functor@{u1 Set Set u u0 u0}] -- it fixes [Omega]'s hom and proof
   universes at [Set] -- and [Cocomplete]'s own shape forces the diagram
   category's hom universe to coincide with [Sets]' carrier universe, so
   the [Set] travels across.  [Sets_Initial@{u u0}], the other donor
   [Chain] consumes, is free and is NOT the cause.  The pin belongs to
   Construction/Chain.v, is NOT repaired here, and is NOT claimed
   unavoidable.

   NON-VACUITY: THE OTHER HALF, AT THE ω-SHAPE

   Instance/Sets/Cocomplete.v's [two_fibres_not_collapsed] shows the
   generated relation does not collapse everything, at a DISCRETE shape,
   where it can merge nothing.  The complementary fact needs a shape that
   HAS a connecting map, and is proved here at a constant ω-diagram
   [OmegaPoints]: [omega_stages_merged] identifies the summands at stages
   0 and 1 in the colimit (by [omega_colim_step], i.e. the glue along the
   generating step), while [omega_stages_apart_in_coproduct] shows the
   coproduct's own [≈] keeps them apart, its index component demanding
   [0 = 1].  So the merge is genuinely the quotient's doing.  Both stages
   are inhabited, by [omega_point], and the two theorems are stated at
   those inhabitants.

   Taken with the other file, what the two witnesses JOINTLY establish is
   that NEITHER endpoint describes [colim_rel] uniformly: this pair
   refutes "always the coproduct's relation", the discrete pair refutes
   "always total".  That is a statement about the FAMILY, not about any
   one diagram.  It is NOT the claim that the relation lies strictly
   inside that interval at some shape -- here it does not, [colim_rel]
   being TOTAL at [OmegaPoints], the fibres being singletons and any two
   stages ordered.  An earlier draft wrote "placed strictly between ...
   EACH FACT AT ITS OWN SHAPE"; the hedge does not rescue the claim.

   WHAT IS NOT DELIVERED, SCOPED TO THIS FILE

   * The necessity half above, hence no theorem that the ω-colimit IS the
     union and no injectivity of the legs.

   * No [AdamekData] (Theory/Adamek.v) and so no initial [F]-algebra:
     Theory/Adamek/Corollaries.v:83-84 records that no [AdamekData]
     witness is constructed anywhere in the tree, and this file does not
     change that.  What it supplies is the [Colimit] argument, not the
     leg-agreement bridge.

   * No filtered-colimit vocabulary, no cofinality statement, and no
     comparison of the ω-shape colimit with any other shape's.

   STATUS: axiom-free.  All 14 constants -- 12 named and the 2 [Program]
   obligations of [OmegaPoints], which the ambient obligation tactic
   discharges -- report "Closed under the global context". *)

Section SetsOmegaColimit.

Context (G : Omega ⟶ Sets).

(** ** The colimit, as an instance of the general witness *)

Definition Sets_Omega_Colimit : Colimit G := Sets_Cocomplete Omega G.

(** ** What the apex and the legs are, by conversion *)

Example Sets_omega_carrier :
  carrier (Sets_colim_obj G) = { n : nat & carrier (G n) }.
Proof. reflexivity. Qed.

Example Sets_omega_inj_at (n : nat) (x : G n) :
  Sets_colim_inj G n x = existT _ n x.
Proof. reflexivity. Qed.

Example Sets_omega_apex :
  @vertex_obj _ _ _ (@limit_cone _ _ _ Sets_Omega_Colimit) = Sets_colim_obj G.
Proof. reflexivity. Qed.

(** ** Agreeing at a common later stage suffices *)

Lemma omega_colim_of_stage (m n k : nat)
  (p : m ~{Omega}~> k) (q : n ~{Omega}~> k) (x : G m) (y : G n) :
  fmap[G] p x ≈ fmap[G] q y ->
  @equiv _ (Sets_colim_obj G) (existT _ m x) (existT _ n y).
Proof.
  intros H.
  apply (@cr_trans _ G _ (existT _ k (fmap[G] p x))).
  - exact (@cr_glue _ G m k p x).
  - apply (@cr_trans _ G _ (existT _ k (fmap[G] q y))).
    + exact (@cr_point _ G k (fmap[G] p x) (fmap[G] q y) H).
    + exact (@cr_sym _ G _ _ (@cr_glue _ G n k q y)).
Qed.

(* The one-sided special case a reader of "the colimit is the union" wants
   first: an element and its image one step along are already identified. *)
Corollary omega_colim_step (n : nat) (x : G n) :
  @equiv _ (Sets_colim_obj G) (existT _ n x)
    (existT _ (S n) (fmap[G] (omega_step n) x)).
Proof. exact (@cr_glue _ G n (S n) (omega_step n) x). Qed.

End SetsOmegaColimit.

(** ** The initial-algebra chain of an endofunctor of [Sets] *)

Definition Sets_Chain_Colimit (F : Sets ⟶ Sets) : Colimit (Chain F) :=
  Sets_Cocomplete Omega (Chain F).

(* Its apex is the sum of the chain's stages, by conversion. *)
Example Sets_chain_carrier (F : Sets ⟶ Sets) :
  carrier (Sets_colim_obj (Chain F)) = { n : nat & carrier (chain_obj F n) }.
Proof. reflexivity. Qed.

(** * Non-vacuity: the quotient merges something the coproduct keeps apart *)

(* Instance/Sets/Cocomplete.v's [two_fibres_not_collapsed] shows the
   generated relation does not collapse everything, at a DISCRETE shape,
   where by construction it can merge nothing.  This is the other half, at
   a shape that HAS a connecting map: two summands at DIFFERENT indices,
   kept apart by the coproduct's own `≈`, are identified in the colimit.
   Together the two witnesses show that NEITHER endpoint describes
   [colim_rel] uniformly across shapes.  Neither is a general theorem
   about all shapes, and neither places the relation strictly inside that
   interval at its own shape -- see the header for the measurement. *)

Section OmegaMergeWitness.

(* A constant ω-diagram: the same singleton at every stage, every
   connecting map the identity.  This file leaves the ambient obligation
   tactic in place (unlike Instance/Sets/Cocomplete.v, which sets it to
   [idtac]), and all three functor laws are constant identities, so no
   obligation survives to be discharged by hand. *)
Program Definition OmegaPoints : Omega ⟶ Sets := {|
  fobj := fun _ => unit_setoid_object;
  fmap := fun _ _ _ => id
|}.

Definition omega_point (n : nat) : carrier (OmegaPoints n) := ttt.

(* MERGED in the colimit: stage 0 and stage 1 are identified, by the glue
   along the generating step [0 ~> 1]. *)
Theorem omega_stages_merged :
  @equiv _ (Sets_colim_obj OmegaPoints)
    (existT _ 0%nat (omega_point 0)) (existT _ 1%nat (omega_point 1)).
Proof. exact (omega_colim_step OmegaPoints 0%nat (omega_point 0)). Qed.

(* ... and KEPT APART by the coproduct, whose `≈` at distinct indices
   demands an equality of those indices.  So the merge above is genuinely
   the quotient's doing and not already present downstairs. *)
Theorem omega_stages_apart_in_coproduct :
  @equiv _ (Sets_colim_sum OmegaPoints)
    (existT _ 0%nat (omega_point 0)) (existT _ 1%nat (omega_point 1)) -> False.
Proof. intros [e _]; discriminate e. Qed.

End OmegaMergeWitness.
