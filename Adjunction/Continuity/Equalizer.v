Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.FromProducts.

Generalizable All Variables.

(** * Right adjoints preserve equalizers, in the elementary form *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.9 Exercise 1, book p. 135 (PDF p. 144), read from the page image
     (catalog id maclane:V.9:ex1): "[...] but show that this functor C
     can have no left adjoint (because of misbehavior on equalizers)."
     The argument the parenthesis names is this file's: a right adjoint
     preserves equalizers, so a functor that sends some equalizer to a
     fork that is not one has no left adjoint.
   nLab: https://ncatlab.org/nlab/show/adjoints+preserve+(co-)limits
   nLab: https://ncatlab.org/nlab/show/equalizer

   BACKGROUND.  Right adjoints preserve limits (Adjunction/Continuity.v's
   [right_adjoint_PreservesLimitCone], RAPL, stated for every shape in
   the cone vocabulary of Structure/Limit/Preservation.v).  An equalizer
   is the limit of a parallel pair, and Structure/Equalizer/Fork.v states
   it elementarily as well, a fork [IsEqualizer f g q e] through which
   every fork of the pair descends uniquely.  Structure/Limit/
   FromProducts.v's [PreservesEqualizers G] is the elementary preservation
   predicate, the one #416's [continuous_from_products_equalizers]
   consumes; before this file no lemma fed it from an adjunction.

   WHY A DIRECT PROOF.  Reaching [PreservesEqualizers U] from RAPL would
   go through Fork.v's [equalizer_is_equalizer] and [is_equalizer_limit]
   and would need the diagram [U ◯ APair f g] read as [APair (fmap[U] f)
   (fmap[U] g)] (Instance/Parallel.v's [APair]).  Their object parts
   agree at [eq_refl], but the two functors are not convertible: [eq_refl]
   at their equality is refused ("cannot unify "U ◯ APair f g" and
   "APair (fmap[U] f) (fmap[U] g)""), at a variable [U : C ⟶ D] and a
   variable pair [f g : x ~> y]: Test/ProbeComponents462.v's N9, beside
   the object parts at [eq_refl] as controls.  Monad/Eilenberg/Moore/
   Limit.v and Monad/Monadicity/Crude.v record the same absence of a
   bridge.  So the proof transposes directly, about twenty lines.  Since
   #477 the coequalizer side needs no such reading: Structure/
   Coequalizer.v's [parallel_colimit_coequalizer] and
   [parallel_coequalizer_colimit] convert at any diagram of
   parallel-pair shape.  Their equalizer twin, which the route above
   would need, is not built, so for equalizers this paragraph stands.

   WHAT IS HERE.
     - [right_adjoint_PreservesEqualizers A]: for [A : F ⊣ U], [U] sends
       every elementary equalizer to one.  The image is a fork by
       [fmap_comp] and [fmap_respects]; a fork [h : z ~> U x] of the
       image pair transposes along the inverse transpose to a fork of the
       pair in C ([from_adj_nat_r]), descends through the equalizer, and
       the descent transposes back ([to_adj_nat_r], [from_adj_comp_law]);
       a competing factorization transposes to a competing descent, which
       the equalizer's uniqueness identifies.
     - [not_PreservesEqualizers_no_left_adjoint]: the contrapositive as a
       refutation, the shape Mac Lane's exercise asks for.  Given an
       equalizer in C whose U-image is not an equalizer, every [F] with
       [F ⊣ U] is refuted.  Instance/Top/Components.v's
       [components_no_left_adjoint] and
       [discrete_left_adjoint_no_left_adjoint] are its consumers.

   PLACEMENT.  Beside Adjunction/Continuity/Finite.v, the other packaged
   corollaries of RAPL used as tests for the non-existence of adjoints.
   It does not require Adjunction/Continuity.v: the direct proof uses none
   of that file's cone machinery.  Structure/Limit/FromProducts.v owns
   [PreservesEqualizers] and requires no adjunction file, so there is no
   cycle: [Print Libraries] on a file requiring this one lists 40
   [Category.*] modules besides it, and the only ones matching
   "Adjunction" or "Continuity" are Theory/Adjunction.v and this file.

   STRENGTHS.  Up to [≈], the elementary universal property: a
   factorization and its uniqueness.  One [Defined] and one [Qed]
   (counted by token).  [right_adjoint_PreservesEqualizers] is data, a
   [PreservesEqualizers] whose mediators are transposes, and it is
   closed [Defined], transparent as Adjunction/Continuity.v's RAPL
   corollaries are ([right_adjoint_PreservesLimitCone] and its
   siblings, each a [Definition]); no consumer in the tree reduces it.
   [not_PreservesEqualizers_no_left_adjoint] concludes [False] and is
   [Qed].  Both constants are closed under the global context ([Print
   Assumptions]).

   UNIVERSES, read by [About] under [Set Printing Universes].
     - [right_adjoint_PreservesEqualizers@{co do h u u0 u1}], with
       [C : Category@{co h h}] and [D : Category@{do h h}]: block
       [h < u0], [co <= u], [do <= u], [h <= u] and the four stdlib caps
       [h <= compose.u0], [compose.u1], [compose.u2], [ID.u0] that
       Instance/Sets.v's [Sets] carries.  [u] is [PreservesEqualizers]'s
       own universe ([PreservesEqualizers@{u co h do}]), [u0] the object
       universe of the [Sets] in which the adjunction's hom-isomorphisms
       live ([Adjunction]'s own [h1 < so]), and [u1] its last slot,
       unconstrained.  The two categories share the one hom level [h]
       because [Adjunction]'s block identifies them ([h1 = h2]).
     - [not_PreservesEqualizers_no_left_adjoint@{co do h u u0}]: block
       [h < u] and the same four caps, [u] and [u0] the adjunction's two
       free slots as above.
   Both binders are written [@{co do h +}], so the adjunction's universes
   stay free and the refutation applies to adjunctions at every universe
   instance.  [Set] occurs in neither block.

   NOT DELIVERED.  The dual, left adjoints preserve coequalizers in the
   elementary form: the tree has no elementary coequalizer-preservation
   predicate to state it against (a grep of the .v files for
   "PreservesCoequalizers" finds only this sentence).  No bridge between
   [PreservesEqualizers] and Structure/Limit/Preservation.v's cone-level
   vocabulary. *)

Definition right_adjoint_PreservesEqualizers@{co do h +}
  {C : Category@{co h h}} {D : Category@{do h h}}
  {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) : PreservesEqualizers U.
Proof.
  intros x y f g q e E.
  unshelve econstructor.
  - rewrite <- !fmap_comp. apply fmap_respects. exact (fork_eq E).
  - intros z h Hh.
    (* the transpose of h forks the pair in C *)
    assert (Hf : f ∘ from (@adj _ _ _ _ A z x) h
                   ≈ g ∘ from (@adj _ _ _ _ A z x) h).
    { rewrite <- !from_adj_nat_r. apply from_adj_respects. exact Hh. }
    destruct (eq_desc E _ Hf) as [u Hu Huniq].
    exists (to (@adj _ _ _ _ A z q) u).
    + rewrite <- to_adj_nat_r. rewrite Hu.
      apply from_adj_comp_law.
    + intros v Hv.
      rewrite <- (from_adj_comp_law (H := A) v).
      apply to_adj_respects.
      apply Huniq.
      rewrite <- from_adj_nat_r. rewrite Hv. reflexivity.
Defined.

Corollary not_PreservesEqualizers_no_left_adjoint@{co do h +}
  {C : Category@{co h h}} {D : Category@{do h h}} {U : C ⟶ D}
  {x y : C} (f g : x ~> y) (q : C) (e : q ~> x) (E : IsEqualizer f g q e)
  (N : IsEqualizer (fmap[U] f) (fmap[U] g) (U q) (fmap[U] e) → False)
  (F : D ⟶ C) (A : F ⊣ U) : False.
Proof. exact (N (right_adjoint_PreservesEqualizers A x y f g q e E)). Qed.
