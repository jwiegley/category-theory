Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Coequalizer.
Require Import Category.Adjunction.Diagonal.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Colimit.

Generalizable All Variables.

(** * The free product of groups as a coequalizer of free groups *)

(* nLab:      https://ncatlab.org/nlab/show/free+product
   nLab:      https://ncatlab.org/nlab/show/monadic+adjunction
   nLab:      https://ncatlab.org/nlab/show/coequalizer
   Wikipedia: https://en.wikipedia.org/wiki/Free_product

   Riehl, "Category Theory in Context", 2nd ed., §5.6, the unnumbered
   construction of the free product of groups (printed pp. 212–213, PDF
   pp. 232–233).  The forgetful functor U : Group → Set does not preserve
   coproducts, so the free product G * H cannot be computed on underlying
   sets, and Riehl works relative to the free-forgetful adjunction F ⊣ U
   instead.  The free group F(UG + UH) on the disjoint union of the two
   carriers is a first approximation, and the relations the two group
   operations impose are encoded by a parallel pair of homomorphisms

       l, r : F(UFUG + UFUH) ⇉ F(UG + UH),

   l being F applied to the disjoint union Uε_G + Uε_H of the counit
   components, and r being F of the canonical comparison
   [UF inl, UF inr] : UFUG + UFUH → UF(UG + UH) (Exercise 3.4.i, printed
   p. 108, PDF p. 128) followed by the counit at F(UG + UH).  The free
   product is the coequalizer of that pair.  Read on one letter: the letter
   [inl w], for w a word in the elements of G, goes under l to the
   one-letter word on the VALUE of w in G, and under r to the word w itself
   with every letter tagged [inl] ([Grp_riehl_l_inl], [Grp_riehl_r_inl]).
   Coequalizing l and r therefore makes the tagged letters of each factor
   multiply as they do in that factor.

   Instance/Grp/Colimit.v obtains the same coproduct from the adjoint
   functor theorem, applied at the diagonal as Instance/Grp/FreeAFT.v
   applies it at the forgetful functor, and Instance/Grp/Pushout.v builds
   it from words and relations.  This file builds Riehl's pair, proves her
   claim in both directions, and compares the result with both.

   ** WHAT IS BUILT

   (a) The canonical presentation of one group.
   [Grp_canonical_presentation]: ε_G : FUG → G is a coequalizer of ε_{FUG}
   and FUε_G.  This is Riehl's Proposition 5.4.2 (printed p. 198, PDF
   p. 218) read at the free-group adjunction and stated upstairs in [Grp].
   The cofork is counit naturality, Theory/Adjunction.v's [counit_comp]
   (Monad/Monadicity/Crude.v's [crude_unit_cofork] is the same equation).
   A coforking k descends to k on one-letter words ([Grp_canonical_desc]).
   That map is a homomorphism because the cofork, evaluated at the
   one-letter word whose single letter is the word [g][g'], identifies
   k([g][g']) with k([gg']).  Uniqueness is proved on elements.  No
   monadicity theorem and no split coequalizer in [Sets] is used: every
   step is Instance/Grp/Free.v's [free_group_counit_generator],
   [free_group_fmap_generators] or [free_grp_extend_unique], the last
   packaged here as [Grp_free_hom_ext] (two homomorphisms out of a free
   group that agree on the letters agree).

   (b) The pair and the transpose.  [Grp_riehl_comparison] is Riehl's
   comparison, and [Grp_riehl_l] and [Grp_riehl_r] are the two legs.
   [Grp_riehl_transpose f1 f2] is the transpose across
   [free_group_adjunction] of the copairing in [Sets] of the underlying
   maps of f1 : G → z and f2 : H → z.  [Grp_riehl_e CC] is the transpose of
   the two injections of a coproduct structure CC, that is Riehl's
   e : F(UG + UH) → G + H.  Every such transpose coforks the pair
   ([Grp_riehl_transpose_cofork]).

   (c) Riehl's claim in both directions, at every coproduct structure.
     - [Grp_coproduct_is_coequalizer CC]: for ANY [Cocartesian] structure
       CC on [Grp], (G +_CC H, e) is a coequalizer of (l, r).  A coforking
       k, restricted along F(inl), coforks G's canonical presentation
       ([Grp_riehl_kG_cofork]), which descends it to G ([Grp_riehl_uG]).
       The same holds for H, and the mediator is the copairing of the two
       descents ([Grp_riehl_desc]).
     - [Grp_Cocartesian_of_coequalizers HC]: conversely, for ANY choice HC
       of coequalizers in [Grp], the coequalizer of (l, r) IS a binary
       coproduct.  Its injections [Grp_riehl_inl] / [Grp_riehl_inr] are e
       restricted to each factor's words and descended through that
       factor's canonical presentation, and its copairing is
       [Grp_riehl_merge].  This is the construction in the direction Riehl
       runs it: the free product DEFINED as the coequalizer.

   (d) Agreement with the adjoint functor theorem.
     - [Grp_free_product_is_coequalizer] is (c) at Instance/Grp/Colimit.v's
       [Grp_Cocartesian_via_GAFT], passed explicitly.  The free product the
       theorem produces is the coequalizer of Riehl's pair, with Riehl's e.
     - [Grp_Cocartesian_via_riehl] is (c)'s converse run on
       Instance/Grp/Colimit.v's [Grp_HasCoequalizers_via_GAFT].  Its
       coproduct object IS, by [eq_refl], the apex of the coequalizer the
       theorem returns for (l, r) ([Grp_Cocartesian_via_riehl_obj]).
     - [Grp_free_product_coequalizer_agrees]: that apex is isomorphic to the
       theorem's coproduct G + H.  The isomorphism is compatible with the
       coequalizing maps ([Grp_free_product_coequalizer_agrees_e]:
       to ∘ e_coeq ≈ e) and carries Riehl's injections to the theorem's
       ([Grp_free_product_coequalizer_agrees_inl], [_inr]).
       [Grp_riehl_coproduct_agrees] is the functor-level statement: the two
       coproduct bifunctors agree up to natural isomorphism, by
       Theory/Adjunction.v's [left_adjoint_iso].
     - Composing with Instance/Grp/Colimit.v's [Grp_free_product_iso]
       carries the same apex to Instance/Grp/Pushout.v's words-based free
       product ([Grp_free_product_coequalizer_agrees_words], with [_e],
       [_inl] and [_inr]).  [Grp_free_product_words_is_coequalizer] is (c)
       at Pushout.v's [Grp_Cocartesian] directly, the reading of Riehl's
       construction that uses no adjoint functor theorem at all.

   ** INSTANCE DISCIPLINE

   Instance/Grp/Pushout.v's [Grp_Cocartesian] and
   Instance/Sets/Cocartesian.v's [Sets_Cocartesian] are both [#[export]],
   and both are imported here.  Every [Coprod], [inl], [inr], [merge] and
   [cover] below names its [Cocartesian] argument explicitly, so no
   statement that says "via the adjoint functor theorem" can resolve to the
   words-based instance.  Nothing here is registered as an [Instance].

   ** A TRANSPARENT TWIN OF [coequalizer_unique]

   Structure/Coequalizer.v's [coequalizer_unique] ends in [Qed] ([About]
   reports it opaque), so the isomorphism it returns cannot be shown to
   carry one coequalizing map to the other.  [coequalizer_unique_along]
   repeats its construction and ends in [Defined], and
   [coequalizer_unique_along_e] records to ∘ e1 ≈ e2.  It is generic in the
   category and belongs in Structure/Coequalizer.v; it is here only because
   it was written for this file's comparison and moving it would touch
   Structure/Coequalizer.v, and it is a merge candidate rather than
   a removal candidate.  It is not an exact copy: [About] shows it carries
   one universe more than the original, with [u0 < u1], a bound the [Qed]
   original's statement does not expose.

   ** STRENGTHS, STRICTEST FIRST

   Two readbacks hold by [eq_refl]: [Grp_Cocartesian_via_riehl_obj] (the
   coproduct object IS the apex of the theorem's coequalizer) and
   [Grp_riehl_inl_is_restriction] (the injection IS e at the image of a
   one-letter word under F(inl)).  Everything else is `≈` or `≅`.  The
   counit does not compute, and neither does [FreeGrp] on arrows, since
   both are defined by universal factorization (Instance/Grp/Free.v's
   comments above [free_group_counit] and [free_group_fmap_generators]),
   so each letter-level fact
   ([Grp_riehl_l_inl], [Grp_riehl_r_inl], [Grp_riehl_transpose_generator])
   is `≈`.  [GAFT] is opaque ([About]), so nothing about the theorem's
   coproduct or coequalizer computes, and every agreement in (d) is an
   isomorphism carried as data, with `≈` equations about it.

   ** UNIVERSES, MEASURED

   Measured by [About] under [Set Printing Universes], with the bounds on
   stdlib globals, and the local strict bounds not named below, dropped.
   [Grp_riehl_l], [Grp_riehl_r], [Grp_riehl_e] and
   [Grp_coproduct_is_coequalizer] live over [Grp@{u p}] with [Set < u] and
   [p < u] and NO lower bound on the carrier [p].
   [Grp_canonical_presentation] takes G : obj[Grp@{u1 u}] with [Set < u1]
   and [u < u1], again with no lower bound on the carrier [u].  The
   theorem-level constants of parts (c) and (d) are declared [@{u p +}] so
   that their first two universes are [Grp]'s; [Grp_canonical_presentation]
   carries no annotation, which is why its readback names [Grp]'s
   universes [u1 u].  [Grp_Cocartesian_of_coequalizers] is
   [HasCoequalizers@{u p} Grp@{u p} → @Cocartesian Grp@{u p}] with
   [Set < u] and [p < u], and [Grp_free_product_words_is_coequalizer] is
   over [Grp@{u p}] with the same two bounds.  Riehl's construction
   therefore holds at [Set] carriers too.
   [Grp_free_product_is_coequalizer], [Grp_Cocartesian_via_riehl] and every
   [_agrees] constant in (d) add [Set < p] and [p < eq_rect_r.u0].  Both
   bounds are inherited from [Grp_Cocartesian_via_GAFT] and
   [Grp_HasCoequalizers_via_GAFT], whose own readbacks carry them.  The
   side condition is the adjoint functor theorem's, not Riehl's.

   One trap is recorded.  The non-vacuity lemmas below were first written
   with no binders, and [About] read [Grp_riehl_pair_nontrivial] back at
   [Z2@{Set}] and [Grp_riehl_e_not_monic] over [@Cocartesian Grp@{u2 Set}].
   At [Set] carriers they could never meet the adjoint functor theorem's
   [Set < carrier].  They now sit in a section declaring [u p], and they
   read back at [Z2@{p}] over [Grp@{u p}] with no LOWER bound on [p] (no
   [Set < p]), [p] sitting strictly below the hom universe of [Sets].

   ** NON-VACUITY

   [Grp_riehl_pair_nontrivial]: at G = H = Z/2 (Instance/Grp.v's [Z2]),
   l ≉ r.  Take w to be the word [1][1].  The homomorphism
   F(UZ2 + UZ2) → Z2 that sends every letter to 1 takes l([inl w]) to 1 and
   r([inl w]) to 1 + 1 = 0.  Hence [Grp_riehl_e_not_monic]: at every
   coproduct structure, e at Z/2, Z/2 is not monic, so the coequalizer
   genuinely quotients.  [Grp_free_product_coequalizer_nontrivial] states
   this at the adjoint functor theorem's coproduct, above [Set].

   ** AXIOMS

   Every constant of this file reports "Closed under the global context"
   when queried by its fully qualified name.  The file uses no [Program],
   so it has no obligations.

   ** NOT DELIVERED

   Riehl's general statement is issue #1009 and is not here: the same
   construction for any monadic U : A → C over a cocomplete C, Proposition
   5.6.11 (printed p. 213, PDF p. 233), and Exercise 5.6.iii (printed
   p. 217, PDF p. 237).  Everything here is at the free-group adjunction
   and is proved on letters.  Proposition 5.4.2 in general, the canonical
   presentation of an algebra over an arbitrary monad, is not here either;
   [Grp_canonical_presentation] is its [Grp] instance only.  Free products
   are binary only; there are no I-indexed ones.

   The tree contains no choice of coequalizers in [Grp] independent of the
   adjoint functor theorem (one could be built from the normal closure of
   the image of f · g⁻¹, which is not yet here).
   [Grp_Cocartesian_of_coequalizers] takes [HasCoequalizers Grp]
   as a hypothesis, and its one inhabitant in the tree is
   [Grp_HasCoequalizers_via_GAFT] (measured by [grep -rn HasCoequalizers]
   over the [.v] files, keeping the hits that mention groups).
   Instance/Grp/Quotient/Colimit.v coequalizes pairs of the form (f, 0)
   only ([normal_closure_IsCoequalizer]), and it is not applied to Riehl's
   pair here.  So "without the adjoint functor theorem" holds only for
   [Grp_free_product_words_is_coequalizer], which starts from Pushout.v's
   words.  There is no element-level description of the coequalizer: no
   reduced words and no normal form. *)

(** ** Homomorphisms out of a free group are determined on the letters *)

Lemma Grp_free_hom_ext {X : Sets} {K : Grp} (g1 g2 : FreeGrp X ~{Grp}~> K) :
  (∀ a, g1 (fg_insert X a) ≈ g2 (fg_insert X a)) → g1 ≈ g2.
Proof.
  intros Hg w.
  transitivity (free_grp_extend (fmap[Grp_Forget] g2 ∘ fg_insert X) w).
  - exact (free_grp_extend_unique X K
             (fmap[Grp_Forget] g2 ∘ fg_insert X) g1 Hg w).
  - symmetry.
    apply (free_grp_extend_unique X K _ g2).
    intro a; reflexivity.
Qed.

(** ** The canonical presentation of one group *)

Section Canonical.

Context (G : Grp).

Lemma Grp_canonical_cofork :
  free_group_counit G ∘ free_group_counit (FreeGrp (Grp_Forget G))
    ≈ free_group_counit G
        ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)).
Proof.
  symmetry.
  exact (@counit_comp _ _ _ _ free_group_adjunction _ _ (free_group_counit G)).
Qed.

Context {c : Grp} (k : FreeGrp (Grp_Forget G) ~{Grp}~> c).
Context (Hk : k ∘ free_group_counit (FreeGrp (Grp_Forget G))
                ≈ k ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G))).

Definition Grp_canonical_desc : G ~{Grp}~> c.
Proof using Hk.
  unshelve refine (@Build_GrpHom' G c
                     (fmap[Grp_Forget] k ∘ fg_insert (Grp_Forget G)) _).
  intros g g'; simpl.
  set (w := grp_mul (FreeGrpObject (Grp_Forget G))
              (fg_insert (Grp_Forget G) g) (fg_insert (Grp_Forget G) g')).
  rewrite <- (grp_map_mul k).
  fold w.
  transitivity (grp_map k (free_group_counit (FreeGrp (Grp_Forget G))
                  (fg_insert (Grp_Forget (FreeGrp (Grp_Forget G))) w))).
  2: { apply (proper_morphism (grp_map k)).
       exact (free_group_counit_generator (FreeGrp (Grp_Forget G)) w). }
  transitivity (grp_map k
                  (fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G))
                     (fg_insert (Grp_Forget (FreeGrp (Grp_Forget G))) w))).
  2: { symmetry. exact (Hk _). }
  apply (proper_morphism (grp_map k)).
  rewrite free_group_fmap_generators.
  apply (proper_morphism (fg_insert (Grp_Forget G))).
  simpl.
  unfold w.
  rewrite (grp_map_mul (free_group_counit G)).
  rewrite !free_group_counit_generator.
  reflexivity.
Defined.

Lemma Grp_canonical_desc_commutes :
  Grp_canonical_desc ∘ free_group_counit G ≈ k.
Proof.
  apply Grp_free_hom_ext; intro a; simpl.
  apply (proper_morphism (grp_map k)).
  apply (proper_morphism (fg_insert (Grp_Forget G))).
  exact (free_group_counit_generator G a).
Qed.

Lemma Grp_canonical_desc_unique (v : G ~{Grp}~> c) :
  v ∘ free_group_counit G ≈ k → Grp_canonical_desc ≈ v.
Proof.
  intros Hv g; simpl.
  rewrite <- (Hv (fg_insert (Grp_Forget G) g)); simpl.
  apply (proper_morphism (grp_map v)).
  exact (free_group_counit_generator G g).
Qed.

End Canonical.

Definition Grp_canonical_presentation (G : Grp) :
  IsCoequalizer (free_group_counit (FreeGrp (Grp_Forget G)))
                (fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)))
                G (free_group_counit G).
Proof.
  unshelve econstructor.
  - exact (Grp_canonical_cofork G).
  - intros c k Hk.
    exact {| unique_obj      := Grp_canonical_desc G k Hk;
             unique_property := Grp_canonical_desc_commutes G k Hk;
             uniqueness      := Grp_canonical_desc_unique G k Hk |}.
Defined.

(** ** Riehl's parallel pair *)

Section RiehlPair.

Universes u p.
Context (G H : Grp@{u p}).

Local Notation UGH :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).
Local Notation UFUGH :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget (FreeGrp (Grp_Forget G)))
                                 (Grp_Forget (FreeGrp (Grp_Forget H)))).
Local Notation inlS :=
  (@inl Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).
Local Notation inrS :=
  (@inr Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).

(* Riehl's "canonical comparison" [UF inl, UF inr] : UFUG + UFUH → UF(UG + UH)
   between the coproduct of the images and the image of the coproduct. *)
Definition Grp_riehl_comparison :
  UFUGH ~{Sets}~> Grp_Forget (FreeGrp UGH) :=
  @merge Sets Sets_Cocartesian _ _ _
    (fmap[Grp_Forget] (fmap[FreeGrp] inlS))
    (fmap[Grp_Forget] (fmap[FreeGrp] inrS)).

(* The leg F(Uε_G + Uε_H). *)
Definition Grp_riehl_l : FreeGrp UFUGH ~{Grp@{u p}}~> FreeGrp UGH :=
  fmap[FreeGrp] (@cover Sets Sets_Cocartesian _ _ _ _
                   (fmap[Grp_Forget] (free_group_counit G))
                   (fmap[Grp_Forget] (free_group_counit H))).

(* The leg ε_{F(UG+UH)} ∘ F[UF inl, UF inr]. *)
Definition Grp_riehl_r : FreeGrp UFUGH ~{Grp@{u p}}~> FreeGrp UGH :=
  free_group_counit (FreeGrp UGH) ∘ fmap[FreeGrp] Grp_riehl_comparison.

(* The transpose, across the free-forgetful adjunction, of the copairing in
   [Sets] of the underlying maps of two homomorphisms out of G and H. *)
Definition Grp_riehl_transpose {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  FreeGrp UGH ~{Grp@{u p}}~> z :=
  from (@adj _ _ _ _ free_group_adjunction _ _)
    (@merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                        (fmap[Grp_Forget] f2)).

(* Riehl's e : F(UG + UH) → G + H, the transpose of [U inl, U inr], at a
   coproduct structure that is passed EXPLICITLY. *)
Definition Grp_riehl_e (CC : @Cocartesian Grp@{u p}) :
  FreeGrp UGH ~{Grp@{u p}}~> @Coprod Grp@{u p} CC G H :=
  Grp_riehl_transpose (@inl Grp@{u p} CC G H) (@inr Grp@{u p} CC G H).

(** *** What the maps do to a letter *)

Lemma Grp_riehl_transpose_generator {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) (s : UGH) :
  Grp_riehl_transpose f1 f2 (fg_insert UGH s)
    ≈ @merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                         (fmap[Grp_Forget] f2) s.
Proof.
  pose proof (@from_adj_comp_law _ _ _ _ free_group_adjunction _ _
                (@merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                                    (fmap[Grp_Forget] f2)))
    as Hc.
  rewrite (@to_adj_unit _ _ _ _ free_group_adjunction) in Hc.
  exact (Hc s).
Qed.

Lemma Grp_riehl_l_inl (w : FGWord (Grp_Forget G)) :
  Grp_riehl_l (fg_insert UFUGH (Datatypes.inl w))
    ≈ fg_insert UGH (Datatypes.inl (free_group_counit G w)).
Proof. exact (@free_group_fmap_generators UFUGH UGH _ (Datatypes.inl w)). Qed.

Lemma Grp_riehl_l_inr (w : FGWord (Grp_Forget H)) :
  Grp_riehl_l (fg_insert UFUGH (Datatypes.inr w))
    ≈ fg_insert UGH (Datatypes.inr (free_group_counit H w)).
Proof. exact (@free_group_fmap_generators UFUGH UGH _ (Datatypes.inr w)). Qed.

Lemma Grp_riehl_r_inl (w : FGWord (Grp_Forget G)) :
  Grp_riehl_r (fg_insert UFUGH (Datatypes.inl w)) ≈ fmap[FreeGrp] inlS w.
Proof.
  transitivity (free_group_counit (FreeGrp UGH)
                  (fg_insert _ (Grp_riehl_comparison (Datatypes.inl w)))).
  - apply (proper_morphism (grp_map (free_group_counit (FreeGrp UGH)))).
    exact (@free_group_fmap_generators UFUGH _ Grp_riehl_comparison
             (Datatypes.inl w)).
  - exact (free_group_counit_generator (FreeGrp UGH) _).
Qed.

Lemma Grp_riehl_r_inr (w : FGWord (Grp_Forget H)) :
  Grp_riehl_r (fg_insert UFUGH (Datatypes.inr w)) ≈ fmap[FreeGrp] inrS w.
Proof.
  transitivity (free_group_counit (FreeGrp UGH)
                  (fg_insert _ (Grp_riehl_comparison (Datatypes.inr w)))).
  - apply (proper_morphism (grp_map (free_group_counit (FreeGrp UGH)))).
    exact (@free_group_fmap_generators UFUGH _ Grp_riehl_comparison
             (Datatypes.inr w)).
  - exact (free_group_counit_generator (FreeGrp UGH) _).
Qed.

(** *** The transpose on each factor, and the cofork *)

Section Transpose.

Context {z : Grp@{u p}} (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z).

Lemma Grp_riehl_transpose_inl :
  Grp_riehl_transpose f1 f2 ∘ fmap[FreeGrp] inlS ≈ f1 ∘ free_group_counit G.
Proof.
  apply Grp_free_hom_ext; intro g.
  transitivity (Grp_riehl_transpose f1 f2 (fg_insert UGH (Datatypes.inl g))).
  - apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    exact (@free_group_fmap_generators _ UGH _ g).
  - rewrite (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)).
    symmetry.
    apply (proper_morphism (grp_map f1)).
    exact (free_group_counit_generator G g).
Qed.

Lemma Grp_riehl_transpose_inr :
  Grp_riehl_transpose f1 f2 ∘ fmap[FreeGrp] inrS ≈ f2 ∘ free_group_counit H.
Proof.
  apply Grp_free_hom_ext; intro g.
  transitivity (Grp_riehl_transpose f1 f2 (fg_insert UGH (Datatypes.inr g))).
  - apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    exact (@free_group_fmap_generators _ UGH _ g).
  - rewrite (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)).
    symmetry.
    apply (proper_morphism (grp_map f2)).
    exact (free_group_counit_generator H g).
Qed.

(* Every such transpose coforks the pair: on the letter [inl w] both legs
   come to f1 applied to the value of the word w in G. *)
Lemma Grp_riehl_transpose_cofork :
  Grp_riehl_transpose f1 f2 ∘ Grp_riehl_l
    ≈ Grp_riehl_transpose f1 f2 ∘ Grp_riehl_r.
Proof.
  apply Grp_free_hom_ext; intros [w|w].
  - transitivity (Grp_riehl_transpose f1 f2
                    (fg_insert UGH (Datatypes.inl (free_group_counit G w)))).
    { apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
      exact (Grp_riehl_l_inl w). }
    rewrite (Grp_riehl_transpose_generator f1 f2).
    transitivity (Grp_riehl_transpose f1 f2 (fmap[FreeGrp] inlS w)).
    { symmetry. exact (Grp_riehl_transpose_inl w). }
    apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    symmetry. exact (Grp_riehl_r_inl w).
  - transitivity (Grp_riehl_transpose f1 f2
                    (fg_insert UGH (Datatypes.inr (free_group_counit H w)))).
    { apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
      exact (Grp_riehl_l_inr w). }
    rewrite (Grp_riehl_transpose_generator f1 f2).
    transitivity (Grp_riehl_transpose f1 f2 (fmap[FreeGrp] inrS w)).
    { symmetry. exact (Grp_riehl_transpose_inr w). }
    apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    symmetry. exact (Grp_riehl_r_inr w).
Qed.

End Transpose.

(** *** A coforking map restricts to each factor *)

Section Factors.

Context {c : Grp@{u p}} (k : FreeGrp UGH ~{Grp@{u p}}~> c).
Context (Hk : k ∘ Grp_riehl_l ≈ k ∘ Grp_riehl_r).

(* The restriction of [k] to the words in each factor's letters. *)
Definition Grp_riehl_kG : FreeGrp (Grp_Forget G) ~{Grp@{u p}}~> c :=
  k ∘ fmap[FreeGrp] inlS.

Definition Grp_riehl_kH : FreeGrp (Grp_Forget H) ~{Grp@{u p}}~> c :=
  k ∘ fmap[FreeGrp] inrS.

(* Each restriction coforks that factor's canonical presentation. *)
Lemma Grp_riehl_kG_cofork :
  Grp_riehl_kG ∘ free_group_counit (FreeGrp (Grp_Forget G))
    ≈ Grp_riehl_kG ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)).
Proof using Hk.
  apply Grp_free_hom_ext; intro w.
  transitivity (k (fmap[FreeGrp] inlS w)).
  { apply (proper_morphism (grp_map Grp_riehl_kG)).
    exact (free_group_counit_generator (FreeGrp (Grp_Forget G)) w). }
  transitivity (k (Grp_riehl_r (fg_insert UFUGH (Datatypes.inl w)))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (Grp_riehl_r_inl w). }
  transitivity (k (Grp_riehl_l (fg_insert UFUGH (Datatypes.inl w)))).
  { symmetry. exact (Hk _). }
  transitivity (k (fg_insert UGH (Datatypes.inl (free_group_counit G w)))).
  { apply (proper_morphism (grp_map k)).
    exact (Grp_riehl_l_inl w). }
  transitivity (Grp_riehl_kG
                  (fg_insert (Grp_Forget G) (free_group_counit G w))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (@free_group_fmap_generators _ UGH _ _). }
  apply (proper_morphism (grp_map Grp_riehl_kG)).
  symmetry.
  exact (@free_group_fmap_generators _ _
           (fmap[Grp_Forget] (free_group_counit G)) w).
Qed.

Lemma Grp_riehl_kH_cofork :
  Grp_riehl_kH ∘ free_group_counit (FreeGrp (Grp_Forget H))
    ≈ Grp_riehl_kH ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit H)).
Proof using Hk.
  apply Grp_free_hom_ext; intro w.
  transitivity (k (fmap[FreeGrp] inrS w)).
  { apply (proper_morphism (grp_map Grp_riehl_kH)).
    exact (free_group_counit_generator (FreeGrp (Grp_Forget H)) w). }
  transitivity (k (Grp_riehl_r (fg_insert UFUGH (Datatypes.inr w)))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (Grp_riehl_r_inr w). }
  transitivity (k (Grp_riehl_l (fg_insert UFUGH (Datatypes.inr w)))).
  { symmetry. exact (Hk _). }
  transitivity (k (fg_insert UGH (Datatypes.inr (free_group_counit H w)))).
  { apply (proper_morphism (grp_map k)).
    exact (Grp_riehl_l_inr w). }
  transitivity (Grp_riehl_kH
                  (fg_insert (Grp_Forget H) (free_group_counit H w))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (@free_group_fmap_generators _ UGH _ _). }
  apply (proper_morphism (grp_map Grp_riehl_kH)).
  symmetry.
  exact (@free_group_fmap_generators _ _
           (fmap[Grp_Forget] (free_group_counit H)) w).
Qed.

(* The descents through the two canonical presentations. *)
Definition Grp_riehl_uG : G ~{Grp@{u p}}~> c :=
  unique_obj (coeq_desc (Grp_canonical_presentation G)
                Grp_riehl_kG Grp_riehl_kG_cofork).

Definition Grp_riehl_uH : H ~{Grp@{u p}}~> c :=
  unique_obj (coeq_desc (Grp_canonical_presentation H)
                Grp_riehl_kH Grp_riehl_kH_cofork).

Lemma Grp_riehl_uG_counit :
  Grp_riehl_uG ∘ free_group_counit G ≈ Grp_riehl_kG.
Proof using Hk.
  exact (unique_property (coeq_desc (Grp_canonical_presentation G)
                            Grp_riehl_kG Grp_riehl_kG_cofork)).
Qed.

Lemma Grp_riehl_uH_counit :
  Grp_riehl_uH ∘ free_group_counit H ≈ Grp_riehl_kH.
Proof using Hk.
  exact (unique_property (coeq_desc (Grp_canonical_presentation H)
                            Grp_riehl_kH Grp_riehl_kH_cofork)).
Qed.

End Factors.

(** *** Every coproduct of G and H is a coequalizer of the pair *)

Section Descent.

Context (CC : @Cocartesian Grp@{u p}).
Context {c : Grp@{u p}} (k : FreeGrp UGH ~{Grp@{u p}}~> c).
Context (Hk : k ∘ Grp_riehl_l ≈ k ∘ Grp_riehl_r).

Definition Grp_riehl_desc : @Coprod Grp@{u p} CC G H ~{Grp@{u p}}~> c :=
  @merge Grp@{u p} CC _ _ _ (Grp_riehl_uG k Hk) (Grp_riehl_uH k Hk).

Lemma Grp_riehl_desc_commutes : Grp_riehl_desc ∘ Grp_riehl_e CC ≈ k.
Proof.
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (Grp_riehl_desc (@inl Grp@{u p} CC G H g)).
    { apply (proper_morphism (grp_map Grp_riehl_desc)).
      exact (Grp_riehl_transpose_generator _ _ (Datatypes.inl g)). }
    transitivity (Grp_riehl_uG k Hk g).
    { exact (@inl_merge Grp@{u p} CC _ _ _ _ _ g). }
    transitivity (Grp_riehl_uG k Hk (free_group_counit G (fg_insert _ g))).
    { apply (proper_morphism (grp_map (Grp_riehl_uG k Hk))).
      symmetry. exact (free_group_counit_generator G g). }
    transitivity (Grp_riehl_kG k (fg_insert _ g)).
    { exact (Grp_riehl_uG_counit k Hk (fg_insert _ g)). }
    apply (proper_morphism (grp_map k)).
    exact (@free_group_fmap_generators _ UGH _ g).
  - transitivity (Grp_riehl_desc (@inr Grp@{u p} CC G H g)).
    { apply (proper_morphism (grp_map Grp_riehl_desc)).
      exact (Grp_riehl_transpose_generator _ _ (Datatypes.inr g)). }
    transitivity (Grp_riehl_uH k Hk g).
    { exact (@inr_merge Grp@{u p} CC _ _ _ _ _ g). }
    transitivity (Grp_riehl_uH k Hk (free_group_counit H (fg_insert _ g))).
    { apply (proper_morphism (grp_map (Grp_riehl_uH k Hk))).
      symmetry. exact (free_group_counit_generator H g). }
    transitivity (Grp_riehl_kH k (fg_insert _ g)).
    { exact (Grp_riehl_uH_counit k Hk (fg_insert _ g)). }
    apply (proper_morphism (grp_map k)).
    exact (@free_group_fmap_generators _ UGH _ g).
Qed.

Lemma Grp_riehl_desc_unique (v : @Coprod Grp@{u p} CC G H ~{Grp@{u p}}~> c) :
  v ∘ Grp_riehl_e CC ≈ k → Grp_riehl_desc ≈ v.
Proof.
  intro Hv.
  assert (HG : Grp_riehl_uG k Hk ≈ v ∘ @inl Grp@{u p} CC G H).
  { apply (uniqueness (coeq_desc (Grp_canonical_presentation G)
                         (Grp_riehl_kG k) (Grp_riehl_kG_cofork k Hk))).
    unfold Grp_riehl_kG.
    rewrite <- Hv.
    rewrite <- !comp_assoc.
    rewrite (Grp_riehl_transpose_inl (@inl Grp@{u p} CC G H)
                                     (@inr Grp@{u p} CC G H)).
    reflexivity. }
  assert (HH : Grp_riehl_uH k Hk ≈ v ∘ @inr Grp@{u p} CC G H).
  { apply (uniqueness (coeq_desc (Grp_canonical_presentation H)
                         (Grp_riehl_kH k) (Grp_riehl_kH_cofork k Hk))).
    unfold Grp_riehl_kH.
    rewrite <- Hv.
    rewrite <- !comp_assoc.
    rewrite (Grp_riehl_transpose_inr (@inl Grp@{u p} CC G H)
                                     (@inr Grp@{u p} CC G H)).
    reflexivity. }
  unfold Grp_riehl_desc.
  rewrite HG, HH.
  rewrite (@merge_comp Grp@{u p} CC).
  rewrite (@merge_inl_inr Grp@{u p} CC).
  exact (@id_right Grp@{u p} _ _ v).
Qed.

End Descent.

Definition Grp_coproduct_is_coequalizer (CC : @Cocartesian Grp@{u p}) :
  IsCoequalizer Grp_riehl_l Grp_riehl_r (@Coprod Grp@{u p} CC G H)
    (Grp_riehl_e CC).
Proof.
  unshelve econstructor.
  - exact (Grp_riehl_transpose_cofork _ _).
  - intros c k Hk.
    exact {| unique_obj      := Grp_riehl_desc CC k Hk;
             unique_property := Grp_riehl_desc_commutes CC k Hk;
             uniqueness      := Grp_riehl_desc_unique CC k Hk |}.
Defined.

(** *** Every coequalizer of the pair is a coproduct of G and H *)

Section Construction.

Context {q : Grp@{u p}} {e : FreeGrp UGH ~{Grp@{u p}}~> q}.
Context (E : IsCoequalizer Grp_riehl_l Grp_riehl_r q e).

(* The injections: e restricted to each factor's words, descended through
   that factor's canonical presentation. *)
Definition Grp_riehl_inl : G ~{Grp@{u p}}~> q := Grp_riehl_uG e (cofork E).
Definition Grp_riehl_inr : H ~{Grp@{u p}}~> q := Grp_riehl_uH e (cofork E).

(* The injection computes: on an element g it IS e at the image of the
   one-letter word [g] under F(inl). *)
Example Grp_riehl_inl_is_restriction (g : carrier (grp_setoid G)) :
  Grp_riehl_inl g = e (fmap[FreeGrp] inlS (fg_insert (Grp_Forget G) g))
  := eq_refl.

(* The copairing: the transpose of the two maps, descended through e. *)
Definition Grp_riehl_merge {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) : q ~{Grp@{u p}}~> z :=
  unique_obj (coeq_desc E (Grp_riehl_transpose f1 f2)
                (Grp_riehl_transpose_cofork f1 f2)).

Lemma Grp_riehl_merge_inl {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  Grp_riehl_merge f1 f2 ∘ Grp_riehl_inl ≈ f1.
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (Grp_canonical_presentation G))).
  rewrite <- comp_assoc.
  rewrite (Grp_riehl_uG_counit e (cofork E)).
  unfold Grp_riehl_kG.
  rewrite comp_assoc.
  rewrite (unique_property (coeq_desc E (Grp_riehl_transpose f1 f2)
                              (Grp_riehl_transpose_cofork f1 f2))).
  exact (Grp_riehl_transpose_inl f1 f2).
Qed.

Lemma Grp_riehl_merge_inr {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  Grp_riehl_merge f1 f2 ∘ Grp_riehl_inr ≈ f2.
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (Grp_canonical_presentation H))).
  rewrite <- comp_assoc.
  rewrite (Grp_riehl_uH_counit e (cofork E)).
  unfold Grp_riehl_kH.
  rewrite comp_assoc.
  rewrite (unique_property (coeq_desc E (Grp_riehl_transpose f1 f2)
                              (Grp_riehl_transpose_cofork f1 f2))).
  exact (Grp_riehl_transpose_inr f1 f2).
Qed.

Lemma Grp_riehl_merge_unique {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (h : q ~{Grp@{u p}}~> z) :
  h ∘ Grp_riehl_inl ≈ f1 → h ∘ Grp_riehl_inr ≈ f2 →
  h ≈ Grp_riehl_merge f1 f2.
Proof.
  intros H1 H2.
  symmetry.
  apply (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                       (Grp_riehl_transpose_cofork f1 f2))).
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (h (Grp_riehl_inl g)).
    { apply (proper_morphism (grp_map h)).
      transitivity (e (fmap[FreeGrp] inlS (fg_insert _ g))).
      { apply (proper_morphism (grp_map e)).
        symmetry. exact (@free_group_fmap_generators _ UGH _ g). }
      transitivity (Grp_riehl_inl (free_group_counit G (fg_insert _ g))).
      { symmetry.
        exact (Grp_riehl_uG_counit e (cofork E) (fg_insert _ g)). }
      apply (proper_morphism (grp_map Grp_riehl_inl)).
      exact (free_group_counit_generator G g). }
    rewrite (H1 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)).
  - transitivity (h (Grp_riehl_inr g)).
    { apply (proper_morphism (grp_map h)).
      transitivity (e (fmap[FreeGrp] inrS (fg_insert _ g))).
      { apply (proper_morphism (grp_map e)).
        symmetry. exact (@free_group_fmap_generators _ UGH _ g). }
      transitivity (Grp_riehl_inr (free_group_counit H (fg_insert _ g))).
      { symmetry.
        exact (Grp_riehl_uH_counit e (cofork E) (fg_insert _ g)). }
      apply (proper_morphism (grp_map Grp_riehl_inr)).
      exact (free_group_counit_generator H g). }
    rewrite (H2 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)).
Qed.

(* Any map out of q that carries e to the transpose of (f1, f2) carries the
   injections to f1 and f2. *)
Lemma Grp_riehl_inl_along {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (φ : q ~{Grp@{u p}}~> z) :
  φ ∘ e ≈ Grp_riehl_transpose f1 f2 → φ ∘ Grp_riehl_inl ≈ f1.
Proof.
  intro Hφ.
  rewrite <- (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                            (Grp_riehl_transpose_cofork f1 f2)) φ Hφ).
  exact (Grp_riehl_merge_inl f1 f2).
Qed.

Lemma Grp_riehl_inr_along {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (φ : q ~{Grp@{u p}}~> z) :
  φ ∘ e ≈ Grp_riehl_transpose f1 f2 → φ ∘ Grp_riehl_inr ≈ f2.
Proof.
  intro Hφ.
  rewrite <- (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                            (Grp_riehl_transpose_cofork f1 f2)) φ Hφ).
  exact (Grp_riehl_merge_inr f1 f2).
Qed.

End Construction.

(* Postcomposition moves inside the transpose. *)
Lemma Grp_riehl_transpose_post {z z' : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (f1' : G ~{Grp@{u p}}~> z') (f2' : H ~{Grp@{u p}}~> z')
  (φ : z ~{Grp@{u p}}~> z') :
  φ ∘ f1 ≈ f1' → φ ∘ f2 ≈ f2' →
  φ ∘ Grp_riehl_transpose f1 f2 ≈ Grp_riehl_transpose f1' f2'.
Proof.
  intros H1 H2.
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (φ (f1 g)).
    { apply (proper_morphism (grp_map φ)).
      exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)). }
    rewrite (H1 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1' f2' (Datatypes.inl g)).
  - transitivity (φ (f2 g)).
    { apply (proper_morphism (grp_map φ)).
      exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)). }
    rewrite (H2 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1' f2' (Datatypes.inr g)).
Qed.

End RiehlPair.

(** ** Riehl's construction as a coproduct structure on [Grp] *)

(* Given coequalizers, from anywhere, the coequalizer of the pair with the
   injections above IS a choice of binary coproducts. *)
Definition Grp_Cocartesian_of_coequalizers@{u p +}
  (HC : HasCoequalizers Grp@{u p}) : @Cocartesian Grp@{u p}.
Proof.
  unshelve refine (@Build_Cartesian (Grp^op)
    (fun G H => `1 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))
    (fun x G H f1 f2 =>
       @Grp_riehl_merge G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H))))
         x f1 f2)
    (fun G H =>
       @Grp_riehl_inl G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))))
    (fun G H =>
       @Grp_riehl_inr G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))))
    _ _).
  - intros x G H f1 f1' Hf1 f2 f2' Hf2.
    apply Grp_riehl_merge_unique.
    + rewrite (Grp_riehl_merge_inl _ _ _ f1 f2); exact Hf1.
    + rewrite (Grp_riehl_merge_inr _ _ _ f1 f2); exact Hf2.
  - intros x G H f1 f2 h; split.
    + intro Hh; split.
      * rewrite Hh. exact (Grp_riehl_merge_inl _ _ _ f1 f2).
      * rewrite Hh. exact (Grp_riehl_merge_inr _ _ _ f1 f2).
    + intros [H1 H2].
      exact (Grp_riehl_merge_unique _ _ _ f1 f2 h H1 H2).
Defined.

(** ** At the adjoint functor theorem's coproduct and coequalizers *)

(* Riehl's statement at the coproduct Instance/Grp/Colimit.v obtains from
   the adjoint functor theorem, passed explicitly. *)
Definition Grp_free_product_is_coequalizer@{u p +} (G H : Grp@{u p}) :
  IsCoequalizer (Grp_riehl_l G H) (Grp_riehl_r G H)
    (@Coprod Grp Grp_Cocartesian_via_GAFT G H)
    (Grp_riehl_e G H Grp_Cocartesian_via_GAFT) :=
  Grp_coproduct_is_coequalizer G H Grp_Cocartesian_via_GAFT.

(* The same at Instance/Grp/Pushout.v's words-based free product. *)
Definition Grp_free_product_words_is_coequalizer@{u p +} (G H : Grp@{u p}) :
  IsCoequalizer (Grp_riehl_l G H) (Grp_riehl_r G H)
    (@Coprod Grp Grp_Cocartesian G H)
    (Grp_riehl_e G H Grp_Cocartesian) :=
  Grp_coproduct_is_coequalizer G H Grp_Cocartesian.

(* Riehl's construction run on the adjoint functor theorem's coequalizers. *)
Definition Grp_Cocartesian_via_riehl@{u p +} : @Cocartesian Grp@{u p} :=
  Grp_Cocartesian_of_coequalizers Grp_HasCoequalizers_via_GAFT.

Example Grp_Cocartesian_via_riehl_obj@{u p +} (G H : Grp@{u p}) :
  @Coprod Grp Grp_Cocartesian_via_riehl G H
    = `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
            (Grp_riehl_l G H) (Grp_riehl_r G H)) := eq_refl.

(** ** Agreement *)

(* [coequalizer_unique] of Structure/Coequalizer.v ends in [Qed], so its
   comparison map cannot be read back; this transparent twin carries the
   coequalizing maps along. *)
Section CoequalizerAlong.

Context {C : Category} {x y : C} {f g : x ~> y}.
Context {q1 q2 : C} {e1 : y ~> q1} {e2 : y ~> q2}.
Context (E1 : IsCoequalizer f g q1 e1) (E2 : IsCoequalizer f g q2 e2).

Definition coequalizer_unique_along : q1 ≅ q2.
Proof using E1 E2.
  pose proof (coeq_desc E1 e2 (cofork E2)) as D12.
  pose proof (coeq_desc E2 e1 (cofork E1)) as D21.
  pose proof (coeq_desc E1 e1 (cofork E1)) as D11.
  pose proof (coeq_desc E2 e2 (cofork E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite <- comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D22).
      apply id_left.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite <- comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D11).
      apply id_left.
Defined.

Lemma coequalizer_unique_along_e : to coequalizer_unique_along ∘ e1 ≈ e2.
Proof using E1 E2. exact (unique_property (coeq_desc E1 e2 (cofork E2))). Qed.

End CoequalizerAlong.

(* The coequalizer Instance/Grp/Colimit.v's [Grp_HasCoequalizers_via_GAFT]
   returns for Riehl's pair is the adjoint functor theorem's coproduct... *)
Definition Grp_free_product_coequalizer_agrees@{u p +} (G H : Grp@{u p}) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
        (Grp_riehl_l G H) (Grp_riehl_r G H))
    ≅ @Coprod Grp Grp_Cocartesian_via_GAFT G H :=
  coequalizer_unique_along
    (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
               (Grp_riehl_l G H) (Grp_riehl_r G H))))
    (Grp_free_product_is_coequalizer G H).

(* ...compatibly with the coequalizing maps... *)
Lemma Grp_free_product_coequalizer_agrees_e@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ `1 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                (Grp_riehl_l G H) (Grp_riehl_r G H)))
    ≈ Grp_riehl_e G H Grp_Cocartesian_via_GAFT.
Proof.
  exact (coequalizer_unique_along_e
           (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                      (Grp_riehl_l G H) (Grp_riehl_r G H))))
           (Grp_free_product_is_coequalizer G H)).
Qed.

(* ...and with the injections: Riehl's on the left, the theorem's on the
   right. *)
Lemma Grp_free_product_coequalizer_agrees_inl@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ @inl Grp Grp_Cocartesian_via_riehl G H
    ≈ @inl Grp Grp_Cocartesian_via_GAFT G H.
Proof.
  exact (Grp_riehl_inl_along G H _
           (@inl Grp Grp_Cocartesian_via_GAFT G H)
           (@inr Grp Grp_Cocartesian_via_GAFT G H) _
           (Grp_free_product_coequalizer_agrees_e G H)).
Qed.

Lemma Grp_free_product_coequalizer_agrees_inr@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ @inr Grp Grp_Cocartesian_via_riehl G H
    ≈ @inr Grp Grp_Cocartesian_via_GAFT G H.
Proof.
  exact (Grp_riehl_inr_along G H _
           (@inl Grp Grp_Cocartesian_via_GAFT G H)
           (@inr Grp Grp_Cocartesian_via_GAFT G H) _
           (Grp_free_product_coequalizer_agrees_e G H)).
Qed.

(* The two coproduct bifunctors agree up to natural isomorphism, both being
   left adjoint to the diagonal. *)
Definition Grp_riehl_coproduct_agrees@{u p +} :
  @InternalCoproductFunctor Grp@{u p} Grp_Cocartesian_via_riehl
    ≈ @InternalCoproductFunctor Grp@{u p} Grp_Cocartesian_via_GAFT :=
  left_adjoint_iso (Diagonal_Product Grp@{u p}) _ _
    (@Diagonal_Coproduct_Adjunction Grp@{u p} Grp_Cocartesian_via_riehl)
    (@Diagonal_Coproduct_Adjunction Grp@{u p} Grp_Cocartesian_via_GAFT).

(* Through Instance/Grp/Colimit.v's [Grp_free_product_iso], the same
   coequalizer is Instance/Grp/Pushout.v's words-based free product. *)
Definition Grp_free_product_coequalizer_agrees_words@{u p +}
  (G H : Grp@{u p}) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
        (Grp_riehl_l G H) (Grp_riehl_r G H))
    ≅ @Coprod Grp Grp_Cocartesian G H :=
  iso_compose (Grp_free_product_iso G H)
              (Grp_free_product_coequalizer_agrees G H).

Lemma Grp_free_product_coequalizer_agrees_words_e@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ `1 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                (Grp_riehl_l G H) (Grp_riehl_r G H)))
    ≈ Grp_riehl_e G H Grp_Cocartesian.
Proof.
  unfold Grp_free_product_coequalizer_agrees_words; simpl to.
  rewrite <- comp_assoc.
  rewrite (Grp_free_product_coequalizer_agrees_e G H).
  apply Grp_riehl_transpose_post.
  - exact (Grp_free_product_iso_inl G H).
  - exact (Grp_free_product_iso_inr G H).
Qed.

Lemma Grp_free_product_coequalizer_agrees_words_inl@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ @inl Grp Grp_Cocartesian_via_riehl G H
    ≈ @inl Grp Grp_Cocartesian G H.
Proof.
  exact (Grp_riehl_inl_along G H _
           (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H) _
           (Grp_free_product_coequalizer_agrees_words_e G H)).
Qed.

Lemma Grp_free_product_coequalizer_agrees_words_inr@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ @inr Grp Grp_Cocartesian_via_riehl G H
    ≈ @inr Grp Grp_Cocartesian G H.
Proof.
  exact (Grp_riehl_inr_along G H _
           (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H) _
           (Grp_free_product_coequalizer_agrees_words_e G H)).
Qed.

(** ** Non-vacuity *)

(* The pair is not trivial: at Z/2 the letter [inl w], for w the word
   "1 then 1", is sent by l to the letter [inl 0] and by r to the word
   "[inl 1] then [inl 1]", and the homomorphism to Z/2 sending every letter
   to 1 separates the two. *)
Section NonVacuity.

Universes u p.

Local Notation Z2 := Z2@{p}.
Local Notation Z2S :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget Z2) (Grp_Forget Z2)).
Local Notation Z2FS :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget (FreeGrp (Grp_Forget Z2)))
                                 (Grp_Forget (FreeGrp (Grp_Forget Z2)))).

Lemma Grp_riehl_pair_nontrivial :
  (Grp_riehl_l Z2 Z2 : _ ~{Grp@{u p}}~> _) ≈ Grp_riehl_r Z2 Z2 → False.
Proof.
  intro Hlr.
  pose (w := grp_mul (FreeGrpObject (Grp_Forget Z2))
               (fg_insert (Grp_Forget Z2) true)
               (fg_insert (Grp_Forget Z2) true)).
  unshelve epose (t := {| morphism := fun _ : Z2S => true |}
                         : Z2S ~{Sets}~> Grp_Forget Z2).
  { intros ? ? ?; reflexivity. }
  pose (k := free_grp_extend t).
  assert (HA : k (Grp_riehl_l Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))
                 ≈ true).
  { transitivity (k (fg_insert Z2S
                       (Datatypes.inl (free_group_counit Z2 w)))).
    - apply (proper_morphism (grp_map k)).
      exact (Grp_riehl_l_inl Z2 Z2 w).
    - exact (free_grp_extend_generators Z2S Z2 t _). }
  assert (HB : k (Grp_riehl_r Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))
                 ≈ false).
  { transitivity (k (fmap[FreeGrp]
                       (@inl Sets Sets_Cocartesian
                          (Grp_Forget Z2) (Grp_Forget Z2)) w)).
    - apply (proper_morphism (grp_map k)).
      exact (Grp_riehl_r_inl Z2 Z2 w).
    - unfold w.
      rewrite (proper_morphism (grp_map k) _ _
                 (grp_map_mul (fmap[FreeGrp]
                    (@inl Sets Sets_Cocartesian
                       (Grp_Forget Z2) (Grp_Forget Z2))) _ _)).
      rewrite (grp_map_mul k).
      rewrite (proper_morphism (grp_map k) _ _
                 (@free_group_fmap_generators (Grp_Forget Z2) Z2S _ true)).
      rewrite (free_grp_extend_generators Z2S Z2 t).
      reflexivity. }
  apply Z2_nontrivial.
  transitivity (k (Grp_riehl_l Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))).
  { symmetry; exact HA. }
  transitivity (k (Grp_riehl_r Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))).
  { apply (proper_morphism (grp_map k)); exact (Hlr _). }
  exact HB.
Qed.

(* Hence e is never monic at Z/2: the coequalizer genuinely quotients the
   free group on the disjoint union. *)
Corollary Grp_riehl_e_not_monic (CC : @Cocartesian Grp@{u p}) :
  Monic (Grp_riehl_e Z2 Z2 CC) → False.
Proof.
  intro Hm.
  apply Grp_riehl_pair_nontrivial.
  apply (@monic _ _ _ _ Hm).
  exact (cofork (Grp_coproduct_is_coequalizer Z2 Z2 CC)).
Qed.

End NonVacuity.

(* The same at the adjoint functor theorem's coproduct, which exists only
   above [Set] carriers. *)
Example Grp_free_product_coequalizer_nontrivial@{u p +} :
  Monic (Grp_riehl_e Z2@{p} Z2@{p}
           (Grp_Cocartesian_via_GAFT : @Cocartesian Grp@{u p})) → False :=
  Grp_riehl_e_not_monic _.
