Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.

Generalizable All Variables.

(** * The direct image and the preimage on SUBOBJECTS

    Seven Sketches (Fong and Spivak, "An Invitation to Applied Category
    Theory") §1.4.3.  There is no page image for that book here, so the
    two clauses are quoted from the catalog issue's own transcription:

      "the direct image ... as an operation on subobjects"

      "monotonicity of the subobject preimage"

    The second is a gap in the tree that can be stated precisely: the
    reindexing map [sub_reindex] of Theory/Subobject/Functor.v:35 is
    proved to respect the [SubObj] SETOID ([sub_reindex_respects], :60),
    to be the identity at [id] (:143) and to turn composition into
    composition (:152), but nothing anywhere says it is monotone for
    Theory/Subobject.v:60's ORDER [sub_le] -- measured: the token
    [sub_le] does not occur in Theory/Subobject/Functor.v at all.  That
    is [sub_reindex_monotone] below.

    nLab: https://ncatlab.org/nlab/show/subobject
    nLab: https://ncatlab.org/nlab/show/image
    nLab: https://ncatlab.org/nlab/show/base+change

    ** WHY NONE OF THIS GOES THROUGH [Proset]

    [sub_le u v] is [{ k : sub_dom u ~> sub_dom v & sub_mono v ∘ k ≈
    sub_mono u }] -- a [sigT], hence [Type]-valued.  A [relation] is
    [Prop]-valued, so [sub_le] is not one, and neither
    Instance/Proset.v's [Proset] nor Instance/Proset/Galois.v's
    [GaloisConnection] can be applied to it.  This file therefore states
    everything elementarily, with no category of subobjects and no
    adjunction; Instance/Powerset.v's [Subsets] is the Prop-valued
    counterpart where those DO apply, and the last section relates the
    two.  (The same Type-versus-Prop wall is what keeps
    Instance/Sets/Powerset.v:238's proof-relevant [Powerset_obj] out of
    Instance/Powerset.v; that rejection is pinned as the probe's formability
    negative 2, a sort rejection.)

    ** WHAT IS DELIVERED, WITH GRADES

    (A) [sub_reindex_monotone], in ANY category with chosen pullbacks:
        the mediator into the chosen pullback of [sub_mono v] along [f],
        built from the [sub_le] factorization; its FIRST triangle IS the
        required [sub_le] equation, so the [sub_le] witness is read off
        [ump_pullbacks] with no further step.  General, so it mentions
        neither [Sets] nor images and is stated before them.  (The file
        still has [Instance/Sets] in scope, transitively, because
        Theory/Subobject/Functor.v itself requires it; that is the
        donor's import, not this section's.)

    (B) [sub_image] in [Sets]: the image of [f ∘ sub_mono u], with
        Instance/Sets/Image.v's [Sets_Image_mono] as the mono and
        [Sets_Image_mono_monic] as its monicity, both cited rather than
        reproved.  [sub_image_monotone] carries [sub_le] forward, and
        [sub_image_respects] upgrades that to the [SubObj] setoid --
        cheaply, because BOTH comparison maps preserve the first
        projection and the image setoid compares nothing else, so the two
        inverse laws are [reflexivity].

    (C) The transposition at subobject level, BOTH directions:
        [sub_image_transpose_to] and [sub_image_transpose_from],
        packaged as [sub_image_reindex_iffT].  The backward direction is
        the one with content: its comparison map sends an image point to
        the second pullback projection of the mediator, and its
        RESPECTFULNESS is where monicity of [sub_mono v] is spent --
        two image points with the same first projection may carry
        different preimages, and only injectivity of a mono in [Sets]
        (Instance/Sets.v:374's [injectivity_is_monic], backward leg)
        identifies their values.

    (D) The bridges to #311's passages, at [≈] (NOT at [eq_refl] -- the
        two truncated existentials are differently bracketed, which is
        exactly what each proof reassociates):
        [sub_image_is_Powerset_Prop_image] and
        [sub_reindex_is_Powerset_Prop_preimage].  With them,
        [subset_le_of_sub_le] carries the Type-valued subobject order to
        the Prop-valued subset order.

    ** WHAT IS NOT DELIVERED

    No category of subobjects, no [Proset], no adjunction and no Galois
    connection at this level -- see the wall above.  No claim that the
    two bridges are mutually inverse (#311 proves one composite,
    [Powerset_subset_roundtrip], and says in terms why the other is
    blocked).  No naturality of [sub_image] in [f], no functoriality in
    the subobject beyond the two monotonicity statements, no image
    factorization system, and nothing about [sub_le_monic] or
    [sub_le_unique] beyond citing them.

    ** UNIVERSES

    Section (A) is at whatever universes the ambient category has; (B)
    through (D) inherit [Set < o] from [Powerset_Prop_truth] as usual and
    [o < so] from [Sets@{o so}].  No constant here introduces a [Set]
    pin.  Measured per constant in the report.

    ** TRANSPARENCY

    [sub_image_map] and [sub_transpose_from_map] MUST be [Defined]:
    measured by flipping each to [Qed], which breaks the file, since the
    consumers read their underlying functions.  The other three
    [Defined]s here compile as [Qed] and are so written for uniformity.

    ** REGISTRATION

    Nothing is an [Instance] except [sub_image_respects], which is
    declared [#[export] Instance] to match Theory/Subobject/Functor.v:60's
    [sub_reindex_respects] -- the two are the same kind of fact about the
    same setoid, and a [Proper] instance is what setoid rewriting
    consumes. *)

(* ------------------------------------------------------------------------ *)
(** ** (A) The subobject preimage is monotone, in any category *)

Section ReindexMonotone.

Context {C : Category}.
Context `{@HasPullbacks C}.

(* Given u ≤ v over x and f : y ~> x, the two chosen pullbacks compare.
   The competing square is the pullback of u corrected by the [sub_le]
   factorization [k], and the mediator's first triangle is exactly the
   [sub_le] equation required downstairs. *)
Lemma sub_reindex_monotone {x y : C} (f : y ~> x) {u v : SubObj x} :
  sub_le u v → sub_le (sub_reindex f u) (sub_reindex f v).
Proof.
  intros [k Hk].
  assert (Hsq : f ∘ pullback_fst f (sub_mono u) (pullback f (sub_mono u))
                  ≈ sub_mono v
                      ∘ (k ∘ pullback_snd f (sub_mono u)
                             (pullback f (sub_mono u)))).
  { rewrite comp_assoc, Hk.
    exact (pullback_commutes f (sub_mono u) (pullback f (sub_mono u))). }
  destruct (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
              (Pull f (sub_mono u) (pullback f (sub_mono u)))
              (pullback_fst f (sub_mono u) (pullback f (sub_mono u)))
              (k ∘ pullback_snd f (sub_mono u) (pullback f (sub_mono u)))
              Hsq) as [w [Hw1 Hw2] _].
  exact (existT _ w Hw1).
Defined.

End ReindexMonotone.

(* ------------------------------------------------------------------------ *)
(** ** (B) The direct image of a subobject of a setoid *)

Section SubImage.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(* The direct image of a subobject: the image of the composite mono,
   Instance/Sets/Image.v's construction reused whole. *)
Definition sub_image (u : @SubObj Sets@{o so} A) : @SubObj Sets@{o so} B :=
  @Build_SubObj Sets@{o so} B
    (Sets_Image (f ∘ sub_mono u))
    (Sets_Image_mono (f ∘ sub_mono u))
    (Sets_Image_mono_monic (f ∘ sub_mono u)).

(* The comparison map along a [sub_le] factorization: the same image
   point with its preimage transported through [k].  The membership
   witness is factored out so the map itself is a plain term. *)
Lemma sub_image_witness {u v : @SubObj Sets@{o so} A}
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom v)
  (Hk : sub_mono v ∘ k ≈ sub_mono u)
  (p : carrier (Sets_Image (f ∘ sub_mono u))) :
  f (sub_mono v (k (`1 (`2 p)))) ≈ `1 p.
Proof.
  transitivity (f (sub_mono u (`1 (`2 p)))).
  - exact (proper_morphism f _ _ (Hk (`1 (`2 p)))).
  - exact (`2 (`2 p)).
Qed.

Definition sub_image_map {u v : @SubObj Sets@{o so} A}
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom v)
  (Hk : sub_mono v ∘ k ≈ sub_mono u) :
  sub_dom (sub_image u) ~{Sets@{o so}}~> sub_dom (sub_image v).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} _ _ _ _
       (fun p => existT _ (`1 p)
                   (existT _ (k (`1 (`2 p))) (sub_image_witness k Hk p)))
       _).
  intros p q Hpq; exact Hpq.
Defined.

Lemma sub_image_monotone {u v : @SubObj Sets@{o so} A} :
  sub_le u v → sub_le (sub_image u) (sub_image v).
Proof.
  intros [k Hk].
  exists (sub_image_map k Hk).
  intro p; reflexivity.
Qed.

(* The setoid upgrade.  Both comparison maps preserve the first
   projection, and the image setoid compares nothing else, so the two
   inverse laws close by [reflexivity]. *)
#[export] Instance sub_image_respects :
  Proper (equiv ==> equiv) sub_image.
Proof.
  intros u v [i Hi].
  assert (Hfrom : sub_mono u ∘ from i ≈ sub_mono v).
  { rewrite <- Hi, <- comp_assoc, iso_to_from; cat. }
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := sub_image_map (to i) Hi
                     ; from := sub_image_map (from i) Hfrom |}.
    + intro p; simpl; reflexivity.
    + intro p; simpl; reflexivity.
  - intro p; simpl; reflexivity.
Qed.

End SubImage.

Arguments sub_image {A B} f u.
Arguments sub_image_monotone {A B} f {u v} H.

(* ------------------------------------------------------------------------ *)
(** ** (C) The transposition, at subobject level *)

Section SubTranspose.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(* Left to right.  The image's epi leg supplies the second pullback leg
   and Instance/Sets/Image.v's [Sets_Image_comm] the square. *)
Lemma sub_image_transpose_to (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le (sub_image f u) v → sub_le u (sub_reindex f v).
Proof.
  intros [k Hk].
  assert (Hsq : f ∘ sub_mono u
                  ≈ sub_mono v ∘ (k ∘ Sets_Image_epi (f ∘ sub_mono u))).
  { rewrite comp_assoc, Hk.
    intro p; reflexivity. }
  destruct (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
              (sub_dom u) (sub_mono u)
              (k ∘ Sets_Image_epi (f ∘ sub_mono u)) Hsq)
    as [w [Hw1 Hw2] _].
  exact (existT _ w Hw1).
Defined.

(* Right to left.  The map sends an image point to the second pullback
   projection of the mediator.  The membership equation is factored out
   first, because it serves twice: as the map's own respectfulness proof
   (through monicity) and as the [sub_le] witness. *)
Lemma sub_transpose_from_eq (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B)
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom (sub_reindex f v))
  (Hk : sub_mono (sub_reindex f v) ∘ k ≈ sub_mono u)
  (p : carrier (Sets_Image (f ∘ sub_mono u))) :
  sub_mono v (pullback_snd f (sub_mono v) (pullback f (sub_mono v))
                (k (`1 (`2 p)))) ≈ `1 p.
Proof.
  transitivity (f (sub_mono u (`1 (`2 p)))).
  - symmetry.
    transitivity (f (pullback_fst f (sub_mono v) (pullback f (sub_mono v))
                       (k (`1 (`2 p))))).
    + symmetry; exact (proper_morphism f _ _ (Hk (`1 (`2 p)))).
    + exact (pullback_commutes f (sub_mono v) (pullback f (sub_mono v))
               (k (`1 (`2 p)))).
  - exact (`2 (`2 p)).
Qed.

(* RESPECTFULNESS IS WHERE MONICITY IS SPENT: two image points with one
   first projection may carry different preimages, and only injectivity
   of a mono in [Sets] identifies the two values. *)
Definition sub_transpose_from_map (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B)
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom (sub_reindex f v))
  (Hk : sub_mono (sub_reindex f v) ∘ k ≈ sub_mono u) :
  sub_dom (sub_image f u) ~{Sets@{o so}}~> sub_dom v.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} _ _ _ _
       (fun p => pullback_snd f (sub_mono v) (pullback f (sub_mono v))
                   (k (`1 (`2 p)))) _).
  intros p q Hpq.
  apply (snd (injectivity_is_monic (sub_mono v)) (sub_is_monic v)).
  transitivity (`1 p); [ exact (sub_transpose_from_eq u v k Hk p) | ].
  transitivity (`1 q); [ exact Hpq | ].
  symmetry; exact (sub_transpose_from_eq u v k Hk q).
Defined.

Lemma sub_image_transpose_from (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le u (sub_reindex f v) → sub_le (sub_image f u) v.
Proof.
  intros [k Hk].
  exact (existT _ (sub_transpose_from_map u v k Hk)
           (sub_transpose_from_eq u v k Hk)).
Defined.

Definition sub_image_reindex_iffT (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le (sub_image f u) v ↔ sub_le u (sub_reindex f v) :=
  (sub_image_transpose_to u v, sub_image_transpose_from u v).

End SubTranspose.

(* ------------------------------------------------------------------------ *)
(** ** (D) The bridges to the Prop-valued subsets of #311 *)

Section Bridges.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(* The direct image of the subobject a subset names IS that subset's
   direct image -- at [≈], because the two truncated existentials are
   bracketed differently and each direction reassociates. *)
Lemma sub_image_is_Powerset_Prop_image
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
    ≈ Powerset_Prop_image@{o} f S.
Proof.
  intro b; split; intros Hb Q k.
  - refine (Hb Q _); intros [p Hp].
    apply k; exists (`1 (`1 (`2 p))); split.
    + exact (`2 (`1 (`2 p))).
    + transitivity (`1 p); [ exact (`2 (`2 p)) | exact Hp ].
  - refine (Hb Q _); intros [a [Ha Hfa]].
    apply k.
    unshelve refine (existT _ _ _).
    + exists b; exists (existT _ a Ha); exact Hfa.
    + reflexivity.
Qed.

(* ... and dually for the preimage. *)
Lemma sub_reindex_is_Powerset_Prop_preimage
  (T : carrier (Powerset_Prop_obj@{o} B)) :
  Powerset_subset_of_subobject@{o so}
      (sub_reindex f (Powerset_subobject_of_subset@{o so} T))
    ≈ Powerset_Prop_preimage@{o} f T.
Proof.
  intro a; split.
  - intro Ha.
    refine (Ha (T (f a)) _); intros [p Hp].
    refine (proj1 (@proper_morphism _ _ _ _ T (`1 (snd (`1 p))) (f a) _)
              (`2 (snd (`1 p)))).
    symmetry.
    transitivity (f (fst (`1 p))).
    + exact (proper_morphism f _ _ (symmetry Hp)).
    + exact (`2 p).
  - intro Ha.
    apply Powerset_squash_intro@{o}.
    unshelve refine (existT _ _ _).
    + unshelve refine (existT _ (a, existT _ (f a) Ha) _).
      reflexivity.
    + reflexivity.
Qed.

(* Consequently the Type-valued subobject order maps to the Prop-valued
   subset order: a factorization between subobjects yields inclusion of
   the subsets they name. *)
Lemma subset_le_of_sub_le (u v : @SubObj Sets@{o so} A) :
  sub_le u v →
  ∀ a, Powerset_subset_of_subobject@{o so} u a
       → Powerset_subset_of_subobject@{o so} v a.
Proof.
  intros [k Hk] a Ha Q j.
  refine (Ha Q _); intros [p Hp].
  apply j; exists (k p).
  transitivity (sub_mono u p); [ exact (Hk p) | exact Hp ].
Qed.

End Bridges.
