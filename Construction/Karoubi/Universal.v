Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Construction.Karoubi.

Generalizable All Variables.

(** The universal property of the Karoubi envelope, and Cauchy completeness. *)

(* nLab:      https://ncatlab.org/nlab/show/Karoubi+envelope
   nLab:      https://ncatlab.org/nlab/show/Cauchy+complete+category
   Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

   A category has split idempotents when every idempotent e : x ~> x factors
   through some object as a retraction followed by a section; the class
   [IdempotentsSplit] packages a chosen such splitting for each idempotent.
   Categories with this property are exactly the Cauchy complete categories
   (in the sense of enrichment over Set), whence [CauchyComplete] below.

   The Karoubi envelope Split(C) of Construction/Karoubi.v is the free
   idempotent-splitting completion of C.  This file records the evidence:

   - idempotents split in Split(C) ([Karoubi_IdempotentsSplit]), and the
     object splitting a given idempotent is unique up to isomorphism
     ([split_idem_unique]);

   - every functor G : C ⟶ D into a category with chosen splittings extends
     along the embedding C ⟶ Split(C) to a functor Split(C) ⟶ D
     ([Karoubi_Extend]) sending (x, e) to the splitting object of G e, with
     Extend ∘ Embed ≈ G ([Karoubi_Extend_comm]); the extension is unique up
     to natural isomorphism among functors restricting to G along the
     embedding ([Karoubi_Extend_unique]);

   - when C itself has split idempotents, the embedding C ⟶ Split(C) is an
     equivalence of categories ([cauchy_complete_embed_equiv]).  Only this
     forward direction is formalized; the converse (an equivalence forces
     the idempotents of C to split, by transporting the envelope's
     splittings backwards) is not carried in the library.

   The uniqueness argument rests on the observation that inside Split(C)
   every object (x, e) is a retract of the embedded object (x, id), both
   directions being carried by e itself ([Karoubi_retraction],
   [Karoubi_section]), so that every morphism of Split(C) factors through
   the image of the embedding ([Karoubi_factors]). *)

(* A choice of splitting for every idempotent of C. *)
Class IdempotentsSplit (C : Category) := {
  split_of {x : C} (e : x ~> x) (H : Idempotent e) :
    ∃ (y : C) (S : @SplitIdempotent C x y), @split_idem C x y S ≈ e
}.

(* Idempotents split in the Karoubi envelope: [karoubi_idem_splits] from
   Construction/Karoubi.v, repackaged through the class.  The splitting it
   chooses for an idempotent φ on (x, e) has φ itself as the split
   idempotent, so agreement with φ is reflexivity. *)
#[export] Instance Karoubi_IdempotentsSplit {C : Category} :
  IdempotentsSplit (Karoubi C).
Proof.
  constructor.
  intros X φ Hφ.
  eexists.
  exists (karoubi_idem_splits X φ Hφ).
  reflexivity.
Defined.

(* Splitting objects are unique up to isomorphism: if S splits an idempotent
   through y, and S' splits an ≈-equal idempotent through y', then composing
   the section of one with the retraction of the other in both orders yields
   a two-sided inverse pair between y and y'. *)
Definition split_idem_unique {C : Category} {x y y' : C}
           (S : @SplitIdempotent C x y) (S' : @SplitIdempotent C x y')
           (Heq : @split_idem C x y S ≈ @split_idem C x y' S') : y ≅ y'.
Proof.
  refine {| to   := @split_idem_r C x y' S' ∘ @split_idem_s C x y S
          ; from := @split_idem_r C x y S ∘ @split_idem_s C x y' S' |}.
  - (* r' ∘ (s ∘ r) ∘ s' ≈ r' ∘ (s' ∘ r') ∘ s' ≈ (r' ∘ s') ∘ (r' ∘ s') ≈ id *)
    rewrite <- comp_assoc.
    rewrite (comp_assoc (@split_idem_s C x y S)).
    rewrite (@split_idem_sr C x y S).
    rewrite Heq.
    rewrite <- (@split_idem_sr C x y' S').
    rewrite <- comp_assoc.
    rewrite (@split_idem_rs C x y' S').
    rewrite id_right.
    apply (@split_idem_rs C x y' S').
  - (* r ∘ (s' ∘ r') ∘ s ≈ r ∘ (s ∘ r) ∘ s ≈ (r ∘ s) ∘ (r ∘ s) ≈ id *)
    rewrite <- comp_assoc.
    rewrite (comp_assoc (@split_idem_s C x y' S')).
    rewrite (@split_idem_sr C x y' S').
    rewrite <- Heq.
    rewrite <- (@split_idem_sr C x y S).
    rewrite <- comp_assoc.
    rewrite (@split_idem_rs C x y S).
    rewrite id_right.
    apply (@split_idem_rs C x y S).
Qed.

(* Inside the envelope, (x, e) is a retract of the embedded object (x, id):
   the section (x, e) ~> (x, id) and the retraction (x, id) ~> (x, e) are
   both carried by e itself. *)
Definition Karoubi_section {C : Category} (X : Karoubi C) :
  X ~{Karoubi C}~> Karoubi_Embed (`1 X).
Proof.
  exists (`1 (`2 X)).
  simpl.
  split.
  - apply id_left.
  - exact (`2 (`2 X)).
Defined.

Definition Karoubi_retraction {C : Category} (X : Karoubi C) :
  Karoubi_Embed (`1 X) ~{Karoubi C}~> X.
Proof.
  exists (`1 (`2 X)).
  simpl.
  split.
  - exact (`2 (`2 X)).
  - apply id_right.
Defined.

(* Retraction after section is the identity of (x, e): both carriers are e,
   and e ∘ e ≈ e. *)
Lemma Karoubi_retraction_section {C : Category} (X : Karoubi C) :
  Karoubi_retraction X ∘ Karoubi_section X ≈ id.
Proof.
  exact (`2 (`2 X)).
Qed.

(* Section after retraction is the image under the embedding of the
   idempotent e, viewed as an endomorphism of (x, id). *)
Lemma Karoubi_section_retraction {C : Category} (X : Karoubi C) :
  Karoubi_section X ∘ Karoubi_retraction X ≈ fmap[Karoubi_Embed] (`1 (`2 X)).
Proof.
  exact (`2 (`2 X)).
Qed.

(* Every morphism of the envelope factors through the embedding, conjugated
   by the retract structure of its endpoints. *)
Lemma Karoubi_factors {C : Category} {X Y : Karoubi C}
      (f : X ~{Karoubi C}~> Y) :
  f ≈ Karoubi_retraction Y ∘ fmap[Karoubi_Embed] (`1 f) ∘ Karoubi_section X.
Proof.
  simpl.
  rewrite (fst (`2 f)).
  rewrite (snd (`2 f)).
  reflexivity.
Qed.

Section KaroubiExtend.

Context {C D : Category}.
Context (G : C ⟶ D).
Context (S : IdempotentsSplit D).

(* The image under G of the idempotent carried by an object of Split(C) is
   again idempotent. *)
Lemma Extend_idem (X : Karoubi C) : Idempotent (fmap[G] (`1 (`2 X))).
Proof using All.
  constructor.
  rewrite <- fmap_comp.
  now rewrite (`2 (`2 X)).
Qed.

(* The chosen splitting in D of G e, for each object (x, e) of Split(C). *)
Definition Extend_split (X : Karoubi C) :=
  @split_of D S (G (`1 X)) (fmap[G] (`1 (`2 X))) (Extend_idem X).

Definition Extend_obj (X : Karoubi C) : D := `1 (Extend_split X).

Definition Extend_S (X : Karoubi C) :
  @SplitIdempotent D (G (`1 X)) (Extend_obj X) := `1 (`2 (Extend_split X)).

Definition Extend_agree (X : Karoubi C) :
  @split_idem D (G (`1 X)) (Extend_obj X) (Extend_S X) ≈ fmap[G] (`1 (`2 X))
  := `2 (`2 (Extend_split X)).

Definition Extend_r (X : Karoubi C) : G (`1 X) ~> Extend_obj X :=
  @split_idem_r D (G (`1 X)) (Extend_obj X) (Extend_S X).

Definition Extend_s (X : Karoubi C) : Extend_obj X ~> G (`1 X) :=
  @split_idem_s D (G (`1 X)) (Extend_obj X) (Extend_S X).

Lemma Extend_rs (X : Karoubi C) : Extend_r X ∘ Extend_s X ≈ id.
Proof using All.
  exact (@split_idem_rs D (G (`1 X)) (Extend_obj X) (Extend_S X)).
Qed.

Lemma Extend_sr (X : Karoubi C) :
  Extend_s X ∘ Extend_r X ≈ fmap[G] (`1 (`2 X)).
Proof using All.
  unfold Extend_s, Extend_r.
  rewrite (@split_idem_sr D (G (`1 X)) (Extend_obj X) (Extend_S X)).
  apply Extend_agree.
Qed.

(* Conjugating G e by the splitting collapses to the identity of the
   splitting object: r ∘ G e ∘ s ≈ r ∘ (s ∘ r) ∘ s ≈ (r ∘ s) ∘ (r ∘ s). *)
Lemma Extend_conjugate (X : Karoubi C) :
  Extend_r X ∘ fmap[G] (`1 (`2 X)) ∘ Extend_s X ≈ id.
Proof using All.
  rewrite <- Extend_sr.
  rewrite comp_assoc.
  rewrite Extend_rs.
  rewrite id_left.
  apply Extend_rs.
Qed.

(* The extension of G along the embedding: on objects, the chosen splitting
   object of G e; on morphisms, conjugation by the splitting data. *)
Definition Karoubi_Extend : Karoubi C ⟶ D.
Proof using All.
  refine {| fobj := Extend_obj
          ; fmap := fun X Y f => Extend_r Y ∘ fmap[G] (`1 f) ∘ Extend_s X |}.
  - (* fmap respects ≈, inherited from G *)
    intros X Y f g Hfg.
    cbn beta.
    simpl in Hfg.
    now rewrite Hfg.
  - (* identities: the identity of (x, e) is carried by e, and conjugating
       G e by the splitting collapses to id *)
    intros X.
    exact (Extend_conjugate X).
  - (* composition: the inner s ∘ r pair regenerates G e at the middle
       object, which is absorbed by the adjacent factor *)
    intros X Y Z f g.
    cbn beta.
    change (`1 (f ∘ g)) with (`1 f ∘ `1 g).
    rewrite fmap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (Extend_s Y) (Extend_r Y)).
    rewrite Extend_sr.
    rewrite (comp_assoc (fmap[G] (`1 (`2 Y))) (fmap[G] (`1 g))).
    rewrite <- fmap_comp.
    rewrite (fst (`2 g)).
    reflexivity.
Defined.

(* At an embedded object (x, id) the splitting of G id ≈ id makes the
   splitting object isomorphic to G x, with the section and retraction as
   the two directions. *)
Definition Karoubi_Extend_embed_iso (x : C) :
  Extend_obj (Karoubi_Embed x) ≅ G x.
Proof using All.
  refine {| to   := Extend_s (Karoubi_Embed x)
          ; from := Extend_r (Karoubi_Embed x) |}.
  - rewrite Extend_sr.
    exact (@fmap_id C D G x).
  - exact (Extend_rs (Karoubi_Embed x)).
Defined.

(* The extension restricts to G along the embedding, up to natural
   isomorphism (the ≈ of Functor_Setoid). *)
Theorem Karoubi_Extend_comm : Karoubi_Extend ◯ Karoubi_Embed ≈ G.
Proof using All.
  exists Karoubi_Extend_embed_iso.
  intros x y f.
  reflexivity.
Qed.

Section Uniqueness.

Context (H : Karoubi C ⟶ D).
Context (eqv : H ◯ Karoubi_Embed ≈ G).

(* The comparison maps between H (x, e) and G x, obtained from the retract
   presentation of (x, e) over the embedded object and the given
   identification of H ∘ Embed with G. *)
Definition extend_unique_u (X : Karoubi C) : H X ~> G (`1 X) :=
  to (`1 eqv (`1 X)) ∘ fmap[H] (Karoubi_section X).

Definition extend_unique_v (X : Karoubi C) : G (`1 X) ~> H X :=
  fmap[H] (Karoubi_retraction X) ∘ from (`1 eqv (`1 X)).

(* The coherence of the given identification, read as transporting the
   H-image of an embedded morphism across the isomorphism family. *)
Lemma extend_unique_transport {x y : C} (g : x ~> y) :
  fmap[H] (fmap[Karoubi_Embed] g)
    ≈ from (`1 eqv y) ∘ fmap[G] g ∘ to (`1 eqv x).
Proof using All.
  exact (`2 eqv x y g).
Qed.

(* u ∘ v ≈ G e: the section-retraction composite on the H side transports
   to G e across the isomorphism family. *)
Lemma extend_unique_u_v (X : Karoubi C) :
  extend_unique_u X ∘ extend_unique_v X ≈ fmap[G] (`1 (`2 X)).
Proof using All.
  unfold extend_unique_u, extend_unique_v.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[H] (Karoubi_section X))
                      (fmap[H] (Karoubi_retraction X))).
  rewrite <- fmap_comp.
  rewrite (Karoubi_section_retraction X).
  rewrite extend_unique_transport.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  rewrite id_right.
  rewrite comp_assoc.
  rewrite iso_to_from.
  apply id_left.
Qed.

(* v ∘ u ≈ id: the retraction-section composite is the identity of (x, e),
   which H preserves. *)
Lemma extend_unique_v_u (X : Karoubi C) :
  extend_unique_v X ∘ extend_unique_u X ≈ id.
Proof using All.
  unfold extend_unique_u, extend_unique_v.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (`1 eqv (`1 X))) (to (`1 eqv (`1 X)))).
  rewrite iso_from_to.
  rewrite id_left.
  rewrite <- fmap_comp.
  rewrite (Karoubi_retraction_section X).
  apply fmap_id.
Qed.

(* Conjugation by u and v recovers H on every morphism of the envelope,
   because every such morphism factors through the embedding. *)
Lemma extend_unique_v_fmap_u (X Y : Karoubi C) (f : X ~{Karoubi C}~> Y) :
  extend_unique_v Y ∘ fmap[G] (`1 f) ∘ extend_unique_u X ≈ fmap[H] f.
Proof using All.
  unfold extend_unique_u, extend_unique_v.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[G] (`1 f)) (to (`1 eqv (`1 X)))).
  rewrite (comp_assoc (from (`1 eqv (`1 Y)))
                      (fmap[G] (`1 f) ∘ to (`1 eqv (`1 X)))).
  rewrite (comp_assoc (from (`1 eqv (`1 Y))) (fmap[G] (`1 f))).
  rewrite <- extend_unique_transport.
  rewrite <- (fmap_comp (fmap[Karoubi_Embed] (`1 f)) (Karoubi_section X)).
  rewrite <- (fmap_comp (Karoubi_retraction Y)).
  rewrite (comp_assoc (Karoubi_retraction Y)
                      (fmap[Karoubi_Embed] (`1 f))
                      (Karoubi_section X)).
  rewrite <- (Karoubi_factors f).
  reflexivity.
Qed.

Definition extend_unique_to (X : Karoubi C) : H X ~> Extend_obj X :=
  Extend_r X ∘ extend_unique_u X.

Definition extend_unique_from (X : Karoubi C) : Extend_obj X ~> H X :=
  extend_unique_v X ∘ Extend_s X.

Lemma extend_unique_to_from (X : Karoubi C) :
  extend_unique_to X ∘ extend_unique_from X ≈ id.
Proof using All.
  unfold extend_unique_to, extend_unique_from.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (extend_unique_u X) (extend_unique_v X)).
  rewrite extend_unique_u_v.
  rewrite comp_assoc.
  apply Extend_conjugate.
Qed.

Lemma extend_unique_from_to (X : Karoubi C) :
  extend_unique_from X ∘ extend_unique_to X ≈ id.
Proof using All.
  unfold extend_unique_to, extend_unique_from.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (Extend_s X) (Extend_r X)).
  rewrite Extend_sr.
  rewrite <- (extend_unique_u_v X).
  rewrite <- comp_assoc.
  rewrite extend_unique_v_u.
  rewrite id_right.
  apply extend_unique_v_u.
Qed.

Definition extend_unique_iso (X : Karoubi C) : H X ≅ Extend_obj X.
Proof using All.
  refine {| to := extend_unique_to X; from := extend_unique_from X |}.
  - apply extend_unique_to_from.
  - apply extend_unique_from_to.
Defined.

(* Uniqueness of the extension: any functor H : Split(C) ⟶ D restricting to
   G along the embedding is naturally isomorphic to the chosen extension. *)
Theorem Karoubi_Extend_unique : H ≈ Karoubi_Extend.
Proof using All.
  exists extend_unique_iso.
  intros X Y f.
  symmetry.
  change (from (extend_unique_iso Y)) with (extend_unique_from Y).
  change (to (extend_unique_iso X)) with (extend_unique_to X).
  change (fmap[Karoubi_Extend] f)
    with (Extend_r Y ∘ fmap[G] (`1 f) ∘ Extend_s X).
  unfold extend_unique_to, extend_unique_from.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (Extend_s Y) (Extend_r Y)).
  rewrite Extend_sr.
  rewrite (comp_assoc (Extend_s X) (Extend_r X)).
  rewrite Extend_sr.
  rewrite (comp_assoc (fmap[G] (`1 f)) (fmap[G] (`1 (`2 X)))).
  rewrite <- fmap_comp.
  rewrite (snd (`2 f)).
  rewrite (comp_assoc (fmap[G] (`1 (`2 Y))) (fmap[G] (`1 f))).
  rewrite <- fmap_comp.
  rewrite (fst (`2 f)).
  rewrite comp_assoc.
  apply extend_unique_v_fmap_u.
Qed.

End Uniqueness.

End KaroubiExtend.

(* Cauchy completeness (for ordinary, Set-enriched categories) is precisely
   the splitting of idempotents. *)
Definition CauchyComplete (C : Category) := IdempotentsSplit C.

Section Cauchy.

Context {C : Category}.
Context (S : IdempotentsSplit C).

(* The chosen splitting in C of the idempotent carried by an object of the
   envelope. *)
Definition Karoubi_split (X : Karoubi C) :=
  @split_of C S (`1 X) (`1 (`2 X)) {| idem := `2 (`2 X) |}.

Definition Karoubi_split_obj (X : Karoubi C) : C := `1 (Karoubi_split X).

Definition Karoubi_split_S (X : Karoubi C) :
  @SplitIdempotent C (`1 X) (Karoubi_split_obj X) := `1 (`2 (Karoubi_split X)).

Definition Karoubi_split_agree (X : Karoubi C) :
  @split_idem C (`1 X) (Karoubi_split_obj X) (Karoubi_split_S X) ≈ `1 (`2 X)
  := `2 (`2 (Karoubi_split X)).

(* The section of the splitting carries a morphism from the embedded
   splitting object to (x, e): e ∘ s ≈ (s ∘ r) ∘ s ≈ s ∘ (r ∘ s) ≈ s. *)
Definition Karoubi_eso_to (X : Karoubi C) :
  Karoubi_Embed (Karoubi_split_obj X) ~{Karoubi C}~> X.
Proof using All.
  exists (@split_idem_s C (`1 X) (Karoubi_split_obj X) (Karoubi_split_S X)).
  split.
  - rewrite <- (Karoubi_split_agree X).
    rewrite <- (@split_idem_sr C (`1 X) (Karoubi_split_obj X)
                  (Karoubi_split_S X)).
    rewrite <- comp_assoc.
    rewrite (@split_idem_rs C (`1 X) (Karoubi_split_obj X)
               (Karoubi_split_S X)).
    apply id_right.
  - apply id_right.
Defined.

(* The retraction of the splitting carries the inverse morphism:
   r ∘ e ≈ r ∘ (s ∘ r) ≈ (r ∘ s) ∘ r ≈ r. *)
Definition Karoubi_eso_from (X : Karoubi C) :
  X ~{Karoubi C}~> Karoubi_Embed (Karoubi_split_obj X).
Proof using All.
  exists (@split_idem_r C (`1 X) (Karoubi_split_obj X) (Karoubi_split_S X)).
  split.
  - apply id_left.
  - rewrite <- (Karoubi_split_agree X).
    rewrite <- (@split_idem_sr C (`1 X) (Karoubi_split_obj X)
                  (Karoubi_split_S X)).
    rewrite comp_assoc.
    rewrite (@split_idem_rs C (`1 X) (Karoubi_split_obj X)
               (Karoubi_split_S X)).
    apply id_left.
Defined.

(* The two carriers compose to e on (x, e) — its identity — and to id on the
   embedded splitting object, so each object of the envelope is isomorphic
   to an embedded one. *)
Definition Karoubi_Embed_eso_iso (X : Karoubi C) :
  Karoubi_Embed (Karoubi_split_obj X) ≅[Karoubi C] X.
Proof using All.
  assert (Hsr :
    @split_idem_s C (`1 X) (Karoubi_split_obj X) (Karoubi_split_S X)
      ∘ @split_idem_r C (`1 X) (Karoubi_split_obj X) (Karoubi_split_S X)
      ≈ `1 (`2 X)).
  { rewrite (@split_idem_sr C (`1 X) (Karoubi_split_obj X)
               (Karoubi_split_S X)).
    apply Karoubi_split_agree. }
  refine {| to := Karoubi_eso_to X; from := Karoubi_eso_from X |}.
  - exact Hsr.
  - exact (@split_idem_rs C (`1 X) (Karoubi_split_obj X) (Karoubi_split_S X)).
Defined.

Definition Karoubi_Embed_EssentiallySurjective :
  EssentiallySurjective (@Karoubi_Embed C) := {|
  eso_obj := Karoubi_split_obj;
  eso_iso := Karoubi_Embed_eso_iso
|}.

(* When C already has split idempotents, the embedding into its Karoubi
   envelope is full, faithful and essentially surjective, hence an
   equivalence of categories: a Cauchy complete category is equivalent to
   its own free idempotent-splitting completion. *)
Theorem cauchy_complete_embed_equiv :
  EquivalenceOfCategories (@Karoubi_Embed C).
Proof using All.
  exact (@FF_ESO_Equivalence C (Karoubi C) (@Karoubi_Embed C)
           Karoubi_Embed_Full Karoubi_Embed_Faithful
           Karoubi_Embed_EssentiallySurjective).
Defined.

End Cauchy.
