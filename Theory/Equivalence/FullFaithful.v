Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   The classical characterization of equivalences: a functor F : C ⟶ D is an
   equivalence of categories exactly when it is full, faithful, and
   essentially surjective.  Both directions are constructive here, because
   the library's [Full] and [EssentiallySurjective] are the split,
   choice-carrying classes ([prefmap] is a chosen section of [fmap[F]];
   [eso_obj]/[eso_iso] a chosen preimage object with its witnessing
   isomorphism), so no choice principle is consumed: the quasi-inverse is
   assembled directly from the carried data.

   Forward direction ([FF_ESO_Equivalence]): the quasi-inverse
   [ff_eso_inverse] acts by [eso_obj] on objects, and on morphisms by
   conjugating with the [eso_iso] isomorphisms and then choosing a preimage
   with [prefmap].  [prefmap] carries no functoriality nor respectfulness of
   its own (see the issue #118 note in Theory/Functor.v), so every law of
   [ff_eso_inverse] is instead recovered from faithfulness: apply
   [fmap_inj], push [fmap[F]] through with [fmap_sur], and conclude among
   the images in D.  The counit of the resulting equivalence is literally
   the family [eso_iso]; the unit component at x is the [prefmap]-image of
   [eso_iso (F x)], inverted ([ff_eso_unit_iso]).

   Converse direction, given [E : EquivalenceOfCategories F]:

   - [Equivalence_Faithful]: injectivity of [fmap[F]] is read off the
     conjugation coherence of the unit cell ([`2 equivalence_unit]).
   - [Equivalence_Inverse_Faithful]: the same statement for the
     quasi-inverse, obtained through [EquivalenceOfCategories_sym] — which
     is exactly reading it off the counit cell.
   - [Equivalence_Full]: the chosen preimage of g : F x ~> F y is the
     unit-conjugate of [fmap[quasi_inverse] g] ([equivalence_prefmap]).
     The section law is the classical argument: the F-image of the
     preimage and g itself have the same image under the faithful
     [quasi_inverse], by naturality of the unit and cancellation of its
     componentwise isomorphisms ([iso_from_monic]/[iso_to_epic] from
     Theory/Isomorphism.v).
   - [Equivalence_EssSurj]: the preimage object of d is
     [quasi_inverse d], witnessed by the counit component
     [equivalence_counit_at d].

   Transparency: [FF_ESO_Equivalence], [Equivalence_Full] and
   [Equivalence_EssSurj] end in [Defined], because their content is data (a
   functor, a chosen section, a chosen preimage object), and downstream
   developments — Theory/Equivalence/Adjoint.v builds the adjunction of an
   adjoint equivalence directly from the [prefmap]/[eso_iso] data extracted
   here — need those components to reduce.  [Equivalence_Faithful] is pure
   proof and ends in [Qed].

   Following Theory/Equivalence.v, nothing in this file is registered for
   instance resolution: quasi-inverses, chosen sections and chosen preimage
   objects are choices, always passed explicitly at use sites. *)

(* The quasi-inverse assembled from a full, faithful, essentially
   surjective functor.  On objects it is the chosen preimage [eso_obj]; on
   morphisms it conjugates through the witnessing isomorphisms and takes
   the chosen [fmap]-preimage. *)
Program Definition ff_eso_inverse `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  D ⟶ C := {|
  fobj := eso_obj;
  fmap := fun d d' g => prefmap (from (eso_iso d') ∘ g ∘ to (eso_iso d))
|}.
Next Obligation.
  (* respectfulness of the morphism action, recovered from faithfulness *)
  proper.
  apply fmap_inj.
  rewrite !fmap_sur.
  now rewrites.
Qed.
Next Obligation.
  (* preservation of identities *)
  apply fmap_inj.
  rewrite fmap_sur, fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  (* preservation of composition: the middle [to ∘ from] pair cancels *)
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (to (eso_iso _)) (from (eso_iso _))).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(* The unit component at x : C, an isomorphism x ≅ eso_obj (F x).  Its two
   sides are the [prefmap]-images of the two sides of [eso_iso (F x)]; the
   inverse laws again go through [fmap_inj]/[fmap_sur]. *)
Program Definition ff_eso_unit_iso `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F}
  (x : C) : x ≅ eso_obj (F x) := {|
  to   := prefmap (from (eso_iso (F x)));
  from := prefmap (to (eso_iso (F x)))
|}.
Next Obligation.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  apply iso_from_to.
Qed.
Next Obligation.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  apply iso_to_from.
Qed.

(* The counit cell F ◯ ff_eso_inverse F ≈ Id[D].  Its isomorphism family
   is literally [eso_iso]; the conjugation coherence is exactly the
   section law [fmap_sur]. *)
Definition ff_eso_counit `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  F ◯ ff_eso_inverse F ≈ Id[D].
Proof.
  exists (fun d => eso_iso d).
  intros d d' g.
  exact (fmap_sur (from (eso_iso d') ∘ g ∘ to (eso_iso d))).
Defined.

(* Conjugation coherence of the unit cell, as a standalone (opaque) lemma:
   only the two [eso_iso (F −)] pairs cancel after pushing [fmap[F]]
   through with [fmap_sur]. *)
Lemma ff_eso_unit_coherence `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F}
  {x y : C} (f : x ~> y) :
  f ≈ from (ff_eso_unit_iso F y)
        ∘ fmap[ff_eso_inverse F ◯ F] f
        ∘ to (ff_eso_unit_iso F x).
Proof.
  apply fmap_inj.
  simpl.
  rewrite !fmap_comp, !fmap_sur.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(* The unit cell Id[C] ≈ ff_eso_inverse F ◯ F. *)
Definition ff_eso_unit `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  Id[C] ≈ ff_eso_inverse F ◯ F.
Proof.
  exists (fun x => ff_eso_unit_iso F x).
  intros x y f.
  exact (ff_eso_unit_coherence F f).
Defined.

(* The forward direction of the characterization: full + faithful +
   essentially surjective functors are equivalences of categories. *)
Theorem FF_ESO_Equivalence `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  EquivalenceOfCategories F.
Proof.
  exact (@Build_EquivalenceOfCategories C D F (ff_eso_inverse F)
           (ff_eso_counit F) (ff_eso_unit F)).
Defined.

(* The converse direction: every equivalence of categories is faithful,
   full, and essentially surjective. *)

Theorem Equivalence_Faithful `(E : @EquivalenceOfCategories C D F) :
  Faithful F.
Proof.
  constructor.
  intros x y f g Hfg.
  pose proof (`2 equivalence_unit x y f) as Hf; simpl in Hf.
  pose proof (`2 equivalence_unit x y g) as Hg; simpl in Hg.
  rewrite Hf, Hg.
  now rewrite Hfg.
Qed.

(* The quasi-inverse is likewise faithful: apply the same argument to the
   symmetric equivalence, i.e. read it off the counit cell. *)
Corollary Equivalence_Inverse_Faithful
  `(E : @EquivalenceOfCategories C D F) :
  Faithful (@quasi_inverse C D F E).
Proof.
  exact (Equivalence_Faithful (@EquivalenceOfCategories_sym C D F E)).
Qed.

(* The chosen preimage of g : F x ~> F y under [fmap[F]]: conjugate
   [fmap[quasi_inverse] g] with the unit components. *)
Definition equivalence_prefmap `(E : @EquivalenceOfCategories C D F)
  {x y : C} (g : F x ~> F y) : x ~> y :=
  from (equivalence_unit_at y)
    ∘ fmap[@quasi_inverse C D F E] g
    ∘ to (equivalence_unit_at x).

(* The section law: [fmap[F] (equivalence_prefmap E g)] and g have the
   same image under the faithful [quasi_inverse] — by the unit's
   conjugation coherence, after cancelling the monic [from] and epic [to]
   components of the unit isomorphism. *)
Lemma equivalence_prefmap_sur `(E : @EquivalenceOfCategories C D F)
  {x y : C} (g : F x ~> F y) :
  fmap[F] (equivalence_prefmap E g) ≈ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  symmetry.
  apply (monic (Monic := iso_from_monic (equivalence_unit_at y))).
  apply (epic (Epic := iso_to_epic (equivalence_unit_at x))).
  exact (`2 equivalence_unit x y (equivalence_prefmap E g)).
Qed.

Theorem Equivalence_Full `(E : @EquivalenceOfCategories C D F) : Full F.
Proof.
  exact (@Build_Full C D F
           (fun x y g => equivalence_prefmap E g)
           (fun x y g => equivalence_prefmap_sur E g)).
Defined.

Theorem Equivalence_EssSurj `(E : @EquivalenceOfCategories C D F) :
  EssentiallySurjective F.
Proof.
  exact (@Build_EssentiallySurjective C D F
           (fun d => quasi_inverse d)
           (fun d => equivalence_counit_at d)).
Defined.
