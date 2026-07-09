Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   An equivalence of categories is a functor F : C ⟶ D together with a
   quasi-inverse G : D ⟶ C whose composites with F are naturally isomorphic
   to the identity functors.  It is the standard weakening of isomorphism of
   categories, and the right notion of "sameness" for categories: it
   preserves and reflects all categorical structure.

   In this library the equivalence [≈] on functors ([Functor_Setoid],
   Theory/Functor.v) is *bundled natural isomorphism*: a family of
   isomorphisms [∀ x, F x ≅ G x] together with the conjugation coherence
   condition on morphisms.  The two comparison cells of an equivalence are
   therefore stated with [≈] directly:

     equivalence_counit : F ◯ quasi_inverse ≈ Id[D]
     equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F

   and, since the hom-setoid of [Cat] (Instance/Cat.v) is exactly
   [Functor_Setoid], an isomorphism in Cat *is* an equivalence of
   categories; the bridge [Equivalence_to_Cat_Iso]/[Cat_Iso_to_Equivalence]
   below repacks the data definitionally in both directions (witnessed up
   to [≈] by the two round-trip corollaries).  The bundled [≅[Fun]] forms
   of the two cells are recovered through [Functor_Setoid_Nat_Iso]
   (Instance/Fun.v): see [equivalence_counit_iso]/[equivalence_unit_iso]
   one way and [Nat_Isos_to_Equivalence] the other way.

   [EssentiallySurjective] is stated in the split, choice-carrying house
   style (compare [Full]'s chosen section [prefmap] in Theory/Functor.v and
   the split [surjective] class of Lib/Setoid.v): a chosen preimage object
   [eso_obj d] for every [d : D], together with a witnessing isomorphism
   [eso_iso d].  The classical characterization — full + faithful +
   essentially surjective is the same as being an equivalence — lives in
   Theory/Equivalence/FullFaithful.v; adjoint equivalences are developed in
   Theory/Equivalence/Adjoint.v; preservation, reflection and creation of
   limits along equivalences in Theory/Equivalence/Limit.v; the bundled
   notion [C ≃ D] in Theory/Equivalence/Bundled.v.

   NOTHING in this file is registered for instance resolution: a
   quasi-inverse is a choice, and must never be conjured by typeclass
   search (the [Monoidal_op] convention of Construction/Opposite/
   Monoidal.v).  All constructions below are plain Definitions, passed
   explicitly at use sites.  This also keeps the Cat-level universe
   constraints of the bridge conversions local to the places that actually
   use them. *)

(* F is essentially surjective (on objects) when every object of the target
   category is isomorphic to the image of some object of the source.  The
   witness is split: [eso_obj] chooses a preimage object and [eso_iso]
   exhibits the isomorphism. *)
Class EssentiallySurjective {C D : Category} (F : C ⟶ D) := {
  eso_obj : D → C;                     (* chosen preimage object *)
  eso_iso (d : D) : F (eso_obj d) ≅ d  (* its image is isomorphic to d *)
}.

(* F is an equivalence of categories when it has a quasi-inverse.  Both
   cells are natural isomorphisms, because [≈] on functors is
   [Functor_Setoid].  The orientation matches the adjunction every
   equivalence refines to (counit F ◯ G ⟹ Id[D], unit Id[C] ⟹ G ◯ F; see
   Theory/Equivalence/Adjoint.v). *)
Class EquivalenceOfCategories {C D : Category} (F : C ⟶ D) := {
  quasi_inverse : D ⟶ C;
  equivalence_counit : F ◯ quasi_inverse ≈ Id[D];
  equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F
}.

(* An equivalence of categories IS an isomorphism in Cat: Cat's hom-setoid
   is [Functor_Setoid], so the two inverse laws of the isomorphism are
   exactly the counit and unit cells.  This is kept as a Definition — never
   an Instance — both by the no-inferable-quasi-inverses rule and because
   it mentions [Cat], one universe level above C and D; as a Definition the
   extra constraints stay local to its use sites. *)
Definition Equivalence_to_Cat_Iso {C D : Category} {F : C ⟶ D}
  (E : EquivalenceOfCategories F) : C ≅[Cat] D :=
  @Build_Isomorphism Cat C D F (@quasi_inverse C D F E)
    (@equivalence_counit C D F E)
    (symmetry (@equivalence_unit C D F E)).

(* ... and conversely: a Cat-isomorphism repacks definitionally as an
   equivalence of categories carried by its [to] functor, quasi-inverted by
   its [from] functor. *)
Definition Cat_Iso_to_Equivalence {C D : Category} (iso : C ≅[Cat] D) :
  EquivalenceOfCategories (to iso) :=
  @Build_EquivalenceOfCategories C D (to iso) (from iso)
    (iso_to_from iso)
    (symmetry (iso_from_to iso)).

(* The two bridges compose to the identity, on the nose for the functor
   data (both corollaries hold by [reflexivity] on the components); the
   isomorphism-level statement is up to [≈] of isos in Cat, which compares
   exactly the [to]/[from] components. *)
Corollary Cat_Iso_to_Equivalence_to_Cat_Iso {C D : Category}
  (iso : C ≅[Cat] D) :
  Equivalence_to_Cat_Iso (Cat_Iso_to_Equivalence iso) ≈ iso.
Proof. split; reflexivity. Qed.

Corollary Equivalence_to_Cat_Iso_to_Equivalence {C D : Category}
  {F : C ⟶ D} (E : EquivalenceOfCategories F) :
  @quasi_inverse C D F (Cat_Iso_to_Equivalence (Equivalence_to_Cat_Iso E))
    ≈ @quasi_inverse C D F E.
Proof. reflexivity. Qed.

Section QuasiInverse.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context `{E : @EquivalenceOfCategories C D F}.

(* The counit and unit as bundled natural isomorphisms in the functor
   category — the [≈] to [≅[Fun]] direction of the round trip provided by
   [Functor_Setoid_Nat_Iso]. *)
Definition equivalence_counit_iso : F ◯ quasi_inverse ≅[Fun] Id[D] :=
  equiv_iso equivalence_counit.

Definition equivalence_unit_iso : Id[C] ≅[Fun] quasi_inverse ◯ F :=
  equiv_iso equivalence_unit.

(* Componentwise accessors: the pointwise isomorphism families carried by
   the two cells (their `1 projections). *)
Definition equivalence_counit_at (d : D) : F (quasi_inverse d) ≅ d :=
  `1 equivalence_counit d.

Definition equivalence_unit_at (x : C) : x ≅ quasi_inverse (F x) :=
  `1 equivalence_unit x.

(* Naturality of the unit and counit components, extracted from the
   conjugation coherence carried by [Functor_Setoid]'s ≈ (the helpers
   [fun_equiv_to_fmap]/[fun_equiv_fmap_from] of Theory/Functor.v). *)

Lemma equivalence_unit_to_natural {x y : C} (f : x ~> y) :
  to (equivalence_unit_at y) ∘ f
    ≈ fmap[quasi_inverse] (fmap[F] f) ∘ to (equivalence_unit_at x).
Proof. exact (fun_equiv_to_fmap equivalence_unit x y f). Qed.

Lemma equivalence_unit_from_natural {x y : C} (f : x ~> y) :
  f ∘ from (equivalence_unit_at x)
    ≈ from (equivalence_unit_at y) ∘ fmap[quasi_inverse] (fmap[F] f).
Proof. exact (fun_equiv_fmap_from equivalence_unit x y f). Qed.

Lemma equivalence_counit_to_natural {x y : D} (g : x ~> y) :
  to (equivalence_counit_at y) ∘ fmap[F] (fmap[quasi_inverse] g)
    ≈ g ∘ to (equivalence_counit_at x).
Proof. exact (fun_equiv_to_fmap equivalence_counit x y g). Qed.

Lemma equivalence_counit_from_natural {x y : D} (g : x ~> y) :
  fmap[F] (fmap[quasi_inverse] g) ∘ from (equivalence_counit_at x)
    ≈ from (equivalence_counit_at y) ∘ g.
Proof. exact (fun_equiv_fmap_from equivalence_counit x y g). Qed.

(* The conjugation form of unit naturality: the composite functor
   [quasi_inverse ◯ F] acts on morphisms by conjugation with the unit
   components. *)
Lemma equivalence_unit_conjugate {x y : C} (f : x ~> y) :
  fmap[quasi_inverse] (fmap[F] f)
    ≈ to (equivalence_unit_at y) ∘ f ∘ from (equivalence_unit_at x).
Proof.
  rewrite equivalence_unit_to_natural.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(* Symmetry: the quasi-inverse is itself an equivalence of categories,
   quasi-inverted by F.  The two cells swap roles, with their orientations
   flipped by symmetry of [≈]. *)
Definition EquivalenceOfCategories_sym :
  EquivalenceOfCategories quasi_inverse :=
  @Build_EquivalenceOfCategories D C quasi_inverse F
    (symmetry equivalence_unit)
    (symmetry equivalence_counit).

End QuasiInverse.

(* Packaging from bundled natural isomorphisms: a functor equipped with
   natural isomorphisms F ◯ G ≅ Id[D] and Id[C] ≅ G ◯ F in the functor
   category is an equivalence — the [≅[Fun]] to [≈] direction of the
   [Functor_Setoid_Nat_Iso] round trip. *)
Definition Nat_Isos_to_Equivalence {C D : Category} (F : C ⟶ D) (G : D ⟶ C)
  (counit_iso : F ◯ G ≅[Fun] Id[D]) (unit_iso : Id[C] ≅[Fun] G ◯ F) :
  EquivalenceOfCategories F :=
  @Build_EquivalenceOfCategories C D F G
    (Category.Instance.Fun.iso_equiv counit_iso)
    (Category.Instance.Fun.iso_equiv unit_iso).

(* The identity functor is an equivalence, quasi-inverse itself. *)
Definition EquivalenceOfCategories_Id {C : Category} :
  EquivalenceOfCategories Id[C] :=
  @Build_EquivalenceOfCategories C C Id[C] Id[C]
    (fun_equiv_id_left Id[C])
    (symmetry (fun_equiv_id_left Id[C])).
