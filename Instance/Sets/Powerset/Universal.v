Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Theory.Subobject.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Theory.Universal.Element.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * A universal element for the contravariant power-set functor *)

(* nLab:      https://ncatlab.org/nlab/show/universal+element
   nLab:      https://ncatlab.org/nlab/show/subobject+classifier
   Wikipedia: https://en.wikipedia.org/wiki/Power_set

   Mac Lane asks (CWM 2nd ed., §III.1, Exercise 2, printed p. 59) for a
   universal element of the contravariant power-set functor, and the
   classical answer is the pair ⟨2, {1}⟩: every subset S ⊆ A is the
   preimage of the distinguished truth value under exactly one map
   A ⟶ 2.  Riehl states the same example (Category Theory in Context,
   2nd ed., §2.3 Example 2.3.6, printed p. 68) with an emphasis that is
   a correctness condition rather than a flourish: the universal element
   is the SUBSET {⊤} ∈ P(Ω) — an element of the functor's VALUE at Ω —
   and not the POINT ⊤ ∈ Ω, the isomorphism being the one that carries
   f : A ⟶ Ω to the subset f⁻¹(⊤) ⊆ A.  Awodey runs the same
   correspondence for Sets (Category Theory, §5.3 Example 5.14, printed
   pp. 104-106), where the punchline is that it is NATURAL in the object.

   The section-and-page coordinates and the one-line summaries of what
   those passages contain are reproduced from the catalogue entry of the
   issue this file answers (jwiegley/category-theory#311, items
   maclane:III.1:ex2, riehl:2.3:example6, awodey:5.3:example14); the
   printed texts were not consulted while writing the file, so every
   statement here about their content is the issue's characterization
   rather than a reading of the books.  The mathematics below stands on
   its own proofs.

   A CORRECTION TO THAT ISSUE'S ACCOUNT OF THE PRIOR ART, measured
   against the parent commit rather than restated from the issue.  Its
   "Current state" says the library has "no power-set functor on a
   set-like category with a III.1-style universal-element statement",
   which read as a claim about power-set functors would be wrong:
   Instance/Sets/Powerset.v (issue #227) already contains FOUR of them —
   [Powerset], [Powerset_op], [Powerset_Prop] and [Powerset_Prop_Lift] —
   and they are substantial.  Three separate things were genuinely
   absent, and they are what these files add:

     (a) a CONTRAVARIANT power-set functor at a SINGLE universe level.
         The donor's contravariant one, [Powerset_op], is
         [(Sets@{o so})^op ⟶ Sets@{so sso}] — its codomain is one
         universe up — and its one-level functor, [Powerset_Prop], is
         COVARIANT.  Neither shape can be the [H] of a universal element
         over [Sets], which needs [H : D ⟶ Sets] for the same [Sets].

     (b) a universal-element statement for ANY power-set functor: no
         [UniversalElement] or [AUniversalElement] anywhere in the tree
         mentioned one.

     (c) the natural-isomorphism upgrade of [classifier_classifies].
         That theorem was per-object, and [Sub] had never been exhibited
         as a representable presheaf.  The upgrade is
         Structure/SubobjectClassifier/Natural.v, delivered for an
         ARBITRARY [SubobjectClassifier] rather than only here.

   THE LEAD THE ISSUE DID NOT TAKE, AND WHY IT WORKS.  The issue proposes
   building this over [FinSet] "where it exists at one universe level",
   taking for granted that [Sets] does not.  [Sets] does.  The donor
   needed the impredicative truncation [Powerset_squash] because the
   DIRECT image has an existential ([λ y, ∃ x, S x ∧ f x ≈ y]) that must
   be squashed to land in [Prop].  The INVERSE image is [λ y, T (f y)]: a
   composition, with no quantifier introduced, so a [Prop]-valued subset
   pulls back to a [Prop]-valued subset with nothing to truncate.
   [Powerset_squash] therefore appears NOWHERE in the construction of
   [Powerset_Prop_op] below.  It reappears in the universal ELEMENT,
   because the donor's singleton is truncated uniformly, and later in the
   direct-image comparison and the subobject section; and at
   Ω that truncation is INERT, which is proved rather than asserted
   ([powerset_squash_prop_inert]: over a [Prop] the squash is
   interderivable with its argument, by impredicativity).  So the tree
   had built the hard half of the power-set story and left the easy half
   undone.

   The pay-off is that [Powerset_Prop_op] and its domain live in the SAME
   [Sets@{o so}], which is what [AUniversalElement (H : D ⟶ Sets) r]
   requires of [H].  Nothing here is a workaround: no cumulativity
   assumption, no disabled universe checking, no axiom.  Impredicativity
   of [Prop] is used exactly where the donor uses it and for the same
   reason — it is what puts a [Prop]-valued predicate setoid at the level
   of the carriers.

   ONE DONOR RESTRICTION BITES, AND IT IS MEASURED RATHER THAN GUESSED.
   [Theory/Universal/Element.v] records that [Yoneda_Lemma] — and hence
   [universal_element_yoneda] and [universal_element_representation] — is
   stated over [C : Category@{u0 u0 u0}], with object, hom and proof
   universes IDENTIFIED, so it cannot be instantiated at a category whose
   objects sit strictly above its homs.  [Sets@{o so} : Category@{so o o}]
   is exactly such a category: its objects live at [so] and its homs at
   [o], with [o < so] forced.  The Yoneda route is therefore unavailable
   here, and the refusal is a genuine universe inconsistency, of the form
   "Cannot enforce _ = _ because _ < _" naming the two anonymous levels;
   it is pinned in Test/ProbePowersetUniversal.v against a positive
   control that uses the direct route at the same arguments.  Everything
   below accordingly goes through the Yoneda-FREE constructions
   [ue_transform], [ue_representation] and [AUniversalElement_of_repr]
   that the donor file built for this situation.  This file is a second
   instance of that restriction (the first being Instance/Coq/Nat.v's
   [Endos]), not an escape from it.

   WHAT THIS FILE DELIVERS, AND AT WHICH STRENGTH.

     (1) [Powerset_Prop_op] — the CONTRAVARIANT power-set functor at ONE
         universe level, [(Sets@{o so})^op ⟶ Sets@{o so}], with subsets
         [Prop]-valued and the action the inverse image.

     (2) [Powerset_Prop_universal_element] — Mac Lane's §III.1 clause
         verbatim, through [Theory/Universal/Element.v]'s
         [AUniversalElement]: the pair ⟨Ω, {⊤}⟩, with Ω the level-o
         truth-value setoid and {⊤} the singleton subset of it.

     (3) Riehl's emphasis, machine-checked twice over: the universal
         element is TYPED as an element of [Powerset_Prop_obj Ω] rather
         than of Ω (the probe file pins the point's rejection in the
         element's position as a type error, against a control), and the
         forward leg of the representing isomorphism IS the preimage of
         {⊤}, by [eq_refl] ([powerset_representation_to_is_preimage]).

     (4) [Powerset_representation] — the representation
         [Hom ─,Ω] ≅ P as an isomorphism in [[Sets^op, Sets]], which is
         Awodey's naturality clause FOR THE POWER SET.  His naturality
         clause for the SUBOBJECT functor is a different statement about
         a different functor, and it is delivered separately, for an
         arbitrary [SubobjectClassifier], in
         Structure/SubobjectClassifier/Natural.v.

   HOW MUCH CONTENT IS IN THIS, STATED PLAINLY, because the packaging
   reads stronger than the mathematics.  In this library a [Prop]-valued
   subset of A IS a map A ~> Ω — the two types are equal by [eq_refl]
   ([powerset_subsets_are_maps]) — so the correspondence is not a
   bijection between two different things.  Its entire content is the
   single equivalence "membership in {⊤} detects truth"
   ([Powerset_truth_subset_intro] / [Powerset_truth_subset_elim]), and
   everything else is bookkeeping around those two lines.  The companion
   file Instance/FinSet/Powerset.v answers the same exercise where
   nothing is definitional — the power set of the n-element set is the
   2^n-element set, subsets are elements of it, and the correspondence
   computes — and the two files are deliberately both shipped for that
   contrast.

   WHAT THIS FILE DOES NOT DELIVER, STATED PLAINLY.  It does not produce
   a [SubobjectClassifier Sets] instance, and it does not claim
   [Powerset_Prop_obj A] and [SubObj A] are isomorphic.  The last section
   proves the half that is true — every [Prop]-valued subset is recovered
   from the subobject it names — and says exactly what blocks the other
   half.  See "The classifier obstruction is a different obstruction"
   below. *)

(* ------------------------------------------------------------------------ *)
(** ** The inverse image, and the contravariant functor *)

(* The inverse image of [T ⊆ X] along [f : Y ~> X] is [λ y, T (f y)] — the
   underlying predicate of [T] composed with the underlying function of
   [f].  Respectfulness is the two respectfulnesses composed. *)

Definition Powerset_Prop_preimage@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y X)
  (T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, T (f y)) _).
  intros y y' Hyy'.
  exact (@proper_morphism _ _ _ _ T (f y) (f y')
           (proper_morphism f _ _ Hyy')).
Defined.

(* Taking inverse images is itself a setoid map on subsets. *)
Definition Powerset_Prop_comap@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y X) :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (carrier (Powerset_Prop_obj@{o} Y)) (is_setoid (Powerset_Prop_obj@{o} Y))
       (λ T, Powerset_Prop_preimage@{o} f T) _).
  intros T U HTU y; exact (HTU (f y)).
Defined.

Lemma Powerset_Prop_comap_respects@{o} {X Y : SetoidObject@{o o}}
  (f g : SetoidMorphism@{o o o} Y X) (H : f ≈ g) :
  Powerset_Prop_comap@{o} f ≈ Powerset_Prop_comap@{o} g.
Proof.
  intros T y; split; intro Ht.
  - exact (proj1 (@proper_morphism _ _ _ _ T (f y) (g y) (H y)) Ht).
  - exact (proj2 (@proper_morphism _ _ _ _ T (f y) (g y) (H y)) Ht).
Qed.

(* [fmap_id] and [fmap_comp] are both a pair of identity implications: the
   inverse image along the identity is the subset itself ON THE NOSE as a
   predicate, and the inverse image along a composite is the iterated
   inverse image, again on the nose.  Only the setoid packaging keeps
   these from being [eq_refl]; the two [split; intro Ht; exact Ht] proofs
   below record exactly that. *)
Lemma Powerset_Prop_comap_id@{o} {X : SetoidObject@{o o}} :
  Powerset_Prop_comap@{o} (@setoid_morphism_id@{o o o} X)
    ≈ @setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X).
Proof. intros T x; split; intro Ht; exact Ht. Qed.

Lemma Powerset_Prop_comap_comp@{o} {X Y Z : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Z Y) (g : SetoidMorphism@{o o o} Y X) :
  Powerset_Prop_comap@{o} (@setoid_morphism_compose@{o o o} Z Y X g f)
    ≈ @setoid_morphism_compose@{o o o}
        (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
        (Powerset_Prop_obj@{o} Z)
        (Powerset_Prop_comap@{o} f) (Powerset_Prop_comap@{o} g).
Proof. intros T z; split; intro Ht; exact Ht. Qed.

(* THE CONTRAVARIANT POWER-SET FUNCTOR, at one level.  Compare
   [Powerset_op] of the donor file, whose codomain is [Sets] one universe
   up. *)
Definition Powerset_Prop_op@{o so} : @Functor (Sets@{o so})^op Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor (Sets@{o so})^op Sets@{o so}
       Powerset_Prop_obj@{o}
       (fun (X Y : SetoidObject@{o o}) (f : Y ~{Sets@{o so}}~> X) =>
          Powerset_Prop_comap@{o} f) _ _ _).
  - intros X Y f g H; exact (Powerset_Prop_comap_respects@{o} f g H).
  - intros X; exact (@Powerset_Prop_comap_id@{o} X).
  - intros X Y Z f g; exact (@Powerset_Prop_comap_comp@{o} X Y Z f g).
Defined.

(* [fmap[Powerset_Prop_op]] IS the inverse image: the two sides are the
   very same term, so the equality is Leibniz [=] rather than [≈].  This is
   the convertibility exception, on the Functor/Bifunctor.v:42-45
   precedent the donor file cites for its own five same-term lemmas. *)
Lemma Powerset_Prop_op_fmap_preimage@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_Prop_obj@{o} X)) :
  fmap[Powerset_Prop_op@{o so}] (f : X ~{(Sets@{o so})^op}~> Y) T
    = Powerset_Prop_preimage@{o} f T.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** Ω, the point ⊤, and the SUBSET {⊤} *)

(* The truth-value object is the donor's [Powerset_Prop_truth]: carrier
   [Prop], equivalence mutual implication.  It is named here so that the
   statements below read as Mac Lane and Riehl write them, and the
   identification is recorded by [eq_refl] so the name adds nothing. *)
Definition Powerset_Omega@{o} : SetoidObject@{o o} := Powerset_Prop_truth@{o}.

Example powerset_Omega_is_truth@{o} :
  Powerset_Omega@{o} = Powerset_Prop_truth@{o} := eq_refl.

(* The POINT ⊤ ∈ Ω. *)
Definition Powerset_truth_point@{o} : carrier Powerset_Omega@{o} := True.

(* The SUBSET {⊤} ∈ P(Ω).  This — not the point above — is Mac Lane's e
   and Riehl's universal element.  It is the donor's singleton predicate
   at the point, so nothing new is constructed; what is new is that it is
   the second component of a universal pair. *)
Definition Powerset_truth_subset@{o} :
  carrier (Powerset_Prop_obj@{o} Powerset_Omega@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=Powerset_Omega@{o})
    Powerset_truth_point@{o}.

Example powerset_truth_subset_is_singleton@{o} :
  Powerset_truth_subset@{o}
    = Powerset_Prop_singleton_pred@{o} (X:=Powerset_Omega@{o})
        Powerset_truth_point@{o} := eq_refl.

(* THE ELEMENT-VERSUS-POINT DISTINCTION, AT THE LEVEL OF TYPES.  The two
   live in different types, and the difference is not a matter of
   emphasis: [Powerset_truth_point] is a [carrier Powerset_Omega] and
   [Powerset_truth_subset] is a [carrier (Powerset_Prop_obj
   Powerset_Omega)].  Putting the point where the element belongs is a
   type error, and Test/ProbePowersetUniversal.v pins it as such against
   a positive control.  This lemma is the affirmative half: the two
   readings of "{⊤}" — the singleton subset, and the predicate "holds" —
   agree up to [≈] (and only up to [≈]; the strict form is refuted, and
   is pinned in the same probe file). *)

(* The predicate "P holds", as a subset of Ω. *)
Definition Powerset_holds@{o} :
  carrier (Powerset_Prop_obj@{o} Powerset_Omega@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       Prop (is_setoid Powerset_Omega@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ P : Prop, P) _).
  intros P Q [HPQ HQP]; split; assumption.
Defined.

(* THE ONE PIECE OF MATHEMATICAL CONTENT IN THE WHOLE CORRESPONDENCE, in
   isolation: the singleton subset {⊤} of Ω DETECTS TRUTH.  Membership of
   [P] in {⊤} unfolds to [Powerset_squash (True ≈ P)], and the two
   implications below say that this squashed pair of implications is
   interderivable with [P] itself.  Everything after this section is
   bookkeeping around these two lines.

   The elimination direction is where impredicativity of [Prop] earns its
   keep: [Powerset_squash A] is [∀ Q : Prop, (A → Q) → Q], so eliminating
   it into the [Prop] goal [P] is instantiation at [Q := P] — legal
   precisely because [P] is a [Prop].  (Into a [Type]-valued goal it would
   not be, which is the donor's own reason for the truncation.) *)

(* The truncation is INERT over a [Prop], which is the fact the header
   promises rather than asserts: [Powerset_squash A] is
   [∀ Q : Prop, (A → Q) → Q], so when A is itself a [Prop] the
   instantiation at [Q := A] recovers it.  This is what makes the donor's
   uniformly-truncated singleton usable at Ω, whose own equivalence is
   [Prop]-valued. *)
Lemma powerset_squash_prop_inert@{o} (P : Prop) :
  Powerset_squash@{o} P <-> P.
Proof.
  split.
  - intro H; exact (H P (fun p => p)).
  - exact (@Powerset_squash_intro@{o} P).
Qed.

Lemma Powerset_truth_subset_intro@{o} (P : Prop) (p : P) :
  Powerset_truth_subset@{o} P.
Proof. exact (Powerset_squash_intro@{o} (conj (fun _ => p) (fun _ => I))). Qed.

Lemma Powerset_truth_subset_elim@{o} (P : Prop) (H : Powerset_truth_subset@{o} P) :
  P.
Proof. exact (H P (fun q => proj1 q I)). Qed.

Lemma powerset_truth_subset_holds@{o} :
  Powerset_truth_subset@{o} ≈ Powerset_holds@{o}.
Proof.
  intro P; split.
  - exact (@Powerset_truth_subset_elim@{o} P).
  - exact (@Powerset_truth_subset_intro@{o} P).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** A subset of A IS a map A ⟶ Ω, definitionally *)

(* This library's [Prop]-valued subsets of [A] are, by construction,
   exactly the setoid maps [A ~> Ω]: both are
   [SetoidMorphism A Powerset_Prop_truth].  The identification is
   [eq_refl], and saying so up front is what keeps the universal property
   below honest — its content is NOT this type identification but the
   [≈]-level round trip of the next section, since the preimage of {⊤}
   along a map is NOT that map on the nose (the strict form is refuted in
   the probe file, and the reason is that the two records carry different
   respectfulness proofs). *)
Example powerset_subsets_are_maps@{o so} (A : SetoidObject@{o o}) :
  carrier (Powerset_Prop_obj@{o} A)
    = (A ~{Sets@{o so}}~> Powerset_Omega@{o}) := eq_refl.

(* The characteristic map of a subset is the subset, read across that
   identification. *)
Definition Powerset_char@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  A ~{Sets@{o so}}~> Powerset_Omega@{o} := S.

Example powerset_char_is_subset@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_char@{o so} S = S := eq_refl.

(* The preimage of {⊤} along [k], which is Riehl's f⁻¹(⊤). *)
Definition Powerset_preimage_of_truth@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  carrier (Powerset_Prop_obj@{o} A) :=
  Powerset_Prop_preimage@{o} k Powerset_truth_subset@{o}.

(* ... and it IS the action of the functor on the universal element, by
   [eq_refl].  The convertibility exception again. *)
Example powerset_preimage_is_fmap@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  fmap[Powerset_Prop_op@{o so}]
    (k : Powerset_Omega@{o} ~{(Sets@{o so})^op}~> A) Powerset_truth_subset@{o}
    = Powerset_preimage_of_truth@{o so} k := eq_refl.

(* The two round trips, at [≈].  Together they are the bijection Riehl
   describes, and each is exactly one half of the universal property
   assembled in the next section. *)
Lemma powerset_preimage_char@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_preimage_of_truth@{o so} (Powerset_char@{o so} S) ≈ S.
Proof.
  intro a; split.
  - exact (@Powerset_truth_subset_elim@{o} (S a)).
  - exact (@Powerset_truth_subset_intro@{o} (S a)).
Qed.

Lemma powerset_char_preimage@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  Powerset_char@{o so} (Powerset_preimage_of_truth@{o so} k) ≈ k.
Proof.
  intro a; split.
  - exact (@Powerset_truth_subset_elim@{o} (k a)).
  - exact (@Powerset_truth_subset_intro@{o} (k a)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Mac Lane's §III.1 universal element *)

(* Mac Lane's clause, read at [D := Sets^op] and [H := Powerset_Prop_op]:
   for every object A of [Sets] and every subset [S] of [A] there is a
   UNIQUE arrow [k : Ω ~{Sets^op}~> A] — that is, a unique setoid map
   [k : A ~> Ω] — with [(P k) {⊤} ≈ S], i.e. with [k⁻¹(⊤) ≈ S].  The
   witness is [S] itself, read as a map through the identification above;
   uniqueness is the observation that two maps whose preimages of {⊤}
   agree are pointwise mutually implying. *)
Definition Powerset_Prop_universal_element@{o so} :
  @AUniversalElement (Sets@{o so})^op Powerset_Prop_op@{o so}
    Powerset_Omega@{o}.
Proof.
  unshelve econstructor.
  - exact Powerset_truth_subset@{o}.
  - intros A S.
    unshelve econstructor.
    + exact (Powerset_char@{o so} S).
    + exact (powerset_preimage_char@{o so} S).
    + intros k Hk a; split.
      * intro Hs.
        exact (@Powerset_truth_subset_elim@{o} (k a) (proj2 (Hk a) Hs)).
      * intro Hka.
        exact (proj1 (Hk a) (@Powerset_truth_subset_intro@{o} (k a) Hka)).
Defined.

(* The element of the pair is {⊤}, and the mediating arrow of a subset is
   that subset — both by [eq_refl], so no reader has to trust the
   assembly above. *)
Example powerset_aue_elem@{o so} :
  @aue_elem (Sets@{o so})^op Powerset_Prop_op@{o so} Powerset_Omega@{o}
    Powerset_Prop_universal_element@{o so}
    = Powerset_truth_subset@{o} := eq_refl.

Example powerset_aue_med@{o so} (A : SetoidObject@{o o})
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  unique_obj (@aue_universal (Sets@{o so})^op Powerset_Prop_op@{o so}
                Powerset_Omega@{o} Powerset_Prop_universal_element@{o so} A S)
    = S := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** The representation, and Awodey's naturality for the power set *)

(* Through the Yoneda-FREE route of Theory/Universal/Element.v (see the
   header for why the Yoneda route is unavailable at [Sets]): the
   contravariant power-set functor is represented by Ω.  As a presheaf on
   [Sets], [@Curried_Hom (Sets^op) Ω] is [Hom_Sets(−, Ω)], the object the
   library writes [Hom ─,Ω]; the [eq_refl] below records that the two
   spellings are the same term. *)
Definition Powerset_representation@{o so} :
  @Curried_Hom (Sets@{o so})^op Powerset_Omega@{o}
    ≅[[(Sets@{o so})^op, Sets@{o so}]] Powerset_Prop_op@{o so} :=
  ue_representation Powerset_Prop_op@{o so} Powerset_Omega@{o}
    Powerset_Prop_universal_element@{o so}.

Example powerset_repr_source@{o so} :
  @Curried_Hom (Sets@{o so})^op Powerset_Omega@{o}
    = @Curried_CoHom Sets@{o so} Powerset_Omega@{o} := eq_refl.

(* RIEHL'S SENTENCE, MACHINE-CHECKED AT LEIBNIZ EQUALITY.  "The
   isomorphism sends f : A ⟶ Ω to the preimage f⁻¹(⊤) ⊆ A" is not a
   description of the forward leg up to [≈]; it IS the forward leg, term
   for term. *)
Example powerset_representation_to_is_preimage@{o so}
  (A : SetoidObject@{o o}) (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  transform (to Powerset_representation@{o so}) A k
    = Powerset_preimage_of_truth@{o so} k := eq_refl.

(* ... and the backward leg is the subset read as a map, again by
   [eq_refl]. *)
Example powerset_representation_from_is_char@{o so}
  (A : SetoidObject@{o o}) (S : carrier (Powerset_Prop_obj@{o} A)) :
  transform (from Powerset_representation@{o so}) A S
    = Powerset_char@{o so} S := eq_refl.

(* The bundled form.  [Representable] is [Functor/Representable.v]'s
   class; the representing object is Ω on the nose. *)
Definition Powerset_Prop_Representable@{o so} :
  Representable Powerset_Prop_op@{o so} :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement
       Powerset_Prop_universal_element@{o so}).

Example powerset_repr_obj@{o so} :
  @repr_obj (Sets@{o so})^op Powerset_Prop_op@{o so}
    Powerset_Prop_Representable@{o so}
    = Powerset_Omega@{o} := eq_refl.

(* Riehl's bijection packaged as an isomorphism of setoids in [Sets], with
   the forward map the preimage of {⊤} and the backward map the
   characteristic subset.  A DISCLOSURE about its strength, because the
   packaging reads stronger than it is: by [powerset_subsets_are_maps]
   the two setoids are the SAME object of [Sets], so what this
   isomorphism carries beyond [Powerset_representation] is exactly its
   two round-trip equations — not an identification of two different
   setoids.  It is stated because it is the shape Riehl's sentence has,
   and because the [to] field names the preimage map explicitly. *)
Definition powerset_truth_bijection@{o so} (A : SetoidObject@{o o}) :
  @Isomorphism Sets@{o so}
    {| carrier   := A ~{Sets@{o so}}~> Powerset_Omega@{o}
     ; is_setoid := @homset Sets@{o so} A Powerset_Omega@{o} |}
    (Powerset_Prop_obj@{o} A).
Proof.
  unshelve refine {| to := _ ; from := _ |}.
  - unshelve refine {| morphism := fun k => Powerset_preimage_of_truth@{o so} k |}.
    intros k k' Hk a.
    exact (@proper_morphism _ _ _ _ Powerset_truth_subset@{o} (k a) (k' a) (Hk a)).
  - unshelve refine {| morphism := fun S => Powerset_char@{o so} S |}.
    intros S S' HS a; exact (HS a).
  - intro S; exact (powerset_preimage_char@{o so} S).
  - intro k; exact (powerset_char_preimage@{o so} k).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity, and the degeneracies excluded by proof *)

(* Three ways this could have proved nothing, and the statement that
   excludes each.

   (1) A DEGENERATE Ω.  If ⊤ and ⊥ were identified in Ω, every subset
       would be everything and the universal property would be empty.
       [powerset_Omega_nondegenerate] refutes that.

   (2) A DEGENERATE UNIVERSAL ELEMENT.  If {⊤} were the empty subset of Ω
       or all of Ω, it would carry no information.  It is neither:
       [powerset_truth_subset_inhabited] and
       [powerset_truth_subset_proper].

   (3) A CONTRAVARIANT ACTION THAT IS SECRETLY THE COVARIANT ONE.  The
       inverse image and the direct image of the SAME morphism on the
       SAME subset are separated below, on a two-element carrier, by
       [powerset_inverse_ne_direct].

   Beyond those, the correspondence is exhibited computing on a concrete
   subset of a three-element setoid, and two distinct subsets are shown
   to have distinct characteristic maps. *)

Lemma powerset_Omega_nondegenerate@{o} :
  @equiv _ (is_setoid Powerset_Omega@{o}) Powerset_truth_point@{o} False
  → False.
Proof. intros [H _]; exact (H I). Qed.

Lemma powerset_truth_subset_inhabited@{o} :
  Powerset_truth_subset@{o} Powerset_truth_point@{o}.
Proof. exact (@Powerset_truth_subset_intro@{o} True I). Qed.

Lemma powerset_truth_subset_proper@{o} :
  Powerset_truth_subset@{o} False → False.
Proof. exact (@Powerset_truth_subset_elim@{o} False). Qed.

(* The three-element carrier, and two subsets of it.  [Powerset_Prop_truth]
   forces [Set < o], so the donor's universe-polymorphic
   [Powerset_Prop_fin_object] is the right carrier here (its own header
   records that this is the only reason it exists). *)

Definition powerset_fin3@{o} : SetoidObject@{o o} :=
  Powerset_Prop_fin_object@{o} 3.

Definition powerset_sub01@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin3@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 3) (is_setoid powerset_fin3@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ i : Fin.t 3, i = Fin.F1 \/ i = Fin.FS Fin.F1) _).
  intros x y Hxy; rewrite Hxy; split; intro H; exact H.
Defined.

Definition powerset_sub0@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin3@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 3) (is_setoid powerset_fin3@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ i : Fin.t 3, i = Fin.F1) _).
  intros x y Hxy; rewrite Hxy; split; intro H; exact H.
Defined.

(* The two subsets are genuinely different: 1 belongs to one and not the
   other. *)
Lemma powerset_sub01_ne_sub0@{o} :
  powerset_sub01@{o} ≈ powerset_sub0@{o} → False.
Proof.
  intro H.
  assert (H1 : @Fin.FS 2 Fin.F1 = Fin.F1)
    by exact (proj1 (H (Fin.FS Fin.F1)) (or_intror eq_refl)).
  discriminate H1.
Qed.

(* ... so their characteristic maps are different: the correspondence is
   not collapsing subsets. *)
Lemma powerset_chars_distinct@{o so} :
  Powerset_char@{o so} powerset_sub01@{o}
    ≈ Powerset_char@{o so} powerset_sub0@{o} → False.
Proof. exact powerset_sub01_ne_sub0@{o}. Qed.

(* The characteristic map takes the expected values: 0 and 1 are in, 2 is
   out. *)
Lemma powerset_char_at_0@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} Fin.F1.
Proof. exact (or_introl eq_refl). Qed.

Lemma powerset_char_at_1@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} (Fin.FS Fin.F1).
Proof. exact (or_intror eq_refl). Qed.

Lemma powerset_char_at_2@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} (Fin.FS (Fin.FS Fin.F1)) → False.
Proof. intros [H | H]; discriminate H. Qed.

(* The round trip on a concrete subset: pulling {⊤} back along the
   characteristic map of {0,1} returns {0,1}. *)
Lemma powerset_fin3_round@{o so} :
  Powerset_preimage_of_truth@{o so} (Powerset_char@{o so} powerset_sub01@{o})
    ≈ powerset_sub01@{o}.
Proof. exact (powerset_preimage_char@{o so} powerset_sub01@{o}). Qed.

(* The inverse image is not the direct image.  [powerset_const0] is the
   constant map at 0 on a two-element carrier, so both actions land in the
   same power set and can be compared; the direct image of {1} is {0},
   while its inverse image is empty. *)

Definition powerset_fin2@{o} : SetoidObject@{o o} :=
  Powerset_Prop_fin_object@{o} 2.

Definition powerset_const0@{o so} : powerset_fin2@{o} ~{Sets@{o so}}~> powerset_fin2@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 2) (is_setoid powerset_fin2@{o})
       (Fin.t 2) (is_setoid powerset_fin2@{o})
       (λ _, Fin.F1) _).
  intros x y _; reflexivity.
Defined.

Definition powerset_sng1@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin2@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=powerset_fin2@{o}) (Fin.FS Fin.F1).

Lemma powerset_inverse_sng1_empty@{o so} (i : Fin.t 2) :
  fmap[Powerset_Prop_op@{o so}]
    (powerset_const0@{o so} : powerset_fin2@{o} ~{(Sets@{o so})^op}~> powerset_fin2@{o})
    powerset_sng1@{o} i → False.
Proof.
  intro H; hnf in H.
  refine (H False _); intro Heq; discriminate Heq.
Qed.

Lemma powerset_direct_sng1_at_0@{o so} :
  fmap[Powerset_Prop@{o so}] powerset_const0@{o so} powerset_sng1@{o} Fin.F1.
Proof.
  hnf.
  apply Powerset_squash_intro@{o}.
  exists (Fin.FS Fin.F1); split.
  - apply Powerset_squash_intro@{o}; reflexivity.
  - reflexivity.
Qed.

Theorem powerset_inverse_ne_direct@{o so} :
  fmap[Powerset_Prop@{o so}] powerset_const0@{o so} powerset_sng1@{o}
    ≈ fmap[Powerset_Prop_op@{o so}]
        (powerset_const0@{o so}
           : powerset_fin2@{o} ~{(Sets@{o so})^op}~> powerset_fin2@{o})
        powerset_sng1@{o}
  → False.
Proof.
  intro H.
  exact (powerset_inverse_sng1_empty@{o so} Fin.F1
           (proj1 (H Fin.F1) powerset_direct_sng1_at_0@{o so})).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The classifier obstruction is a DIFFERENT obstruction *)

(* Instance/Sets/Classifier.v proves the subobject-classifier theorems for
   [Sets] as CROSS-UNIVERSE statements, and its header explains why: the
   characteristic predicate of a MONO [m : A ~> B] is
   [λ b, ∃ a, m a ≈ b], which is [Type@{o}]-valued because [≈] is, and
   [sets_char_pullback] and [sets_char_unique] must recover the witness
   [a] out of the truth value in order to mediate for a cone.  Truncating
   to [Prop] destroys exactly what they need.

   Nothing of the sort is asked of a power set.  Mac Lane's §III.1 clause
   asks only for a unique arrow with [(H k) e ≈ x], and above, the
   mediating arrow IS the subset — no witness is extracted from a truth
   value anywhere in [Powerset_Prop_universal_element].  That is why one
   level suffices here, and why the two results coexist without either
   weakening the other.

   READ THAT COMPARISON PRECISELY: NO IMPOSSIBILITY IS PROVED.  What is
   measured is that Classifier.v's construction consumes a witness and
   this one does not.  Whether some OTHER construction yields a one-level
   [SubobjectClassifier Sets] is not settled here — it was not attempted,
   and nothing below rules it out.  The issue asked for a note on why
   [Sets] may support only the cross-universe reading for the CLASSIFIER
   even where the power-set universal element works at one level; this
   paragraph is that note, and it is a note about a construction, not a
   theorem about the category.

   THE CONSEQUENCE, AND THE HONEST LIMIT.  This file does NOT produce a
   [SubobjectClassifier Sets] instance, and no such instance follows from
   what is proved here, because [SubobjectClassifier] classifies [SubObj]
   — monos up to isomorphism — not [Prop]-valued subsets.  The passage
   from a subset to a subobject is available and its round trip holds
   (both are proved immediately below); the passage back truncates the
   membership witness, and recovering it is the very step Classifier.v
   records as blocked.  So the composite in the other direction is left
   unproven and unclaimed here, rather than asserted in either
   direction. *)

(* A subset [S] of [A] names a subobject of [A]: the sub-setoid of
   elements satisfying [S], with the first projection.  Since membership
   is a [Prop] and the sub-setoid compares only first components, the
   projection is injective, hence monic. *)
Definition Powerset_subset_setoid@{o} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) : SetoidObject@{o o}.
Proof.
  unshelve refine
    {| carrier   := { a : carrier A & S a }
     ; is_setoid :=
         {| equiv := fun p q => @equiv _ (is_setoid A) (projT1 p) (projT1 q) |} |}.
  constructor.
  - intro p; reflexivity.
  - intros p q H; now symmetry.
  - intros p q r H K; now transitivity (projT1 q).
Defined.

Definition Powerset_subset_incl@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_setoid@{o} S ~{Sets@{o so}}~> A.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       { a : carrier A & S a } (is_setoid (Powerset_subset_setoid@{o} S))
       (carrier A) (is_setoid A)
       (λ p, projT1 p) _).
  intros p q Hpq; exact Hpq.
Defined.

Lemma Powerset_subset_incl_monic@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  @Monic Sets@{o so} _ _ (Powerset_subset_incl@{o so} S).
Proof.
  apply (injectivity_is_monic@{so o} (Powerset_subset_incl@{o so} S)).
  intros p q H; exact H.
Qed.

Definition Powerset_subobject_of_subset@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) : @SubObj Sets@{o so} A :=
  @Build_SubObj Sets@{o so} A
    (Powerset_subset_setoid@{o} S)
    (Powerset_subset_incl@{o so} S)
    (Powerset_subset_incl_monic@{o so} S).

(* ... and back: the truncated image of a mono is a [Prop]-valued subset.
   This is the step that discards the witness. *)
Definition Powerset_subset_of_subobject@{o so} {A : SetoidObject@{o o}}
  (u : @SubObj Sets@{o so} A) : carrier (Powerset_Prop_obj@{o} A).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier A) (is_setoid A) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ a, Powerset_squash@{o}
               (∃ p : carrier (sub_dom u),
                  @equiv _ (is_setoid A) (sub_mono u p) a)) _).
  intros a a' Haa'; split; intros H Q k; apply H; intros [p Hp]; apply k;
    exists p.
  - now transitivity a.
  - transitivity a'; [ exact Hp | now symmetry ].
Defined.

(* THE HALF THAT HOLDS: a subset is recovered from the subobject it names.
   Both directions stay inside [Prop], so the truncation is transparent
   here — which is exactly what is not true in the other order. *)
Theorem Powerset_subset_roundtrip@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so} (Powerset_subobject_of_subset@{o so} S)
    ≈ S.
Proof.
  intro a; split.
  - intro H; hnf in H.
    refine (H (S a) _); intros [[b Hb] Hba]; simpl in Hba.
    exact (proj1 (@proper_morphism _ _ _ _ S b a Hba) Hb).
  - intro Ha.
    hnf.
    apply Powerset_squash_intro@{o}.
    exists (existT _ a Ha); reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Where the rest of the exercise lives *)

(* Awodey's naturality clause for the SUBOBJECT functor —
   [Sub ≅ Hom(─,Ω)] in [[C^op, Sets]] for an arbitrary classifier — is
   Structure/SubobjectClassifier/Natural.v, and the same exercise answered
   where the correspondence is not definitional, over skeletal [FinSet]
   with Ω = 2 and everything computing, is Instance/FinSet/Powerset.v.
   Neither is restated here. *)
