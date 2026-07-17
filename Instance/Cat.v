Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/Cat
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

   Cat is the category of all small categories:

    objects               Categories
    arrows                Functors
    arrow equivalence     Natural Isomorphisms
    identity              Identity Functor
    composition           Horizontal composition of Functors

    isomorphisms          Equivalences of Categories (caused by the definition
                          of [Functor_Setoid]).

   Size: Cat is a large category, and so cannot be an object of itself (there
   is no category of *all* categories). Here that constraint is enforced by
   universe polymorphism: [Category@{o h p | h <= p}] lives at a strictly
   higher universe than its objects, so the inner categories collected by
   [obj := Category] sit below the universe of [Cat] itself.

   Strict vs. weak: because the hom-setoid [Functor_Setoid] identifies functors
   whenever they are naturally isomorphic (not on-the-nose equal on objects and
   morphisms), an isomorphism in this [Cat] is an *equivalence* of categories.
   Identifying functors up to natural isomorphism makes this the homotopy
   category Ho(Cat) (the 1-truncation of the 2-category Cat), whose morphisms are
   natural-isomorphism classes of functors. It is therefore NOT the strict
   1-category of categories of the textbooks; and although it keeps the same
   objects, it is neither the *underlying* 1-category of the 2-category Cat
   (which keeps functor equality) nor its *core* (which keeps only the
   isomorphisms).

   This is deliberate, and consistent with the rest of the library: lacking
   function extensionality, the development compares morphisms up to a setoid
   equivalence [≈] rather than by Coq's intensional equality [=]. For [Cat] the
   morphisms are functors, and the corresponding [≈] is natural isomorphism —
   the equivalence-invariant notion of sameness for functors. So [Cat] applies
   the weaker notion of equivalence used everywhere else, lifted one level up, to
   suit Coq's metatheory.

   The reporter of issue #138 is right that the textbook bare-name "Cat" is the
   STRICT 1-category (functors compared by on-the-nose equality); that is
   [Category.Instance.StrictCat.StrictCat]. The choice here is not an error but a
   weaker, equivalence-invariant convention (cf. agda-categories' [Cats], whose
   functor equivalence is likewise natural isomorphism). The identity-on-objects
   comparison functor [StrictCat_to_Cat : StrictCat ⟶ Cat] of
   [Category.Instance.StrictCat.ToCat] sends each strict equality to the natural
   isomorphism it induces, exhibiting [StrictCat] as a strictification of this
   Ho(Cat). The weak hom-equivalence is moreover used substantively, not merely
   for phrasing: [Construction.Comma.Adjunction], for instance, builds an
   adjunction's unit and counit out of the *natural-isomorphism components* of a
   comma equivalence [≅[Cat]] — it takes the underlying morphism
   [from (`1 (iso_from_to lawvere_iso) x)] of such a component — which relies on
   [≅] in [Cat] being a natural isomorphism; a strict reformulation would be a
   genuinely different, transport-based construction rather than a rename.
   Conversely, the construction that cannot live over this
   [Cat] at all is the object-equality-dependent underlying-graph functor
   [Forgetful : StrictCat ⟶ Quiv] of issue #138, which does not respect natural
   isomorphism. *)

(* Where Cat comes from, and what it is for

   SEP:   https://plato.stanford.edu/entries/category-theory/
   nLab:  https://ncatlab.org/nlab/show/2-category
   nLab:  https://ncatlab.org/nlab/show/ETCC

   Cat is category theory applied to itself.  Every ingredient of the
   instance below is already implicit in the founding paper of the subject
   (Eilenberg and Mac Lane, "General theory of natural equivalences",
   Trans. Amer. Math. Soc. 58, 1945), yet the concept of a category of
   categories is nowhere mentioned there; the authors regarded categories
   as scaffolding — "the whole concept of a category is essentially an
   auxiliary one", the basic concepts being functor and natural
   transformation, with "the categories are provided as the domains and
   ranges of functors" (quoted in Marquis, "Category Theory", Stanford
   Encyclopedia of Philosophy).  The instance below is the structure that
   finally makes categories themselves the objects, so that the machinery
   of the theory can be turned on the theory itself.

   The dimension this 1-categorical instance truncates away has its own
   history.  Vertical and horizontal composition of natural
   transformations, with whiskering, first appear in the appendix of
   Godement's "Topologie algébrique et théorie des faisceaux" (1958),
   invented for the standard resolution of abelian sheaves; the Godement
   product is this library's [nat_hcompose] in
   Theory/Natural/Transformation.v.  Strict 2-categories are due to
   Bénabou ("Catégories relatives", 1965) and Maranda ("Formal
   categories", 1965) — not to Ehresmann, whose 1963 double categories
   were the inspiration — and Cat is the archetypical 2-category (nLab,
   "2-category").  Here the higher cells live in
   Instance/Cat/Bicategory.v, where the hom-categories are definitionally
   the functor categories of Instance/Fun.v.

   Lawvere proposed to make the self-application foundational: the
   category of categories itself, axiomatized in first-order terms, would
   replace membership-based set theory ("The Category of Categories as a
   Foundation for Mathematics", La Jolla Proceedings, Springer 1966,
   following his 1963 dissertation).  J. R. Isbell's review (Mathematical
   Reviews, 1967) found an error in a core result, no repair achieved
   consensus, and the programme was largely eclipsed by topos theory,
   though it has recent successors (Hughes and Miranda, arXiv:2403.03647,
   2025).  The size question it wrestled with is the one the header above
   settles by typing: a category of all categories invites a Russell-style
   paradox, classically avoided by the small/large distinction or by
   Grothendieck universes.  Rather than adopt either device axiomatically,
   this library has a [Cat] at every universe level, each strictly above
   its own objects, so self-membership is a universe inconsistency caught
   by the elaborator rather than a paradox to be excluded by axiom.

   It follows that categorical algebra now applies to categories
   themselves.  Binary products in [Cat] are the product categories
   ([Cat_Cartesian] in Instance/Cat/Cartesian.v), coproducts the
   disjoint-union categories (Instance/Cat/Cocartesian.v), the terminal
   and initial objects the one-object and empty categories ([Cat_Terminal]
   in Instance/One.v, [Cat_Initial] in Instance/Zero.v), and the
   exponentials the functor categories: [Cat_Closed] in
   Instance/Cat/Cartesian/Closed.v exhibits cartesian closure (detailed in
   Awodey, "Category Theory", 2010), with the transposition [exp_iso]
   currying a bifunctor into a functor-valued functor and evaluation the
   uncurried identity.  Read computationally, the exponentials are
   function objects one universe up, the picture behind higher-order
   manipulation of functors in typed functional programming (Milewski,
   "Natural Transformations", 2015) — though Cat is not locally cartesian
   closed (Wikipedia, "Category of small categories").  Within this file
   the weak convention yields concrete theorems: both legs of an
   isomorphism in [Cat] are faithful unconditionally
   ([Cat_Iso_to_Faithful], [Cat_Iso_from_Faithful]) and full under an
   explicit compatibility hypothesis between the unit and counit
   components ([Cat_Iso_to_Full], [Cat_Iso_from_Full]), the four
   assembled into [Isomorphism_FullyFaithful] by [Cat_Iso_FullyFaithful];
   the definitional bridge to equivalence of categories is
   [Equivalence_to_Cat_Iso] and [Cat_Iso_to_Equivalence] in
   Theory/Equivalence.v. *)

#[export]
Instance Cat : Category := {
  obj     := Category;
  hom     := @Functor;
  homset  := @Functor_Setoid;
  id      := @Id;
  compose := @Compose;

  compose_respects := @Compose_respects;
  id_left          := @fun_equiv_id_left;
  id_right         := @fun_equiv_id_right;
  comp_assoc       := @fun_equiv_comp_assoc;
  comp_assoc_sym   := fun a b c d f g h =>
    symmetry (@fun_equiv_comp_assoc a b c d f g h)
}.

Record Isomorphism_FullyFaithful `(iso : C ≅ D) := {
  to_full       : Full (to iso);
  to_faithful   : Faithful (to iso);
  from_full     : Full (from iso);
  from_faithful : Faithful (from iso)
}.

#[export]
Instance Cat_Iso_to_Faithful `(iso : C ≅ D) : Faithful (to iso).
Proof.
  construct.
  rewrite <- id_left.
  rewrite <- id_right.
  symmetry.
  rewrite <- id_left.
  rewrite <- id_right.
  symmetry.
  spose (`2 (iso_from_to iso) x y) as X2.
  transitivity (`1 (iso_from_to iso) y ∘ (`1 (iso_from_to iso) y)⁻¹ ∘ f
                 ∘ (`1 (iso_from_to iso) x ∘ (`1 (iso_from_to iso) x)⁻¹)).
  { repeat apply compose_respects.
    - symmetry. apply (iso_to_from (`1 (iso_from_to iso) y)).
    - reflexivity.
    - symmetry. apply (iso_to_from (`1 (iso_from_to iso) x)).
  }
  transitivity (`1 (iso_from_to iso) y ∘ (`1 (iso_from_to iso) y)⁻¹ ∘ g
                 ∘ (`1 (iso_from_to iso) x ∘ (`1 (iso_from_to iso) x)⁻¹)).
  2: {
    repeat apply compose_respects.
    - apply (iso_to_from (`1 (iso_from_to iso) y)).
    - reflexivity.
    - apply (iso_to_from (`1 (iso_from_to iso) x)).
  }
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ f _).
  rewrite (comp_assoc _ g _).
  rewrite (comp_assoc (_ ∘ _) _ _).
  rewrite (comp_assoc (_ ∘ _) _ _).
  rewrite <- (X2 f).
  rewrite <- (X2 g).
  comp_left.
  comp_right.
  now apply (@fmap_respects D C iso⁻¹).
Qed.

#[export]
Instance Cat_Iso_from_Faithful `(iso : C ≅ D) : Faithful (from iso).
Proof.
  apply (Cat_Iso_to_Faithful (iso_sym iso)).
Qed.

Section Cat_Iso_FullyFaithful.

#[local] Obligation Tactic := simpl; intros.

Program Definition Cat_Iso_to_Full `(iso : C ≅ D) :
  let φ := to iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  (∀ x, fmap[φ] (η x) ≈ μ (φ x)) ->
  Full (to iso) :=
  let φ := to iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  fun H0 =>
    {| prefmap x y g := to (`1 (iso_from_to iso) y)
                           ∘ fmap[from iso] g
                           ∘ from (`1 (iso_from_to iso) x)
    |}.
Next Obligation.
  rewrite !fmap_comp.
  srewrite H0.
  srewrite (`2 (iso_to_from iso)).
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  srewrite_r H0.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  transitivity (g ∘ id).
  - comp_left. rewrite iso_to_from. apply fmap_id.
  - apply id_right.
Qed.

End Cat_Iso_FullyFaithful.

Corollary Cat_Iso_from_Full `(iso : C ≅ D) :
  let ψ := from iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  (∀ x, fmap[ψ] (μ x) ≈ η (ψ x)) ->
  Full (from iso).
Proof.
  apply (Cat_Iso_to_Full (iso_sym iso)).
Qed.

Definition Cat_Iso_FullyFaithful `(iso : C ≅ D) :
  let φ := to iso in
  let ψ := from iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  (∀ x, fmap[φ] (η x) ≈ μ (φ x)) ->
  (∀ x, fmap[ψ] (μ x) ≈ η (ψ x)) ->
  Isomorphism_FullyFaithful iso :=
  fun H0 H1 =>
  {| to_full       := Cat_Iso_to_Full iso H0
   ; from_full     := Cat_Iso_from_Full iso H1
   ; to_faithful   := Cat_Iso_to_Faithful iso
   ; from_faithful := Cat_Iso_from_Faithful iso
   |}.
