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
   only up to natural isomorphism (not on-the-nose equality of object/morphism
   maps), an isomorphism in this [Cat] is an *equivalence* of categories rather
   than a strict isomorphism. Cat is the underlying 1-category of the strict
   2-category whose 2-cells are natural transformations; only the 1-category
   structure is built here.

   The strict counterpart — functors compared by on-the-nose equality of their
   object and morphism maps — is [Category.Instance.StrictCat.StrictCat]; the
   identity-on-objects comparison functor [StrictCat_to_Cat : StrictCat ⟶ Cat]
   of [Category.Instance.StrictCat.ToCat] exhibits the former as a refinement of
   the latter. Issue #138 discusses why the weak hom-equivalence is retained
   here (the Lawvere/comma characterisation of adjunctions, e.g.
   [Construction.Comma.Adjunction], genuinely needs [≅] in [Cat] to mean
   equivalence of categories). *)

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
