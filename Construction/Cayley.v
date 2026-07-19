Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The Cayley representation of a category. *)

(* nLab: https://ncatlab.org/nlab/show/Cayley's+theorem
   nLab: https://ncatlab.org/nlab/show/Yoneda+embedding
   Wikipedia: https://en.wikipedia.org/wiki/Cayley%27s_theorem

   Cayley's theorem (group version) says every group G embeds into the
   symmetric group Sym(G) via left multiplication g ↦ (x ↦ g x); for a monoid
   M the same map g ↦ (x ↦ g · x) embeds M into the endofunction monoid
   (M → M, id, ∘).  Reading a category C as a many-object monoid, the
   corresponding statement is the covariant Yoneda embedding C ⟶ [C, Set]
   sending x to the corepresentable [Hom x,─], which is full and faithful.

   This file builds that embedding's image directly, without naming Sets or a
   functor category.  An object of Cayley is an object of C; a morphism
   x ~> y is the underlying data of a natural transformation
   [Hom y,─] ⟹ [Hom x,─] (post-composition acting on the left), namely a
   family

       f : ∀ r, (y ~> r) → (x ~> r)

   that is Proper in r and k and satisfies the naturality/representability
   law  f r k ≈ k ∘ f _ id, so every f is determined by the single morphism
   f _ id : x ~> y (this is the bijection of the Yoneda lemma).  Composition
   g ∘ f is r,k ↦ g r (f r k) and identity is r,k ↦ k; two morphisms are
   equivalent when they agree as functions, ∀ r k, `1 f r k ≈ `1 g r k.

   To_Cayley : C ⟶ Cayley and From_Cayley : Cayley ⟶ C below witness that this
   embedding is (split) faithful: From_Cayley (To_Cayley f) ≈ f.  Its point is
   that the round trip normalises composition.  Because each f is recovered as
   f _ id, a composite is always read back as a fully *left*-associated chain
   (… (id ∘ f) ∘ g) ∘ h regardless of how it was bracketed in Cayley; this is
   the categorical form of the "difference list" / Cayley-monoid trick, where
   a monoid is replaced by its endofunctions to reassociate · into ∘.  See
   Cayley_Right and Cayley_Left below. *)

(* Where the theorem comes from, and what the image is for

   Wikipedia: https://en.wikipedia.org/wiki/Cayley%27s_theorem
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   The theorem is named for Arthur Cayley, who in 1854 observed that a
   group of order n can be presented as a subgroup of the symmetric group
   on n letters (Cayley, "On the theory of groups, as depending on the
   symbolic equation θⁿ = 1", Philosophical Magazine 1854).  Cayley checked
   that the assignment of each element to its left multiplication is
   one-to-one, yet did not separately verify that it respects the group
   operation; the modern packaging as the left regular representation
   ℓ_g : x ↦ g x, an injective homomorphism into Sym(G), supplies that step
   (Wikipedia, "Cayley's theorem").  The name has been disputed — Burnside
   credited Camille Jordan, and Nummela defended the attribution to Cayley,
   who had made the result known roughly sixteen years before Jordan.  The
   statement also reaches past groups: the Wagner–Preston theorem embeds
   every inverse semigroup into a semigroup of partial bijections of a set
   (nLab, "Cayley's theorem").

   The many-object form is the Yoneda embedding, which Wikipedia describes
   as a vast generalisation of Cayley's theorem (Wikipedia, "Yoneda
   lemma"); at a one-object category it is exactly full faithfulness of the
   covariant embedding (Riehl, "Category Theory in Context", Dover 2016,
   Corollary 2.2.11).  That framing, together with the reading that an
   object is determined by its web of maps, is developed in
   Functor/Hom/Yoneda.v, whose [Covariant_Yoneda_Embedding] this file
   consumes and which points back here; Functor/Hom.v carries the abstract
   [Yoneda_Full] and [Yoneda_Faithful] that [Cayley] realizes as a concrete
   image.  The distinctive contribution here is that image on its own
   terms — a standalone category rather than a functor into Sets — with the
   classical one-object cases living in Structure/Group.v and in the monoid
   objects of Structure/Monoid.v and Theory/Algebra/Monoid.v.

   Read as programming, the reassociation that [Cayley_Right] and
   [Cayley_Left] record is the difference list (Hughes, "A novel
   representation of lists and its application to the function reverse",
   Information Processing Letters 1986).  A list l is represented by the
   function λ k, l ++ k, so that append becomes composition and the list is
   recovered by applying to the empty list; a left-nested chain of appends
   that would cost O(n²) is thereby run in O(n).  In the image this is the
   round trip: [To_Cayley] reifies a morphism as its post-composition
   action, the analogue of consing onto an accumulator, and [From_Cayley]
   runs the accumulated handler on the identity, the analogue of reading
   the list out.  Rather than stop at the free monoid, Rivas and Jaskelioff
   situate the pattern one level up, where monads, applicative functors,
   and arrows are monoids in monoidal categories and a monoid that is an
   exponent embeds into its endomorphism monoid; the difference list is the
   case of the free monoid on a type (Rivas and Jaskelioff, "Notions of
   Computation as Monoids", Journal of Functional Programming 2017).
   Structure/Monoid.v cites the same work, and the continuation-transformer
   reading of the morphism data ∀ r, (y ~> r) → (x ~> r) is drawn out in
   Functor/Hom/Yoneda.v.

   The construction also transports finite products.  [Cayley_Cartesian]
   carries a cartesian structure on C (Structure/Cartesian.v) onto [Cayley]
   by moving fork, exl, and exr across the covariant Yoneda isomorphism on
   hom-sets, and [To_Cayley_CartesianFunctor] and
   [From_Cayley_CartesianFunctor], over Functor/Structure/Cartesian.v,
   record that both the embedding and its retraction preserve it. *)

Section Cayley.

Context {C : Category}.

(* An object is just an object of C; a morphism x ~> y is the underlying
   transformation of [Hom y,─] ⟹ [Hom x,─], determined by f _ id (Yoneda). *)
Program Instance Cayley : Category := {
  obj     := C;
  hom     := fun x y =>
    { f : ∀ r, (y ~> r) → (x ~> r)          (* the post-composition action  *)
    & Proper (forall_relation (fun _ => respectful equiv equiv)) f ∧
      ∀ (r : C) (k : y ~> r), f r k ≈ k ∘ f _ id };  (* naturality / Yoneda  *)
  homset  := fun x y => {| equiv := fun f g => ∀ r k, `1 f r k ≈ `1 g r k |};
  id      := fun _ => (fun _ => Datatypes.id; _);
  compose := fun x y z f g  => (fun r k => `1 g r (`1 f r k); _)
}.
Next Obligation.
  equivalence.
  now rewrite X, X0.
Qed.
Next Obligation.
  split.
  - proper.
  - intros; cat.
Qed.
Next Obligation.
  split.
  - proper.
    apply p.
    apply p0.
    apply X.
  - intros.
    symmetry.
    rewrite e.
    rewrite comp_assoc.
    rewrite <- e0.
    rewrite <- e.
    reflexivity.
Qed.
Next Obligation.
  proper.
  simpl in *.
  rewrite H, H0.
  rewrite X.
  comp_left.
  apply X0.
Qed.

(* The embedding: f : x ~> y is sent to its post-composition action
   k ↦ k ∘ f, the corepresentable transformation [Hom y,─] ⟹ [Hom x,─]. *)
Program Instance To_Cayley : C ⟶ Cayley := {
  fobj := fun x => x;
  fmap := fun _ _ f => (fun _ k => k ∘ f; _);
}.
Next Obligation.
  proper.
  proper.
Defined.

(* The retraction: read a Cayley-morphism f back as the C-morphism f _ id,
   recovering the original by the Yoneda law.  From_Cayley ∘ To_Cayley = Id. *)
Program Instance From_Cayley : Cayley ⟶ C := {
  fobj := fun x => x;
  fmap := fun _ y f => `1 f y (@id C y);
}.

Context `{Cayley}.

(* No matter how we associate the mapped morphisms, the functor back from
   Cayley yields them left-associated. *)

Lemma Cayley_Right (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) :
  (∀ a b (k : a ~{C}~> b), id[b] ∘ k = k) ->
    f ∘ g ∘ h = fmap[From_Cayley]
                  (fmap[To_Cayley] f ∘ (fmap[To_Cayley] g
                                          ∘ fmap[To_Cayley] h)).
Proof.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

Lemma Cayley_Left (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) :
  (∀ a b (k : a ~{C}~> b), id[b] ∘ k = k) ->
    f ∘ g ∘ h = fmap[From_Cayley]
                  (((fmap[To_Cayley] f ∘ fmap[To_Cayley] g)
                      ∘ fmap[To_Cayley] h)).
Proof.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

(* The embedding transports any cartesian structure on C onto Cayley: products
   are the same objects, and fork/exl/exr are obtained by carrying C's
   universal arrows across the covariant Yoneda isomorphism on hom-sets. *)
Program Instance Cayley_Cartesian `{CA : @Cartesian C} : @Cartesian Cayley := {
  product_obj := @product_obj C CA;
  fork := fun x y z f g =>
    let f' := to (Covariant_Yoneda_Embedding C x y) (_ f) in
    let g' := to (Covariant_Yoneda_Embedding C x z) (_ g) in
    _ f' g';
  exl := fun x y =>
    let f' := from (Covariant_Yoneda_Embedding C _ _) (@exl C CA x y) in
    _ f';
  exr := fun x y =>
    let f' := from (Covariant_Yoneda_Embedding C _ _) (@exr C CA x y) in
    _ f';
}.
Next Obligation.
  construct.
  - construct.
    + apply f.
      exact X.
    + proper.
      rewrite e1.
      rewrite X.
      rewrite <- e1.
      reflexivity.
  - simpl.
    rewrite e1.
    rewrite comp_assoc.
    rewrite <- e1.
    reflexivity.
  - simpl.
    rewrite e1.
    rewrite <- comp_assoc.
    rewrite <- e1.
    reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + apply g.
      exact X.
    + proper.
      rewrite e0.
      rewrite X.
      rewrite <- e0.
      reflexivity.
  - simpl.
    rewrite e0.
    rewrite comp_assoc.
    rewrite <- e0.
    reflexivity.
  - simpl.
    rewrite e0.
    rewrite <- comp_assoc.
    rewrite <- e0.
    reflexivity.
Defined.
Next Obligation.
  exists (fun r h => h ∘ x0 △ x1).
  split.
  - proper.
  - intros; cat.
Defined.
Next Obligation.
  destruct x0; simpl in *.
  exists (fun r h => transform r h).
  split.
  - proper.
    now apply proper_morphism.
  - intros.
    rewrite naturality.
    apply proper_morphism; cat.
Defined.
Next Obligation.
  destruct x0; simpl in *.
  exists (fun r h => transform r h).
  split.
  - proper.
    now apply proper_morphism.
  - intros.
    rewrite naturality.
    apply proper_morphism; cat.
Defined.
Next Obligation.
  proper; simpl in *.
  comp_left.
  apply fork_respects.
  - apply X.
  - apply X0.
Qed.
Next Obligation.
  proper; simpl in *.
  - rewrite X.
    rewrite <- comp_assoc.
    rewrite exl_fork.
    rewrite <- e1.
    reflexivity.
  - rewrite X.
    rewrite <- comp_assoc.
    rewrite exr_fork.
    rewrite <- e0.
    reflexivity.
  - rewrite <- X, <- H0.
    rewrite e.
    comp_left.
    rewrite (e _ (_ ∘ exl)).
    rewrite (e _ (_ ∘ exr)).
    cat.
    rewrite fork_comp.
    rewrite fork_exl_exr.
    cat.
Qed.

End Cayley.

Require Import Category.Functor.Structure.Cartesian.

#[export]
Program Instance To_Cayley_CartesianFunctor `{@Cartesian C} :
  @CartesianFunctor _ _ To_Cayley _ Cayley_Cartesian.

#[export]
Program Instance From_Cayley_CartesianFunctor `{@Cartesian C} :
  @CartesianFunctor _ _ From_Cayley Cayley_Cartesian _.
