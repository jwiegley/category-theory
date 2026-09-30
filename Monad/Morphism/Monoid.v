Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Compose.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Fun.
Require Import Category.Monad.Morphism.

Generalizable All Variables.

(** * The category of monads is Mac Lane's Mon_{C^C} *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2 Exercise 3(a), printed p. 142
         (PDF p. 151) — maclane:VI.2:ex3; with §VI.1, printed
         pp. 138-139 (PDF pp. 147-148), and §VII.3, printed p. 171
         (PDF p. 179)
   nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
         monads")

   WHAT THE BOOK ASKS, AND WHAT IT MEANS BY IT.  Exercise 3(a), read from
   the page image, ends "and construct the category of all monads in X".
   The request repeats §VI.1, which on p. 139 leaves "the reader to
   describe a morphism ⟨T, μ, η⟩ → ⟨T', μ', η'⟩ of monads (a suitable
   natural transformation T ⇝ T') and the category of all monads in a
   given category X".  Two other pages give Mac Lane's own answer.  On
   p. 138: "All told, a monad in X is just a monoid in the category of
   endofunctors of X, with product × replaced by composition of
   endofunctors and unit set by the identity endofunctor."  In §VII.3,
   p. 171: "A morphism f : ⟨c, μ, η⟩ → ⟨c', μ', η'⟩ of monoids is an
   arrow f : c → c' such that fμ = μ'(f □ f) : c □ c → c', fη = η' :
   e → c'.  With these arrows, the monoids in B constitute a category
   Mon_B", and the table below it pairs the monoidal category
   ⟨C^C, ∘, Id⟩ with "Monads (cf. Chapter VI!)".  So, on the book's own
   terms, the category of all monads in X is Mon_{X^X}.
   Monad/Morphism.v builds a category [Monads C] directly, with objects
   the pairs of an endofunctor and a [Monad] on it and arrows its
   [MonadHom]s.  This file proves that category equivalent to Mac Lane's.

   MON_{C^C} IN THE TREE.  Theory/Algebra/Monoid/Hom.v's [Mon], the
   category of internal monoids and their homomorphisms, taken at
   Instance/Fun.v's endofunctor category [C, C] with Structure/Monoidal/
   Compose.v's [Compose_Monoidal]: the tensor of two endofunctors is
   their composite, the unit is [Id], and the tensor of two
   transformations is their horizontal composite, α(G'x) ∘ F(βx) at x.
   That category was in the tree when #468 was filed on 2026-07-23 (Hom.v
   since commit 4dd4c124 of 2026-07-05, Compose.v since 2017, by git log
   --follow), but nothing related it to Theory/Monad.v's [Monad].
   Monad/Monoid.v's [Monoid_Monad] is a different statement: a logical
   equivalence (↔) between a [Monad] and Structure/Monoid.v's
   [MonoidObject], another monoid class, on the same monoidal category,
   with no category of either.  Composed with Theory/Algebra/Monoid/
   Product.v's [Monoid_of_MonoidObject] and [MonoidObject_of_Monoid],
   which convert between the two monoid classes, it gives a second route
   to this file's object bridges: its monoid of a monad has μ and η equal
   to [monad_monoid]'s at each component, and its round trip keeps
   [ret], at [eq_refl] (the three pinned together as control C40 of
   Test/ProbeMonadMorphism468.v).  That route is not taken, because it
   costs eighteen modules: this file's [Require] closure has 28 files,
   itself included, and 46 with Monad/Monoid.v and Theory/Algebra/Monoid/
   Product.v added, among them those two, Structure/Monoid.v,
   Instance/Sets/Cartesian.v and nine Structure/Monoidal files (measured
   by a script over coqdep's output).

   OBJECTS.  [monad_monoid M] is the monoid of a monad: μ is [join] and
   η is [ret], each made a [Transform] from its naturality law
   ([join_fmap_fmap], [fmap_ret]), and the three monoid laws are the
   three monad laws once the identity components are cleared that the
   associator, the unitors and the identity of [C, C] insert (that
   identity is [nat_id], with components fmap[T] id).  [monoid_monad N]
   is the converse.  Both proofs, and every proof in this file, are
   chains of [etransitivity], [compose_respects] and the category laws
   with no setoid [rewrite], which would add a universe (Monad/
   Morphism.v measured h < u on its identity morphism).  The data round
   trip on the nose: the unit and multiplication of monoid_monad
   (monad_monoid M) are M's ([monoid_monad_ret], [monoid_monad_join]),
   and the components of μ and η of monad_monoid (monoid_monad N) are
   N's ([monad_monoid_mu_round], [monad_monoid_eta_round]).  The whole
   round trips are refused (below): the law fields are rebuilt.

   ARROWS.  The horizontal composite θ □ θ of [Compose_Monoidal] at x IS
   θ_{T'x} ∘ T(θ_x), the right factor of Monad/Morphism.v's [mh_join]
   ([mh_bimap_component], [eq_refl]).  More: the type of [mh_join],
   quantified over x, IS the type of Hom.v's multiplication square
   f ∘ μ ≈ μ' ∘ (f ⨂ f) at f = θ ([mh_join_is_hom_mu], an equation of
   types proved by [eq_refl]), and the type of [mh_ret] that of the unit
   triangle ([mh_ret_is_hom_eta]).  So [MonadHom]'s fields ARE Mac Lane's
   fμ = μ'(f □ f) and fη = η' at the in-tree tensor, by conversion, and
   the bridges are two [exact]s: [mh_monoidhom θ] is a [MonoidHom] on
   [mh_transform θ], and [monoidhom_mh] turns a [MonoidHom] on θ back
   into a [MonadHom] whose transformation is θ itself
   ([monoidhom_mh_transform], [eq_refl]).  The proof terms pass through
   unchanged: the multiplication square of [mh_monoidhom θ] at x IS
   [mh_join θ] at x, and the [mh_join] of [monoidhom_mh θ H] IS the
   square of H, both at [eq_refl] (controls C38 and C39 of
   Test/ProbeMonadMorphism468.v).

   THE FUNCTOR.  [Monads_Mon C : Monads C ⟶ Mon [C, C]] sends (T; M) to
   (T; monad_monoid M) and θ to (mh_transform θ; mh_monoidhom θ)
   ([Monads_Mon_obj], [Monads_Mon_map], both [eq_refl]).  It is faithful by
   conversion, since both categories compare arrows by the components of
   their transformations ([Monads_Mon_Faithful]); full, with [monoidhom_mh]
   as the chosen preimage ([Monads_Mon_Full]); and essentially surjective, a
   monoid (T; N) being isomorphic to the image of (T; monoid_monad N) by the
   transformation with identity components, in both directions
   ([Monads_Mon_ESO]).  Hence [Monads_Mon_Equivalence], an equivalence of
   categories by Theory/Equivalence/FullFaithful.v's [FF_ESO_Equivalence];
   Theory/Equivalence.v's [Equivalence_to_Cat_Iso] reads it as an
   isomorphism in Cat, whose ≈ of functors is natural isomorphism, with the
   object and hom levels of both categories taken at one level f: [About] of
   that application prints Monads@{o h f f} C ≅ Mon@{f f f t} [C, C].  The
   functor preserves composites on components by [eq_refl] (both sides are
   φ_x ∘ θ_x; a control in the probe) and identities at ≈ only: the identity
   of [Monads C] has components [id] (Monad/Morphism.v's [mh_id]), the
   identity of [Mon [C, C]] is [nat_id], with components fmap[T] id, and T
   is a variable functor.

   STRENGTHS.  By [eq_refl]: [monad_monoid_mu], [monad_monoid_eta], the four
   data round trips, [mh_bimap_component], the two equations of types
   [mh_join_is_hom_mu] and [mh_ret_is_hom_eta], [monoidhom_mh_transform],
   [Monads_Mon_obj] and [Monads_Mon_map].  At ≈: the monoid and monad laws,
   the functor laws of [Monads_Mon], its fullness and the isomorphisms of
   its essential surjectivity.  Refused at [eq_refl], by conversion, each
   pinned in Test/ProbeMonadMorphism468.v with its positive controls:
   [Monads_Mon] on an identity against the identity of [Mon [C, C]], at a
   component (id against fmap[T] id; R7, controls C21 to C23); monoid_monad
   (monad_monoid M) against M (R8, control C24); and monad_monoid
   (monoid_monad N) against N (R9, control C25).  All three stand in a copy
   of the probe's dependency closure with every [Qed] turned into [Defined]
   and [Transparent Obligations] set (Instance/Sets.v,
   Structure/Cartesian/Closed.v, Instance/Grp.v and Instance/Grp/Free.v
   keeping their [Qed]s, as in #464's measurement), with the same texts:
   they are not opacity.  The first compares [id] with a stuck projection of
   a variable functor, and the other two compare rebuilt law proofs with the
   projections of a variable [Monad] or [Monoid].

   UNIVERSES, read off [About].  Every bridge constant binds [@{o h f s}]
   with h < s, o <= f and h <= f, and takes [C, C] at
   [Fun@{o h o h f f s}]: object and hom level both f, because
   [Compose_Monoidal@{u u0 u1 u2}] is a [Monoidal@{u0 u0}], a monoidal
   structure on a category whose object and hom levels are one level;
   h < s is [Fun]'s own strict level ([u0 < u5] in its block).  The stdlib
   caps o, h, f <= projections.u0/u1 and h <= prod_rect.u0/u1/u2 are
   [Compose_Monoidal]'s, which its block states; a binder cannot name
   them, whence the trailing [+].  [mh_join_is_hom_mu] and
   [mh_ret_is_hom_eta] add q, with o < q, h < q and f <= q, the level
   of the [Type] in which their two types are compared.  [Monads_Mon] binds
   [@{o h m1 m2 f s mo t}]: [Monads@{o h m1 m2}] and [Mon@{f f mo t}],
   whose block states f < t and f <= mo; m2 <= f is Theory/Functor.v's
   [Functor] bound h1 <= h2; the sigma projections add the
   Projections.u0/u1 caps of both.  [Monads_Mon_Faithful],
   [Monads_Mon_Full] and [Monads_Mon_ESO] bind [@{o h m1 f s mo t}] and
   state their class at m2 := f, because Theory/Functor.v's [Faithful]
   and [Full] and Theory/Equivalence.v's [EssentiallySurjective] each
   give their two categories one hom level (measured: with m2 free, the
   faithfulness constant's block acquired the equation m2 = f).
   [Monads_Mon_Equivalence] adds e, with m1 <= e and f <= e, taking
   [EquivalenceOfCategories@{mo t e m1 mo f}], whose block states the
   remaining bounds.  No [Set] and no equation occur.

   NOT DELIVERED.  An isomorphism of categories on the nose, and the
   whole round trips of the two object bridges (refused above).  The
   2-categorical reading, Street's 2-category of monads with its
   2-cells, and the monoidal structure of [Monads C], are not built.
   The route through Monad/Monoid.v's [Monoid_Monad] (above) is measured
   against this file's bridges on components only; it is not made a
   functor. *)

(** ** Objects: a monad is a monoid in ⟨[C, C], ◯, Id⟩ *)

Definition monad_monoid@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) :
  @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T.
Proof.
  unshelve refine (@Build_Monoid (@Fun@{o h o h f f s} C C)
     (@Compose_Monoidal@{s f o h} C) T _ _ _ _ _).
  - exact (Build_Transform'@{o h h o h h} (F := T ◯ T) (G := T)
             (fun x => @join C T M x)
             (fun x y g => symmetry (join_fmap_fmap g))).
  - exact (Build_Transform'@{o h h o h h} (F := Id) (G := T)
             (fun x => @ret C T M x)
             (fun x y g => symmetry (fmap_ret g))).
  - intros x; simpl.
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects, fmap_respects, fmap_id | ].
      etransitivity; [ apply fmap_respects, fmap_id | ].
      apply fmap_id. }
    symmetry.
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    etransitivity; [ apply id_right | ].
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity;
        [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
      apply id_left. }
    apply join_fmap_join.
  - intros x; simpl.
    etransitivity; [ | symmetry; apply fmap_id ].
    etransitivity; [ | apply join_ret ].
    apply compose_respects; [ reflexivity | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    apply id_right.
  - intros x; simpl.
    etransitivity; [ | symmetry; apply fmap_id ].
    etransitivity; [ | apply join_fmap_ret ].
    apply compose_respects; [ reflexivity | ].
    etransitivity;
      [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
    apply id_left.
Defined.

Example monad_monoid_mu@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  transform[@mu _ _ _ (monad_monoid@{o h f s} M)] x = @join C T M x
  := eq_refl.

Example monad_monoid_eta@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  transform[@eta _ _ _ (monad_monoid@{o h f s} M)] x = @ret C T M x
  := eq_refl.

Definition monoid_monad@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C}
  (N : @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T) :
  @Monad C T.
Proof.
  unshelve refine (@Build_Monad C T
     (fun x => transform[@eta _ _ _ N] x)
     (fun x => transform[@mu _ _ _ N] x) _ _ _ _ _).
  - intros x y g. symmetry. exact (naturality[@eta _ _ _ N] _ _ g).
  - intros x.
    pose proof (@mu_assoc _ _ _ N x) as E; simpl in E.
    symmetry.
    etransitivity; [ | etransitivity; [ exact E | ] ].
    + symmetry.
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects, fmap_respects, fmap_id | ].
      etransitivity; [ apply fmap_respects, fmap_id | ].
      apply fmap_id.
    + etransitivity;
        [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
      etransitivity; [ apply id_right | ].
      apply compose_respects; [ reflexivity | ].
      etransitivity;
        [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
      apply id_left.
  - intros x.
    pose proof (@mu_unit_right _ _ _ N x) as E; simpl in E.
    etransitivity; [ | etransitivity; [ exact E | apply fmap_id ] ].
    apply compose_respects; [ reflexivity | ].
    symmetry.
    etransitivity;
      [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
    apply id_left.
  - intros x.
    pose proof (@mu_unit_left _ _ _ N x) as E; simpl in E.
    etransitivity; [ | etransitivity; [ exact E | apply fmap_id ] ].
    apply compose_respects; [ reflexivity | ].
    symmetry.
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    apply id_right.
  - intros x y g. symmetry. exact (naturality[@mu _ _ _ N] _ _ g).
Defined.

(* Round trips on the data, on the nose. *)

Example monoid_monad_ret@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  @ret C T (monoid_monad@{o h f s} (monad_monoid@{o h f s} M)) x
    = @ret C T M x := eq_refl.

Example monoid_monad_join@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C} (M : @Monad C T) (x : C) :
  @join C T (monoid_monad@{o h f s} (monad_monoid@{o h f s} M)) x
    = @join C T M x := eq_refl.

Example monad_monoid_mu_round@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C}
  (N : @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T)
  (x : C) :
  transform[@mu _ _ _ (monad_monoid@{o h f s} (monoid_monad@{o h f s} N))] x
    = transform[@mu _ _ _ N] x := eq_refl.

Example monad_monoid_eta_round@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T : C ⟶ C}
  (N : @Monoid (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) T)
  (x : C) :
  transform[@eta _ _ _ (monad_monoid@{o h f s} (monoid_monad@{o h f s} N))] x
    = transform[@eta _ _ _ N] x := eq_refl.

(** ** Arrows: [mh_join] IS fμ = μ'(f □ f) *)

(* The tensor of Compose_Monoidal on (θ, θ), at x. *)

Example mh_bimap_component@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  transform[@bimap _ _ _ (@tensor _ (@Compose_Monoidal@{s f o h} C))
              _ _ _ _ (mh_transform θ) (mh_transform θ)] x
    = mh_transform θ (T' x) ∘ fmap[T] (mh_transform θ x) := eq_refl.

(* The type of [mh_join], quantified over x, IS the type of the
   multiplication square of a monoid homomorphism. *)

Example mh_join_is_hom_mu@{o h f s q |
  h < s, o <= f, h <= f, o < q, h < q, f <= q +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @eq Type@{q}
    (∀ x : C, mh_transform θ x ∘ @join C T M x
                ≈ @join C T' M' x
                    ∘ (mh_transform θ (T' x) ∘ fmap[T] (mh_transform θ x)))
    (@compose (@Fun@{o h o h f f s} C C) _ _ _
       (mh_transform θ) (@mu _ _ _ (monad_monoid@{o h f s} M))
     ≈ @compose (@Fun@{o h o h f f s} C C) _ _ _
         (@mu _ _ _ (monad_monoid@{o h f s} M'))
         (@bimap _ _ _ (@tensor _ (@Compose_Monoidal@{s f o h} C))
            _ _ _ _ (mh_transform θ) (mh_transform θ))) := eq_refl.

Example mh_ret_is_hom_eta@{o h f s q |
  h < s, o <= f, h <= f, o < q, h < q, f <= q +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @eq Type@{q} (∀ x : C, mh_transform θ x ∘ @ret C T M x ≈ @ret C T' M' x)
  (@compose (@Fun@{o h o h f f s} C C) _ _ _
       (mh_transform θ) (@eta _ _ _ (monad_monoid@{o h f s} M))
     ≈ @eta _ _ _ (monad_monoid@{o h f s} M')) := eq_refl.

Definition mh_monoidhom@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @MonoidHom (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C)
    T T' (monad_monoid@{o h f s} M) (monad_monoid@{o h f s} M')
    (mh_transform θ).
Proof.
  constructor.
  - intros x. exact (mh_join θ).
  - intros x. exact (mh_ret θ).
Defined.

Definition monoidhom_mh@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : T ⟹ T')
  (H : @MonoidHom (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C)
         T T' (monad_monoid@{o h f s} M) (monad_monoid@{o h f s} M') θ) :
  MonadHom@{o h} M M'.
Proof.
  unshelve refine (@Build_MonadHom C T T' M M' θ _ _).
  - intros x. exact (@hom_eta _ _ _ _ _ _ _ H x).
  - intros x. exact (@hom_mu _ _ _ _ _ _ _ H x).
Defined.

Example monoidhom_mh_transform@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : T ⟹ T')
  (H : @MonoidHom (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C)
         T T' (monad_monoid@{o h f s} M) (monad_monoid@{o h f s} M') θ) :
  mh_transform (monoidhom_mh@{o h f s} θ H) = θ := eq_refl.

(** ** The functor Monads C ⟶ Mon [C, C] *)

Definition Monads_Mon@{o h m1 m2 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= f,
  o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) :
  Monads@{o h m1 m2} C
    ⟶ @Mon@{f f mo t} (@Fun@{o h o h f f s} C C)
        (@Compose_Monoidal@{s f o h} C).
Proof.
  unshelve refine
    (@Build_Functor (Monads@{o h m1 m2} C)
       (@Mon@{f f mo t} (@Fun@{o h o h f f s} C C)
          (@Compose_Monoidal@{s f o h} C))
       (fun N : { T : C ⟶ C & @Monad C T } =>
          (projT1 N; monad_monoid@{o h f s} (projT2 N)))
       (fun N N' (θ : MonadHom@{o h} (projT2 N) (projT2 N')) =>
          (mh_transform θ; mh_monoidhom@{o h f s} θ)) _ _ _).
  - intros N N' θ θ' E. exact E.
  - intros N x. simpl. symmetry. apply fmap_id.
  - intros N N' N'' φ θ x. simpl. reflexivity.
Defined.

Example Monads_Mon_obj@{o h m1 m2 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= f,
  o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N : Monads@{o h m1 m2} C) :
  fobj[Monads_Mon@{o h m1 m2 f s mo t} C] N
    = (projT1 N; monad_monoid@{o h f s} (projT2 N)) := eq_refl.

Example Monads_Mon_map@{o h m1 m2 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= f,
  o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) (N N' : Monads@{o h m1 m2} C)
  (θ : N ~{Monads@{o h m1 m2} C}~> N') :
  fmap[Monads_Mon@{o h m1 m2 f s mo t} C] θ
    = (mh_transform θ; mh_monoidhom@{o h f s} θ) := eq_refl.

Definition Monads_Mon_Faithful@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) :
  Faithful (Monads_Mon@{o h m1 f f s mo t} C).
Proof. constructor. intros N N' θ θ' E. exact E. Defined.

Definition Monads_Mon_Full@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) :
  Full (Monads_Mon@{o h m1 f f s mo t} C).
Proof.
  unshelve refine (@Build_Full _ _ (Monads_Mon@{o h m1 f f s mo t} C) _ _).
  - intros N N' g. exact (monoidhom_mh@{o h f s} (projT1 g) (projT2 g)).
  - intros N N' g x. simpl. reflexivity.
Defined.

(* Every monoid in ⟨[C, C], ◯, Id⟩ is, up to an isomorphism with
   identity components, the image of the monad it defines. *)

Definition Monads_Mon_ESO@{o h m1 f s mo t |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo +}
  (C : Category@{o h h}) :
  EssentiallySurjective (Monads_Mon@{o h m1 f f s mo t} C).
Proof.
  unshelve refine
    (@Build_EssentiallySurjective _ _ (Monads_Mon@{o h m1 f f s mo t} C)
       (fun P => (projT1 P; monoid_monad@{o h f s} (projT2 P))) _).
  intros P.
  unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
  - exists (mh_transform (mh_id (monoid_monad@{o h f s} (projT2 P)))).
    constructor.
    + intros x; simpl.
      etransitivity; [ apply id_left | ].
      symmetry.
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply id_left | apply fmap_id ].
    + intros x; simpl. apply id_left.
  - exists (mh_transform (mh_id (monoid_monad@{o h f s} (projT2 P)))).
    constructor.
    + intros x; simpl.
      etransitivity; [ apply id_left | ].
      symmetry.
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply id_left | apply fmap_id ].
    + intros x; simpl. apply id_left.
  - intros x; simpl.
    etransitivity; [ apply id_left | ].
    symmetry. apply fmap_id.
  - intros x; simpl.
    etransitivity; [ apply id_left | ].
    symmetry. apply fmap_id.
Defined.

Definition Monads_Mon_Equivalence@{o h m1 f s mo t e |
  h < s, f < t, o <= m1, h <= m1, o <= f, h <= f, f <= mo,
  m1 <= e, f <= e +}
  (C : Category@{o h h}) :
  EquivalenceOfCategories@{mo t e m1 mo f}
    (Monads_Mon@{o h m1 f f s mo t} C) :=
  @FF_ESO_Equivalence@{mo t e m1 mo f} _ _ (Monads_Mon@{o h m1 f f s mo t} C)
    (Monads_Mon_Full@{o h m1 f s mo t} C)
    (Monads_Mon_Faithful@{o h m1 f s mo t} C)
    (Monads_Mon_ESO@{o h m1 f s mo t} C).
