Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Transformer.
Require Import Category.Monad.Morphism.

Generalizable All Variables.

(** * Monad transformers are morphisms of monads *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2 Exercise 3(a), printed p. 142
         (PDF p. 151) — maclane:VI.2:ex3
   nLab: https://ncatlab.org/nlab/show/monad+transformer
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
         monads")

   WHAT IS PROVED.  Monad/Transformer.v's [MonadTransformer T], at a
   monad M on C and a monad on T M, carries a family
   lift_a : M a ~> T M a with two laws in the Kleisli form, [lift_return]
   (lift ∘ ret ≈ ret) and [lift_bind] (lift ∘ join ∘ fmap f ≈
   join ∘ fmap (lift ∘ f) ∘ lift).  Its header reads lift as "a monad
   morphism lift : M ⟹ T M", but the class has no naturality field and
   no law about [join] alone, and until this file the tree had no record
   of monad morphisms to measure the reading against.  With Monad/
   Morphism.v's [MonadHom], the reading is a theorem, in both directions:
   - [lift_natural]: lift is natural, from [lift_bind] at ret ∘ g,
     [lift_return] and the unit law [join_fmap_ret] of both monads;
   - [transformer_hom L : MonadHom M (T M)], whose transformation has the
     components of lift ([transformer_hom_lift], [eq_refl]); its unit law
     IS [lift_return], and its multiplication law is [lift_bind] at
     f = id, turned into Monad/Morphism.v's horizontal-composite form by
     [lift_natural] at lift_x;
   - [hom_transformer θ : MonadTransformer T] for any θ : MonadHom M
     (T M), whose lift has the components of θ ([hom_transformer_lift],
     [eq_refl]); [lift_return] IS [mh_ret], and [lift_bind] follows from
     Monad/Morphism.v's [mh_join_nat], the naturality of θ at f and
     [fmap_comp].
   The component families round trip on the nose, both ways
   ([transformer_round_trip], [hom_round_trip]).  The two records do not:
   hom_transformer (transformer_hom L) against L, and transformer_hom
   (hom_transformer θ) against θ, are refused at [eq_refl], because the
   laws are rebuilt proofs where the variable record has projections.
   So the transformer laws at one monad M are exactly a morphism of
   monads M ⟶ T M, up to the proofs of the laws: the "suitable natural
   transformation" of Mac Lane's exercise, specialized to the pair
   (M, T M).  This is the sense in which #468 asks for "generalizing the
   MonadTransformer laws".

   WHERE IT COMES FROM.  nLab's page "monad transformer", read through a
   fetch of the page, states the transformer condition in the return and
   bind form, which it attributes to Liang, Hudak and Jones (1995), and
   states it equivalent to lift's being a homomorphism of monads: a
   natural transformation of the underlying functors respecting the unit
   and the multiplication.  That equivalence is what this file checks at
   the library's definitions.  The same page makes a transformer, as used
   in functional programming, a pointed endofunctor on the category of
   monads, whose point is lift; the class here constrains T at one monad
   M only, and so is one component of such a point.

   ISSUE #468's PREMISE.  Its "Current state" says that [MonadTransformer]
   "packages the monad-morphism laws as `lift : M ⟹ T M`", citing the class
   by a line number.  The class has sat unchanged since before the issue was
   filed (its last commit, 83b38386, is of 2026-06-17, by git log), and lift
   was then, as now, a bare family with no naturality field: the premise was
   imprecise when filed, and [lift_natural] is the missing field, derived.

   STRENGTHS.  By [eq_refl]: [transformer_hom_lift], [hom_transformer_lift]
   and the two component round trips.  At ≈: [lift_natural] and the laws of
   both constructions.  Refused at [eq_refl], by conversion, pinned in
   Test/ProbeMonadMorphism468.v with the component round trips as controls
   (C26, C27): the two whole-record round trips (R10, R11).  Both stand in a
   copy of the probe's dependency closure with every [Qed] turned into
   [Defined] and [Transparent Obligations] set (Instance/Sets.v,
   Structure/Cartesian/Closed.v, Instance/Grp.v and Instance/Grp/Free.v
   keeping their [Qed]s), so they are not opacity: the rebuilt laws are
   compared with projections of the variable L or θ.

   UNIVERSES, read off [About].  [lift_natural], [transformer_hom] and
   [hom_transformer] bind [@{o h}] over [Category@{o h h}], at
   [MonadTransformer@{o h}] and [MonadHom@{o h}], with the constraint list
   closed and empty.  They stay so because no proof uses a setoid [rewrite]:
   measured on copies proved by [rewrite], [lift_natural] carries
   h <= prod_rect.u0/u1/u2, and each of the two constructions an extra
   universe u with h < u.  The four readbacks state = and end their lists
   with [+], for the bound on the standard library's [eq] that Coq 8.19 and
   8.20 add (Monad/Morphism.v's UNIVERSES paragraph).  No [Set], no strict
   bound and no equation occur.

   NOT DELIVERED.  The pointed endofunctor on [Monads C] of nLab's page:
   [MonadTransformer] does not ask T to act on morphisms of monads, and
   nothing here makes it.  Monad/Transformer.v's [MonadTransformerLaws]
   is not addressed: it sits inside a comment block of that file, so the
   tree has no such constant (a [Check] of it is refused, "not found",
   while [Check @MonadTransformer] is accepted).  Neither the class nor
   its instance [IdentityT_MonadTransformer] is changed. *)

(* [lift] is natural: [lift_bind] at ret ∘ g, then [lift_return]. *)

Lemma lift_natural@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) {x y : C} (g : x ~> y) :
  fmap[T M] g ∘ @lift C M HM T HT L x ≈ @lift C M HM T HT L y ∘ fmap[M] g.
Proof.
  pose proof (@lift_bind C M HM T HT L x y (@ret C M HM y ∘ g)) as E.
  (* the right side of E is fmap[T M] g ∘ lift x *)
  symmetry in E.
  etransitivity; [ | etransitivity; [ exact E | ] ].
  - symmetry.
    apply compose_respects; [ | reflexivity ].
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects | ].
      - etransitivity; [ apply comp_assoc | ].
        apply compose_respects; [ apply lift_return | reflexivity ].
      - apply fmap_comp. }
    etransitivity; [ apply comp_assoc | ].
    etransitivity; [ apply compose_respects; [ apply join_fmap_ret | ];
                     reflexivity | ].
    apply id_left.
  - etransitivity.
    { apply compose_respects; [ reflexivity | apply fmap_comp ]. }
    etransitivity; [ apply comp_assoc_sym | ].
    apply compose_respects; [ reflexivity | ].
    etransitivity; [ apply comp_assoc | ].
    etransitivity; [ apply compose_respects; [ apply join_fmap_ret | ];
                     reflexivity | ].
    apply id_left.
Qed.

(** ** A transformer gives a morphism of monads M ⟶ T M *)

Definition transformer_hom@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) : MonadHom@{o h} HM HT.
Proof.
  unshelve refine
    (@Build_MonadHom C M (T M) HM HT
       (Build_Transform'@{o h h o h h} (F:=M) (G:=T M)
          (fun x => @lift C M HM T HT L x)
          (fun x y g => lift_natural L g)) _ _).
  - intros x. exact (@lift_return C M HM T HT L x).
  - intros x; simpl.
    pose proof (@lift_bind C M HM T HT L (M x) x id) as E.
    etransitivity; [ | etransitivity; [ exact E | ] ].
    + symmetry.
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | apply fmap_id ].
    + etransitivity; [ apply comp_assoc_sym | ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply lift_natural ].
      apply compose_respects; [ | reflexivity ].
      apply fmap_respects. apply id_right.
Defined.

(* Its components are [lift], on the nose. *)

Example transformer_hom_lift@{o h | +} {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) (x : C) :
  mh_transform (transformer_hom@{o h} L) x = @lift C M HM T HT L x
  := eq_refl.

(** ** A morphism of monads M ⟶ T M satisfies the transformer laws *)

Definition hom_transformer@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (θ : MonadHom@{o h} HM HT) : @MonadTransformer C M HM T HT.
Proof.
  unshelve refine
    (@Build_MonadTransformer C M HM T HT (fun x => mh_transform θ x) _ _).
  - intros a. exact (mh_ret θ).
  - intros a b f.
    etransitivity;
      [ apply compose_respects; [ apply (mh_join_nat θ b) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity; [ | apply comp_assoc ].
    apply compose_respects; [ reflexivity | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity | symmetry; apply (naturality (mh_transform θ)) ] | ].
    etransitivity; [ apply comp_assoc | ].
    apply compose_respects; [ | reflexivity ].
    symmetry. apply fmap_comp.
Defined.

Example hom_transformer_lift@{o h | +} {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (θ : MonadHom@{o h} HM HT) (x : C) :
  @lift C M HM T HT (hom_transformer@{o h} θ) x = mh_transform θ x
  := eq_refl.

(* The two round trips, on the component family. *)

Example transformer_round_trip@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (L : @MonadTransformer C M HM T HT) (x : C) :
  @lift C M HM T HT (hom_transformer@{o h} (transformer_hom@{o h} L)) x
    = @lift C M HM T HT L x := eq_refl.

Example hom_round_trip@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (θ : MonadHom@{o h} HM HT) (x : C) :
  mh_transform (transformer_hom@{o h} (hom_transformer@{o h} θ)) x
    = mh_transform θ x := eq_refl.
