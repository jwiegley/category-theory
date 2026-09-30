Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * Morphisms of monads, and the category of monads on C *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2 Exercise 3(a), printed p. 142
         (PDF p. 151) — maclane:VI.2:ex3; with §VI.1, printed pp. 138-139
         (PDF pp. 147-148), and §VII.3, printed p. 171 (PDF p. 179)
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
         monads")
   Paper: Eilenberg, Moore, "Adjoint functors and triples", Illinois
          Journal of Mathematics 9(3), 1965
   Paper: Street, "The formal theory of monads", Journal of Pure and
          Applied Algebra 2(2), 1972, pp. 149-168

   WHAT THE BOOK ASKS.  Exercise 3(a), read from the page image: "For
   monads ⟨T, η, μ⟩ and ⟨T', η', μ'⟩ on X, define a morphism θ of monads
   as a suitable natural transformation θ : T ⇝ T', and construct the
   category of all monads in X."  Part (b), the functor θ* between the
   categories of algebras, is Monad/Morphism/Algebra.v.  The exercise
   repeats a request of §VI.1, which ends on p. 139 with "We leave the
   reader to describe a morphism ⟨T, μ, η⟩ → ⟨T', μ', η'⟩ of monads (a
   suitable natural transformation T ⇝ T') and the category of all
   monads in a given category X."

   MAC LANE'S OWN ANSWER.  Two other pages settle what "suitable" and
   "the category of all monads" mean for him.  On p. 138: "All told, a
   monad in X is just a monoid in the category of endofunctors of X, with
   product × replaced by composition of endofunctors and unit set by the
   identity endofunctor."  In §VII.3, p. 171: "A morphism f : ⟨c, μ, η⟩ →
   ⟨c', μ', η'⟩ of monoids is an arrow f : c → c' such that fμ = μ'(f □ f)
   : c □ c → c', fη = η' : e → c'.  With these arrows, the monoids in B
   constitute a category Mon_B", and the table below it pairs the
   monoidal category ⟨C^C, ∘, Id⟩ with "Monads (cf. Chapter VI!)".  So
   Mac Lane's category of all monads in X is Mon_{X^X}, and a morphism is
   a transformation θ with θ ∘ μ = μ' ∘ (θ □ θ) and θ ∘ η = η', where
   θ □ θ is the horizontal composite of θ with itself.

   THIS FILE'S READING.  [MonadHom M M'] is a class over two monads on
   one category C, whose fields are Mac Lane's data and his two
   equations, with ≈ for his =: [mh_transform], a [Transform] T ⟹ T' of
   Theory/Natural/Transformation.v (the book's "suitable natural
   transformation"); [mh_ret], θ_x ∘ η_x ≈ η'_x (fη = η'); and
   [mh_join], θ_x ∘ μ_x ≈ μ'_x ∘ (θ_{T'x} ∘ T(θ_x)) (fμ = μ'(f □ f)).
   The factor θ_{T'x} ∘ T(θ_x) is the library's horizontal composite:
   [mh_join_hcompose] shows that it IS the component at x of
   [nat_hcompose θ θ], by [eq_refl].  Its other form,
   T'(θ_x) ∘ θ_{Tx}, equal by naturality, is [mh_join_nat].  Mac Lane's
   Mon_{X^X} is in the tree already: Theory/Algebra/Monoid/Hom.v's [Mon]
   over the endofunctor category [C, C] with Structure/Monoidal/
   Compose.v's composition tensor.  The functor from the category below
   into it, and the reading of [mh_join] as its multiplication law, are
   Monad/Morphism/Monoid.v.

   [Monads C] is the category: objects are the pairs (T; M) of an
   endofunctor and a [Monad] on it, arrows are [MonadHom]s, and two
   arrows are ≈ when their components are, which is literally the ≈ of
   [C, C] on [mh_transform] ([Monads_equiv_is_Fun_equiv], [eq_refl]).
   The identity has components [id] ([mh_id], [mh_id_component]) and
   composition is componentwise ([mh_compose], [mh_compose_component]);
   the category laws are C's, componentwise.  [Monads_Forget] forgets
   the monad structure into [C, C], sending θ to [mh_transform θ] on the
   nose, and it is faithful by conversion: the two ≈ coincide, so
   [Monads_Forget_Faithful] is the identity on proofs.  Fullness is not
   claimed.

   Why a field of type [Transform] and not a bare family of components
   with a naturality law.  The [Transform] is the book's phrase, and it
   lets [Monads_Forget] send θ to its transformation with no
   repackaging.  Monad/Transformer.v's [MonadTransformer] carries its
   [lift] as a bare family, with no naturality field.

   WHERE THE NOTION COMES FROM.  Eilenberg and Moore (op. cit.) built
   the category of algebras of a monad, then called a triple, and Mac
   Lane's §VI.2 follows them; his book leaves the morphisms to the reader,
   as quoted above.  Street (op. cit.) made monads, and their morphisms,
   2-categorical: a monad in any 2-category K, and a 2-category of monads
   in K.  nLab's section "The 2-category of monads" gives that
   definition, cites Street, remarks that the orientation of the
   transformation in a morphism of monads is a convention that authors
   choose differently, and specializes it, in its example "transformation
   of monads on a fixed category", to the notion of this file: a natural
   transformation between the underlying functors of two monads on one
   category, compatible with the units and the multiplications, a special
   case the page calls "of relevance notably for monads in computer
   science" (citing Moggi 1989, Def. 4.0.11).  The 2-category itself,
   with monads on different categories and 2-cells between morphisms, is
   not built here.

   In the tree, before this file existed, one functor between categories
   of algebras was built by hand, Instance/Fun/Action/Monad/BG.v's
   [BG_Act_EM] (#464), and the object part of another, Instance/SupLat/
   Free.v's [SL_induced_repack] (#466), whose functor that file does not
   build.  Each has the shape of the θ* of Monad/Morphism/Algebra.v for a
   morphism of monads with identity components.  Neither file is changed
   here; Instance/Fun/Action/Monad/BG/Morphism.v and Instance/SupLat/
   Free/Morphism.v state the two morphisms of monads and compare each
   with θ*.

   STRENGTHS.  By [eq_refl]: [mh_join_hcompose] (the right factor of
   [mh_join] is the horizontal composite), [mh_id_component],
   [mh_compose_component], [Monads_equiv_is_Fun_equiv] (the ≈ of
   [Monads C] is the ≈ of [C, C] on [mh_transform]),
   [Monads_Forget_obj] and [Monads_Forget_map] (the forgetful functor is
   the first projection on objects and [mh_transform] on arrows), and
   [Monads_Forget_comp_component] (its composition law at each
   component: both sides are φ_x ∘ θ_x).  At ≈: the laws of [MonadHom]
   and of [Monads C], [mh_join_nat], and the two functor laws of
   [Monads_Forget] between whole transformations.  Refused at [eq_refl],
   by conversion, each pinned in Test/ProbeMonadMorphism468.v with its
   positive controls:
   - the composition law between whole transformations (R18; control
     C37 at a component): the two [Transform]s have the same components
     and different naturality proofs, [mh_compose]'s chain against the
     obligation of the composite in [C, C];
   - [Monads_Forget] on an identity, compared with the identity of
     [C, C] even at a component (R6; controls C3 and C4): the identity
     of [Monads C] has components [id] and the identity of [C, C] is
     [nat_id], whose components are [fmap[T] id], and T is a variable,
     so the two do not reduce to one term.
   Both refusals stand in a copy of the dependency closure with every
   [Qed] turned into [Defined] and [Transparent Obligations] set
   (Instance/Sets.v keeping its [Qed]s, where that change is itself
   refused with a universe error), where Theory/Natural/Transformation.v's
   [nat_compose_obligation_1] reports "is transparent" and in the tree
   "is opaque": they are not opacity.

   UNIVERSES, read off [About].  [MonadHom@{o h}] over [Category@{o h h}],
   with [Monad@{o h}] at both ends and no constraint; [mh_join_nat],
   [mh_id] and [mh_compose] are [@{o h}] with the constraint list closed
   and empty.  They stay so because their proofs use no setoid
   [rewrite]: the same [mh_id] proved with [rewrite id_left] is
   [@{o h u}] with h < u (measured).  The two component readbacks are
   [@{o h}] with no constraint on Rocq 9.1, but their lists end with [+]:
   on Coq 8.19 and 8.20 a statement = between arrows of C also carries
   h <= eq.u0, the universe of the standard library's [eq], and a closed
   list refuses it (measured on both, at [mh_join_hcompose]); every
   readback of this file and of Monad/Morphism/Algebra.v states = and
   ends its list with [+].
   [mh_join_hcompose] adds s with h < s, the strict level of
   [nat_hcompose], whose own block states it.  [Monads@{o h m1 m2}] is
   [Category@{m1 m2 m2}], with its object and hom levels chosen
   independently, as [Fun]'s are, above o and h; it also carries
   o <= Projections.u0/u1 and h <= Projections.u0/u1, the universes of
   the sigma projections, which its [hom] applies to the objects.  A
   binder cannot name those, so its constraint list ends with [+].
   [Monads_equiv_is_Fun_equiv], [Monads_Forget] and the constants after
   it add u with h < u, the strict level of [Fun], whose own block states
   it ([u0 < u5]); [C, C] is taken at [Fun@{o h o h m1 m2 u}], the levels
   of [Monads C].  No [Set] and no equation occur.

   REQUIRE COST.  Only [Monads_equiv_is_Fun_equiv], [Monads_Forget], its
   readbacks and [Monads_Forget_Faithful] use Instance/Fun.v; its
   [Require] is kept here, with the category the functor forgets, rather
   than in a satellite.  Measured by a script over coqdep's output, this
   file's [Require] closure has 21 files, itself included, and 14 without
   that line: Instance/Fun.v brings seven, itself, Instance/Sets.v,
   Structure/Monoidal.v, Functor/Bifunctor.v, Construction/Product.v,
   Structure/Initial.v and Structure/Terminal.v.

   NOT DELIVERED.  Street's 2-category of monads, with monads on
   different categories and 2-cells.  Comonad morphisms, which duality
   would give as [MonadHom] on C^op with the two comonads exchanged.
   Isomorphisms of [Monads C] are not characterized, and fullness of
   [Monads_Forget] is not claimed.  The Kleisli functor induced by θ is
   not built. *)

(** ** Morphisms of monads *)

(* A transformation T ⟹ T' preserving the unit (Mac Lane's fη = η') and
   the multiplication (his fμ = μ'(f □ f)), the horizontal composite
   f □ f written in [nat_hcompose]'s form at x. *)

Class MonadHom@{o h | } {C : Category@{o h h}} {T T' : C ⟶ C}
      (M : @Monad C T) (M' : @Monad C T') := {
  mh_transform : T ⟹ T';
  mh_ret {x : C} : mh_transform x ∘ @ret C T M x ≈ @ret C T' M' x;
  mh_join {x : C} :
    mh_transform x ∘ @join C T M x
      ≈ @join C T' M' x ∘ (mh_transform (T' x) ∘ fmap[T] (mh_transform x))
}.

Arguments mh_transform {C T T' M M'} _.
Arguments mh_ret {C T T' M M'} _ {x}.
Arguments mh_join {C T T' M M'} _ {x}.

(* The right factor of [mh_join] is the horizontal composite θθ. *)

Example mh_join_hcompose@{o h s | h < s +} {C : Category@{o h h}}
  {T T' : C ⟶ C} {M : @Monad C T} {M' : @Monad C T'}
  (θ : MonadHom@{o h} M M') (x : C) :
  transform[nat_hcompose@{s o o o h} (mh_transform θ) (mh_transform θ)] x
    = mh_transform θ (T' x) ∘ fmap[T] (mh_transform θ x) := eq_refl.

(* The other form of θθ, T'(θ_x) ∘ θ_{Tx}, by naturality of θ. *)

Lemma mh_join_nat@{o h | } {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  mh_transform θ x ∘ @join C T M x
    ≈ @join C T' M' x ∘ (fmap[T'] (mh_transform θ x) ∘ mh_transform θ (T x)).
Proof.
  etransitivity; [ apply (mh_join θ) | ].
  apply compose_respects; [ reflexivity | ].
  symmetry. apply (naturality (mh_transform θ)).
Qed.

(* Identity and composite.  The proofs are chains of [etransitivity],
   [compose_respects] and the associativity laws, with no setoid
   [rewrite], which would add a universe (see UNIVERSES above). *)

Definition mh_id@{o h | } {C : Category@{o h h}} {T : C ⟶ C}
  (M : @Monad C T) : MonadHom@{o h} M M.
Proof.
  unshelve refine {| mh_transform := Build_Transform'@{o h h o h h}
                       (F:=T) (G:=T) (fun x => id) _ |}.
  - intros x y f.
    transitivity (fmap[T] f); [ apply id_right | symmetry; apply id_left ].
  - intros x; cbn. apply id_left.
  - intros x; cbn.
    transitivity (@join C T M x); [ apply id_left | ].
    symmetry.
    transitivity (@join C T M x ∘ id); [ | apply id_right ].
    apply compose_respects; [ reflexivity | ].
    transitivity (fmap[T] (@id C (T x))); [ apply id_left | apply fmap_id ].
Defined.

Example mh_id_component@{o h | +} {C : Category@{o h h}} {T : C ⟶ C}
  (M : @Monad C T) (x : C) :
  mh_transform (mh_id@{o h} M) x = id := eq_refl.

Definition mh_compose@{o h | } {C : Category@{o h h}} {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M') :
  MonadHom@{o h} M M''.
Proof.
  unshelve refine {| mh_transform := Build_Transform'@{o h h o h h}
                       (F:=T) (G:=T'')
                       (fun x => mh_transform φ x ∘ mh_transform θ x) _ |}.
  - intros x y f; cbn.
    etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects;
          [ apply (naturality (mh_transform φ)) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity | apply (naturality (mh_transform θ)) ] | ].
    apply comp_assoc.
  - intros x; cbn.
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_ret θ) ] | ].
    apply (mh_ret φ).
  - intros x; cbn.
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_join θ) ] | ].
    etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects; [ apply (mh_join φ) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    apply compose_respects; [ reflexivity | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply comp_assoc ] | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity
          | apply compose_respects;
              [ apply (naturality (mh_transform θ)) | reflexivity ] ] | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply comp_assoc_sym ] | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity
          | apply compose_respects;
              [ reflexivity | symmetry; apply fmap_comp ] ] | ].
    apply comp_assoc.
Defined.

Example mh_compose_component@{o h | +} {C : Category@{o h h}}
  {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M') (x : C) :
  mh_transform (mh_compose@{o h} φ θ) x
    = mh_transform φ x ∘ mh_transform θ x := eq_refl.

(** ** The category of monads on C *)

(* Objects are monads, arrows are morphisms of monads, and ≈ compares
   components, as the ≈ of [C, C] does. *)

Definition Monads@{o h m1 m2 | o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) : Category@{m1 m2 m2}.
Proof.
  unshelve refine
    {| obj := { T : C ⟶ C & @Monad C T }
     ; hom := fun M N => MonadHom@{o h} (projT2 M) (projT2 N)
     ; homset := fun M N =>
         {| equiv := fun θ φ => ∀ x : C,
              @equiv _ (@homset C _ _) (mh_transform θ x) (mh_transform φ x) |}
     ; id := fun M => mh_id (projT2 M)
     ; compose := fun M N P φ θ => mh_compose φ θ |}.
  - constructor.
    + intros θ x. reflexivity.
    + intros θ φ E x. symmetry. apply E.
    + intros θ φ ψ E F x.
      transitivity (mh_transform φ x); [ apply E | apply F ].
  - intros M N P φ φ' Eφ θ θ' Eθ x; cbn.
    apply compose_respects; [ exact (Eφ x) | exact (Eθ x) ].
  - intros M N θ x; cbn. apply id_left.
  - intros M N θ x; cbn. apply id_right.
  - intros M N P Q f g k x; cbn. apply comp_assoc.
  - intros M N P Q f g k x; cbn. apply comp_assoc_sym.
Defined.

Example Monads_equiv_is_Fun_equiv@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +}
  (C : Category@{o h h}) (N N' : Monads@{o h m1 m2} C)
  (θ φ : N ~{Monads@{o h m1 m2} C}~> N') :
  @equiv _ (@homset (Monads@{o h m1 m2} C) N N') θ φ
    = @equiv _ (@homset (@Fun@{o h o h m1 m2 u} C C) (projT1 N) (projT1 N'))
        (mh_transform θ) (mh_transform φ) := eq_refl.

(** ** The forgetful functor into [C, C] *)

Definition Monads_Forget@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h}) :
  Monads@{o h m1 m2} C ⟶ @Fun@{o h o h m1 m2 u} C C.
Proof.
  unshelve refine
    (@Build_Functor (Monads@{o h m1 m2} C) (@Fun@{o h o h m1 m2 u} C C)
       (fun N : { T : C ⟶ C & @Monad C T } => projT1 N)
       (fun N N' θ => mh_transform θ) _ _ _).
  - intros N N' θ θ' E. exact E.
  - intros N x. simpl. symmetry. apply fmap_id.
  - intros N N' N'' φ θ x. simpl. reflexivity.
Defined.

Example Monads_Forget_obj@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N : Monads@{o h m1 m2} C) :
  fobj[Monads_Forget@{o h m1 m2 u} C] N = projT1 N := eq_refl.

Example Monads_Forget_map@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N N' : Monads@{o h m1 m2} C) (θ : N ~{Monads@{o h m1 m2} C}~> N') :
  fmap[Monads_Forget@{o h m1 m2 u} C] θ = mh_transform θ := eq_refl.

(* The composition law at a component: both sides are φ_x ∘ θ_x. *)

Example Monads_Forget_comp_component@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h})
  (N N' N'' : Monads@{o h m1 m2} C)
  (φ : N' ~{Monads@{o h m1 m2} C}~> N'')
  (θ : N ~{Monads@{o h m1 m2} C}~> N') (x : C) :
  transform[fmap[Monads_Forget@{o h m1 m2 u} C] (φ ∘ θ)] x
    = transform[fmap[Monads_Forget@{o h m1 m2 u} C] φ
                ∘ fmap[Monads_Forget@{o h m1 m2 u} C] θ] x := eq_refl.

(* Faithful by conversion: the hypothesis is already the conclusion. *)

Definition Monads_Forget_Faithful@{o h m1 m2 u |
  h < u, o <= m1, h <= m1, o <= m2, h <= m2 +} (C : Category@{o h h}) :
  Faithful (Monads_Forget@{o h m1 m2 u} C).
Proof. constructor. intros N N' θ θ' E. exact E. Defined.
