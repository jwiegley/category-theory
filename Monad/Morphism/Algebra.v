Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Morphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * θ*: the functor on algebras induced by a morphism of monads *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2 Exercise 3(b), printed p. 142
         (PDF p. 151) — maclane:VI.2:ex3; with §VI.2 Theorem 1, printed
         p. 140 (PDF p. 149)
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
         monads")
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category

   WHAT THE BOOK ASKS.  Exercise 3(b), read from the page image: "From θ
   construct a functor θ* : X^{T'} → X^T such that G^T ∘ θ* = G^{T'} and a
   natural transformation F^T ⇝ θ* ∘ F^{T'}."  Here θ : T ⇝ T' is a
   morphism of monads, part (a), which is Monad/Morphism.v's
   [MonadHom].  X^T, the forgetful G^T and the free F^T are those of
   Theorem 1 on p. 140, the adjunction ⟨F^T, G^T; η^T, ε^T⟩ : X ⇀ X^T;
   in the tree they are Monad/Eilenberg/Moore.v's [EilenbergMoore T] and
   Monad/Eilenberg/Moore/Adjunction.v's [EM_Forget T], [EM_Free T] and
   [EM_Adjunction].

   THE DIRECTION.  The page prints F^T ⇝ θ* ∘ F^{T'}: both sides are
   functors X → X^T, since F^{T'} lands in X^{T'} and θ* carries X^{T'}
   to X^T.  This file implements that direction ([mh_EM_free]).  Issue
   #468's body, filed on 2026-07-23 (gh createdAt), writes the
   transformation as "F^{T'} ⇒ θ* ∘ Fᵀ" in its "Current state" and as
   "Fᵀ' ⇒ θ* ∘ Fᵀ" in its "Work to be done"; that statement has been
   ill-typed since the issue was filed: θ* takes T'-algebras and F^T
   produces T-algebras.  Test/ProbeMonadMorphism468.v pins it as a
   TYPING refusal (R1), whose error, with the probe's name T2 for T', is
   "The term "EM_Free T" has type "C ⟶ EilenbergMoore T" while it is
   expected to have type "C ⟶ EilenbergMoore T2"".

   THE CONSTRUCTION.  A T'-algebra (a, h') becomes the T-algebra
   (a, h' ∘ θ_a) ([mh_algebra]).  Its unit law is [mh_ret] followed by
   [t_id]; its action law uses [mh_join], the naturality of θ, [t_action]
   and [fmap_comp].  An algebra map keeps its underlying arrow, and its
   square is the old one followed by the naturality of θ.  That is θ*,
   [mh_EM θ : EilenbergMoore T' ⟶ EilenbergMoore T].  The
   transformation F^T ⇝ θ* ∘ F^{T'} has at x the component θ_x, which is
   an algebra map from the free T-algebra (Tx, μ_x) to
   θ*(T'x, μ'_x) = (T'x, μ'_x ∘ θ_{T'x}); its square is [mh_join]
   reassociated ([mh_free_component]).  It is the transpose, along
   F^T ⊣ G^T, of η'_x : x → T'x = G^T θ* F^{T'} x: the component
   agrees at ≈ with [EM_extend] applied to η'
   ([mh_EM_free_transpose]), which reduces to θ_x by naturality of θ and
   the unit law [join_fmap_ret].

   THE BOOK'S "=".  Mac Lane writes G^T ∘ θ* = G^{T'}, an equation of
   functors.  It holds here in four forms, from the strongest down:
   - on objects, by [eq_refl], at each algebra ([mh_EM_forget_obj]) and
     as a function ([mh_EM_forget_obj_fun]), because [EM_Forget]'s
     object map is the first projection and θ* keeps the carrier;
   - on arrows, by [eq_refl] ([mh_EM_forget_map]);
   - as an equality in Theory/Functor.v's [Functor_StrictEq_Setoid], the
     setoid of functors that compares objects by = and arrows by ≈ after
     transport, with the object equation [eq_refl] at every algebra
     ([mh_EM_forget_strict]);
   - at Cat's ≈, the [Functor_Setoid] that Instance/Cat.v takes as its
     [homset] ([mh_EM_forget], [Defined]), whose isomorphisms are
     [iso_id], both legs [id] at [eq_refl] ([mh_EM_forget_iso_id]).
   As Leibniz equality of functors it is REFUSED, by conversion, and the
   probe pins it (R2): the data fields [fobj] and [fmap] convert (controls
   C10 and C11), and the three proof fields [fmap_respects], [fmap_id] and
   [fmap_comp] do not (R2a, R2b, R2c).  Each of the three is refused on
   its own, and all four refusals stand in a copy of this file's
   dependency closure in which every [Qed] was turned into [Defined] and
   [Transparent Obligations] was set, except Instance/Sets.v, whose [Qed]s
   stay because that change is itself refused there ("Universe ... is
   unbound"), with its obligations made transparent.  So the refusal is
   not opacity: the proof fields are different proofs of a [Type]-valued
   ≈, the composite's built by [Compose] from [EM_Forget]'s and θ*'s.

   FUNCTORIALITY IN θ.  θ ≈ θ' gives θ* ≈ θ'* ([mh_EM_respects]); the
   identity morphism gives the identity functor ([mh_EM_id]); and
   (φ ∘ θ)* ≈ θ* ◯ φ* ([mh_EM_compose]), so the assignment reverses
   composition.  [Monads_EM C : (Monads C)^op ⟶ Cat] packages the three.
   The three are [Defined], and each of their isomorphisms is built by
   [talg_same], the identity arrow between two algebra structures on one
   carrier whose structure maps are ≈: both legs have underlying arrow
   [id] at [eq_refl] ([mh_EM_respects_iso_id], [mh_EM_id_iso_id],
   [mh_EM_compose_iso_id]).  The laws hold at Cat's ≈ only: (id)* sends
   (a, h) to (a, h ∘ id), not to (a, h), and (φ ∘ θ)* sends it to
   (a, h ∘ (φ_a ∘ θ_a)), not to (a, (h ∘ φ_a) ∘ θ_a).  Both object
   equations are refused, by conversion, and pinned (R3, R4), with
   carriers, structure maps and underlying arrows at [eq_refl] as
   controls (C14 to C17); C is a variable category, so its [compose]
   does not reduce, and both refusals stand in the transparent copy
   above.

   WHERE IT SITS.  nLab's "The 2-category of monads" places a morphism of
   monads on one category among Street's morphisms of monads, and its
   remark on handedness records that the orientation of the
   transformation is a convention on which the direction of the induced
   functor between Kleisli categories depends.  For θ : T ⇝ T' as here,
   f : x → Ty goes to θ_y ∘ f, a functor from the Kleisli category of T
   to that of T', the opposite direction to θ*; it is not built here.
   (nLab's own wording, that under this orientation the association of
   monad morphisms to functors between Kleisli categories is
   contravariant, is not followed: the direction just given is this
   file's statement, read off the definition.)
   In the tree, before this file, one functor of this shape was built by
   hand for its instance, Instance/Fun/Action/Monad/BG.v's [BG_Act_EM]
   (#464), and the object part of another, Instance/SupLat/Free.v's
   [SL_induced_repack] (#466), whose functor Free.v does not build.  Each
   has the shape of θ* for a morphism of monads with identity components:
   it keeps carriers and underlying arrows.  Neither file is changed
   here; Instance/Fun/Action/Monad/BG/Morphism.v and Instance/SupLat/Free/
   Morphism.v compare each with θ*.  BG.v's readback
   [BG_Act_EM_alg] states, at [eq_refl], that its functor keeps the
   structure map h as a setoid morphism; for identity components θ*
   has h ∘ id there ([mh_EM_alg]), a composite in Sets, so that readback
   is not a statement about θ*.
   CORRECTION (#1347): since Instance/Sets.v gives its identity's and
   composite's properness fields as terms, h ∘ id converts with h in
   Sets, and that readback restated for θ* of Instance/Fun/Action/Monad/
   BG/Morphism.v's [BG_theta M] holds at [eq_refl]
   (Test/ProbeMonadMorphism468.v's R12, now a control).

   STRENGTHS.  By [eq_refl]: the carrier of θ* X ([mh_EM_carrier]), its
   structure map as h' ∘ θ_a ([mh_EM_alg]), the underlying arrow of
   θ* f ([mh_EM_hom]), the three G^T readbacks above, the object
   equations of [mh_EM_forget_strict], the G^T-image of each component
   of F^T ⇝ θ* ∘ F^{T'} as θ_x ([mh_EM_free_forget]), and [Monads_EM] on
   objects and arrows ([Monads_EM_obj], [Monads_EM_map]), and the legs
   of the isomorphisms of [mh_EM_forget] and of the three laws as [id]
   (the four [_iso_id] readbacks).  At ≈: [mh_EM_forget],
   [mh_EM_free_transpose], and the three functor laws of [Monads_EM].
   Refused, each pinned in Test/ProbeMonadMorphism468.v with its kind
   and its positive controls: the issue body's direction (R1, TYPING;
   controls C5 and C6, the page's direction); the Leibniz functor
   equation and its three proof fields (R2, R2a, R2b, R2c, CONVERSION;
   controls C7 to C12); the (id)* and (φ ∘ θ)* objects (R3, R4,
   CONVERSION; controls C14 to C17); the transpose at [eq_refl] (R5,
   CONVERSION; controls C13 and C18).  The controls C41 to C44 restate
   the four [_iso_id] readbacks.

   UNIVERSES, read off [About].  [mh_algebra] and [talg_same] are [@{o h}]
   with the constraint list closed and empty.  θ*, its readbacks and its
   laws bind [@{o h e s}] with h < s, o <= e and h <= e: exactly the block
   of [EilenbergMoore@{e o s h}], the first carrier, which states h < s
   (its hom level strictly below its third universe) and the bounds
   o <= Projections.u0 and h <= Projections.u1 of the sigma projections
   that a binder cannot name, whence the trailing [+].  [Compose] and
   [Functor_Setoid], each with a strict level of its own, take s for it,
   so [mh_EM_forget] and the laws add no level; turning them from [Qed]
   into [Defined] left their blocks as they were (compared by script,
   [About] before and after).  The four [_iso_id] readbacks add only the
   caps h <= Projections.u0 and e <= Projections.u0/u1 of the [projT1]
   they apply to Cat's ≈, a sigma type.  [mh_EM_forget_strict] adds a and
   b, the levels of [Functor_StrictEq_Setoid], together with the stdlib
   bounds of that setoid's own block (transport, eq_rect, eq_rect_r,
   projections and the others).  [Monads_EM] and its two readbacks bind
   [@{o h m1 m2 e s u}]: [Monads@{o h m1 m2}] and [Cat@{u e s e h}], whose
   block states e < u and h < u; m2 <= e is [Functor]'s own bound
   h1 <= h2, the hom level of (Monads C)^op below that of Cat.  No [Set]
   and no equation occur.

   NOT DELIVERED.  The Leibniz form of G^T ∘ θ* = G^{T'} (refused,
   above).  The converse, that every functor X^{T'} → X^T over X comes
   from exactly one morphism of monads, is not proved.  The Kleisli
   functor induced by θ, comonad morphisms and their coalgebras, and
   θ* as a morphism of adjunctions are not built.  Mac Lane's §VI.2
   Theorem 1 (the Eilenberg–Moore adjunction F^T ⊣ G^T induces the
   given monad) is not packaged as an isomorphism in [Monads C].
   BG.v and SupLat/Free.v are not rewired onto θ*. *)

(** ** θ* on objects: (a, h') ↦ (a, h' ∘ θ_a) *)

Definition mh_algebra@{o h | } {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') {a : C}
  (A : @TAlgebra C T' M' a) : @TAlgebra C T M a.
Proof.
  unshelve refine
    (@Build_TAlgebra C T M a (t_alg[A] ∘ mh_transform θ a) _ _).
  - etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_ret θ) ] | ].
    apply (@t_id C T' M' a A).
  - symmetry.
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply (mh_join θ) ] | ].
    etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects;
          [ symmetry; apply (@t_action C T' M' a A) | reflexivity ] | ].
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
    etransitivity; [ apply comp_assoc | ].
    apply compose_respects; [ reflexivity | ].
    symmetry. apply fmap_comp.
Defined.

(** ** θ* : X^{T'} ⟶ X^T *)

Definition mh_EM@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @EilenbergMoore@{e o s h} C T' M' ⟶ @EilenbergMoore@{e o s h} C T M.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{e o s h} C T' M') (@EilenbergMoore@{e o s h} C T M)
       (fun X => (`1 X; mh_algebra θ (`2 X)))
       (fun X Y f =>
          @Build_TAlgebraHom C T M (`1 X) (`1 Y)
            (mh_algebra θ (`2 X)) (mh_algebra θ (`2 Y))
            (t_alg_hom[f]) _) _ _ _).
  - etransitivity; [ apply comp_assoc | ].
    etransitivity;
      [ apply compose_respects;
          [ apply (@t_alg_hom_commutes _ _ _ _ _ _ _ f) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity | apply (naturality (mh_transform θ)) ] | ].
    apply comp_assoc.
  - intros X Y f g E. exact E.
  - intros X. simpl. reflexivity.
  - intros X Y Z f g. simpl. reflexivity.
Defined.

Example mh_EM_carrier@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T' M') :
  `1 (fobj[mh_EM@{o h e s} θ] X) = `1 X := eq_refl.

Example mh_EM_alg@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T' M') :
  @t_alg _ _ _ _ (`2 (fobj[mh_EM@{o h e s} θ] X))
    = @t_alg _ _ _ _ (`2 X) ∘ mh_transform θ (`1 X) := eq_refl.

Example mh_EM_hom@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X Y : @EilenbergMoore@{e o s h} C T' M') (f : X ~> Y) :
  t_alg_hom[fmap[mh_EM@{o h e s} θ] f] = t_alg_hom[f] := eq_refl.

(** ** G^T ∘ θ* = G^{T'} *)

(* On objects and on arrows, by [eq_refl]. *)

Example mh_EM_forget_obj@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T' M') :
  fobj[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] X
    = fobj[@EM_Forget@{o h s e} C T' M'] X := eq_refl.

Example mh_EM_forget_obj_fun@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  (fun X => fobj[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] X)
    = (fun X => fobj[@EM_Forget@{o h s e} C T' M'] X) := eq_refl.

Example mh_EM_forget_map@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X Y : @EilenbergMoore@{e o s h} C T' M') (f : X ~> Y) :
  fmap[@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ] f
    = fmap[@EM_Forget@{o h s e} C T' M'] f := eq_refl.

(* At Cat's ≈, with identity isomorphisms. *)

Theorem mh_EM_forget@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ
    ≈ @EM_Forget@{o h s e} C T' M'.
Proof.
  exists (fun X => iso_id).
  intros X Y f; cbn.
  symmetry.
  etransitivity; [ apply id_right | ].
  apply id_left.
Defined.

(* Its isomorphisms are identities, on the nose. *)

Example mh_EM_forget_iso_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T' M') :
  (to (projT1 (mh_EM_forget@{o h e s} θ) X),
   from (projT1 (mh_EM_forget@{o h e s} θ) X)) = (id, id) := eq_refl.

(* In the strict setoid of functors: objects equal by [eq_refl]. *)

Definition mh_EM_forget_strict@{o h e s a b |
  h < s, o <= e, h <= e, o <= a, h <= a, e <= a, h <= b, e <= b +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @equiv _ (@Functor_StrictEq_Setoid@{a b e o s h} _ C)
    (@EM_Forget@{o h s e} C T M ◯ mh_EM@{o h e s} θ)
    (@EM_Forget@{o h s e} C T' M').
Proof.
  exists (fun X => eq_refl).
  intros X Y f. reflexivity.
Defined.

(** ** F^T ⇝ θ* ∘ F^{T'}, the page's direction *)

(* The component at x: θ_x as an algebra map from (Tx, μ_x) to
   θ*(T'x, μ'_x) = (T'x, μ'_x ∘ θ_{T'x}). *)

Definition mh_free_component@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  fobj[@EM_Free@{o h s e} C T M] x
    ~{ @EilenbergMoore@{e o s h} C T M }~>
  fobj[mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T' M'] x.
Proof.
  unshelve refine (@Build_TAlgebraHom C T M (T x) (T' x) _ _
                     (mh_transform θ x) _).
  etransitivity; [ apply (mh_join θ) | ].
  apply comp_assoc.
Defined.

Definition mh_EM_free@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') :
  @EM_Free@{o h s e} C T M
    ⟹ mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T' M'.
Proof.
  unshelve refine (Build_Transform' (mh_free_component θ) _).
  intros x y f. simpl.
  apply (naturality (mh_transform θ)).
Defined.

(* Its image under G^T is θ itself. *)

Example mh_EM_free_forget@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  fmap[@EM_Forget@{o h s e} C T M] (transform[mh_EM_free@{o h e s} θ] x)
    = mh_transform θ x := eq_refl.

(* The component is the transpose of η'_x along F^T ⊣ G^T. *)

Lemma mh_EM_free_transpose@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ : MonadHom@{o h} M M') (x : C) :
  t_alg_hom[@EM_extend@{o h e s} C T M x
                 (fobj[mh_EM@{o h e s} θ ◯ @EM_Free@{o h s e} C T' M'] x)
                 (@ret C T' M' x)]
    ≈ mh_transform θ x.
Proof.
  simpl.
  etransitivity; [ apply comp_assoc_sym | ].
  etransitivity;
    [ apply compose_respects;
        [ reflexivity | symmetry; apply (naturality (mh_transform θ)) ] | ].
  etransitivity; [ apply comp_assoc | ].
  etransitivity;
    [ apply compose_respects; [ apply join_fmap_ret | reflexivity ] | ].
  apply id_left.
Qed.

(** ** Functoriality in θ *)

(* The identity arrow between two structures on one carrier whose
   structure maps are ≈. *)

Definition talg_same@{o h | } {C : Category@{o h h}} {T : C ⟶ C}
  {M : @Monad C T} {a : C} (A B : @TAlgebra C T M a)
  (E : @t_alg C T M a A ≈ @t_alg C T M a B) : @TAlgebraHom C T M a a A B.
Proof.
  unshelve refine (@Build_TAlgebraHom C T M a a A B id _).
  etransitivity; [ apply id_left | ].
  etransitivity; [ exact E | ].
  symmetry.
  etransitivity;
    [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
  apply id_right.
Defined.

Lemma mh_EM_respects@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ θ' : MonadHom@{o h} M M')
  (E : ∀ x, mh_transform θ x ≈ mh_transform θ' x) :
  mh_EM@{o h e s} θ ≈ mh_EM@{o h e s} θ'.
Proof.
  unshelve eexists.
  - intros X.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + apply talg_same. simpl.
      apply compose_respects; [ reflexivity | apply E ].
    + apply talg_same. simpl.
      apply compose_respects; [ reflexivity | symmetry; apply E ].
    + simpl. apply id_left.
    + simpl. apply id_left.
  - intros X Y f. simpl.
    symmetry. etransitivity; [ apply id_right | ]. apply id_left.
Defined.

Lemma mh_EM_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T : C ⟶ C} {M : @Monad C T} :
  mh_EM@{o h e s} (mh_id M) ≈ @Id (@EilenbergMoore@{e o s h} C T M).
Proof.
  unshelve eexists.
  - intros X.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + apply talg_same. simpl. apply id_right.
    + apply talg_same. simpl. symmetry. apply id_right.
    + simpl. apply id_left.
    + simpl. apply id_left.
  - intros X Y f. simpl.
    symmetry. etransitivity; [ apply id_right | ]. apply id_left.
Defined.

Lemma mh_EM_compose@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M') :
  mh_EM@{o h e s} (mh_compose φ θ)
    ≈ mh_EM@{o h e s} θ ◯ mh_EM@{o h e s} φ.
Proof.
  unshelve eexists.
  - intros X.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + apply talg_same. simpl. apply comp_assoc.
    + apply talg_same. simpl. apply comp_assoc_sym.
    + simpl. apply id_left.
    + simpl. apply id_left.
  - intros X Y f. simpl.
    symmetry. etransitivity; [ apply id_right | ]. apply id_left.
Defined.

(* The isomorphisms of the three laws are identities, on the nose. *)

Example mh_EM_respects_iso_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} (θ θ' : MonadHom@{o h} M M')
  (E : ∀ x, mh_transform θ x ≈ mh_transform θ' x)
  (X : @EilenbergMoore@{e o s h} C T' M') :
  (t_alg_hom[to (projT1 (mh_EM_respects@{o h e s} θ θ' E) X)],
   t_alg_hom[from (projT1 (mh_EM_respects@{o h e s} θ θ' E) X)])
    = (id, id) := eq_refl.

Example mh_EM_id_iso_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T : C ⟶ C} {M : @Monad C T}
  (X : @EilenbergMoore@{e o s h} C T M) :
  (t_alg_hom[to (projT1 (@mh_EM_id@{o h e s} C T M) X)],
   t_alg_hom[from (projT1 (@mh_EM_id@{o h e s} C T M) X)]) = (id, id)
  := eq_refl.

Example mh_EM_compose_iso_id@{o h e s | h < s, o <= e, h <= e +}
  {C : Category@{o h h}} {T T' T'' : C ⟶ C}
  {M : @Monad C T} {M' : @Monad C T'} {M'' : @Monad C T''}
  (φ : MonadHom@{o h} M' M'') (θ : MonadHom@{o h} M M')
  (X : @EilenbergMoore@{e o s h} C T'' M'') :
  (t_alg_hom[to (projT1 (mh_EM_compose@{o h e s} φ θ) X)],
   t_alg_hom[from (projT1 (mh_EM_compose@{o h e s} φ θ) X)]) = (id, id)
  := eq_refl.

(** ** The contravariant functor (Monads C)^op ⟶ Cat *)

Definition Monads_EM@{o h m1 m2 e s u |
  h < s, h < u, e < u, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= e,
  o <= e, h <= e +} (C : Category@{o h h}) :
  (Monads@{o h m1 m2} C)^op ⟶ Cat@{u e s e h}.
Proof.
  unshelve refine
    (@Build_Functor ((Monads@{o h m1 m2} C)^op) Cat@{u e s e h}
       (fun N : { T : C ⟶ C & @Monad C T } =>
          @EilenbergMoore@{e o s h} C (projT1 N) (projT2 N))
       (fun N N' (θ : MonadHom@{o h} (projT2 N') (projT2 N)) =>
          mh_EM@{o h e s} θ) _ _ _).
  - intros N N' θ θ' E. exact (mh_EM_respects θ θ' E).
  - intros N. exact mh_EM_id.
  - intros N N' N'' φ θ. exact (mh_EM_compose θ φ).
Defined.

Example Monads_EM_obj@{o h m1 m2 e s u |
  h < s, h < u, e < u, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= e,
  o <= e, h <= e +} (C : Category@{o h h}) (N : Monads@{o h m1 m2} C) :
  fobj[Monads_EM@{o h m1 m2 e s u} C] N
    = @EilenbergMoore@{e o s h} C (projT1 N) (projT2 N) := eq_refl.

Example Monads_EM_map@{o h m1 m2 e s u |
  h < s, h < u, e < u, o <= m1, h <= m1, o <= m2, h <= m2, m2 <= e,
  o <= e, h <= e +} (C : Category@{o h h}) (N N' : Monads@{o h m1 m2} C)
  (θ : N' ~{Monads@{o h m1 m2} C}~> N) :
  fmap[Monads_EM@{o h m1 m2 e s u} C] θ = mh_EM@{o h e s} θ := eq_refl.
