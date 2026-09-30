Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.

Generalizable All Variables.

(** * The identity monad *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §VI.3, book p. 144 (PDF p. 153), read from the page image: the
     discrete-space adjunction ⟨D, G, η, …⟩ : Set ⇀ Top "defines on Set
     the monad I = ⟨I, 1, 1⟩ which is the identity (identity functor,
     identity as unit and as multiplication).  The I-algebras in Set are
     just the sets" (catalog id maclane:VI.3:remark1).
   nLab: https://ncatlab.org/nlab/show/monad
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category

   BACKGROUND.  The identity functor, with the identity as unit and as
   multiplication, is a monad on every category, and an adjunction whose unit
   is the identity induces a monad isomorphic to it: the unit's naturality
   gives T f ≈ f, and a triangle identity makes the multiplication U ε F ≈ the
   identity too; in Mac Lane's example these hold on data at [eq_refl].  An
   algebra for it is an arrow h : a → a with h ∘ id ≈ id, so h ≈ id and the
   action law holds of itself: Mac Lane's "the I-algebras in Set are just the
   sets", here at any category and up to ≈.  The monad matters because it is
   induced by adjunctions of very different kinds.  Mac Lane's example on p.
   144 is the discrete-space adjunction, whose right adjoint is not monadic
   (Instance/Top/Monadicity.v); the adjunction Id ⊣ Id, whose right adjoint is
   monadic (Monad/Monadicity/Examples.v's [identity_monadic]), induces a monad
   with functor Id ◯ Id whose unit and multiplication are [id] at [eq_refl]
   (control C55 of Test/ProbeMonadicity469.v), isomorphic to this one (no
   constant states that isomorphism).  So an induced monad does not determine
   whether its right adjoint is monadic.

   WHY A NEW CONSTANT.  Before this file the tree had three identity
   monads of Theory/Monad.v's class [Monad] (a fourth, Theory/Coq/
   Monad.v's [Identity_Monad], is of the programming class there), and
   none serves a statement over an arbitrary category that must compile
   on every supported version.
     - Monad/Strong.v's [Id_Monad] is a [#[local] Program Instance] inside
       the section of the identity strong monad.  Its universe list has
       three levels on Rocq 9.1.1, five on Coq 8.20.1 and seventeen on
       8.19.2 (#467's measurement, recorded in the header of Monad/
       Eilenberg/Moore/Limit/Examples.v), so no explicit instance of it
       compiles on all three versions.
     - Monad/Eilenberg/Moore/Limit/Examples.v's [IdSM] gives every field,
       but on [Sets] only, inside an examples file.
     - [Adjunction_Induced_Monad Adjunction_Id], the monad behind
       [identity_monadic], has the functor Id ◯ Id, not Id.
   [IdMonad C] follows [IdSM]'s pattern at an arbitrary category: the
   constructor [Build_Monad] with every field given, the laws closed by
   [reflexivity], [id_left] and [id_right], with no rewriting.

   WHAT IS HERE.
     - [IdMonad C : Monad Id[C]], with the readbacks [IdMonad_fobj],
       [IdMonad_fmap], [IdMonad_ret] and [IdMonad_join].
     - [IdMonad_alg_id]: the structure map of every algebra is ≈ id.
     - [IdMonad_EM_equivalence]: the forgetful functor of the
       Eilenberg-Moore category of [IdMonad C] is an equivalence of
       categories, with the free-algebra functor [EM_Free] as its
       quasi-inverse.  The counit [IdMonad_EM_counit] has the identity
       isomorphisms [iso_id] as components; the unit's component at an
       algebra (a, h), [IdMonad_EM_unit_iso], is the identity arrow of a,
       read as an algebra map (a, h) → (a, id) and back
       ([IdMonad_EM_unit_iso_id]).

   STRENGTHS.  By [eq_refl]: [IdMonad_fobj], [IdMonad_fmap],
   [IdMonad_ret], [IdMonad_join] and [IdMonad_EM_unit_iso_id].  Up to ≈:
   [IdMonad_alg_id] and the two cells of [IdMonad_EM_equivalence], in
   Theory/Functor.v's [Functor_Setoid].  The equivalence is not an
   isomorphism of categories: an algebra remembers its structure map h,
   which is ≈ id and need not be id.  For [IdSM] on [Sets] that is #467's
   [A_id_ne_A_true] (two different algebras on one carrier), the reason
   the forgetful functor there is not injective on objects; it is not
   restated here for [IdMonad].  Four proofs end [Defined] (counted by
   token).  Two are load-bearing, measured by closing each alone [Qed] in
   a copy of this file followed by Instance/Top/Monadicity.v: [IdMonad]
   ([IdMonad_ret] is then refused) and [IdMonad_EM_unit_iso]
   ([IdMonad_EM_unit] and [IdMonad_EM_unit_iso_id]: the proof of the
   first stops with "Unable to unify", and the readback is refused).  The
   two cells [IdMonad_EM_counit] and [IdMonad_EM_unit] are [Defined] by
   the data convention only.

   UNIVERSES, read off [About].  [IdMonad@{o h}] and
   [IdMonad_alg_id@{o h}]: constraint list empty.  The four readbacks
   bind [@{o h | +}]: empty on 9.1.1; the [+] is for the level of [eq],
   which Coq 8.19.2 and 8.20.1 bound below by o ([IdMonad_fobj]) or h
   (the other three), as #468 measured for its own readbacks.  The
   Eilenberg-Moore constants bind [@{o h s e}] with h < s, o <= e and
   h <= e, plus the bounds o <= Projections.u0 and h <= Projections.u1
   of the sigma projections, whence the [+]: exactly the block of
   [EilenbergMoore@{e o s h}], their first carrier.  [Compose] and
   [Functor_Setoid] take s for their own strict level, so no constant
   here adds a level.  No [Set] and no equation occur.

   NOT DELIVERED.  The identity monad is the initial object of [Monads C]
   (Monad/Morphism.v): the unit of any monad is the unique morphism of
   monads out of it.  That is not stated.  The Kleisli category of
   [IdMonad C] is not built, and [Id_Monad] and [IdSM] are not rewired
   onto [IdMonad]. *)

(** ** The monad ⟨I, 1, 1⟩ *)

Definition IdMonad@{o h | } (C : Category@{o h h}) : @Monad C Id[C].
Proof.
  unshelve refine (@Build_Monad C Id[C] (fun x => id) (fun x => id)
                     _ _ _ _ _); intros; simpl.
  - transitivity f; [ apply id_left | symmetry; apply id_right ].
  - reflexivity.
  - apply id_left.
  - apply id_left.
  - transitivity f; [ apply id_left | symmetry; apply id_right ].
Defined.

Example IdMonad_fobj@{o h | +} (C : Category@{o h h}) (x : C) :
  fobj[Id[C]] x = x := eq_refl.

Example IdMonad_fmap@{o h | +} (C : Category@{o h h}) (x y : C)
  (f : x ~> y) : fmap[Id[C]] f = f := eq_refl.

Example IdMonad_ret@{o h | +} (C : Category@{o h h}) (x : C) :
  @ret C Id[C] (IdMonad@{o h} C) x = id := eq_refl.

Example IdMonad_join@{o h | +} (C : Category@{o h h}) (x : C) :
  @join C Id[C] (IdMonad@{o h} C) x = id := eq_refl.

(** ** Its algebras are the objects *)

Lemma IdMonad_alg_id@{o h | } (C : Category@{o h h}) (a : C)
  (A : @TAlgebra C Id[C] (IdMonad@{o h} C) a) : t_alg[A] ≈ id.
Proof.
  transitivity (t_alg[A] ∘ id); [ symmetry; apply id_right | ].
  exact (@t_id C Id[C] (IdMonad@{o h} C) a A).
Qed.

Definition IdMonad_EM_counit@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)
    ◯ @EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C) ≈ Id[C].
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  transitivity (id ∘ f); [ symmetry; apply id_left | ].
  symmetry; apply id_right.
Defined.

Definition IdMonad_EM_unit_iso@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h})
  (X : @EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)) :
  @Isomorphism (@EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C))
    X (fobj[@EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C)
             ◯ @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)] X).
Proof.
  unshelve econstructor.
  - unshelve refine (@Build_TAlgebraHom C Id[C] (IdMonad@{o h} C)
                       (`1 X) (`1 X) (`2 X) _ id _); simpl.
    transitivity (t_alg[`2 X]); [ apply id_left | ].
    transitivity (@id C (`1 X)); [ exact (IdMonad_alg_id C _ (`2 X)) | ].
    symmetry; apply id_left.
  - unshelve refine (@Build_TAlgebraHom C Id[C] (IdMonad@{o h} C)
                       (`1 X) (`1 X) _ (`2 X) id _); simpl.
    transitivity (@id C (`1 X)); [ apply id_left | ].
    transitivity (t_alg[`2 X]);
      [ symmetry; exact (IdMonad_alg_id C _ (`2 X)) | ].
    symmetry; apply id_right.
  - simpl; apply id_left.
  - simpl; apply id_left.
Defined.

Example IdMonad_EM_unit_iso_id@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h})
  (X : @EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)) :
  (t_alg_hom[to (IdMonad_EM_unit_iso@{o h s e} C X)],
   t_alg_hom[from (IdMonad_EM_unit_iso@{o h s e} C X)]) = (id, id)
  := eq_refl.

Definition IdMonad_EM_unit@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  Id[@EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)]
    ≈ @EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C)
        ◯ @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C).
Proof.
  exists (IdMonad_EM_unit_iso C).
  intros X Y f; simpl.
  transitivity (id ∘ t_alg_hom[f]); [ symmetry; apply id_left | ].
  symmetry; apply id_right.
Defined.

Definition IdMonad_EM_equivalence@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  EquivalenceOfCategories (@EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)) :=
  @Build_EquivalenceOfCategories _ _ _ _
    (IdMonad_EM_counit@{o h s e} C) (IdMonad_EM_unit@{o h s e} C).
