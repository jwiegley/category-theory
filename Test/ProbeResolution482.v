Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Map.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Monad.Comparison.Resolution.

Generalizable All Variables.

(** * Probe for issue #482: the strength boundaries of
      Monad/Comparison/Resolution.v and the controls of
      Instance/Fun/Action/Monad/Comparison.v *)

(* The import list is the first target's, in its order, followed by that
   target.  The last section adds, after every command above it, the
   import list of the second target,
   Instance/Fun/Action/Monad/Comparison.v, and that module; so nothing
   above it is elaborated under the second target's imports.

   REFUTATIONS.  Five lines open with the refutation keyword: the
   instrument, NAME-ABSENCE, a [Check] of a name that does not exist,
   which shows that the keyword is live; and four CONVERSION boundaries,
   R1, R2a, R2 and R3, each a statement that is well typed and refused
   at [eq_refl].  Each refutation, stripped of its keyword in a copy of
   this whole file, stops inside the stripped command, the instrument
   with "The reference p482_absent_name was not found in the current
   environment" and the other four with "cannot unify" (five of five,
   measured).  Each control, prefixed in such a copy, stops with "The
   command has not" and the rest of that message (twenty-three of
   twenty-three).

   R1  The strict left triangle of [EM_Comparison] on objects:
       K (F x) = F^T x at [eq_refl].  The two algebras agree on carrier
       (C1) and on structure map (C2), both at [eq_refl]; the [TAlgebra]
       records differ in their law fields.  This is why the comparison of
       a resolution is read at ≈ (the target's header, THE READING).
   R2  The Lemma's comparison at the Eilenberg–Moore resolution,
       [EM_Comparison_via_Lemma], against [EM_Comparison], on objects at
       [eq_refl].  They agree on carriers (C3) and are isomorphic
       ([EM_Comparison_via_Lemma_agrees]); R2a: their structure maps are
       refused at [eq_refl].  The Lemma's uniqueness is up to
       isomorphism, not on the nose.  R2a and R2 measure conversion:
       the Leibniz equality of the two is neither proved nor refuted.
   R3  The coherence [cmp_monad] of [EM_Comparison_Comparison] at
       [eq_refl]: its left side is id ∘ id at [eq_refl] (C5), the right
       side id, in a variable category.

   CONTROLS.  C1-C5 above; C4, the right triangle of the Lemma's
   comparison at the Eilenberg–Moore resolution on objects, at
   [eq_refl]; and C6-C17, the twelve [Example]s of the first target
   restated, so that a rename or a lost transparency breaks this file.
   In the last section, the second target's positive controls: at the
   adjunction of LZ-sets, [EM_Comparison] satisfies the two hypotheses
   that [bare_awodey_refuted] quantifies over (C18, C19) and is a
   comparison over the identity identification (C20), to which
   [EM_Comparison_unique] applies (C21), so that neither
   [bare_awodey_refuted] nor [K_no_coherent_comparison] is vacuous; and
   C22, C23, that target's two [Example]s restated. *)

(* ------------------------------------------------------------------------ *)
(** ** The instrument *)

(* The instrument *)
Fail Check p482_absent_name.

Section EMProbe.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).

Local Notation T := (Adjunction_Induced_Monad Adj).

Example C1 (x : X) :
  `1 (fobj[EM_Comparison Adj ◯ F] x) = `1 (fobj[@EM_Free X (G ◯ F) T] x)
  := eq_refl.

Example C2 (x : X) :
  t_alg[`2 (fobj[EM_Comparison Adj ◯ F] x)]
    = t_alg[`2 (fobj[@EM_Free X (G ◯ F) T] x)] := eq_refl.

Fail Example R1 (x : X) :
  fobj[EM_Comparison Adj ◯ F] x = fobj[@EM_Free X (G ◯ F) T] x := eq_refl.

Example C3 (a : A) :
  `1 (fobj[EM_Comparison_via_Lemma Adj] a) = `1 (fobj[EM_Comparison Adj] a)
  := eq_refl.

Fail Example R2a (a : A) :
  t_alg[`2 (fobj[EM_Comparison_via_Lemma Adj] a)]
    = t_alg[`2 (fobj[EM_Comparison Adj] a)] := eq_refl.

Fail Example R2 (a : A) :
  fobj[EM_Comparison_via_Lemma Adj] a = fobj[EM_Comparison Adj] a := eq_refl.

Example C4 (a : A) :
  fobj[EM_Forget (G ◯ F) ◯ EM_Comparison_via_Lemma Adj] a = fobj[G] a
  := eq_refl.

Fail Example R3 (x : X) :
  fmap[EM_Forget (G ◯ F)] (to (`1 (EM_Comparison_Free Adj) x))
    ∘ from (`1 (EM_Comparison_Forget Adj) (F x))
    = transform[mh_transform (to (EM_Comparison_theta Adj))] x := eq_refl.

Example C5 (x : X) :
  fmap[EM_Forget (G ◯ F)] (to (`1 (EM_Comparison_Free Adj) x))
    ∘ from (`1 (EM_Comparison_Forget Adj) (F x))
    = id ∘ id := eq_refl.

(* Restatements. *)

Example C6 (x : X) :
  transform[mh_transform (to (EM_Comparison_theta Adj))] x = id := eq_refl.

Example C7 (a : A) :
  `1 (EM_Comparison_Forget Adj) a = iso_id := eq_refl.

Example C8 (x : X) :
  `1 (EM_Comparison_Free Adj) x = EM_Comparison_Free_iso Adj x := eq_refl.

End EMProbe.

Section MonadProbe.

Context {X : Category} (T : X ⟶ X) `{H : @Monad X T}.

Example C9 (x : X) :
  transform[mh_transform (to (@EM_Monad_iso X T H))] x = id := eq_refl.

Example C10 (x : X) :
  transform[mh_transform (from (@EM_Monad_iso X T H))] x = id := eq_refl.

End MonadProbe.

Section LemmaProbe.

(* The object and hom levels of [Monads X], kept apart as in the target. *)
Universes m1 m2.

Context {X : Category}.
Context {A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).
Context {A' : Category} {F' : X ⟶ A'} {G' : A' ⟶ X} (Adj' : F' ⊣ G').
Context (θ : @Isomorphism (Monads@{_ _ m1 m2} X)
               (G' ◯ F'; Adjunction_Induced_Monad Adj')
               (G ◯ F; Adjunction_Induced_Monad Adj)).
Context (CR : CreatesUSplitCoequalizers G).
Context (P : Comparison Adj Adj' θ).

Example C11 :
  wsq_K (wmap_squares Adj' Adj (Comparison_map Adj Adj' θ P))
    = cmp_functor Adj Adj' θ P := eq_refl.

Example C12 :
  wsq_L (wmap_squares Adj' Adj (Comparison_map Adj Adj' θ P)) = Id[X]
  := eq_refl.

Example C13 (a : A') : `1 (fobj[Comparison_alg Adj Adj' θ] a) = G' a
  := eq_refl.

Example C14 (a : A') :
  t_alg[`2 (fobj[Comparison_alg Adj Adj' θ] a)]
    = fmap[G'] (@counit _ _ _ _ Adj' a)
        ∘ transform[mh_transform (from θ)] (G' a) := eq_refl.

Example C15 (a : A') :
  fobj[Comparison_functor Adj Adj' θ CR] a
    = beck_G_obj Adj CR (fobj[Comparison_alg Adj Adj' θ] a) := eq_refl.

Example C16 (a : A') :
  to (`1 (Comparison_right Adj Adj' θ CR) a)
    = beck_to Adj CR (fobj[Comparison_alg Adj Adj' θ] a) := eq_refl.

Example C17 (a : A') :
  from (`1 (Comparison_right Adj Adj' θ CR) a)
    = fmap[G] (beck_e Adj CR (fobj[Comparison_alg Adj Adj' θ] a))
        ∘ @unit _ _ _ _ Adj (G' a) := eq_refl.

End LemmaProbe.

(* ------------------------------------------------------------------------ *)
(** ** The positive controls of Instance/Fun/Action/Monad/Comparison.v *)

(* Required here, after every other command above, so that the sections
   above are elaborated under the first target's import list alone: the
   import list of Instance/Fun/Action/Monad/Comparison.v, in its order,
   and that module. *)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.
Require Import Category.Monad.Comparison.Resolution.
Require Import Category.Instance.Fun.Action.Monad.Comparison.

(* C18: at the adjunction of LZ-sets, [EM_Comparison] satisfies the first
   hypothesis that [bare_awodey_refuted] quantifies over. *)
Example C18 :
  EM_Forget (ActF LZ) ◯ EM_Comparison (MSet_adj LZ) ≈ MSet_Forget LZ :=
  EM_Comparison_Forget (MSet_adj LZ).

(* C19: and the second. *)
Example C19 :
  EM_Comparison (MSet_adj LZ) ◯ MSet_Free LZ ≈ EM_Free (ActF LZ) :=
  EM_Comparison_Free (MSet_adj LZ).

(* C20: a comparison over the identity identification exists there. *)
Definition C20 :
  Comparison (@EM_Adjunction Sets (ActF LZ) (ActMonad LZ)) (MSet_adj LZ)
    (EM_Comparison_theta (MSet_adj LZ)) :=
  EM_Comparison_Comparison (MSet_adj LZ).

(* C21: and the Lemma's uniqueness applies to it. *)
Definition C21 : cmp_functor _ _ _ C20 ≈ EM_Comparison (MSet_adj LZ) :=
  EM_Comparison_unique (MSet_adj LZ) C20.

(* C22: [K_forget_components] restated. *)
Example C22 (A : MSetoidAction LZ) : `1 K_forget A = iso_id := eq_refl.

(* C23: [theta_sigma_component] restated. *)
Example C23 (X : SetoidObject) :
  transform[mh_transform (to theta_sigma)] X = lz_swap_first X := eq_refl.
