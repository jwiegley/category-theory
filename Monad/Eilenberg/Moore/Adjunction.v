Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The Eilenberg–Moore free/forgetful adjunction

    nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category
    Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

    Monad/Adjunction.v shows that every adjunction F ⊣ U induces a monad
    U ◯ F on the domain of F.  This file provides the terminal converse
    resolution, through the Eilenberg–Moore category C^T of algebras
    (Monad/Eilenberg/Moore.v) of a monad (T, ret, join) = (T, η, μ) on C:

    - [EM_Forget] U^T : C^T ⟶ C sends an algebra (a, ν) to its carrier a,
      and an algebra homomorphism to its underlying C-arrow;
    - [EM_Free] F^T : C ⟶ C^T sends x to the free algebra (T x, μ_x): the
      structure map is the multiplication join, whose algebra laws are the
      monad laws [join_ret] and [join_fmap_join], and a morphism f : x ~> y
      becomes the homomorphism fmap[T] f, which intertwines the two free
      actions by the multiplication naturality [join_fmap_fmap];
    - [EM_Adjunction] F^T ⊣ U^T: the transpose ⌊g⌋ of an algebra map
      g : (T x, μ_x) ~> (b, ν) is t_alg_hom[g] ∘ ret, and the transpose
      ⌈f⌉ of f : x ~> b is its universal extension ν ∘ fmap[T] f, packaged
      as an algebra homomorphism by [EM_extend].  That the two transposes
      are mutually inverse is the universal property of the free algebra:
      [EM_extend_ret] (extension restricted along η recovers f) and
      [EM_extend_unique] (every algebra map out of a free algebra is the
      extension of its own restriction).

    The adjunction presents the monad we started with:
    [EM_Monad_agrees] identifies the composite U^T ◯ F^T with T (a natural
    isomorphism whose components are identities), [EM_unit_agrees]
    identifies the adjunction unit with ret, and [EM_join_agrees]
    identifies the U^T-image of the counit — which is exactly the
    multiplication of the monad that Monad/Adjunction.v extracts from this
    adjunction — with join.  The counit itself acts at (b, ν) by the
    structure map ν ([EM_counit_agrees]).

    This is the terminal resolution of T; the initial one is the Kleisli
    adjunction of Monad/Kleisli/Adjunction.v, whose comparison into C^T
    lands in the free algebras. *)

Section EilenbergMooreAdjunction.

Context {C : Category}.
Context (T : C ⟶ C).
Context `{H : @Monad C T}.

#[local] Obligation Tactic := program_simpl.

(** The forgetful functor C^T ⟶ C: project the carrier of an algebra and
    the underlying arrow of an algebra homomorphism.  Since equivalence of
    algebra homomorphisms in C^T is equivalence of their underlying arrows,
    all three functor laws hold on the nose. *)

Program Definition EM_Forget : EilenbergMoore T ⟶ C := {|
  fobj := fun a => `1 a;
  fmap := fun _ _ f => t_alg_hom[f]
|}.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** The free-algebra functor C ⟶ C^T: on objects, the free algebra
    (T x, μ_x); on morphisms, fmap[T].  The algebra laws for μ_x are the
    monad unit law join_ret and the associativity join_fmap_join, and the
    homomorphism square for fmap[T] f is the multiplication naturality
    join_fmap_fmap. *)

Program Definition EM_Free : C ⟶ EilenbergMoore T := {|
  fobj := fun a => (T a; {| t_alg := @join C T H a |});
  fmap := fun x y f => {| t_alg_hom := fmap[T] f |}
|}.
Next Obligation. apply join_ret. Qed.
Next Obligation. apply join_fmap_join. Qed.
Next Obligation. symmetry; apply join_fmap_fmap. Qed.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. apply fmap_id. Qed.
Next Obligation. apply fmap_comp. Qed.

(** The universal property of the free algebra, on underlying arrows.  Fix
    an algebra (b, ν) and an arrow f : x ~> b.  Its extension ν ∘ fmap[T] f
    is an algebra homomorphism (T x, μ_x) ~> (b, ν)
    ([EM_extend_is_alg_hom]); it restricts along η back to f
    ([EM_extend_ret]); and it is the only such homomorphism, in that any
    algebra map g out of the free algebra is the extension of g ∘ η
    ([EM_extend_unique]). *)

Lemma EM_extend_is_alg_hom {x b : C} (N : @TAlgebra C T H b)
      (f : x ~{C}~> b) :
  (t_alg[N] ∘ fmap[T] f) ∘ join ≈ t_alg[N] ∘ fmap[T] (t_alg[N] ∘ fmap[T] f).
Proof.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite (@t_action _ _ _ _ N).
  rewrite <- !comp_assoc.
  rewrite join_fmap_fmap.
  reflexivity.
Qed.

Lemma EM_extend_ret {x b : C} (N : @TAlgebra C T H b) (f : x ~{C}~> b) :
  (t_alg[N] ∘ fmap[T] f) ∘ ret ≈ f.
Proof.
  rewrite <- comp_assoc.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite (@t_id _ _ _ _ N).
  apply id_left.
Qed.

Lemma EM_extend_unique {x b : C} (N : @TAlgebra C T H b) (g : T x ~{C}~> b)
      (Hg : g ∘ join ≈ t_alg[N] ∘ fmap[T] g) :
  t_alg[N] ∘ fmap[T] (g ∘ ret) ≈ g.
Proof.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- Hg.
  rewrite <- comp_assoc.
  rewrite join_fmap_ret.
  apply id_right.
Qed.

(** The extension, packaged as a morphism of C^T out of a free algebra. *)

Program Definition EM_extend {x : C} {y : EilenbergMoore T}
        (f : x ~{C}~> `1 y) : EM_Free x ~{EilenbergMoore T}~> y := {|
  t_alg_hom := t_alg[`2 y] ∘ fmap[T] f
|}.
Next Obligation. apply EM_extend_is_alg_hom. Qed.

(** [EM_extend_unique], restated for a morphism of C^T out of a free
    algebra: extending the restriction of g recovers g.  The structure map
    of the free algebra is definitionally join, so the commuting square of
    g is exactly the hypothesis that [EM_extend_unique] consumes. *)

Lemma EM_restrict_extend {x : C} {y : EilenbergMoore T}
      (g : EM_Free x ~{EilenbergMoore T}~> y) :
  t_alg[`2 y] ∘ fmap[T] (t_alg_hom[g] ∘ ret) ≈ t_alg_hom[g].
Proof.
  apply EM_extend_unique.
  apply (@t_alg_hom_commutes _ _ _ _ _ _ _ g).
Qed.

(** The transposition isomorphism of hom-setoids: an algebra homomorphism
    F^T x ~{C^T}~> (b, ν) corresponds to a C-arrow x ~> b, forward by
    restriction along η, backward by [EM_extend]. *)

Program Definition EM_adj_iso (x : C) (y : EilenbergMoore T) :
  @Isomorphism Sets
    {| carrier   := @hom (EilenbergMoore T) (EM_Free x) y
     ; is_setoid := @homset (EilenbergMoore T) (EM_Free x) y |}
    {| carrier   := @hom C x (EM_Forget y)
     ; is_setoid := @homset C x (EM_Forget y) |} := {|
  to   := {| morphism := fun g => t_alg_hom[g] ∘ ret |};
  from := {| morphism := fun f => EM_extend f |}
|}.
Next Obligation. proper. Qed.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. apply EM_extend_ret. Qed.
Next Obligation. apply EM_restrict_extend. Qed.

(** Naturality of the transposition in the source argument, on underlying
    arrows: restricting after precomposition with a free arrow fmap[T] g is
    restricting first and then precomposing with g in C. *)

Lemma EM_transpose_nat_l {x y b : C} (h : T y ~{C}~> b) (g : x ~{C}~> y) :
  (h ∘ fmap[T] g) ∘ ret ≈ (h ∘ ret) ∘ g.
Proof.
  rewrite <- comp_assoc.
  rewrite <- fmap_ret.
  now rewrite !comp_assoc.
Qed.

Program Definition EM_Adjunction : EM_Free ⊣ EM_Forget :=
  @Build_Adjunction' (EilenbergMoore T) C EM_Free EM_Forget EM_adj_iso _ _.
Next Obligation. apply EM_transpose_nat_l. Qed.
Next Obligation. apply comp_assoc_sym. Qed.

(** The unit of the adjunction is the unit of the monad. *)

Lemma EM_unit_agrees {x : C} :
  @unit _ _ _ _ EM_Adjunction x ≈ ret[T].
Proof. apply id_left. Qed.

(** The counit at an algebra (b, ν) acts by the structure map ν, stated on
    the underlying arrow of the algebra homomorphism. *)

Lemma EM_counit_agrees {y : EilenbergMoore T} :
  t_alg_hom[@counit _ _ _ _ EM_Adjunction y] ≈ t_alg[`2 y].
Proof.
  cbn.
  rewrite fmap_id.
  apply id_right.
Qed.

(** The multiplication of the monad induced by this adjunction (per
    Monad/Adjunction.v it is the U^T-image of the counit) is join. *)

Lemma EM_join_agrees {x : C} :
  fmap[EM_Forget] (@counit _ _ _ _ EM_Adjunction (EM_Free x)) ≈ join[T].
Proof.
  cbn.
  rewrite fmap_id.
  apply id_right.
Qed.

(** The resolution recovers T: the composite U^T ◯ F^T is naturally
    isomorphic to T, with identity components. *)

Theorem EM_Monad_agrees : EM_Forget ◯ EM_Free ≈ T.
Proof.
  exists (fun x => iso_id).
  intros x y f; cbn.
  cat.
Qed.

End EilenbergMooreAdjunction.
