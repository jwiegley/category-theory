Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * The Eilenberg–Moore comparison functor

    nLab: https://ncatlab.org/nlab/show/monadic+adjunction
    nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

    Every adjunction F ⊣ U with F : D ⟶ C induces a monad T = U ◯ F on D
    (Monad/Adjunction.v), and the Eilenberg–Moore category D^T of T-algebras
    carries the terminal resolution F^T ⊣ U^T of that monad
    (Monad/Eilenberg/Moore/Adjunction.v).  The comparison functor
    K = [EM_Comparison] : C ⟶ D^T mediates between the given resolution and
    the terminal one: it sends an object c to the algebra (U c, U ε_c) — the
    unit law is the zig-zag identity [fmap_counit_unit] and the action law is
    the U-image of a counit naturality square — and a morphism h to
    fmap[U] h, an algebra homomorphism again by naturality of ε.  The
    comparison commutes with both resolutions:

      [EM_Comparison_Forget]  U^T ◯ K ≈ U    (identity components), and
      [EM_Comparison_Free]    K ◯ F ≈ F^T    (identity underlying arrows).

    U is a monadic functor ([Monadic]) when it has a left adjoint whose
    comparison functor is an equivalence of categories
    (Theory/Equivalence.v): then C is, up to equivalence, the category of
    algebras for the monad it induces.  Beck's monadicity theorem
    characterizes the adjunctions with this property.

    The induced monad is packaged here as [Adjunction_Induced_Monad], with
    the same underlying data as [Adjunction_Monad]: ret = η, and
    join = U ε F.  The latter is a Qed-sealed theorem, so those readings
    stay hidden inside its proof term (compare the remark in
    Comonad/Duality.v); the algebra laws of the comparison need them
    definitionally, hence this transparent packaging, whose law fields are
    proved below from the zig-zag identities and the naturality of the unit
    and counit transposes. *)

Section EilenbergMooreComparison.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(** Naturality of the unit at an arbitrary morphism of D.  (The library's
    [unit_comp] is the special case whose codomain is an object U y; the
    proof below is the same transposition argument.) *)

Lemma adj_unit_natural {x y : D} (f : x ~> y) :
  @unit _ _ _ _ A y ∘ f ≈ fmap[U] (fmap[F] f) ∘ @unit _ _ _ _ A x.
Proof.
  unfold unit.
  rewrite <- to_adj_nat_r.
  rewrite <- to_adj_nat_l.
  apply to_adj_respects.
  cat.
Qed.

(** Naturality of the counit at an arbitrary morphism of C.  (The library's
    [counit_comp] is the special case whose domain is an object F x.) *)

Lemma adj_counit_natural {x y : C} (g : x ~> y) :
  @counit _ _ _ _ A y ∘ fmap[F] (fmap[U] g) ≈ g ∘ @counit _ _ _ _ A x.
Proof.
  unfold counit.
  rewrite <- from_adj_nat_l.
  rewrite <- from_adj_nat_r.
  apply from_adj_respects.
  cat.
Qed.

(** The monad laws for (U ◯ F, η, U ε F), as named lemmas so that the monad
    below is a fully transparent record. *)

Lemma Induced_Monad_join_fmap_join (x : D) :
  fmap[U] (@counit _ _ _ _ A (F x))
      ∘ fmap[U] (fmap[F] (fmap[U] (@counit _ _ _ _ A (F x))))
    ≈ fmap[U] (@counit _ _ _ _ A (F x))
        ∘ fmap[U] (@counit _ _ _ _ A (F (U (F x)))).
Proof.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  apply adj_counit_natural.
Qed.

Lemma Induced_Monad_join_fmap_ret (x : D) :
  fmap[U] (@counit _ _ _ _ A (F x))
      ∘ fmap[U] (fmap[F] (@unit _ _ _ _ A x)) ≈ id.
Proof.
  rewrite <- fmap_comp.
  rewrite (@counit_fmap_unit _ _ _ _ A x).
  apply fmap_id.
Qed.

Lemma Induced_Monad_join_fmap_fmap {x y : D} (f : x ~> y) :
  fmap[U] (@counit _ _ _ _ A (F y))
      ∘ fmap[U] (fmap[F] (fmap[U] (fmap[F] f)))
    ≈ fmap[U] (fmap[F] f) ∘ fmap[U] (@counit _ _ _ _ A (F x)).
Proof.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  apply adj_counit_natural.
Qed.

(** The monad induced by the adjunction, with transparent unit and
    multiplication: ret = η and join = U ε F. *)

Definition Adjunction_Induced_Monad : @Monad D (U ◯ F) :=
  @Build_Monad D (U ◯ F)
    (fun x => @unit _ _ _ _ A x)                     (* ret  = η     *)
    (fun x => fmap[U] (@counit _ _ _ _ A (F x)))     (* join = U ε F *)
    (fun x y f => adj_unit_natural f)
    (fun x => Induced_Monad_join_fmap_join x)
    (fun x => Induced_Monad_join_fmap_ret x)
    (fun x => @fmap_counit_unit _ _ _ _ A (F x))
    (fun x y f => Induced_Monad_join_fmap_fmap f).

(** The comparison algebra on U c: the structure map is U ε_c.  Its unit law
    is the zig-zag identity, and its action law is the U-image of the counit
    naturality square at ε_c. *)

Lemma EM_Comparison_Algebra_id (c : C) :
  fmap[U] (@counit _ _ _ _ A c) ∘ @unit _ _ _ _ A (U c) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ A c). Qed.

Lemma EM_Comparison_Algebra_action (c : C) :
  fmap[U] (@counit _ _ _ _ A c)
      ∘ fmap[U] (fmap[F] (fmap[U] (@counit _ _ _ _ A c)))
    ≈ fmap[U] (@counit _ _ _ _ A c) ∘ fmap[U] (@counit _ _ _ _ A (F (U c))).
Proof.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  apply adj_counit_natural.
Qed.

Definition EM_Comparison_Algebra (c : C) :
  @TAlgebra D (U ◯ F) Adjunction_Induced_Monad (U c) :=
  @Build_TAlgebra D (U ◯ F) Adjunction_Induced_Monad (U c)
    (fmap[U] (@counit _ _ _ _ A c))
    (EM_Comparison_Algebra_id c)
    (EM_Comparison_Algebra_action c).

(** U h intertwines the comparison algebras: the commuting square is the
    U-image of counit naturality at h. *)

Lemma EM_Comparison_fmap_commutes {c c' : C} (h : c ~> c') :
  fmap[U] h ∘ fmap[U] (@counit _ _ _ _ A c)
    ≈ fmap[U] (@counit _ _ _ _ A c') ∘ fmap[U] (fmap[F] (fmap[U] h)).
Proof.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  symmetry.
  apply adj_counit_natural.
Qed.

Definition EM_Comparison_fmap {c c' : C} (h : c ~> c') :
  @TAlgebraHom D (U ◯ F) Adjunction_Induced_Monad (U c) (U c')
    (EM_Comparison_Algebra c) (EM_Comparison_Algebra c') :=
  @Build_TAlgebraHom D (U ◯ F) Adjunction_Induced_Monad (U c) (U c')
    (EM_Comparison_Algebra c) (EM_Comparison_Algebra c')
    (fmap[U] h)
    (EM_Comparison_fmap_commutes h).

Lemma EM_Comparison_fmap_respects {c c' : C} (h h' : c ~> c') (E : h ≈ h') :
  fmap[U] h ≈ fmap[U] h'.
Proof. now rewrite E. Qed.

(** The comparison functor K : C ⟶ D^T.  Its functor laws are those of U,
    since morphisms of D^T are compared on their underlying arrows. *)

Definition EM_Comparison :
  C ⟶ @EilenbergMoore D (U ◯ F) Adjunction_Induced_Monad :=
  @Build_Functor C (@EilenbergMoore D (U ◯ F) Adjunction_Induced_Monad)
    (fun c => (U c; EM_Comparison_Algebra c))
    (fun c c' h => EM_Comparison_fmap h)
    (fun c c' h h' E => EM_Comparison_fmap_respects h h' E)
    (fun c => @fmap_id C D U c)
    (fun c c' c'' f g => @fmap_comp C D U c c' c'' f g).

(** Forgetting after comparing is U, on the nose: the iso family is the
    identity, mirroring [EM_Monad_agrees]. *)

Theorem EM_Comparison_Forget :
  @EM_Forget D (U ◯ F) Adjunction_Induced_Monad ◯ EM_Comparison ≈ U.
Proof.
  exists (fun c => iso_id).
  intros x y f; cbn.
  cat.
Qed.

(** Comparing after F is the free-algebra functor F^T.  At each d : D both
    sides yield the carrier U (F d) with structure map U ε_{F d} — the free
    algebra's join reads off exactly so, as in [EM_join_agrees] — but the
    two TAlgebra records package distinct proofs of the algebra laws, so the
    objects are not literally equal; the identity arrow of D underlies an
    isomorphism between them. *)

Lemma EM_Comparison_Free_id_commutes (d : D) :
  id ∘ fmap[U] (@counit _ _ _ _ A (F d))
    ≈ fmap[U] (@counit _ _ _ _ A (F d)) ∘ fmap[U] (fmap[F] id).
Proof.
  rewrite id_left.
  rewrite !fmap_id.
  now rewrite id_right.
Qed.

Definition EM_Comparison_Free_to (d : D) :
  fobj[EM_Comparison ◯ F] d
    ~{@EilenbergMoore D (U ◯ F) Adjunction_Induced_Monad}~>
  fobj[@EM_Free D (U ◯ F) Adjunction_Induced_Monad] d :=
  @Build_TAlgebraHom D (U ◯ F) Adjunction_Induced_Monad
    (U (F d)) (U (F d))
    (EM_Comparison_Algebra (F d))
    (`2 (fobj[@EM_Free D (U ◯ F) Adjunction_Induced_Monad] d))
    id
    (EM_Comparison_Free_id_commutes d).

Definition EM_Comparison_Free_from (d : D) :
  fobj[@EM_Free D (U ◯ F) Adjunction_Induced_Monad] d
    ~{@EilenbergMoore D (U ◯ F) Adjunction_Induced_Monad}~>
  fobj[EM_Comparison ◯ F] d :=
  @Build_TAlgebraHom D (U ◯ F) Adjunction_Induced_Monad
    (U (F d)) (U (F d))
    (`2 (fobj[@EM_Free D (U ◯ F) Adjunction_Induced_Monad] d))
    (EM_Comparison_Algebra (F d))
    id
    (EM_Comparison_Free_id_commutes d).

Lemma EM_Comparison_Free_id_id (d : D) :
  id[U (F d)] ∘ id ≈ id.
Proof. now rewrite id_left. Qed.

Definition EM_Comparison_Free_iso (d : D) :
  @Isomorphism (@EilenbergMoore D (U ◯ F) Adjunction_Induced_Monad)
    (fobj[EM_Comparison ◯ F] d)
    (fobj[@EM_Free D (U ◯ F) Adjunction_Induced_Monad] d) :=
  @Build_Isomorphism (@EilenbergMoore D (U ◯ F) Adjunction_Induced_Monad)
    (fobj[EM_Comparison ◯ F] d)
    (fobj[@EM_Free D (U ◯ F) Adjunction_Induced_Monad] d)
    (EM_Comparison_Free_to d)
    (EM_Comparison_Free_from d)
    (EM_Comparison_Free_id_id d)
    (EM_Comparison_Free_id_id d).

Theorem EM_Comparison_Free :
  EM_Comparison ◯ F ≈ @EM_Free D (U ◯ F) Adjunction_Induced_Monad.
Proof.
  exists EM_Comparison_Free_iso.
  intros x y f; cbn.
  cat.
Qed.

End EilenbergMooreComparison.

(** A functor U is monadic when it has a left adjoint whose Eilenberg–Moore
    comparison functor is an equivalence of categories. *)

Definition Monadic {C D : Category} (U : C ⟶ D) : Type :=
  ∃ (F : D ⟶ C) (A : F ⊣ U), EquivalenceOfCategories (EM_Comparison A).
