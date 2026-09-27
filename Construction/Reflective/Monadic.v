(** * The inclusion of a reflective subcategory is monadic

    Riehl, "Category Theory in Context", §5.3, printed p. 196 (PDF
    p. 216), read from the page image.  Definition 5.3.1: an adjunction
    "is monadic if the canonical comparison functor of Proposition
    5.2.13 from D to the category of algebras for the underlying monad
    on C defines an equivalence of categories", and a functor is monadic
    when it has a left adjoint whose adjunction is monadic (the second
    sentence of the definition, paraphrased).  Proposition 5.3.3 (ii):
    "The inclusion D ↪ C of a reflective subcategory is monadic: that
    is, the functor K from D to the category of algebras C^L for the
    induced idempotent monad L is an equivalence of categories."
    Exercise 5.3.ii, printed p. 197 (PDF p. 217), catalog item
    riehl:5.3:exii: "Revisit your favorite example of an reflective
    subcategory from Examples 4.6.13 and use Proposition 5.3.3 to give
    an equivalent presentation of this subcategory as the category of
    algebras for an idempotent monad."
    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §IV.3, printed p. 91 (PDF p. 100), read from the page image, for
    the notion itself: "A subcategory A of B is called reflective in B
    when the inclusion functor K: A → B has a left adjoint F: B → A."
    nLab: https://ncatlab.org/nlab/show/reflective+subcategory
    nLab: https://ncatlab.org/nlab/show/monadic+functor
    nLab: https://ncatlab.org/nlab/show/idempotent+monad

    BACKGROUND.  nLab's reflective-subcategory page states the fact as a
    proposition -- "Every reflective subcategory inclusion is a monadic
    functor, exhibiting the reflective subcategory as the
    Eilenberg-Moore category of modules for its induced idempotent
    monad" -- with the converse, and points to Borceux's Handbook,
    vol. 2, Cor. 4.2.4, for a proof.  Riehl proves the essential
    surjectivity of K from the characterization of the algebras of an
    idempotent monad (an object carries an algebra structure exactly
    when its unit is invertible, the structure map being the inverse)
    and concludes by her Theorem 1.5.9.  The route here is the same in
    outline: full, faithful and essentially surjective, then
    Theory/Equivalence/FullFaithful.v's [FF_ESO_Equivalence].

    WHAT THIS ADDS TO Construction/Reflective/Idempotent.v.  That file
    already has both directions of the correspondence and the
    Eilenberg–Moore reading, but its [Idempotent_EM_Equivalence] is an
    equivalence between the algebras of an idempotent monad and that
    monad's M-LOCAL subcategory [MLocal_Subcategory], not the subcategory
    a reflection started from.  Fed a reflection, it lands on the
    objects at which the unit is invertible, which is a different
    [Subcategory] record.  This file instead takes Monad/Comparison.v's
    [EM_Comparison] of the reflection itself, [reflective_comparison R :
    Sub C S ⟶ EilenbergMoore (Incl ◯ reflector R)], and proves THAT an
    equivalence, so the subcategory S is itself presented as the
    algebras ([Reflective_EM_Equivalence]) and its inclusion is monadic
    in Monad/Comparison.v's own sense ([Reflective_Monadic]).  The monad
    is Idempotent.v's [Reflective_Monad R], which is
    [Adjunction_Induced_Monad (reflective_adj R)] by definition, so the
    two developments speak about one category of algebras.

    THE PROOF.  Faithful: morphisms of algebras are compared on their
    underlying arrows.  Full: an algebra morphism between comparison
    algebras is an arrow of C between objects of S, lifted by the
    record's fullness field ([reflective_comparison_prefmap]).
    Essentially surjective: the chosen preimage of an algebra (a, α) is
    the reflection of a ([reflective_eso_obj]); the isomorphism has α
    as its forward leg and the unit as its backward leg, with the
    algebra laws [t_id] and [t_action] and Idempotent.v's
    [algebra_ret_iso] as the four obligations.  The witness of
    [algebra_ret_iso] is bound with [pose] rather than [pose proof], and
    that is load-bearing: in a copy using [pose proof] the step
    [exact (is_right_inverse Hret)] is refused, its type reading
    [ret ∘ two_sided_inverse ≈ id] where [unit ∘ t_alg[alg] ≈ id] is
    wanted.

    STRENGTHS.  The five [Example]s hold at [eq_refl]: the comparison
    sends an object of S to its own carrier ([reflective_comparison_obj])
    with the counit, read through the inclusion, as the structure map
    ([reflective_comparison_alg]); the chosen preimage IS the reflection
    of the carrier ([reflective_eso_obj_is_reflector]); the forward leg
    of the isomorphism IS the algebra's structure map
    ([reflective_eso_iso_to]); and the left adjoint of the monadic
    witness IS the reflector ([Reflective_Monadic_left]).  No constant
    is closed with [Qed].  Concrete instances: Instance/Ab/Torsion.v
    ([TorsionFree_EM_Equivalence], [TorsionFree_Incl_Monadic], at #371's
    torsion-free reflection) and Instance/Grp/Abelianize/Reflective.v
    ([AbGrp_Incl_Monadic]).

    UNIVERSES, read by [About] under [Set Printing Universes] on all
    fourteen constants.  Each carries the binder [@{o h +}] with
    [C : Category@{o h h}] and binds S at [Subcategory@{o h s h}] for a
    level s of its own: the hom-with-proof identification is
    [Subcategory]'s, and the fourth level's identification with h is
    [Reflective]'s own binder ([Subcategory@{u3 u5 u4 u5}]).  No
    constraint block carries an equation or mentions [Set], and every
    global universe in them ([Basics.compose.u0]-[u2], [ID.u0],
    [Projections.u0]/[u1]) is an upper bound.  Against a copy with
    every binder removed, compared under [Set Printing All], every
    constant has the same number of universes and the same
    identifications.

    NOT DELIVERED.
      - No comparison between [reflective_comparison R] and
        Idempotent.v's [idem_G], and no equivalence between S and the
        M-local subcategory of its monad.
      - No strict monadicity: the comparison is an equivalence, not an
        isomorphism of categories.
      - No comonadic statement for a coreflection, although
        [Reflective_Monadic] applies to a [Coreflective] record (which
        is a [Reflective] one in the opposite category) as it stands.
      - The monadicity here is proved directly; Beck's theorem
        (Monad/Monadicity/Beck.v) is not used. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.

Generalizable All Variables.

(** ** The comparison functor of a reflection *)

(* [Reflective_Monad R] is [Adjunction_Induced_Monad (reflective_adj R)]
   by definition, so the Eilenberg–Moore comparison of the reflection
   lands in the category of algebras for the idempotent monad
   Construction/Reflective/Idempotent.v attaches to [R]. *)
Definition reflective_comparison@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Sub C S ⟶ @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)
  := EM_Comparison (reflective_adj R).

Definition reflective_comparison_Faithful@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Faithful (reflective_comparison R).
Proof. constructor; intros x y f g H; exact H. Defined.

(* A morphism of algebras between two comparison algebras is an arrow of
   C between objects of the subcategory; fullness of the subcategory puts
   it back in [Sub C S]. *)
Definition reflective_comparison_prefmap@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) {s t : Sub C S}
  (h : reflective_comparison R s ~> reflective_comparison R t) : s ~> t :=
  (t_alg_hom[h]; reflective_full R _ _ `2 s `2 t t_alg_hom[h]).

Definition reflective_comparison_Full@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Functor.Full (reflective_comparison R).
Proof.
  refine {| prefmap := @reflective_comparison_prefmap C S R |}.
  intros s t h; simpl; reflexivity.
Defined.

(* The chosen preimage of an algebra (a, α) is the reflection of [a]. *)
Definition reflective_eso_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  Sub C S := reflector R ``z.

(* The comparison algebra at the reflection of [a] is isomorphic to
   (a, α): forward the structure map α, backward the unit.  That the unit
   is inverse to α is Idempotent.v's [algebra_ret_iso]; the witness is
   bound with [pose] so that its inverse stays a reduct of α. *)
Definition reflective_eso_iso@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  reflective_comparison R (reflective_eso_obj R z) ≅ z.
Proof.
  destruct z as [a alg].
  pose (Hret := @algebra_ret_iso C _ (Reflective_Monad R)
                  (Reflective_IdempotentMonad R) a alg).
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R))
       (reflective_comparison R (reflective_eso_obj R (a; alg))) (a; alg)
       _ _ _ _).
  - refine (@Build_TAlgebraHom C _ (Reflective_Monad R) _ _ _ _
              (t_alg[alg]) _).
    simpl. symmetry. exact (@t_action C _ (Reflective_Monad R) a alg).
  - refine (@Build_TAlgebraHom C _ (Reflective_Monad R) _ _ _ _
              (@ret C _ (Reflective_Monad R) a) _).
    simpl.
    transitivity (@id C (fobj[Incl C S ◯ reflector R] a)).
    + exact (@is_right_inverse C _ _ _ Hret).
    + symmetry. exact (@join_fmap_ret C _ (Reflective_Monad R) a).
  - simpl. exact (@t_id C _ (Reflective_Monad R) a alg).
  - simpl. exact (@is_right_inverse C _ _ _ Hret).
Defined.

Definition reflective_comparison_ESO@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  EssentiallySurjective (reflective_comparison R) :=
  @Build_EssentiallySurjective _ _ (reflective_comparison R)
    (reflective_eso_obj R) (reflective_eso_iso R).

(** ** Riehl, Proposition 5.3.3 (ii) *)

(* The subcategory ITSELF is equivalent to the algebras of the induced
   idempotent monad, by the comparison functor. *)
Definition Reflective_EM_Equivalence@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  EquivalenceOfCategories (reflective_comparison R) :=
  @FF_ESO_Equivalence _ _ (reflective_comparison R)
    (reflective_comparison_Full R) (reflective_comparison_Faithful R)
    (reflective_comparison_ESO R).

(* The inclusion of a reflective subcategory is monadic, in
   Monad/Comparison.v's sense: the reflector, the reflection, and the
   equivalence above. *)
Definition Reflective_Monadic@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) : Monadic (Incl C S) :=
  (reflector R; (reflective_adj R; Reflective_EM_Equivalence R)).

(** ** Readbacks *)

(* The comparison sends an object of the subcategory to its own carrier,
   with the counit read through the inclusion as the structure map. *)
Example reflective_comparison_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (s : Sub C S) :
  ``(reflective_comparison R s) = `1 s := eq_refl.

Example reflective_comparison_alg@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (s : Sub C S) :
  t_alg[projT2 (reflective_comparison R s)]
    = fmap[Incl C S] (@counit _ _ _ _ (reflective_adj R) s) := eq_refl.

(* The chosen preimage of an algebra is the reflection of its carrier. *)
Example reflective_eso_obj_is_reflector@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  reflective_eso_obj R z = fobj[reflector R] ``z := eq_refl.

(* The isomorphism's forward leg IS the algebra's structure map. *)
Example reflective_eso_iso_to@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (a : C)
  (alg : @TAlgebra C _ (Reflective_Monad R) a) :
  t_alg_hom[to (reflective_eso_iso R (a; alg))] = t_alg[alg] := eq_refl.

(* The monadic witness's left adjoint is the reflector itself. *)
Example Reflective_Monadic_left@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  `1 (Reflective_Monadic R) = reflector R := eq_refl.
