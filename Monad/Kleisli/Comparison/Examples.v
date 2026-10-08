Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Skeleton.
Require Import Category.Theory.Skeleton.Separation.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Kleisli.Comparison.

Generalizable All Variables.

(** * The one-point monad on Sets: Exercise 3, and every algebra free *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.5, Exercise 3, printed p. 148 (PDF
         p. 157) — maclane:VI.5:ex3
   Book: Riehl, "Category Theory in Context", the paragraph after Lemma
         5.2.14, printed p. 194 (PDF p. 214) — riehl:5.2:lem14
   nLab: https://ncatlab.org/nlab/show/Kleisli+category

   WHAT THE BOOKS SAY, read from the page image and the PDF.  Mac Lane:
   "Construct an example of an adjunction where F is not a bijection on
   objects.  Deduce that the equivalence X_T → FX in Exercise 2 need not
   be an isomorphism.  (Suggestion: S ↦ T(S) = the one-point-set defines
   a monad in Set.)"  Exercise 2 is Monad/Kleisli/Comparison.v's, with
   Theorem 2's comparison functor L : X_T → A and FX the full
   subcategory of A on the objects F x.  Riehl: "Lemma 5.2.14 also tells
   us precisely when the Kleisli and Eilenberg–Moore categories are
   equivalent: this is the case when all algebras are free."

   THE ADJUNCTION.  [kleisli_point_adj] is Adjunction/LeftInverse.v's
   [point_adj] at Instance/Sets.v's terminal object, Erase ⊣ PointAt 1,
   the adjunction Sets ⇀ 1 whose left adjoint F = [Erase] sends every
   setoid to the one object of 1; it is reused, and no second adjunction
   is built.  The monad it defines, Monad/Comparison.v's
   [Adjunction_Induced_Monad], is Mac Lane's S ↦ T(S) = the one-point
   set ([kleisli_point_monad_obj], at [eq_refl]).  F is not a bijection
   on objects: it is not injective ([kleisli_point_F_not_injective]),
   the empty setoid and the one-point setoid, Sets' initial and terminal
   objects ([kleisli_point_empty], [kleisli_point_one]), being distinct
   ([kleisli_point_distinct], by their carriers [False] and [poly_unit]).

   FX.  Here FX is Mac Lane's set of objects {F x}: the one object of 1,
   which is F of every setoid.  So FX is all of 1, and the restriction of
   L to FX is L : X_T ⟶ 1 itself ([Kleisli_Comparison]), surjective on
   objects ([kleisli_point_surjective], the chosen preimage being the
   one-point setoid).  As a full subcategory of 1, FX is
   [kleisli_point_FX], on every object with membership the proposition
   [True] ([kleisli_point_FX_full]), and the chooser Comparison.v's
   Exercise 2 asks of it, [kleisli_point_FX_pick], picks the one-point
   setoid.  Comparison.v's proof-relevant image [LaliImageSub] of F would
   instead have an object for every setoid, and its corestriction of L
   is an isomorphism, as there for every adjunction
   ([Kleisli_Comparison_Image_StrictIso]).

   THE EQUIVALENCE HOLDS.  L is full and faithful (Comparison.v's
   [Kleisli_Comparison_Full], [Kleisli_Comparison_Faithful]) and
   surjective on objects, so [kleisli_point_equivalence] makes L an
   equivalence X_T ≃ 1 (Theory/Equivalence/Strict.v's
   [ff_surj_eso_equivalence]).  Exercise 2's equivalence X_T → FX
   itself, Comparison.v's general [Kleisli_Comparison_Restrict_Equivalence]
   at [kleisli_point_FX], is [kleisli_point_FX_equivalence].

   IT IS NOT AN ISOMORPHISM.  L is not injective on objects
   ([kleisli_point_L_not_injective]), and X_T is not isomorphic to 1 in
   Instance/StrictCat.v by any functor at all ([kleisli_point_not_iso]):
   1 is skeletal (Theory/Skeleton/Separation.v's [One_Skeletal]),
   skeletality is invariant under isomorphism in StrictCat
   (Theory/Skeleton.v's [Skeletal_StrictCat_invariant]), and X_T is not
   skeletal ([kleisli_point_not_skeletal]): the empty and the one-point
   setoid are distinct objects of X_T, isomorphic there because
   X_T(S, S') = Sets(S, T S') = Sets(S, 1) has one arrow up to ≈.  Nor
   is X_T isomorphic in StrictCat to FX as the full subcategory
   [kleisli_point_FX] ([kleisli_point_FX_not_iso]), which is skeletal
   too ([kleisli_point_FX_skeletal]): Exercise 2's equivalence is not an
   isomorphism.  The three are constructive theorems, with no axiom.

   EVERY ALGEBRA IS FREE.  The monad also witnesses the premise of
   Comparison.v's [Kleisli_EM_equivalence_iff], Riehl's "all algebras
   are free".  For an algebra (A, h), h : T A = 1 ~> A and the unique
   arrow ! : A ~> 1 are inverse, h ∘ ! being h ∘ η = id by terminality
   and the unit law, and ! ∘ h the identity of 1 by terminality; so
   (A, h) is isomorphic, by h, to the free algebra on A
   ([kleisli_point_every_algebra_free]), and K : C_T ⟶ C^T is an
   equivalence, by the biconditional read from right to left
   ([kleisli_point_K_equivalence]).  The identity monad would serve as
   well: a witness at Monad/Identity.v's [IdMonad] compiles, closed, in
   a scratch file, and is not built here.

   STRENGTHS.  [kleisli_point_monad_obj] holds at [eq_refl] (control C35
   of Test/ProbeKleisliComparison475.v).  Three proofs end [Defined]
   (counted by token), [kleisli_point_surjective], [kleisli_point_FX_pick]
   and [kleisli_point_every_algebra_free], each by the data convention
   only (closed [Qed] alone, nothing stops, measured in a renamed copy of
   the two files and the probe); seven end [Qed].

   UNIVERSES, read off [About] (every name, by script).  The section
   declares two levels, o and so, and states every name in it over
   Sets@{o so}, for readability only: a copy with the declaration removed
   and Sets@{o so} written Sets compiles.  Each of its sixteen names is
   universe polymorphic and binds two to ten levels, with o < so; the
   three before it, [kleisli_point_FX], [kleisli_point_FX_full] and
   [kleisli_point_FX_skeletal], are about 1 alone and bind four to seven
   levels of their own.  No block mentions [Set] or carries an equation,
   the same on Coq 8.19.2 and 8.20.1 (Comparison.v's census).  No
   explicit universe instance of a constant #475 adds is written.

   NOT DELIVERED.  Nothing the exercise asks is left out.  The isomorphism
   refuted here is the one with Mac Lane's FX; with the proof-relevant
   image the corestriction is an isomorphism (above).  The identity
   monad's witness of "every algebra free" is not built (above), and
   Riehl's own two witnesses are issue #1359's. *)

(* Mac Lane's FX in 1, all of it: a full subcategory on every object, its
   membership a proposition.  It does not mention Sets. *)
Definition kleisli_point_FX : Subcategory _1 :=
  @Build_Subcategory _1 (fun _ => True) (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I) (fun _ _ => I).

Definition kleisli_point_FX_full :
  Construction.Subcategory.Full _1 kleisli_point_FX := fun _ _ _ _ _ => I.

Lemma kleisli_point_FX_skeletal : Skeletal (Sub _1 kleisli_point_FX).
Proof. intros [a p] [b q] _. destruct a, b, p, q. reflexivity. Qed.

Section PointMonad.

Universes o so.

Notation SetsC := Sets@{o so}.

Definition kleisli_point_adj :
  Erase SetsC ⊣ PointAt (@terminal_obj SetsC Sets_Terminal) :=
  point_adj Sets_Terminal.

Notation T1 := (Adjunction_Induced_Monad kleisli_point_adj).
Notation XT1 := (@Kleisli SetsC (PointAt _ ◯ Erase SetsC) T1).

(* S ↦ T(S) = the one-point set. *)
Example kleisli_point_monad_obj (S : SetsC) :
  fobj[PointAt (@terminal_obj SetsC Sets_Terminal) ◯ Erase SetsC] S
    = @terminal_obj SetsC _ := eq_refl.

Definition kleisli_point_empty : SetsC := @initial_obj SetsC Sets_Initial.
Definition kleisli_point_one : SetsC := @terminal_obj SetsC Sets_Terminal.

Lemma kleisli_point_distinct : kleisli_point_empty = kleisli_point_one → False.
Proof.
  intro e.
  pose proof (f_equal carrier e) as e1.
  simpl in e1.
  exact (match eq_sym e1 in _ = P return P with eq_refl => ttt end).
Qed.

(* F is not injective on objects, so not a bijection on objects. *)
Lemma kleisli_point_F_not_injective :
  InjectiveOnObjects (Erase SetsC) → False.
Proof.
  intro H. apply kleisli_point_distinct. apply H. reflexivity.
Qed.

(* Neither is the comparison L. *)
Lemma kleisli_point_L_not_injective :
  InjectiveOnObjects (Kleisli_Comparison kleisli_point_adj) → False.
Proof.
  intro H. apply kleisli_point_distinct. apply H. reflexivity.
Qed.

(* FX is all of 1: its one object is F x; L is surjective on objects. *)
Definition kleisli_point_surjective :
  SurjectiveOnObjects (Kleisli_Comparison kleisli_point_adj).
Proof.
  intros c. exists kleisli_point_one. destruct c. reflexivity.
Defined.

Definition kleisli_point_equivalence :
  EquivalenceOfCategories (Kleisli_Comparison kleisli_point_adj) :=
  @ff_surj_eso_equivalence XT1 _ (Kleisli_Comparison kleisli_point_adj)
    _ _ kleisli_point_surjective.

(* ... but X_T is not isomorphic to 1 = FX. *)
Lemma kleisli_point_not_skeletal : Skeletal XT1 → False.
Proof.
  intro SK.
  apply kleisli_point_distinct.
  apply SK.
  unshelve eapply Build_Isomorphism.
  - exact (@one SetsC Sets_Terminal _).
  - exact (@one SetsC Sets_Terminal _).
  - apply (@one_unique SetsC Sets_Terminal).
  - apply (@one_unique SetsC Sets_Terminal).
Qed.

Theorem kleisli_point_not_iso : @Isomorphism StrictCat XT1 _1 → False.
Proof.
  intro i.
  apply kleisli_point_not_skeletal.
  exact (Skeletal_StrictCat_invariant (iso_sym i) One_Skeletal).
Qed.

(* Its chooser: the one object of 1 is F of the one-point setoid. *)
Definition kleisli_point_FX_pick (a : _1) (m : sobj _1 kleisli_point_FX a) :
  { x : SetsC & Erase SetsC x ≅ a }.
Proof. exists kleisli_point_one. destruct a. apply iso_id. Defined.

(* Exercise 2's equivalence X_T → FX, the general theorem at this FX... *)
Definition kleisli_point_FX_equivalence :
  EquivalenceOfCategories
    (Kleisli_Comparison_Restrict kleisli_point_adj kleisli_point_FX
       kleisli_point_FX_full (fun _ => I)) :=
  Kleisli_Comparison_Restrict_Equivalence kleisli_point_adj kleisli_point_FX
    kleisli_point_FX_full (fun _ => I) kleisli_point_FX_pick.

(* ... is not an isomorphism. *)
Theorem kleisli_point_FX_not_iso :
  @Isomorphism StrictCat XT1 (Sub _1 kleisli_point_FX) → False.
Proof.
  intro i.
  apply kleisli_point_not_skeletal.
  exact (Skeletal_StrictCat_invariant (iso_sym i) kleisli_point_FX_skeletal).
Qed.

(* Every algebra of the one-point monad is free: its structure map
   h : T A = 1 ~> A and the unique arrow A ~> 1 are inverse. *)
Definition kleisli_point_every_algebra_free : @EveryAlgebraFree SetsC _ T1.
Proof.
  intros [A alg].
  exists A.
  unshelve eapply Build_Isomorphism.
  - unshelve econstructor.
    + exact (@t_alg _ _ _ _ alg).
    + symmetry. exact (@t_action _ _ _ _ alg).
  - unshelve econstructor.
    + exact (@one SetsC Sets_Terminal A).
    + apply (@one_unique SetsC Sets_Terminal).
  - assert (E : @t_alg _ _ _ _ alg ∘ @one SetsC Sets_Terminal A ≈ id[A]).
    { rewrite (@one_unique SetsC Sets_Terminal A (@one SetsC Sets_Terminal A)
                 (@ret SetsC _ T1 A)).
      apply (@t_id _ _ _ _ alg). }
    exact E.
  - exact (@one_unique SetsC Sets_Terminal _
             (@one SetsC Sets_Terminal _ ∘ @t_alg _ _ _ _ alg) id).
Defined.

(* Hence K : C_T ⟶ C^T is an equivalence here, by the biconditional. *)
Definition kleisli_point_K_equivalence :
  EquivalenceOfCategories (@Kleisli_EM SetsC _ T1) :=
  snd (Kleisli_EM_equivalence_iff _) kleisli_point_every_algebra_free.

End PointMonad.
