Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.

Generalizable All Variables.

(** * Commutative Frobenius algebras in a symmetric monoidal category *)

(* A Frobenius algebra is commutative when its multiplication is symmetric
   under the braiding, and equivalently when its comultiplication is
   cosymmetric.  In our library notation, with [braid : X ⨂ X ~> X ⨂ X] the
   symmetry, the two laws are

       mu ∘ braid ≈ mu              (commutativity of the monoid)
       braid ∘ delta ≈ delta        (cocommutativity of the comonoid)

   Over a symmetric monoidal category these two statements are equivalent
   (the bend/cap of the Frobenius structure turns either one into the
   other), but we record both as fields because both are useful as
   left-to-right rewrite rules.

   TQFT correspondence: commutative Frobenius algebras are exactly the
   algebraic data of (1+1)-dimensional / 2-dimensional TQFTs.  The category
   of commutative Frobenius algebras over a field [K] is equivalent to the
   category of symmetric strong monoidal functors from the 2-cobordism
   category [2Cob] to [Vect_K]: the circle is sent to the algebra, the
   "pair of pants" cobordism to [mu] (resp. [delta] read backwards), and
   the cap/cup disks to [eta] / [epsilon].

   nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
   nLab:      https://ncatlab.org/nlab/show/2-dimensional+TQFT
   Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra *)

Section CommutativeFrobenius.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeFrobenius (X : C) : Type := {
  cfrob_frobenius : @Frobenius C _ X;          (* underlying Frobenius algebra *)

  (* multiplication is invariant under the braiding: [mu ∘ braid ≈ mu] *)
  mu_commutative :
    (@mu _ _ _ (@frob_monoid _ _ _ cfrob_frobenius)) ∘ braid
      ≈ (@mu _ _ _ (@frob_monoid _ _ _ cfrob_frobenius));

  (* comultiplication is invariant under the braiding: [braid ∘ delta ≈ delta] *)
  delta_cocommutative :
    braid ∘ (@delta _ _ _ (@frob_comonoid _ _ _ cfrob_frobenius))
      ≈ (@delta _ _ _ (@frob_comonoid _ _ _ cfrob_frobenius))
}.
#[export] Existing Instance cfrob_frobenius.

Coercion cfrob_frobenius : CommutativeFrobenius >-> Frobenius.

End CommutativeFrobenius.

Arguments cfrob_frobenius {C S X _}.

(** ** Flat projections

    Convenience aliases paralleling [scfa_mu] / [scfa_eta] /
    [scfa_delta] / [scfa_epsilon] (in
    [Theory/Algebra/SpecialCommutativeFrobenius.v]) and [cmon_mu] /
    [cmon_eta] (in [Theory/Algebra/CommutativeMonoid.v]).  Use these
    to keep downstream goal states free of deeply-nested
    instance-projection chains. *)

Section CommutativeFrobeniusProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition cfrob_mu {X : C} (F : CommutativeFrobenius X)
  : (X ⨂ X)%object ~> X :=
  @mu _ _ _ (@frob_monoid _ _ _ (cfrob_frobenius (X := X))).

Definition cfrob_eta {X : C} (F : CommutativeFrobenius X)
  : @I _ _ ~> X :=
  @eta _ _ _ (@frob_monoid _ _ _ (cfrob_frobenius (X := X))).

Definition cfrob_delta {X : C} (F : CommutativeFrobenius X)
  : X ~> (X ⨂ X)%object :=
  @delta _ _ _ (@frob_comonoid _ _ _ (cfrob_frobenius (X := X))).

Definition cfrob_epsilon {X : C} (F : CommutativeFrobenius X)
  : X ~> @I _ _ :=
  @epsilon _ _ _ (@frob_comonoid _ _ _ (cfrob_frobenius (X := X))).

End CommutativeFrobeniusProjections.

Arguments cfrob_mu      {C S X} F.
Arguments cfrob_eta     {C S X} F.
Arguments cfrob_delta   {C S X} F.
Arguments cfrob_epsilon {C S X} F.
