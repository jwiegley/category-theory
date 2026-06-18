Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Strong.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.

Generalizable All Variables.

(** Applicative functors. *)

(* nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   An applicative functor is the categorical structure underlying the
   Haskell [Applicative] class (McBride and Paterson, "Applicative
   programming with effects", JFP 18(1), 2008): it is precisely a strong lax
   monoidal endofunctor on a (closed, symmetric/braided) monoidal category.
   Here it is packaged as an endofunctor F : C ⟶ C on a monoidal closed
   category that is both [StrongFunctor] and [LaxMonoidalFunctor].

   Under that characterization the two operations of the FP class correspond
   to the comparison maps of the lax monoidal structure:

       pure : x ~> F x          ↔ the unit comparison (built in [Pure] from
                                   lax_pure : I ~> F I and the strength),
       ap   : F (x ⇒ y) ⨂ F x   ↔ the tensor comparison lax_ap (μ), composed
              ~> F y              with F eval through the internal hom ⇒.

   The closed structure supplies the internal hom ⇒ and its evaluation
   eval : (x ⇒ y) ⨂ x ~> y, which is what turns the bare tensor comparison
   F (x ⇒ y) ⨂ F x ~> F ((x ⇒ y) ⨂ x) into the Haskell-style <*>.  This is
   the categorical, law-respecting account; the lawless FP type class lives
   in Theory/Coq/Applicative.v. *)

Section ApplicativeFunctor.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.

Class Applicative := {
  applicative_is_strong : StrongFunctor F;             (* tensorial strength *)
  applicative_is_lax_monoidal : LaxMonoidalFunctor F;  (* lax monoidal: η and μ *)

  (* <*> recovered from the tensor comparison μ = lax_ap and F eval *)
  ap {x y} : F (x ⇒ y) ⨂ F x ~> F y :=
    fmap[F] eval ∘ @lax_ap _ _ _ _ F _ (x ⇒ y) x
}.
#[export] Existing Instance applicative_is_strong.
#[export] Existing Instance applicative_is_lax_monoidal.

Coercion applicative_is_strong : Applicative >-> StrongFunctor.
Coercion applicative_is_lax_monoidal : Applicative >-> LaxMonoidalFunctor.

End ApplicativeFunctor.

Arguments Applicative {_ _} F.
Arguments pure {C _ F _ _ _}.

Notation "pure[ F ]" := (@pure _ _ F _ _ _)
  (at level 0, format "pure[ F ]") : morphism_scope.
