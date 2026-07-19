Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.

Generalizable All Variables.

(** * Preadditive categories *)

(* nLab:      https://ncatlab.org/nlab/show/preadditive+category
   Wikipedia: https://en.wikipedia.org/wiki/Preadditive_category

   A preadditive category in the classical sense is a category enriched in
   abelian groups: every hom-set is an abelian group and composition is
   bilinear.  The class below records the additive skeleton of that notion
   in setoid form: each hom-setoid carries a commutative monoid structure
   ([padd] with unit [pzero]) that respects ≈, composition distributes over
   addition on both sides, and the zero morphism absorbs composition on
   both sides.  Additive inverses are deliberately not demanded, so the
   class is precisely enrichment in commutative monoids (CMon-enrichment);
   every Ab-enriched category is an instance, and this much structure
   already supports biproducts and the matrix calculus.  The laws are
   self-dual, so C^op is preadditive whenever C is.

   The additive notations live in their own [addition_scope] (key %padd),
   keeping `+` and `0` untouched elsewhere; users opt in locally with
   `Open Scope addition_scope` or the %padd scope key.

   When the category also has a zero object, the enrichment zero agrees
   with the tunnelled zero morphism of Structure/ZeroObject.v; this is
   [pzero_zero_mor] below. *)

Class Preadditive (C : Category) := {
  padd {x y : C} : (x ~> y) -> (x ~> y) -> (x ~> y);
  pzero {x y : C} : x ~> y;

  padd_respects {x y : C} :
    Proper (equiv ==> equiv ==> equiv) (@padd x y);

  (* (hom(x,y), padd, pzero) is a commutative monoid. *)
  padd_assoc {x y : C} (f g h : x ~> y) :
    padd (padd f g) h ≈ padd f (padd g h);
  padd_comm {x y : C} (f g : x ~> y) :
    padd f g ≈ padd g f;
  padd_zero_left {x y : C} (f : x ~> y) :
    padd pzero f ≈ f;

  (* Composition is additive in each argument separately. *)
  compose_padd_left {x y z : C} (h : y ~> z) (f g : x ~> y) :
    h ∘ padd f g ≈ padd (h ∘ f) (h ∘ g);
  compose_padd_right {x y z : C} (f g : y ~> z) (h : x ~> y) :
    padd f g ∘ h ≈ padd (f ∘ h) (g ∘ h);

  (* The additive unit absorbs composition on both sides. *)
  compose_pzero_left {x y z : C} (f : x ~> y) :
    @pzero y z ∘ f ≈ pzero;
  compose_pzero_right {x y z : C} (f : y ~> z) :
    f ∘ @pzero x y ≈ pzero
}.

#[export] Existing Instance padd_respects.

(* The right unit law follows from commutativity and the left unit law. *)
Corollary padd_zero_right {C : Category} `{P : @Preadditive C} {x y : C}
  (f : x ~> y) :
  padd f pzero ≈ f.
Proof.
  rewrite padd_comm.
  apply padd_zero_left.
Qed.

(* Additive notations in a dedicated scope, so `+` and `0` retain their
   usual meanings wherever this scope is not open. *)
Declare Scope addition_scope.
Delimit Scope addition_scope with padd.

Infix "+" := padd : addition_scope.
Notation "0" := pzero : addition_scope.

(* Compatibility with zero objects: in a preadditive category that also has
   a zero object, the enrichment zero [pzero] coincides with the canonical
   zero morphism x ~> 1 ~> 0 ~> y of Structure/ZeroObject.v.  The proof
   exhibits [pzero] as a morphism factoring through the zero object —
   [compose_pzero_left] collapses each tunnelling leg — after which
   [zero_mor_unique] identifies it with [zero_mor]. *)
Lemma pzero_zero_mor {C : Category} `{P : @Preadditive C} `{Z : @ZeroObject C}
  {x y : C} :
  @pzero C P x y ≈ @zero_mor C Z x y.
Proof.
  rewrite <- (@zero_mor_unique C Z x y
                (@one C (@zero_terminal C Z) x)
                (@pzero C P (@initial_obj C (@zero_initial C Z)) y)).
  (* Goal: pzero ≈ (pzero ∘ from zero_coincide) ∘ one.  Each composite with
     [pzero] on the left collapses by [compose_pzero_left]. *)
  rewrite compose_pzero_left.
  rewrite compose_pzero_left.
  reflexivity.
Qed.
