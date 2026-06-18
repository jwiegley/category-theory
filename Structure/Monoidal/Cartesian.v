Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Export Category.Structure.Monoidal.Relevance.
Require Export Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

Section CartesianMonoidal.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/cartesian+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   A cartesian monoidal category is a monoidal category whose tensor is the
   categorical product and whose unit is a terminal object. In this library's
   notation that means

       x ⨂ y   is the product  x × y,
       I       is the terminal object  1,

   with the associator, unitors and braiding all induced by the universal
   property of products. We do not assume products outright; instead we
   characterise the same structure from the two halves that, combined, force
   the tensor to be a product: a coherent diagonal (RelevanceMonoidal,
   copying) and a terminal unit (SemicartesianMonoidal, discarding). The two
   proj_*_diagonal laws below are exactly the missing compatibility that makes
   the result cartesian — this is Fox's theorem (Fox 1976), stated on nLab as:
   a symmetric monoidal category with natural diagonals ∆ and augmentations e
   is cartesian iff proj_left ∘ ∆ ≈ id and proj_right ∘ ∆ ≈ id, where
   proj_left = unit_right ∘ id ⨂ eliminate and proj_right = unit_left ∘
   eliminate ⨂ id (see Semicartesian.v).

   Wikipedia: "Cartesian monoidal categories have a number of special and
   important properties, such as the existence of diagonal maps (Δ) x : x → x
   ⨂ x and augmentations (e) x : x → I for any object x. In applications to
   computer science we can think of (Δ) as 'duplicating data' and (e) as
   'deleting' data. These maps make any object into a comonoid. In fact, any
   object in a cartesian monoidal category becomes a comonoid in a unique way.

   Moreover, one can show (e.g. Heunen-Vicary 12, p. 84) that any symmetric
   monoidal category equipped with suitably well-behaved diagonals and
   augmentations must in fact be cartesian monoidal." *)

Class CartesianMonoidal := {
  cartesian_is_relevance     : @RelevanceMonoidal C;
  cartesian_is_semicartesian : @SemicartesianMonoidal C _;

  (* Fox's coherence: copying then discarding one copy is the identity. These
     two laws are precisely what upgrades the relevance + semicartesian data to
     a genuine product (tensor = ×), per the nLab characterisation above. *)
  proj_left_diagonal  {x} : proj_left  ∘ diagonal ≈ id[x];
  proj_right_diagonal {x} : proj_right ∘ diagonal ≈ id[x];

  (* Unit/braiding coherence λ ∘ σ ≈ ρ and ρ ∘ σ ≈ λ at the unit. In a
     symmetric monoidal category these are derivable from Mac Lane's coherence
     theorem rather than minimal; they are kept as explicit fields here because
     this library's SymmetricMonoidal does not expose that derivation, and
     downstream proofs (e.g. Cartesian/Proofs.v, Group/Proofs.v) rewrite with
     them directly. *)
  unit_left_braid  {x} : unit_left  ∘ @braid _ _ x I ≈ unit_right;
  unit_right_braid {x} : unit_right ∘ @braid _ _ I x ≈ unit_left
}.
#[export] Existing Instance cartesian_is_semicartesian.
#[export] Existing Instance cartesian_is_relevance.

Coercion cartesian_is_relevance : CartesianMonoidal >-> RelevanceMonoidal.
Coercion cartesian_is_semicartesian : CartesianMonoidal >-> SemicartesianMonoidal.

Context `{CartesianMonoidal}.

(* The product action on morphisms, built from the projections and fork (the
   pairing ⟨-,-⟩ = (- ⨂ -) ∘ ∆ supplied by RelevanceMonoidal). With a genuine
   product available these agree with the usual combinators: [first f] runs f
   on the left factor and keeps the right, [second f] does the dual, and
   [split f g] = f ⨂ g acts componentwise (the bifunctorial action). *)

Definition first  {x y z : C} (f : x ~> y) : x ⨂ z ~> y ⨂ z :=
  fork (f ∘ proj_left) proj_right.

Definition second  {x y z : C} (f : x ~> y) : z ⨂ x ~> z ⨂ y :=
  fork proj_left (f ∘ proj_right).

Definition split  {x y z w : C} (f : x ~> y) (g : z ~> w) :
  x ⨂ z ~> y ⨂ w :=
  fork (f ∘ proj_left) (g ∘ proj_right).

#[export] Program Instance first_respects {a b c : C} :
  Proper (equiv ==> equiv) (@first a b c).
Next Obligation.
  proper.
  unfold first.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance second_respects {a b c : C} :
  Proper (equiv ==> equiv) (@second a b c).
Next Obligation.
  proper.
  unfold second.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance split_respects {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@split a b c d).
Next Obligation.
  proper.
  unfold split.
  rewrites.
  reflexivity.
Qed.

End CartesianMonoidal.
