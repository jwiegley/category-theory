Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Monoid objects in a monoidal category *)

(* nLab:      https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   Given a monoidal category (C, ⨂, I), a monoid object on an object [mon : C]
   is a triple (mon, mappend, mempty) consisting of a multiplication
   [mappend : mon ⨂ mon ~> mon] and a unit [mempty : I ~> mon] subject to the
   associativity and left/right unit laws, with the associator and unitors
   inserted so the maps compose:

     associativity  mappend ∘ (mappend ⨂ id) ≈ mappend ∘ (id ⨂ mappend) ∘ α
     left unit      mappend ∘ (mempty ⨂ id)  ≈ λ
     right unit     mappend ∘ (id ⨂ mempty)  ≈ ρ

   Here ⨂ on morphisms is [bimap], α = [to tensor_assoc] is the associator
   (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon), and λ = [to unit_left],
   ρ = [to unit_right] are the left/right unitors I ⨂ mon ≅ mon and
   mon ⨂ I ≅ mon. This is exactly the nLab/Wikipedia definition (the names
   [mempty]/[mappend] echo Haskell's [Monoid] type class).

   Relationship to [Theory.Algebra.Monoid]: that file defines the very same
   structure under the name [Monoid] with fields [mu]/[eta], as a standalone
   abstract building block (used for Frobenius algebras and dualised to give
   comonoids). This file is the older, richer development: it specialises the
   monoid object to a cartesian monoidal category (giving an ordinary monoid)
   and proves closure under products ([Product_Monoid]) and exponentials
   ([Hom_Monoid]). The two definitions are equivalent up to field renaming. *)

Section MonoidObject.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class MonoidObject (mon : C) := {
  mempty  : I ~> mon;             (* unit           η : I       ~> mon *)
  mappend : mon ⨂ mon ~> mon;     (* multiplication μ : mon ⨂ mon ~> mon *)

  (* left unit law: mappend ∘ (mempty ⨂ id) ≈ λ (left unitor I ⨂ mon ≅ mon) *)
  mempty_left : mappend ∘ bimap mempty id ≈ to (@unit_left C _ mon);
  (* right unit law: mappend ∘ (id ⨂ mempty) ≈ ρ (right unitor mon ⨂ I ≅ mon) *)
  mempty_right : mappend ∘ bimap id mempty ≈ to (@unit_right C _ mon);

  (* associativity, with the associator α reassociating the triple tensor:
     (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon) *)
  mappend_assoc :
    mappend ∘ bimap mappend id ≈ mappend ∘ bimap id mappend ∘ to tensor_assoc
}.

Context (mon : C).
Context `{@MonoidObject mon}.

(* Symmetric form of [mappend_assoc], reassociating in the opposite direction
   by composing with the inverse associator [tensor_assoc ⁻¹]. *)
Lemma mappend_assoc_sym :
  mappend ∘ bimap id mappend ≈ mappend ∘ bimap mappend id ∘ (tensor_assoc ⁻¹).
Proof.
  rewrite mappend_assoc.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  cat.
Qed.

End MonoidObject.

(* Projections to the unit and multiplication of a given monoid object [M]. *)
Notation "mempty[ M ]" := (@mempty _ _ _ M)
  (at level 9, format "mempty[ M ]") : category_scope.
Notation "mappend[ M ]" := (@mappend _ _ _ M)
  (at level 9, format "mappend[ M ]") : category_scope.

Section Monoid.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(* A monoid object for the cartesian monoidal structure [CC_Monoidal] (tensor
   = categorical product ×, unit = terminal object 1) is a monoid in the usual
   sense, with [mappend] reducing a product of two objects to one.

   nLab: "Classical monoids are of course just monoids in Set with the
   cartesian product." *)
Definition Monoid := @MonoidObject C CC_Monoidal.

(* The categorical product of two monoids is again a monoid, multiplying and
   uniting componentwise; [toggle] rearranges (x × y) × (x × y) into the
   (x × x) × (y × y) form expected by the componentwise [split] of the
   two multiplications. *)
#[export] Program Instance Product_Monoid `(X : Monoid x) `(Y : Monoid y) :
  @MonoidObject C CC_Monoidal (x × y) := {|
  mempty  := @mempty _ _ _ X △ @mempty _ _ _ Y;
  mappend := split (@mappend _ _ _ X) (@mappend _ _ _ Y) ∘ toggle
|}.
Next Obligation.
  spose (@mempty_left _ _ _ X) as HX.
  spose (@mempty_left _ _ _ Y) as HY.
  assert ((mempty[X] △ mempty[Y] ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (mempty[X] △ mempty[Y]) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ X) as HX.
  spose (@mempty_right _ _ _ Y) as HY.
  assert ((id[x × y] ∘ exl) △ (mempty[X] △ mempty[Y] ∘ exr)
            ≈ split id[x × y] (mempty[X] △ mempty[Y]))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ X) as HX.
  spose (@mappend_assoc _ _ _ Y) as HY.
  assert ((split mappend[X] mappend[Y] ∘ toggle ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (split mappend[X] mappend[Y] ∘ toggle) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  assert ((id[x × y] ∘ exl) △ (split mappend[X] mappend[Y] ∘ toggle ∘ exr)
            ≈ split id[x × y] (split mappend[X] mappend[Y] ∘ toggle))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite !split_fork.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !id_left.
  rewrite !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !split_comp.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite !id_right.
  rewrite <- (id_left (exl (x:=x) (y:=y))) at 1.
  rewrite <- (id_left (exr (x:=x) (y:=y))) at 1.
  rewrite <- !split_comp.
  rewrite !comp_assoc.
  rewrite HX, HY.
  rewrite !id_left.
  apply fork_respects; clear;
  now unfold split; unfork; cat.
Qed.

Context `{@Closed C _}.

(* Duplicate the [z] component across both halves of a product:
   (x × y) × z ~> (x × z) × (y × z). Used to feed the shared argument to both
   pointwise multiplications in [Hom_Monoid]. *)
Definition doppel {x y z : C} : (x × y) × z ~> (x × z) × (y × z) :=
  first exl △ first exr.

(* The pair of uncurried projections equals evaluating both function arguments
   at the shared point, after distributing that point via [doppel]. *)
Lemma uncurry_exl_fork_exr {x y : C} :
  uncurry exl △ uncurry exr ≈ split eval eval ∘ @doppel (y ^ x) (y ^ x) x.
Proof.
  unfold doppel.
  rewrite split_fork.
  now rewrite !eval_first.
Qed.

(* The exponential [y ^ x] inherits a monoid structure pointwise from a monoid
   [Y] on [y]: the unit is the constant function at [mempty[Y]], and two
   functions are combined by evaluating each at the same point and multiplying
   the results with [mappend[Y]]. This is the "monoid of functions into a
   monoid", obtained here internally via currying. *)
#[export] Program Instance Hom_Monoid {x} `(Y : Monoid y) :
  @MonoidObject C CC_Monoidal (y ^ x) := {
  mempty  := curry (@mempty _ _ _ Y ∘ exl);
  mappend := curry (@mappend _ _ _ Y ∘ uncurry exl △ uncurry exr)
}.
Next Obligation.
  spose (@mempty_left _ _ _ Y) as HY.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mempty[Y] ∘ exl)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exr_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ Y) as HY.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mempty[Y] ∘ exl)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exl_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ Y) as HY.
  rewrite uncurry_exl_fork_exr.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mappend[Y] ∘ split eval eval ∘ doppel)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mappend[Y] ∘ split eval eval ∘ doppel)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  unfold doppel.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !eval_first.
  simpl.
  rewrite split_fork.
  rewrite !eval_first.
  unfold split.
  rewrite !id_left.
  rewrite !curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !uncurry_comp.
  rewrite exl_fork.
  rewrite exr_fork.
  rewrite !uncurry_curry.
  rewrite <- (id_left (uncurry exr)).
  rewrite <- split_fork.
  rewrite comp_assoc.
  rewrite HY; clear HY.
  rewrite id_left.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  now rewrite uncurry_curry.
Qed.

End Monoid.
