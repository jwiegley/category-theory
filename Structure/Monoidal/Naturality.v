Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

Section MonoidalNaturality.

Context `{M : @Monoidal C}.

(** Naturality glue for monoidal categories. *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   In a monoidal category the tensor ⊗ is a bifunctor (functorial in each
   argument) and the associator alpha = [tensor_assoc], left unitor lambda =
   [unit_left] and right unitor rho = [unit_right] are natural isomorphisms.
   This file feeds those facts to the `natural`/`Mapping` machinery of
   Theory/Naturality.v, so that monoidal naturality obligations elsewhere
   (e.g. [strength_natural] in Functor/Strong.v and [braid_natural] in
   Structure/Monoidal/Braided.v) are discharged by instance resolution.

   For an object map P : C → C with a `Mapping` action map = P f, the partial
   applications of the tensor are themselves morphism actions:

       fun x => P x ⨂ y    with action  map f ⨂ id      ([Tensor_Left_Map]),
       fun y => x ⨂ P y    with action  id ⨂ map f      ([Tensor_Right_Map]),
       fun x => P x ⨂ P x  with action  map f ⨂ map f    ([Tensor_Both_Map]).

   Registering these `Mapping` instances lets the per-argument `Arity*`
   naturality squares of Theory/Naturality.v be computed for families built
   from a tensor whose factors are functorial, without materialising a single
   `C ⟶ C` functor. The companion `Program Definition`s ([Tensor_Left],
   [Tensor_Right], [Tensor_Both]) bundle the same actions as genuine functors
   `C ⟶ C`; they record functoriality but are not used by the resolution
   machinery (only the `Mapping` instances are).

   The closing theorem [monoidal_naturality] then states naturality of the
   three structural isomorphisms as the product of their `to`/`from` squares;
   `prove_naturality` reduces it to the `*_natural` fields of [M].

   Note: [Tensor_Right] is declared `#[export] Program Instance` whereas its
   siblings [Tensor_Left] and [Tensor_Both] are plain `Program Definition`.
   None of the three functor forms is referenced elsewhere, so this asymmetry
   is harmless, but registering an unconstrained `C ⟶ C` functor as a global
   instance is a resolution-hygiene wrinkle; left as-is to keep the change
   minimal. *)

Program Definition Tensor_Left {F : C ⟶ C} {y : C} : C ⟶ C := {|
  fobj := fun x => (F x ⨂ y)%object;
  fmap := fun _ _ f => fmap[F] f ⨂[M] id
|}.
Next Obligation.
  proper; apply bimap_respects; rewrites; reflexivity.
Defined.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Left_Map `{@Mapping C P} {y : C} :
  @Mapping C (fun x => P x ⨂ y)%object := {
  map := fun _ _ f => map f ⨂ id;
}.

#[export] Program Instance Tensor_Right {F : C ⟶ C} {x : C} : C ⟶ C := {
  fobj := fun y => (x ⨂ F y)%object;
  fmap := fun _ _ f => id ⨂[M] fmap[F] f
}.
Next Obligation.
  proper; apply bimap_respects;
  rewrites; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Right_Map `{@Mapping C P} {x : C} :
  @Mapping C (fun y => x ⨂ P y)%object := {
  map := fun _ _ f => id ⨂ map f;
}.

Program Definition Tensor_Both `{F : C ⟶ C} : C ⟶ C := {|
  fobj := fun x => (F x ⨂ F x)%object;
  fmap := fun _ _ f => fmap[F] f ⨂[M] fmap[F] f
|}.
Next Obligation.
  proper; apply bimap_respects;
  rewrites; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Both_Map `{@Mapping C P} :
  @Mapping C (fun x => P x ⨂ P x)%object := {
  map := fun _ _ f => map f ⨂ map f;
}.

Theorem monoidal_naturality :
  natural (@unit_left _ M) *
  natural (@unit_right _ M) *
  natural (@tensor_assoc _ M).
Proof. prove_naturality M normal. Qed.

End MonoidalNaturality.
