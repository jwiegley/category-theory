Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Constant.

Generalizable All Variables.

(** * Functors compatible with embedded constants *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+functor
   nLab: https://ncatlab.org/nlab/show/global+element
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   Given a functor `F : C ⟶ D` and a shared type `T` of foreign constants
   embedded into both `C` and `D` as families of global elements (see
   Structure/Constant.v), this structure says that `F` carries the embedding
   on the source over to the embedding on the target, up to comparison maps.

   It is the global-element analogue of the *unit comparison map* of a (lax)
   monoidal functor `ψ_I : I ~> F I`: with the terminal object `1` playing the
   role of the monoidal unit, `unmap_one` is the comparison between the units,
   and `map_const` compares the host objects of each constant. Because `1` is
   terminal in `D`, the unit comparison is forced to run `F 1 ~> 1` (the unique
   map into the terminal object), the reverse of the lax-monoidal direction.

   Beware that the two `Terminal`/`Constant` instances in scope (`CT`,`H` on the
   `C` side and `DT`,`H0` on the `D` side) make some textually-identical
   notations resolve differently. In `unmap_one`, `F 1` is `F` of `C`'s
   terminal object while the codomain `1` is `D`'s terminal object. In
   `map_const`, the domain `constant_obj T x` is the `D`-side host object while
   the `constant_obj T x` under `F` is the `C`-side host object. The coherence
   law then states `fmap (constant x) ≈ map_const x ∘ constant x ∘ unmap_one`,
   where the left `constant x` is the `C`-side global element and the right one
   is the `D`-side global element. *)

Section ConstantFunctor.

Context `{F : C ⟶ D}.
Context `{@Constant C CT T}.
Context `{@Constant D DT T}.

Class ConstantFunctor := {
  unmap_one : F 1 ~{D}~> 1;     (* unit comparison: F of C's `1` into D's `1` *)

  (* host-object comparison: D-side `constant_obj x` into F of the C-side one *)
  map_const {x : T} : constant_obj T x ~> F (constant_obj T x);

  (* coherence: F of the C-side global element of `x` agrees with the D-side
     global element of `x` transported through the comparison maps *)
  fmap_constant (x : T) :
    fmap (constant x) ≈ @map_const x ∘ constant x ∘ unmap_one;
}.

End ConstantFunctor.
