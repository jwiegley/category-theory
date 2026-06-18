Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(** * Embedded constants via global elements *)

(* nLab: https://ncatlab.org/nlab/show/global+element
   Wikipedia: https://en.wikipedia.org/wiki/Global_element

   A global element of an object `x` in a category with a terminal object `1`
   is a morphism `1 ~> x`; in `Sets` (where `1` is a singleton) these are in
   bijection with the elements of `x`, which is what makes them "elements". A
   global element is the special case of a generalized (`T`-valued) element
   `T ~> x` where the stage `T` is the terminal object `1`.

   This structure bundles a whole Coq type `A` of foreign constants together
   with a way to embed them: each value `x : A` names a host object
   `constant_obj x : C` and is realized there by a global element
   `constant x : 1 ~> constant_obj x`. So `Constant A` is a family of global
   elements indexed by the constants of `A`. Used to host foreign values of a
   given Coq type inside a category (see Instance/Coq.v). Note that an object
   is not in general determined by its global elements, so this carries the
   embedding as structure rather than recovering it as a property. *)

Class Constant `{@Terminal C} (A : Type) := {
  constant_obj : A → C;                       (* host object for each value of A *)
  constant (x : A) : 1 ~> constant_obj x       (* global element naming x in C *)
}.

Arguments constant_obj {_ _} A {_}.
