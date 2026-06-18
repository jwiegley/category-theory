Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   An initial object `0` is an object equipped, for every object `x`, with a
   morphism `zero : 0 ~> x` (written `¡` in the literature), subject to the
   universal mapping property that this morphism is unique: any two morphisms
   `0 ~> x` are equal (zero_unique). This is exactly the dual of a terminal
   object: an initial object in C is a terminal object in C^op, with all arrows
   reversed. The dual of `one : x ~> 1` is `zero : 0 ~> x`. An object that is
   both initial and terminal is a zero object. *)

(* To be initial is just to be terminal in the opposite category; but to avoid
   confusion, we'd like a set of notations specific to categories with initial
   objects. As a consequence the initial-object UMP is not restated here as a
   primitive Class: `Initial C` literally unfolds to `Terminal (C^op)`, and the
   projections below recover the C-side names (initial_obj, zero, zero_unique)
   from the Terminal fields. *)

Notation "'Initial' C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.

Section Initial_.

Context `{I : @Initial C}.

(* The initial object `0` itself (terminal in C^op).         *)
Definition initial_obj : C := @terminal_obj _ I.

(* The unique morphism `¡ : 0 ~> x` (the `one` of C^op).      *)
Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

(* Uniqueness: any two morphisms out of `0` are equivalent.   *)
Definition zero_unique {x} (f g : initial_obj ~{C}~> x) : f ≈ g :=
  @one_unique _ I _ _ _.

End Initial_.

Notation "0" := initial_obj : object_scope.

Notation "zero[ C ]" := (@zero _ _ C)
  (at level 9, format "zero[ C ]") : morphism_scope.

(* Postcomposing the unique morphism `0 ~> x` is again unique (dual of
   one_comp): any `f ∘ zero` is forced to equal `zero` by zero_unique. *)
Corollary zero_comp `{T : @Initial C} {x y : C} {f : x ~> y} :
  f ∘ zero ≈ zero.
Proof. apply (@one_comp _ T). Qed.
