Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * Category with a terminal object *)

(* nLab: https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   A terminal object `1` in a category C is an object such that for every
   object `x` there is exactly one morphism `! : x ~> 1`. "Exactly one" splits
   into existence (the morphism [one]) and uniqueness (any two morphisms into
   `1` agree under `≈`, the law [one_unique]). Equivalently, every hom-setoid
   `x ~> 1` is contractible (a singleton up to `≈`). A terminal object is the
   dual of an initial object — it is initial in `C^op` — and is the limit of
   the empty diagram; see Structure/Initial.v, which derives initial objects
   from this file by duality. Terminal objects are unique up to (unique)
   isomorphism whenever they exist. *)

Section Terminal.

Context {C : Category}.

Class Terminal := {
  terminal_obj : C;                     (* the terminal object 1 *)
  one {x} : x ~> terminal_obj;          (* the morphism ! : x ~> 1 *)

  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g  (* ! is unique up to ≈ *)
}.

End Terminal.

Notation "1" := terminal_obj : object_scope.

(* Precomposing the unique map collapses: ! ∘ f ≈ !, since both land in `1`. *)
Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.

(* `one[x]` names the morphism `! : x ~> 1` at an explicit Terminal instance. *)
Notation "one[ C ]" := (@one _ _ C)
  (at level 9, format "one[ C ]") : morphism_scope.

(* A "constant" map `x ~> y` factoring through `1`: pick `f : 1 ~> y`, then
   precompose with `! : x ~> 1`, so the result ignores its argument's data. *)
Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].
