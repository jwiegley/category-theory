Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(** * The category of cones over a diagram *)

(* nLab: https://ncatlab.org/nlab/show/cone
   Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

   The cones over a fixed diagram F : J ⟶ C form a category. Its objects are
   the cones over F, i.e. apex objects N : C equipped with a coherent leg
   family ψx : N ~> F x (see [Cone]). A morphism from a cone N (legs ψ) to a
   cone L (legs φ) is a single apex map u : N ~> L of C that is compatible
   with both leg families: φx ∘ u ≈ ψx for every object x of J, so that u
   transports N's legs onto L's. (Viewing cones as natural transformations
   Δ N ⟹ F, such a u is the unique component to which any compatible
   Δ N ⟹ Δ L collapses.) Two cone morphisms are identified exactly when
   their underlying apex maps agree under ≈; the commutativity witness is
   proof-irrelevant. Composition is composition of apex maps, and the
   identity cone morphism is the identity apex map.

   The limit of F is the terminal object of this category: the universal cone
   through which every other cone factors uniquely (see Cones/Limit). *)

Program Definition Cones `(F : J ⟶ C) : Category := {|
  obj     := Cone F;
  hom     := fun N L => { u : vertex_obj[N] ~> vertex_obj[L]
                              & ∀ j, vertex_map[L] ∘ u ≈ @vertex_map _ _ _ F
                                       (@coneFrom _ _ _ N) j };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun x => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _);
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite X0; auto.
Qed.

(* The category of cocones over F is dually the category of cones over the
   opposite diagram F^op : J^op ⟶ C^op, whose objects are the cocones over F
   (legs F x ~> apex; see [Cocone]). Its initial object is the colimit of F. *)
Definition Cocones `(F : J ⟶ C) := Cones (F^op).
