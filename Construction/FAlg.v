Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** * The category of F-algebras *)

(* nLab:      https://ncatlab.org/nlab/show/algebra+over+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/F-algebra

   For an endofunctor [F : C ⟶ C], an F-algebra is an object [a] with a
   structure map [α : F a ~> a] (this is [FAlgebra F a] of Theory/Functor.v).
   A morphism of F-algebras [(a, α) ~> (b, β)] is a carrier map [h : a ~> b]
   commuting with the structure maps: [h ∘ α ≈ β ∘ fmap[F] h].  These form the
   category [FAlg F]; its initial object (when it exists) is the least fixed
   point of [F], and Lambek's lemma shows the initial structure map is an
   isomorphism [F μF ≅ μF] (Theory/Lambek.v).

   The construction mirrors [Monad/Eilenberg/Moore.v]: a bundled hom class
   [FAlgHom] carrying the commuting square, a dependent-pair object carrier,
   and a hom-setoid comparing the underlying carrier maps. *)

Class FAlgHom `(F : C ⟶ C) (a b : C)
      (α : FAlgebra F a) (β : FAlgebra F b) := {
  falg_hom : a ~> b;
  falg_commutes : falg_hom ∘ α ≈ β ∘ fmap[F] falg_hom
}.

Notation "falg_hom[ H ]" := (@falg_hom _ _ _ _ _ _ H)
  (at level 9, format "falg_hom[ H ]") : morphism_scope.

Program Definition FAlg `(F : C ⟶ C) : Category := {|
  obj     := ∃ a : C, FAlgebra F a;
  hom     := fun x y => FAlgHom F ``x ``y (`2 x) (`2 y);
  homset  := fun _ _ => {| equiv := fun f g => falg_hom[f] ≈ falg_hom[g] |};
  id      := fun _ => {| falg_hom := id |};
  compose := fun _ _ _ f g => {| falg_hom := falg_hom[f] ∘ falg_hom[g] |}
|}.
Next Obligation.
  (* the composite carrier map is an algebra map, pasting the two squares
     (the id-map and the setoid/category-law obligations are discharged by the
     ambient obligation tactic, as in Monad/Eilenberg/Moore.v). *)
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- falg_commutes.
  rewrite <- !comp_assoc.
  rewrite <- falg_commutes.
  reflexivity.
Qed.

(* The forgetful functor to the underlying category, dropping the structure. *)
Program Definition FAlg_Forget `(F : C ⟶ C) : FAlg F ⟶ C := {|
  fobj := fun x => ``x;
  fmap := fun x y f => falg_hom[f]
|}.
