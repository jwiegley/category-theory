Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** The pointwise product of two functors into a monoidal category. *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   Given two functors F, G : C ⟶ D into a monoidal category D, their pointwise
   product F :*: G : C ⟶ D acts objectwise by the tensor of D:

     (F :*: G) x  =  F x ⨂ G x          (on objects)
     (F :*: G) f  =  fmap[F] f ⨂ fmap[G] f  (on arrows, i.e. bimap (F f) (G f))

   The functor laws hold pointwise: each follows from the corresponding law in
   F and G together with the bifunctoriality of the tensor ⊗ (bimap_respects,
   bimap_id_id, bimap_comp). This is the construction by which a monoidal
   structure on D is transported pointwise to the functor category [C, D], the
   unit being the constant functor at the monoidal unit I.

   This is the OBJECTWISE/pointwise tensor of two functors with a common
   domain and codomain. It is distinct from:
     - Functor/Construction/Product.v, the componentwise product F ∏⟶ G of
       functors on product categories, C ∏ J ⟶ D ∏ K; and
     - the coend tensor of functors ∫^c F c ⨂ G c (nLab "tensor product of
       functors"), which is not this pointwise construction. *)

#[export]
Program Instance Product
        {C : Category} {D : Category} `{@Monoidal D}
        {F : C ⟶ D} {G : C ⟶ D} : C ⟶ D := {
  fobj := fun x => (F x ⨂ G x)%object;          (* objectwise tensor: F x ⨂ G x *)
  fmap := fun _ _ f => fmap[F] f ⨂ fmap[G] f     (* arrowwise: bimap (F f) (G f) *)
}.
Next Obligation.
  proper;
  apply bimap_respects;
  now apply fmap_respects.
Qed.
Next Obligation. normal; reflexivity. Qed.

Notation "F :*: G" := (@Product _ _ _ F%functor G%functor)
  (at level 9) : functor_scope.
