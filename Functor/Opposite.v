Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** The opposite (dual) functor F^op : C^op ⟶ D^op. *)

(* nLab: https://ncatlab.org/nlab/show/opposite+functor
   Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

   Given F : C ⟶ D, the opposite functor F^op : C^op ⟶ D^op acts the same as
   F on both objects and morphisms; only the (formally reversed) source and
   target categories change. On objects (F^op) x := F x, and a morphism
   f : x ~{C^op}~> y (that is, f : y ~> x in C) is sent to fmap[F] f, read as a
   morphism F x ~{D^op}~> F y. The functoriality fields are the corresponding
   fields of F with their object indices swapped, and fmap_comp is reindexed to
   match the reversed composition of C^op (g ∘ f there is f ∘ g in C).

   Because the underlying duality is built in so that (C^op)^op = C holds by
   reflexivity, and F^op reuses the same object/morphism maps as F, the
   construction is involutive: (F^op)^op = F, provable by [reflexivity] (see
   Opposite_Functor_invol below). A contravariant functor C ⟶ D is, by
   definition, an ordinary functor out of C^op; see [contramap] at the end.

   On 1-cells (functors) oppositization is covariant, but note that on 2-cells
   (natural transformations) it reverses direction: a natural transformation
   F^op ⟹ G^op corresponds to one G ⟹ F, so op is the 2-functor Cat^co ⟶ Cat. *)

Definition Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op :=
  @Build_Functor (C^op) (D^op) F
    (λ (x y : C ^op) (f : x ~{ C ^op }~> y), @fmap C D F y x f)
    (λ (x y : C ^op) (f g : x ~{ C ^op }~> y), @fmap_respects _ _ F y x f g)
    (λ x : C ^op, fmap_id)
    (λ (x y z : C ^op) (f : y ~{ C ^op }~> z)
      (g : x ~{ C ^op }~> y), @fmap_comp _ _ F _ _ _ g f).

(* Mirrors the C^op notation on categories, at the same level/scope. *)

Notation "F ^op" := (@Opposite_Functor _ _ F)
  (at level 7, format "F ^op", left associativity) : functor_scope.

Open Scope functor_scope.

(* The op functor is an involution on functors: applying it twice recovers F
   on the nose. Both sources state (C^op)^op = C, and F^op reuses F's maps. *)

Corollary Opposite_Functor_invol `{F : C ⟶ D} : (F^op)^op = F.
Proof. reflexivity. Qed.

(* A functor F : C^op ⟶ D is a contravariant functor on C: it reverses the
   direction of morphisms. [contramap] applies it to a C-arrow f : x ~> y by
   reading f as the C^op-arrow (op f), yielding F y ~> F x in D. *)

Definition contramap `{F : C^op ⟶ D} `(f : x ~{C}~> y) :
  F y ~{D}~> F x := fmap (op f).
