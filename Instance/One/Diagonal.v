Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.

(** * The constant diagram factors through the terminal category 1. *)

(* nLab:      https://ncatlab.org/nlab/show/constant+functor
   nLab:      https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Diagonal_functor

   The constant diagram Δ[J](d) : J ⟶ D (every object ↦ d, every morphism ↦
   id[d]) does not depend on J's structure, only on d. nLab records this as a
   factorization through the point: "a constant functor can be expressed as the
   composite C → 1 → D", where the first arrow is the unique functor `! : J ⟶ 1`
   ([one], here [Erase J] at Cat's Terminal instance) and the second is the
   functor `1 ⟶ D` picking out d — which is exactly the constant diagram on the
   terminal index category, Δ[1](d), written here Δ(d).

   So Δ[J](d) ≈ Δ(d) ∘ ! in Cat. Both functors send every object to d and every
   morphism to id[d], so they are equal on the nose; the witnessing natural
   isomorphism (Cat's hom-setoid identifies functors up to natural iso) is the
   identity iso [iso_id] at every j : J, and naturality is discharged by [cat].
   This is the J-indexed analogue of [1, C] ≃ C: every constant diagram is an
   object of D inflated along the unique map to 1. *)

Corollary Diagonal_Unique (J C : Category) {D : Category} (d : D) :
  Δ[J](d) ≈[Cat] Δ(d) ∘[Cat] one.
Proof. exists (fun _ => iso_id); simpl; intros; cat. Qed.
