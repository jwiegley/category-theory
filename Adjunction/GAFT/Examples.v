Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Diagonal.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Product.

Set Universe Polymorphism.

Generalizable All Variables.

(** * A worked example of the General Adjoint Functor Theorem *)

(* This file exercises [GAFT_from_initials] (Adjunction/GAFT.v) end to end on a
   concrete, non-degenerate adjunction: the binary diagonal / product adjunction

       Δ ⊣ (×)

   on any cartesian category [C].  Feeding a genuine comma-category initial
   object to the universal-arrow half of GAFT reproduces this known adjunction,
   validating that the GAFT plumbing composes with the universal-arrow bridge of
   [Theory/Universal/Arrow.v].

   VARIANCE (donor-signature deviation, recorded honestly).  [GAFT_from_initials]
   consumes [forall d, @Initial (=(d) ↓ U)] for a functor [U : C ⟶ D] and yields
   a *left* adjoint [F ⊣ U].  For the diagonal / product pair, [Δ] is the *left*
   adjoint and [(×)] the *right* adjoint (the general triangle is
   [(+) ⊣ Δ ⊣ (×)]).  So the functor that must play the role of [U] — the one
   fed to GAFT — is the product bifunctor

       ×(C) : C ∏ C ⟶ C   (Functor/Product/Internal.v, [InternalProductFunctor]),

   and the produced left adjoint [F : C ⟶ C ∏ C] is the diagonal.  The initial
   object of the comma [=(d) ↓ ×(C)] is [((d, d), δ)] with the diagonal
   [δ := id △ id : d ~> d × d] as its universal arrow (this is the classical
   "a product is a universal arrow out of the diagonal", read for the binary
   diagonal).  Taking [U := ×(C)] rather than the literal symbol [Δ] is forced by
   the *direction* GAFT produces; feeding [Δ] itself to GAFT would instead
   reconstruct the coproduct adjunction [(+) ⊣ Δ], a different, equally genuine
   left adjoint.  The conclusion delivered here is the full, honest adjunction
   [F ⊣ ×(C)] with no hypothesis weakened; the produced [F] is opaque (GAFT ends
   in [Qed]) and only *provably* the diagonal, so this file also exhibits, as
   [diagonal_product_via_gaft_is_diagonal], the natural isomorphism [F ≅ Δ] that
   makes it genuinely [Δ ⊣ (×)] (uniqueness of left adjoints, [left_adjoint_iso]). *)

Section GAFTExample.

Context `{C : Category}.
Context `{@Cartesian C}.

(* The universal mapping property of the diagonal, in the exact shape consumed
   by [universal_arrow_from_UMP]: for [d : C] the object [(d, d) : C ∏ C]
   together with the diagonal [id △ id : d ~> d × d] is a universal arrow from
   [d] to the product bifunctor [×(C)].  Any [f : d ~> a × b] factors uniquely
   through the diagonal, the factorization being the pair of projections
   [(exl ∘ f, exr ∘ f)] read as a morphism [(d, d) ~> (a, b)] of [C ∏ C]. *)
#[local] Obligation Tactic := idtac.

Program Definition diagonal_unique (d : C) (d' : C ∏ C)
  (f : d ~> InternalProductFunctor C d') :
  ∃! g : (d, d) ~{ C ∏ C }~> d',
    f ≈ fmap[InternalProductFunctor C] g ∘ (id[d] △ id[d]) :=
  {| unique_obj := (exl ∘ f, exr ∘ f) |}.
Next Obligation.
  (* existence: the projection pair factors [f] through the diagonal *)
  intros d d' f; simpl.
  assert (PFf : f ≈ (exl ∘ f) △ (exr ∘ f))
    by (apply ump_products; split; reflexivity).
  rewrite PFf at 1.
  symmetry.
  apply ump_products; split.
  - rewrite exl_fork_comp, <- comp_assoc, exl_fork, id_right; reflexivity.
  - rewrite exr_fork_comp, <- comp_assoc, exr_fork, id_right; reflexivity.
Qed.
Next Obligation.
  (* uniqueness: any factorizer [(v1, v2)] agrees with the projection pair *)
  intros d d' f [v1 v2] Hv.
  simpl in Hv.
  assert (Hf : f ≈ (v1 △ v2)).
  { rewrite Hv.
    apply ump_products; split.
    - rewrite exl_fork_comp, <- comp_assoc, exl_fork, id_right; reflexivity.
    - rewrite exr_fork_comp, <- comp_assoc, exr_fork, id_right; reflexivity. }
  simpl; split.
  - rewrite Hf, exl_fork; reflexivity.
  - rewrite Hf, exr_fork; reflexivity.
Qed.

(* Packaged as a [UniversalArrow], whose [arrow_initial] projection is exactly
   the comma-category initial object [GAFT_from_initials] wants. *)
Definition diagonal_UA (d : C) : UniversalArrow d (InternalProductFunctor C) :=
  universal_arrow_from_UMP d (InternalProductFunctor C) (d, d)
    (id[d] △ id[d]) (diagonal_unique d).

(* The example: run [GAFT_from_initials] on the product bifunctor, supplying at
   each [d] the initial object of [=(d) ↓ ×(C)] produced above.  The result is a
   genuine left adjoint [F ⊣ ×(C)], produced purely through the GAFT machinery.
   Because [GAFT_from_initials] is [Qed]-opaque, this [F] is not *definitionally*
   the diagonal [Δ]; it is a left adjoint to [×(C)], necessarily isomorphic to
   [Δ] by uniqueness of left adjoints.  That isomorphism is exhibited just below,
   in [diagonal_product_via_gaft_is_diagonal]. *)
Definition diagonal_product_via_gaft :
  { F : C ⟶ C ∏ C & F ⊣ InternalProductFunctor C } :=
  GAFT_from_initials (InternalProductFunctor C)
    (fun d => arrow_initial (UniversalArrow := diagonal_UA d)).

(* The GAFT-produced left adjoint is naturally isomorphic to the concrete binary
   diagonal [Diagonal_Product C].  Left adjoints to a fixed functor are unique up
   to natural isomorphism ([Theory/Adjunction.v], [left_adjoint_iso]); pitting the
   opaque GAFT adjunction [projT2 diagonal_product_via_gaft] against the concrete
   diagonal–product adjunction [Diagonal_Product_Adjunction] over their common
   right adjoint [×(C)] delivers that isomorphism.  So the [F] above, though
   opaque, is provably (naturally isomorphic to) the diagonal — the
   reconstruction of [Δ ⊣ (×)] is genuine, not merely asserted. *)
Definition diagonal_product_via_gaft_is_diagonal :
  projT1 diagonal_product_via_gaft ≈ Diagonal_Product C :=
  left_adjoint_iso (InternalProductFunctor C)
    (projT1 diagonal_product_via_gaft) (Diagonal_Product C)
    (projT2 diagonal_product_via_gaft)
    (Diagonal_Product_Adjunction C).

End GAFTExample.
