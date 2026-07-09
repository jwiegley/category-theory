Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(** * Tensor and unit comonoids in a symmetric monoidal category

    In any symmetric monoidal category the (commutative) comonoids are
    closed under the tensor product and inhabited at the unit object:

    - given comonoids on [X] and [Y], the canonical morphisms
      [canonical_tensor_delta]/[canonical_tensor_epsilon] of
      Structure/Monoidal/Hypergraph.v — the doubled comultiplication
      routed through the middle interchange, and the doubled counit
      collapsed by the unitor — form a comonoid on [X ⨂ Y]
      ([Comonoid_Tensor]), cocommutative when the components are
      ([CommutativeComonoid_Tensor]);
    - the unit object carries the trivial comonoid [δ := λ⁻¹, ε := id]
      ([Comonoid_Unit], [CommutativeComonoid_Unit]).

    This is the classical fact that the squaring-style structure maps of
    the tensor bifunctor make it a symmetric (strong) monoidal functor
    [C ∏ C ⟶ C], so it carries comonoids to comonoids (Fong–Spivak,
    "Hypergraph Categories", §2; the [scfa_tensor_*]/[scfa_unit_*]
    coherence fields of the [Hypergraph] class assert exactly these
    composites, and Structure/Monoidal/CopyDiscard.v assumes them as the
    supply-coherence fields).  Here the comonoid laws are PROVED rather
    than assumed, so downstream developments can derive a comonoid on a
    composite boundary from per-generator comonoids without any
    boundary-level axiom.

    Tensoring two DIFFERENT comonoids needs the interchange coherences
    of Structure/Monoidal/Braided/Proofs.v at mixed arguments: the
    four-slot naturality [swap_inner_natural], the involution
    [swap_inner_invol], the unit coherences [swap_inner_unit_left2] /
    [swap_inner_unit_right2] in their solved and inverse orientations,
    and the inverted associativity hexagon [swap_inner_assoc_inv].  The
    diagonal forms consumed by the copy-discard stack are one-line
    instances of the same lemmas.

    nLab:      https://ncatlab.org/nlab/show/comonoid
    nLab:      https://ncatlab.org/nlab/show/monoidal+functor
    Reference: Fong & Spivak, "Hypergraph Categories",
               J. Pure Appl. Algebra 223(11):4746–4777, 2019
               (arXiv:1806.08304), §2
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
               string diagrams", MSCS 29(7):938–971, 2019
               (arXiv:1709.00322), §2 *)

(* ------------------------------------------------------------------ *)

(** ** The tensor of two comonoids *)

Section ComonoidTensor.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* Hypergraph.v's [mid_swap_inv] is definitionally the diagonal of the
   interchange; this bridge lets the canonical morphisms be rewritten
   into [swap_inner] form (the mirror orientation of Deterministic.v's
   [swap_inner_diag], restated locally to keep this file independent of
   the copy-discard stack). *)
Lemma mid_swap_inv_swap_inner (x y : C) :
  mid_swap_inv x y ≈ swap_inner x x y y.
Proof. reflexivity. Qed.

(** *** The comonoid laws of the canonical tensor morphisms *)

Theorem canonical_tensor_delta_coassoc {X Y : C}
        (CX : Comonoid X) (CY : Comonoid Y) :
  bimap (canonical_tensor_delta CX CY) id[(X ⨂ Y)%object]
    ∘ canonical_tensor_delta CX CY
    ≈ from (@tensor_assoc C _ (X ⨂ Y) (X ⨂ Y) (X ⨂ Y))
        ∘ bimap id[(X ⨂ Y)%object] (canonical_tensor_delta CX CY)
        ∘ canonical_tensor_delta CX CY.
Proof.
  unfold canonical_tensor_delta.
  rewrite !mid_swap_inv_swap_inner.
  (* Push the doubled comultiplication through the interchange on each
     side (four-slot naturality), leaving the component redexes. *)
  assert (L : bimap (swap_inner X X Y Y
                       ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY))
                    id[(X ⨂ Y)%object]
                ∘ (swap_inner X X Y Y
                     ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY))
              ≈ bimap (swap_inner X X Y Y) id[(X ⨂ Y)%object]
                  ∘ (swap_inner (X ⨂ X) X (Y ⨂ Y) Y
                       ∘ bimap (bimap (@delta _ _ _ CX) id[X]
                                  ∘ @delta _ _ _ CX)
                               (bimap (@delta _ _ _ CY) id[Y]
                                  ∘ @delta _ _ _ CY))).
  { rewrite bimap_comp_id_right.
    rewrite <- !comp_assoc.
    comp_left.
    rewrite <- (@bimap_id_id C C C (@tensor C _) X Y).
    rewrite swap_inner_natural_cons.
    comp_left.
    rewrite <- bimap_comp.
    reflexivity. }
  assert (R : bimap id[(X ⨂ Y)%object]
                    (swap_inner X X Y Y
                       ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY))
                ∘ (swap_inner X X Y Y
                     ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY))
              ≈ bimap id[(X ⨂ Y)%object] (swap_inner X X Y Y)
                  ∘ (swap_inner X (X ⨂ X) Y (Y ⨂ Y)
                       ∘ bimap (bimap id[X] (@delta _ _ _ CX)
                                  ∘ @delta _ _ _ CX)
                               (bimap id[Y] (@delta _ _ _ CY)
                                  ∘ @delta _ _ _ CY))).
  { rewrite bimap_comp_id_left.
    rewrite <- !comp_assoc.
    comp_left.
    rewrite <- (@bimap_id_id C C C (@tensor C _) X Y).
    rewrite swap_inner_natural_cons.
    comp_left.
    rewrite <- bimap_comp.
    reflexivity. }
  rewrite <- !comp_assoc.
  rewrite L; clear L.
  rewrite R; clear R.
  (* Component coassociativity on the left branch. *)
  rewrite (@delta_coassoc C _ X CX).
  rewrite (@delta_coassoc C _ Y CY).
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  (* Peel the shared tail; the residual is the inverted hexagon. *)
  rewrite !comp_assoc.
  comp_right.
  comp_right.
  symmetry.
  apply (@swap_inner_assoc_inv C S X Y X Y X Y).
Qed.

Theorem canonical_tensor_delta_counit_left {X Y : C}
        (CX : Comonoid X) (CY : Comonoid Y) :
  bimap (canonical_tensor_epsilon CX CY) id[(X ⨂ Y)%object]
    ∘ canonical_tensor_delta CX CY
    ≈ from (@unit_left C _ (X ⨂ Y)).
Proof.
  unfold canonical_tensor_delta, canonical_tensor_epsilon.
  rewrite mid_swap_inv_swap_inner.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  (* Push the doubled counit through the interchange, then use the
     component counit laws. *)
  assert (T : bimap (bimap (@epsilon _ _ _ CX) (@epsilon _ _ _ CY))
                    id[(X ⨂ Y)%object]
                ∘ (swap_inner X X Y Y
                     ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY))
              ≈ swap_inner I X I Y
                  ∘ bimap ((@unit_left C _ X)⁻¹) ((@unit_left C _ Y)⁻¹)).
  { rewrite <- (@bimap_id_id C C C (@tensor C _) X Y).
    rewrite swap_inner_natural_cons.
    comp_left.
    rewrite <- bimap_comp.
    rewrite (@delta_counit_left C _ X CX).
    rewrite (@delta_counit_left C _ Y CY).
    reflexivity. }
  rewrite T; clear T.
  rewrite swap_inner_from_unit_left2.
  rewrite comp_assoc.
  rewrite bimap_fuse_id_right.
  rewrite iso_to_from.
  rewrite bimap_id_id.
  apply id_left.
Qed.

Theorem canonical_tensor_delta_counit_right {X Y : C}
        (CX : Comonoid X) (CY : Comonoid Y) :
  bimap id[(X ⨂ Y)%object] (canonical_tensor_epsilon CX CY)
    ∘ canonical_tensor_delta CX CY
    ≈ from (@unit_right C _ (X ⨂ Y)).
Proof.
  unfold canonical_tensor_delta, canonical_tensor_epsilon.
  rewrite mid_swap_inv_swap_inner.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  assert (T : bimap id[(X ⨂ Y)%object]
                    (bimap (@epsilon _ _ _ CX) (@epsilon _ _ _ CY))
                ∘ (swap_inner X X Y Y
                     ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY))
              ≈ swap_inner X I Y I
                  ∘ bimap ((@unit_right C _ X)⁻¹) ((@unit_right C _ Y)⁻¹)).
  { rewrite <- (@bimap_id_id C C C (@tensor C _) X Y).
    rewrite swap_inner_natural_cons.
    comp_left.
    rewrite <- bimap_comp.
    rewrite (@delta_counit_right C _ X CX).
    rewrite (@delta_counit_right C _ Y CY).
    reflexivity. }
  rewrite T; clear T.
  rewrite swap_inner_from_unit_right2.
  rewrite bimap_id_fuse_cons.
  rewrite iso_to_from.
  rewrite bimap_id_id.
  apply id_left.
Qed.

(** *** The packaged tensor comonoid *)

Definition Comonoid_Tensor {X Y : C} (CX : Comonoid X) (CY : Comonoid Y) :
  Comonoid (X ⨂ Y) :=
  @Build_Comonoid C _ (X ⨂ Y)%object
    (canonical_tensor_delta CX CY)
    (canonical_tensor_epsilon CX CY)
    (canonical_tensor_delta_coassoc CX CY)
    (canonical_tensor_delta_counit_left CX CY)
    (canonical_tensor_delta_counit_right CX CY).

(* The projections compute to the canonical morphisms on the nose. *)
Lemma Comonoid_Tensor_delta {X Y : C} (CX : Comonoid X) (CY : Comonoid Y) :
  @delta _ _ _ (Comonoid_Tensor CX CY) ≈ canonical_tensor_delta CX CY.
Proof. reflexivity. Qed.

Lemma Comonoid_Tensor_epsilon {X Y : C} (CX : Comonoid X) (CY : Comonoid Y) :
  @epsilon _ _ _ (Comonoid_Tensor CX CY) ≈ canonical_tensor_epsilon CX CY.
Proof. reflexivity. Qed.

(** *** Cocommutativity of the tensor comonoid *)

Theorem canonical_tensor_delta_cocomm {X Y : C}
        (CX : CommutativeComonoid X) (CY : CommutativeComonoid Y) :
  braid ∘ canonical_tensor_delta CX CY ≈ canonical_tensor_delta CX CY.
Proof.
  unfold canonical_tensor_delta.
  rewrite !mid_swap_inv_swap_inner.
  (* The braid slides across the interchange onto the components. *)
  assert (BW : @braid C _ (X ⨂ Y)%object (X ⨂ Y)%object
                 ∘ swap_inner X X Y Y
               ≈ swap_inner X X Y Y
                   ∘ (@braid C _ X X ⨂ @braid C _ Y Y)).
  { rewrite <- (id_left (@braid C _ (X ⨂ Y)%object (X ⨂ Y)%object
                           ∘ swap_inner X X Y Y)).
    rewrite <- (@swap_inner_invol C S X Y X Y).
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (swap_inner X Y X Y)).
    rewrite swap_inner_braid.
    rewrite <- !comp_assoc.
    rewrite (@swap_inner_invol C S X X Y Y).
    rewrite id_right.
    reflexivity. }
  rewrite comp_assoc.
  rewrite BW; clear BW.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite (@delta_cocommutative_of_ccomon C S X CX).
  rewrite (@delta_cocommutative_of_ccomon C S Y CY).
  reflexivity.
Qed.

Definition CommutativeComonoid_Tensor {X Y : C}
    (CX : CommutativeComonoid X) (CY : CommutativeComonoid Y) :
  CommutativeComonoid (X ⨂ Y) :=
  @Build_CommutativeComonoid C S (X ⨂ Y)%object
    (Comonoid_Tensor CX CY)
    (canonical_tensor_delta_cocomm CX CY).

Lemma CommutativeComonoid_Tensor_delta {X Y : C}
      (CX : CommutativeComonoid X) (CY : CommutativeComonoid Y) :
  ccomon_delta (CommutativeComonoid_Tensor CX CY)
    ≈ canonical_tensor_delta CX CY.
Proof. reflexivity. Qed.

Lemma CommutativeComonoid_Tensor_epsilon {X Y : C}
      (CX : CommutativeComonoid X) (CY : CommutativeComonoid Y) :
  ccomon_epsilon (CommutativeComonoid_Tensor CX CY)
    ≈ canonical_tensor_epsilon CX CY.
Proof. reflexivity. Qed.

End ComonoidTensor.

(* ------------------------------------------------------------------ *)

(** ** The trivial comonoid on the unit object

    [δ_I := λ⁻¹, ε_I := id] — the structure the [Hypergraph] class
    asserts through its [scfa_unit_delta]/[scfa_unit_epsilon] fields
    and Fong–Spivak show is the unique unit-compatible choice.  The
    laws are pure unitor coherence (Kelly's λ_I ≈ ρ_I). *)

Section ComonoidUnit.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Lemma unit_comonoid_coassoc :
  bimap ((@unit_left C _ I)⁻¹) id[I] ∘ (@unit_left C _ I)⁻¹
    ≈ from (@tensor_assoc C _ I I I)
        ∘ bimap id[I] ((@unit_left C _ I)⁻¹)
        ∘ (@unit_left C _ I)⁻¹.
Proof.
  rewrite tensor_assoc_from_unit_left.
  rewrite <- unit_identity_from.
  reflexivity.
Qed.

Lemma unit_comonoid_counit_left :
  bimap id[I] id[I] ∘ (@unit_left C _ I)⁻¹ ≈ from (@unit_left C _ I).
Proof.
  rewrite bimap_id_id.
  apply id_left.
Qed.

Lemma unit_comonoid_counit_right :
  bimap id[I] id[I] ∘ (@unit_left C _ I)⁻¹ ≈ from (@unit_right C _ I).
Proof.
  rewrite bimap_id_id.
  rewrite id_left.
  apply unit_identity_from.
Qed.

Definition Comonoid_Unit : Comonoid I :=
  @Build_Comonoid C _ I
    ((@unit_left C _ I)⁻¹)
    id[I]
    unit_comonoid_coassoc
    unit_comonoid_counit_left
    unit_comonoid_counit_right.

Lemma Comonoid_Unit_delta :
  @delta _ _ _ Comonoid_Unit ≈ (@unit_left C _ I)⁻¹.
Proof. reflexivity. Qed.

Lemma Comonoid_Unit_epsilon : @epsilon _ _ _ Comonoid_Unit ≈ id[I].
Proof. reflexivity. Qed.

Lemma unit_comonoid_cocomm :
  braid ∘ (@unit_left C _ I)⁻¹ ≈ (@unit_left C _ I)⁻¹.
Proof.
  rewrite braid_I_I.
  apply id_left.
Qed.

Definition CommutativeComonoid_Unit : CommutativeComonoid I :=
  @Build_CommutativeComonoid C S I Comonoid_Unit unit_comonoid_cocomm.

End ComonoidUnit.
