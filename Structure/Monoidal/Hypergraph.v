Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.

Generalizable All Variables.

(** * Hypergraph categories

    A hypergraph category is a symmetric monoidal category [(C, ⨂, I, σ)]
    equipped with a special commutative Frobenius algebra (SCFA) on every
    object, such that the SCFA on [X ⨂ Y] is canonically constructed from
    those on [X] and [Y].

    Following Carboni–Walters and Fong–Spivak, the canonical SCFA on the
    tensor is built from the "middle-interchange" isomorphism
    [(X ⨂ Y) ⨂ (X ⨂ Y) ≅ (X ⨂ X) ⨂ (Y ⨂ Y)] obtained by braiding the
    middle two factors:

      μ_{X⨂Y} : (X⨂Y) ⨂ (X⨂Y) -mid-> (X⨂X) ⨂ (Y⨂Y) -μ⊗μ-> X⨂Y
      η_{X⨂Y} : I = I⨂I -η⊗η-> X⨂Y
      δ_{X⨂Y} : X⨂Y -δ⊗δ-> (X⨂X) ⨂ (Y⨂Y) -mid-> (X⨂Y) ⨂ (X⨂Y)
      ε_{X⨂Y} : X⨂Y -ε⊗ε-> I⨂I = I

    Each of these is definable in terms of the [braid], [tensor_assoc],
    [unit_left] and [unit_right] structure of the symmetric monoidal
    category.

    Mathematical comments:

    - The middle-interchange iso is what nLab denotes "Tau" or
      "swap-inner-two-of-four".
    - On the unit object [I] the canonical SCFA is trivial:
      μ = unit_left, η = id, δ = unit_left⁻¹, ε = id.  These four
      coherence axioms are stated as the [scfa_unit_*] fields of the
      [Hypergraph] class. *)

Section Hypergraph.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(** The "middle two factors" swap [(X⨂Y) ⨂ (X⨂Y) ≅ (X⨂X) ⨂ (Y⨂Y)],
    built by re-associating, braiding the middle pair, then re-associating
    back.  Concretely, the chain is

      (X⨂Y) ⨂ (X⨂Y)
        =α=> X ⨂ (Y ⨂ (X⨂Y))
        =id⨂α⁻¹=> X ⨂ ((Y⨂X) ⨂ Y)
        =id⨂(braid⨂id)=> X ⨂ ((X⨂Y) ⨂ Y)
        =id⨂α=> X ⨂ (X ⨂ (Y⨂Y))
        =α⁻¹=> (X⨂X) ⨂ (Y⨂Y).
*)
Definition mid_swap (X Y : C) :
  (X ⨂ Y) ⨂ (X ⨂ Y) ~> (X ⨂ X) ⨂ (Y ⨂ Y) :=
  (@tensor_assoc C _ X X (Y ⨂ Y))⁻¹
    ∘ bimap id[X] (to (@tensor_assoc C _ X Y Y))
    ∘ bimap id[X] (bimap (@braid C _ Y X) id[Y])
    ∘ bimap id[X] ((@tensor_assoc C _ Y X Y)⁻¹)
    ∘ to (@tensor_assoc C _ X Y (X ⨂ Y)).

(** Inverse direction, used in the canonical [delta]. *)
Definition mid_swap_inv (X Y : C) :
  (X ⨂ X) ⨂ (Y ⨂ Y) ~> (X ⨂ Y) ⨂ (X ⨂ Y) :=
  (@tensor_assoc C _ X Y (X ⨂ Y))⁻¹
    ∘ bimap id[X] (to (@tensor_assoc C _ Y X Y))
    ∘ bimap id[X] (bimap (@braid C _ X Y) id[Y])
    ∘ bimap id[X] ((@tensor_assoc C _ X Y Y)⁻¹)
    ∘ to (@tensor_assoc C _ X X (Y ⨂ Y)).

(** ** The middle-swap is an isomorphism

    Both composites of [mid_swap] and [mid_swap_inv] reduce to the identity
    by associator cancellation, braid involution ([braid ∘ braid ≈ id]) on
    the inner pair, and the [bimap id id ≈ id] coherence. *)

Lemma mid_swap_iso (X Y : C) :
  mid_swap X Y ∘ mid_swap_inv X Y ≈ id[(X ⨂ X) ⨂ (Y ⨂ Y)].
Proof.
  unfold mid_swap, mid_swap_inv.
  rewrite <- !comp_assoc.
  (* Collapse the central α ∘ α⁻¹ to identity. *)
  rewrite (comp_assoc (to tensor_assoc) ((tensor_assoc)⁻¹)).
  rewrite iso_to_from, id_left.
  (* Collapse  id ⨂ α⁻¹ ∘ id ⨂ α  through bimap_comp + bimap_id_id. *)
  rewrite (comp_assoc (bimap id ((tensor_assoc)⁻¹))
                      (bimap id (to tensor_assoc))).
  rewrite <- bimap_comp, id_left.
  rewrite iso_from_to, bimap_id_id, id_left.
  (* Collapse the two adjacent inner braid bimaps via braid_invol. *)
  rewrite (comp_assoc (bimap id (bimap (@braid C _ Y X) id[Y]))
                      (bimap id (bimap (@braid C _ X Y) id[Y]))).
  rewrite <- bimap_comp, id_left.
  rewrite <- bimap_comp, id_left.
  rewrite braid_invol, !bimap_id_id, id_left.
  (* Collapse  id ⨂ α ∘ id ⨂ α⁻¹  via bimap_comp + iso_to_from. *)
  rewrite (comp_assoc (bimap id (to tensor_assoc))
                      (bimap id ((tensor_assoc)⁻¹))).
  rewrite <- bimap_comp, id_left.
  rewrite iso_to_from, bimap_id_id, id_left.
  (* Final outer α⁻¹ ∘ α. *)
  rewrite iso_from_to.
  reflexivity.
Qed.

Lemma mid_swap_iso_sym (X Y : C) :
  mid_swap_inv X Y ∘ mid_swap X Y ≈ id[(X ⨂ Y) ⨂ (X ⨂ Y)].
Proof.
  unfold mid_swap, mid_swap_inv.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) ((tensor_assoc)⁻¹)).
  rewrite iso_to_from, id_left.
  rewrite (comp_assoc (bimap id ((tensor_assoc)⁻¹))
                      (bimap id (to tensor_assoc))).
  rewrite <- bimap_comp, id_left.
  rewrite iso_from_to, bimap_id_id, id_left.
  rewrite (comp_assoc (bimap id (bimap (@braid C _ X Y) id[Y]))
                      (bimap id (bimap (@braid C _ Y X) id[Y]))).
  rewrite <- bimap_comp, id_left.
  rewrite <- bimap_comp, id_left.
  rewrite braid_invol, !bimap_id_id, id_left.
  rewrite (comp_assoc (bimap id (to tensor_assoc))
                      (bimap id ((tensor_assoc)⁻¹))).
  rewrite <- bimap_comp, id_left.
  rewrite iso_to_from, bimap_id_id, id_left.
  rewrite iso_from_to.
  reflexivity.
Qed.

(** Canonical [mu] on [X ⨂ Y] from those on [X] and [Y]. *)
Definition canonical_tensor_mu {X Y : C}
           (MX : Monoid X) (MY : Monoid Y) :
  (X ⨂ Y) ⨂ (X ⨂ Y) ~> X ⨂ Y :=
  bimap (@mu _ _ _ MX) (@mu _ _ _ MY) ∘ mid_swap X Y.

(** Canonical [eta] on [X ⨂ Y]. *)
Definition canonical_tensor_eta {X Y : C}
           (MX : Monoid X) (MY : Monoid Y) :
  I ~> X ⨂ Y :=
  bimap (@eta _ _ _ MX) (@eta _ _ _ MY) ∘ from (@unit_left C _ I).

(** Canonical [delta] on [X ⨂ Y]. *)
Definition canonical_tensor_delta {X Y : C}
           (CX : Comonoid X) (CY : Comonoid Y) :
  X ⨂ Y ~> (X ⨂ Y) ⨂ (X ⨂ Y) :=
  mid_swap_inv X Y ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY).

(** Canonical [epsilon] on [X ⨂ Y]. *)
Definition canonical_tensor_epsilon {X Y : C}
           (CX : Comonoid X) (CY : Comonoid Y) :
  X ⨂ Y ~> I :=
  to (@unit_left C _ I) ∘ bimap (@epsilon _ _ _ CX) (@epsilon _ _ _ CY).

(** ** The hypergraph category class

    A hypergraph category is a symmetric monoidal category with a chosen
    SCFA on every object, satisfying:

    - the tensor coherence: the SCFA on [X ⨂ Y] agrees with the canonical
      SCFA assembled from those of [X] and [Y];
    - the unit coherence: the SCFA on [I] is the trivial one (μ ≈ unit_left,
      η ≈ id, δ ≈ unit_left⁻¹, ε ≈ id).

    Without the unit coherence the user could supply an arbitrary
    incoherent SCFA on [I]; the unit fields close that gap. *)
Class Hypergraph : Type := {
  scfa : forall (X : C), SpecialCommutativeFrobenius X;

  scfa_tensor_mu : forall (X Y : C),
    scfa_mu (scfa (X ⨂ Y)) ≈ canonical_tensor_mu (scfa X) (scfa Y);

  scfa_tensor_eta : forall (X Y : C),
    scfa_eta (scfa (X ⨂ Y)) ≈ canonical_tensor_eta (scfa X) (scfa Y);

  scfa_tensor_delta : forall (X Y : C),
    scfa_delta (scfa (X ⨂ Y)) ≈ canonical_tensor_delta (scfa X) (scfa Y);

  scfa_tensor_epsilon : forall (X Y : C),
    scfa_epsilon (scfa (X ⨂ Y)) ≈ canonical_tensor_epsilon (scfa X) (scfa Y);

  (** Unit-object coherence — closes CRIT-1.  The canonical SCFA on [I]
      is the trivial one: [μ_I ≈ unit_left], [η_I ≈ id], etc. *)

  scfa_unit_mu :
    scfa_mu (scfa I) ≈ to (@unit_left C _ I);

  scfa_unit_eta :
    scfa_eta (scfa I) ≈ id[I];

  scfa_unit_delta :
    scfa_delta (scfa I) ≈ from (@unit_left C _ I);

  scfa_unit_epsilon :
    scfa_epsilon (scfa I) ≈ id[I]
}.

End Hypergraph.

Arguments scfa {C S _} X.
Arguments Hypergraph C {S}.
