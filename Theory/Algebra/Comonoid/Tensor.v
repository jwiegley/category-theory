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

    The interchange toolkit of Structure/Monoidal/Braided/Proofs.v
    states its naturality, involution and unit coherences only in the
    diagonal forms consumed by the copy-discard stack ([swap_inner_nat1],
    the [mid_swap_iso] lemmas of Hypergraph.v, [swap_inner_unit_left] /
    [swap_inner_unit_right] at [swap_inner I I x x]).  Tensoring two
    DIFFERENT comonoids needs the mixed-argument forms, so this file
    first extends the toolkit — replaying the library's own proof
    scripts at general arguments:

    - [swap_inner_natural]: full four-slot naturality (the
      [mid_swap_inv_natural] chase of CopyDiscard/Proofs.v, which never
      uses that its four morphisms coincide pairwise);
    - [swap_inner_invol]: the interchange is involutive (the
      [mid_swap_iso] chase of Hypergraph.v with four distinct letters);
    - [swap_inner_unit_left2] / [swap_inner_unit_right2]: unit coherence
      at [swap_inner I I x y] / [swap_inner x y I I], plus the solved
      and inverse-orientation corollaries the counit laws consume;
    - [swap_inner_assoc_inv]: the associativity hexagon
      [swap_inner_assoc] with every factor inverted, obtained by
      exhibiting both sides as two-sided inverses of the same composite
      ([comp_inverse_unique]).

    nLab:      https://ncatlab.org/nlab/show/comonoid
    nLab:      https://ncatlab.org/nlab/show/monoidal+functor
    Reference: Fong & Spivak, "Hypergraph Categories",
               J. Pure Appl. Algebra 223(11):4746–4777, 2019
               (arXiv:1806.08304), §2
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
               string diagrams", MSCS 29(7):938–971, 2019
               (arXiv:1709.00322), §2 *)

(* ------------------------------------------------------------------ *)

(** ** Interchange toolkit extensions *)

Section InterchangeMore.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* Two-sided inverses are unique up to ≈: if [g] is a right inverse and
   [g'] a left inverse of the same [f], they agree.  Stated for plain
   morphisms (no isomorphism packaging), which is the form the inverted
   coherence laws below need.  This is a fully general [Category]-level
   fact (the section discharges it over [{C : Category}] alone); it
   carries the scoped name [comp_inverse_unique] so that it neither
   squats the generic name nor collides if the fact is later
   consolidated into Theory/Isomorphism.v. *)
Lemma comp_inverse_unique {x y : C} (f : x ~> y) (g g' : y ~> x) :
  f ∘ g ≈ id[y] -> g' ∘ f ≈ id[x] -> g ≈ g'.
Proof.
  intros H1 H2.
  rewrite <- (id_left g).
  rewrite <- H2.
  rewrite <- comp_assoc.
  rewrite H1.
  apply id_right.
Qed.

(** Naturality of the interchange in all four slots at once.  The proof
    replays the [mid_swap_inv_natural] script of
    Structure/Monoidal/CopyDiscard/Proofs.v, which is insensitive to the
    four morphisms being pairwise equal. *)
Lemma swap_inner_natural {a a' b b' c c' d d' : C}
      (f : a ~> a') (g : b ~> b') (h : c ~> c') (k : d ~> d') :
  swap_inner a' b' c' d' ∘ ((f ⨂ g) ⨂ (h ⨂ k))
    ≈ ((f ⨂ h) ⨂ (g ⨂ k)) ∘ swap_inner a b c d.
Proof.
  unfold swap_inner.
  rewrite <- !comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal.
  rewrite from_tensor_assoc_natural.
  normal.
  comp_right.
  comp_left.
  normal.
  bimap_left.
  rewrite to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  comp_left.
  comp_right.
  normal.
  bimap_right.
  symmetry.
  apply bimap_braid.
Qed.

(* The same naturality in mid-composition ("cons") position, oriented
   for pushing a tensor-of-tensors across the interchange from the
   left. *)
Lemma swap_inner_natural_cons {a a' b b' c c' d d' z : C}
      (f : a ~> a') (g : b ~> b') (h : c ~> c') (k : d ~> d')
      (m : z ~> ((a ⨂ b) ⨂ (c ⨂ d))%object) :
  ((f ⨂ h) ⨂ (g ⨂ k)) ∘ (swap_inner a b c d ∘ m)
    ≈ swap_inner a' b' c' d' ∘ (((f ⨂ g) ⨂ (h ⨂ k)) ∘ m).
Proof.
  rewrite comp_assoc.
  rewrite <- swap_inner_natural.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

(** Involution: swapping the two middle factors twice is the identity.
    This is the [mid_swap_iso] chase of Hypergraph.v carried out with
    four distinct objects; the braid pair inside dies by
    [braid_invol]. *)
Lemma swap_inner_invol {a b c d : C} :
  swap_inner a c b d ∘ swap_inner a b c d
    ≈ id[((a ⨂ b) ⨂ (c ⨂ d))%object].
Proof.
  unfold swap_inner.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) ((tensor_assoc)⁻¹)).
  rewrite iso_to_from, id_left.
  rewrite (comp_assoc (bimap id ((tensor_assoc)⁻¹))
                      (bimap id (to tensor_assoc))).
  rewrite <- bimap_comp, id_left.
  rewrite iso_from_to, bimap_id_id, id_left.
  rewrite (comp_assoc (bimap id (bimap (@braid C _ c b) id[d]))
                      (bimap id (bimap (@braid C _ b c) id[d]))).
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

Lemma swap_inner_invol_cons {a b c d z : C}
      (k : z ~> ((a ⨂ b) ⨂ (c ⨂ d))%object) :
  swap_inner a c b d ∘ (swap_inner a b c d ∘ k) ≈ k.
Proof.
  rewrite comp_assoc.
  rewrite swap_inner_invol.
  apply id_left.
Qed.

(** *** Unit coherence at mixed arguments

    [braid_conjugate_left] and [swap_inner_unit_left]/[_right] of
    Braided/Proofs.v are stated with both non-unit slots equal; the
    proofs below replay the same scripts with the two slots
    distinct. *)

Lemma braid_conjugate_left2 {x y : C} :
  to tensor_assoc ∘ (@braid C _ I x ⨂ id[y]) ∘ tensor_assoc⁻¹
    ≈ (id[x] ⨂ unit_left⁻¹) ∘ unit_left.
Proof.
  rewrite braid_I_left.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite triangle_inverse_middle.
  rewrite <- comp_assoc.
  rewrite <- bimap_triangle_left.
  reflexivity.
Qed.

Lemma swap_inner_unit_left2 {x y : C} :
  (unit_left ⨂ unit_left) ∘ swap_inner I I x y
    ∘ (unit_left⁻¹ ⨂ id[(x ⨂ y)%object])
    ≈ @unit_left C _ (x ⨂ y).
Proof.
  unfold swap_inner.
  normal.
  rewrite braid_conjugate_left2.
  rewrite unit_identity_from.
  rewrite <- !comp_assoc.
  rewrite triangle_inverse_middle.
  assert (E : (id[I] ⨂ ((id[x] ⨂ (@unit_left C _ y)⁻¹) ∘ unit_left))
                ∘ (id[I] ⨂ (@unit_left C _ (x ⨂ y))⁻¹)
                ≈ id[I] ⨂ (id[x] ⨂ (@unit_left C _ y)⁻¹)).
  { rewrite <- bimap_comp_id_left.
    bimap_left.
    rewrite <- comp_assoc.
    rewrite iso_to_from.
    apply id_right. }
  rewrite E; clear E.
  rewrite <- from_tensor_assoc_natural.
  rewrite bimap_id_id.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_right.
  rewrite <- bimap_triangle_left.
  reflexivity.
Qed.

Lemma swap_inner_unit_right2 {x y : C} :
  (unit_right ⨂ unit_right) ∘ swap_inner x y I I
    ∘ (id[(x ⨂ y)%object] ⨂ unit_left⁻¹)
    ≈ @unit_right C _ (x ⨂ y).
Proof.
  rewrite <- (id_right (swap_inner x y I I)).
  rewrite <- (braid_invol (x := (x ⨂ y)%object) (y := (I ⨂ I)%object)).
  rewrite (comp_assoc (swap_inner x y I I)).
  rewrite swap_inner_braid.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.
  rewrite bimap_fuse_cons.
  rewrite !braid_unit_right.
  rewrite !comp_assoc.
  rewrite swap_inner_unit_left2.
  apply braid_unit_left.
Qed.

(* The unit coherences solved for the interchange composite, with the
   inverse unitor moved to the other side. *)

Lemma swap_inner_unit_left2_solved {x y : C} :
  (unit_left ⨂ unit_left) ∘ swap_inner I I x y
    ≈ @unit_left C _ (x ⨂ y) ∘ (unit_left ⨂ id[(x ⨂ y)%object]).
Proof.
  rewrite <- (id_right ((unit_left ⨂ unit_left) ∘ swap_inner I I x y)).
  assert (E : ((@unit_left C _ I)⁻¹ ⨂ id[(x ⨂ y)%object])
                ∘ (unit_left ⨂ id[(x ⨂ y)%object])
                ≈ id[((I ⨂ I) ⨂ (x ⨂ y))%object]).
  { rewrite bimap_fuse_id_right.
    rewrite iso_from_to.
    apply bimap_id_id. }
  rewrite <- E; clear E.
  rewrite !comp_assoc.
  rewrite swap_inner_unit_left2.
  reflexivity.
Qed.

Lemma swap_inner_unit_right2_solved {x y : C} :
  (unit_right ⨂ unit_right) ∘ swap_inner x y I I
    ≈ @unit_right C _ (x ⨂ y) ∘ (id[(x ⨂ y)%object] ⨂ unit_left).
Proof.
  rewrite <- (id_right ((unit_right ⨂ unit_right) ∘ swap_inner x y I I)).
  assert (E : (id[(x ⨂ y)%object] ⨂ (@unit_left C _ I)⁻¹)
                ∘ (id[(x ⨂ y)%object] ⨂ unit_left)
                ≈ id[((x ⨂ y) ⨂ (I ⨂ I))%object]).
  { rewrite bimap_id_fuse.
    rewrite iso_from_to.
    apply bimap_id_id. }
  rewrite <- E; clear E.
  rewrite !comp_assoc.
  rewrite swap_inner_unit_right2.
  reflexivity.
Qed.

(* The unit coherences in the inverse orientation: the interchange
   applied AFTER the doubled inverse unitors is the inverse unitor of
   the tensor, decorated by the unit-object unitor.  These are the exact
   residuals of the counit laws of the tensor comonoid. *)

Lemma swap_inner_from_unit_left2 {x y : C} :
  swap_inner I x I y ∘ (unit_left⁻¹ ⨂ unit_left⁻¹)
    ≈ (unit_left⁻¹ ⨂ id[(x ⨂ y)%object]) ∘ (@unit_left C _ (x ⨂ y))⁻¹.
Proof.
  apply (comp_inverse_unique ((unit_left ⨂ unit_left) ∘ swap_inner I I x y)).
  - rewrite <- !comp_assoc.
    rewrite swap_inner_invol_cons.
    rewrite <- bimap_comp.
    rewrite !iso_to_from.
    apply bimap_id_id.
  - rewrite <- !comp_assoc.
    rewrite swap_inner_unit_left2_solved.
    rewrite (cancel_from_to_cons unit_left).
    rewrite bimap_fuse_id_right.
    rewrite iso_from_to.
    apply bimap_id_id.
Qed.

Lemma swap_inner_from_unit_right2 {x y : C} :
  swap_inner x I y I ∘ (unit_right⁻¹ ⨂ unit_right⁻¹)
    ≈ (id[(x ⨂ y)%object] ⨂ unit_left⁻¹) ∘ (@unit_right C _ (x ⨂ y))⁻¹.
Proof.
  apply (comp_inverse_unique ((unit_right ⨂ unit_right) ∘ swap_inner x y I I)).
  - rewrite <- !comp_assoc.
    rewrite swap_inner_invol_cons.
    rewrite <- bimap_comp.
    rewrite !iso_to_from.
    apply bimap_id_id.
  - rewrite <- !comp_assoc.
    rewrite swap_inner_unit_right2_solved.
    rewrite (cancel_from_to_cons unit_right).
    rewrite bimap_id_fuse.
    rewrite iso_from_to.
    apply bimap_id_id.
Qed.

(** *** The associativity hexagon, inverted

    [swap_inner_assoc] with every factor replaced by its inverse (the
    inverse of an interchange being the interchange with the middle
    slots swapped, by [swap_inner_invol]).  Both sides are two-sided
    inverses of [swap_inner_assoc]'s left-hand side, so they agree by
    [comp_inverse_unique]. *)
Theorem swap_inner_assoc_inv {a b c d e f : C} :
  tensor_assoc⁻¹
    ∘ (id[(a ⨂ b)%object] ⨂ swap_inner c e d f)
    ∘ swap_inner a (c ⨂ e) b (d ⨂ f)
    ≈ (swap_inner a c b d ⨂ id[(e ⨂ f)%object])
        ∘ swap_inner (a ⨂ c) e (b ⨂ d) f
        ∘ (tensor_assoc⁻¹ ⨂ tensor_assoc⁻¹).
Proof.
  apply (comp_inverse_unique
           (swap_inner a b (c ⨂ e) (d ⨂ f)
              ∘ ((id[(a ⨂ b)%object] ⨂ swap_inner c d e f)
                   ∘ to tensor_assoc))).
  - (* The forward hexagon side against the inverted left side. *)
    rewrite <- !comp_assoc.
    rewrite (cancel_to_from_cons tensor_assoc).
    rewrite bimap_id_fuse_cons.
    rewrite swap_inner_invol.
    rewrite bimap_id_id, id_left.
    apply swap_inner_invol.
  - (* The inverted right side against the forward hexagon side; here
       [swap_inner_assoc] itself discharges the composite. *)
    rewrite swap_inner_assoc.
    rewrite <- !comp_assoc.
    rewrite bimap_fuse_cons.
    rewrite !iso_from_to.
    rewrite bimap_id_id, id_left.
    rewrite swap_inner_invol_cons.
    rewrite bimap_fuse_id_right.
    rewrite swap_inner_invol.
    apply bimap_id_id.
Qed.

End InterchangeMore.

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
