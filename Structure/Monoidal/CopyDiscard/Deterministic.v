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
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Hom.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * Deterministic morphisms in a copy-discard category

    A [CopyDiscard] category deliberately imposes NO naturality on [copy] and
    [discard]: a general morphism need not commute with duplication or
    deletion.  Following Cho–Jacobs, a morphism [f : x ~> y] is
    DETERMINISTIC when it does commute with both, i.e. when it is a comonoid
    homomorphism between the canonical comonoids:

      copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x]        (copying the output of [f]
                                               is running [f] twice on a
                                               copied input)
      discard[y] ∘ f ≈ discard[x]             (running [f] and discarding
                                               is just discarding)

    In a Markov category these two squares single out exactly the morphisms
    that carry no randomness.  Deterministic morphisms contain the
    identities and are closed under composition and under ⨂; all the
    structural isomorphisms of the symmetric monoidal base — braiding,
    unitors, associator — are deterministic.  Consequently the deterministic
    morphisms form a wide (lluf) subcategory [Det] of [C], packaged here
    through [Construction/Subcategory.v].

    The structural-morphism proofs are instances of the classical fact that
    the squaring functor [x ↦ x ⨂ x] of a symmetric monoidal category is
    itself symmetric (strong) monoidal, with structure map the middle
    interchange [(a ⨂ b) ⨂ (c ⨂ d) ≅ (a ⨂ c) ⨂ (b ⨂ d)].  That
    interchange, [swap_inner], and its coherence laws ([swap_inner_braid],
    [swap_inner_assoc], [swap_inner_unit_left] / [swap_inner_unit_right])
    are developed for any symmetric monoidal category in the shared toolkit
    of Structure/Monoidal/Braided/Proofs.v; this file identifies its
    diagonal with Hypergraph.v's [mid_swap_inv] ([swap_inner_diag]) and
    restates the coherences in the [mid_swap_inv] form the determinism
    proofs consume ([mid_swap_inv_braid], [mid_swap_inv_assoc],
    [mid_swap_inv_unit_left] / [mid_swap_inv_unit_right]).

    The structural determinism lemmas are direct coherence chases at the
    canonical [cd_comonoid] supply.  The [Comonoid_Iso] transport of
    Theory/Algebra/Comonoid/Hom.v cannot be used for them: determinism
    demands a [ComonoidHom] between the canonical comonoids at BOTH
    endpoints, whereas transporting a comonoid along a structural
    isomorphism only produces homomorphisms into the transported comonoid
    [Comonoid_Iso i _], which is not the canonical one.

    The headline citation-ready facts are [copy_natural_on_deterministic]
    and [discard_natural_on_deterministic]: copy/discard ARE natural once
    restricted to deterministic morphisms.

    nLab:      https://ncatlab.org/nlab/show/Markov+category
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
               string diagrams", MSCS 29(7):938–971, 2019
               (arXiv:1709.00322), §2
    Reference: Fritz, "A synthetic approach to Markov kernels, conditional
               independence and theorems on sufficient statistics",
               Adv. Math. 370:107239, 2020 (arXiv:1908.07021), §10 *)

(* ------------------------------------------------------------------ *)

(** ** Diagonal corollaries of the interchange

    The four-object middle interchange [swap_inner] and its coherence laws
    are developed for any symmetric monoidal category in the shared toolkit
    of Structure/Monoidal/Braided/Proofs.v.  Its diagonal
    [swap_inner x x y y] is definitionally Hypergraph.v's [mid_swap_inv]
    ([swap_inner_diag]); the corollaries below restate the interchange
    coherences in [mid_swap_inv] form, which is the shape the determinism
    proofs consume.  This is the only place the toolkit meets the
    hypergraph vocabulary — Braided/Proofs.v itself stays independent of
    the hypergraph stack. *)

Section MidSwapCoherence.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* [mid_swap_inv] (Hypergraph.v) is the diagonal of the interchange. *)
Lemma swap_inner_diag (x y : C) : swap_inner x x y y ≈ mid_swap_inv x y.
Proof. reflexivity. Qed.

Corollary mid_swap_inv_braid {x y : C} :
  mid_swap_inv y x ∘ braid
    ≈ (@braid C _ x y ⨂ @braid C _ x y) ∘ mid_swap_inv x y.
Proof.
  rewrite <- !swap_inner_diag.
  apply swap_inner_braid.
Qed.

Corollary mid_swap_inv_assoc {x y z : C} :
  mid_swap_inv x (y ⨂ z)
    ∘ ((id[(x ⨂ x)%object] ⨂ mid_swap_inv y z) ∘ to tensor_assoc)
    ≈ (to tensor_assoc ⨂ to tensor_assoc)
        ∘ (mid_swap_inv (x ⨂ y) z ∘ (mid_swap_inv x y ⨂ id[(z ⨂ z)%object])).
Proof.
  rewrite <- !swap_inner_diag.
  apply swap_inner_assoc.
Qed.

(* The unit coherence, left form: conjugating [mid_swap_inv I x] by the
   canonical unit isomorphisms is the left unitor. *)
Corollary mid_swap_inv_unit_left {x : C} :
  (unit_left ⨂ unit_left) ∘ mid_swap_inv I x
    ∘ (unit_left⁻¹ ⨂ id[(x ⨂ x)%object])
    ≈ @unit_left C _ (x ⨂ x).
Proof.
  rewrite <- swap_inner_diag.
  apply swap_inner_unit_left.
Qed.

(* The unit coherence, right form. *)
Corollary mid_swap_inv_unit_right {x : C} :
  (unit_right ⨂ unit_right) ∘ mid_swap_inv x I
    ∘ (id[(x ⨂ x)%object] ⨂ unit_left⁻¹)
    ≈ @unit_right C _ (x ⨂ x).
Proof.
  rewrite <- swap_inner_diag.
  apply swap_inner_unit_right.
Qed.

End MidSwapCoherence.

(* ------------------------------------------------------------------ *)

(** ** Deterministic morphisms *)

Section Deterministic.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{CD : @CopyDiscard C S}.

(* A morphism is deterministic when it is a comonoid homomorphism between
   the canonical copy/discard comonoids (Cho–Jacobs, Definition 2.2 of
   arXiv:1709.00322 in the Markov setting). *)
Definition deterministic {x y : C} (f : x ~> y) : Type :=
  ComonoidHom (cd_comonoid x) (cd_comonoid y) f.

Lemma deterministic_id {x : C} : deterministic (id[x]).
Proof. apply ComonoidHom_id. Qed.

Lemma deterministic_comp {x y z : C} {f : y ~> z} {g : x ~> y} :
  deterministic f → deterministic g → deterministic (f ∘ g).
Proof. apply ComonoidHom_comp. Qed.

Lemma deterministic_equiv {x y : C} {f g : x ~> y} :
  f ≈ g → deterministic f → deterministic g.
Proof. apply ComonoidHom_equiv. Qed.

(** The headline: copy and discard ARE natural once restricted to
    deterministic morphisms.  These are the two squares whose breakdown for
    general morphisms is the defining negative space of [CopyDiscard]. *)

Theorem copy_natural_on_deterministic {x y : C} (f : x ~> y) :
  deterministic f → copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x].
Proof. intro F. exact (@hom_delta _ _ _ _ _ _ _ F). Qed.

Theorem discard_natural_on_deterministic {x y : C} (f : x ~> y) :
  deterministic f → discard[y] ∘ f ≈ discard[x].
Proof. intro F. exact (@hom_epsilon _ _ _ _ _ _ _ F). Qed.

(* Closure under the tensor: the δ-square pastes through
   [mid_swap_inv_natural], the ε-square through the unit. *)
Lemma deterministic_tensor {x x' y y' : C} {f : x ~> y} {f' : x' ~> y'} :
  deterministic f → deterministic f' → deterministic (f ⨂ f').
Proof.
  intros [Fd Fe] [Fd' Fe'].
  split.
  - change (copy[(y ⨂ y')%object] ∘ (f ⨂ f')
              ≈ ((f ⨂ f') ⨂ (f ⨂ f')) ∘ copy[(x ⨂ x')%object]).
    rewrite !copy_tensor.
    rewrite <- comp_assoc.
    rewrite <- bimap_comp.
    rewrite Fd, Fd'.
    rewrite bimap_comp.
    rewrite comp_assoc.
    rewrite mid_swap_inv_natural.
    rewrite <- comp_assoc.
    reflexivity.
  - change (discard[(y ⨂ y')%object] ∘ (f ⨂ f')
              ≈ discard[(x ⨂ x')%object]).
    rewrite !discard_tensor.
    rewrite <- comp_assoc.
    rewrite <- bimap_comp.
    rewrite Fe, Fe'.
    reflexivity.
Qed.

(* The inverse of a deterministic isomorphism is deterministic. *)
Lemma deterministic_iso_from {x y : C} (i : x ≅ y) :
  deterministic (to i) → deterministic (i⁻¹).
Proof.
  intros [Fd Fe].
  split.
  - rewrite <- (id_left (delta[ccomon_comonoid] ∘ i⁻¹)).
    rewrite <- bimap_id_id.
    rewrite <- (iso_from_to i).
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to i ⨂ to i)).
    rewrite <- Fd.
    rewrite <- !comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
  - rewrite <- Fe.
    rewrite <- comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
Qed.

(** Rewrite-friendly forms of the unit coherence fields. *)

Corollary copy_unit : copy[I] ≈ (@unit_left C _ I)⁻¹.
Proof. exact cd_unit_delta. Qed.

Corollary discard_unit : discard[I] ≈ id[I].
Proof. exact cd_unit_epsilon. Qed.

(** *** The structural isomorphisms are deterministic *)

(* Braiding: the δ-square is the interchange/braid compatibility, the
   ε-square degenerates through [braid_I_I]. *)

Lemma copy_braid {x y : C} :
  copy[(y ⨂ x)%object] ∘ braid ≈ (braid ⨂ braid) ∘ copy[(x ⨂ y)%object].
Proof.
  rewrite !copy_tensor.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  rewrite (comp_assoc (mid_swap_inv y x)).
  rewrite mid_swap_inv_braid.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Lemma discard_braid {x y : C} :
  discard[(y ⨂ x)%object] ∘ braid ≈ discard[(x ⨂ y)%object].
Proof.
  rewrite !discard_tensor.
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite braid_I_I.
  rewrite id_right.
  reflexivity.
Qed.

Theorem deterministic_braid {x y : C} : deterministic (@braid C _ x y).
Proof.
  split.
  - exact copy_braid.
  - exact discard_braid.
Qed.

(* Left unitor. *)

Lemma copy_unit_left {x : C} :
  copy[x] ∘ unit_left
    ≈ (unit_left ⨂ unit_left) ∘ copy[(I ⨂ x)%object].
Proof.
  rewrite copy_tensor.
  rewrite copy_unit.
  rewrite to_unit_left_natural.
  rewrite <- (bimap_id_right_left ((@unit_left C _ I)⁻¹) (copy x)).
  rewrite !comp_assoc.
  comp_right.
  symmetry.
  apply mid_swap_inv_unit_left.
Qed.

Lemma discard_unit_left {x : C} :
  discard[x] ∘ unit_left ≈ discard[(I ⨂ x)%object].
Proof.
  rewrite discard_tensor.
  rewrite discard_unit.
  rewrite to_unit_left_natural.
  reflexivity.
Qed.

Theorem deterministic_unit_left_to {x : C} :
  deterministic (to (@unit_left C _ x)).
Proof.
  split.
  - exact copy_unit_left.
  - exact discard_unit_left.
Qed.

Theorem deterministic_unit_left_from {x : C} :
  deterministic ((@unit_left C _ x)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_unit_left_to). Qed.

(* Right unitor. *)

Lemma copy_unit_right {x : C} :
  copy[x] ∘ unit_right
    ≈ (unit_right ⨂ unit_right) ∘ copy[(x ⨂ I)%object].
Proof.
  rewrite copy_tensor.
  rewrite copy_unit.
  rewrite to_unit_right_natural.
  rewrite <- (bimap_id_left_right ((@unit_left C _ I)⁻¹) (copy x)).
  rewrite !comp_assoc.
  comp_right.
  symmetry.
  apply mid_swap_inv_unit_right.
Qed.

Lemma discard_unit_right {x : C} :
  discard[x] ∘ unit_right ≈ discard[(x ⨂ I)%object].
Proof.
  rewrite discard_tensor.
  rewrite discard_unit.
  rewrite to_unit_right_natural.
  rewrite <- unit_identity.
  reflexivity.
Qed.

Theorem deterministic_unit_right_to {x : C} :
  deterministic (to (@unit_right C _ x)).
Proof.
  split.
  - exact copy_unit_right.
  - exact discard_unit_right.
Qed.

Theorem deterministic_unit_right_from {x : C} :
  deterministic ((@unit_right C _ x)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_unit_right_to). Qed.

(* Associator: the δ-square is the associativity hexagon of the
   interchange, the ε-square a triangle-and-Kelly computation. *)

Lemma copy_tensor_assoc {x y z : C} :
  copy[(x ⨂ (y ⨂ z))%object] ∘ to tensor_assoc
    ≈ (to tensor_assoc ⨂ to tensor_assoc) ∘ copy[((x ⨂ y) ⨂ z)%object].
Proof.
  rewrite !copy_tensor.
  assert (E1 : (copy x ⨂ (mid_swap_inv y z ∘ (copy y ⨂ copy z)))
                 ≈ (id[(x ⨂ x)%object] ⨂ mid_swap_inv y z)
                     ∘ (copy x ⨂ (copy y ⨂ copy z))).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E1; clear E1.
  assert (E2 : ((mid_swap_inv x y ∘ (copy x ⨂ copy y)) ⨂ copy z)
                 ≈ (mid_swap_inv x y ⨂ id[(z ⨂ z)%object])
                     ∘ ((copy x ⨂ copy y) ⨂ copy z)).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E2; clear E2.
  spose (to_tensor_assoc_natural (copy x) (copy y) (copy z)) as X.
  rewrite <- !comp_assoc.
  rewrite X; clear X.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply mid_swap_inv_assoc.
Qed.

Lemma discard_tensor_assoc {x y z : C} :
  discard[(x ⨂ (y ⨂ z))%object] ∘ to tensor_assoc
    ≈ discard[((x ⨂ y) ⨂ z)%object].
Proof.
  rewrite !discard_tensor.
  assert (E1 : (discard x ⨂ (unit_left ∘ (discard y ⨂ discard z)))
                 ≈ (id[I] ⨂ to (@unit_left C _ I))
                     ∘ (discard x ⨂ (discard y ⨂ discard z))).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E1; clear E1.
  assert (E2 : ((unit_left ∘ (discard x ⨂ discard y)) ⨂ discard z)
                 ≈ (to (@unit_left C _ I) ⨂ id[I])
                     ∘ ((discard x ⨂ discard y) ⨂ discard z)).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E2; clear E2.
  spose (to_tensor_assoc_natural (discard x) (discard y) (discard z)) as X.
  rewrite <- !comp_assoc.
  rewrite X; clear X.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  rewrite <- unit_identity.
  reflexivity.
Qed.

Theorem deterministic_tensor_assoc_to {x y z : C} :
  deterministic (to (@tensor_assoc C _ x y z)).
Proof.
  split.
  - exact copy_tensor_assoc.
  - exact discard_tensor_assoc.
Qed.

Theorem deterministic_tensor_assoc_from {x y z : C} :
  deterministic ((@tensor_assoc C _ x y z)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_tensor_assoc_to). Qed.

(** *** The wide deterministic subcategory (Cho–Jacobs [Det]) *)

Program Definition DeterministicSub : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => deterministic f;
  scomp := fun _ _ _ _ _ _ _ _ df dg => deterministic_comp df dg;
  sid   := fun _ _ => deterministic_id
|}.

Definition Det : Category := Sub C DeterministicSub.

Lemma Det_wide : Wide C DeterministicSub.
Proof. intro x; exact ttt. Qed.

(* The inclusion Det ⟶ C is the generic (faithful) [Incl C DeterministicSub]
   from Construction/Subcategory.v. *)

End Deterministic.
