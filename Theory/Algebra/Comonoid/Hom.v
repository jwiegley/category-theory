Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(** * Comonoid homomorphisms and the category of internal comonoids *)

(* nLab: https://ncatlab.org/nlab/show/comonoid

   Given internal comonoids (x, delta[Cx], epsilon[Cx]) and
   (y, delta[Cy], epsilon[Cy]) in a monoidal category (C, ⨂, I), a morphism
   f : x ~> y is a comonoid homomorphism when it commutes with the
   comultiplications and counits:

     comultiplication square   delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx]
     counit triangle           epsilon[Cy] ∘ f ≈ epsilon[Cx]

   This is the exact arrow-reversed mirror of [MonoidHom] in
   Theory/Algebra/Monoid/Hom.v.  Comonoid homomorphisms contain the
   identities and are closed under composition, so internal comonoids and
   their homomorphisms form a category Comon(C), packaged with sigma objects
   and homs exactly as [Mon] is — morphism equivalence is equivalence of the
   underlying C-morphisms — and projecting out the underlying object and
   morphism gives the forgetful functor Comon(C) ⟶ C, faithful by
   construction ([Comon_Forget_Faithful]).

   Beyond its algebraic role, this class is the predicate behind
   *determinism* in categorical probability: in a category where every
   object carries a canonical copy/discard comonoid, Cho–Jacobs
   (arXiv:1709.00322) call a morphism deterministic precisely when it is a
   comonoid homomorphism between the canonical comonoids — copying the
   output of f is the same as running f twice on a copied input, and
   discarding the output is the same as discarding the input.
   Structure/Monoidal/CopyDiscard/Deterministic.v instantiates this class at
   those canonical comonoids.

   The [Comonoid_Iso] transport at the end moves a comonoid structure across
   an isomorphism i : x ≅ y by conjugation; both components of i then become
   comonoid homomorphisms — with respect to the TRANSPORTED structure on the
   codomain.  It is provided as standalone infrastructure and currently has
   no in-tree consumer.  In particular,
   Structure/Monoidal/CopyDiscard/Deterministic.v does NOT use it: the
   determinism of the structural isomorphisms demands a [ComonoidHom]
   between the canonical comonoids at BOTH endpoints, whereas the transport
   only yields homomorphisms into [Comonoid_Iso i Cx], so those lemmas are
   proved there by direct coherence chases at the canonical supply. *)

Section ComonoidHom.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class ComonoidHom {x y : C} (Cx : Comonoid x) (Cy : Comonoid y)
      (f : x ~> y) : Type := {
  (* f preserves comultiplication: delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx] *)
  hom_delta   : delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx];
  (* f preserves the counit: epsilon[Cy] ∘ f ≈ epsilon[Cx] *)
  hom_epsilon : epsilon[Cy] ∘ f ≈ epsilon[Cx]
}.

(* The identity is a comonoid homomorphism. *)
Lemma ComonoidHom_id {x} (Cx : Comonoid x) : ComonoidHom Cx Cx id.
Proof. split; cat. Qed.

(* Comonoid homomorphisms are closed under composition: paste the two
   preservation squares, fusing (f ⨂ f) ∘ (g ⨂ g) into (f ∘ g) ⨂ (f ∘ g)
   by the interchange law [bimap_comp]. *)
Lemma ComonoidHom_comp {x y z} {Cx : Comonoid x} {Cy : Comonoid y}
      {Cz : Comonoid z} {f : y ~> z} {g : x ~> y} :
  ComonoidHom Cy Cz f → ComonoidHom Cx Cy g → ComonoidHom Cx Cz (f ∘ g).
Proof.
  intros F G.
  split.
  - rewrite comp_assoc.
    rewrite (@hom_delta _ _ _ _ _ F).
    rewrite <- comp_assoc.
    rewrite (@hom_delta _ _ _ _ _ G).
    rewrite comp_assoc.
    now rewrite <- bimap_comp.
  - rewrite comp_assoc.
    rewrite (@hom_epsilon _ _ _ _ _ F).
    apply (@hom_epsilon _ _ _ _ _ G).
Qed.

(* Being a comonoid homomorphism transports along ≈ (bimap respects ≈). *)
Lemma ComonoidHom_equiv {x y} {Cx : Comonoid x} {Cy : Comonoid y}
      {f g : x ~> y} :
  f ≈ g → ComonoidHom Cx Cy f → ComonoidHom Cx Cy g.
Proof.
  intros E F.
  split.
  - rewrite <- E.
    apply (@hom_delta _ _ _ _ _ F).
  - rewrite <- E.
    apply (@hom_epsilon _ _ _ _ _ F).
Qed.

(* Transport of a comonoid structure across an isomorphism i : x ≅ y, by
   conjugation: copy on y is "carry back along i⁻¹, copy on x, carry both
   halves forward along i", and discard on y is "carry back, discard".  The
   laws are those of Cx conjugated by i; each proof cancels the inner
   [from i ∘ to i], applies the corresponding law of Cx, and transports the
   result across the naturality square of the relevant structural map. *)

#[local] Obligation Tactic := intros.

Program Definition Comonoid_Iso {x y : C} (i : x ≅ y) (Cx : Comonoid x) :
  Comonoid y := {|
  delta   := (to i ⨂ to i) ∘ delta[Cx] ∘ from i;
  epsilon := epsilon[Cx] ∘ from i
|}.
Next Obligation.
  (* coassociativity: cancel the conjugating iso on the right, then it is
     [delta_coassoc] of Cx pushed across the associator's naturality. *)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : ((to i ⨂ to i) ∘ delta[Cx]) ⨂ to i
                ≈ ((to i ⨂ to i) ⨂ to i) ∘ (delta[Cx] ⨂ id)).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_coassoc _ _ _ Cx).
  normal.
  rewrite from_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  normal.
  reflexivity.
Qed.
Next Obligation.
  (* left counit: cancel the conjugating iso, apply [delta_counit_left] of
     Cx, and close with naturality of the left unitor's inverse. *)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : epsilon[Cx] ⨂ to i ≈ (id ⨂ to i) ∘ (epsilon[Cx] ⨂ id)).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_counit_left _ _ _ Cx).
  apply from_unit_left_natural.
Qed.
Next Obligation.
  (* right counit: mirror of the previous obligation. *)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : to i ⨂ epsilon[Cx] ≈ (to i ⨂ id) ∘ (id ⨂ epsilon[Cx])).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_counit_right _ _ _ Cx).
  apply from_unit_right_natural.
Qed.

#[local] Obligation Tactic := cat_simpl.

(* Both components of the isomorphism are comonoid homomorphisms with
   respect to the transported structure. *)
Lemma ComonoidHom_Iso_to {x y} (i : x ≅ y) (Cx : Comonoid x) :
  ComonoidHom Cx (Comonoid_Iso i Cx) (to i).
Proof.
  split; simpl.
  - rewrite <- !comp_assoc.
    rewrite iso_from_to; cat.
  - rewrite <- comp_assoc.
    rewrite iso_from_to; cat.
Qed.

Lemma ComonoidHom_Iso_from {x y} (i : x ≅ y) (Cx : Comonoid x) :
  ComonoidHom (Comonoid_Iso i Cx) Cx (from i).
Proof.
  split; simpl.
  - symmetry.
    rewrite comp_assoc.
    normal.
    rewrite !iso_from_to; cat.
  - reflexivity.
Qed.

(* The category Comon(C) of internal comonoids in C: objects are objects of
   C equipped with a comonoid structure, morphisms are C-morphisms equipped
   with a proof of homomorphy, and equivalence is equivalence of the
   underlying morphisms — the same sigma packaging as [Mon] and [Sub] in
   Construction/Subcategory.v. *)
Program Definition Comon : Category := {|
  obj     := { x : C & Comonoid x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & ComonoidHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; ComonoidHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; ComonoidHom_comp `2 f `2 g)
|}.

(* The forgetful functor Comon(C) ⟶ C projects out the underlying object
   and morphism; it is faithful by construction ([Comon_Forget_Faithful]
   below). *)
Program Definition Comon_Forget : Comon ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

(* Faithfulness is definitional: morphism equivalence in Comon(C) IS
   equivalence of the underlying C-morphisms, which is what [fmap] projects
   out. *)
#[export] Instance Comon_Forget_Faithful : Faithful Comon_Forget.
Proof.
  constructor.
  intros X Y f g E.
  exact E.
Qed.

End ComonoidHom.

Arguments Comon C {M}.
