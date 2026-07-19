Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Construction.Enriched.
Require Import Category.Construction.Enriched.Natural.
Require Import Category.Construction.Enriched.Compose.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** The ORDINARY category [C, D]_V of K-enriched functors and V-natural
    transformations.

    Objects are the enriched functors C ⟶ D, morphisms are the V-natural
    transformations of Natural.v under their componentwise setoid, the
    identity at F has components eid, and composition is VERTICAL
    composition: at x, the composite of τ after σ is

        ecompose ∘ (τ_x ⨂ σ_x) ∘ λ_I⁻¹

    where λ_I⁻¹ : I ~> I ⨂ I coerces the tensor unit so that the two
    I-sourced components can be tensored and then composed in D.

    Ledger entry 11 (a scope note, not a weakening): this file delivers the
    ordinary category of V-functors, which is exactly this phase's named
    deliverable.  Upgrading it to a genuine V-CATEGORY — with hom-OBJECTS
    ∫_c D(F c, G c) valued in K rather than hom-sets — requires ends in K
    and underlying-category machinery, and is deferred to a later phase
    (ledger 11). *)

(** * A small splitting/cons toolkit in K

    Interchange specializations that peel a composite out of one tensor
    slot, plus right-nested ("cons") forms of the enriched associativity
    law and of the solved triangle identities from
    Structure/Monoidal/Braided/Proofs.v.  All are pure monoidal-category
    facts except [ecompose_assoc_cons], which is the associativity law of
    an enriched category re-bracketed for right-nested rewriting. *)

Section Toolkit.

Context {K : Category}.
Context `{M : @Monoidal K}.

Lemma tensor_split_left {x y z w v : K}
      (f : y ~> z) (g : x ~> y) (h : w ~> v) :
  (f ∘ g) ⨂ h ≈ (f ⨂ id[v]) ∘ (g ⨂ h).
Proof. now rewrite <- bimap_comp, id_left. Qed.

Lemma tensor_split_right {x y z w v : K}
      (f : y ~> z) (g : x ~> y) (h : w ~> v) :
  (f ∘ g) ⨂ h ≈ (f ⨂ h) ∘ (g ⨂ id[w]).
Proof. now rewrite <- bimap_comp, id_right. Qed.

Lemma tensor_split2_left {x y z w v : K}
      (h : w ~> v) (f : y ~> z) (g : x ~> y) :
  h ⨂ (f ∘ g) ≈ (id[v] ⨂ f) ∘ (h ⨂ g).
Proof. now rewrite <- bimap_comp, id_left. Qed.

Lemma tensor_split2_right {x y z w v : K}
      (h : w ~> v) (f : y ~> z) (g : x ~> y) :
  h ⨂ (f ∘ g) ≈ (h ⨂ f) ∘ (id[w] ⨂ g).
Proof. now rewrite <- bimap_comp, id_right. Qed.

(* [triangle_inverse_middle] against a continuation:
   α ∘ ((ρ⁻¹ ⨂ id) ∘ k) ≈ (id ⨂ λ⁻¹) ∘ k. *)
Lemma triangle_inverse_middle_cons {u v z : K} (k : z ~> (u ⨂ v)%object) :
  tensor_assoc ∘ ((unit_right⁻¹ ⨂ id[v]) ∘ k) ≈ (id[u] ⨂ unit_left⁻¹) ∘ k.
Proof. rewrite comp_assoc; now rewrite triangle_inverse_middle. Qed.

(* The associativity law of an enriched category, re-bracketed so that it
   rewrites in right-nested composition chains. *)
Lemma ecompose_assoc_cons {D : Enriched K} {x y z w : D} {v : K}
      (k : v ~{K}~> ((z ⟿ w) ⨂ (y ⟿ z)) ⨂ (x ⟿ y)) :
  ecompose ∘ ((ecompose ⨂ id) ∘ k)
    ≈ ecompose ∘ ((id ⨂ ecompose) ∘ (tensor_assoc ∘ k)).
Proof.
  rewrite comp_assoc.
  rewrite ecompose_assoc.
  now rewrite <- !comp_assoc.
Qed.

End Toolkit.

(** * Component-level unit and associativity laws

    The vertical composite's unit and associativity laws hold at each
    component for purely typological reasons — no naturality is involved —
    so we prove them once, for arbitrary I-sourced elements of hom-objects
    of any K-category D. *)

Section Vertical.

Context {K : Category}.
Context `{M : @Monoidal K}.
Context {D : Enriched K}.

(* eid is a left unit for vertical composition, by eid_left. *)
Lemma vertical_id_left {x y : D} (f : I ~{K}~> (x ⟿ y)) :
  ecompose ∘ (eid ⨂ f) ∘ unit_left⁻¹ ≈ f.
Proof.
  rewrite <- (bimap_id_right_left eid).
  rewrite !comp_assoc.
  rewrite eid_left.
  rewrite <- comp_assoc.
  rewrite from_unit_left_natural.
  rewrite comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

(* eid is a right unit for vertical composition, by eid_right; Kelly's
   λ_I⁻¹ ≈ ρ_I⁻¹ ([unit_identity_from]) converts the coercion. *)
Lemma vertical_id_right {x y : D} (f : I ~{K}~> (x ⟿ y)) :
  ecompose ∘ (f ⨂ eid) ∘ unit_left⁻¹ ≈ f.
Proof.
  rewrite unit_identity_from.
  rewrite <- (bimap_id_left_right eid).
  rewrite !comp_assoc.
  rewrite eid_right.
  rewrite <- comp_assoc.
  rewrite from_unit_right_natural.
  rewrite comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

(* Vertical composition is associative: reassociate with ecompose_assoc,
   slide the associator through the components, and let the unitor
   bookkeeping cancel via the solved triangle identities. *)
Lemma vertical_assoc {w x y z : D}
      (p : I ~{K}~> (y ⟿ z)) (q : I ~{K}~> (x ⟿ y))
      (r : I ~{K}~> (w ⟿ x)) :
  ecompose ∘ (p ⨂ (ecompose ∘ (q ⨂ r) ∘ unit_left⁻¹)) ∘ unit_left⁻¹
    ≈ ecompose ∘ ((ecompose ∘ (p ⨂ q) ∘ unit_left⁻¹) ⨂ r) ∘ unit_left⁻¹.
Proof.
  rewrite <- !comp_assoc.
  (* left side: peel ecompose and the coercion out of the second slot *)
  rewrite (tensor_split2_left p ecompose).
  rewrite (tensor_split2_right p (q ⨂ r)).
  rewrite <- !comp_assoc.
  (* (id ⨂ λ_I⁻¹) ∘ λ_I⁻¹ ≈ λ_{I⨂I}⁻¹ ∘ λ_I⁻¹, then solve λ_{I⨂I}⁻¹ for α *)
  rewrite from_unit_left_natural.
  rewrite <- triangle_inverse_left.
  rewrite <- !comp_assoc.
  (* slide α through the three components and reassociate the composition *)
  rewrite to_assoc_nat_cons.
  rewrite <- ecompose_assoc_cons.
  (* fuse everything back into the right-hand shape *)
  rewrite !bimap_fuse_cons.
  rewrite id_right, id_left.
  (* match the bracketing of the right-hand side *)
  now rewrite (comp_assoc ecompose (p ⨂ q) (unit_left⁻¹)).
Qed.

End Vertical.

(** * The identity V-natural transformation *)

Program Definition EnrichedIdTransform {K : Category} `{M : @Monoidal K}
        {C D : Enriched K} (F : EnrichedFunctor K C D) :
  EnrichedTransform F F := {|
  etransform := fun x => eid
|}.
Next Obligation.
  intros K M C D F x y.
  simpl.
  (* Both whiskerings reduce to efmap: split eid out of the tensor, collapse
     ecompose against it via eid_left / eid_right, and cancel the unitors by
     their naturality. *)
  rewrite <- (bimap_id_right_left eid).
  rewrite <- (bimap_id_left_right eid).
  rewrite !comp_assoc.
  rewrite eid_left, eid_right.
  rewrite <- (to_unit_left_natural (efmap (EnrichedFunctor := F))).
  rewrite <- (to_unit_right_natural (efmap (EnrichedFunctor := F))).
  rewrite <- !comp_assoc.
  rewrite !iso_to_from.
  now rewrite !id_right.
Qed.

(** * Vertical composition of V-natural transformations *)

Program Definition EnrichedTransform_vcompose {K : Category} `{M : @Monoidal K}
        {C D : Enriched K} {F G J : EnrichedFunctor K C D}
        (τ : EnrichedTransform G J) (σ : EnrichedTransform F G) :
  EnrichedTransform F J := {|
  etransform := fun x =>
    ecompose ∘ (etransform (EnrichedTransform := τ) x
                  ⨂ etransform (EnrichedTransform := σ) x) ∘ unit_left⁻¹
|}.
Next Obligation.
  (* V-naturality of the vertical composite.  Reassociate with
     ecompose_assoc so that σ's component meets efmap F, apply σ's
     enaturality, reassociate back so that τ's component meets efmap G, and
     apply τ's enaturality; the unitor bookkeeping mirrors the ecompose_assoc
     proof pattern via the solved triangle identities. *)
  intros K M C D F G J τ σ x y.
  simpl.
  rewrite <- !comp_assoc.
  transitivity
    (ecompose
       ∘ (((ecompose
              ∘ (efmap (EnrichedFunctor := J) (x:=x) (y:=y)
                   ⨂ etransform (EnrichedTransform := τ) x)
              ∘ unit_right⁻¹)
             ⨂ etransform (EnrichedTransform := σ) x)
            ∘ unit_right⁻¹)).
  - (* Left whiskering into the middle form. *)
    rewrite (tensor_split_left ecompose).
    rewrite (tensor_split_right
               (etransform (EnrichedTransform := τ) y
                  ⨂ etransform (EnrichedTransform := σ) y)).
    rewrite <- !comp_assoc.
    rewrite ecompose_assoc_cons.
    rewrite <- to_assoc_nat_cons.
    rewrite bimap_fuse_cons.
    rewrite id_left.
    (* α ∘ ((λ_I⁻¹ ⨂ id) ∘ λ⁻¹) ≈ (id ⨂ λ⁻¹) ∘ λ⁻¹ *)
    rewrite unit_identity_from.
    rewrite triangle_inverse_middle_cons.
    rewrite bimap_fuse_cons.
    rewrite id_right.
    (* σ's enaturality, inside the second tensor slot *)
    rewrite (enaturality (EnrichedTransform := σ) (x:=x) (y:=y)).
    (* peel it back apart around the associator *)
    rewrite (tensor_split2_right (etransform (EnrichedTransform := τ) y)
               (ecompose ∘ (efmap (EnrichedFunctor := G) (x:=x) (y:=y)
                              ⨂ etransform (EnrichedTransform := σ) x))).
    rewrite (tensor_split2_left (etransform (EnrichedTransform := τ) y)
               ecompose).
    rewrite <- !comp_assoc.
    (* (id ⨂ ρ⁻¹) ∘ λ⁻¹ ≈ λ_{A⨂I}⁻¹ ∘ ρ⁻¹, then solve λ_{A⨂I}⁻¹ for α *)
    rewrite from_unit_left_natural.
    rewrite <- triangle_inverse_left.
    rewrite <- !comp_assoc.
    rewrite to_assoc_nat_cons.
    rewrite <- ecompose_assoc_cons.
    rewrite !bimap_fuse_cons.
    rewrite id_right, id_left.
    (* τ's enaturality, inside the first tensor slot *)
    rewrite (enaturality (EnrichedTransform := τ) (x:=x) (y:=y)).
    now rewrite <- !comp_assoc.
  - (* Right whiskering into the middle form: pure unitor bookkeeping. *)
    symmetry.
    rewrite (tensor_split2_left (efmap (EnrichedFunctor := J) (x:=x) (y:=y))
               ecompose).
    rewrite (tensor_split2_right (efmap (EnrichedFunctor := J) (x:=x) (y:=y))
               (etransform (EnrichedTransform := τ) x
                  ⨂ etransform (EnrichedTransform := σ) x)).
    rewrite <- !comp_assoc.
    (* (id ⨂ λ_I⁻¹) ∘ ρ⁻¹ ≈ (α ∘ (ρ⁻¹ ⨂ id)) ∘ ρ⁻¹ *)
    rewrite <- triangle_inverse_middle.
    rewrite <- !comp_assoc.
    rewrite to_assoc_nat_cons.
    rewrite <- ecompose_assoc_cons.
    rewrite !bimap_fuse_cons.
    rewrite id_right, id_left.
    now rewrite <- !comp_assoc.
Qed.

(** * The functor category [C, D]_V *)

Program Definition Enriched_Fun {K : Category} `{M : @Monoidal K}
        (C D : Enriched K) : Category := {|
  obj     := EnrichedFunctor K C D;
  hom     := fun F G => EnrichedTransform F G;
  homset  := fun F G => EnrichedTransform_Setoid F G;
  id      := fun F => EnrichedIdTransform F;
  compose := fun F G J τ σ => EnrichedTransform_vcompose τ σ
|}.
Next Obligation.
  (* compose respects the componentwise setoid *)
  intros K M C D F G J.
  proper.
  simpl.
  now rewrite (X x1), (X0 x1).
Qed.
Next Obligation.
  (* id_left, componentwise *)
  intros K M C D F G σ x.
  simpl.
  apply vertical_id_left.
Qed.
Next Obligation.
  (* id_right, componentwise *)
  intros K M C D F G σ x.
  simpl.
  apply vertical_id_right.
Qed.
Next Obligation.
  (* comp_assoc, componentwise *)
  intros K M C D F G J L τ σ υ x.
  simpl.
  apply vertical_assoc.
Qed.
Next Obligation.
  (* comp_assoc_sym, componentwise *)
  intros K M C D F G J L τ σ υ x.
  simpl.
  symmetry.
  apply vertical_assoc.
Qed.
