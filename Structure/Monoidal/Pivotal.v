Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Braided.
(* Require Export Category.Structure.Monoidal.Rigid. *)
Require Export Category.Structure.Monoidal.Naturality.

Generalizable All Variables.

Section PivotalMonoidal.

Context {C : Category}.
Context `{@BraidedMonoidal C}.

(* A simple pivotal structure without worrying about rigid constraints *)
Class PivotalMonoidal := {
  (* The twist endomorphism for each object - the key feature of pivotal categories *)
  twist {x} : x ~> x;
  
  (* The twist is natural *)
  twist_natural {x y} (f : x ~> y) :
    twist ∘ f ≈ f ∘ twist;
    
  (* The twist respects the monoidal structure *)
  twist_monoidal {x y} :
    @twist (x ⨂ y) ≈ (@twist x ⨂ @twist y) ∘ braid ∘ braid;
    
  (* The twist on the unit object *)
  twist_unit : @twist I ≈ id[I];
  
  (* The twist is involutive (spherical condition) *)
  twist_involutive {x} : twist ∘ twist ≈ id[x];
}.

Context `{@PivotalMonoidal}.

(* Alternative characterizations of the twist *)
Definition double_braid {x y} : x ⨂ y ~> x ⨂ y := @braid _ _ y x ∘ @braid _ _ x y.

(* Basic properties of the twist *)
Lemma twist_idempotent {x} : twist ∘ twist ≈ id[x].
Proof.
  (* This follows directly from the twist_involutive axiom *)
  apply twist_involutive.
Qed.

Lemma double_braid_twist {x y} :
  @twist (x ⨂ y) ≈ double_braid ∘ (@twist x ⨂ @twist y).
Proof.
  (* The twist is related to double braiding.
     Key insight: twist_monoidal gives us (@twist x ⨂ @twist y) ∘ braid ∘ braid,
     and we need to commute the twists to get double_braid ∘ (@twist x ⨂ @twist y).
     This uses the naturality of braid twice. *)
  unfold double_braid.
  (* Start from the twist_monoidal axiom *)
  rewrite twist_monoidal.
  (* We have: (@twist x ⨂ @twist y) ∘ braid ∘ braid *)
  (* We want: (@braid _ _ y x ∘ @braid _ _ x y) ∘ (@twist x ⨂ @twist y) *)
  
  (* The key is to show that the two braids can commute past the twists *)
  (* Use naturality: braid ∘ (f ⨂ g) ≈ (g ⨂ f) ∘ braid *)
  
  (* First, move twists past the rightmost braid *)
  rewrite <- comp_assoc.
  rewrite (@braid_natural _ _ x y x y (@twist x) (@twist y)).
  
  (* Now move the swapped twists past the leftmost braid *)  
  rewrite comp_assoc.
  rewrite (@braid_natural _ _ y x y x (@twist y) (@twist x)).
  
  (* Now we have the desired form *)
  rewrite comp_assoc.
  reflexivity.
Qed.

(* Compatibility with the braiding *)
Lemma twist_braid_commute {x y} :
  braid ∘ (@twist x ⨂ @twist y) ≈ (@twist y ⨂ @twist x) ∘ braid.
Proof.
  (* The twist commutes with braiding when applied tensorwise *)
  (* This follows from naturality of braid with respect to twist *)
  pose proof (@braid_natural _ _ x y x y (@twist x) (@twist y)) as H.
  exact H.
Qed.

End PivotalMonoidal.

Notation "θ" := twist (at level 30) : morphism_scope.