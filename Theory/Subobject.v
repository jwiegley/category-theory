Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/subobject

   A subobject of an object x is (an equivalence class of) a monomorphism
   into x. Here the setoid structure itself carries the quotient: two monos
   into x are equivalent when there is an isomorphism of their domains
   commuting with them over x. *)

Record SubObj {C : Category} (x : C) := {
  sub_dom : C;                     (* the domain of the mono *)
  sub_mono : sub_dom ~> x;         (* the mono into x *)
  sub_is_monic : Monic sub_mono
}.

Arguments sub_dom {C x} _.
Arguments sub_mono {C x} _.
Arguments sub_is_monic {C x} _.

#[export] Existing Instance sub_is_monic.

Section Subobject.

Universes o h p.
Context {C : Category@{o h p}}.
Context {x : C}.

#[export] Program Instance SubObj_Setoid : Setoid (SubObj x) := {
  equiv := fun u v =>
    { i : sub_dom u ≅ sub_dom v & sub_mono v ∘ to i ≈ sub_mono u }
}.
Next Obligation.
  constructor.
  - (* reflexivity: the identity isomorphism *)
    intros u.
    exists iso_id; cat.
  - (* symmetry: the inverse triangle follows by precomposing with from i *)
    intros u v [i Hi].
    exists (iso_sym i); simpl.
    rewrite <- Hi.
    rewrite <- comp_assoc.
    rewrite iso_to_from; cat.
  - (* transitivity: compose the isomorphisms *)
    intros u v w [i Hi] [j Hj].
    exists (iso_compose j i); simpl.
    rewrite comp_assoc.
    now rewrite Hj.
Qed.

(* The preorder on subobjects: u ≤ v when the mono of u factors through the
   mono of v. The factorization is automatically monic-through, and unique
   (sub_le_unique below), so this is a genuine preorder whose induced
   equivalence is exactly the setoid equivalence above. *)
Definition sub_le (u v : SubObj x) : Type :=
  { k : sub_dom u ~> sub_dom v & sub_mono v ∘ k ≈ sub_mono u }.

Lemma sub_le_refl (u : SubObj x) : sub_le u u.
Proof.
  exists id; cat.
Defined.

Lemma sub_le_trans (u v w : SubObj x) :
  sub_le u v → sub_le v w → sub_le u w.
Proof.
  intros [k Hk] [l Hl].
  exists (l ∘ k).
  rewrite comp_assoc.
  now rewrite Hl.
Defined.

(* Mediating morphisms are unique: any two factorizations of sub_mono u
   through sub_mono v agree, by monicity of sub_mono v. *)
Lemma sub_le_unique (u v : SubObj x) (k k' : sub_dom u ~> sub_dom v) :
  sub_mono v ∘ k ≈ sub_mono u →
  sub_mono v ∘ k' ≈ sub_mono u →
  k ≈ k'.
Proof.
  intros Hk Hk'.
  apply (monic (Monic:=sub_is_monic v)).
  now rewrite Hk, Hk'.
Qed.

(* Two subobjects are equivalent exactly when each factors through the other:
   the isomorphism supplies both factorizations, and conversely mutual
   factorizations k, l compose to endomorphisms over the same mono, hence to
   the identity by monicity, assembling an isomorphism of domains. Ends in
   Defined because both directions transport data. *)
Theorem sub_equiv_iff_mutual (u v : SubObj x) :
  (u ≈ v) ↔ (sub_le u v * sub_le v u).
Proof.
  split.
  - (* forward: to/from of the domain isomorphism are the factorizations *)
    intros [i Hi].
    split.
    + exists (to i); exact Hi.
    + exists (from i).
      rewrite <- Hi.
      rewrite <- comp_assoc.
      rewrite iso_to_from; cat.
  - (* backward: the round trips are id by monicity *)
    intros [[k Hk] [l Hl]].
    unshelve eexists {| to := k; from := l |}; simpl.
    + (* k ∘ l ≈ id, by monicity of sub_mono v *)
      apply (monic (Monic:=sub_is_monic v)).
      rewrite comp_assoc, Hk, Hl; cat.
    + (* l ∘ k ≈ id, by monicity of sub_mono u *)
      apply (monic (Monic:=sub_is_monic u)).
      rewrite comp_assoc, Hl, Hk; cat.
    + exact Hk.
Defined.

End Subobject.
