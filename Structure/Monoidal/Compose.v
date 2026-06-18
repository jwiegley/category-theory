Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Fun.

Generalizable All Variables.

#[local] Obligation Tactic := intros; simplify; simpl in *; intros; normal.

(* nLab: https://ncatlab.org/nlab/show/endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   The endofunctor category [C, C] is monoidal, with functor composition ◯ as
   the tensor product and the identity functor Id as the unit object:

       F ⨂ G := F ◯ G            (tensor on objects, [tensor.fobj]),
       I     := Id               (unit object).

   On morphisms the tensor is the horizontal (Godement) composite of natural
   transformations: for N = (fst N, snd N) with fst N : fst F ⟹ fst G and
   snd N : snd F ⟹ snd G, the component at x is

       (fst N) (snd G x) ∘ fmap[fst F] (snd N x)   ([tensor.fmap]),

   the standard interchange formula α(G' x) ∘ F(β x).

   This reflects the fact that categories are themselves "monoidoids", or
   monoidal with respect to identity and composition; it is also the structure
   behind "a monad is a monoid in the category of endofunctors".

   In the literature this monoidal structure is strict: the associator and the
   two unitors are identity natural transformations, since F ◯ (G ◯ H) and
   (F ◯ G) ◯ H, and Id ◯ F and F ◯ Id, are equal on the nose. Here it is
   nonetheless presented as a general (non-strict) Monoidal instance whose
   unitors and associator are component-wise identity isomorphisms, which is
   why the associator/unitor and coherence obligations still appear below. *)

Program Definition Compose_Monoidal {C : Category} :
  @Monoidal ([C, C]) := {|
  tensor :=
    {| fobj := fun p => fst p ◯ snd p
     ; fmap := fun F G N =>
         {| transform := fun x =>
              fst N (snd G x) ∘ fmap[fst F] (snd N x) |}
     |};
  I := Id
|}.
Next Obligation.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (naturality[snd N]).
  rewrite fmap_comp.
  comp_left.
  apply naturality.
Qed.
Next Obligation.
  rewrite naturality.
  rewrite <- !comp_assoc.
  comp_left.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  apply naturality_sym.
Qed.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. rewrite !fmap_id; cat. Qed.
Next Obligation.
  rewrite <- !comp_assoc.
  apply compose_respects.
  - reflexivity.
  - rewrite <- !naturality.
    rewrite fmap_comp.
    rewrite comp_assoc.
    reflexivity.
Qed.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation.
  rewrite !fmap_id.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  rewrite !fmap_id.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  normal; reflexivity.
Qed.
Next Obligation.
  normal; rewrite !fmap_id; reflexivity.
Qed.
