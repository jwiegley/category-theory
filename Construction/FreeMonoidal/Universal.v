Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Construction.Product.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.FreeMonoidal.
Require Import Category.Construction.FreeMonoidal.Normal.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Theorem 1: W is the free monoidal category on one generator

    Mac Lane, CWM 2nd ed., §VII.2, Theorem 1 [maclane:VII.2:thm1]: for any
    monoidal category [B] and object [b : B] there is a unique morphism
    [W ⟶ B] of monoidal categories carrying the generator to [b] — namely
    substitution of [b] into all blanks.

    THE MORPHISM NOTION IS STRICT, and that is Mac Lane's own reading, not a
    weakening: his Moncat (§VII.1, [maclane:VII.1:construction2]) is "the
    category of all small monoidal categories with STRICT morphisms as
    arrows", and a strict morphism ([maclane:VII.1:def3]) carries α, λ, ρ to
    α', λ', ρ' on the nose.  Uniqueness among merely strong monoidal functors
    is false — any conjugate of [Subst] by a nonidentity natural isomorphism
    is again strong monoidal and sends the generator to an isomorph of [b] —
    so the strict reading is the only one under which Theorem 1 can hold.
    Existence is nevertheless delivered at BOTH strengths below:
    [Subst_Monoidal] (strong) and [Subst_Strict] (strict, with both object
    equations [eq_refl] on the nose).

    What is deliberately NOT delivered here, and where it is recorded:
    uniqueness up to monoidal natural isomorphism among STRONG monoidal
    functors.  The library has no monoidal-natural-transformation class for
    strong functors (Theory/Natural/Transformation/Monoidal.v states
    [LaxMonoidal_Transform] for lax functors only), so that statement has no
    home; it is ledgered in doc/classical-completion-plan.md rather than
    approximated. *)

Section Universal.

Context {B : Category}.
Context `{MB : @Monoidal B}.
Context (b : B).

(** ** The substitution functor *)

(* On objects, [subst b]; on the unique arrow [p : wlen v = wlen w],
   normalise, transport along [p], denormalise. *)
Program Definition Subst : W ⟶ B := {|
  fobj := subst b;
  fmap := fun v w (p : v ~{W}~> w) =>
    from (can b w)
      ∘ id_cast (f_equal (fun i => nf b i I) p)
      ∘ to (can b v)
|}.
Next Obligation.
  (* fmap_respects: W's hom-setoid identifies ALL parallel arrows, so the
     cast must not depend on the proof — nat-UIP, the only place it is
     needed for functoriality. *)
  proper.
  apply compose_respects; [| reflexivity ].
  apply compose_respects; [ reflexivity |].
  apply nf_cast_irr.
Qed.
Next Obligation.
  (* fmap_id: the cast at eq_refl is the identity by conversion. *)
  rewrite id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  (* fmap_comp: cancel the inner normalise/denormalise pair, fuse casts. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (can b y))).
  rewrite iso_to_from, id_left.
  rewrite (comp_assoc (id_cast _)).
  rewrite nf_cast_trans.
  reflexivity.
Qed.

(** ** The tensor comparison *)

(* Mac Lane's T(f □ g) = Tf □' Tg. *)
Theorem Subst_tensor {v v' u u' : Word}
  (p : v ~{W}~> v') (q : u ~{W}~> u') :
  fmap[Subst] (fmap[W_tensor] ((p, q) : (v, u) ~{W ∏ W}~> (v', u')))
    ≈ bimap (fmap[Subst] p) (fmap[Subst] q).
Proof.
  simpl.
  (* Peel the join off the cast with [J_cast], then cancel it against its
     inverse; the residue is the bimap of the two component fmaps. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (id_cast _) (to (J b (wlen v) (wlen u) I))).
  rewrite (J_cast b p q).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (J b (wlen v') (wlen u') I))
                      (to (J b (wlen v') (wlen u') I))).
  rewrite iso_from_to, id_left.
  normal.
  reflexivity.
Qed.

(* From here on the goals are monoidal-coherence shaped, and the global
   [cat_simpl] obligation tactic pre-processes them unpredictably; take manual
   control instead (precedent: Functor/Structure/Monoidal/Id.v). *)
#[local] Obligation Tactic := idtac.

(* The comparison natural isomorphism has identity components: [subst] is
   strict on objects, so the two composite functors agree definitionally on
   objects and the comparison square is [Subst_tensor]. *)
Program Definition Subst_ap_to :
  ((⨂) ◯ Subst ∏⟶ Subst) ~{[W ∏ W, B]}~> (Subst ◯ (⨂)) := {|
  transform := fun _ => id
|}.
Next Obligation.
  intros [v u] [v' u'] [p q]; simpl.
  rewrite id_left, id_right.
  first [ exact (@Subst_tensor v v' u u' p q)
        | symmetry; exact (@Subst_tensor v v' u u' p q) ].
Qed.
Next Obligation.
  intros [v u] [v' u'] [p q]; simpl.
  rewrite id_left, id_right.
  first [ exact (@Subst_tensor v v' u u' p q)
        | symmetry; exact (@Subst_tensor v v' u u' p q) ].
Qed.

Program Definition Subst_ap_from :
  (Subst ◯ (⨂)) ~{[W ∏ W, B]}~> ((⨂) ◯ Subst ∏⟶ Subst) := {|
  transform := fun _ => id
|}.
Next Obligation.
  intros [v u] [v' u'] [p q]; simpl.
  rewrite id_left, id_right.
  first [ exact (@Subst_tensor v v' u u' p q)
        | symmetry; exact (@Subst_tensor v v' u u' p q) ].
Qed.
Next Obligation.
  intros [v u] [v' u'] [p q]; simpl.
  rewrite id_left, id_right.
  first [ exact (@Subst_tensor v v' u u' p q)
        | symmetry; exact (@Subst_tensor v v' u u' p q) ].
Qed.

Program Definition Subst_ap :
  ((⨂) ◯ Subst ∏⟶ Subst) ≅[[W ∏ W, B]] (Subst ◯ (⨂)) := {|
  to   := Subst_ap_to;
  from := Subst_ap_from
|}.
Next Obligation.
  intros [v u]; simpl; cat.
  symmetry.
  rewrite nf_cast_loop, id_right.
  rewrite <- (comp_assoc _ (from (J b (wlen v) (wlen u) I))).
  rewrite (comp_assoc (from (J b (wlen v) (wlen u) I))
             (to (J b (wlen v) (wlen u) I))).
  rewrite iso_from_to, id_left.
  normal.
  rewrite !iso_from_to.
  normal.
  reflexivity.
Qed.
Next Obligation.
  intros [v u]; simpl; cat.
  symmetry.
  etransitivity; [| apply bimap_id_id ].
  apply fmap_respects.
  split; apply iso_from_to.
Qed.

(** ** The three strictness equations

    Stated standalone so the coherence corollary (#497) can consume them. *)

Theorem Subst_unit_left (x : Word) :
  fmap[Subst] (to (@unit_left W W_Monoidal x))
    ≈ to (@unit_left B MB (subst b x)).
Proof.
  simpl.
  rewrite id_right.
  rewrite <- (to_unit_left_natural (to (can b x))).
  rewrite comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.

Theorem Subst_unit_right (x : Word) :
  fmap[Subst] (to (@unit_right W W_Monoidal x))
    ≈ to (@unit_right B MB (subst b x)).
Proof.
  simpl.
  (* Group the cast against the join; that pair is exactly [J_right_unit]. *)
  rewrite comp_assoc.
  rewrite <- (comp_assoc (from (can b x))).
  rewrite (J_right_unit b (wlen x)).
  rewrite <- (comp_assoc (from (can b x))).
  rewrite <- (to_unit_right_natural (to (can b x))).
  rewrite comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.

Theorem Subst_assoc (x y z : Word) :
  fmap[Subst] (to (@tensor_assoc W W_Monoidal x y z))
    ≈ to (@tensor_assoc B MB (subst b x) (subst b y) (subst b z)).
Proof.
  simpl.
  (* Read J_assoc across the eq_sym cast first: composing both sides of
     [J_assoc] with the loop kills its cast. *)
  assert (JA' :
    id_cast (f_equal (fun i => nf b i I)
               (eq_sym (Nat.add_assoc (wlen x) (wlen y) (wlen z))))
      ∘ to (J b (wlen x + wlen y) (wlen z) I)
      ∘ bimap (to (J b (wlen x) (wlen y) I)) id
      ≈ to (J b (wlen x) (wlen y + wlen z) I)
          ∘ bimap id (to (J b (wlen y) (wlen z) I))
          ∘ to tensor_assoc).
  { rewrite <- comp_assoc.
    rewrite (J_assoc b (wlen x) (wlen y) (wlen z) I).
    rewrite !comp_assoc.
    rewrite nf_cast_trans.
    rewrite nf_cast_loop, id_left.
    reflexivity. }
  (* Assemble the left side into cast-join-components form and fire JA'. *)
  rewrite comp_assoc.
  rewrite <- (comp_assoc _ (id_cast _)
                (to (J b (wlen x + wlen y) (wlen z) I))).
  rewrite <- (id_left (to (can b z))) at 1.
  rewrite bimap_comp.
  rewrite (comp_assoc _ (bimap (to (J b (wlen x) (wlen y) I)) id)
             (bimap (bimap (to (can b x)) (to (can b y))) (to (can b z)))).
  rewrite <- (comp_assoc _
                (id_cast _ ∘ to (J b (wlen x + wlen y) (wlen z) I))
                (bimap (to (J b (wlen x) (wlen y) I)) id)).
  rewrite JA'.
  (* Cancel the outer join pair, carry α across the components, and let the
     remaining conjugates cancel. *)
  rewrite <- (comp_assoc _ (from (J b (wlen x) (wlen y + wlen z) I))).
  rewrite (comp_assoc (from (J b (wlen x) (wlen y + wlen z) I))
             (to (J b (wlen x) (wlen y + wlen z) I)
                ∘ bimap id (to (J b (wlen y) (wlen z) I)))
             (to tensor_assoc)).
  rewrite (comp_assoc (from (J b (wlen x) (wlen y + wlen z) I))
             (to (J b (wlen x) (wlen y + wlen z) I))).
  rewrite iso_from_to, id_left.
  rewrite <- (comp_assoc _
                (bimap id (to (J b (wlen y) (wlen z) I)) ∘ to tensor_assoc)).
  rewrite <- (comp_assoc (bimap id (to (J b (wlen y) (wlen z) I)))
                (to tensor_assoc)).
  rewrite <- (to_tensor_assoc_natural
                (to (can b x)) (to (can b y)) (to (can b z))).
  normal.
  (* The residue is [bimap id CONJ ∘ α ≈ α] with CONJ a conjugate of the
     y/z-join by its inverse; close by congruence so the argument does not
     depend on how [normal] grouped the composite. *)
  etransitivity; [| apply id_left ].
  apply compose_respects; [| reflexivity ].
  etransitivity; [| apply bimap_id_id ].
  apply fmap_respects; split; simpl.
  - apply iso_from_to.
  - rewrite <- !comp_assoc.
    rewrite (comp_assoc (from (J b (wlen y) (wlen z) I))
                        (to (J b (wlen y) (wlen z) I))).
    rewrite iso_from_to, id_left.
    normal.
    rewrite ?iso_from_to.
    normal.
    reflexivity.
Qed.

(** ** The strong and strict monoidal packagings *)

Program Definition Subst_Monoidal :
  @MonoidalFunctor W B W_Monoidal MB Subst := {|
  pure_iso       := iso_id;
  ap_functor_iso := Subst_ap;
  pure_iso_left  := fun x => iso_id;
  pure_iso_right := fun x => iso_id;
  ap_iso_assoc   := fun x y z => tensor_assoc
|}.
Next Obligation.
  intros x; simpl.
  normal.
  rewrite ?id_left, ?id_right.
  symmetry.
  rewrite <- comp_assoc.
  rewrite <- (to_unit_left_natural (to (can b x))).
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.
Next Obligation.
  intros x; simpl.
  normal.
  rewrite ?id_left, ?id_right.
  symmetry.
  rewrite <- (comp_assoc (from (can b x)) (id_cast _)
                (to (J b (wlen x) 0 I))).
  rewrite (J_right_unit b (wlen x)).
  rewrite <- comp_assoc.
  rewrite <- (to_unit_right_natural (to (can b x))).
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.
Next Obligation.
  intros x y z; simpl.
  normal.
  rewrite ?id_left, ?id_right.
  (* [normal] left-associated one node further than [fmap]'s definitional
     grouping; put it back and the goal IS [Subst_assoc], by conversion. *)
  rewrite <- (comp_assoc _ (to (J b (wlen x + wlen y) (wlen z) I))
                (bimap (to (J b (wlen x) (wlen y) I)
                          ∘ bimap (to (can b x)) (to (can b y)))
                       (to (can b z)))).
  exact (Subst_assoc x y z).
Qed.

Program Definition Subst_Strict :
  @StrictMonoidalFunctor W B W_Monoidal MB Subst := {|
  strict_functor_is_monoidal := Subst_Monoidal;
  strict_pure_obj := eq_refl;
  strict_ap_obj   := fun _ _ => eq_refl
|}.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. intros x y; simpl; reflexivity. Qed.

(** ** Acceptance tests *)

(* The generator condition, definitionally. *)
Example Subst_generator : Subst WI = b := eq_refl.

(* Strictness on the nose: both object equalities of [Subst_Strict] are
   literally [eq_refl], stronger than the class demands. *)
Example Subst_strict_pure_on_the_nose :
  @strict_pure_obj W B W_Monoidal MB Subst Subst_Strict = eq_refl := eq_refl.
Example Subst_strict_ap_on_the_nose (x y : Word) :
  @strict_ap_obj W B W_Monoidal MB Subst Subst_Strict x y = eq_refl := eq_refl.

(* The associator instance at length 3, and the unitors at length 1. *)
Corollary Subst_assoc_words :
  fmap[Subst] (to (@tensor_assoc W W_Monoidal WI WI WI))
    ≈ to (@tensor_assoc B MB b b b).
Proof. apply Subst_assoc. Qed.

Corollary Subst_unit_left_word :
  fmap[Subst] (to (@unit_left W W_Monoidal WI))
    ≈ to (@unit_left B MB b).
Proof. apply Subst_unit_left. Qed.

Corollary Subst_unit_right_word :
  fmap[Subst] (to (@unit_right W W_Monoidal WI))
    ≈ to (@unit_right B MB b).
Proof. apply Subst_unit_right. Qed.

End Universal.
