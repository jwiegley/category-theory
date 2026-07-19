Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.End.
Require Import Category.Structure.Coend.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Coend.
Require Import Category.Instance.Sets.End.

Generalizable All Variables.

(** Element-level readings of the functor laws for a [Sets]-valued functor,
    pinning the functor so [apply] discharges applied goals directly. *)
Local Lemma fmap_id_app {D : Category} (G : D ⟶ Sets) {x : D} (z : G x) :
  fmap[G] (@id D x) z ≈ z.
Proof. exact (@fmap_id D Sets G x z). Qed.

Local Lemma fmap_comp_app {D : Category} (G : D ⟶ Sets) {x y z : D}
  (g : y ~{D}~> z) (f : x ~{D}~> y) (w : G x) :
  fmap[G] (g ∘ f) w ≈ fmap[G] g (fmap[G] f w).
Proof. exact (@fmap_comp D Sets G x y z g f w). Qed.

(** * The ninja-Yoneda lemma in [Sets], both variances *)

(* nLab: https://ncatlab.org/nlab/show/co-Yoneda+lemma
   nLab: https://ncatlab.org/nlab/show/end#yoneda_reduction

   For a covariant functor [F : C ⟶ Sets] and an object [c : C] the Yoneda
   lemma has two dual "reduction" forms, computing a (co)end of a hom-weighted
   integrand back to [F c]:

     coend form (co-Yoneda) :   ∫^x  C(x,c) × F x   ≅   F c
       end form   (Yoneda)   :   ∫_x  [ C(c,x) , F x ]   ≅   F c

   Both are realised here concretely in [Sets] over the direct (co)end
   constructions of Instance/Sets/Coend and Instance/Sets/End, so both are
   [funext]-free and axiom-closed.

   Form 1 (this file's [coyoneda_reduction]).  The integrand
   [YoI : C^op ∏ C ⟶ Sets] sends [(x, y)] to the product setoid
   [C(x,c) × F y], contravariant in [x] by hom-precomposition and covariant in
   [y] by [fmap[F]].  The forward map is the coend mediator whose leg at [x]
   is [(g, a) ↦ fmap[F] g a] (co-dinaturality holds by [fmap_comp]); the
   inverse is [b ↦ ci c (id, b)].  One round trip is [fmap_id]; the other is a
   single application of the coend glue [ce_glue] (with [id]-law and [fmap_id]
   bookkeeping), witnessing that every generator [ci x (g, a)] is already
   identified with [ci c (id, fmap[F] g a)].

   Form 2 (this file's [yoneda_reduction]).  The integrand
   [YoE : C^op ∏ C ⟶ Sets] sends [(x, y)] to the exponential setoid
   [ [C(c,x) , F y] ] of setoid maps, contravariant in [x], covariant in [y];
   an element of [Sets_End YoE] is exactly a family [s x : C(c,x) → F x]
   satisfying the wedge (naturality) law, i.e. a natural transformation
   [C(c,-) ⟹ F].  The forward map evaluates at the identity, [s ↦ s c id];
   the inverse is [b ↦ (fun x g => fmap[F] g b)] (its wedge law holds by
   [fmap_comp]); the round trips use [fmap_id] and the family's own naturality.

   As with every Sets-valued (co)limit here the indexing category's object
   level is constrained below Sets' carrier level; these smallness constraints
   are inferred by universe polymorphism and recorded on the reductions. *)

Section Yoneda.

Context {C : Category}.
Context (F : C ⟶ Sets).
Context (c : C).

(** ** Form 1: co-Yoneda via the coend *)

(** The integrand [YoI (x, y) = C(x, c) × F y]: contravariant in [x] via
    hom-precomposition, covariant in [y] via [fmap[F]]. *)
Program Definition YoI : C^op ∏ C ⟶ Sets := {|
  fobj := fun p =>
    {| carrier   := (fst p ~{C}~> c) * F (snd p)
     ; is_setoid := @prod_setoid _ _ (@homset C (fst p) c) (is_setoid (F (snd p))) |};
  fmap := fun p q u =>
    {| morphism := fun ga => (fst ga ∘ fst u, fmap[F] (snd u) (snd ga)) |}
|}.
Next Obligation.
  unfold Proper, respectful; intros [g a] [g' a'] [Hg Ha]; split; simpl.
  - now rewrite Hg.
  - now rewrite Ha.
Qed.
Next Obligation.
  unfold Proper, respectful; intros u u' [Hu1 Hu2] [g a]; split; simpl.
  - now rewrite Hu1.
  - exact (@fmap_respects _ _ F _ _ (snd u) (snd u') Hu2 a).
Qed.
Next Obligation.
  split.
  - apply id_right.
  - apply fmap_id_app.
Qed.
Next Obligation.
  split.
  - apply comp_assoc.
  - apply fmap_comp_app.
Qed.

(** The coend leg at [x]: [(g, a) ↦ fmap[F] g a]. *)
Program Definition coy_leg (x : C) : SetoidMorphism (YoI (x, x)) (F c) := {|
  morphism := fun ga => fmap[F] (fst ga) (snd ga)
|}.
Next Obligation.
  unfold Proper, respectful; intros [g a] [g' a'] [Hg Ha]; simpl.
  transitivity (fmap[F] g a').
  - exact (proper_morphism (fmap[F] g) a a' Ha).
  - exact (@fmap_respects _ _ F _ _ g g' Hg a').
Qed.

(** Co-dinaturality of the legs: the cowedge condition, holding by
    [fmap_comp] plus [fmap_id] and identity laws. *)
Lemma coy_cowedge : Cowedge_cond YoI (F c) coy_leg.
Proof.
  intros x y f [g a]; simpl.
  transitivity (fmap[F] (g ∘ f) a).
  - apply proper_morphism.
    apply fmap_id_app.
  - transitivity (fmap[F] g (fmap[F] f a)).
    + apply fmap_comp_app.
    + symmetry.
      exact (@fmap_respects _ _ F _ _ (g ∘ id) g (id_right g) (fmap[F] f a)).
Qed.

(** Forward map: the coend mediator. *)
Definition coy_to : SetoidMorphism (coend_apex_setoid YoI) (F c) :=
  coend_mediator YoI coy_leg coy_cowedge.

(** Inverse map: [b ↦ ci c (id, b)]. *)
Program Definition coy_from : SetoidMorphism (F c) (coend_apex_setoid YoI) := {|
  morphism := fun b => ci YoI c (id, b)
|}.
Next Obligation.
  proper.
  apply ce_point; split; simpl.
  - reflexivity.
  - assumption.
Qed.

(** The co-Yoneda isomorphism on the coend apex. *)
Program Definition coyoneda_iso :
  @Isomorphism Sets (coend_apex_setoid YoI) (F c) := {|
  to   := coy_to;
  from := coy_from
|}.
Next Obligation.
  apply fmap_id_app.
Qed.
Next Obligation.
  destruct x as [x0 [g a]].
  (* coend glue: ci c (id, fmap[F] g a) ≈ ci x0 (g, a), oriented via ce_sym *)
  apply ce_sym.
  apply (ce_trans YoI (ci YoI x0 (g, a))
                      (ci YoI x0 (id ∘ g, fmap[F] id a))
                      (ci YoI c (id, fmap[F] g a))).
  - apply ce_point; split.
    + now rewrite id_left.
    + symmetry; apply fmap_id_app.
  - apply (ce_trans YoI (ci YoI x0 (id ∘ g, fmap[F] id a))
                        (ci YoI c (id ∘ id, fmap[F] g a))
                        (ci YoI c (id, fmap[F] g a))).
    + exact (ce_glue YoI x0 c g (id, a)).
    + apply ce_point; split.
      * now rewrite id_right.
      * reflexivity.
Qed.

(** The primary Form-1 deliverable, stated over the packaged coend. *)
Definition coyoneda_reduction : coend_obj (SetsCoend YoI) ≅[Sets] F c :=
  coyoneda_iso.

(** ** Form 2: Yoneda via the end *)

(** [C(c, x)] as a [SetoidObject], the exponent's domain. *)
Let homc (x : C) : SetoidObject :=
  {| carrier := c ~{C}~> x; is_setoid := @homset C c x |}.

(** The integrand [YoE (x, y) = [C(c, x), F y]]: contravariant in [x] by
    hom-precomposition of the exponent's domain, covariant in [y] via
    [fmap[F]]. *)
Program Definition YoE : C^op ∏ C ⟶ Sets := {|
  fobj := fun p =>
    {| carrier   := SetoidMorphism (homc (fst p)) (F (snd p))
     ; is_setoid := @SetoidMorphism_Setoid (homc (fst p)) (F (snd p)) |};
  fmap := fun p q u =>
    {| morphism := fun phi =>
         {| morphism := fun k =>
              fmap[F] (snd u) (phi ((fst u : fst q ~{C}~> fst p) ∘ k)) |} |}
|}.
Next Obligation.
  unfold Proper, respectful; intros k k' Hk.
  apply proper_morphism; apply proper_morphism; now rewrite Hk.
Qed.
Next Obligation.
  unfold Proper, respectful; intros phi phi' Hphi k; simpl.
  apply proper_morphism; apply Hphi.
Qed.
Next Obligation.
  unfold Proper, respectful; intros [u1 u2] [u1' u2'] [Hu1 Hu2] phi k; simpl.
  transitivity (fmap[F] u2 (phi (u1' ∘ k))).
  - apply proper_morphism; apply proper_morphism; now rewrite Hu1.
  - exact (@fmap_respects _ _ F _ _ u2 u2' Hu2 (phi (u1' ∘ k))).
Qed.
Next Obligation.
  transitivity (fmap[F] id (x0 x1)).
  - apply proper_morphism; apply proper_morphism; now rewrite id_left.
  - apply fmap_id_app.
Qed.
Next Obligation.
  transitivity (fmap[F] h2 (fmap[F] h0 (x0 (h ∘ h1 ∘ x1)))).
  - apply fmap_comp_app.
  - apply proper_morphism; apply proper_morphism; apply proper_morphism.
    now rewrite comp_assoc.
Qed.

(** An element of [Sets_End YoE] is a family [s x : C(c,x) → F x] satisfying
    the wedge law: exactly a natural transformation [C(c,-) ⟹ F]. We build
    the two setoid maps directly and prove the round trips. The pristine
    obligation regime keeps each obligation goal unsimplified, so the intro
    structure of the wedge and round-trip proofs is stated explicitly. *)
#[local] Obligation Tactic := idtac.

(** Forward map: evaluate the family at [c] on the identity, [s ↦ (s c) id]. *)
Program Definition ye_to : SetoidMorphism (Sets_End_obj YoE) (F c) := {|
  morphism := fun s => `1 s c id
|}.
Next Obligation.
  unfold Proper, respectful; intros s t Hst.
  exact (Hst c id).
Qed.

(** The component at [x] of the inverse's natural family: [k ↦ fmap[F] k b],
    the image of [b : F c] under the Yoneda embedding [C(c,-) ⟹ F]. *)
Program Definition ye_from_fam (b : F c) (x : C) :
  SetoidMorphism (homc x) (F x) := {|
  morphism := fun k => fmap[F] k b
|}.
Next Obligation.
  unfold Proper, respectful; intros b x k k' Hk.
  exact (@fmap_respects _ _ F _ _ k k' Hk b).
Qed.

(** The inverse's image assembled into a compatible family; its wedge law is
    the naturality of [k ↦ fmap[F] k b], holding by [fmap_comp] and [fmap_id]. *)
Program Definition ye_from_family (b : F c) : end_family YoE :=
  (fun x => ye_from_fam b x; _).
Next Obligation.
  intros b x y f k.
  change (fmap[F] f (fmap[F] (id ∘ k) b) ≈ fmap[F] id (fmap[F] (f ∘ k) b)).
  transitivity (fmap[F] (f ∘ k) b).
  - transitivity (fmap[F] f (fmap[F] k b)).
    + apply proper_morphism.
      exact (@fmap_respects _ _ F _ _ (id ∘ k) k (id_left k) b).
    + symmetry; exact (fmap_comp_app F f k b).
  - symmetry; exact (fmap_id_app F (fmap[F] (f ∘ k) b)).
Qed.

(** Inverse map: [b ↦ (fun x k => fmap[F] k b)]. *)
Program Definition ye_from : SetoidMorphism (F c) (Sets_End_obj YoE) := {|
  morphism := ye_from_family
|}.
Next Obligation.
  unfold Proper, respectful; intros b b' Hbb' x k.
  exact (proper_morphism (fmap[F] k) b b' Hbb').
Qed.

(** The Yoneda isomorphism on the end apex. *)
Program Definition yoneda_iso :
  @Isomorphism Sets (Sets_End_obj YoE) (F c) := {|
  to   := ye_to;
  from := ye_from
|}.
Next Obligation.
  intro b.
  change (fmap[F] id b ≈ b).
  apply fmap_id_app.
Qed.
Next Obligation.
  intros s x k.
  change (fmap[F] k (`1 s c id) ≈ `1 s x k).
  transitivity (fmap[F] k (`1 s c (id ∘ id))).
  - apply proper_morphism; apply proper_morphism; now rewrite id_left.
  - transitivity (fmap[F] id (`1 s x (k ∘ id))).
    + exact (`2 s c x k id).
    + transitivity (fmap[F] id (`1 s x k)).
      * apply proper_morphism; apply proper_morphism; now rewrite id_right.
      * apply fmap_id_app.
Qed.

(** The primary Form-2 deliverable, stated over the concrete end object;
    [Sets_End YoE : End YoE] carries this setoid as its apex. *)
Definition yoneda_reduction : Sets_End_obj YoE ≅[Sets] F c :=
  yoneda_iso.

End Yoneda.
