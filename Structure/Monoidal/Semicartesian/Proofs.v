Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

(* Derived equalities for the semicartesian (affine) monoidal structure: a
   monoidal category whose unit object I is terminal.  Terminality of I gives,
   for every object, a unique discard map `eliminate` x ~> I, and from it the
   two projections

       proj_left  = unit_right ∘ id ⨂ eliminate : x ⨂ y ~> x,
       proj_right = unit_left  ∘ eliminate ⨂ id : x ⨂ y ~> y.

   The lemmas below are the projection calculus that follows purely from this
   data, with no diagonal/copying assumed (that extra structure is what would
   make the category cartesian).  They split into three groups: the associator
   compatibilities proj_left_tensor_id / proj_right_tensor_id, the iterated
   projection equations proj_left_left / proj_right_right, and the projection
   naturality corollaries proj_left_natural / proj_right_natural.  Every step is
   discharged from the monoidal coherence axioms together with the terminality
   of I (used only through `eliminate` and `unit_terminal`/`eliminate_comp`).

   nLab:      https://ncatlab.org/nlab/show/semicartesian+monoidal+category
   Wikipedia: no dedicated article; the unit-terminal condition is noted under
              https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   These establish that the projection maps a semicartesian category carries are
   natural and associate coherently with the tensor, i.e. that x ⨂ y behaves
   like a (weak, non-universal) "product-with-discarding" already at the affine
   level, before any diagonal is added. *)

Section SemicartesianProofs.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

(* Associator compatibility of the left projection: projecting the left pair of
   a triple tensor and re-tensoring with id on the right agrees, across the
   associator (x ⨂ y) ⨂ z ~> x ⨂ (y ⨂ z), with discarding the inner z by the
   right projection on the right factor.  Both sides discard exactly z, so this
   is the triangle/associativity coherence of the discard map. *)
Lemma proj_left_tensor_id {x y z} :
  proj_left ⨂ id ≈ id[x] ⨂ @proj_right _ _ _ y z ∘ tensor_assoc.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_right.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal; reflexivity.
Qed.

(* The mirror image of proj_left_tensor_id: re-tensoring the right projection
   with id on the left agrees, across the inverse associator, with discarding
   the inner x by the left projection on the left factor.  Both sides discard
   exactly x. *)
Lemma proj_right_tensor_id {x y z} :
  id ⨂ proj_right ≈ @proj_left _ _ _ x y ⨂ id[z] ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_left.
  rewrite inverse_triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  normal; reflexivity.
Qed.

(* Iterated left projection: projecting (x ⨂ y) ⨂ z down to x ⨂ y and then to x
   is the same as re-associating to x ⨂ (y ⨂ z) and projecting straight onto x.
   Both routes discard y and z and keep x, so they agree; this is the
   associativity coherence between the projection and the associator. *)
Lemma proj_left_left {x y z} :
  proj_left ∘ proj_left ≈ @proj_left _ _ _ x (y ⨂ z) ∘ tensor_assoc.
Proof.
  unfold proj_left; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ unit_right).
  rewrite to_unit_right_natural; normal.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite bimap_triangle_right.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [reflexivity|].
  apply unit_terminal.
Qed.

(* The mirror image of proj_left_left: projecting x ⨂ (y ⨂ z) down to y ⨂ z and
   then to z equals re-associating to (x ⨂ y) ⨂ z and projecting straight onto
   z.  Both routes discard x and y and keep z. *)
Lemma proj_right_right {x y z} :
  proj_right ∘ proj_right ≈ @proj_right _ _ _ (x ⨂ y) z ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_right; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ unit_left).
  rewrite to_unit_left_natural; normal.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite bimap_triangle_left.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [|reflexivity].
  apply unit_terminal.
Qed.

(* Naturality of the left projection: projecting after acting by f ⨂ g equals
   acting by f after projecting.  The discarded g is killed by eliminate_comp
   (eliminate ∘ g ≈ eliminate, since I is terminal), leaving only f.  This is the
   naturality square of proj_left as a transformation (- ⨂ =) ⟹ pr1. *)
Corollary proj_left_natural {x y z w} (f : x ~> y) (g : z ~> w) :
  proj_left ∘ f ⨂ g ≈ f ∘ proj_left.
Proof.
  unfold proj_left.
  rewrite comp_assoc.
  rewrite to_unit_right_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

(* Naturality of the right projection, dual to proj_left_natural: the discarded
   f is killed by eliminate_comp, leaving only g.  This is the naturality square
   of proj_right as a transformation (- ⨂ =) ⟹ pr2. *)
Corollary proj_right_natural {x y z w} (f : x ~> y) (g : z ~> w) :
  proj_right ∘ f ⨂ g ≈ g ∘ proj_right.
Proof.
  unfold proj_right.
  rewrite comp_assoc.
  rewrite to_unit_left_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

End SemicartesianProofs.
