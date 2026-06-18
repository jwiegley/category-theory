Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Product.
Require Import Category.Functor.Strong.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Semicartesian.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Proofs.

Generalizable All Variables.

(** Strength of a pointwise product of strong functors *)

(* nLab: https://ncatlab.org/nlab/show/tensorial+strength
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   In a cartesian monoidal category (tensor = product, unit = terminal) the
   pointwise product functor F :*: G : x ↦ F x ⨂ G x (see Functor/Product.v)
   inherits a tensorial strength from strengths on F and on G.  Writing
   strength[F], strength[G] for the two given left strengths and using the
   copying diagonal ∆ together with the projections proj_left, proj_right of
   the cartesian structure, the product strength is

     strength[F:*:G][x,y]
       : x ⨂ (F y ⨂ G y) ~> F (x ⨂ y) ⨂ G (x ⨂ y)
       = (strength[F] ∘ id ⨂ proj_left) ⨂ (strength[G] ∘ id ⨂ proj_right)
           ∘ ∆(x ⨂ F y ⨂ G y).

   Operationally: copy the input pair, on one copy keep x and the F-summand
   (id ⨂ proj_left) then slide x inside F via strength[F], on the other copy
   keep x and the G-summand (id ⨂ proj_right) then slide x inside G via
   strength[G], and pair the results.  This construction genuinely uses the
   cartesian assumption: the diagonal ∆ (copying x so it can be fed to both
   factors) and the projections are only available because ⨂ is the product.
   The two obligations discharge Kock's unit law ([strength_id_left]) and
   associativity law ([strength_assoc]) for the resulting strength; the
   leading obligation discharges naturality in both arguments. *)

Section ProductStrong.

Context `{@CartesianMonoidal C}.
Context {F : C ⟶ C}.
Context {G : C ⟶ C}.

#[local] Obligation Tactic := simpl; intros.

Program Definition Product_Strong :
  StrongFunctor F → StrongFunctor G → StrongFunctor (F :*: G) := fun O P => {|
  strength := fun x y =>
    (strength ∘ id ⨂ proj_left) ⨂ (strength ∘ id ⨂ proj_right)
      ∘ ∆(x ⨂ F y ⨂ G y);
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  pose proof (@strength_natural _ _ _ O _ _ g _ _ h) as X0.
  pose proof (@strength_natural _ _ _ P _ _ g _ _ h) as X1.
  simpl in *; normal.
  rewrites.

  normal.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  unfold proj_left, proj_right.
  normal.
  rewrite to_unit_left_natural.
  rewrite to_unit_right_natural.
  normal.
  rewrite <- !comp_assoc.
  srewrite_r diagonal_natural.
  normal.
  rewrite !eliminate_comp.
  reflexivity.
Qed.
Next Obligation.
  pose proof (@strength_id_left _ _ _ O) as X0.
  pose proof (@strength_id_left _ _ _ P) as X1.
  normal.
  rewrite X0, X1; clear X0 X1.

  rewrite <- !to_unit_left_natural.
  rewrite bimap_comp.
  rewrite <- comp_assoc.
  srewrite diagonal_natural.
  rewrite comp_assoc.
  rewrite proj_left_right_diagonal; cat.
Qed.
Next Obligation.
  pose proof (@strength_assoc _ _ _ O) as X0.
  pose proof (@strength_assoc _ _ _ P) as X1.
  normal.
  rewrite X0, X1; clear X0 X1.

  normal.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !proj_right_tensor_id.
  unfold proj_left, proj_right.
  normal.
  rewrite <- !comp_assoc.
  pose proof (@to_tensor_assoc_natural _ _ x _ y _ (F z ⨂ G z) _
                id id (unit_right ∘ (id[F z] ⨂ eliminate))) as X0.
  rewrite bimap_id_id in X0.
  rewrites.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  srewrite_r diagonal_natural.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects.
  - apply compose_respects; [|reflexivity].
    apply bimap_respects; [reflexivity|].
    rewrite !eliminate_comp.
    rewrite unit_right_eliminate.
    reflexivity.
  - rewrite !bimap_comp.
    rewrite !bimap_comp_id_left.
    rewrite !bimap_comp_id_right.
    rewrite !comp_assoc.
    rewrite !triangle_identity.
    rewrite <- !comp_assoc.
    rewrite from_tensor_assoc_natural.
    rewrite (comp_assoc tensor_assoc (tensor_assoc⁻¹)).
    rewrite iso_to_from, id_left.
    rewrite <- bimap_comp, id_left.
    rewrite <- to_tensor_assoc_natural.
    pose proof (@to_tensor_assoc_natural _ _ x _ y _ (F z ⨂ G z) _
                  id id (unit_left ∘ eliminate ⨂ id[G z])) as X0.
    rewrite bimap_id_id in X0.
    rewrites.
    rewrite !comp_assoc.
    apply compose_respects; [|reflexivity].
    rewrite <- (comp_assoc _ tensor_assoc).
    rewrite <- to_tensor_assoc_natural.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc tensor_assoc (tensor_assoc⁻¹)).
    rewrite iso_to_from, id_left.
    rewrite to_tensor_assoc_natural.
    rewrite (comp_assoc _ tensor_assoc).
    rewrite <- triangle_identity.
    normal.
    rewrite !eliminate_comp.
    rewrite unit_left_eliminate.
    rewrite (bimap_comp_id_right unit_right).
    rewrite <- !comp_assoc.
    rewrite from_tensor_assoc_natural.
    rewrite (comp_assoc _ (tensor_assoc⁻¹)).
    rewrite <- inverse_triangle_identity.
    normal.
    reflexivity.
Qed.

End ProductStrong.
