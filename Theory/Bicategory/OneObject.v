Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Theory.Bicategory.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/bicategory (§ "Examples", delooping)
   nLab: https://ncatlab.org/nlab/show/delooping

   A monoidal category is exactly a one-object bicategory.  Delooping the single
   0-cell, the 1-cells become the objects of the monoidal category, the 2-cells
   its morphisms, vertical composition its composition, horizontal composition
   its tensor product, and the unitors/associator of the bicategory the
   unitors/associator of the monoidal structure.  This is the routine sanity
   check that every field added to [Bicategory] in Theory/Bicategory.v was
   shaped to mirror the corresponding field of [Structure/Monoidal.v]: here the
   mirror is *exact*, so the entire bicategory is assembled by directly
   projecting the monoidal data, with no wrapper on a single field.

   Dictionary (Bicategory field  ←  Monoidal field):

       bi0cell               ←  unit          (the single delooped 0-cell)
       bicat tt tt           ←  C             (the one hom-category is C itself)
       hcompose              ←  tensor
       bi1id                 ←  I
       hunit_left            ←  unit_left     (λ)
       hunit_right           ←  unit_right    (ρ)
       hassoc                ←  tensor_assoc  (α, same orientation)
       hunit_left_natural    ←  to_unit_left_natural
       hunit_right_natural   ←  to_unit_right_natural
       hassoc_natural        ←  to_tensor_assoc_natural
       hcoherence_triangle   ←  triangle_identity
       hcoherence_pentagon   ←  pentagon_identity

   DEFINITIONAL-EQUALITY NOTE (the same technique as Instance/Cat/Bicategory.v).
   The [hcompose] field wants a functor `bicat tt tt ∏ bicat tt tt ⟶ bicat tt tt`,
   whereas [tensor] has type `C ∏ C ⟶ C`.  For Coq to accept it cheaply the
   manifest hom-category `bicat tt tt` must be *definitionally* C; otherwise
   unifying two non-convertible `Category` records churns.  We obtain that
   convertibility by feeding the structural fields of the bicategory from C's own
   projections (record eta then gives `bicat tt tt ≡ C`), i.e. we build with the
   raw [Build_Bicategory], supplying C's own `comp_assoc_sym` projection directly
   (record eta breaks under the `symmetry`-derived form of [Build_Bicategory']).
   With `bicat tt tt ≡ C` in place, every coherence field type reduces to the
   corresponding monoidal axiom verbatim, so the monoidal proof plugs straight in.
   (`hcomp2 θ η` is the manifest `fmap[hcompose] (θ, η)`, which is exactly
   `bimap θ η` for `hcompose := tensor`, so the naturality and coherence
   statements land on the nose.) *)

Definition Monoidal_OneObject_Bicategory
    (C : Category) `{M : @Monoidal C} : Bicategory :=
  Build_Bicategory
    unit                             (* bi0cell   : one delooped 0-cell   *)
    (fun _ _ => @obj C)              (* bi1cell   := objects of C         *)
    (fun _ _ => @hom C)              (* bi2cell   := morphisms of C       *)
    (fun _ => @I C M)                (* bi1id     := I                    *)
    (fun _ _ => @homset C)           (* bi2homset := hom-setoids of C     *)
    (fun _ _ => @id C)               (* bi2id     := identities of C      *)
    (fun _ _ => @compose C)          (* vcompose  := composition of C     *)
    (fun _ _ => @compose_respects C) (* vcompose_respects                 *)
    (fun _ _ => @id_left C)          (* bi2id_left                        *)
    (fun _ _ => @id_right C)         (* bi2id_right                       *)
    (fun _ _ => @comp_assoc C)       (* vcompose_assoc                    *)
    (fun _ _ => @comp_assoc_sym C)   (* vcompose_assoc_sym (raw form)     *)
    (fun _ _ _ => @tensor C M)       (* hcompose  := tensor               *)
    (fun _ _ => @unit_left C M)      (* hunit_left  := λ                  *)
    (fun _ _ => @unit_right C M)     (* hunit_right := ρ                  *)
    (fun _ _ _ _ => @tensor_assoc C M)            (* hassoc := α          *)
    (fun _ _ => @to_unit_left_natural C M)        (* hunit_left_natural   *)
    (fun _ _ => @to_unit_right_natural C M)       (* hunit_right_natural  *)
    (fun _ _ _ _ => @to_tensor_assoc_natural C M) (* hassoc_natural       *)
    (fun _ _ _ => @triangle_identity C M)         (* hcoherence_triangle  *)
    (fun _ _ _ _ _ => @pentagon_identity C M).    (* hcoherence_pentagon  *)

(* Kelly's unit-coincidence, transported.  A monoidal category satisfies
   λ_I ≈ ρ_I ([unit_identity] in Structure/Monoidal/Proofs.v, a derived
   consequence of the triangle and pentagon axioms).  Under the delooping this
   is precisely the statement that the left and right unitors of the one-object
   bicategory agree on the identity 1-cell.  Because `bicat tt tt ≡ C`, the two
   unitors-at-`bi1id` are the very isomorphisms `unit_left`/`unit_right` at I, so
   the corollary is [unit_identity] lifted from the `to`-level to an equivalence
   of isomorphisms by [to_equiv_implies_iso_equiv]. *)

Corollary Monoidal_OneObject_unit_coincidence
    (C : Category) `{M : @Monoidal C} :
  @hunit_left  (Monoidal_OneObject_Bicategory C) tt tt
               (@bi1id (Monoidal_OneObject_Bicategory C) tt)
    ≈ @hunit_right (Monoidal_OneObject_Bicategory C) tt tt
                   (@bi1id (Monoidal_OneObject_Bicategory C) tt).
Proof.
  apply to_equiv_implies_iso_equiv, unit_identity.
Qed.
