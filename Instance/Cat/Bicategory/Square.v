Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Square.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Cat.Bicategory.Adjunction.

Generalizable All Variables.

(** * The adjoint-square mate is the mates mate, at Cat *)

(* nLab: https://ncatlab.org/nlab/show/mate

   Adjunction/Square.v develops Mac Lane §IV.7 Exercises 4 and 5 in
   ordinary-category vocabulary, with no bicategorical machinery, so that
   it applies to categories of any size.  This file reconciles that
   development with Theory/Bicategory/Mates.v:486 [mate] and :490
   [mate_inv] read in Cat, of which it is the ordinary-functor case, and
   it is the sibling of Instance/Cat/Bicategory/Conjugate.v, which does
   the same for the identity-bounding-cell development of
   Adjunction/Conjugate.v.

   Nothing here needs a padding transformation.  Scout measurement, re-run
   here: [mate] and [mate_inv] at Cat take and return the ORDINARY functor
   composites — the statements below ascribe [SqMate A A' K L sg] against
   [mate SqBA SqBA' sg] with no comparison map and no transport — because
   the bounding cells are genuine functors K and L rather than identities,
   so the F' ◯ Id trap that Instance/Cat/Bicategory/Conjugate.v records
   does not arise on this route.  The bridge to the bicategorical side is
   taken through the TRANSPARENT Instance/Cat/Bicategory/Adjunction.v:159
   [Cat_Adjunction_BicatAdjunction], never through :163
   [Cat_BicatAdjunction_Adjunction_iff], which is data closed with Qed.

   WHAT THE COMPARISON COSTS, MEASURED.  After [simpl; unfold sq_mate] the
   right-hand side of [sq_mate_is_mate] carries NINE unitor and associator
   residues of the form [fmap _ id] (counted in the printed goal: three
   [fmap[U'] (fmap[K] id)], three [fmap[U'] id], two [fmap[L] id] and one
   [fmap[L] (fmap[U] id)]), against the intended
   [fmap[U'] (fmap[K] counit) ∘ (fmap[U'] (sg (U a)) ∘ unit)].  They are
   cleared by exactly [rewrite !fmap_id; rewrite ?id_left, ?id_right],
   which is what Instance/Cat/Bicategory/Adjunction.v:244
   [Cat_mate_unfold_raw] does; the extra steps on this side are
   [to_adj_unit], which turns the caller's own transpose into the pasted
   form, then one [fmap_comp] and one [comp_assoc] to reassociate it.
   The strict form [SqMate A A' K L sg a = mate SqBA SqBA' sg a] is
   REFUTED at [eq_refl] (pinned as Test/ProbeSquare398.v's N12); only ≈
   holds.  [sq_mate_inv_is_mate_inv] goes
   through the same way and is in fact shorter — [from_adj_counit] then
   the same two clearing lines, with no [fmap_comp] and no [comp_assoc] —
   and its goal carries nine residues of the same shape.

   [adjoint_square_iff_Cat_mate] is the issue's second work item read at
   Cat: the adjoint-square condition on a pair of natural transformations
   holds exactly when the second is the bicategorical mate of the first.
   It is stated with NO naturality hypothesis, which is stronger than the
   corresponding bare-family statement [adjoint_square_iff_mate] needs:
   the σ here is a [Transform], so Adjunction/Square.v's
   [transform_SigmaNat] supplies the hypothesis for free.
   [adjoint_square_iff_Cat_mate_inv] is its mirror over [mate_inv], from
   [transform_TauNat].

   NOT DELIVERED.  Nothing relates the two PASTINGS of
   Adjunction/Square.v to any bicategorical composition, so
   Theory/Bicategory/Mates.v's descope ledger 10 — pasting functoriality
   in an ARBITRARY bicategory — was left untouched by this file, which did
   not edit Mates.v; Instance/Adj/Bicategory.v (#399) later narrows that
   note without discharging the entry, and its arbitrary-bicategory half
   remains open.
   No comparison with :525 [mate_iso] as an isomorphism of setoids, so
   Adjunction/Square.v's [square_bijection] is not identified with it.  No
   [mate_inv] component lemma is added to the donor file.  Nothing is
   registered as an [Instance], and there is no concrete witness. *)

Section SquareMatesAtCat.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Definition SqBA  : BicatAdjunction (B:=Cat_Bicategory) F  U  :=
  Cat_Adjunction_BicatAdjunction A.
Definition SqBA' : BicatAdjunction (B:=Cat_Bicategory) F' U' :=
  Cat_Adjunction_BicatAdjunction A'.

Theorem sq_mate_is_mate (sg : F' ◯ L ⟹ K ◯ F) :
  SqMate A A' K L sg ≈ mate SqBA SqBA' sg.
Proof.
  intros a; simpl; unfold sq_mate.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem sq_mate_inv_is_mate_inv (ta : L ◯ U ⟹ U' ◯ K) :
  SqMateInv A A' K L ta ≈ mate_inv SqBA SqBA' ta.
Proof.
  intros x; simpl; unfold sq_mate_inv.
  rewrite (from_adj_counit (H:=A')).
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem adjoint_square_iff_Cat_mate
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT A A' K L sg ta ↔ ta ≈ mate SqBA SqBA' sg.
Proof.
  split; intro H.
  - intro a.
    rewrite (SqMate_uniq A A' K L sg ta H a).
    exact (sq_mate_is_mate sg a).
  - apply (sq_mate_to_hom A A' K L _ _ (transform_SigmaNat K L sg)).
    intro a.
    rewrite (H a).
    symmetry; exact (sq_mate_is_mate sg a).
Qed.

Theorem adjoint_square_iff_Cat_mate_inv
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT A A' K L sg ta ↔ sg ≈ mate_inv SqBA SqBA' ta.
Proof.
  split; intro H.
  - intro x.
    rewrite (SqMateInv_uniq A A' K L sg ta H x).
    exact (sq_mate_inv_is_mate_inv ta x).
  - apply (sq_mate_inv_to_hom A A' K L _ _ (transform_TauNat K L ta)).
    intro x.
    rewrite (H x).
    symmetry; exact (sq_mate_inv_is_mate_inv ta x).
Qed.

End SquareMatesAtCat.
