Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Bicartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.

Generalizable All Variables.

(** * Semiadditive categories *)

(* nLab:      https://ncatlab.org/nlab/show/semiadditive+category
   Wikipedia: https://en.wikipedia.org/wiki/Biproduct

   A semiadditive category is a category in which finite products and finite
   coproducts exist and coincide (as biproducts).  Its hom-setoids are then
   canonically commutative monoids, and this file proves the two theorems
   that make the slogan precise, in both directions:

   (i)  [biproduct_addition]: in a category enriched in commutative monoids
        (a [Preadditive] category in the CMon sense of
        Structure/Preadditive.v) with a zero object, biproducts express the
        enrichment: f + g ≈ ∇ ∘ (f ⊕ g) ∘ Δ.  Moreover the enrichment
        already forces every product to be a biproduct
        ([cartesian_biproduct]), the key identity being the decomposition
        of the identity [biproduct_id_decomp]:
        inl ∘ exl + inr ∘ exr ≈ id.

   (ii) [bicartesian_preadditive]: conversely, in a bicartesian category
        with a zero object where the canonical comparison morphism
        x + y ~> x × y ([can_comparison]) is invertible, the convolution

            f + g  :=  (f ▽ g) ∘ can⁻¹ ∘ ⟨id, id⟩

        makes the category preadditive.  Commutativity and associativity
        of the convolution follow from an Eckmann–Hilton argument: the
        coproduct-flavoured convolution [conv] and the product-flavoured
        convolution [conv_pr] share the unit 0 and satisfy the interchange
        law (via [fork_merge] of Structure/Bicartesian.v), hence coincide
        and are commutative and associative. *)

(** ** Theorem (i): biproducts realize the preadditive structure *)

Section BiproductAddition.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.

(* The identity of a biproduct decomposes as the sum of its two
   "projection-then-injection" idempotents.  Both sides mediate the product
   cone (bi_exl, bi_exr), so they agree by the uniqueness half of the
   product universal property. *)
Theorem biproduct_id_decomp {x y : C} (B : Biproduct x y) :
  padd (bi_inl B ∘ bi_exl B) (bi_inr B ∘ bi_exr B) ≈ id.
Proof.
  apply (bi_pair_eq B (bi_exl B) (bi_exr B)).
  - rewrite compose_padd_left.
    rewrite !comp_assoc.
    rewrite bi_exl_inl, bi_exl_inr.
    rewrite id_left.
    rewrite zero_mor_right.
    rewrite <- pzero_zero_mor.
    apply padd_zero_right.
  - rewrite compose_padd_left.
    rewrite !comp_assoc.
    rewrite bi_exr_inl, bi_exr_inr.
    rewrite id_left.
    rewrite zero_mor_right.
    rewrite <- pzero_zero_mor.
    apply padd_zero_left.
  - apply id_right.
  - apply id_right.
Qed.

(* Every morphism into a biproduct is the sum of its two components,
   reinjected.  This is the identity decomposition transported along the
   pairing. *)
Lemma bi_pair_decomp {x y z : C} (B : Biproduct x y)
  (f : z ~> x) (g : z ~> y) :
  bi_pair B f g ≈ padd (bi_inl B ∘ f) (bi_inr B ∘ g).
Proof.
  transitivity (id ∘ bi_pair B f g).
  - now rewrite id_left.
  - rewrite <- (biproduct_id_decomp B).
    rewrite compose_padd_right.
    apply padd_respects.
    + now rewrite <- comp_assoc, bi_exl_pair.
    + now rewrite <- comp_assoc, bi_exr_pair.
Qed.

(* Copairing against pairing computes the matrix product: a 1×2 row against
   a 2×1 column yields the sum of the diagonal composites. *)
Lemma bi_copair_pair {x y z w : C} (B : Biproduct x y)
  (u : x ~> w) (v : y ~> w) (f : z ~> x) (g : z ~> y) :
  bi_copair B u v ∘ bi_pair B f g ≈ padd (u ∘ f) (v ∘ g).
Proof.
  rewrite bi_pair_decomp.
  rewrite compose_padd_left.
  apply padd_respects.
  - now rewrite comp_assoc, bi_copair_inl.
  - now rewrite comp_assoc, bi_copair_inr.
Qed.

(* Pairing fuses with the biproduct's functorial action. *)
Lemma bimap_bi_pair {x y x' y' z : C}
  (B : Biproduct x y) (B' : Biproduct x' y')
  (f : x ~> x') (g : y ~> y') (h : z ~> x) (k : z ~> y) :
  bimap B B' f g ∘ bi_pair B h k ≈ bi_pair B' (f ∘ h) (g ∘ k).
Proof.
  symmetry.
  apply bi_pair_unique.
  - rewrite comp_assoc.
    rewrite bimap_exl.
    now rewrite <- comp_assoc, bi_exl_pair.
  - rewrite comp_assoc.
    rewrite bimap_exr.
    now rewrite <- comp_assoc, bi_exr_pair.
Qed.

(* The first canonical theorem: the enrichment addition is computed by the
   biproduct as f + g ≈ ∇ ∘ (f ⊕ g) ∘ Δ. *)
Theorem biproduct_addition {x y : C} (B : Biproduct x x) (B' : Biproduct y y)
  (f g : x ~> y) :
  padd f g ≈ bi_copair B' id id ∘ bimap B B' f g ∘ bi_pair B id id.
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_bi_pair.
  rewrite bi_copair_pair.
  now rewrite !id_left, !id_right.
Qed.

End BiproductAddition.

(** ** Theorem (i), continued: products are biproducts in a preadditive
    category *)

Section CartesianBiproduct.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.
Context `{H : @Cartesian C}.

(* The product-side universal property, packaged for the biproduct record:
   the mediator is the fork, and uniqueness is [ump_products]. *)
Definition cartesian_bi_is_product (x y z : C) (f : z ~> x) (g : z ~> y) :
  ∃! h : z ~> x × y, (exl ∘ h ≈ f) ∧ (exr ∘ h ≈ g).
Proof.
  unshelve refine {| unique_obj := f △ g |}.
  - split.
    + apply exl_fork.
    + apply exr_fork.
  - intros v Hv.
    symmetry.
    now apply ump_products.
Defined.

(* The identity decomposition for the product equipped with the additive
   injections id △ 0 and 0 △ id.  Both sides mediate the cone (exl, exr). *)
Lemma cartesian_id_decomp {x y : C} :
  padd ((id △ zero_mor) ∘ exl) ((zero_mor △ id) ∘ exr) ≈ id[x × y].
Proof.
  rewrite <- fork_exl_exr.
  apply ump_products; split.
  - rewrite compose_padd_left.
    rewrite !comp_assoc.
    rewrite !exl_fork.
    rewrite id_left.
    rewrite zero_mor_right.
    rewrite <- pzero_zero_mor.
    apply padd_zero_right.
  - rewrite compose_padd_left.
    rewrite !comp_assoc.
    rewrite !exr_fork.
    rewrite id_left.
    rewrite zero_mor_right.
    rewrite <- pzero_zero_mor.
    apply padd_zero_left.
Qed.

(* The coproduct-side universal property of the product: the mediator out of
   x × y is the sum of the composites through the projections, and its
   uniqueness follows from [cartesian_id_decomp]. *)
Definition cartesian_bi_is_coproduct (x y z : C) (f : x ~> z) (g : y ~> z) :
  ∃! h : x × y ~> z,
    (h ∘ (id △ zero_mor) ≈ f) ∧ (h ∘ (zero_mor △ id) ≈ g).
Proof using C H P Z.
  unshelve refine {| unique_obj := padd (f ∘ exl) (g ∘ exr) |}.
  - split.
    + rewrite compose_padd_right.
      rewrite <- !comp_assoc.
      rewrite exl_fork, exr_fork.
      rewrite id_right.
      rewrite zero_mor_left.
      rewrite <- pzero_zero_mor.
      apply padd_zero_right.
    + rewrite compose_padd_right.
      rewrite <- !comp_assoc.
      rewrite exl_fork, exr_fork.
      rewrite id_right.
      rewrite zero_mor_left.
      rewrite <- pzero_zero_mor.
      apply padd_zero_left.
  - intros v Hv.
    destruct Hv as [Hl Hr].
    symmetry.
    transitivity (v ∘ padd ((id △ zero_mor) ∘ exl) ((zero_mor △ id) ∘ exr)).
    + rewrite cartesian_id_decomp.
      now rewrite id_right.
    + rewrite compose_padd_left.
      rewrite !comp_assoc.
      rewrite Hl, Hr.
      reflexivity.
Defined.

(* In a preadditive category, every binary product is a biproduct: the
   injections are id △ 0 and 0 △ id, and the four interaction laws are the
   fork computation rules. *)
Definition cartesian_biproduct (x y : C) : Biproduct x y := {|
  biproduct_obj := x × y;
  bi_inl := id △ zero_mor;
  bi_inr := zero_mor △ id;
  bi_exl := exl;
  bi_exr := exr;
  bi_exl_inl := exl_fork id zero_mor;
  bi_exr_inr := exr_fork zero_mor id;
  bi_exl_inr := exl_fork zero_mor id;
  bi_exr_inl := exr_fork id zero_mor;
  bi_is_product := cartesian_bi_is_product x y;
  bi_is_coproduct := cartesian_bi_is_coproduct x y
|}.

(* Corollary: a preadditive category with finite products has all binary
   biproducts. *)
Definition cartesian_has_biproducts : HasBiproducts C := {|
  biproduct := cartesian_biproduct
|}.

End CartesianBiproduct.

(** ** Theorem (ii): semiadditivity from a bicartesian category with an
    invertible canonical comparison *)

Section BicartesianSemiadditive.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{HC : @Cartesian C}.
Context `{HD : @Cocartesian C}.

(* Two morphisms into a product agree when their projections agree. *)
Lemma fork_ext {x y z : C} (u v : x ~> y × z) :
  exl ∘ u ≈ exl ∘ v → exr ∘ u ≈ exr ∘ v → u ≈ v.
Proof.
  intros Hl Hr.
  transitivity ((exl ∘ u) △ (exr ∘ u)).
  - rewrite fork_comp, fork_exl_exr.
    now rewrite id_left.
  - rewrite Hl, Hr.
    rewrite fork_comp, fork_exl_exr.
    now rewrite id_left.
Qed.

(* Dually, two morphisms out of a coproduct agree when their restrictions
   along the injections agree. *)
Lemma merge_ext {x y z : C} (u v : x + y ~{C}~> z) :
  u ∘ inl ≈ v ∘ inl → u ∘ inr ≈ v ∘ inr → u ≈ v.
Proof.
  intros Hl Hr.
  transitivity ((u ∘ inl) ▽ (u ∘ inr)).
  - rewrite merge_comp, merge_inl_inr.
    now rewrite id_right.
  - rewrite Hl, Hr.
    rewrite merge_comp, merge_inl_inr.
    now rewrite id_right.
Qed.

(* The canonical comparison morphism from the coproduct to the product,
   the "identity matrix" ((id, 0), (0, id)). *)
Definition can_comparison (x y : C) : x + y ~{C}~> x × y :=
  (id △ zero_mor) ▽ (zero_mor △ id).

(* The two column computations... *)
Lemma can_inl {x y : C} : can_comparison x y ∘ inl ≈ id △ zero_mor.
Proof. apply inl_merge. Qed.

Lemma can_inr {x y : C} : can_comparison x y ∘ inr ≈ zero_mor △ id.
Proof. apply inr_merge. Qed.

(* ...and the four matrix entries of the comparison. *)
Lemma exl_can_inl {x y : C} : exl ∘ can_comparison x y ∘ inl ≈ id.
Proof.
  rewrite <- comp_assoc, can_inl.
  apply exl_fork.
Qed.

Lemma exr_can_inl {x y : C} : exr ∘ can_comparison x y ∘ inl ≈ zero_mor.
Proof.
  rewrite <- comp_assoc, can_inl.
  apply exr_fork.
Qed.

Lemma exl_can_inr {x y : C} : exl ∘ can_comparison x y ∘ inr ≈ zero_mor.
Proof.
  rewrite <- comp_assoc, can_inr.
  apply exl_fork.
Qed.

Lemma exr_can_inr {x y : C} : exr ∘ can_comparison x y ∘ inr ≈ id.
Proof.
  rewrite <- comp_assoc, can_inr.
  apply exr_fork.
Qed.

(* Semiadditivity hypothesis: the canonical comparison is invertible. *)
Context (E : ∀ x y : C, IsIsomorphism (can_comparison x y)).

Definition can_inv (x y : C) : x × y ~{C}~> x + y :=
  @two_sided_inverse C _ _ (can_comparison x y) (E x y).

Lemma can_can_inv {x y : C} : can_comparison x y ∘ can_inv x y ≈ id.
Proof. exact (@is_right_inverse C _ _ (can_comparison x y) (E x y)). Qed.

Lemma can_inv_can {x y : C} : can_inv x y ∘ can_comparison x y ≈ id.
Proof. exact (@is_left_inverse C _ _ (can_comparison x y) (E x y)). Qed.

(* Cancellation forms of the inverse laws, shaped for rewriting inside
   right-associated composites. *)
Lemma can_can_inv_cancel {x y z : C} (h : z ~> x × y) :
  can_comparison x y ∘ (can_inv x y ∘ h) ≈ h.
Proof.
  rewrite comp_assoc, can_can_inv.
  now rewrite id_left.
Qed.

Lemma can_inv_can_cancel {x y z : C} (h : z ~> x + y) :
  can_inv x y ∘ (can_comparison x y ∘ h) ≈ h.
Proof.
  rewrite comp_assoc, can_inv_can.
  now rewrite id_left.
Qed.

(* The inverse sends the additive injections of the product back to the
   coproduct injections. *)
Lemma can_inv_fork_inl {x y : C} : can_inv x y ∘ (id △ zero_mor) ≈ inl.
Proof.
  rewrite <- can_inl.
  apply can_inv_can_cancel.
Qed.

Lemma can_inv_fork_inr {x y : C} : can_inv x y ∘ (zero_mor △ id) ≈ inr.
Proof.
  rewrite <- can_inr.
  apply can_inv_can_cancel.
Qed.

(* The convolution addition on hom-setoids, in its coproduct-flavoured form
   (sum after the coproduct copairing)...

       x --⟨id,id⟩--> x × x --can⁻¹--> x + x --f ▽ g--> y            *)
Definition conv {x y : C} (f g : x ~> y) : x ~> y :=
  (f ▽ g) ∘ can_inv x x ∘ (id △ id).

(* ...and in its product-flavoured form (sum before the product pairing):

       x --f △ g--> y × y --can⁻¹--> y + y --[id,id]--> y            *)
Definition conv_pr {x y : C} (f g : x ~> y) : x ~> y :=
  (id ▽ id) ∘ can_inv y y ∘ (f △ g).

#[local] Instance conv_respects {x y : C} :
  Proper (equiv ==> equiv ==> equiv) (@conv x y).
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  unfold conv.
  now rewrite Hf, Hg.
Qed.

#[local] Instance conv_pr_respects {x y : C} :
  Proper (equiv ==> equiv ==> equiv) (@conv_pr x y).
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  unfold conv_pr.
  now rewrite Hf, Hg.
Qed.

(* Copairing with a zero component factors through a single projection. *)
Lemma merge_zero_left {x y : C} (f : x ~> y) :
  zero_mor ▽ f ≈ (f ∘ exr) ∘ can_comparison x x.
Proof.
  apply merge_ext.
  - rewrite inl_merge.
    rewrite <- !comp_assoc.
    rewrite can_inl.
    rewrite exr_fork.
    now rewrite zero_mor_left.
  - rewrite inr_merge.
    rewrite <- !comp_assoc.
    rewrite can_inr.
    rewrite exr_fork.
    now rewrite id_right.
Qed.

Lemma merge_zero_right {x y : C} (f : x ~> y) :
  f ▽ zero_mor ≈ (f ∘ exl) ∘ can_comparison x x.
Proof.
  apply merge_ext.
  - rewrite inl_merge.
    rewrite <- !comp_assoc.
    rewrite can_inl.
    rewrite exl_fork.
    now rewrite id_right.
  - rewrite inr_merge.
    rewrite <- !comp_assoc.
    rewrite can_inr.
    rewrite exl_fork.
    now rewrite zero_mor_left.
Qed.

(* Dually, pairing with a zero component factors through a single
   injection. *)
Lemma fork_zero_left {x y : C} (f : x ~> y) :
  zero_mor △ f ≈ can_comparison y y ∘ (inr ∘ f).
Proof.
  apply fork_ext.
  - rewrite exl_fork.
    rewrite !comp_assoc.
    rewrite exl_can_inr.
    now rewrite zero_mor_right.
  - rewrite exr_fork.
    rewrite !comp_assoc.
    rewrite exr_can_inr.
    now rewrite id_left.
Qed.

Lemma fork_zero_right {x y : C} (f : x ~> y) :
  f △ zero_mor ≈ can_comparison y y ∘ (inl ∘ f).
Proof.
  apply fork_ext.
  - rewrite exl_fork.
    rewrite !comp_assoc.
    rewrite exl_can_inl.
    now rewrite id_left.
  - rewrite exr_fork.
    rewrite !comp_assoc.
    rewrite exr_can_inl.
    now rewrite zero_mor_right.
Qed.

(* The zero morphism is a two-sided unit for both convolutions. *)
Lemma conv_zero_left {x y : C} (f : x ~> y) : conv zero_mor f ≈ f.
Proof.
  unfold conv.
  rewrite merge_zero_left.
  rewrite <- !comp_assoc.
  rewrite can_can_inv_cancel.
  rewrite exr_fork.
  now rewrite id_right.
Qed.

Lemma conv_zero_right {x y : C} (f : x ~> y) : conv f zero_mor ≈ f.
Proof.
  unfold conv.
  rewrite merge_zero_right.
  rewrite <- !comp_assoc.
  rewrite can_can_inv_cancel.
  rewrite exl_fork.
  now rewrite id_right.
Qed.

Lemma conv_pr_zero_left {x y : C} (f : x ~> y) : conv_pr zero_mor f ≈ f.
Proof.
  unfold conv_pr.
  rewrite fork_zero_left.
  rewrite <- !comp_assoc.
  rewrite can_inv_can_cancel.
  rewrite comp_assoc.
  rewrite inr_merge.
  now rewrite id_left.
Qed.

Lemma conv_pr_zero_right {x y : C} (f : x ~> y) : conv_pr f zero_mor ≈ f.
Proof.
  unfold conv_pr.
  rewrite fork_zero_right.
  rewrite <- !comp_assoc.
  rewrite can_inv_can_cancel.
  rewrite comp_assoc.
  rewrite inl_merge.
  now rewrite id_left.
Qed.

(* The Eckmann–Hilton interchange law between the two convolutions.  It is
   exactly the bicartesian interchange [fork_merge] of
   Structure/Bicartesian.v, conjugated by can⁻¹ on both sides. *)
Lemma conv_interchange {x y : C} (a b c d : x ~> y) :
  conv (conv_pr a b) (conv_pr c d) ≈ conv_pr (conv a c) (conv b d).
Proof.
  unfold conv, conv_pr.
  rewrite merge_comp.
  rewrite fork_merge.
  rewrite !fork_comp.
  rewrite !comp_assoc.
  reflexivity.
Qed.

(* Eckmann–Hilton, first consequence: the two convolutions coincide. *)
Lemma conv_conv_pr {x y : C} (f g : x ~> y) : conv f g ≈ conv_pr f g.
Proof.
  transitivity (conv (conv_pr f zero_mor) (conv_pr zero_mor g)).
  - now rewrite conv_pr_zero_right, conv_pr_zero_left.
  - rewrite conv_interchange.
    now rewrite conv_zero_right, conv_zero_left.
Qed.

(* Eckmann–Hilton, second consequence: convolution is commutative. *)
Lemma conv_comm {x y : C} (f g : x ~> y) : conv f g ≈ conv g f.
Proof.
  transitivity (conv (conv_pr zero_mor f) (conv_pr g zero_mor)).
  - now rewrite conv_pr_zero_left, conv_pr_zero_right.
  - rewrite conv_interchange.
    rewrite conv_zero_left, conv_zero_right.
    now rewrite <- conv_conv_pr.
Qed.

(* Eckmann–Hilton, third consequence: convolution is associative. *)
Lemma conv_assoc {x y : C} (f g h : x ~> y) :
  conv (conv f g) h ≈ conv f (conv g h).
Proof.
  transitivity (conv (conv_pr f zero_mor) (conv_pr g h)).
  - rewrite conv_interchange.
    rewrite conv_zero_left.
    now rewrite <- conv_conv_pr.
  - rewrite conv_pr_zero_right.
    now rewrite <- conv_conv_pr.
Qed.

(* Composition distributes over convolution on the left (computed in the
   coproduct-flavoured form)... *)
Lemma conv_compose_left {x y z : C} (h : y ~> z) (f g : x ~> y) :
  h ∘ conv f g ≈ conv (h ∘ f) (h ∘ g).
Proof.
  unfold conv.
  rewrite !comp_assoc.
  rewrite <- merge_comp.
  reflexivity.
Qed.

(* ...and on the right (computed in the product-flavoured form). *)
Lemma conv_compose_right {x y z : C} (f g : y ~> z) (h : x ~> y) :
  conv f g ∘ h ≈ conv (f ∘ h) (g ∘ h).
Proof.
  rewrite !conv_conv_pr.
  unfold conv_pr.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  reflexivity.
Qed.

(* The second canonical theorem: a bicartesian category with a zero object
   in which the canonical comparison x + y ~> x × y is invertible is
   preadditive (CMon-enriched), with convolution as addition and the zero
   morphism as unit.  Together with [cartesian_biproduct] this closes the
   loop: such a category is semiadditive, i.e. its products and coproducts
   are biproducts. *)
Definition bicartesian_preadditive : Preadditive C := {|
  padd := @conv;
  pzero := @zero_mor C Z;
  padd_respects := @conv_respects;
  padd_assoc := @conv_assoc;
  padd_comm := @conv_comm;
  padd_zero_left := @conv_zero_left;
  compose_padd_left := @conv_compose_left;
  compose_padd_right := @conv_compose_right;
  compose_pzero_left := @zero_mor_right C Z;
  compose_pzero_right := @zero_mor_left C Z
|}.

End BicartesianSemiadditive.
