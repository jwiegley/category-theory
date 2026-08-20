Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.

Generalizable All Variables.

(** * The direct sum is the coproduct in R-Mod *)

(* Book: Mac Lane, "Categories for the Working Mathematician" (2nd ed.),
         §III.3, book p. 63 (maclane:III.3:remark1)
   Book: Riehl, "Category Theory in Context" (2nd ed.), §3.1,
         printed p. 93 (riehl:3.1:exxi)
   Wikipedia: https://en.wikipedia.org/wiki/Direct_sum_of_modules

   Mac Lane's roster entry for R-Mod, one layer above Instance/Ab.v: the
   coproduct of two modules is their direct sum, carried by the product of
   the underlying sets, with the action taken componentwise.

   THREE GRADES OF TRANSFER, MEASURED.  This is the informative half of
   the file, because R-Mod sits at a different distance from its donor
   than Ab does, and the distance is different for DATA, for LAWS and for
   the ∃!-PACKAGES.  Instance/Ab.v defines [AbHom A B := CMonHom A B] as
   a bare abbreviation, so Ab's arrows ARE CMon's and
   Instance/Ab/Coproduct.v inherits ten of the biproduct record's eleven
   fields by [:=].  Instance/Mod.v instead makes [RModHom] a RECORD
   wrapping an [AbHom] together with [rm_map_smul] (Instance/Mod.v:203).
   The three grades are then:

   (1) DATA — the four structural morphisms and the two mediators — must
   be REBUILT.  An arrow of R-Mod is not an arrow of Ab, and each rebuild
   carries exactly one new obligation, that it commutes with the action.
   TWO of the six are [reflexivity] — the two projections.  The other
   four are more: both injections need [rm_smul_zero_r]
   (Instance/Mod.v:163), r·0 ≈ 0, because [inl a] is [(a, 0)] and must
   satisfy [(r·a, 0) ≈ (r·a, r·0)]; the two mediators each spend
   [rm_map_smul]; and the copairing additionally spends
   [rm_smul_distr_l].  (An earlier draft of this header said "only one of
   the six", which was wrong twice over — it undercounted, and it
   contradicted this file's own later sentence about where
   [rm_smul_distr_l] is spent.)

   (2) LAWS — all four interaction laws — TRANSFER UNCHANGED, by [:=]
   with no tactic, exactly as at Ab.  [RModHom_Setoid]
   (Instance/Mod.v:224) compares the underlying maps and
   [rmod_hom_compose] (Instance/Mod.v:256) is [cmon_hom_compose] on those
   maps, so each law, once unfolded, IS the CMon equation about the same
   two functions — including the two comparing against [zero_mor], since
   [rmod_zero_mor_is_cmon_zero_mor] shows the UNDERLYING arrow of R-Mod's
   zero morphism IS CMon's by [eq_refl].  Note the statement has to be
   about [rm_hom] of it: the two zero morphisms themselves inhabit
   different types, so [≈] between them is not even well-formed, and it is
   the two PROPOSITIONS that are convertible, not the two terms.  (An
   earlier draft of this file proved all four by hand and said in this
   header that only the CMon MATHEMATICS carried over; that understated
   the transfer, and the four proofs are gone.)

   (3) The ∃!-PACKAGES must be REPACKAGED but not re-argued.  They
   quantify over [RModHom], a different type from [CMonHom], so the
   [∃!] record cannot be handed over as a term — that is a genuine
   formability failure, pinned in Test/ProbeCoproduct.v — while every
   equation INSIDE it is again the CMon equation.  The two proofs are
   three lines each and cite [CMon_bi_is_product] and
   [CMon_bi_is_coproduct] for all of their content.

   So the honest summary is: same propositions throughout, different
   containers for the data and for the ∃!, and nothing new proved about
   commutative monoids anywhere.

   WHAT IS PROVED, AND AT WHAT STRENGTH.  [RMod_Biproducts] inhabits
   [HasBiproducts (RMod R)] and, through
   [Structure/Biproduct/Cartesian.v], yields [RMod_Cartesian] and
   [RMod_Cocartesian] — the first product and coproduct structures on a
   module category in this tree (Instance/Vect/TensorAlgebra.v:113
   records the absence of [Cocartesian (RMod R)] as an obstruction it had
   to route around).  The coproduct object IS the product object at
   LEIBNIZ EQUALITY ([RMod_coprod_is_prod], [eq_refl]), and so is the
   underlying abelian group of the direct sum: [RMod_coprod_ab] shows it
   IS Instance/Ab/Coproduct.v's [Ab_product], so the two roster entries
   agree on the nose rather than up to a comparison.  Non-vacuity over
   ℤ ⊕ ℤ as a ℤ-module: the injections differ at the generator, and the
   copairing, the projections and the scalar action all compute by
   [eq_refl] on closed input.

   WHAT IS NOT DELIVERED.  No indexed or infinite direct sums, hence
   nothing about the free module on a set (Instance/Mod/Free.v owns that,
   and its carrier is an inductive quotient, not a product).  No
   [Additive (RMod R)]; [RMod_Preadditive] (Instance/Mod.v:809) exists and
   is not extended here.  Nothing about right modules beyond what
   [ModR R := RMod (Ring_op R)] gives for free by conversion, which is the
   whole statement again at the opposite ring — no separate development.
   And nothing about the tensor product, which is Instance/Mod/Tensor.v's
   subject and is a different universal property. *)

(* Instance/Mod.v:104's convention: the obligations below are
   introduced by hand, so that the record binders [M] and [N] arrive with
   their own names rather than whatever the global obligation tactic has
   already put in scope. *)
#[local] Obligation Tactic := idtac.

(** ** The direct sum as an object of R-Mod *)

(* The underlying abelian group is Instance/Ab/Coproduct.v's
   [Ab_product]; all that is added is the componentwise action. *)
Program Definition RMod_product {R : RingObject}
  (M N : RModObject R) : RModObject R := {|
  rm_ab := Ab_product M N;
  rm_smul := fun r p => (rm_smul M r (fst p), rm_smul N r (snd p))
|}.
Next Obligation.
  intros R M N r s Hrs p q [H1 H2].
  split; simpl.
  - now rewrite Hrs, H1.
  - now rewrite Hrs, H2.
Qed.
Next Obligation.
  intros R M N r m n.
  split; simpl; apply rm_smul_distr_l.
Qed.
Next Obligation.
  intros R M N r s m.
  split; simpl; apply rm_smul_distr_r.
Qed.
Next Obligation.
  intros R M N r s m.
  split; simpl; apply rm_smul_assoc.
Qed.
Next Obligation.
  intros R M N m.
  split; simpl; apply rm_smul_one.
Qed.

(** ** The four structural morphisms *)

(* Each wraps the corresponding morphism of Ab; the single new obligation
   is compatibility with the action. *)
Program Definition RMod_inl {R : RingObject} (M N : RModObject R) :
  M ~{RMod R}~> RMod_product M N := {|
  rm_hom := Ab_inl M N
|}.
Next Obligation.
  intros R M N r m.
  split; simpl.
  - reflexivity.
  - symmetry.
    apply rm_smul_zero_r.
Qed.

Program Definition RMod_inr {R : RingObject} (M N : RModObject R) :
  N ~{RMod R}~> RMod_product M N := {|
  rm_hom := Ab_inr M N
|}.
Next Obligation.
  intros R M N r n.
  split; simpl.
  - symmetry.
    apply rm_smul_zero_r.
  - reflexivity.
Qed.

Program Definition RMod_exl {R : RingObject} (M N : RModObject R) :
  RMod_product M N ~{RMod R}~> M := {|
  rm_hom := Ab_exl M N
|}.
Next Obligation. intros R M N r p; reflexivity. Qed.

Program Definition RMod_exr {R : RingObject} (M N : RModObject R) :
  RMod_product M N ~{RMod R}~> N := {|
  rm_hom := Ab_exr M N
|}.
Next Obligation. intros R M N r p; reflexivity. Qed.

(** ** The two mediators *)

Program Definition RMod_pair {R : RingObject} {M N P : RModObject R}
  (f : P ~{RMod R}~> M) (g : P ~{RMod R}~> N) :
  P ~{RMod R}~> RMod_product M N := {|
  rm_hom := CMon_pair (rm_hom f) (rm_hom g)
|}.
Next Obligation.
  intros R M N P f g r a.
  split; simpl.
  - apply (rm_map_smul f).
  - apply (rm_map_smul g).
Qed.

(* The copairing (a, b) ↦ f a + g b.  Its action obligation is the one
   place [rm_smul_distr_l] is spent. *)
Program Definition RMod_copair {R : RingObject} {M N P : RModObject R}
  (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) :
  RMod_product M N ~{RMod R}~> P := {|
  rm_hom := CMon_copair (rm_hom f) (rm_hom g)
|}.
Next Obligation.
  intros R M N P f g r p; simpl.
  rewrite (rm_map_smul f), (rm_map_smul g).
  symmetry.
  apply rm_smul_distr_l.
Qed.

(** ** The zero morphism of R-Mod is CMon's *)

(* What makes the two [zero_mor] laws transfer: [RMod_Zero]'s [one] and
   [zero] wrap [Ab_one] and [Ab_zero_hom] (Instance/Mod.v:339, :360),
   which are [CMon_one] and [CMon_zero_hom], and the hom-setoid compares
   underlying maps. *)
Example rmod_zero_mor_is_cmon_zero_mor {R : RingObject}
  (M N : RModObject R) :
  rm_hom (@zero_mor (RMod R) (RMod_Zero R) M N)
    = @zero_mor CMon CMon_Zero M N := eq_refl.

Lemma rmod_zero_mor_value {R : RingObject} (M N : RModObject R)
  (a : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (@zero_mor (RMod R) (RMod_Zero R) M N)) a
    ≈ cmon_zero N.
Proof.
  simpl.
  apply (cmon_map_zero (Ab_zero_hom N)).
Qed.

(** ** The four interaction laws, all four inherited on the nose *)

Definition RMod_exl_inl {R : RingObject} (M N : RModObject R) :
  RMod_exl M N ∘ RMod_inl M N ≈ id := CMon_exl_inl M N.

Definition RMod_exr_inr {R : RingObject} (M N : RModObject R) :
  RMod_exr M N ∘ RMod_inr M N ≈ id := CMon_exr_inr M N.

Definition RMod_exl_inr {R : RingObject} (M N : RModObject R) :
  RMod_exl M N ∘ RMod_inr M N ≈ @zero_mor (RMod R) (RMod_Zero R) N M :=
  CMon_exl_inr M N.

Definition RMod_exr_inl {R : RingObject} (M N : RModObject R) :
  RMod_exr M N ∘ RMod_inl M N ≈ @zero_mor (RMod R) (RMod_Zero R) M N :=
  CMon_exr_inl M N.

(** ** Both universal properties *)

(* The ∃!-package must be rebuilt — it quantifies over [RModHom], not over
   [CMonHom] — but every equation inside it is, after unfolding
   [RModHom_Setoid] and [rmod_hom_compose], the CMon equation about the
   same underlying maps.  So each proof cites the CMon original and adds
   nothing. *)
Definition RMod_is_product {R : RingObject} (M N P : RModObject R)
  (f : P ~{RMod R}~> M) (g : P ~{RMod R}~> N) :
  ∃! h : P ~{RMod R}~> RMod_product M N,
    (RMod_exl M N ∘ h ≈ f) ∧ (RMod_exr M N ∘ h ≈ g).
Proof.
  unshelve refine {| unique_obj := RMod_pair f g |}.
  - exact (unique_property
             (CMon_bi_is_product M N P (rm_hom f) (rm_hom g))).
  - intros v Hv.
    exact (uniqueness
             (CMon_bi_is_product M N P (rm_hom f) (rm_hom g))
             (rm_hom v) Hv).
Defined.

Definition RMod_is_coproduct {R : RingObject} (M N P : RModObject R)
  (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) :
  ∃! h : RMod_product M N ~{RMod R}~> P,
    (h ∘ RMod_inl M N ≈ f) ∧ (h ∘ RMod_inr M N ≈ g).
Proof.
  unshelve refine {| unique_obj := RMod_copair f g |}.
  - exact (unique_property
             (CMon_bi_is_coproduct M N P (rm_hom f) (rm_hom g))).
  - intros v Hv.
    exact (uniqueness
             (CMon_bi_is_coproduct M N P (rm_hom f) (rm_hom g))
             (rm_hom v) Hv).
Defined.

(** ** The biproduct, and with it the product and coproduct structures *)

Definition RMod_Biproduct {R : RingObject} (M N : RModObject R) :
  @Biproduct (RMod R) (RMod_Zero R) M N :=
  @Build_Biproduct (RMod R) (RMod_Zero R) M N
    (RMod_product M N)
    (RMod_inl M N)
    (RMod_inr M N)
    (RMod_exl M N)
    (RMod_exr M N)
    (RMod_exl_inl M N)
    (RMod_exr_inr M N)
    (RMod_exl_inr M N)
    (RMod_exr_inl M N)
    (RMod_is_product M N)
    (RMod_is_coproduct M N).

#[export] Instance RMod_Biproducts (R : RingObject) :
  @HasBiproducts (RMod R) (RMod_Zero R) :=
  @Build_HasBiproducts (RMod R) (RMod_Zero R) (@RMod_Biproduct R).

#[export] Instance RMod_Cartesian (R : RingObject) : @Cartesian (RMod R) :=
  @biproduct_Cartesian (RMod R) (RMod_Zero R) (RMod_Biproducts R).

#[export] Instance RMod_Cocartesian (R : RingObject) :
  @Cocartesian (RMod R) :=
  @biproduct_Cocartesian (RMod R) (RMod_Zero R) (RMod_Biproducts R).

(** ** Strict identifications *)

Example RMod_coprod_is_prod (R : RingObject) (M N : RModObject R) :
  @Coprod (RMod R) (RMod_Cocartesian R) M N
    = @product_obj (RMod R) (RMod_Cartesian R) M N := eq_refl.

Example RMod_coprod_obj (R : RingObject) (M N : RModObject R) :
  @Coprod (RMod R) (RMod_Cocartesian R) M N = RMod_product M N := eq_refl.

(* The two roster entries agree: the underlying abelian group of the
   direct sum of modules IS the direct sum of the underlying groups, as
   built in Instance/Ab/Coproduct.v. *)
Example RMod_coprod_ab (R : RingObject) (M N : RModObject R) :
  rm_ab (@Coprod (RMod R) (RMod_Cocartesian R) M N)
    = Ab_product M N := eq_refl.

Example RMod_inl_is_Ab_inl (R : RingObject) (M N : RModObject R) :
  rm_hom (@inl (RMod R) (RMod_Cocartesian R) M N) = Ab_inl M N := eq_refl.

Example RMod_inr_is_Ab_inr (R : RingObject) (M N : RModObject R) :
  rm_hom (@inr (RMod R) (RMod_Cocartesian R) M N) = Ab_inr M N := eq_refl.

(** ** Non-vacuity over ℤ ⊕ ℤ as a ℤ-module *)

Definition zmod : RModObject Int_Ring := Ring_RMod Int_Ring.

Lemma rmod_coprod_injections_differ :
  cmon_map (rm_hom (@inl (RMod Int_Ring) (RMod_Cocartesian Int_Ring)
                         zmod zmod)) 1%Z
    ≈ cmon_map (rm_hom (@inr (RMod Int_Ring) (RMod_Cocartesian Int_Ring)
                             zmod zmod)) 1%Z → False.
Proof.
  intros [H _].
  simpl in H.
  discriminate H.
Qed.

Example rmod_coprod_merge_computes :
  cmon_map (rm_hom (@merge (RMod Int_Ring) (RMod_Cocartesian Int_Ring)
                           zmod zmod zmod id id)) (2%Z, 3%Z) = 5%Z :=
  eq_refl.

(* The action on the direct sum is componentwise, and computes. *)
Example rmod_coprod_smul_computes :
  rm_smul (RMod_product zmod zmod) 4%Z (2%Z, 3%Z) = (8%Z, 12%Z) := eq_refl.

Example rmod_coprod_exl_computes :
  cmon_map (rm_hom (RMod_exl zmod zmod)) (2%Z, 3%Z) = 2%Z := eq_refl.

Example rmod_coprod_exr_computes :
  cmon_map (rm_hom (RMod_exr zmod zmod)) (2%Z, 3%Z) = 3%Z := eq_refl.
