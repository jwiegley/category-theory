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
Require Import Coq.ZArith.ZArith.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

(** * The direct sum is the coproduct in Ab *)

(* Book: Mac Lane, "Categories for the Working Mathematician" (2nd ed.),
         §III.3, book p. 63 (maclane:III.3:remark1)
   Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
         §3.2, Example 3.10, printed p. 64 (awodey:3.2:example10)
   Book: Riehl, "Category Theory in Context" (2nd ed.), §3.1,
         printed p. 93 (riehl:3.1:exxi)
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   Mac Lane's §III.3 roster names the direct sum as the coproduct in Ab,
   and Awodey's Example 3.10 says exactly why it is not the free product:
   the free product of abelian groups need not be abelian, so the
   coproduct in Ab is instead carried by the underlying PRODUCT set, with
   injections a ↦ (a, 0) and b ↦ (0, b) and copairing (a, b) ↦ f a + g b.
   That is the semiadditive phenomenon, and Instance/CMon/Biproduct.v had
   already proved every line of it one layer down, for commutative
   monoids.

   HOW MUCH IS INHERITED, MEASURED RATHER THAN ASSERTED.  Instance/Ab.v
   makes [AbObject] extend [CMonObject] by a coercion
   ([ab_cmon :> CMonObject], Instance/Ab.v:116) and — the load-bearing
   choice — defines [AbHom A B := CMonHom A B] as a bare [Definition]
   (Instance/Ab.v:184), with [Ab]'s hom-setoid, identity and composition
   taken from [CMon] literally.  So an arrow of Ab IS an arrow of CMon,
   not merely one up to some comparison.

   The consequence, measured: TEN of the biproduct record's ELEVEN fields
   are supplied by Instance/CMon/Biproduct.v's constants WITH NO ADAPTER
   AT ALL, by [:=] and no tactic — the four structural morphisms, all
   four interaction laws, and both universal properties.  The ONLY new
   field is [biproduct_obj]: [Ab_product] adds the negation
   [(a, b) ↦ (−a, −b)] that a [CMonObject] does not carry, and its two
   obligations are this file's only new proof content.

   AN EARLIER DRAFT OF THIS HEADER GOT THAT WRONG AND IS CORRECTED HERE.
   It claimed that the two interaction laws comparing against [zero_mor]
   "do not transfer" and are "not even well-typed here", on the ground
   that Ab's zero object is [Ab_Zero] while CMon's is [CMon_Zero].  That
   is FALSE, and the falsity is now machine-checked:
   [ab_zero_mor_is_cmon_zero_mor] shows the two zero morphisms are the
   SAME TERM by [eq_refl].  They are, because [Ab_Zero] is assembled from
   [Ab_Terminal] and [Ab_Initial], whose [one] and [zero] fields are
   Instance/Ab.v's [Ab_one] and [Ab_zero_hom] — and those are literally
   [CMon_one] and [CMon_zero_hom] (Instance/Ab.v:238, :252).  So
   [Ab_exl_inr] and [Ab_exr_inl] are [CMon_exl_inr] and [CMon_exr_inl],
   supplied by [:=] like the rest.  The general lesson is the one the
   correction cost: at this depth of inheritance, "different record at a
   different category" is not by itself a reason for anything, and the
   convertibility has to be TESTED rather than reasoned about.

   WHAT IS PROVED, AND AT WHAT STRENGTH.  [Ab_Biproducts] inhabits
   [HasBiproducts Ab] — the first such instance outside CMon — and
   [Structure/Biproduct/Cartesian.v]'s generic bridge then yields
   [Ab_Cartesian] and [Ab_Cocartesian], the tree's first product and
   coproduct structures on Ab (neither existed: no [Ab_Cartesian],
   [Ab_product] or [Ab_Biproduct] occurred anywhere).  The identification
   of the coproduct object with the product object,
   [Ab_coprod_is_prod], holds at LEIBNIZ EQUALITY by [eq_refl], as do the
   readings of [inl], [inr] and [merge] as the concrete maps
   ([Ab_inl_is_pair_zero] and its siblings).  Non-degeneracy is proved
   rather than assumed: over ℤ ⊕ ℤ the two injections have DIFFERENT
   values at the generator ([ab_coprod_injections_differ]), and the
   copairing and both projections COMPUTE on closed input by [eq_refl]
   ([ab_coprod_merge_computes], [ab_coprod_exl_computes],
   [ab_coprod_exr_computes]).

   A UNIVERSE PIN, MEASURED AND ATTRIBUTED BUT NOT REPAIRED.
   [Ab_product@{…}] is universe-polymorphic with thirteen free binders,
   but [Ab_Biproduct@{u} : ∀ M N : AbObject@{Set Set Set}, …] and
   [Ab_Cocartesian@{u} : Cartesian@{u Set}] are PINNED at [Set].  The
   cause is located rather than guessed: Instance/Ab.v:227's [Ab_trivial]
   is declared with NO universe binders, at [AbObject@{Set Set Set}], and
   everything mentioning a zero morphism goes through it via [Ab_Zero].
   The contrast that identifies it is Instance/CMon/Coproduct.v, whose
   [CMon_Cocartesian@{u u0} : Cartesian@{u u0}] is FREE of any [Set] —
   because Instance/CMon/Biproduct.v:72's [CMon_trivial@{o}] IS
   polymorphic.  So the pin is one donor constant's, it enters exactly
   where the zero object does, and it is NOT claimed unavoidable; the
   repair belongs to Instance/Ab.v and is not made here.  Both halves are
   guarded in Test/ProbeCoproduct.v, the negative at [Ab_Biproduct] and
   the control at [Ab_product], each above [Set].

   WHAT IS NOT DELIVERED.  No indexed or infinite direct sums — the
   coproduct here is binary, matching [Cocartesian]; the indexed statement
   would need [HasIndexedCoproducts Ab], which is not built.  No
   [Additive Ab] or [Abelian Ab] instance is claimed: Instance/Ab.v:17
   records that it instantiates none of [Preadditive], [Additive] or
   [Abelian], and while [Structure/AbCategory.v:333] has since supplied
   [Ab_Preadditive], the remaining two need more than biproducts.  And
   nothing is said about coproducts in Grp, where the answer is the free
   product and no part of this file applies — that is exactly Awodey's
   point in Example 3.10, and it is why this file is about Ab. *)

(** ** The direct sum as an object of Ab *)

(* The underlying commutative monoid is [CMon_product]; all that is added
   is the componentwise negation. *)
Program Definition Ab_product (M N : AbObject) : AbObject := {|
  ab_cmon := CMon_product M N;
  ab_neg := fun p => (ab_neg M (fst p), ab_neg N (snd p))
|}.
Next Obligation.
  intros p q [H1 H2].
  split; simpl.
  - now rewrite H1.
  - now rewrite H2.
Qed.
Next Obligation.
  split; simpl; apply ab_neg_left.
Qed.

(** ** The four structural morphisms, inherited on the nose *)

(* [Ab]'s homs, identity and composition ARE [CMon]'s, and the underlying
   commutative monoid of [Ab_product M N] IS [CMon_product M N], so each
   of these four is supplied by [:=] with no tactic and no adapter. *)
Definition Ab_inl (M N : AbObject) : M ~{Ab}~> Ab_product M N :=
  CMon_inl M N.

Definition Ab_inr (M N : AbObject) : N ~{Ab}~> Ab_product M N :=
  CMon_inr M N.

Definition Ab_exl (M N : AbObject) : Ab_product M N ~{Ab}~> M :=
  CMon_exl M N.

Definition Ab_exr (M N : AbObject) : Ab_product M N ~{Ab}~> N :=
  CMon_exr M N.

(* The copairing (a, b) ↦ f a + g b — Awodey's formula — likewise. *)
Definition Ab_copair {M N P : AbObject}
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) : Ab_product M N ~{Ab}~> P :=
  CMon_copair f g.

(** ** The zero morphism of Ab is CMon's *)

(* The fact that makes the two [zero_mor] laws transfer: Ab's zero
   morphism and CMon's are the same term, [Ab_Zero]'s [one] and [zero]
   being [CMon_one] and [CMon_zero_hom] (Instance/Ab.v:238, :252) and
   Ab's composition being CMon's. *)
Example ab_zero_mor_is_cmon_zero_mor (M N : AbObject) :
  @zero_mor Ab Ab_Zero M N = @zero_mor CMon CMon_Zero M N := eq_refl.

(* Its value at a point, for readability at the use sites downstream. *)
Lemma ab_zero_mor_value (M N : AbObject) (a : carrier (cmon_setoid M)) :
  cmon_map (@zero_mor Ab Ab_Zero M N) a ≈ cmon_zero N.
Proof.
  simpl.
  apply (cmon_map_zero (Ab_zero_hom N)).
Qed.

(** ** The four interaction laws, all four inherited on the nose *)

Definition Ab_exl_inl (M N : AbObject) :
  Ab_exl M N ∘ Ab_inl M N ≈ id := CMon_exl_inl M N.

Definition Ab_exr_inr (M N : AbObject) :
  Ab_exr M N ∘ Ab_inr M N ≈ id := CMon_exr_inr M N.

Definition Ab_exl_inr (M N : AbObject) :
  Ab_exl M N ∘ Ab_inr M N ≈ @zero_mor Ab Ab_Zero N M := CMon_exl_inr M N.

Definition Ab_exr_inl (M N : AbObject) :
  Ab_exr M N ∘ Ab_inl M N ≈ @zero_mor Ab Ab_Zero M N := CMon_exr_inl M N.

(** ** Both universal properties, inherited on the nose *)

(* The ∃! ranges over [Ab_product M N ~{Ab}~> P], which IS
   [CMon_product M N ~{CMon}~> P]; its equality is [CMonHom_Setoid], which
   IS Ab's; and the composites are [cmon_hom_compose], which IS Ab's.  So
   both universal properties are the CMon ones, verbatim. *)
Definition Ab_is_product (M N P : AbObject)
  (f : P ~{Ab}~> M) (g : P ~{Ab}~> N) :
  ∃! h : P ~{Ab}~> Ab_product M N,
    (Ab_exl M N ∘ h ≈ f) ∧ (Ab_exr M N ∘ h ≈ g) :=
  CMon_bi_is_product M N P f g.

Definition Ab_is_coproduct (M N P : AbObject)
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) :
  ∃! h : Ab_product M N ~{Ab}~> P,
    (h ∘ Ab_inl M N ≈ f) ∧ (h ∘ Ab_inr M N ≈ g) :=
  CMon_bi_is_coproduct M N P f g.

(** ** The biproduct, and with it the product and coproduct structures *)

Definition Ab_Biproduct (M N : AbObject) : @Biproduct Ab Ab_Zero M N :=
  @Build_Biproduct Ab Ab_Zero M N
    (Ab_product M N)
    (Ab_inl M N)
    (Ab_inr M N)
    (Ab_exl M N)
    (Ab_exr M N)
    (Ab_exl_inl M N)
    (Ab_exr_inr M N)
    (Ab_exl_inr M N)
    (Ab_exr_inl M N)
    (Ab_is_product M N)
    (Ab_is_coproduct M N).

#[export] Instance Ab_Biproducts : @HasBiproducts Ab Ab_Zero :=
  @Build_HasBiproducts Ab Ab_Zero Ab_Biproduct.

(* Mac Lane's roster entry.  [Cocartesian Ab] is the deliverable; the
   cartesian structure comes with it, from the same biproduct. *)
#[export] Instance Ab_Cartesian : @Cartesian Ab :=
  @biproduct_Cartesian Ab Ab_Zero Ab_Biproducts.

#[export] Instance Ab_Cocartesian : @Cocartesian Ab :=
  @biproduct_Cocartesian Ab Ab_Zero Ab_Biproducts.

(** ** Strict identifications *)

(* Awodey's Example 3.10 in one conversion: the coproduct of two abelian
   groups IS their product, the same object, not merely isomorphic to it. *)
Example Ab_coprod_is_prod (M N : AbObject) :
  @Coprod Ab Ab_Cocartesian M N = @product_obj Ab Ab_Cartesian M N :=
  eq_refl.

Example Ab_coprod_obj (M N : AbObject) :
  @Coprod Ab Ab_Cocartesian M N = Ab_product M N := eq_refl.

(* And the injections and the copairing are the concrete maps. *)
Example Ab_inl_is_pair_zero (M N : AbObject) :
  @inl Ab Ab_Cocartesian M N = CMon_inl M N := eq_refl.

Example Ab_inr_is_zero_pair (M N : AbObject) :
  @inr Ab Ab_Cocartesian M N = CMon_inr M N := eq_refl.

Example Ab_merge_is_copair (M N P : AbObject)
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) :
  @merge Ab Ab_Cocartesian P M N f g = CMon_copair f g := eq_refl.

(* The underlying set of the coproduct is the PRODUCT of the underlying
   sets — the sentence Awodey uses to distinguish Ab from Grp. *)
Example Ab_coprod_carrier (M N : AbObject) :
  carrier (cmon_setoid (@Coprod Ab Ab_Cocartesian M N))
    = (carrier (cmon_setoid M) * carrier (cmon_setoid N))%type := eq_refl.

(** ** Non-vacuity over ℤ ⊕ ℤ *)

(* [Instance/Rng.v]'s [ring_ab] reads the additive group off a ring, and
   [Theory/Algebra/Rig.v]'s [Int_Ring] is the axiom-free integers, so ℤ is
   available as an abelian group with no new construction. *)
Definition ab_Z : AbObject := ring_ab Int_Ring.

(* The two injections are genuinely different maps: at the generator 1
   they land at (1, 0) and at (0, 1). *)
Lemma ab_coprod_injections_differ :
  cmon_map (@inl Ab Ab_Cocartesian ab_Z ab_Z) 1%Z
    ≈ cmon_map (@inr Ab Ab_Cocartesian ab_Z ab_Z) 1%Z → False.
Proof.
  intros [H _].
  simpl in H.
  discriminate H.
Qed.

(* And the copairing computes: with both legs the identity it is
   Awodey's (a, b) ↦ f a + g b, i.e. addition. *)
Example ab_coprod_merge_computes :
  cmon_map (@merge Ab Ab_Cocartesian ab_Z ab_Z ab_Z id id) (2%Z, 3%Z)
    = 5%Z := eq_refl.

(* The two summands are not collapsed by the copairing either: the
   projections separate them. *)
Example ab_coprod_exl_computes :
  cmon_map (Ab_exl ab_Z ab_Z) (2%Z, 3%Z) = 2%Z := eq_refl.

Example ab_coprod_exr_computes :
  cmon_map (Ab_exr ab_Z ab_Z) (2%Z, 3%Z) = 3%Z := eq_refl.
