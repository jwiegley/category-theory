Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Semiadditive.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.

Generalizable All Variables.

(** * CMon is semiadditive: zero object, biproducts, CMon-enrichment *)

(* nLab:      https://ncatlab.org/nlab/show/semiadditive+category
   nLab:      https://ncatlab.org/nlab/show/biproduct
   nLab:      https://ncatlab.org/nlab/show/CMon
   Wikipedia: https://en.wikipedia.org/wiki/Biproduct

   [CMon] is the archetypal semiadditive category.  This file exhibits the
   three layers of that structure concretely:

   - [CMon_Zero]: the trivial (one-element) monoid is a zero object.  It is
     terminal (everything maps to the point) and initial (the point maps to
     the unit of any monoid, and any homomorphism out of it is forced to do
     the same by [cmon_map_zero]); since one record plays both roles, the
     coincidence isomorphism is the identity.

   - [CMon_Biproducts]: the direct product M ⊕ N (product setoid,
     componentwise operation) is simultaneously a product — with the
     projections [fst], [snd] and the pairing a ↦ (f a, g a) — and a
     coproduct — with the injections a ↦ (a, 0) and b ↦ (0, b) and the
     copairing (a, b) ↦ f a + g b.  Commutativity of + enters exactly where
     the theory predicts: the copairing is a homomorphism by the
     middle-four interchange [cmon_plus_interchange], and its uniqueness
     uses that any candidate is itself a homomorphism.

   - [CMon_Preadditive]: hom-setoids are commutative monoids under the
     pointwise addition (f + g) a := f a + g a with unit the constant-zero
     homomorphism; composition distributes on both sides.  ROUTE NOTE: the
     enrichment is defined directly by this pointwise formula (the honest,
     carrier-level route) rather than derived through
     [bicartesian_preadditive]; the connection to the phase machinery is
     then proved, not assumed: [CMon_padd_biproduct] instantiates
     [biproduct_addition] of Structure/Semiadditive.v at [CMon_Biproducts]
     and shows the pointwise addition agrees with the biproduct convolution
     ∇ ∘ (f ⊕ g) ∘ Δ. *)

(* The middle-four interchange for a commutative monoid: rebracketing a sum
   of four terms so that the outer pairs swap partners.  This is the single
   algebraic identity behind the copairing homomorphism law and the
   pointwise-addition homomorphism law below. *)
Lemma cmon_plus_interchange (P : CMonObject) (a b c d : carrier P) :
  cmon_plus P (cmon_plus P a b) (cmon_plus P c d)
    ≈ cmon_plus P (cmon_plus P a c) (cmon_plus P b d).
Proof.
  rewrite cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc P b c d).
  rewrite (cmon_plus_comm P b c).
  rewrite (cmon_plus_assoc P c b d).
  rewrite <- cmon_plus_assoc.
  reflexivity.
Qed.

(** ** The zero object: the trivial monoid *)

(* The one-element commutative monoid on [poly_unit]: the operation and the
   unit are both the point, and every law holds by computation. *)
Definition CMon_trivial@{o} : CMonObject@{o o o}.
Proof.
  unshelve notypeclasses refine {|
    cmon_setoid := {| carrier := poly_unit@{o}; is_setoid := unit_setoid@{o o} |};
    cmon_zero := ttt;
    cmon_plus := fun _ _ => ttt
  |}.
  - (* cmon_plus_respects *)
    intros x y Hxy u v Huv.
    reflexivity.
  - (* cmon_plus_assoc *)
    intros a b c.
    reflexivity.
  - (* cmon_plus_comm *)
    intros a b.
    reflexivity.
  - (* cmon_plus_zero_l *)
    intros a.
    destruct a.
    reflexivity.
Defined.

(* The unique homomorphism into the trivial monoid: everything to the
   point. *)
Definition CMon_one@{u o} (M : CMonObject@{o o o}) : M ~{CMon@{u o}}~> CMon_trivial@{o}.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom M CMon_trivial
       {| morphism := fun _ => ttt |} _ _).
  - (* proper_morphism *)
    intros a b Hab.
    reflexivity.
  - (* cmon_map_zero *)
    reflexivity.
  - (* cmon_map_plus *)
    intros a b.
    reflexivity.
Defined.

(* Uniqueness into the trivial monoid: both images live in [poly_unit]. *)
Lemma CMon_one_unique@{u o} (M : CMonObject@{o o o})
  (f g : M ~{CMon@{u o}}~> CMon_trivial@{o}) : f ≈ g.
Proof.
  intro a.
  destruct (cmon_map f a), (cmon_map g a).
  reflexivity.
Qed.

Definition CMon_Terminal : @Terminal CMon :=
  @Build_Terminal CMon CMon_trivial CMon_one CMon_one_unique.

(* The unique homomorphism out of the trivial monoid: the point goes to the
   unit — the only unit-preserving choice. *)
Definition CMon_zero_hom@{u o} (M : CMonObject@{o o o}) : CMon_trivial@{o} ~{CMon@{u o}}~> M.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom CMon_trivial M
       {| morphism := fun _ => cmon_zero M |} _ _).
  - (* proper_morphism *)
    intros a b Hab.
    reflexivity.
  - (* cmon_map_zero *)
    reflexivity.
  - (* cmon_map_plus *)
    intros a b.
    symmetry.
    apply cmon_plus_zero_l.
Defined.

(* Uniqueness out of the trivial monoid: the point is the unit, and any
   homomorphism sends units to units ([cmon_map_zero]). *)
Lemma CMon_zero_hom_unique@{u o} (M : CMonObject@{o o o})
  (f g : CMon_trivial@{o} ~{CMon@{u o}}~> M) : f ≈ g.
Proof.
  intro a.
  destruct a.
  transitivity (cmon_zero M).
  - exact (cmon_map_zero f).
  - symmetry.
    exact (cmon_map_zero g).
Qed.

Definition CMon_Initial : @Initial CMon :=
  @Build_Terminal (CMon^op) CMon_trivial CMon_zero_hom CMon_zero_hom_unique.

(* The trivial monoid is a zero object.  The same record [CMon_trivial]
   carries both the terminal and the initial structure, so the coincidence
   isomorphism is the identity. *)
#[export] Instance CMon_Zero : ZeroObject CMon :=
  @Build_ZeroObject CMon CMon_Terminal CMon_Initial iso_id.

(** ** Biproducts: the direct product of commutative monoids *)

(* The direct product M ⊕ N: the product setoid with componentwise unit and
   operation. *)
Definition CMon_product (M N : CMonObject) : CMonObject.
Proof.
  unshelve notypeclasses refine {|
    cmon_setoid := {| carrier := (carrier M * carrier N)%type
                    ; is_setoid := @prod_setoid _ _
                        (is_setoid (cmon_setoid M))
                        (is_setoid (cmon_setoid N)) |};
    cmon_zero := (cmon_zero M, cmon_zero N);
    cmon_plus := fun p q =>
      (cmon_plus M (fst p) (fst q), cmon_plus N (snd p) (snd q))
  |}.
  - (* cmon_plus_respects *)
    intros p p' Hp q q' Hq.
    destruct Hp as [Hp1 Hp2], Hq as [Hq1 Hq2].
    split.
    + simpl.
      now rewrite Hp1, Hq1.
    + simpl.
      now rewrite Hp2, Hq2.
  - (* cmon_plus_assoc *)
    intros a b c.
    split.
    + simpl.
      apply cmon_plus_assoc.
    + simpl.
      apply cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros a b.
    split.
    + simpl.
      apply cmon_plus_comm.
    + simpl.
      apply cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros a.
    split.
    + simpl.
      apply cmon_plus_zero_l.
    + simpl.
      apply cmon_plus_zero_l.
Defined.

(* Left injection a ↦ (a, 0): a homomorphism because 0 ≈ 0 + 0. *)
Definition CMon_inl (M N : CMonObject) : M ~{CMon}~> CMon_product M N.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom M (CMon_product M N)
       {| morphism := fun a => (a, cmon_zero N) |} _ _).
  - (* proper_morphism *)
    intros a b Hab.
    split.
    + exact Hab.
    + reflexivity.
  - (* cmon_map_zero *)
    reflexivity.
  - (* cmon_map_plus *)
    intros a b.
    split.
    + simpl.
      reflexivity.
    + simpl.
      symmetry.
      apply cmon_plus_zero_l.
Defined.

(* Right injection b ↦ (0, b). *)
Definition CMon_inr (M N : CMonObject) : N ~{CMon}~> CMon_product M N.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom N (CMon_product M N)
       {| morphism := fun b => (cmon_zero M, b) |} _ _).
  - (* proper_morphism *)
    intros a b Hab.
    split.
    + reflexivity.
    + exact Hab.
  - (* cmon_map_zero *)
    reflexivity.
  - (* cmon_map_plus *)
    intros a b.
    split.
    + simpl.
      symmetry.
      apply cmon_plus_zero_l.
    + simpl.
      reflexivity.
Defined.

(* Left projection [fst]: a homomorphism on the nose. *)
Definition CMon_exl (M N : CMonObject) : CMon_product M N ~{CMon}~> M.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom (CMon_product M N) M
       {| morphism := fun p => fst p |} _ _).
  - (* proper_morphism *)
    intros p q Hpq.
    destruct Hpq as [H1 H2].
    exact H1.
  - (* cmon_map_zero *)
    reflexivity.
  - (* cmon_map_plus *)
    intros p q.
    reflexivity.
Defined.

(* Right projection [snd]. *)
Definition CMon_exr (M N : CMonObject) : CMon_product M N ~{CMon}~> N.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom (CMon_product M N) N
       {| morphism := fun p => snd p |} _ _).
  - (* proper_morphism *)
    intros p q Hpq.
    destruct Hpq as [H1 H2].
    exact H2.
  - (* cmon_map_zero *)
    reflexivity.
  - (* cmon_map_plus *)
    intros p q.
    reflexivity.
Defined.

(* The four interaction laws.  The matched composites are identities by
   computation; the mixed composites compute to the constant-zero map, which
   is precisely what [zero_mor] tunnelled through [CMon_trivial] unfolds
   to. *)
Lemma CMon_exl_inl (M N : CMonObject) :
  CMon_exl M N ∘ CMon_inl M N ≈ id.
Proof.
  intro a.
  reflexivity.
Qed.

Lemma CMon_exr_inr (M N : CMonObject) :
  CMon_exr M N ∘ CMon_inr M N ≈ id.
Proof.
  intro b.
  reflexivity.
Qed.

Lemma CMon_exl_inr (M N : CMonObject) :
  CMon_exl M N ∘ CMon_inr M N ≈ zero_mor.
Proof.
  intro b.
  reflexivity.
Qed.

Lemma CMon_exr_inl (M N : CMonObject) :
  CMon_exr M N ∘ CMon_inl M N ≈ zero_mor.
Proof.
  intro a.
  reflexivity.
Qed.

(* The product mediator a ↦ (f a, g a): componentwise a homomorphism. *)
Definition CMon_pair {M N P : CMonObject}
  (f : P ~{CMon}~> M) (g : P ~{CMon}~> N) :
  P ~{CMon}~> CMon_product M N.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom P (CMon_product M N)
       {| morphism := fun a => (cmon_map f a, cmon_map g a) |} _ _).
  - (* proper_morphism *)
    intros a b Hab.
    split.
    + simpl.
      now rewrite Hab.
    + simpl.
      now rewrite Hab.
  - (* cmon_map_zero *)
    split.
    + simpl.
      exact (cmon_map_zero f).
    + simpl.
      exact (cmon_map_zero g).
  - (* cmon_map_plus *)
    intros a b.
    split.
    + simpl.
      exact (cmon_map_plus f a b).
    + simpl.
      exact (cmon_map_plus g a b).
Defined.

(* The product-side universal property: (M ⊕ N, exl, exr) is a product. *)
Definition CMon_bi_is_product (M N P : CMonObject)
  (f : P ~{CMon}~> M) (g : P ~{CMon}~> N) :
  ∃! h : P ~{CMon}~> CMon_product M N,
    (CMon_exl M N ∘ h ≈ f) ∧ (CMon_exr M N ∘ h ≈ g).
Proof.
  unshelve refine {| unique_obj := CMon_pair f g |}.
  - split.
    + intro a.
      reflexivity.
    + intro a.
      reflexivity.
  - intros v Hv.
    destruct Hv as [Hl Hr].
    intro a.
    split.
    + symmetry.
      exact (Hl a).
    + symmetry.
      exact (Hr a).
Defined.

(* The coproduct mediator (a, b) ↦ f a + g b.  This is where commutativity
   of the target's addition is indispensable: preservation of + is the
   middle-four interchange. *)
Definition CMon_copair {M N P : CMonObject}
  (f : M ~{CMon}~> P) (g : N ~{CMon}~> P) :
  CMon_product M N ~{CMon}~> P.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom (CMon_product M N) P
       {| morphism := fun p =>
            cmon_plus P (cmon_map f (fst p)) (cmon_map g (snd p)) |} _ _).
  - (* proper_morphism *)
    intros p q Hpq.
    destruct Hpq as [H1 H2].
    simpl.
    now rewrite H1, H2.
  - (* cmon_map_zero *)
    simpl.
    rewrite (cmon_map_zero f), (cmon_map_zero g).
    apply cmon_plus_zero_l.
  - (* cmon_map_plus *)
    intros p q.
    simpl.
    rewrite (cmon_map_plus f), (cmon_map_plus g).
    apply cmon_plus_interchange.
Defined.

(* The coproduct-side universal property: (M ⊕ N, inl, inr) is a coproduct.
   Existence is the copairing; uniqueness decomposes (a, b) as
   (a, 0) + (0, b) and uses that any candidate mediator is itself a
   homomorphism. *)
Definition CMon_bi_is_coproduct (M N P : CMonObject)
  (f : M ~{CMon}~> P) (g : N ~{CMon}~> P) :
  ∃! h : CMon_product M N ~{CMon}~> P,
    (h ∘ CMon_inl M N ≈ f) ∧ (h ∘ CMon_inr M N ≈ g).
Proof.
  unshelve refine {| unique_obj := CMon_copair f g |}.
  - split.
    + intro a.
      simpl.
      rewrite (cmon_map_zero g).
      apply cmon_plus_zero_r.
    + intro b.
      simpl.
      rewrite (cmon_map_zero f).
      apply cmon_plus_zero_l.
  - intros v Hv.
    destruct Hv as [Hl Hr].
    intros [a b].
    simpl.
    symmetry.
    transitivity
      (cmon_map v
        (cmon_plus (CMon_product M N) (a, cmon_zero N) (cmon_zero M, b))).
    + apply (proper_morphism (cmon_map v)).
      split.
      * simpl.
        symmetry.
        apply cmon_plus_zero_r.
      * simpl.
        symmetry.
        apply cmon_plus_zero_l.
    + rewrite (cmon_map_plus v).
      apply cmon_plus_respects.
      * exact (Hl a).
      * exact (Hr b).
Defined.

(* The direct product assembled as a biproduct. *)
Definition CMon_Biproduct (M N : CMonObject) :
  @Biproduct CMon CMon_Zero M N :=
  @Build_Biproduct CMon CMon_Zero M N
    (CMon_product M N)
    (CMon_inl M N)
    (CMon_inr M N)
    (CMon_exl M N)
    (CMon_exr M N)
    (CMon_exl_inl M N)
    (CMon_exr_inr M N)
    (CMon_exl_inr M N)
    (CMon_exr_inl M N)
    (CMon_bi_is_product M N)
    (CMon_bi_is_coproduct M N).

#[export] Instance CMon_Biproducts : @HasBiproducts CMon CMon_Zero :=
  @Build_HasBiproducts CMon CMon_Zero CMon_Biproduct.

(** ** The CMon-enrichment: pointwise addition of homomorphisms *)

(* Pointwise addition (f + g) a := f a + g a.  Preservation of + is again
   the middle-four interchange; preservation of 0 is 0 + 0 ≈ 0. *)
Definition CMon_padd {M N : CMonObject}
  (f g : M ~{CMon}~> N) : M ~{CMon}~> N.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom M N
       {| morphism := fun a =>
            cmon_plus N (cmon_map f a) (cmon_map g a) |} _ _).
  - (* proper_morphism *)
    intros a b Hab.
    simpl.
    now rewrite Hab.
  - (* cmon_map_zero *)
    simpl.
    rewrite (cmon_map_zero f), (cmon_map_zero g).
    apply cmon_plus_zero_l.
  - (* cmon_map_plus *)
    intros a b.
    simpl.
    rewrite (cmon_map_plus f), (cmon_map_plus g).
    apply cmon_plus_interchange.
Defined.

(* The constant-zero homomorphism, the unit for pointwise addition. *)
Definition CMon_pzero (M N : CMonObject) : M ~{CMon}~> N.
Proof.
  unshelve notypeclasses refine
    (Build_CMonHom M N
       {| morphism := fun _ => cmon_zero N |} _ _).
  - (* proper_morphism *)
    intros a b Hab.
    reflexivity.
  - (* cmon_map_zero *)
    reflexivity.
  - (* cmon_map_plus *)
    intros a b.
    symmetry.
    apply cmon_plus_zero_l.
Defined.

(* The commutative-monoid laws for the hom-setoids, all pointwise. *)
Lemma CMon_padd_respects {M N : CMonObject} :
  Proper (equiv ==> equiv ==> equiv) (@CMon_padd M N).
Proof.
  intros f f' Hf g g' Hg a.
  simpl.
  now rewrite (Hf a), (Hg a).
Qed.

Lemma CMon_padd_assoc {M N : CMonObject} (f g h : M ~{CMon}~> N) :
  CMon_padd (CMon_padd f g) h ≈ CMon_padd f (CMon_padd g h).
Proof.
  intro a.
  simpl.
  apply cmon_plus_assoc.
Qed.

Lemma CMon_padd_comm {M N : CMonObject} (f g : M ~{CMon}~> N) :
  CMon_padd f g ≈ CMon_padd g f.
Proof.
  intro a.
  simpl.
  apply cmon_plus_comm.
Qed.

Lemma CMon_padd_zero_left {M N : CMonObject} (f : M ~{CMon}~> N) :
  CMon_padd (CMon_pzero M N) f ≈ f.
Proof.
  intro a.
  simpl.
  apply cmon_plus_zero_l.
Qed.

(* Composition is additive in each argument: on the left because the outer
   homomorphism preserves +, on the right by computation. *)
Lemma CMon_compose_padd_left {M N P : CMonObject}
  (h : N ~{CMon}~> P) (f g : M ~{CMon}~> N) :
  h ∘ CMon_padd f g ≈ CMon_padd (h ∘ f) (h ∘ g).
Proof.
  intro a.
  simpl.
  exact (cmon_map_plus h (cmon_map f a) (cmon_map g a)).
Qed.

Lemma CMon_compose_padd_right {M N P : CMonObject}
  (f g : N ~{CMon}~> P) (h : M ~{CMon}~> N) :
  CMon_padd f g ∘ h ≈ CMon_padd (f ∘ h) (g ∘ h).
Proof.
  intro a.
  reflexivity.
Qed.

(* The constant-zero homomorphism absorbs composition on both sides. *)
Lemma CMon_compose_pzero_left {M N P : CMonObject} (f : M ~{CMon}~> N) :
  CMon_pzero N P ∘ f ≈ CMon_pzero M P.
Proof.
  intro a.
  reflexivity.
Qed.

Lemma CMon_compose_pzero_right {M N P : CMonObject} (f : N ~{CMon}~> P) :
  f ∘ CMon_pzero M N ≈ CMon_pzero M P.
Proof.
  intro a.
  exact (cmon_map_zero f).
Qed.

(* CMon is preadditive in the CMon-enriched sense of
   Structure/Preadditive.v: each hom-setoid is a commutative monoid and
   composition is bi-additive. *)
#[export] Instance CMon_Preadditive : Preadditive CMon :=
  @Build_Preadditive CMon
    (@CMon_padd)
    CMon_pzero
    (@CMon_padd_respects)
    (@CMon_padd_assoc)
    (@CMon_padd_comm)
    (@CMon_padd_zero_left)
    (@CMon_compose_padd_left)
    (@CMon_compose_padd_right)
    (@CMon_compose_pzero_left)
    (@CMon_compose_pzero_right).

(** ** Integration with the phase machinery *)

(* The pointwise addition agrees with the biproduct convolution
   ∇ ∘ (f ⊕ g) ∘ Δ: this is [biproduct_addition] of
   Structure/Semiadditive.v instantiated at [CMon_Biproducts], confirming
   that the concrete enrichment above is the one the abstract theory
   induces from the biproducts. *)
Theorem CMon_padd_biproduct {M N : CMonObject} (f g : M ~{CMon}~> N) :
  CMon_padd f g
    ≈ bi_copair (@biproduct CMon CMon_Zero CMon_Biproducts N N) id id
        ∘ bimap (@biproduct CMon CMon_Zero CMon_Biproducts M M)
                (@biproduct CMon CMon_Zero CMon_Biproducts N N) f g
        ∘ bi_pair (@biproduct CMon CMon_Zero CMon_Biproducts M M) id id.
Proof.
  exact (@biproduct_addition CMon CMon_Zero CMon_Preadditive M N
           (@biproduct CMon CMon_Zero CMon_Biproducts M M)
           (@biproduct CMon CMon_Zero CMon_Biproducts N N) f g).
Qed.
