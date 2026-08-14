(** * Ab-enrichment: Enriched over (Ab, ⊗, ℤ) is exactly AbEnriched *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §I.8, printed pp. 28–29 (PDF pp. 38–39) — maclane:I.8:def5
   nLab:      https://ncatlab.org/nlab/show/Ab-enriched+category
   Wikipedia: https://en.wikipedia.org/wiki/Preadditive_category

   Mac Lane's remark after the tensor-data definition: an Ab-category
   "can be described completely in these terms" — hom-groups, composition
   morphisms A(b,c) ⊗ A(a,b) → A(a,c), and units ℤ → A(a,a) subject to
   associativity and unit laws.  With Instance/Ab/Tensor.v's tensor and
   Instance/Ab/Monoidal.v's monoidal structure in hand, that remark is a
   theorem of this library:

     [Enriched_Ab_iff_AbEnriched :
        @Enriched Ab Ab_Monoidal ↔ { C : Category & AbEnriched C }]

   in the same Type-valued-↔ form as Construction/Enriched.v's
   [Category_is_Enriched_over_Set] and Construction/Enriched/Two.v's
   [Enriched_Two_preorder].  The two directions:

     - [Enriched_of_AbEnriched]: an [AbEnriched] category (the direct
       Structure/AbCategory.v class) yields tensor data — hom-objects
       are the hom-groups, [eid] sends n to n·id by the integer action,
       [ecompose] is the ⊗-factorization of composition, whose
       bilinearity is exactly [compose_padd_left]/[compose_padd_right].
     - [Category_of_Enriched_Ab] + [AbEnriched_of_Enriched_Ab]: tensor
       data yields a category — composition is [ecompose] at a
       generator, identity is [eid] at 1 — that is [AbEnriched], its
       bilinearity read back off the generator relations of the tensor.

   Design:

   1. EVERY LAW IS A GENERATOR COMPUTATION.  In the forward direction
      the three enrichment equations are morphism equalities out of
      (iterated) tensors, so [tensor_hom_ext]/[tensor_hom_ext2] reduce
      them to generators, where the mediators compute: the unit laws
      become the integer-action equations n·id ∘ f ≈ n·f (an instance
      of [zsmul_hom] at the pre/postcomposition homomorphisms) and the
      associativity equation becomes [comp_assoc].  In the reverse
      direction the SAME three equations are consumed at generator
      arguments, where they compute to the category laws being built.

   2. PRE/POSTCOMPOSITION ARE HOMOMORPHISMS.  [precomp_hom]/
      [postcomp_hom] package (− ∘ f) and (g ∘ −) as [AbHom]s of the
      hom-groups — their additivity is the other half of bilinearity —
      so the ℤ-action bridge n·g ∘ f ≈ n·(g ∘ f) is one application of
      Instance/Ab/Monoidal.v's [zsmul_hom] rather than a fresh
      induction.

   3. BOTH DIRECTIONS ARE IDENTITY ON OBJECTS AND HOM-CARRIERS.  The
      forward direction sets [eobj := obj[C]] and the carrier of each
      hom-object to [x ~> y] itself; the reverse reads them back
      unchanged, and composition at a generator reduces to the original
      [∘].  The correspondence is thus a repackaging of the same data —
      which is exactly Mac Lane's claim — with no equivalence-of-
      categories apparatus invoked, and [Enriched_Ab_itself] below
      exercises the forward direction at the concrete [Ab_AbEnriched].
      (Bare [1%Z] at [carrier ZAb] positions is harmless here because
      the [@ts_gen ZAb …] applications pin the object first, so the
      projection reduces to [Z] before the literal is matched —
      Instance/Ab/Monoidal.v's header note on [ZAb_one] scopes the
      danger to unresolved [carrier ?G] evars.)

   4. NOTHING IS ASSUMED BEYOND THE CLASSES.  Both directions are
      constructions, closed under the global context; the reverse
      direction never inspects [eobj] and the forward one never
      inspects the ambient category beyond its [AbEnriched] fields. *)

Require Import Coq.ZArith.BinInt.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Ab.Monoidal.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** From an AbEnriched category to tensor data *)

Section FromAbEnriched.

Context {C : Category} {A : AbEnriched C}.

(* The hom-group of a hom-set: Structure/AbCategory.v's fields, packaged
   as an object of Ab. *)
Definition ehom_ab (x y : C) : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := x ~> y; is_setoid := @homset C x y |};
    cmon_zero := @pzero C _ x y;
    cmon_plus := @padd C _ x y;
    cmon_plus_respects := @padd_respects C _ x y;
    cmon_plus_assoc := @padd_assoc C _ x y;
    cmon_plus_comm := @padd_comm C _ x y;
    cmon_plus_zero_l := @padd_zero_left C _ x y
  |};
  ab_neg := @abneg C A x y;
  ab_neg_respects := @abneg_respects C A x y;
  ab_neg_left := fun f =>
    transitivity (@padd_comm C _ x y (abneg f) f) (padd_abneg f)
|}.

(* Precomposition with f, as a homomorphism of hom-groups: additivity is
   [compose_padd_right], zero-preservation [compose_pzero_left]. *)
Program Definition precomp_hom {x y z : C} (f : x ~> y) :
  AbHom (ehom_ab y z) (ehom_ab x z) := {|
  cmon_map := {| morphism := fun g : y ~> z => g ∘ f |}
|}.
Next Obligation.
  intros x y z f g g' Hg.
  exact (compose_respects _ _ Hg _ _ (reflexivity f)).
Qed.
Next Obligation.
  intros x y z f; simpl.
  exact (@compose_pzero_left C _ x y z f).
Qed.
Next Obligation.
  intros x y z f g g'; simpl.
  exact (@compose_padd_right C _ x y z g g' f).
Qed.

(* Postcomposition with g, likewise: [compose_padd_left] and
   [compose_pzero_right]. *)
Program Definition postcomp_hom {x y z : C} (g : y ~> z) :
  AbHom (ehom_ab x y) (ehom_ab x z) := {|
  cmon_map := {| morphism := fun f : x ~> y => g ∘ f |}
|}.
Next Obligation.
  intros x y z g f f' Hf.
  exact (compose_respects _ _ (reflexivity g) _ _ Hf).
Qed.
Next Obligation.
  intros x y z g; simpl.
  exact (@compose_pzero_right C _ x y z g).
Qed.
Next Obligation.
  intros x y z g f f'; simpl.
  exact (@compose_padd_left C _ x y z g f f').
Qed.

(* The ℤ-action commutes with composition on either side — instances of
   [zsmul_hom] at the two homomorphisms above (design note 2). *)
Lemma zsmul_precomp {x y z : C} (n : Z) (g : y ~> z) (f : x ~> y) :
  zsmul (ehom_ab y z) n g ∘ f ≈ zsmul (ehom_ab x z) n (g ∘ f).
Proof.
  exact (zsmul_hom (precomp_hom f) n g).
Qed.

Lemma zsmul_postcomp {x y z : C} (n : Z) (g : y ~> z) (f : x ~> y) :
  g ∘ zsmul (ehom_ab x y) n f ≈ zsmul (ehom_ab x z) n (g ∘ f).
Proof.
  exact (zsmul_hom (postcomp_hom g) n f).
Qed.

(* The unit ℤ → A(x,x): n ↦ n·id.  Additivity in n is [zsmul_add]. *)
Program Definition ab_eid (x : C) : AbHom ZAb (ehom_ab x x) := {|
  cmon_map := {| morphism := fun n : Z => zsmul (ehom_ab x x) n (@id C x) |}
|}.
Next Obligation.
  intros x n m Hnm.
  rewrite (ZAb_eq n m Hnm).
  reflexivity.
Qed.
Next Obligation.
  intros x; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x n m; simpl.
  exact (zsmul_add (ehom_ab x x) n m (@id C x)).
Qed.

(* Composition A(y,z) ⊗ A(x,y) → A(x,z): the ⊗-factorization of ∘, its
   bilinearity the two composition-bilinearity fields of Preadditive. *)
Program Definition ab_ecompose (x y z : C) :
  AbHom (AbTensor (ehom_ab y z) (ehom_ab x y)) (ehom_ab x z) :=
  tensor_ump (@Build_Bilinear (ehom_ab y z) (ehom_ab x y) (ehom_ab x z)
    (fun g f => g ∘ f) _ _ _).
Next Obligation.
  intros x y z g g' f; simpl.
  exact (@compose_padd_right C _ x y z g g' f).
Qed.
Next Obligation.
  intros x y z g f f'; simpl.
  exact (@compose_padd_left C _ x y z g f f').
Qed.

(* The enrichment.  Each equation is [tensor_hom_ext] to generators, a
   mediator computation, and a category/action law (design note 1). *)
Definition Enriched_of_AbEnriched : @Enriched Ab Ab_Monoidal.
Proof using A C.
  unshelve refine
    (@Build_Enriched Ab Ab_Monoidal obj[C] ehom_ab ab_eid ab_ecompose
       _ _ _).
  - (* eid_left : ecompose ∘ eid ⨂ id ≈ unit_left *)
    intros x y s; revert s.
    apply tensor_hom_ext.
    intros n f; simpl.
    refine (transitivity (zsmul_precomp n (@id C y) f) _).
    exact (zsmul_respects (ehom_ab x y) n _ _ (id_left f)).
  - (* eid_right : ecompose ∘ id ⨂ eid ≈ unit_right *)
    intros x y s; revert s.
    apply tensor_hom_ext.
    intros f n; simpl.
    refine (transitivity (zsmul_postcomp n f (@id C x)) _).
    exact (zsmul_respects (ehom_ab x y) n _ _ (id_right f)).
  - (* ecompose_assoc *)
    intros x y z w s; revert s.
    apply tensor_hom_ext2.
    intros h g f; simpl.
    exact (symmetry (comp_assoc h g f)).
Defined.

End FromAbEnriched.

(** ** From tensor data to an AbEnriched category *)

Section ToAbEnriched.

Context (E : @Enriched Ab Ab_Monoidal).

(* The category: composition is [ecompose] at a generator, identity is
   [eid] at 1.  The laws are E's equations consumed at generators, where
   both sides compute. *)
Program Definition Category_of_Enriched_Ab : Category := {|
  obj := @eobj Ab Ab_Monoidal E;
  hom := fun x y => carrier (@ehom Ab Ab_Monoidal E x y);
  homset := fun x y =>
    is_setoid (cmon_setoid (ab_cmon (@ehom Ab Ab_Monoidal E x y)));
  id := fun x => cmon_map (@eid Ab Ab_Monoidal E x) 1%Z;
  compose := fun x y z g f =>
    cmon_map (@ecompose Ab Ab_Monoidal E x y z) (ts_gen g f)
|}.
Next Obligation.
  (* compose_respects *)
  intros x y z g g' Hg f f' Hf.
  exact (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
           _ _ (te_gen Hg Hf)).
Qed.
Next Obligation.
  (* id_left: eid_left at the generator ts_gen 1 f *)
  intros x y f.
  pose proof (@eid_left Ab Ab_Monoidal E x y
                (@ts_gen ZAb (@ehom Ab Ab_Monoidal E x y) 1%Z f)) as Hl.
  simpl in Hl.
  refine (transitivity Hl _).
  exact (zsmul_one (@ehom Ab Ab_Monoidal E x y) f).
Qed.
Next Obligation.
  (* id_right: eid_right at the generator ts_gen f 1 *)
  intros x y f.
  pose proof (@eid_right Ab Ab_Monoidal E x y
                (@ts_gen (@ehom Ab Ab_Monoidal E x y) ZAb f 1%Z)) as Hr.
  simpl in Hr.
  refine (transitivity Hr _).
  exact (zsmul_one (@ehom Ab Ab_Monoidal E x y) f).
Qed.
Next Obligation.
  (* comp_assoc: ecompose_assoc at ts_gen (ts_gen f g) h *)
  intros x y z w f g h.
  pose proof (@ecompose_assoc Ab Ab_Monoidal E x y z w
                (@ts_gen (AbTensor (@ehom Ab Ab_Monoidal E z w)
                                   (@ehom Ab Ab_Monoidal E y z))
                         (@ehom Ab Ab_Monoidal E x y)
                   (@ts_gen (@ehom Ab Ab_Monoidal E z w)
                            (@ehom Ab Ab_Monoidal E y z) f g) h)) as Ha.
  simpl in Ha.
  exact (symmetry Ha).
Qed.
Next Obligation.
  (* comp_assoc_sym *)
  intros x y z w f g h.
  pose proof (@ecompose_assoc Ab Ab_Monoidal E x y z w
                (@ts_gen (AbTensor (@ehom Ab Ab_Monoidal E z w)
                                   (@ehom Ab Ab_Monoidal E y z))
                         (@ehom Ab Ab_Monoidal E x y)
                   (@ts_gen (@ehom Ab Ab_Monoidal E z w)
                            (@ehom Ab Ab_Monoidal E y z) f g) h)) as Ha.
  simpl in Ha.
  exact Ha.
Qed.

(* The AbEnriched structure: hom-group operations from the hom-objects;
   bilinearity of composition is the generator relations of the tensor
   pushed through [ecompose]'s homomorphism property. *)
Program Definition AbEnriched_of_Enriched_Ab :
  AbEnriched Category_of_Enriched_Ab := {|
  abenriched_preadditive := {|
    padd := fun x y f g =>
      cmon_plus (ab_cmon (@ehom Ab Ab_Monoidal E x y)) f g;
    pzero := fun x y =>
      cmon_zero (ab_cmon (@ehom Ab Ab_Monoidal E x y))
  |};
  abneg := fun x y f => ab_neg (@ehom Ab Ab_Monoidal E x y) f
|}.
Next Obligation.
  intros x y f g h.
  exact (cmon_plus_assoc _ f g h).
Qed.
Next Obligation.
  intros x y f g.
  exact (cmon_plus_comm _ f g).
Qed.
Next Obligation.
  intros x y f.
  exact (cmon_plus_zero_l _ f).
Qed.
Next Obligation.
  (* compose_padd_left: h ∘ (f + g) ≈ h ∘ f + h ∘ g *)
  intros x y z h f g; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (te_bilin_r h f g)) _).
  exact (cmon_map_plus (@ecompose Ab Ab_Monoidal E x y z)
           (ts_gen h f) (ts_gen h g)).
Qed.
Next Obligation.
  (* compose_padd_right: (f + g) ∘ h ≈ f ∘ h + g ∘ h *)
  intros x y z f g h; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (te_bilin_l f g h)) _).
  exact (cmon_map_plus (@ecompose Ab Ab_Monoidal E x y z)
           (ts_gen f h) (ts_gen g h)).
Qed.
Next Obligation.
  (* compose_pzero_left: 0 ∘ f ≈ 0 *)
  intros x y z f; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (ts_gen_zero_l f)) _).
  exact (cmon_map_zero (@ecompose Ab Ab_Monoidal E x y z)).
Qed.
Next Obligation.
  (* compose_pzero_right: f ∘ 0 ≈ 0 *)
  intros x y z f; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (ts_gen_zero_r f)) _).
  exact (cmon_map_zero (@ecompose Ab Ab_Monoidal E x y z)).
Qed.
Next Obligation.
  (* padd_abneg: f + (− f) ≈ 0 *)
  intros x y f.
  exact (ab_neg_right (@ehom Ab Ab_Monoidal E x y) f).
Qed.

End ToAbEnriched.

(** ** The correspondence *)

(* Mac Lane's "can be described completely in these terms", as a
   Type-valued equivalence of the two presentations — the same shape as
   [Category_is_Enriched_over_Set] and [Enriched_Two_preorder]. *)
(* The forward direction, exercised at the concrete witness: Ab is an
   Ab-category, so it is enriched over itself. *)
Definition Enriched_Ab_itself : @Enriched Ab Ab_Monoidal :=
  @Enriched_of_AbEnriched Ab Ab_AbEnriched.

Theorem Enriched_Ab_iff_AbEnriched :
  @Enriched Ab Ab_Monoidal ↔ { C : Category & AbEnriched C }.
Proof.
  split.
  - intro E.
    exact (Category_of_Enriched_Ab E; AbEnriched_of_Enriched_Ab E).
  - intros [C A].
    exact (@Enriched_of_AbEnriched C A).
Defined.
