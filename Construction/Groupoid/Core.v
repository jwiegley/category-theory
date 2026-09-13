Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grpd.

Generalizable All Variables.

(** * The core functor, and its adjunction with the inclusion *)

(* nLab:      https://ncatlab.org/nlab/show/core
   nLab:      https://ncatlab.org/nlab/show/Grpd
   Wikipedia: https://en.wikipedia.org/wiki/Core_(group_theory)

   Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,
         Example 4.1.15, printed p. 137 (PDF pp. 157-158)

   Construction/Groupoid.v builds the core of ONE category:
   [Groupoid C] has the objects of C and the isomorphisms of C as its
   morphisms.  This file makes that construction a functor
   [Core : Cat ⟶ Grpd] and proves it right adjoint to the inclusion
   [Grpd_Incl : Grpd ⟶ Cat] of Instance/Grpd.v.

   The morphism part is forced.  A functor F : C ⟶ D carries isomorphisms
   to isomorphisms -- Theory/Functor.v's [fobj_iso] is exactly that
   statement, as a [Proper] instance -- so [CoreMap F] is F restricted to
   the isomorphisms, sending x ≅ y to F x ≅ F y componentwise.  [CoreMap]
   below writes that two-field isomorphism out directly instead of
   projecting it from [fobj_iso], so that its two inverse laws are named
   obligations here.  The object part needs [IsGroupoid (Groupoid C)];
   that lemma is already in-tree, as Structure/Groupoid.v's
   [core_is_groupoid], and is reused rather than reproved.

   The adjunction is the universal property of the core: for a groupoid G,
   every functor G ⟶ C lands in the isomorphisms of C, so it factors
   through [Groupoid C], and uniquely.  The forward transpose is
   [core_lift]: it re-reads F : G ⟶ C as a functor into [Groupoid C] by
   pairing F f with F of the chosen inverse of f.  The backward transpose
   is post-composition with [ForgetCore C : Groupoid C ⟶ C], which takes an
   isomorphism to its [to] component.  What makes the two mutually inverse
   is that a functor into a core is DETERMINED by its [to] components
   ([core_functor_from] below): the [from] component of P f is forced to be
   the [to] component of P (f⁻¹), by uniqueness of inverses.

   The result is delivered as a `≈`-level [Adjunction] over the CATEGORY
   [Grpd], through Theory/Adjunction.v's [Build_Adjunction'] -- not as a
   per-object factorization statement.  Both of the naturality squares
   [Build_Adjunction'] asks for are witnessed by the IDENTITY natural
   isomorphism: the two functors being compared agree on objects and in
   their [to] components, so [cat] closes those halves.  Only the [from]
   halves need an argument, and only for the first square
   ([to_adj_nat_l]); it is there that the one genuine lemma of the file,
   [functor_ginv], is used.  The second ([to_adj_nat_r]) is componentwise
   identical on both sides.

   Not delivered here: the LEFT adjoint.  The category of fractions, which
   universally inverts every morphism, is not built in any part, so the
   adjoint triple Fractions ⊣ Incl ⊣ Core is exhibited only on its
   right-hand side. *)

(** ** Functors between groupoids preserve the chosen inverse

    [IsGroupoid] carries a CHOSEN inverse for each arrow, so "F preserves
    inverses" is not a tautology: it says the choice made in B at [fmap[F] f]
    agrees, up to `≈`, with the image of the choice made in A at f.  It does,
    because both are inverses of the same arrow and inverses are unique
    (Structure/Groupoid.v's [ginv_unique_r], which is Eilenberg and
    Mac Lane's Lemma 1.4 read at the chosen inverse). *)

Lemma functor_ginv {A B : Category} (HA : IsGroupoid A) (HB : IsGroupoid B)
      (F : A ⟶ B) {x y : A} (f : x ~> y) :
  fmap[F] (ginv HA f) ≈ ginv HB (fmap[F] f).
Proof.
  symmetry.
  apply ginv_unique_r.
  rewrite <- fmap_comp.
  rewrite ginv_right.
  apply fmap_id.
Qed.

(* In the core the chosen inverse is [iso_sym] ON THE NOSE, not merely up to
   `≈`: [core_is_groupoid] hands [Build_IsIsomorphism] the term [iso_sym f]
   and [ginv] projects it straight back out.  Recorded as an [Example] at
   [eq_refl], the strongest available reading. *)

Example core_ginv_eq {C : Category} {x y : Groupoid C} (f : x ~> y) :
  ginv (core_is_groupoid C) f = iso_sym f := eq_refl.

(** ** Isomorphisms of the core

    An isomorphism of C is a morphism of [Groupoid C]; it is moreover an
    ISOMORPHISM of [Groupoid C], with [iso_sym] as its inverse.  This is
    [core_is_groupoid] packaged as `≅` rather than as [IsIsomorphism], and
    it is what turns a natural isomorphism between functors into C into one
    between the corresponding functors into [Groupoid C]. *)

Program Definition core_iso {D : Category} {a b : D} (i : a ≅ b) :
  a ≅[Groupoid D] b := {|
  to          := i;
  from        := iso_sym i;
  iso_to_from := iso_sym_right_inverse i;
  iso_from_to := iso_sym_left_inverse i
|}.

(** ** The core of a functor *)

Program Definition CoreMap {C D : Category} (F : C ⟶ D) :
  Groupoid C ⟶ Groupoid D := {|
  fobj := fun x => F x;
  fmap := fun _ _ f => {| to := fmap[F] (to f); from := fmap[F] (from f) |}
|}.
Next Obligation.
  rewrite <- fmap_comp, iso_to_from.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp, iso_from_to.
  apply fmap_id.
Qed.
Next Obligation.
  intros f g [Hto Hfrom]; split; simpl.
  - now rewrite Hto.
  - now rewrite Hfrom.
Qed.
(* The [fmap_id] obligation is discharged by the ambient [cat_simpl]; only
   [fmap_comp] survives it. *)
Next Obligation. split; simpl; apply fmap_comp. Qed.

(* The core of a natural isomorphism.  [Cat]'s hom-setoid is
   [Functor_Setoid], so F ≈ F' is a natural isomorphism; each component is
   an isomorphism of D, hence a morphism of [Groupoid D], and [core_iso]
   promotes it to an isomorphism THERE.  The naturality square is checked
   twice, once in each component of the isomorphism, the [from] half being
   the given square read at f⁻¹. *)

Lemma CoreMap_respects {C D : Category} (F F' : C ⟶ D) :
  F ≈ F' → CoreMap F ≈ CoreMap F'.
Proof.
  intros [n Hn].
  exists (fun x => core_iso (n x)).
  intros x y f; split; simpl.
  - apply (Hn _ _ (to f)).
  - rewrite (Hn _ _ (from f)).
    now rewrite comp_assoc.
Qed.

Program Definition Core : Cat ⟶ Grpd := {|
  fobj := fun C => ((Groupoid C; core_is_groupoid C) : Grpd);
  fmap := fun _ _ F => (CoreMap F; I)
|}.
(* Only [fmap_respects] survives the ambient [cat_simpl]; the two functor
   laws of [Core] are the identity natural isomorphism on both sides and it
   discharges them. *)
Next Obligation.
  intros F F1 HF; simpl.
  now apply CoreMap_respects.
Qed.

(** ** The counit: reading an isomorphism as a morphism *)

(* [ForgetCore C] is the counit of the adjunction below at C, up to `≈` --
   [core_counit_is_ForgetCore] measures that.  It is the inclusion of the
   core back into C: identity on objects, and the [to] component on
   morphisms.  It is not an inclusion in the sense of
   Construction/Subcategory.v -- the core is a subcategory of C only up to
   the choice of inverse carried by each arrow -- and it is faithful
   precisely because an isomorphism is determined by its [to] component
   (Theory/Isomorphism.v's [to_equiv_implies_iso_equiv]). *)

Program Definition ForgetCore (C : Category) : Groupoid C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => to f
|}.

Lemma ForgetCore_Faithful (C : Category) : Faithful (ForgetCore C).
Proof.
  construct.
  now apply to_equiv_implies_iso_equiv.
Qed.

(** ** The forward transpose

    A functor out of a groupoid factors through the core.  The factoring
    functor sends f to the isomorphism whose [to] is F f and whose [from] is
    F of the chosen inverse of f; the two inverse laws are the images under
    F of [ginv_right] and [ginv_left]. *)

Program Definition core_lift {G : Category} (HG : IsGroupoid G)
        {C : Category} (F : G ⟶ C) : G ⟶ Groupoid C := {|
  fobj := fun x => F x;
  fmap := fun _ _ f => {| to := fmap[F] f; from := fmap[F] (ginv HG f) |}
|}.
Next Obligation.
  rewrite <- fmap_comp, ginv_right.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp, ginv_left.
  apply fmap_id.
Qed.
Next Obligation.
  intros f g Hfg; split; simpl.
  - now rewrite Hfg.
  - (* [ginv_respects] is what carries `≈` under the chosen inverse. *)
    now rewrite Hfg.
Qed.
Next Obligation.
  split; simpl.
  - apply fmap_id.
  - rewrite ginv_id.
    apply fmap_id.
Qed.
Next Obligation.
  split; simpl.
  - apply fmap_comp.
  - rewrite ginv_comp.
    apply fmap_comp.
Qed.

(* The [from] component of a functor into a core is not free data: it is
   forced to be the [to] component at the inverse arrow.  This is
   [functor_ginv] read at [core_is_groupoid], whose chosen inverse is
   [iso_sym] ([core_ginv_eq] above), taken in its [to] component. *)

Lemma core_functor_from {G : Category} (HG : IsGroupoid G) {C : Category}
      (P : G ⟶ Groupoid C) {x y : G} (f : x ~> y) :
  to (fmap[P] (ginv HG f)) ≈ from (fmap[P] f).
Proof.
  exact (fst (functor_ginv HG (core_is_groupoid C) P f)).
Qed.

(** ** The two round trips *)

Lemma core_lift_forget {G : Category} (HG : IsGroupoid G) {C : Category}
      (F : G ⟶ C) : ForgetCore C ◯ core_lift HG F ≈ F.
Proof.
  exists (fun x => @iso_id C (F x)).
  intros x y f; simpl; cat.
Qed.

Lemma forget_core_lift {G : Category} (HG : IsGroupoid G) {C : Category}
      (P : G ⟶ Groupoid C) : core_lift HG (ForgetCore C ◯ P) ≈ P.
Proof.
  exists (fun x => @iso_id (Groupoid C) (P x)).
  intros x y f; split; simpl.
  - cat.
  - rewrite core_functor_from.
    cat.
Qed.

(* Transporting the forward transpose along a natural isomorphism of its
   argument.  Same shape as [CoreMap_respects]: the [to] half is the given
   naturality square, the [from] half is that square read at the chosen
   inverse. *)

Lemma core_lift_respects {G : Category} (HG : IsGroupoid G) {C : Category}
      (F F' : G ⟶ C) : F ≈ F' → core_lift HG F ≈ core_lift HG F'.
Proof.
  intros [n Hn].
  exists (fun x => core_iso (n x)).
  intros x y f; split; simpl.
  - apply (Hn _ _ f).
  - rewrite (Hn _ _ (ginv HG f)).
    now rewrite comp_assoc.
Qed.

(** ** The adjunction Incl ⊣ Core *)

(* Riehl §4.1, Example 4.1.15, right-hand half.  The hom-setoid isomorphism
   is [core_lift] one way and post-composition with [ForgetCore] the other,
   and the two naturality squares are the two [to_adj_nat_*] fields
   Theory/Adjunction.v's [Build_Adjunction'] asks for -- the other two are
   derived there. *)

Definition Incl_Core_Adjunction : Adjunction Grpd_Incl Core.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros G C.
    unshelve eapply Isomorphism.Build_Isomorphism.
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun F => (core_lift (`2 G) F; I)).
      * abstract (intros F F' HF; simpl; now apply core_lift_respects).
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun P => ForgetCore C ◯ `1 P).
      * abstract (intros P Q HPQ; simpl;
                  exact (Compose_respects (ForgetCore C) (ForgetCore C)
                           (Equivalence_Reflexive _) _ _ HPQ)).
    + abstract (intro P; simpl; apply forget_core_lift).
    + abstract (intro F; simpl; exact (core_lift_forget (`2 G) F)).
  - abstract (intros G G' C f g; simpl;
              exists (fun x => @iso_id (Groupoid C) (f (`1 g x)));
              intros x y h; split; simpl;
              [ cat
              | rewrite id_left, id_right;
                apply fmap_respects;
                apply (functor_ginv (`2 G) (`2 G') (`1 g) h) ]).
  - abstract (intros G C C' f g; simpl;
              exists (fun x => @iso_id (Groupoid C') (f (g x)));
              intros x y h; split; simpl; cat).
Defined.

(** ** The universal property, spelled out

    Riehl's phrasing of the same fact: "because functors preserve
    isomorphisms, any functor out of a groupoid factors uniquely through the
    core".  This is the adjunction read at one object, and it is derived FROM
    the adjunction's two round trips rather than proved again -- the
    adjunction is the theorem, this is its restatement.  Uniqueness is up to
    `≈`, which for functors into [Groupoid C] is natural isomorphism, not
    equality: that is the strongest reading [Cat]'s hom-setoid supports. *)

Theorem core_factorization {G : Grpd} {C : Category} (F : `1 G ⟶ C) :
  { P : `1 G ⟶ Groupoid C
  & (ForgetCore C ◯ P ≈ F) *
    (∀ Q : `1 G ⟶ Groupoid C, ForgetCore C ◯ Q ≈ F → Q ≈ P) }.
Proof.
  exists (core_lift (`2 G) F).
  split.
  - apply core_lift_forget.
  - intros Q HQ.
    rewrite <- (forget_core_lift (`2 G) Q).
    now apply core_lift_respects.
Qed.

(* The counit of the adjunction is the inclusion of the core back into C,
   as it must be: [counit] is the backward transpose of the identity, and
   the backward transpose is post-composition with [ForgetCore]. *)

Example core_counit_is_ForgetCore (C : Cat) :
  @counit Cat Grpd Grpd_Incl Core Incl_Core_Adjunction C ≈ ForgetCore C.
Proof. apply fun_equiv_id_right. Qed.

(* The unit sends an arrow of a groupoid to itself regarded as an
   isomorphism -- that is exactly [core_lift] applied to the identity
   functor. *)

Example core_unit_is_core_lift_Id (G : Grpd) :
  `1 (@unit Cat Grpd Grpd_Incl Core Incl_Core_Adjunction G)
    ≈ core_lift (`2 G) Id.
Proof. reflexivity. Qed.
