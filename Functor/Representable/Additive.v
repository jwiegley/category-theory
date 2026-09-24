(** * The Ab-valued hom functor, and the additive upgrade of a representation *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed., §V.8, printed pp. 131–132, PDF pp. 140–141 (ledger
              items `maclane:V.8:thm-watt` and `maclane:V.8:ex3`, issue
              #454) — Watt's theorem, on p. 131, and its covariant form,
              Exercise 3, on p. 132.  The step this file supplies is the
              book's own sentence in the proof: once T has a left adjoint
              F, "since T is additive, the adjunction Ab(G, TA) ≅
              hom_R(A, FG), G ∈ Ab, A ∈ R-Mod, is an isomorphism of
              additive groups" (read from the printed page).  Read
              through Yoneda instead of an adjoint, the same step says: a
              representation of the UNDERLYING set-valued functor of an
              additive Ab-valued T is automatically a representation of T
              itself, in Ab.
   Book:      Mac Lane, ibid., §I.8 and §VIII.2 — Ab-categories and
              additive functors, whose in-tree statement is
              Structure/AbCategory.v.
   nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
   nLab:      https://ncatlab.org/nlab/show/additive+functor
   nLab:      https://ncatlab.org/nlab/show/representable+functor

   WHAT IS CONSUMED, NOT BUILT.

     - Structure/AbCategory.v: [AbEnriched], [AdditiveFunctor] with its
       only field [fmap_padd], the theorem [fmap_pzero] and
       [Ab_AbEnriched]; Structure/Preadditive.v's bilinearity fields
       [compose_padd_left], [compose_padd_right] and
       [compose_pzero_right].  The tree HAS an
       additive-functor notion; the catalog issue behind #454 said
       otherwise, and Adjunction/Additive.v's header already records that
       correction for the issue behind it.
     - Adjunction/Additive.v: [hom_ab], the hom-setoid of a locally
       propositional Ab-enriched category read as an [AbObject], and
       [AbEnriched_op].  Every value of the functor below IS [hom_ab];
       nothing about the group is rebuilt.
     - Functor/Representable.v: the [Representable] class and its
       [represented] isomorphism, in [Sets]-valued form.
     - Instance/Ab.v: [Ab], [Ab_Forget].
     - For the continuity of [HomAb] only: Structure/Limit/
       Preservation.v's [ContinuousFunctor], [FCone] and
       [cone_assoc_inv]; Functor/Hom/Continuous.v's
       [representable_iso_ContinuousFunctor]; Instance/Ab/Limit.v's
       [Ab_Forget_reflects_limits]; Instance/Fun.v's [iso_equiv].

   WHAT IS BUILT.

     - [LocallyPropositional_op]: the opposite of a locally propositional
       category is one, by the same hom-setoids read backwards
       ([LocallyPropositional_op_at] at [eq_refl]).  It is what lets the
       contravariant reading below reuse the covariant one verbatim.
     - **[HomAb AC A0 : C ⟶ Ab]**, the Ab-valued hom functor x ↦ hom(A0, x)
       of an Ab-enriched, locally propositional C, acting by
       postcomposition ([HomAb_fmap_at] at [eq_refl]); it is additive
       ([HomAb_additive], which is [compose_padd_right]); forgetting the
       group structure gives back [Hom A0,─] ([HomAb_forget_iso], the
       identity map both ways), so it carries a canonical
       [HomAb_representable] with representing object A0 itself.
     - [CoHomAb AC A0 : C^op ⟶ Ab], the contravariant one, defined as
       [HomAb] at [C^op] (through [AbEnriched_op] and
       [LocallyPropositional_op]), acting by precomposition
       ([CoHomAb_fmap_at] at [eq_refl]).
     - [HomAb_continuous AC A0 : ContinuousFunctor (HomAb AC A0)], and
       [CoHomAb_continuous], the same at C^op: the Ab-valued hom functors
       carry limit cones to limit cones, so the contravariant one carries
       colimits of C to limits of Ab.  Forgetting the group structure
       gives the Sets-valued hom functor ([HomAb_forget_iso]), which is
       continuous ([representable_iso_ContinuousFunctor]), and
       [Ab_Forget] reflects limit cones.  Both are term definitions, so
       transparent.  Instance/Mod/Watts.v and
       Instance/Mod/Watts/Unconditional.v consume them.
     - **[watt_ab_iso AC T AF Rp]**: for T : C ⟶ Ab additive and a
       representation Rp of [Ab_Forget ◯ T] in [Sets], the natural
       isomorphism [HomAb AC (repr_obj Rp) ≅ T] in the functor category
       [@Fun C Ab]; [watt_ab_repr] is the same fact as a Σ-type.  Its two
       components ARE the representation's components, at [eq_refl]
       ([watt_ab_iso_to_at], [watt_ab_iso_from_at]); nothing is
       re-chosen.

   THE ARGUMENT.  Write φ for the representation and x0 := φ(id).
   Naturality at the identity gives φ(f) ≈ T(f)(x0) ([wab_to_elem]).  So
   φ(f + g) ≈ T(f + g)(x0) ≈ T(f)(x0) + T(g)(x0) by [fmap_padd] — addition
   of Ab homomorphisms is pointwise — and φ(0) ≈ 0 by [fmap_pzero]
   ([wab_to_padd], [wab_to_pzero]).  The inverse is additive because it
   inverts an additive bijection ([wab_from_hom]).  Naturality in Ab is
   the naturality in [Sets], hom-equality in both being pointwise.  This
   is the "plus additivity" half of the issue's Reviewer line ("the
   representability must be derived from SAFT plus additivity"): SAFT
   supplies Rp (Adjunction/SAFT/Characterization/Corollaries.v's
   [continuous_Set_functor_representable]; at (RMod R)^op GAFT also
   supplies it, with no hypothesis, Instance/Mod/Watts/Unconditional.v's
   [RModop_continuous_representable]), and this file turns it into the
   Ab-level statement.  It is stated ONCE for an arbitrary C, so the
   covariant form (C := RMod R, Exercise 3) and the book's contravariant
   text form (C := (RMod R)^op, through [AbEnriched_op] and
   [LocallyPropositional_op]) are two instantiations of the same
   constant.

   STRENGTHS, strict first.  At [eq_refl]: [HomAb]'s object and arrow
   actions, [CoHomAb]'s arrow action, both components of [watt_ab_iso],
   and [watt_ab_iso_HomAb_obj] (the representing object recovered from
   [HomAb_representable AC A0] is A0 itself).  Up to ≈: the
   isomorphism laws of [HomAb_forget_iso] and of [watt_ab_iso], both
   componentwise in the functor category's hom-setoid.

   UNIVERSES, measured by [About] under [Set Printing Universes].
   [HomAb@{o h a} : ∀ {C : Category@{o h h}}, LocallyPropositional@{h o} C
   → AbEnriched@{o h} C → obj[C] → C ⟶ Ab@{a h}] with no universe
   equation: besides [Set < a] and [h < a] its constraint block carries
   only [h <= compose.u0], [h <= compose.u1], [h <= compose.u2] and
   [h <= ID.u0], the stdlib bounds [Ab@{a h}] itself carries on its hom
   universe.  The object universe o is left free, and C's hom
   universe h IS the carrier universe of the Ab it lands in, because
   [hom_ab@{u u0}] returns [AbObject@{u u u}] at the hom universe u.
   [watt_ab_iso] carries no universe equation at all (its constraint
   block has only [<] and [<=]); T : [Functor@{o h h a h h}], i.e. into
   the same [Ab@{a h}].  No constant of the module carries one: [Print
   Module] lists 38 constants, and the [About] output of each, queried by
   its fully qualified name, has no " = " in its constraint block; each
   is "Closed under the global context".  The sections below declare
   [Universes] and the top-level constants carry explicit binders.

   NON-VACUITY.  [watt_ab_iso_HomAb] instantiates the upgrade at
   T := [HomAb AC A0] with its own [HomAb_representable], and
   [watt_ab_iso_at_Ab] instantiates every hypothesis in tree at C := Ab
   ([Ab_AbEnriched], and [Ab_LocallyPropositional] by resolution).  Both
   feed the upgrade a hom functor's own representation, so they exercise
   the hypotheses without testing them.  A witness that does is
   Instance/Mod/Watts.v's [watt_at_forget]: at C := RMod R and
   T := [RMod_Forget_Ab R], whose representation is Instance/Mod/
   Representable.v's [rmod_representable] carried along an
   identity-component isomorphism, the upgrade gives
   [HomAb (RMod_AbEnriched R) (Ring_RMod R) ≅ RMod_Forget_Ab R] with no
   hypothesis, the representing object being [Ring_RMod R] by
   conversion (the statement names it);
   and the same file's [ab_hom_Z_iso] gives Ab(ℤ, X) ≅ X, natural in X,
   at T := Id[Ab] with ℤ the free abelian group on one point.

   AT C^op THE LOCAL-PROPOSITIONALITY ARGUMENT IS EXPLICIT.
   [LocallyPropositional_op] is a [Definition], not an [Instance], so
   resolution does not find it: [watt_ab_iso (AbEnriched_op
   (RMod_AbEnriched R)) T AF Rp] at T : (RMod R)^op ⟶ Ab is refused
   with "Cannot infer the implicit parameter LP of watt_ab_iso whose type
   is "LocallyPropositional (RMod R)^op" (no type class instance found)",
   and the same term with [(LocallyPropositional_op _)] passed for LP is
   accepted (both measured in scratch files under this file's imports
   plus Instance/Mod/Bimodule.v's).  [CoHomAb] and Instance/Mod/Watts.v
   pass it explicitly.

   NOT DELIVERED.  [HomAb] is a functor in ONE variable: there is no
   bifunctor [C^op ∏ C ⟶ Ab] and no naturality in A0.  The
   representation Rp is a HYPOTHESIS here; producing it from continuity
   is SAFT's business and is not done in this file.  At
   C := (RMod R)^op it is also produced with no hypothesis, by GAFT
   rather than SAFT: Instance/Mod/Watts/Unconditional.v's
   [RModop_continuous_representable].  The continuity of [HomAb] and
   [CoHomAb] is not among the gaps: [HomAb_continuous] and
   [CoHomAb_continuous] (WHAT IS BUILT) are its one definition each, and
   both Watts files consume them.  Adjunction/Additive.v's
   [adj_hom_ab_iso] is not restated as a natural isomorphism between two
   [HomAb]/[CoHomAb] functors; it remains the family of group
   isomorphisms its header describes.  No uniqueness beyond
   Functor/Representable.v's. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Adjunction.Additive.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Instance.Ab.Limit.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** The opposite of a locally propositional category *)

Definition LocallyPropositional_op@{o h +} {C : Category@{o h h}}
  (LP : LocallyPropositional C) : LocallyPropositional (C^op).
Proof. constructor; intros x y; exact (@locally_prop C LP y x). Defined.

Example LocallyPropositional_op_at@{o h +} {C : Category@{o h h}}
  (LP : LocallyPropositional C) (x y : C) :
  @locally_prop (C^op) (LocallyPropositional_op LP) x y
    = @locally_prop C LP y x := eq_refl.

(** ** The Ab-valued hom functor *)

Section HomAbFunctor.

Universes o h a.

Context {C : Category@{o h h}}.
Context {LP : LocallyPropositional C}.
Context (AC : AbEnriched C).
Context (A0 : C).

Definition HomAb_fmap {x y : C} (f : x ~{C}~> y) :
  hom_ab AC A0 x ~{Ab@{a h}}~> hom_ab AC A0 y.
Proof.
  unshelve econstructor; [unshelve econstructor|..].
  - exact (fun g => f ∘ g).
  - intros g g' H. exact (@compose_respects C _ _ _ f f (reflexivity f) g g' H).
  - exact (@compose_pzero_right _ (@abenriched_preadditive C AC) _ _ _ f).
  - intros g k.
    exact (@compose_padd_left _ (@abenriched_preadditive C AC) _ _ _ f g k).
Defined.

Program Definition HomAb : C ⟶ Ab@{a h} := {|
  fobj := fun x => hom_ab AC A0 x;
  fmap := fun x y f => HomAb_fmap f
|}.
Next Obligation.
  intros x y f f' H g.
  exact (@compose_respects C _ _ _ f f' H g g (reflexivity g)).
Qed.
Next Obligation. intros x g; simpl. apply (@id_left C). Qed.
Next Obligation. intros x y z f k g; simpl. apply (@comp_assoc_sym C). Qed.

Example HomAb_obj (x : C) : fobj[HomAb] x = hom_ab AC A0 x := eq_refl.

Example HomAb_fmap_at {x y : C} (f : x ~{C}~> y) (g : A0 ~{C}~> x) :
  cmon_map (fmap[HomAb] f) g = f ∘ g := eq_refl.

(* Post-composition is additive in the arrow composed with. *)
Definition HomAb_additive :
  @AdditiveFunctor C Ab@{a h} AC Ab_AbEnriched HomAb.
Proof.
  constructor.
  intros x y f g k; simpl.
  exact (@compose_padd_right _ (@abenriched_preadditive C AC) _ _ _ f g k).
Defined.

(* Forgetting the group structure gives back the Sets-valued hom functor,
   componentwise by the identity map. *)
Definition HomAb_forget_to : [Hom A0,─] ⟹ Ab_Forget ◯ HomAb.
Proof.
  unshelve eapply Build_Transform'.
  - intro x; simpl.
    exact {| morphism := fun g => g; proper_morphism := fun g g' H => H |}.
  - intros x y f g; simpl; reflexivity.
Defined.

Definition HomAb_forget_from : Ab_Forget ◯ HomAb ⟹ [Hom A0,─].
Proof.
  unshelve eapply Build_Transform'.
  - intro x; simpl.
    exact {| morphism := fun g => g; proper_morphism := fun g g' H => H |}.
  - intros x y f g; simpl; reflexivity.
Defined.

Definition HomAb_forget_iso : [Hom A0,─] ≅[Fun] Ab_Forget ◯ HomAb.
Proof.
  unshelve econstructor.
  - exact HomAb_forget_to.
  - exact HomAb_forget_from.
  - intros x g; simpl; now rewrite id_left.
  - intros x g; simpl; now rewrite id_left.
Defined.

#[local] Obligation Tactic := idtac.

Definition HomAb_representable : Representable (Ab_Forget ◯ HomAb) :=
  {| repr_obj := A0; represented := HomAb_forget_iso |}.

End HomAbFunctor.

Arguments HomAb {C LP} AC A0.
Arguments HomAb_fmap {C LP} AC A0 {x y} f.
Arguments HomAb_additive {C LP} AC A0.
Arguments HomAb_representable {C LP} AC A0.

(** ** The contravariant Ab-valued hom functor *)

Definition CoHomAb@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  C^op ⟶ Ab@{a h} :=
  @HomAb (C^op) (LocallyPropositional_op LP) (AbEnriched_op AC) A0.

Example CoHomAb_fmap_at@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) {x y : C}
  (f : y ~{C}~> x) (g : x ~{C}~> A0) :
  cmon_map (fmap[CoHomAb AC A0] f) g = g ∘ f := eq_refl.

(** ** The Ab-valued hom functors are continuous *)

(* Forgetting the group structure of [HomAb AC A0] gives the Sets-valued
   hom functor up to the identity-component iso [HomAb_forget_iso], which
   is continuous; [Ab_Forget] reflects limit cones, and [cone_assoc_inv]
   repackages a cone over [Ab_Forget ◯ (HomAb ◯ K)] as one over
   [(Ab_Forget ◯ HomAb) ◯ K]. *)
Definition HomAb_continuous@{o h a +}
  {C : Category@{o h h}} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (A0 : C) :
  ContinuousFunctor (HomAb AC A0 : C ⟶ Ab@{a h}) :=
  fun J K N HN =>
    Ab_Forget_reflects_limits (HomAb AC A0 ◯ K) (FCone (HomAb AC A0) N)
      (fun M => representable_iso_ContinuousFunctor A0
                  (iso_equiv (HomAb_forget_iso AC A0)) J K N HN
                  (cone_assoc_inv M)).

(* The contravariant one is the covariant one at [C^op]: it carries the
   colimits of C, which are the limits of [C^op], to limits of [Ab]. *)
Definition CoHomAb_continuous@{o h a +}
  {C : Category@{o h h}} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (A0 : C) :
  ContinuousFunctor (CoHomAb AC A0 : C^op ⟶ Ab@{a h}) :=
  @HomAb_continuous (C^op) (LocallyPropositional_op LP) (AbEnriched_op AC) A0.

(** ** The additive upgrade *)

Section AdditiveUpgrade.

Universes o h a s.

Context {C : Category@{o h h}}.
Context {LP : LocallyPropositional C}.
Context (AC : AbEnriched C).
Context (T : C ⟶ Ab@{a h}).
Context (AF : @AdditiveFunctor C Ab@{a h} AC Ab_AbEnriched T).
Context (Rp : Representable (Ab_Forget@{a s h} ◯ T)).

Definition wab_obj : C := @repr_obj _ _ Rp.

Definition wab_to (x : C) :=
  transform[to (@represented _ _ Rp)] x.

Definition wab_from (x : C) :=
  transform[from (@represented _ _ Rp)] x.

Definition wab_elem : carrier (cmon_setoid (T wab_obj)) :=
  wab_to wab_obj (@id C wab_obj).

Lemma wab_to_elem (x : C) (f : wab_obj ~{C}~> x) :
  wab_to x f ≈ cmon_map (fmap[T] f) wab_elem.
Proof using T Rp.
  pose proof (@naturality _ _ _ _ (to (@represented _ _ Rp)) wab_obj x f
                (@id C wab_obj)) as N.
  unfold wab_to, wab_elem.
  etransitivity; [|symmetry; exact N].
  apply proper_morphism. simpl. symmetry.
  rewrite ?id_left, ?id_right. reflexivity.
Qed.

Lemma wab_to_padd (x : C) (f g : wab_obj ~{C}~> x) :
  wab_to x (@padd _ (@abenriched_preadditive C AC) _ _ f g)
    ≈ cmon_plus (T x) (wab_to x f) (wab_to x g).
Proof using AF.
  rewrite wab_to_elem, wab_to_elem, wab_to_elem.
  pose proof (@fmap_padd _ _ _ _ T AF _ _ f g wab_elem) as H. simpl in H.
  exact H.
Qed.

Lemma wab_to_pzero (x : C) :
  wab_to x (@pzero _ (@abenriched_preadditive C AC) wab_obj x)
    ≈ cmon_zero (T x).
Proof using AF.
  rewrite wab_to_elem.
  pose proof (@fmap_pzero _ _ _ _ T AF wab_obj x wab_elem) as H. simpl in H.
  exact H.
Qed.

Lemma wab_to_from (x : C) (t : carrier (cmon_setoid (T x))) :
  wab_to x (wab_from x t) ≈ t.
Proof using T Rp.
  pose proof (@iso_to_from _ _ _ (@represented _ _ Rp) x t) as H.
  simpl in H. etransitivity; [exact H|]. exact (@fmap_id _ _ T x t).
Qed.

Lemma wab_from_to (x : C) (f : wab_obj ~{C}~> x) :
  wab_from x (wab_to x f) ≈ f.
Proof using T Rp.
  pose proof (@iso_from_to _ _ _ (@represented _ _ Rp) x f) as H.
  simpl in H. etransitivity; [exact H|]. rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

Definition wab_to_hom (x : C) : hom_ab AC wab_obj x ~{Ab@{a h}}~> T x.
Proof using AF.
  unshelve econstructor; [unshelve econstructor|..].
  - exact (wab_to x).
  - exact (@proper_morphism _ _ _ _ (wab_to x)).
  - exact (wab_to_pzero x).
  - exact (wab_to_padd x).
Defined.

Definition wab_from_hom (x : C) : T x ~{Ab@{a h}}~> hom_ab AC wab_obj x.
Proof using AF.
  unshelve econstructor; [unshelve econstructor|..].
  - exact (wab_from x).
  - exact (@proper_morphism _ _ _ _ (wab_from x)).
  - transitivity
      (wab_from x
         (wab_to x (@pzero _ (@abenriched_preadditive C AC) wab_obj x))).
    + apply proper_morphism. symmetry. apply wab_to_pzero.
    + apply wab_from_to.
  - intros t u.
    transitivity (wab_from x (wab_to x
      (@padd _ (@abenriched_preadditive C AC) _ _
         (wab_from x t) (wab_from x u)))).
    + apply proper_morphism. rewrite wab_to_padd, !wab_to_from. reflexivity.
    + apply wab_from_to.
Defined.

Definition wab_to_nat : HomAb AC wab_obj ⟹ T.
Proof using AF.
  unshelve eapply Build_Transform'.
  - exact wab_to_hom.
  - intros x y f g; simpl.
    exact (@naturality _ _ _ _ (to (@represented _ _ Rp)) x y f g).
Defined.

Definition wab_from_nat : T ⟹ HomAb AC wab_obj.
Proof using AF.
  unshelve eapply Build_Transform'.
  - exact wab_from_hom.
  - intros x y f t; simpl.
    exact (@naturality _ _ _ _ (from (@represented _ _ Rp)) x y f t).
Defined.

Definition watt_ab_iso : @Isomorphism (@Fun C Ab@{a h}) (HomAb AC wab_obj) T.
Proof using AF.
  unshelve econstructor.
  - exact wab_to_nat.
  - exact wab_from_nat.
  - intros x t; simpl. etransitivity; [exact (wab_to_from x t)|].
    symmetry; exact (@fmap_id _ _ T x t).
  - intros x f; simpl. etransitivity; [exact (wab_from_to x f)|].
    rewrite ?id_left, ?id_right. reflexivity.
Defined.

Example watt_ab_iso_to_at (x : C) (f : wab_obj ~{C}~> x) :
  cmon_map (transform[to watt_ab_iso] x) f
    = transform[to (@represented _ _ Rp)] x f := eq_refl.

Example watt_ab_iso_from_at (x : C) (t : carrier (cmon_setoid (T x))) :
  cmon_map (transform[from watt_ab_iso] x) t
    = transform[from (@represented _ _ Rp)] x t := eq_refl.

(* Tactic form, kept as a precaution only: the term-mode [existT]
   spelling, and the anonymous-constructor one, also compile on Coq
   8.19.2 and 8.20.1 (measured in scratch copies against built 8.19.2 and
   8.20.1 closures of this file). *)
Definition watt_ab_repr :
  { A : C & @Isomorphism (@Fun C Ab@{a h}) (HomAb AC A) T }.
Proof using AF Rp. exists wab_obj. exact watt_ab_iso. Defined.

End AdditiveUpgrade.

Arguments wab_obj {C T} Rp.
Arguments watt_ab_iso {C LP} AC T AF Rp.
Arguments watt_ab_repr {C LP} AC T AF Rp.

(** ** Non-vacuity: the hom functor itself *)

Definition watt_ab_iso_HomAb@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  @Isomorphism (@Fun C Ab@{a h})
    (HomAb AC (wab_obj (HomAb_representable AC A0))) (HomAb AC A0) :=
  watt_ab_iso AC (HomAb AC A0) (HomAb_additive AC A0)
    (HomAb_representable AC A0).

Example watt_ab_iso_HomAb_obj@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  @wab_obj C (HomAb@{o h a} AC A0) (HomAb_representable AC A0) = A0 :=
  eq_refl.

(* The hypotheses are met in tree: at [Ab] itself, by [Ab_AbEnriched] and
   [Ab_LocallyPropositional]. *)
Definition watt_ab_iso_at_Ab@{a b h +} (A0 : AbObject@{h h h}) :
  @Isomorphism (@Fun Ab@{a h} Ab@{b h})
    (HomAb Ab_AbEnriched (wab_obj (HomAb_representable Ab_AbEnriched A0)))
    (HomAb Ab_AbEnriched A0) :=
  watt_ab_iso_HomAb Ab_AbEnriched A0.
