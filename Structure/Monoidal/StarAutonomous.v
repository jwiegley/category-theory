Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* The homset isomorphisms of the closed structure live in [Sets], so
   [Instance/Sets] is in scope; suppress its product-monoidal instance as a
   typeclass hint so that `⨂` resolves to the ambient [SymMonClosed]/[Monoidal]
   structure on `C` rather than the tensor of [Sets].  Structure/Monoidal/Closed
   performs the same removal for exactly this reason. *)
Remove Hints Sets_Product_Monoidal : typeclass_instances.

(** * Star-autonomous categories (definition level) *)

(* nLab:      https://ncatlab.org/nlab/show/star-autonomous+category
   nLab:      https://ncatlab.org/nlab/show/dualizing+object
   Wikipedia: https://en.wikipedia.org/wiki/Star-autonomous_category

   A *-autonomous (star-autonomous) category is a symmetric monoidal closed
   category C equipped with a DUALIZING OBJECT `⊥ : C` (here [dualizer]): an
   object such that the canonical map from every `x` into its double dual

       x ~> (x ⇒ ⊥) ⇒ ⊥

   is an isomorphism.  Writing the internal-hom into the dualizer as the
   contravariant DUAL functor

       (-)^*  :=  (- ⇒ ⊥)  :  C^op ⟶ C,

   the defining datum is a natural isomorphism `x ≅ x^*^*` together with the
   closed transpose `Hom(x ⨂ y, ⊥) ≅ Hom(x, y ⇒ ⊥)` exhibiting `y ⇒ ⊥` as the
   dual of `y`.  This is the categorical semantics of classical multiplicative
   linear logic: `⊗` is the multiplicative conjunction, the dual is linear
   negation, and the dualizing object is the unit `⊥` of the multiplicative
   disjunction `⅋`.

   BASE.  A *-autonomous category is symmetric monoidal CLOSED, so the base must
   supply a genuine internal hom over a possibly NON-cartesian tensor.  The
   library's [ClosedMonoidal] (Structure/Monoidal/Closed.v) bundles the
   genuinely cartesian [CartesianMonoidal]; but over a cartesian closed base a
   dualizing object forces the category to be a preorder (a standard no-go
   result), collapsing [StarAutonomous] to a vacuous predicate in every
   nondegenerate model and excluding the intended examples — the category `Rel`
   of relations, finite-dimensional vector spaces, coherence spaces.  We
   therefore introduce the general base [SymMonClosed] below: the internal hom
   `⇒`, the tensor-hom adjunction `exp_iso` in isomorphism-of-homsets form, and
   its universal property [ump_exponents], over an arbitrary [SymmetricMonoidal]
   structure.  [SymMonClosed] is [ClosedMonoidal] verbatim with the cartesian
   field replaced by a symmetric monoidal one, so every accessor name
   (`exponent_obj`, `exp_iso`, `eval'`, `ump_exponents'`) agrees and the
   cartesian [ClosedMonoidal] is exactly the special case where `⨂` is the
   categorical product.  We do NOT use Structure/Closed.v, an Eilenberg-Kelly
   closed placeholder carrying no tensor-hom adjunction.

   SCOPE (ledger 4).  This file is definition-level only.  The multiplicative
   disjunction `⅋` (par), the linear-distributivity / linearly-distributed
   structure relating `⨂` and `⅋`, and any coherence beyond the three fields of
   [StarAutonomous] are OUT of scope and go to ledger entry 4.  No concrete
   instance is constructed here.

   PRECISION (necessary vs. sufficient — ledger 4).  The three fields make
   [StarAutonomous C] a condition that every genuine *-autonomous category
   satisfies, but NOT yet a sufficient one.  [star_double_dual] posits SOME
   natural isomorphism `x ≅ (x ⇒ ⊥) ⇒ ⊥` as data, rather than requiring the
   CANONICAL dualization map — the transpose of `eval'` through the symmetric
   braid — to be invertible; a model could in principle meet the field with an
   incidental iso that is not the canonical map.  Likewise [star_transpose] is
   definitionally `exp_iso` at the dualizer, so it records data every
   [SymMonClosed] already supplies and constrains no model.  Pinning
   [star_double_dual] to the canonical map and requiring it to be an
   isomorphism (equivalently, the Barr coherence tying the iso to the closed
   structure) is the star-autonomous coherence deferred to ledger entry 4.

   DEVIATION (transpose used for the dual functor).  The monoidal
   [ump_exponents'] field is stated in existence-and-uniqueness form,
   `∃! h, f ≈ eval' ∘ (h ⨂ id)`, and is NOT wired to `curry := to exp_iso`.
   Consequently the beta law `eval' ∘ (curry f ⨂ id) ≈ f` for the packaged
   `curry` is not derivable from the class fields alone.  We therefore transpose
   with the UMP WITNESS itself, [dcur] below, whose defining beta law [dcur_beta]
   and uniqueness [dcur_uniq] come straight from [ump_exponents]; this makes the
   dual functor's [fmap_comp] provable with no additional assumptions. *)

(** ** The genuine symmetric monoidal closed base

    [SymMonClosed] is [ClosedMonoidal] (Structure/Monoidal/Closed.v) verbatim
    except that the underlying `⨂`-structure is an arbitrary [SymmetricMonoidal]
    rather than the [CartesianMonoidal] bundled there.  It packages the internal
    hom `⇒`, the tensor-hom adjunction `exp_iso` in the isomorphism-of-homsets
    form `x ⨂ y ~> z ≊ x ~> y ⇒ z`, and the universal property [ump_exponents']
    in existence-and-uniqueness form.  Keeping the field names identical to
    [ClosedMonoidal] lets the dual functor and the star-autonomous class below
    read exactly as over the cartesian base, now with non-cartesian models
    available. *)

Section SMClosed.

Context {C : Category}.

Reserved Infix "⇒" (at level 30, right associativity).

Class SymMonClosed := {
  smc_is_symmetric : @SymmetricMonoidal C;   (* the underlying ⨂-structure *)

  exponent_obj : obj → obj → obj    (* internal hom; x ⇒ y = exponent_obj x y *)
    where "x ⇒ y" := (exponent_obj x y);

  exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z;

  curry'   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := to (@exp_iso x y z);
  uncurry' {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := from (@exp_iso x y z);

  eval' {x y} : (x ⇒ y) ⨂ x ~> y := @uncurry' _ _ _ id;

  ump_exponents' {x y z} (f : x ⨂ y ~> z) :
    ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id)
}.
#[export] Existing Instance smc_is_symmetric.

Coercion smc_is_symmetric : SymMonClosed >-> SymmetricMonoidal.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : object_scope.

Context `{SymMonClosed}.

Definition ump_exponents {x y z} (f : x ⨂ y ~> z) :
  ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id) := @ump_exponents' _ x y z f.

Arguments eval' {_ _ _} /.

End SMClosed.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : category_scope.

Section StarAutonomous.

Context {C : Category}.
Context `{@SymMonClosed C}.

#[local] Obligation Tactic := idtac.

(** ** The UMP transpose

    [dcur f] is the unique transpose supplied by [ump_exponents]; unlike the
    packaged `curry` (which is `to exp_iso` and is not, over this class, known
    to satisfy the beta law), [dcur] carries the beta law [dcur_beta] and the
    uniqueness principle [dcur_uniq] definitionally. *)

Definition dcur {x y z : C} (f : x ⨂ y ~> z) : x ~> y ⇒ z :=
  unique_obj (ump_exponents f).

Lemma dcur_beta {x y z : C} (f : x ⨂ y ~> z) :
  f ≈ eval' ∘ (dcur f ⨂ id).
Proof. exact (unique_property (ump_exponents f)). Qed.

Lemma dcur_uniq {x y z : C} (f : x ⨂ y ~> z) (v : x ~> y ⇒ z) :
  f ≈ eval' ∘ (v ⨂ id) -> dcur f ≈ v.
Proof. exact (uniqueness (ump_exponents f) v). Qed.

#[local] Program Instance dcur_respects {x y z : C} :
  Proper (equiv ==> equiv) (@dcur x y z).
Next Obligation.
  proper.
  apply dcur_uniq.
  match goal with [ Heq : _ ≈ _ |- _ ] => rewrite Heq end.
  apply dcur_beta.
Qed.

(** Two bookkeeping slides for the tensor bifunctor, factoring a joint action
    `u ⨂ v` through the two one-sided actions in either order. *)

Lemma bimap_slide_l {a a' b b' : C} (u : a ~> a') (v : b ~> b') :
  u ⨂ v ≈ (u ⨂ id) ∘ (id ⨂ v).
Proof.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Lemma bimap_slide_r {a a' b b' : C} (u : a ~> a') (v : b ~> b') :
  u ⨂ v ≈ (id ⨂ v) ∘ (u ⨂ id).
Proof.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** ** The dual (linear-negation) functor `(- ⇒ d) : C^op ⟶ C`

    Contravariant in its argument: a morphism `f : y ~> x` in C is a morphism
    `x ~> y` in `C^op`, and is sent to the precomposition-in-the-exponent map
    `(x ⇒ d) ~> (y ⇒ d)`. *)

Lemma dual_hom_comp (d : C) {x y z : C} (f : z ~> y) (g : y ~> x) :
  dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ (g ∘ f)))
    ≈ dcur (eval' ∘ (@id _ (y ⇒ d) ⨂ f))
        ∘ dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)).
Proof.
  apply dcur_uniq.
  transitivity (eval' ∘ (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)) ⨂ f)).
  - (* left leg: fold `g`'s beta law back into `id ⨂ (g ∘ f)` *)
    symmetry.
    rewrite (bimap_slide_l (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g))) f).
    rewrite comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (@id _ (x ⇒ d) ⨂ g))).
    rewrite <- comp_assoc.
    rewrite <- bimap_comp_id_left.
    reflexivity.
  - (* right leg: fold `f`'s beta law back into `dcur (…g…) ⨂ f` *)
    rewrite (bimap_comp_id_right
               (dcur (eval' ∘ (@id _ (y ⇒ d) ⨂ f)))
               (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)))).
    rewrite comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (@id _ (y ⇒ d) ⨂ f))).
    rewrite <- comp_assoc.
    rewrite <- (bimap_slide_r (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g))) f).
    reflexivity.
Qed.

Program Definition dual (d : C) : C^op ⟶ C := {|
  fobj := fun x => @exponent_obj C _ x d;
  fmap := fun x y f => dcur (eval' ∘ (id ⨂ (f : y ~{C}~> x)))
|}.
Next Obligation.
  (* fmap respects ≈ *)
  proper.
  apply dcur_respects.
  match goal with [ Heq : _ ≈ _ |- _ ] => now rewrite Heq end.
Qed.
Next Obligation.
  (* fmap preserves identities *)
  intros.
  apply dcur_uniq.
  reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition *)
  intros.
  apply dual_hom_comp.
Qed.

(** The double-dual endofunctor `(-)^*^* : C ⟶ C`. *)
Definition double_dual (d : C) : C ⟶ C := dual d ◯ (dual d)^op.

(** ** Star-autonomous structure

    The three defining fields over the closed monoidal base: a dualizing object,
    the closed transpose exhibiting `y ⇒ ⊥` as the dual of `y` (this is
    `exp_iso` at the dualizer, recorded here as data), and the double-dual
    isomorphism together with its naturality. *)

Class StarAutonomous : Type := {
  dualizer : C;

  (* `Hom(x ⨂ y, ⊥) ≅ Hom(x, y ⇒ ⊥)`, the closed transpose at the dualizer. *)
  star_transpose {x y : C} :
    (x ⨂ y ~> dualizer) ≊ (x ~> dual dualizer y);

  (* the double-dual isomorphism `x ≅ x^*^*` *)
  star_double_dual {x : C} :
    x ≅ double_dual dualizer x;

  (* naturality of the double-dual isomorphism *)
  star_natural {a b : C} (f : a ~> b) :
    to (star_double_dual (x:=b)) ∘ f
      << a ~~> double_dual dualizer b >>
    fmap[double_dual dualizer] f ∘ to (star_double_dual (x:=a))
}.

End StarAutonomous.

Arguments dcur {C _ x y z} f.
Arguments dual {C _} d.
Arguments double_dual {C _} d.
Arguments StarAutonomous C {_}.
Arguments dualizer {C _ _}.
