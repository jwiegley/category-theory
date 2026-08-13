(** * Coproducts as the left adjoint of the diagonal functor

    Mac Lane, "Categories for the Working Mathematician", §IV.1, p. 84, and
    Awodey, "Category Theory", §9.3, p. 225, are cited BY LOCATION ONLY: the
    printed text at those two locations was not consulted while this file was
    written, and both locations are the ones recorded in issue
    jwiegley/category-theory#351, which this file answers.

    The tree already carries the other half of the triple: the binary product
    bifunctor is a RIGHT adjoint of the binary diagonal
    [Δ = Diagonal_Product C : C ⟶ C ∏ C], namely
    Adjunction/Diagonal/Product.v:38's [Diagonal_Product_Adjunction], over the
    bifunctor Functor/Product/Internal.v:34 with its notation [×(C)]
    (Functor/Product/Internal.v:51).  Here the coproduct bifunctor [+(C)] is
    built and shown to be a LEFT adjoint of that same diagonal, with the
    statement read in [C] itself: no [^op] occurs in the type of
    [Diagonal_Coproduct_Adjunction].  The unit and counit of the adjunction
    are then named and identified -- the pair of injections, and the folding
    map [id ▽ id].

    ON THE DUALITY ROUTE.  Structure/Cocartesian.v:115 defines [Cocartesian C]
    to BE [@Cartesian (C^op)], so the product adjunction taken at [C^op] and
    pushed through Adjunction/Opposite.v:34's [Opposite_Adjunction] is already
    a term, of type [×(C^op)^op ⊣ (Diagonal_Product C^op)^op].  Two
    observations about that term were checked at the Rocq prompt while this
    file was prepared; they are not re-checked by the build.  Its right-hand
    endpoint is already the covariant one: [Opposite_Functor (Diagonal_Product
    (Opposite C))] and [Diagonal_Product C] are equal by [reflexivity], at
    Leibniz equality.  Its left-hand endpoint is not: [Opposite_Functor
    (×(Opposite C))] and [+(C)] do not unify: ascribing the whole record is
    rejected with a bare top-level type mismatch (no field is named), and
    comparing the two functor records shows [fobj] and [fmap] converging while
    all three opaque [Program]-obligation fields ([fmap_respects], [fmap_id],
    [fmap_comp]) differ.  So the coproduct bifunctor has
    to be given directly on either route, and the dualized term reaches the
    covariant statement by re-assembling Theory/Adjunction.v:130's
    [Adjunction] class field by field (a [Build_Adjunction] with five
    projections, which does typecheck, since no field of that class mentions
    [fmap_respects]).  The route taken below gives the two transposes
    directly, mirroring Adjunction/Diagonal/Product.v:38 field for field; the
    statement, the transposes and the identification lemmas are then all read
    in [C], and the obligations close by the coproduct laws of
    Structure/Cocartesian.v.

    NOT TO BE CONFUSED WITH Functor/Coproduct.v:61's [CoproductFunctor], which
    is the fold out of the coproduct CATEGORY [C ∐ C]; the bifunctor here has
    the product category [C ∏ C] as its domain. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.

Generalizable All Variables.

(** ** The coproduct bifunctor *)

(** [+(C) : C ∏ C ⟶ C], the dual of Functor/Product/Internal.v:34's [×(C)].
    On a pair of morphisms it is the copairing of the two injections after
    each component. *)
#[export]
Program Instance InternalCoproductFunctor `(C : Category) `{@Cocartesian C} :
  C ∏ C ⟶ C := {
  fobj := fun p => fst p + snd p;
  fmap := fun _ _ p => (inl ∘ fst p) ▽ (inr ∘ snd p)
}.
Next Obligation.
  proper.
  simpl in *.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  (* [merge_comp] (Structure/Cocartesian.v:200) reads
     [(g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h]: the common factor stands on the LEFT,
     the mirror of [fork_comp]'s right one.  The script below therefore uses
     [comp_assoc] forward before [inl_merge]/[inr_merge]; the corresponding
     step of Functor/Product/Internal.v:45-48 uses it backwards. *)
  simpl in *.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge, inr_merge.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Notation "+( C )" := (@InternalCoproductFunctor C _)
  (at level 0, format "+( C )") : functor_scope.

(** ** The adjunction *)

(** [+(C) ⊣ Δ].  The forward transpose splits a map out of a coproduct into
    its two restrictions, [f ↦ (f ∘ inl, f ∘ inr)]; the inverse copairs a pair
    of maps, [g ↦ fst g ▽ snd g].  Read in [C^op] these are the transposes of
    Adjunction/Diagonal/Product.v:41-42.

    The global obligation tactic of Lib/Tactics.v:225 ([cat_simpl]) is left in
    force, as in the product file, and five scripts remain: the [Proper] of
    the inverse transpose, one round trip, and three of the four naturality
    squares.  Program re-runs the obligation tactic as obligations become
    unblocked, so these five scripts are not in bijection with the five fields
    of Theory/Adjunction.v:130.  The first three mirror
    Adjunction/Diagonal/Product.v:44, :45 and :48 with [merge] for [fork].
    The last two are [merge_comp] orientation steps, written out explicitly.
    [unmerge] (Structure/Cocartesian.v:204 -- an unfold/simpl prefix followed
    by [repeat (rewrite <- !merge_comp; cat; rewrite <- !comp_assoc; cat)])
    closes the second of them but not the first: its final rewrite
    right-associates composites, the direction suited to [fork_comp]'s common
    RIGHT factor, while [merge_comp] factors on the LEFT.  Both are written
    out so the orientation is visible rather than split across two styles. *)
#[export]
Program Instance Diagonal_Coproduct_Adjunction (C : Category) `{@Cocartesian C} :
  +(C) ⊣ Diagonal_Product C := {
  adj := fun _ _ =>
    {| to   := {| morphism := fun f => (f ∘ inl, f ∘ inr) |}
     ; from := {| morphism := fun f => fst f ▽ snd f |} |}
}.
(* The inverse transpose respects the pairwise equivalence of [C ∏ C]
   (Construction/Product.v:97-104), by [merge_respects]
   (Structure/Cocartesian.v:136). *)
Next Obligation. proper; apply merge_respects; auto. Qed.
(* Round trip [(x ∘ inl) ▽ (x ∘ inr) ≈ x]: [merge_comp] factors [x] out,
   leaving [x ∘ (inl ▽ inr)], and [cat] finishes with [merge_inl_inr]
   (Structure/Cocartesian.v:189) and the identity law. *)
Next Obligation. rewrite merge_comp; cat. Qed.
(* Naturality in the [C ∏ C] argument: one equation per component, hence the
   [split], each an [inl_merge]/[inr_merge] step. *)
Next Obligation. split; unmerge. Qed.
(* [merge_comp] backwards on the right-hand side, then [comp_assoc] forward so
   that [inl_merge] and [inr_merge] apply under the composites. *)
Next Obligation.
  rewrite <- merge_comp, !comp_assoc, inl_merge, inr_merge; reflexivity.
Qed.
(* This square is [merge_comp] itself. *)
Next Obligation. apply merge_comp. Qed.

(** ** Unit and counit

    Theory/Adjunction.v:214-215 defines [unit := ⌊id⌋] and [counit := ⌈id⌉] as
    plain MORPHISMS; the class at Theory/Adjunction.v:130 carries no
    natural-transformation field, so the identifications below are single [≈]
    equations quantified over the object.  The notations [⌊-⌋], [⌈-⌉], [η] and
    [ε] are local to the section in Theory/Adjunction.v, so [unit] and
    [counit] are spelled out here with their four implicit arguments. *)

(** The unit at [p = (a, b)] is the pair of injections into [a + b]. *)
Definition coproduct_unit (C : Category) `{@Cocartesian C} (p : C ∏ C) :
  p ~{C ∏ C}~> Diagonal_Product C (fst p + snd p) := (inl, inr).

(** The counit at [x] is the folding map [x + x ~> x]. *)
Definition coproduct_counit (C : Category) `{@Cocartesian C} (x : C) :
  x + x ~{C}~> x := id ▽ id.

Lemma coproduct_unit_is_unit (C : Category) `{@Cocartesian C} (p : C ∏ C) :
  @unit _ _ +(C) (Diagonal_Product C) (Diagonal_Coproduct_Adjunction C) p
    ≈ coproduct_unit C p.
Proof. unfold coproduct_unit; simpl; split; cat. Qed.

(** The componentwise reading of the same equation: equivalence in [C ∏ C] is
    the pair of the two component equivalences (Construction/Product.v:97-104),
    so this and [coproduct_unit_is_unit] are one statement. *)
Lemma coproduct_unit_components (C : Category) `{@Cocartesian C}
      (p : C ∏ C) :
  fst (@unit _ _ +(C) (Diagonal_Product C)
         (Diagonal_Coproduct_Adjunction C) p) ≈ inl ∧
  snd (@unit _ _ +(C) (Diagonal_Product C)
         (Diagonal_Coproduct_Adjunction C) p) ≈ inr.
Proof. simpl; split; cat. Qed.

(** A definitional check, not a use of any coproduct law: [counit] is [⌈id⌉],
    which unfolds to [fst (id, id) ▽ snd (id, id)], so the two sides are
    convertible and [reflexivity] closes the goal. *)
Lemma coproduct_counit_is_counit (C : Category) `{@Cocartesian C} (x : C) :
  @counit _ _ +(C) (Diagonal_Product C) (Diagonal_Coproduct_Adjunction C) x
    ≈ coproduct_counit C x.
Proof. unfold coproduct_counit; reflexivity. Qed.

(** ** Sanity: the adjunction at two concrete cocartesian categories

    Issue #351's work item 4 asks for a sanity example so that the prose
    promise in Adjunction/GAFT/Examples.v points at real code; the
    GAFT-side reconstruction itself remains not undertaken, as that file
    says.  These two instantiations also make the non-vacuity of the
    hypothesis class an in-tree, build-checked fact rather than an ad-hoc
    observation: [Coq] (Instance/Coq.v:199) and [Sets]
    (Instance/Sets/Cocartesian.v:28) both carry [Cocartesian] instances,
    and the adjunction specializes to each.  Importing concrete instances
    into an Adjunction/ file follows the precedent of Adjunction/GAFT/Sets.v. *)

Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cocartesian.

Example coq_coproduct_diagonal : +(Coq) ⊣ Diagonal_Product Coq :=
  Diagonal_Coproduct_Adjunction Coq.

Example sets_coproduct_diagonal : +(Sets) ⊣ Diagonal_Product Sets :=
  Diagonal_Coproduct_Adjunction Sets.
