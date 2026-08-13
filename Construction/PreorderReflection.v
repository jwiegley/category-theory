(** * The preorder reflection of a category

    Every category has an underlying preorder on objects: [x ≤ y] whenever
    some morphism [x ~> y] exists.  Passing to it discards the identity of the
    witnessing morphism and keeps only its existence.  The construction that
    performs that erasure while staying inside [Cat] is built here: the same
    objects, with all parallel morphisms identified.  The result is THIN -- at
    most one morphism between any two objects -- and thin categories are
    exactly preorders, as recorded at Theory/Category.v:279-280 and
    Instance/Proset.v:25-31.  See https://ncatlab.org/nlab/show/thin+category.

    NOT THE POSETAL REFLECTION.  These must not be conflated, and the
    difference is exactly which data is discarded.  The nLab's posetal
    reflection (https://ncatlab.org/nlab/show/posetal+reflection) quotients
    OBJECTS by mutual relatedness -- [a ≃ b] when [a ≤ b] and [b ≤ a] -- and
    exhibits posets as reflective in preorders.  [PreorderReflect] does the
    opposite: [preorder_reflect_obj] below proves objects are untouched
    DEFINITIONALLY, and only morphisms are identified.  This construction is
    the category-level ANALOGUE of the posetal reflection, which is how
    jwiegley/category-theory#803 words it; the object-identifying construction
    is a separate obligation that remains open.

    WHY "REFLECTION" IS EARNED HERE.  Not by citation, but by the universal
    property proved below: [ThinLift] shows every functor into a thin category
    factors through [Reflect] uniquely ([ThinLift_proj], [ThinLift_unique]).
    That makes [PreorderReflect C] THE universal thin quotient of [C], rather
    than merely a quotient that happens to be thin.  The full reflective
    adjunction with the inclusion of preorders into [Cat] is a stronger
    statement and is NOT proved here (see SCOPE).

    WHY IT MATTERS HERE.  A diagram commutes exactly when it factors through
    the preorder reflection of its indexing category.  That is the packaging
    Fong and Spivak give for commutativity in Seven Sketches in
    Compositionality §3.3.4, the footnote to Definition 3.51; it is the
    reading that makes
    "commutes" a statement about the SHAPE rather than about any one figure:
    once parallel morphisms of the shape are identified, a functor out of the
    quotient cannot distinguish two parallel paths, so it cannot help but
    commute.  Theory/Diagram.v proves both directions.

    Cited by location only: the Fong-Spivak text was not consulted while
    writing this file, matching the disclosure in Theory/Diagram.v.

    HOW IT IS BUILT.  Nothing new is required.  Construction/Quotient.v already
    quotients a category by a hom-congruence -- [HomCongruence] (:226),
    [Quotient] (:254), [QuotientProj] (:294), and the universal property
    [QuotientLift] (:313) with [QuotientLift_proj] (:322) and
    [QuotientLift_unique] (:334).  The preorder reflection is that quotient at
    the TOTAL congruence, the relation relating every pair of parallel
    morphisms.  All FOUR congruence fields -- [cong_incl], [cong_sym],
    [cong_trans], [cong_comp] -- are immediate, since the relation is
    constantly [True].  (Reflexivity is not a field: it is the derived
    [cong_refl] at Construction/Quotient.v:236.)  Before this file the only in-tree [HomCongruence]
    instances were the PROP and coloured-PROP term congruences.

    NOT [hom_preorder].  Theory/Category.v:282 declares
    [hom_preorder : PreOrder (@hom C)], but that is a different thing and is
    not the reflection: being a [CRelationClasses.PreOrder] on [hom] it is
    [Type]-valued, so it REMEMBERS which morphism witnesses the relation --
    exactly the information the reflection is meant to discard.  Its header
    does not use the phrase "Type-valued"; what it records is that reflexivity
    is witnessed by [id] and transitivity by composition, which is the same
    fact stated constructively.

    SCOPE.  jwiegley/category-theory#803 lists SEVEN work items.  This file
    supplies item 1 (the total hom-congruence and the quotient), plus the
    universal property below.  The remaining SIX are NOT built here and nothing
    below depends on them: the truncated object preorder
    [c ≤ c' := inhabited (c ~> c')] and its comparison with [PreorderReflect]
    (item 2); functoriality of [PreorderReflect] on [Cat] (3); the reflective
    adjunction with the inclusion of preorders (4); Exercise 3.21, the
    reflection of [FreeOnQuiver G] as a reachability preorder (5); Exercise
    3.22, the reflection of the loop category (6); and Remark 3.23's two-sided
    [HomRel] containment (7).

    NAMES.  #803's plan names the module [Construction/PreorderReflection.v]
    and the constant [PreorderReflect]; those two are taken from it so that
    issue lands here cleanly.  [TotalRel], [preorder_reflect_thin], [Reflect],
    [Thin] and [ThinLift] are this file's own coinages, not the plan's. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.

Generalizable All Variables.

(** ** The total hom-congruence *)

(** The relation relating ALL parallel morphisms.  Note this is a relation on
    each hom, not on objects: it never relates morphisms of different type. *)
Definition TotalRel (C : Category) : HomRel C := fun _ _ _ _ => True.

(** Every congruence field is immediate: the relation is constantly [True], so
    inclusion of [≈], symmetry, transitivity, and compatibility with
    composition all hold by [I].  (Reflexivity is derived, not a field.) *)
#[export] Instance TotalRel_Congruence (C : Category) :
  @HomCongruence C (TotalRel C).
Proof. constructor; intros; exact I. Defined.

(** ** The reflection *)

(** Same objects as [C]; parallel morphisms all identified. *)
Definition PreorderReflect (C : Category) : Category :=
  Quotient C (TotalRel C).

(** The defining property: the result is thin.  Thin is exactly "is a
    preorder" (Theory/Category.v:279-280), so this is the sense in which
    [PreorderReflect C] is a preorder rather than merely a category. *)
Lemma preorder_reflect_thin (C : Category) (x y : PreorderReflect C)
      (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(** Objects are untouched -- definitionally, not merely up to iso. *)
Lemma preorder_reflect_obj (C : Category) :
  obj[PreorderReflect C] = obj[C].
Proof. reflexivity. Qed.

(** The reflection map, identity on objects and on morphisms; only the
    hom-setoid coarsens. *)
Definition Reflect (C : Category) : C ⟶ PreorderReflect C :=
  @QuotientProj C (TotalRel C) _.

(** ** The universal property: the universal thin quotient *)

(** A category is THIN when any two parallel morphisms agree.  By
    Theory/Category.v:279-280 that is exactly "is a preorder". *)
Definition Thin (D : Category) : Type :=
  ∀ (x y : D) (f g : x ~> y), f ≈ g.

(** [PreorderReflect C] is thin -- [preorder_reflect_thin] repackaged to the
    predicate, so it can be handed to [ThinLift]. *)
Definition PreorderReflect_Thin (C : Category) : Thin (PreorderReflect C) :=
  fun _ _ _ _ => I.

Section Universal.

Context {C D : Category}.
Context (HD : Thin D).
Context (F : C ⟶ D).

(** Every functor into a thin category factors through the reflection.  The
    hypothesis [QuotientLift] needs -- that [F] identifies related morphisms --
    is discharged by thinness of the target alone, with no condition on [F]. *)
Definition ThinLift : PreorderReflect C ⟶ D :=
  @QuotientLift C (TotalRel C) _ D F (fun x y f g _ => HD _ _ _ _).

(** The factorization reproduces [F] on the nose. *)
Lemma ThinLift_proj {x y : C} (f : x ~> y) :
  fmap[ThinLift] (fmap[Reflect C] f) = fmap[F] f.
Proof. reflexivity. Qed.

(** ...and it is the only such functor -- in a form STRONGER than the usual
    uniqueness clause, so read the hypotheses carefully.  No agreement between
    [G] and [F] after the reflection is assumed; object agreement [Hobj] alone
    (needed anyway for the statement to typecheck, since [hom_cast] transports
    along it) already pins [G] on every hom.  The proof is [apply HD] and uses
    nothing else, which is exactly the content: a thin target leaves no room
    for two functors with the same object action to differ, so a fortiori none
    for two different factorizations of [F]. *)
Lemma ThinLift_unique (G : PreorderReflect C ⟶ D)
      (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
      {x y : C} (f : x ~{PreorderReflect C}~> y) :
  hom_cast (Hobj x) (Hobj y) (fmap[G] f) ≈ fmap[ThinLift] f.
Proof. apply HD. Qed.

End Universal.

(** So [PreorderReflect C] is THE universal thin quotient of [C], not merely a
    quotient that happens to be thin.  This is what earns the word
    "reflection" here; the full reflective adjunction with the inclusion of
    preorders into [Cat] is stronger and is item 4 of #803. *)
