(** * Size vocabulary: small, locally small, and the arrows-with-dom-cod packaging

    Mac Lane fixes ZFC plus one universe [U] and calls a set, a function, or a
    category SMALL when it lies in [U] (Categories for the Working
    Mathematician, 2nd ed., §I.6, printed pp. 22-24).  Awodey Definition 1.11
    says a category is small when its objects [C0] and its arrows [C1] are both
    sets, and Definition 1.12 calls it LOCALLY SMALL when each [Hom(X,Y)] is a
    set.  Riehl Definition 1.1.6 says the same with "a set's worth of arrows",
    and Definition 1.1.7 the same for local smallness.

    This library takes a different foundational route, and docs/SIZE.md sets
    the two side by side in full.  The short version: there is no universe
    object, no membership, and no size axiom.  [Class Category@{o h p}]
    (Theory/Category.v:111) is universe-POLYMORPHIC, so every category already
    carries its own three levels, and the work Mac Lane's [U] does is done by
    the elaborator's constraint solver.  That is why self-membership is a
    universe inconsistency rather than a paradox to be excluded by axiom
    (Instance/Cat.v:108-114).

    WHAT THIS FILE ADDS, AND WHY IT IS NOT REDUNDANT.  The discipline above is
    enforced but was UNSTATABLE: before this file `Small`, `IsSmall` and
    `LocallySmall` had no declaration anywhere in the tree, so smallness could
    be neither a hypothesis nor a conclusion -- it could only be chosen at a
    definition site by instantiating universes.  Theory/Lawvere/Sets.v:44
    records the consequence in passing ("the library has no smallness
    machinery").  The predicates below are that missing vocabulary.

    THE DESIGN, AND THE ONE THING THAT MAKES IT WORK.  A category is small
    RELATIVE TO A PAIR OF LEVELS when its objects and each of its hom-setoids
    are matched by copies at those levels.  All the content sits in the strict
    constraints [uo < o] and [uh < h]: without them one could discharge
    [Small C] for every [C] by handing back [obj[C]] and [hom] themselves, and
    the predicate would be vacuously true.  With them that discharge is a
    universe inconsistency -- Test/Size.v exhibits exactly that, since
    demonstrating it needs the rejection vernacular, which this file avoids so
    that the [make todo] sweep sees no new hit from here.

    OBJECTS USE [=], HOMS USE [≈].  Objects carry no setoid in this library, so
    a bijection of object types is Leibniz; that matches Instance/StrictCat.v's
    treatment.  Morphisms do carry setoids, and CLAUDE.md's standing rule is
    that [=] is never used on them, so the hom half is a SETOID ISOMORPHISM.
    This is not a stylistic choice: stating the hom round trip with [=] is also
    REJECTED, because the [eq] lemmas it drags in impose constraints
    ([h <= eq_ind.u0]) that a declared universe binder cannot mention.

    A TWO-SIDED SITUATION, RECORDED AS SUCH.  What the library PROVIDES is
    stronger than the books' convention: [Class Category]'s [homset] field
    (Theory/Category.v:116) gives every category hom-setoids at a fixed level
    [h], so local smallness holds by construction and a non-locally-small
    category is not expressible.  [locally_small_ambient] below records that as
    a lemma rather than as prose, which is what makes the observation checkable.
    What the library LACKED is the predicate needed to state the distinction at
    all, and that is what [LocallySmall] supplies.  Accordingly [LocallySmall]
    is stated with a NON-STRICT [uh <= h], so that the ambient instance exists;
    [Small] is stated with strict constraints, so that it has content.  Both
    readings are deliberate and neither is an oversight.

    The books are cited BY LOCATION only.  Their printed text was not consulted
    while writing this file; the locations record where each definition is
    stated, and the Coq below stands on its own.  The attributions follow issue
    jwiegley/category-theory#253, which supplies them. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.One.

Generalizable All Variables.

(** ** A level-polymorphic identity type for objects *)

(** Objects carry no setoid in this library, so an object bijection has to be
    stated with an identity type.  Stdlib [eq] cannot be used HERE, and the
    reason is a genuine portability constraint rather than a preference: on
    Coq 8.19 and 8.20 [eq] is pinned to a global universe, so mentioning it
    inside a definition that DECLARES its own universe binder yields
    "Universe constraints are not implied by the ones declared: o <= eq.u0",
    which a binder has no syntax to discharge.  Rocq 9.1 made [eq] polymorphic
    and accepts the same text, so this breaks only on the older toolchains --
    exactly the kind of divergence the three-version build exists to catch.

    Two details, since both are easy to state too broadly.  First, the trigger
    is not merely declaring a universe binder: [Definition d@{u} (A : Type@{u})
    (x : A) : x = x := eq_refl] SUCCEEDS on 8.19 and 8.20.  What breaks is a
    binder carrying an explicit constraint clause -- both [@{u | }] and
    [@{u v | u <= v}] are rejected.  Second, [ObjEq] is used in the two
    [arrow_quiver_*] lemmas below as well, which carry no binder at all; it is
    used there for uniformity with the [ArrowQuiver] fields they are about, not
    from necessity.

    [ObjEq] follows the [poly_unit@{u}] idiom at Lib/Setoid.v:56. *)
Inductive ObjEq@{u} {A : Type@{u}} : A → A → Type@{u} :=
  obj_refl : ∀ a : A, ObjEq a a.

Arguments obj_refl {A} a.


(** ** Local smallness *)

(** Awodey Definition 1.12 / Riehl Definition 1.1.7: only a set's worth of
    morphisms between any two objects.  "A set's worth" is read as: matched by
    a setoid at level [uh].

    [uh <= h] is deliberately NON-STRICT, so that [locally_small_ambient] below
    can witness the predicate at a category's own hom level.  Instantiating it
    at a strictly smaller [uh] is the reading with content. *)
Class LocallySmall@{o h p uh up | h <= p, uh <= up, uh <= h}
      (C : Category@{o h p}) := {
  ls_hom     : ∀ (x y : C), Type@{uh};
  ls_setoid  : ∀ x y, Setoid@{uh up} (ls_hom x y);

  ls_to      : ∀ {x y}, ls_hom x y → (x ~> y);
  ls_from    : ∀ {x y}, (x ~> y) → ls_hom x y;

  (* Respectfulness is stated directly rather than through [Proper]: the
     relation spans both hom types, so a [Proper] instance lands at
     max(h,uh) and cannot be a field constrained to [Type@{uh}]. *)
  ls_to_resp : ∀ {x y} (u v : ls_hom x y),
                 @Setoid.equiv _ (ls_setoid x y) u v → ls_to u ≈ ls_to v;

  (* [ls_from] must respect [≈] too.  Without this field the structure is only
     a section/retraction pair and NOT a setoid isomorphism: [ls_from] could
     send [≈]-equal morphisms to unrelated small representatives, and no such
     field is derivable from the others.  A countermodel exists -- a category
     whose hom-setoid relates everything, resized by a small setoid that
     relates nothing, satisfies every other field. *)
  ls_from_resp : ∀ {x y} (f g : x ~> y),
                 f ≈ g → @Setoid.equiv _ (ls_setoid x y) (ls_from f) (ls_from g);

  ls_to_from : ∀ {x y} (f : x ~> y), ls_to (ls_from f) ≈ f;
  ls_from_to : ∀ {x y} (u : ls_hom x y),
                 @Setoid.equiv _ (ls_setoid x y) (ls_from (ls_to u)) u
}.

(** EVERY category is locally small at its own hom level, by the identity
    resizing.  This is Riehl's "each of these is locally small" (Definition
    1.1.7 and the discussion after Example 1.1.3) turned into a lemma.

    Note precisely what it does and does not say.  It is not that local
    smallness is a theorem of category theory -- it is that [Class Category]
    BUILDS IT IN, by giving [homset] at a fixed level.  So in this library the
    book's distinction between "small" and "merely locally small" collapses on
    the locally-small side: the predicate is universally satisfiable at the
    ambient level, and only acquires content strictly below it. *)
Definition locally_small_ambient@{o h p | h <= p} (C : Category@{o h p})
  : LocallySmall@{o h p h p} C :=
  @Build_LocallySmall@{o h p h p} C
    (fun x y => (x ~> y))
    (@homset C)
    (fun _ _ f => f)
    (fun _ _ f => f)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H)
    (fun x y f => reflexivity f)
    (fun x y u => reflexivity u).

(** ** Smallness *)

(** Awodey Definition 1.11 / Riehl Definition 1.1.6: the objects and the arrows
    are both sets.  Here BOTH constraints are strict, and that is the whole
    content of the definition. *)
Class Small@{o h p uo uh up | h <= p, uh <= up, uo < o, uh < h}
      (C : Category@{o h p}) := {
  small_locally     :: LocallySmall@{o h p uh up} C;

  small_ob          : Type@{uo};
  small_ob_to       : small_ob → obj[C];
  small_ob_from     : obj[C] → small_ob;
  small_ob_to_from  : ∀ x, ObjEq (small_ob_to (small_ob_from x)) x;
  small_ob_from_to  : ∀ a, ObjEq (small_ob_from (small_ob_to a)) a
}.

(** "Every small category is locally small" (Awodey, the note after Definition
    1.12; Riehl, likewise).  Here it is a projection -- which is the honest
    form, since smallness was DEFINED to include the hom condition. *)
Definition small_locally_small@{o h p uo uh up
    | h <= p, uh <= up, uo < o, uh < h}
  (C : Category@{o h p}) (S : Small@{o h p uo uh up} C)
  : LocallySmall@{o h p uh up} C := small_locally.

(** A setoid whose equivalence is constantly [True]: any two elements agree.
    Used below for the one-element small hom, mirroring the device at
    Construction/Sq.v:41 and Instance/Proset.v:39.  Kept [#[local]] for the
    reason Construction/Sq.v:38-40 gives for its own copy: applied to a
    data-carrying type it would silently identify everything, so it must not
    leak into the library interface. *)
#[local] Definition True_setoid@{u p} (A : Type@{u}) : Setoid@{u p} A :=
  {| Setoid.equiv    := fun _ _ => True
   ; setoid_equiv    :=
       {| Equivalence_Reflexive  := fun _ => I
        ; Equivalence_Symmetric  := fun _ _ _ => I
        ; Equivalence_Transitive := fun _ _ _ _ _ => I |} |}.

(** The terminal category is small: one object and one arrow, so [poly_unit] at
    the lower levels serves as the small copy.

    Every proof term is given EXPLICITLY rather than by [destruct] or [Program].
    That is not fastidiousness: the [destruct] route elaborates through
    [eq_ind], whose global universe ([eq_ind.u0]) a declared universe binder
    cannot mention, so the definition is rejected with "Universe constraints are
    not implied by the ones declared".

    The hom half is split out with an explicit type ascription because a nested
    record literal leaves the class parameter [C] unresolved. *)
(* No explicit universe binder here, deliberately, and the hom half is INLINED
   rather than named separately.  Two distinct obstacles force this shape:

   - [_1]'s hom-setoid is [Morphism_equality], a [Program Definition] whose own
     obligations carry constraints on [eq]'s global universes ([eq_ind.u0]).  A
     declared binder cannot mention those, so declaring one makes the witness
     un-typecheckable.
   - Naming the hom half separately makes Coq solve its constraints in
     isolation, where it collapses [uh] to [h]; the result then cannot be used
     at the strict [uh < h] that [Small] demands.  Inlining lets both halves be
     solved together.

   Nothing is given up.  The STRICTNESS lives in the class, so any inhabitant
   of [Small] satisfies [uo < o] and [uh < h] by [Small]'s own constraints --
   which is exactly why this witness is evidence that those constraints are
   satisfiable rather than merely restrictive. *)
Definition One_Small : Small _1 :=
  @Build_Small _1
    (@Build_LocallySmall _1
       (fun _ _ => poly_unit)
       (fun _ _ => True_setoid poly_unit)
       (fun _ _ _ => ttt)
       (fun _ _ _ => ttt)
       (fun _ _ _ _ _ => eq_refl)
       (fun _ _ _ _ _ => I)
       (fun _ _ f => match f with ttt => eq_refl end)
       (fun _ _ _ => I))
    poly_unit
    (fun _ => ttt)
    (fun _ => ttt)
    (fun x => match x with ttt => obj_refl ttt end)
    (fun a => match a with ttt => obj_refl ttt end).

(** ** Riehl's arrows-with-domain-and-codomain packaging *)

(** Riehl Remark 1.1.2 (used again at Definition 1.1.6) packages a category as
    a set of objects, a set of morphisms, and functions [dom], [cod], [id],
    with [dom] and [cod] retracting [id].

    The tree's [Quiver] (Construction/Free/Quiver.v:54) is the INDEXED
    presentation -- [edges : nodes → nodes → Type] -- in which [dom] and [cod]
    are carried by the indexing rather than by functions, and it has no
    identity selection at all, so it supplies neither half of Riehl's
    retraction.  A "reflexive quiver" appears nowhere in the tree.

    Both presentations are given below, because the difference is exactly where
    the retraction laws live.  In the UNINDEXED form they are genuine equations
    that a candidate must satisfy; in the INDEXED form they are definitional,
    since an identity edge at [x] has source and target [x] by typing.  That is
    worth having on record: it is a case where the library's formulation makes
    a book axiom disappear rather than proving it. *)

(** The unindexed packaging, as Riehl states it. *)
Record ArrowQuiver@{u} := {
  aq_ob      : Type@{u};
  aq_mor     : Type@{u};
  aq_dom     : aq_mor → aq_ob;
  aq_cod     : aq_mor → aq_ob;
  aq_id      : aq_ob → aq_mor;
  aq_dom_id  : ∀ x, ObjEq (aq_dom (aq_id x)) x;
  aq_cod_id  : ∀ x, ObjEq (aq_cod (aq_id x)) x
}.

(** The total arrow collection of a category: Awodey's [C1], Riehl's "a set's
    worth of arrows".  Note it bundles the endpoints, so its level is at least
    that of the objects -- which is why Awodey's Definition 1.11 needs BOTH
    halves and not just the hom condition. *)
(** The total arrow collection of a category: Awodey's [C1], Riehl's "a set's
    worth of arrows".  Note it BUNDLES the endpoints, so its level is at least
    that of the objects -- which is exactly why Awodey's Definition 1.11 needs
    both halves rather than the hom condition alone.  An [ArrowQuiver] keeps
    objects and arrows in ONE universe, the way a set-theoretic presentation
    keeps them both sets; universes are left to inference here, since
    [sigT]'s projections carry global constraints ([Projections.u0]) that a
    declared binder cannot mention, and no strictness is wanted at this
    point anyway. *)
Definition TotalMor (C : Category) : Type :=
  { x : obj[C] & { y : obj[C] & x ~{C}~> y }}.

(** A category packages as an [ArrowQuiver], and both retraction laws hold
    by [obj_refl] -- the identity arrow at [x] is stored with [x] as both of
    its endpoints, so [aq_dom] and [aq_cod] project it back definitionally.

    Proof terms are explicit rather than left to [Program]: see the note on
    [One_Small] above for why the [eq]-lemma route is not available under a
    declared universe binder.

    SCOPE.  Leaving universes to inference here has one consequence worth
    stating rather than leaving to be discovered: it forces [p] equal to [h],
    so this applies to every category whose hom-setoid proofs sit at the hom
    level -- which is every category in the tree, since inference unifies them
    at each use site -- but NOT to a hypothetical [C : Category@{o h p}] with
    strictly [h < p], which the class permits.  [locally_small_ambient] carries
    no such restriction. *)
Definition ArrowQuiverOfCat (C : Category) : ArrowQuiver :=
  {| aq_ob     := obj[C]
   ; aq_mor    := TotalMor C
   ; aq_dom    := fun m => projT1 m
   ; aq_cod    := fun m => projT1 (projT2 m)
   ; aq_id     := fun x => existT _ x (existT _ x (@id C x))
   ; aq_dom_id := fun x => obj_refl x
   ; aq_cod_id := fun x => obj_refl x |}.

(** The two retraction laws, stated separately so the file records that in this
    presentation they are DEFINITIONAL rather than assumed -- the point of
    giving both packagings. *)
Lemma arrow_quiver_dom_id (C : Category) (x : obj[C]) :
  ObjEq (aq_dom (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x.
Proof. exact (obj_refl x). Qed.

Lemma arrow_quiver_cod_id (C : Category) (x : obj[C]) :
  ObjEq (aq_cod (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x.
Proof. exact (obj_refl x). Qed.
