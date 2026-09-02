(** * Ord, the category of all preorders (Mac Lane's Preord)

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer GTM 5, §IV.3, printed p. 92, Exercise 4.  Read from
          the page image rather than from memory: "4. Show the following
          subcategories to be reflective: (a) The full subcategory of all
          partial orders in the category Preord of all preorders, with
          arrows all monotone functions.  (b) The full subcategory of
          T_0-spaces in Top."  Catalog id: maclane:IV.3:ex4.

    This file and Instance/Ord/Poset.v are half (a).  Half (b) is
    Instance/Top/Kolmogorov.v, written in parallel against the same
    brief; nothing here depends on it and nothing there depends on this.

    ** What is delivered here

    Mac Lane's AMBIENT category, which the exercise cannot even be stated
    without: [Ord], whose objects are preordered setoids and whose
    morphisms are the monotone maps.  Around it, [OrdObject], [OrdHom],
    [OrdHom_Setoid], [ord_hom_id], [ord_hom_compose], the forgetful
    [Ord_Forget : Ord ⟶ Sets], the predicate [OrdAntisymmetric], the full
    subcategory [Pos_Sub]/[Posets] with its inclusion proved Full AND
    Faithful, the comparison with the pre-existing [Pos], and the bridge
    to the thin-category reading.  The REFLECTION itself -- the exercise's
    actual content -- is the sibling file Instance/Ord/Poset.v, whose
    pinned artifact is [Poset_Reflective_in_Ord].

    ** The name

    Mac Lane writes Preord.  This file writes [Ord], because issue #372
    pins the verification name [Poset_Reflective_in_Ord] and a category
    named [Preord] would make that name read wrongly.  The header of
    Instance/Proset.v anticipated exactly this object and called it "an
    Ord category", so the spelling is the tree's own.

    ** Reused, and what that saves

    [OrdObject] is Instance/Pos.v:81's [PosetObject] MINUS its last field
    [pos_antisym], field for field and name for name with an [ord_]
    prefix; [OrdHom] is :99's [MonoHom] likewise; [OrdHom_Setoid],
    [ord_hom_id], [ord_hom_compose], [ord_hom_compose_respects], [Ord]
    and [Ord_Forget] are :112, :125, :130, :139, :150 and :164 with the
    same proofs.  That is deliberate and it is what makes the comparison
    below cheap: the two records differ in exactly one field, so
    [OrdObject_of_Poset] drops it and [Poset_of_antisym] supplies it, and
    BOTH object round trips close by [eq_refl] (record eta -- Lib.v:10
    sets [Set Primitive Projections], and [About] reports both records as
    having primitive projections with eta conversion).

    Also reused: Construction/Subcategory.v's [Subcategory] (:36), [Sub]
    (:55), [Incl] (:64), [Incl_Faithful] (:89), [Full] (:99) and
    [Full_Implies_Full_Functor] (:104), with the trivially-true [shom] of
    Instance/Ab/TorsionFree.v:386's [TorsionFree_Sub] and
    Instance/Rng.v's [CRng_Sub]; [Full] is written qualified as
    [Category.Construction.Subcategory.Full] for the reason that file
    gives -- it exports its OWN [Full], whose first argument is a
    Category.  Instance/Proset.v:35's [Proset] supplies the thin category.
    Instance/StrictCat.v:56's [StrictCat] hosts the comparison.

    NEW here: everything about the ANTISYMMETRY-FREE record, the
    subcategory of partial orders inside it, the two passages to and from
    [PosetObject] and the functors they induce, and [ord_le_of_equiv].

    ** Prior art, measured at d658518e (the issue's "Current state" is
       stale in one direction and right in another)

    Issue #372 says "both ambient categories are missing" and "there is no
    Instance/Top.v".  Both are false: Instance/Top.v:273 declares [Top],
    and Instance/Pos.v:150 declares [Pos], the category whose OBJECTS are
    posets.  What IS absent, and is supplied here, is a category of ALL
    preorders: [rg -i 'PreorderObject|ProsetObject|OrdObject|OrdHom'] over
    the .v files returns ZERO hits at d658518e, and the only in-tree
    reading of "preorder as a category" is Instance/Proset.v:35's
    [Proset P], which turns ONE preorder into a thin category.  A
    case-sensitive [rg -n '\bPreord\b'] returns three lines, all in
    Instance/Roster.v (:128, :140, :413) and all prose.

    Two pieces of that prose are made false by this file and are NOT
    edited here (they belong to their own files): Instance/Proset.v:20-22
    says the preorder analogue "does not exist yet", and
    Instance/Roster.v:140 says Mac Lane's "Preord" is [Proset] -- which
    was never right, [Proset] being one preorder rather than the category
    of all of them.

    ** The reviewer's distinction, as constructions rather than prose

    The check on this issue is that [Ord] really is the category of ALL
    preorders and not a single preorder viewed as a thin category.  Both
    readings are built and both are pinned by computation:
    [Ord_obj_are_preorders] records [obj[Ord] = OrdObject] and
    [OrdAsCategory_obj_are_points] records
    [obj[OrdAsCategory P] = carrier (ord_setoid P)], each by [eq_refl];
    their IDENTIFICATION is refuted in Test/ProbeOrd372.v.  The passage
    between them runs one way only and is the one Instance/Pos.v:191/:197
    already takes for posets: [OrdAsCategory] sends a preorder to its thin
    category and [OrdHomAsFunctor] sends a monotone map to the induced
    functor, whose three laws are equations between parallel morphisms in
    a thin target and hence [I].  There is no passage the other way, and
    none is claimed: an object of [Ord] carries a setoid and a relation,
    where a thin category carries neither.

    ** The comparison with [Pos], and its strength

    [Pos_Posets_strict_iso : @Isomorphism StrictCat Pos Posets] -- an
    ISOMORPHISM OF CATEGORIES, not merely an equivalence.  The weaker
    [≅[Cat]] reading is what [Cat]'s hom-setoid ([Functor_Setoid], natural
    isomorphism) would give; [StrictCat] compares functors by
    Theory/Functor.v:606's [Functor_StrictEq_Setoid], object equality on
    the nose plus a transported agreement of the arrow actions, and both
    round trips meet it.  One of the two [eq_on_obj] families is
    [fun P => eq_refl] outright; the other, [posets_pos_posets_obj], needs
    a [destruct] first, because an object of [Posets] is a stdlib [sigT]
    and stdlib [sigT] is not covered by Lib.v:10's [Set Primitive
    Projections], so [(`1 x; `2 x) = x] is not definitional.  That
    rejection is pinned as the probe's first negative, with
    [posets_pos_posets_obj] itself as its control -- the SAME statement
    proved, so the negative measures the missing eta and nothing else.

    ** Strengths, measured strict-first

    Eleven [eq_refl] occurrences, all outside any rejection:
    [poset_ord_poset_round] and [ord_poset_ord_round] (both object round
    trips, on the WHOLE record); [pos_to_posets_obj], [posets_to_pos_obj],
    [pos_roundtrip_obj] and [pos_roundtrip_map] (the two functors' actions
    and the [Pos]-side round trip on objects and on the underlying map);
    [ord_functor_fobj]; [Ord_obj_are_preorders] and
    [OrdAsCategory_obj_are_points]; and [monotone_functor_fobj]'s
    counterpart is Instance/Pos.v:210, not restated.

    ** Universes

    Measured with [Set Printing Universes] on all 66 constants of this
    module, reading BOTH the binder and the constraint block.  NO
    constraint block of any constant carries a universe EQUATION -- every
    entry is [<] or [<=].  The identifications live in BINDERS, and they
    are the donors':

    - [Ord@{u u0 u1 u2 u3 u4} : Category@{u u4 u4}] identifies hom with
      proof.  So does [Pos@{u u0 u1 u2 u3 u4} : Category@{u u4 u4}] --
      character for character the same binder and the same twelve-entry
      block, which is the measurement behind calling this INHERITED from
      the Instance/Pos.v template rather than introduced here.
    - [Subcategory@{u u0 u1 u2} : Category@{u u0 u0} -> Type] identifies
      hom with proof too, on an EMPTY constraint block; [Posets] is
      [Category@{u0 u u}] and [Pos_Sub] is
      [Subcategory@{u u0 u0 u1} Ord@{...}].  This is the one guarded
      rejection: the probe declares [uh < up] and finds [Subcategory C]
      refused with "Cannot enforce up = uh" while [x ~> y] and [id{C}] at
      those very levels are accepted.  [Reflective] cannot be tested apart
      from it -- [Reflective@{u u0 u1 u2 u3 u4 u5}] takes a
      [Subcategory@{u3 u5 u4 u5} C] over [Category@{u3 u5 u5}] -- so no
      second formability negative is stated, and whether [Reflective]
      identifies anything OF ITS OWN is not measured here.  Neither
      identification is claimed unavoidable.

    113 of the 122 constants of the two files carry a [Set] token in a
    universe instance or a constraint block (the nine that do not are the
    [MixPt] inductive family and [mix_le]), always as a BOUND ([Set < u])
    and never as an equation.  The cause is the
    [Prop]-valued order, and that is a discriminating measurement rather
    than a guess: a two-field record [{ s :> SetoidObject; le : carrier s
    -> carrier s -> Prop }] elaborates at [Type@{max(Set+1,u+1,u0+1)}]
    while the same record with [Type] in place of [Prop] elaborates at
    [Type@{max(u+1,u0+1,u1+1)}], with [Set] nowhere.  [Prop]-valuedness is
    Instance/Pos.v:81's choice, inherited here so that the two records
    differ in one field only.

    ** An engineering finding: [reverse_coercion] eats a negative

    A negative asserting that a thin category is not an object of [Ord]
    was drafted as a guarded [Example : obj[Ord] := OrdAsCategory P] and
    is a FALSE PASS: the guarded command SUCCEEDS.  [Set Printing All]
    shows why -- the elaborated term is
    [@reverse_coercion (obj[Ord]) Category P
    (OrdAsCategory P)], Coq's reverse-coercion mechanism silently
    accepting the ascription because [OrdObject] coerces to [Type].  The
    negative shipped in its place is a CONVERSION one on the two object
    TYPES, where no coercion can intervene.

    ** NOT delivered

    - No equivalence between [Posets] and [Pos] beyond the isomorphism
      measured above, and no claim that the two are equal as categories.
    - No passage from a thin category back to an [OrdObject], hence no
      comparison of [Ord] with any subcategory of [Cat], and nothing
      about thinness or skeletality as in-tree predicates.  Instance/
      Proset/Skeletal.v:53's [Proset_Skeletal_iff_Antisymmetric], :80's
      [skeleton_of_proset_antisymmetric] and :95's [Proset_Skeleton] are
      the thin-category shadow of the sibling file's reflection; they are
      CITED and no bridge to them is built.
    - No relation to Instance/Proset/Monotone.v:82's [MonotoneFun] (bare
      monotone functions between prosets, no setoid) or to
      Construction/Enriched/Two.v:60's [TwoPreorder] (a [Type]-valued
      relation carrying a decider).
    - No limits, colimits, monoidal structure, or completeness for [Ord];
      no [Ord]-analogue of Instance/Pos.v's [Pos_Forget] beyond
      [Ord_Forget] itself, and no adjoint to it.
    - Nothing about the specialization preorder of a topological space,
      which would be the natural bridge to half (b) and is built in
      neither file.

    ** Corrections to the brief that guided this file

    Each is a measurement.  (1) The brief asked for the predicate to be
    named [Antisymmetric]; it is named [OrdAntisymmetric], because
    [Antisymmetric] is a stdlib class ([Coq.Classes.RelationClasses]) used
    in tree at Instance/Proset/Skeletal.v:95, and [make print-assumptions]
    loads many modules into ONE scope where a shared name audits the wrong
    constant.  No in-tree file DECLARES [Antisymmetric], so this is a
    hazard avoided rather than a collision repaired.  (2) The brief left
    open whether the [Pos] comparison would reach [≅[StrictCat]] or only
    [≅[Cat]]; it reaches [StrictCat].  (3) The brief's suggested typing
    negative on [Proset P] versus an object of [Ord] does not exist as a
    well-typed mis-statement -- see the [reverse_coercion] finding -- and
    was replaced rather than dropped.  Every donor line number the brief
    gave was re-grepped at d658518e and is correct. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** ** Objects *)

Record OrdObject := {
  ord_setoid :> SetoidObject;

  ord_le : carrier ord_setoid → carrier ord_setoid → Prop;

  ord_le_respects : Proper (equiv ==> equiv ==> iff) ord_le;

  ord_refl  : ∀ x, ord_le x x;
  ord_trans : ∀ x y z, ord_le x y → ord_le y z → ord_le x z
}.

#[export] Existing Instance ord_le_respects.

(** The order is implied by the carrier's own equivalence: this is the one
    consequence of [ord_le_respects] that the development below consumes. *)
Lemma ord_le_of_equiv (P : OrdObject) (x y : carrier (ord_setoid P)) :
  x ≈ y → ord_le P x y.
Proof.
  intro Hxy.
  assert (Hxx : x ≈ x) by reflexivity.
  exact (proj1 (ord_le_respects P x x Hxx x y Hxy) (ord_refl P x)).
Qed.


(** ** Morphisms *)

Record OrdHom (P Q : OrdObject) := {
  ord_fn :> SetoidMorphism (ord_setoid P) (ord_setoid Q);
  ord_mono : ∀ x y, ord_le P x y → ord_le Q (ord_fn x) (ord_fn y)
}.

Arguments ord_fn {P Q} _.
Arguments ord_mono {P Q} _ _ _ _.

#[local] Obligation Tactic := idtac.

#[export]
Program Instance OrdHom_Setoid {P Q : OrdObject} : Setoid (OrdHom P Q) := {|
  equiv := fun f g => ∀ a, ord_fn f a ≈ ord_fn g a
|}.
Next Obligation.
  intros P Q. constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a;
    transitivity (ord_fn g a); [apply Hfg|apply Hgh].
Qed.

Program Definition ord_hom_id {P : OrdObject} : OrdHom P P := {|
  ord_fn := setoid_morphism_id
|}.
Next Obligation. intros P x y H; exact H. Qed.

Program Definition ord_hom_compose {P Q R : OrdObject}
        (g : OrdHom Q R) (f : OrdHom P Q) : OrdHom P R := {|
  ord_fn := setoid_morphism_compose (ord_fn g) (ord_fn f)
|}.
Next Obligation.
  intros P Q R g f x y H; simpl.
  apply (ord_mono g), (ord_mono f); exact H.
Qed.

Program Instance ord_hom_compose_respects {P Q R : OrdObject} :
  Proper (equiv ==> equiv ==> equiv) (@ord_hom_compose P Q R).
Next Obligation.
  intros P Q R g g' Hg f f' Hf a; simpl.
  transitivity (ord_fn g (ord_fn f' a)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(** ** The category *)

Program Definition Ord : Category := {|
  obj     := OrdObject;
  hom     := OrdHom;
  homset  := @OrdHom_Setoid;
  id      := @ord_hom_id;
  compose := @ord_hom_compose;
  compose_respects := @ord_hom_compose_respects
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

Program Definition Ord_Forget : Ord ⟶ Sets := {|
  fobj := fun P => ord_setoid P;
  fmap := fun _ _ f => ord_fn f
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

(** ** Partial orders as a full subcategory *)

Definition OrdAntisymmetric (P : OrdObject) : Type :=
  ∀ x y : carrier (ord_setoid P),
    ord_le P x y → ord_le P y x → x ≈ y.

Definition Pos_Sub : Subcategory Ord :=
  @Build_Subcategory Ord
    OrdAntisymmetric
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Posets : Category := Sub Ord Pos_Sub.

Lemma Pos_Sub_Full :
  Category.Construction.Subcategory.Full Ord Pos_Sub.
Proof. intros x y ox oy g; exact I. Defined.

Lemma Posets_Incl_Full : Functor.Full (Incl Ord Pos_Sub).
Proof. exact (Full_Implies_Full_Functor Ord Pos_Sub Pos_Sub_Full). Defined.

Lemma Posets_Incl_Faithful : Functor.Faithful (Incl Ord Pos_Sub).
Proof. exact (Incl_Faithful Ord Pos_Sub). Defined.

(** ** Comparison with the pre-existing [Pos] *)

Definition OrdObject_of_Poset (P : PosetObject) : OrdObject := {|
  ord_setoid      := pos_setoid P;
  ord_le          := pos_le P;
  ord_le_respects := pos_le_respects P;
  ord_refl        := pos_refl P;
  ord_trans       := pos_trans P
|}.

Definition Poset_of_antisym (P : OrdObject) (H : OrdAntisymmetric P)
  : PosetObject := {|
  pos_setoid      := ord_setoid P;
  pos_le          := ord_le P;
  pos_le_respects := ord_le_respects P;
  pos_refl        := ord_refl P;
  pos_trans       := ord_trans P;
  pos_antisym     := H
|}.

Example poset_ord_poset_round (P : PosetObject) :
  Poset_of_antisym (OrdObject_of_Poset P) (pos_antisym P) = P := eq_refl.

Example ord_poset_ord_round (P : OrdObject) (H : OrdAntisymmetric P) :
  OrdObject_of_Poset (Poset_of_antisym P H) = P := eq_refl.

Definition OrdHom_of_MonoHom {P Q : PosetObject} (f : MonoHom P Q)
  : OrdHom (OrdObject_of_Poset P) (OrdObject_of_Poset Q) :=
  @Build_OrdHom (OrdObject_of_Poset P) (OrdObject_of_Poset Q)
    (mono_fn f) (mono_le f).

Definition MonoHom_of_OrdHom {P Q : OrdObject}
    (HP : OrdAntisymmetric P) (HQ : OrdAntisymmetric Q) (f : OrdHom P Q)
  : MonoHom (Poset_of_antisym P HP) (Poset_of_antisym Q HQ) :=
  @Build_MonoHom (Poset_of_antisym P HP) (Poset_of_antisym Q HQ)
    (ord_fn f) (ord_mono f).

Program Definition Pos_to_Posets : Pos ⟶ Posets := {|
  fobj := fun P => (OrdObject_of_Poset P; pos_antisym P);
  fmap := fun _ _ f => (OrdHom_of_MonoHom f; I)
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

Program Definition Posets_to_Pos : Posets ⟶ Pos := {|
  fobj := fun x => Poset_of_antisym `1 x `2 x;
  fmap := fun x y f => MonoHom_of_OrdHom `2 x `2 y `1 f
|}.
Next Obligation. intros x y f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros x a; simpl; reflexivity. Qed.
Next Obligation. intros x y z f g a; simpl; reflexivity. Qed.

Example pos_to_posets_obj (P : PosetObject) :
  `1 (fobj[Pos_to_Posets] P) = OrdObject_of_Poset P := eq_refl.

Example posets_to_pos_obj (x : Posets) :
  fobj[Posets_to_Pos] x = Poset_of_antisym `1 x `2 x := eq_refl.

Example pos_roundtrip_obj (P : PosetObject) :
  fobj[Posets_to_Pos] (fobj[Pos_to_Posets] P) = P := eq_refl.

Example pos_roundtrip_map (P Q : PosetObject) (f : MonoHom P Q)
    (a : carrier (pos_setoid P)) :
  mono_fn (fmap[Posets_to_Pos] (fmap[Pos_to_Posets] f)) a = mono_fn f a
  := eq_refl.

Lemma posets_pos_posets_obj (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x.
Proof. destruct x as [P HP]; exact eq_refl. Defined.

Program Definition Pos_Posets_strict_iso :
  @Isomorphism StrictCat Pos Posets := {|
  to   := Pos_to_Posets;
  from := Posets_to_Pos
|}.
Next Obligation.
  exists posets_pos_posets_obj.
  intros x y f; destruct x as [P HP], y as [Q HQ]; simpl.
  intro a; simpl; reflexivity.
Qed.
Next Obligation.
  exists (fun P : PosetObject => eq_refl).
  intros P Q f a; simpl; reflexivity.
Qed.

(** ** A preorder as a thin category, and the reviewer's distinction *)

Definition ord_preorder (P : OrdObject)
  : RelationClasses.PreOrder (ord_le P).
Proof.
  constructor.
  - exact (ord_refl P).
  - intros x y z f g; exact (ord_trans P x y z f g).
Defined.

Definition OrdAsCategory (P : OrdObject) : Category :=
  Proset (ord_preorder P).

Program Definition OrdHomAsFunctor {P Q : OrdObject} (f : OrdHom P Q)
  : OrdAsCategory P ⟶ OrdAsCategory Q := {|
  fobj := fun x => ord_fn f x;
  fmap := fun x y h => ord_mono f x y h
|}.
Next Obligation. intros P Q f x y g h Hgh; exact I. Qed.
Next Obligation. intros P Q f x; exact I. Qed.
Next Obligation. intros P Q f x y z g h; exact I. Qed.

Example ord_functor_fobj {P Q : OrdObject} (f : OrdHom P Q)
    (x : carrier (ord_setoid P)) :
  fobj[OrdHomAsFunctor f] x = ord_fn f x := eq_refl.

Example Ord_obj_are_preorders : obj[Ord] = OrdObject := eq_refl.

Example OrdAsCategory_obj_are_points (P : OrdObject) :
  obj[OrdAsCategory P] = carrier (ord_setoid P) := eq_refl.
