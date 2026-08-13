(** * Pos, the category of posets and monotone maps

    Awodey §1.4 (Categories of structured sets): posets with monotone maps
    form a category, the identity being monotone and monotone maps being
    closed under composition.  The book is cited BY LOCATION only; its printed
    text was not consulted while writing this file, and the locations follow
    issue jwiegley/category-theory#641.

    TWO DIFFERENT THINGS CALLED "POSET AS A CATEGORY", and this file is the
    second.  Instance/Poset.v turns ONE poset into a thin category, whose
    objects are the elements and whose homs are the order relation.  This file
    builds the category whose OBJECTS ARE POSETS and whose morphisms are the
    monotone maps between them -- the structured-sets reading, in the same
    spirit as Instance/CMon.v's [CMon].  Neither subsumes the other, and #641
    is explicit that it wants this one.

    WHY Instance/Poset.v CANNOT BE REUSED.  Its [Poset] (:118-119, shifted by
    this commit's own two-line edit to that file's header) reads
    [Definition Poset ... := Proset P], DISCARDING the antisymmetry argument,
    which never appears in the body.  So a [Poset] VALUE is literally a
    [Proset] value: antisymmetry is not recoverable from it, and a category of
    posets cannot be carved out of [Cat] by selecting such values.  The
    structure has to be bundled, which is what [PosetObject] does.

    A FIELD Instance/Poset.v DOES NOT HAVE: [pos_le_respects], requiring the
    order to be compatible with the carrier's own [≈].  State its status
    accurately: it is an OBJECT WELL-FORMEDNESS condition, not a lemma anything
    below consumes.  Composition of monotone maps is proved from
    [SetoidMorphism]'s [proper_morphism] alone, and the file still compiles
    with [pos_le_respects] deleted.  It is kept because an order that
    distinguished [≈]-equal elements would not deserve the name, and because
    Instance/CMon.v carries [cmon_plus_respects] in exactly this slot -- not
    because any proof here needs it.

    Antisymmetry is likewise stated at the SETOID level
    ([pos_antisym : le x y -> le y x -> x ≈ y]) rather than with Leibniz [eq];
    that is the honest reading of "partial order" over setoid carriers.  It is
    what makes this the category of POSETS -- [Pos] compiles as a category
    without it -- and it is a disclosed deviation from Awodey's set-level
    statement.

    SCOPE.  #641's work item 2 offers an "alternative": realize [Pos] as a full
    subcategory of [Cat] on "the skeletal thin categories [Poset P]".  That is
    NOT taken, and the honest reason is the one the issue itself gives -- it
    calls the direct construction "likely simpler and the recommended
    principal artifact".

    Be precise about what is and is not an obstacle here, because it is easy to
    overstate.  The subcategory ITSELF is constructible in a few lines:
    Construction/Subcategory.v:32's [sobj : C -> Type] takes an arbitrary
    [Type]-valued predicate, so "thin and skeletal" can be selected directly
    with no equality on [Category] values anywhere.  Nor does "skeletal thin"
    misdescribe its family: skeletality is exactly what antisymmetry buys (as
    Instance/Poset.v:19-20 says), and it strictly excludes preorders -- the
    two-element indiscrete preorder is thin and NOT skeletal.

    What is genuinely deferred is the AGREEMENT: showing the subcategory
    presentation matches [Pos] means recovering the carrier setoid and the
    order from a skeletal thin category, which is real work and is not
    attempted here.  ([thin] and [skeletal] also have no in-tree predicate
    today, but that is a "nobody wrote it yet" fact, not a viability
    argument.)

    A comparison in the other direction is cheap and IS provided:
    [PosetAsCategory] sends a poset to its thin category and
    [MonotoneAsFunctor] sends a monotone map to the induced functor, which is
    the honest formal link between the two readings. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.

Generalizable All Variables.

(** ** Objects *)

(** A poset over a setoid carrier: a relation that respects [≈], is reflexive
    and transitive, and is antisymmetric UP TO [≈]. *)
Record PosetObject := {
  pos_setoid :> SetoidObject;

  pos_le : carrier pos_setoid → carrier pos_setoid → Prop;

  pos_le_respects : Proper (equiv ==> equiv ==> iff) pos_le;

  pos_refl    : ∀ x, pos_le x x;
  pos_trans   : ∀ x y z, pos_le x y → pos_le y z → pos_le x z;
  pos_antisym : ∀ x y, pos_le x y → pos_le y x → x ≈ y
}.

#[export] Existing Instance pos_le_respects.

(** ** Morphisms *)

(** A monotone map: a setoid morphism preserving the order.  Respect for [≈]
    comes from [SetoidMorphism]; monotonicity is the added field. *)
Record MonoHom (P Q : PosetObject) := {
  mono_fn :> SetoidMorphism (pos_setoid P) (pos_setoid Q);
  mono_le : ∀ x y, pos_le P x y → pos_le Q (mono_fn x) (mono_fn y)
}.

Arguments mono_fn {P Q} _.
Arguments mono_le {P Q} _ _ _ _.

#[local] Obligation Tactic := idtac.

(** Monotone maps are compared pointwise up to the codomain's [≈], as in
    Instance/CMon.v:74 and Instance/Sets.v -- never by Leibniz equality. *)
#[export]
Program Instance MonoHom_Setoid {P Q : PosetObject} : Setoid (MonoHom P Q) := {|
  equiv := fun f g => ∀ a, mono_fn f a ≈ mono_fn g a
|}.
Next Obligation.
  intros P Q. constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (mono_fn g a); [apply Hfg|apply Hgh].
Qed.

(** Awodey's two closure facts: the identity is monotone, and composites of
    monotone maps are monotone.  Both are the [Next Obligation]s below, so they
    are proved rather than assumed. *)
Program Definition mono_hom_id {P : PosetObject} : MonoHom P P := {|
  mono_fn := setoid_morphism_id
|}.
Next Obligation. intros P x y H; exact H. Qed.

Program Definition mono_hom_compose {P Q R : PosetObject}
        (g : MonoHom Q R) (f : MonoHom P Q) : MonoHom P R := {|
  mono_fn := setoid_morphism_compose (mono_fn g) (mono_fn f)
|}.
Next Obligation.
  intros P Q R g f x y H; simpl.
  apply (mono_le g), (mono_le f); exact H.
Qed.

Program Instance mono_hom_compose_respects {P Q R : PosetObject} :
  Proper (equiv ==> equiv ==> equiv) (@mono_hom_compose P Q R).
Next Obligation.
  intros P Q R g g' Hg f f' Hf a; simpl.
  transitivity (mono_fn g (mono_fn f' a)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(** ** The category *)

Program Definition Pos : Category := {|
  obj     := PosetObject;
  hom     := MonoHom;
  homset  := @MonoHom_Setoid;
  id      := @mono_hom_id;
  compose := @mono_hom_compose;
  compose_respects := @mono_hom_compose_respects
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** The underlying-set functor, forgetting the order. *)
Program Definition Pos_Forget : Pos ⟶ Sets := {|
  fobj := fun P => pos_setoid P;
  fmap := fun _ _ f => mono_fn f
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

(** ** The link between the two readings *)

(** Every poset yields a thin category -- Instance/Proset.v's construction
    applied to its order.  This is the formal bridge between "a poset viewed as
    a category" and "the category of posets", and it is what #641's work item 2
    was reaching for; taken in this direction it needs no equality on
    [Category] values and no [thin]/[skeletal] vocabulary. *)
(* [RelationClasses.PreOrder] qualified explicitly: unqualified [PreOrder]
   resolves to the [crelation] version from Category.Lib, while [Proset] wants
   the stdlib [Prop]-valued one.  Importing Coq.Classes.Equivalence to
   disambiguate is NOT an option -- it shadows the library's own [equiv]. *)
Definition pos_preorder (P : PosetObject)
  : RelationClasses.PreOrder (pos_le P).
Proof.
  constructor.
  - exact (pos_refl P).
  - intros x y z f g; exact (pos_trans P x y z f g).
Defined.

Definition PosetAsCategory (P : PosetObject) : Category :=
  Proset (pos_preorder P).

(** A monotone map induces a functor between the thin categories: on objects it
    is the map, on morphisms it is monotonicity, and every law is an equation
    between parallel morphisms in a thin target, hence free. *)
Program Definition MonotoneAsFunctor {P Q : PosetObject} (f : MonoHom P Q)
  : PosetAsCategory P ⟶ PosetAsCategory Q := {|
  fobj := fun x => mono_fn f x;
  fmap := fun x y h => mono_le f x y h
|}.
(* The file sets [Obligation Tactic := idtac] above, so these are discharged
   explicitly rather than silently.  All three are equations between parallel
   morphisms in a thin target, hence [I]. *)
Next Obligation. intros P Q f x y g h Hgh; exact I. Qed.
Next Obligation. intros P Q f x; exact I. Qed.
Next Obligation. intros P Q f x y z g h; exact I. Qed.

(** Sanity: the induced functor's object action IS the underlying map. *)
Example monotone_functor_fobj {P Q : PosetObject} (f : MonoHom P Q)
  (x : carrier (pos_setoid P)) :
  fobj[MonotoneAsFunctor f] x = mono_fn f x := eq_refl.
