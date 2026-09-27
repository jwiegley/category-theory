(** * Coreflective subcategories, read covariantly

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    Springer GTM 5, §IV.3, printed p. 91 (PDF p. 100), read from the
    page image: "Dually, A ⊂ B is coreflective in B when the inclusion
    functor A → B has a right adjoint.  (Warning: Mitchell [1965] has
    interchanged the meanings of "reflection" and "coreflection".)"
    The example printed on p. 92 (PDF p. 101) is the torsion subgroup:
    "A coreflective subcategory of Ab is the full subcategory of all
    torsion abelian groups (a group is torsion if all elements have
    finite order); the coreflector sends each abelian group A to the
    subgroup TA of all elements of finite order in A."  That example is
    Instance/Ab/Torsion.v, the first consumer of this file.
    Riehl, "Category Theory in Context", §4.6, printed p. 169 (PDF
    p. 189), read from the page image: Lemma 4.6.11 lists, for an
    adjunction F ⊣ G, "(iii) G is full and faithful if and only if ε is
    an isomorphism" and dually "(iii) F is full and faithful if and only
    if η is an isomorphism"; "The third conditions in each list
    characterize adjunctions defined by reflective subcategories or
    coreflective subcategories."
    nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

    BACKGROUND.  nLab defines a coreflective subcategory as "a full
    subcategory whose inclusion functor has a right adjoint R (a cofree
    functor)", calls the reflective subcategory its dual concept, and
    refers there "for more details".  Mac Lane's warning records that the
    two words were once used the other way round, so the side on which
    the adjoint sits is the whole content of the definition: a reflector
    is LEFT adjoint to the inclusion, a coreflector RIGHT adjoint.  The
    first of nLab's equivalent characterizations is that a left adjoint
    is fully faithful exactly when its unit is a natural isomorphism,
    which is Riehl's second (iii); an inclusion is fully faithful, so at
    an object of a coreflective subcategory the unit is invertible.
    That is [coreflective_unit_iso] below.

    WHY THIS FILE EXISTS.  Construction/Reflective.v defines
    [Coreflective S] as [Reflective (C^op) (op_subcategory S)]: a record
    whose reflector is typed [C^op ⟶ Sub (C^op) (op_subcategory S)] and
    whose adjunction relates opposite categories.  Nothing in the tree
    read such a record back covariantly, so a coreflection could not be
    stated as Mac Lane states it -- the inclusion has a right adjoint --
    and be an inhabitant of the record at once.  The two halves of the
    bridge:

      - [Coreflective_of_adjunction full G A : Coreflective S], built
        from covariant data: fullness of S, a functor [G : C ⟶ Sub C S]
        and an adjunction [A : Incl C S ⊣ G];
      - [coreflective_full], [coreflector] and [coreflective_adj], which
        read any record back as covariant data, the adjunction at the
        type [Incl C S ⊣ coreflector R].

    Each is built field by field.  The functor laws and the four
    naturality fields of [Adjunction] are the donor's own with their
    arguments permuted ([coreflector_op], [coreflector_op_adj]), and the
    hom-set isomorphism exchanges [to] and [from]; nothing is proved
    afresh.

    WHY FIELD BY FIELD, MEASURED.  The objects and the hom types of
    [Opposite (Sub C S)] and [Sub (Opposite C) (op_subcategory S)]
    convert, and so do the two [equiv] relations on a hom-set, but the
    two categories do not: stating their equality at [eq_refl] is
    refused with "cannot unify", and so is the equality of the two
    hom-SETOIDS, whose equivalence proofs are the different instances
    [Sub_obligation_1 C S x y] and [Sub_obligation_1 (C^op)
    (op_subcategory S) y x] of Construction/Subcategory.v's [Sub]
    ([Print Sub]).  Test/ProbeReflective370.v pins the two refusals
    beside the conversions of the objects, the hom types and the two
    [equiv] relations.  So no functor can be retyped from one side to
    the other, and handing the donor's [from] and [to] straight to
    [Build_Isomorphism Sets] is refused with a mismatch between the two
    [≊] statements; the two setoid morphisms are rebuilt around the
    donor's functions and respectfulness proofs instead.

    STRENGTHS, measured strict first.  All eight [Example]s hold at
    [eq_refl]:
      - the two halves are mutually inverse on the nose, on whole
        records and in both orders: [coreflector_roundtrip] (the
        functor), [coreflective_adj_roundtrip] (the adjunction),
        [coreflective_full_roundtrip] (the fullness witness) and
        [Coreflective_roundtrip] (the record), with the object and arrow
        parts [coreflector_obj_roundtrip] and
        [coreflector_fmap_roundtrip].  Under the project-wide primitive
        projections every record here has definitional eta, and that is
        what lets a rebuilt record convert with the one it was read
        from;
      - [coreflective_counit_is_op_unit]: the covariant counit IS the
        record's unit, and [coreflective_unit_is_op_counit]: the
        covariant unit IS the record's counit.
    [coreflective_unit_iso] is [reflective_counit_iso]'s isomorphism
    with its two inverse laws exchanged.  No constant is closed with
    [Qed].

    UNIVERSES, read by [About] under [Set Printing Universes] on all
    fifteen constants.  Each carries the binder [@{o h +}] with
    [C : Category@{o h h}], hom and proof identified; that
    identification is [Subcategory]'s own ([About Subcategory] reads
    [Category@{u u0 u0} → ...]).  The constants that mention
    [Coreflective] bind S at [Subcategory@{o h u4 h}], its fourth level
    identified with h; that is [Coreflective]'s own binder
    ([Subcategory@{u5 u6 u4 u6}]), while [coreflector_op] and
    [coreflector_op_adj] leave both of S's own levels free.  No
    constraint block carries an equation or mentions [Set].  Every
    global universe in the blocks is an upper bound and never a lower
    one: [Basics.compose.u0]-[u2], [ID.u0] and the standard library's
    [Projections.u0]/[u1] ([Sub] carries the last two in its own
    block).  The binders were measured not to narrow anything: against
    a copy of this file with every binder and annotation removed,
    compared under [Set Printing All], no constant has fewer distinct
    universes in its type (a block equation counting its two sides as
    one) or an identification the copy lacks, and one,
    [coreflector_op_adj], has one free level more.

    NOT DELIVERED.
      - Construction/Reflective.v is unchanged: [Coreflective] stays
        op-typed, and this file only reads and builds it.
      - No couniversal-arrow constructor for the record in THIS file,
        which builds a coreflection from an adjunction and does not
        require Theory/Universal/Arrow.v.  The constructor is
        Construction/Reflective/Universal.v's
        [Coreflective_of_CouniversalArrows]: Theory/Universal/Arrow/
        Dual.v's [AdjunctionFromCouniversalArrows] fed to
        [Coreflective_of_adjunction].
      - Nothing on the idempotent comonad of a coreflection beyond
        Construction/Reflective/FixedPoints.v's op-form
        [Coreflective_IdempotentMonad_op], and no co-Eilenberg–Moore
        reading.
      - No uniqueness of the coreflector up to isomorphism. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

Generalizable All Variables.

(** ** From covariant data to the record *)

(* A covariant functor into the subcategory, read as a functor between
   the opposites.  Every field is the donor's own, with the two object
   arguments exchanged. *)
Definition coreflector_op@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (G : C ⟶ Sub C S) :
  C^op ⟶ Sub (C^op) (op_subcategory S).
Proof.
  refine (@Build_Functor (C^op) (Sub (C^op) (op_subcategory S))
            (fun x => fobj[G] x)
            (fun x y f => @fmap _ _ G y x f) _ _ _).
  - intros x y f g E. exact (@fmap_respects _ _ G y x f g E).
  - intros x. exact (@fmap_id _ _ G x).
  - intros x y z f g. exact (@fmap_comp _ _ G z y x g f).
Defined.

(* The covariant adjunction [Incl ⊣ G] read as [G^op ⊣ Incl^op].  The
   hom-set isomorphism is the donor's with [to] and [from] exchanged, and
   each of the four naturality fields is one of the donor's four with its
   arguments permuted: nothing is re-proved. *)
Definition coreflector_op_adj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflector_op G ⊣ Incl (C^op) (op_subcategory S).
Proof.
  unshelve refine
    (@Build_Adjunction (Sub (C^op) (op_subcategory S)) (C^op)
       (coreflector_op G) (Incl (C^op) (op_subcategory S))
       (fun x y => _) _ _ _ _).
  - unshelve refine (@Build_Isomorphism Sets _ _ _ _ _ _).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => from (@adj _ _ _ _ A y x) f) _).
      intros f g E. exact (proper_morphism (from (@adj _ _ _ _ A y x)) f g E).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => to (@adj _ _ _ _ A y x) f) _).
      intros f g E. exact (proper_morphism (to (@adj _ _ _ _ A y x)) f g E).
    + intros f. exact (iso_from_to (@adj _ _ _ _ A y x) f).
    + intros f. exact (iso_to_from (@adj _ _ _ _ A y x) f).
  - intros x y z f g. exact (@from_adj_nat_r _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@from_adj_nat_l _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@to_adj_nat_r _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@to_adj_nat_l _ _ _ _ A z y x g f).
Defined.

(* Mac Lane's dual definition, built from covariant data: a full
   subcategory together with a right adjoint of its inclusion. *)
Definition Coreflective_of_adjunction@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) : Coreflective S :=
  @Build_Reflective (C^op) (op_subcategory S)
    (fun x y ox oy f => full y x oy ox f)
    (coreflector_op G) (coreflector_op_adj G A).

(** ** From the record back to covariant data *)

Definition coreflective_full@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Construction.Subcategory.Full C S :=
  fun x y ox oy f => reflective_full R y x oy ox f.

Definition coreflector@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) : C ⟶ Sub C S.
Proof.
  refine (@Build_Functor C (Sub C S)
            (fun x => fobj[reflector R] x)
            (fun x y f => @fmap _ _ (reflector R) y x f) _ _ _).
  - intros x y f g E. exact (@fmap_respects _ _ (reflector R) y x f g E).
  - intros x. exact (@fmap_id _ _ (reflector R) x).
  - intros x y z f g. exact (@fmap_comp _ _ (reflector R) z y x g f).
Defined.

Definition coreflective_adj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Incl C S ⊣ coreflector R.
Proof.
  unshelve refine
    (@Build_Adjunction C (Sub C S) (Incl C S) (coreflector R)
       (fun x y => _) _ _ _ _).
  - unshelve refine (@Build_Isomorphism Sets _ _ _ _ _ _).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => from (@adj _ _ _ _ (reflective_adj R) y x) f) _).
      intros f g E.
      exact (proper_morphism (from (@adj _ _ _ _ (reflective_adj R) y x))
               f g E).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => to (@adj _ _ _ _ (reflective_adj R) y x) f) _).
      intros f g E.
      exact (proper_morphism (to (@adj _ _ _ _ (reflective_adj R) y x))
               f g E).
    + intros f. exact (iso_from_to (@adj _ _ _ _ (reflective_adj R) y x) f).
    + intros f. exact (iso_to_from (@adj _ _ _ _ (reflective_adj R) y x) f).
  - intros x y z f g.
    exact (@from_adj_nat_r _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@from_adj_nat_l _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@to_adj_nat_r _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@to_adj_nat_l _ _ _ _ (reflective_adj R) z y x g f).
Defined.

(** ** Round trips *)

Example coreflector_obj_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) (x : C) :
  fobj[coreflector (Coreflective_of_adjunction full G A)] x = fobj[G] x
  := eq_refl.

Example coreflector_fmap_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) (x y : C) (f : x ~> y) :
  fmap[coreflector (Coreflective_of_adjunction full G A)] f = fmap[G] f
  := eq_refl.

(* The whole functor, the whole adjunction, the fullness witness and the
   whole record all return on the nose. *)
Example coreflector_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflector (Coreflective_of_adjunction full G A) = G := eq_refl.

Example coreflective_adj_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflective_adj (Coreflective_of_adjunction full G A) = A := eq_refl.

Example coreflective_full_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflective_full (Coreflective_of_adjunction full G A) = full
  := eq_refl.

Example Coreflective_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Coreflective_of_adjunction (coreflective_full R) (coreflector R)
    (coreflective_adj R) = R := eq_refl.

(** ** Unit and counit, read across the bridge *)

(* The covariant counit at [x : C] IS the record's unit at [x], and the
   covariant unit at [s : Sub C S] IS the record's counit at [s]. *)
Example coreflective_counit_is_op_unit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (x : C) :
  @counit _ _ _ _ (coreflective_adj R) x
    = @Category.Theory.Adjunction.unit _ _ _ _ (reflective_adj R) x
  := eq_refl.

Example coreflective_unit_is_op_counit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (s : Sub C S) :
  @Category.Theory.Adjunction.unit _ _ _ _ (coreflective_adj R) s
    = @counit _ _ _ _ (reflective_adj R) s
  := eq_refl.

(* The dual of [reflective_counit_iso]: at an object of a coreflective
   subcategory the unit is invertible, [x ≅ coreflector (Incl x)].  The
   two morphisms are [reflective_counit_iso]'s, and its two inverse laws
   are exchanged. *)
Definition coreflective_unit_iso@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (x : Sub C S) :
  x ≅[Sub C S] fobj[coreflector R] (fobj[Incl C S] x).
Proof.
  pose (i := reflective_counit_iso R x).
  unshelve refine (@Build_Isomorphism (Sub C S) _ _ (to i) (from i) _ _).
  - exact (iso_from_to i).
  - exact (iso_to_from i).
Defined.
