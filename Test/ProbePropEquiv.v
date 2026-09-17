Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Cat.

(** * Probe for [PropEquiv]: setoids whose equality is propositional

    The import list above is the union of the two target files' own lists --
    Lib/Setoid/Propositional.v and Instance/Sets/Propositional.v -- plus those
    two files themselves and Instance/Cat.v, whose own list is a subset of what
    is already here.  A shorter prefix is what makes a probe pass for no
    reason.

    WHAT THIS FILE PINS.  Four things, each a measurement rather than an
    assertion.

    (1) The library's `≈` cannot be truncated.  Cat's hom-setoid is
        [Functor_Setoid] (Theory/Functor.v:149, installed as Cat's [homset] at
        Instance/Cat.v:145) and an [F ≈ G] there IS a family of isomorphisms.
        Replacing it by [inhabited (F ≈ G)] and asking for the isomorphism at
        an object is refused -- NEGATIVE 1.  The same refusal, in the shape a
        would-be blanket instance takes, is NEGATIVE 3.  This is why
        [PropEquiv] is a PROPERTY of a setoid and not a change to
        [Class Setoid].

    (2) The property has to name its relation.  The sort ascription
        [(x ≈ y : Prop)] is refused even for [eq_Setoid], whose relation is
        Coq's [eq] -- NEGATIVE 2.  [PropEquiv_of_relation] is the constructor
        that takes the named relation instead.

    (3) The size fact the whole exercise rests on: a [Prop]-valued relation on
        a carrier in [Type@{u}] lands in [Type@{u}] itself, a [Type]-valued one
        lands in [Type@{u+1}].  Both halves are measured below, the second as
        NEGATIVE 4, and the contrast is repeated for [PropEquiv] against
        [Setoid] itself as NEGATIVE 5.

    (4) [PropEquiv] lands AT the carrier universe.  [PropEquiv_at_carrier]
        below is accepted with the measured signature quoted beside it.

    DISCIPLINE.  The messages quoted below are as this file produces them,
    with [Set Printing Universes] OFF -- which is why four of the five show a
    bare [Type] where a universe name would otherwise stand.  Exactly two
    edits are applied to the quotations and to nothing else: NEGATIVE 2's
    generated universe name, which is file-name dependent and would not
    survive a rename, is replaced by the readable [u_eq]; and Coq's line
    breaks are re-flowed to this comment's width, with trailing spaces
    trimmed.  Every other character is verbatim.  The SIGNATURES quoted beside
    the size measurements were taken separately, with [About] under
    [Set Printing Universes].  Every negative is paired with a positive control
    naming the same library constants; the instrument was checked (a refusal
    expected around a command that succeeds stops the file); and each negative
    was re-run with its guard stripped IN A COPY OF THE WHOLE FILE, so that the
    refusal kind is read off the message rather than guessed.  The refusal
    kinds recorded are ELIMINATION (two), SORT (one) and UNIVERSE (two),
    beside the instrument check, whose refusal is a missing NAME. *)

(** ** Instrument check *)

(* A refusal expected around a name that is not there.  If the instrument were
   inert this line would pass silently and so would everything below it. *)
Fail Check zzz_no_such_constant_propequiv.

(** ** Positive controls: every constant the negatives sit beside *)

Check @PropEquiv.
Check @pequiv.
Check @pequiv_to.
Check @pequiv_from.
Check @PropEquiv_of_relation.
Check @pequiv_Equivalence.
Check @pequiv_Equivalence_Prop.
Check @pequiv_Proper.
Check @pequiv_elim_inhabited.

Check @eq_PropEquiv.
Check @unit_PropEquiv.
Check @Fin_PropEquiv.
Check @funext_PropEquiv.
Check @fun_PropEquiv.
Check @prod_PropEquiv.
Check @sum_PropEquiv.
Check @option_PropEquiv.
Check @list_PropEquiv.
Check @nat_PropEquiv.

Check @PropEquivObj.
Check @hom_PropEquiv.
Check @product_PropEquiv.
Check @iprod_PropEquiv.
Check @limit_PropEquiv.
Check @LocallyPropositional.
Check @locally_prop.
Check @LocallyPropositional_of_relation.
Check @Morphism_equality_PropEquiv.
Check @LocallyPropositional_of_eq.

(* The two [Cat] constants NEGATIVE 1 is about.  [Functor_Setoid] is Cat's
   hom-setoid, and the projection out of an UNTRUNCATED [F ≈ G] is accepted:
   the negative below is about the truncation, not about the projection. *)
Check @Functor_Setoid.

Definition cat_equiv_is_data {C D : Category} (F G : C ⟶ D)
  (H : F ≈ G) (x : C) : F x ≅ G x := `1 H x.

(* [eq_PropEquiv] is registered, so instance resolution closes a [pequiv] goal
   at a discrete setoid with no explicit instance argument. *)
Example c_resolution (A : Type) (x y : A) : Prop := @pequiv A (eq_Setoid A) _ x y.

(* ... and the relation it resolves to is Coq's [eq], on the nose. *)
Example c_resolution_is_eq (A : Type) (x y : A) :
  @pequiv A (eq_Setoid A) (eq_PropEquiv A) x y = (x = y) := eq_refl.

(* [pequiv_elim_inhabited] takes its [PropEquiv] implicitly, so the one
   elimination the class buys elaborates with instance resolution alone. *)
Example c_elim (A : Type) (x y : A)
  (h : inhabited (@equiv A (eq_Setoid A) x y)) : @equiv A (eq_Setoid A) x y :=
  pequiv_elim_inhabited x y h.

(** ** Control: [PropEquiv_of_relation] on a relation that is not [eq]

    A setoid on [nat] whose `≈` identifies numbers of the same parity.  Its
    relation is already [Prop]-valued, so [PropEquiv_of_relation] applies with
    both implications the identity -- which is the whole point of that
    constructor: the relation is handed over by NAME, since the ascription of
    NEGATIVE 2 is refused. *)

Definition parity_rel (x y : nat) : Prop := Nat.even x = Nat.even y.

Definition parity_Equivalence : Equivalence parity_rel.
Proof.
  unfold parity_rel.
  constructor.
  - intro x; reflexivity.
  - intros x y H; symmetry; exact H.
  - intros x y z H1 H2; transitivity (Nat.even y); assumption.
Defined.

Definition parity_Setoid : Setoid nat :=
  {| equiv := parity_rel ; setoid_equiv := parity_Equivalence |}.

Definition parity_PropEquiv : PropEquiv parity_Setoid.
Proof.
  unshelve refine (PropEquiv_of_relation parity_rel _ _).
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

Example c_parity_pequiv (x y : nat) :
  @pequiv nat parity_Setoid parity_PropEquiv x y = parity_rel x y := eq_refl.

(** ** Controls: the pointwise and componentwise transports read back *)

(* The hom-setoid of [Sets]: pointwise into the target. *)
Example c_hom_pointwise {x y : SetoidObject} (Py : PropEquiv (is_setoid y))
  (f g : x ~{Sets}~> y) :
  @pequiv _ _ (hom_PropEquiv Py) f g
    = (forall a : carrier x, @pequiv _ _ Py (f a) (g a)) := eq_refl.

(* Indexed products: pointwise in the index. *)
Example c_iprod_pointwise {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i)))
  (g h : carrier (Sets_iprod_obj F)) :
  @pequiv _ _ (iprod_PropEquiv F H) g h
    = (forall i : A, @pequiv _ _ (H i) (g i) (h i)) := eq_refl.

(* Limits: pointwise in the shape, the compatibility witness playing no part. *)
Example c_limit_pointwise {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d)))
  (p q : Sets_limit_carrier F) :
  @pequiv _ _ (limit_PropEquiv F H) p q
    = (forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d)) := eq_refl.

(* The dependent-function setoid of Lib/Setoid.v. *)
Example c_funext_pointwise {T : Type} (t : T -> Type) (a b : T)
  {Sb : Setoid (t b)} (Pb : PropEquiv Sb) (f g : t a -> t b) :
  @pequiv _ _ (funext_PropEquiv t a b Pb) f g
    = (forall x : t a, @pequiv _ _ Pb (f x) (g x)) := eq_refl.

(* A [SetoidObject] that DOES have the property, as the control for
   NEGATIVE 3: the blanket instance is refused, individual ones are not. *)
Definition eq_SetoidObject (A : Type) : SetoidObject :=
  {| carrier := A ; is_setoid := eq_Setoid A |}.

Definition eq_SetoidObject_PropEquiv (A : Type) :
  PropEquiv (is_setoid (eq_SetoidObject A)) := eq_PropEquiv A.

(** ** Size measurements, and their controls

    The three-line size fact of Lib/Setoid/Propositional.v's header, measured.
    [PropRelSpace] is ACCEPTED at the carrier universe, with the constraint
    [Set < u] that the sort of [Prop] imposes:

      PropRelSpace@{u} : Type@{u} → Type@{u}
      (* u |= Set < u *)

    [PropEquiv] itself lands there too:

      PropEquiv_at_carrier@{u} : ∀ A : Type@{u}, Setoid@{u u} A → Type@{u}
      (* u |= Set < u *)

    NEGATIVE 4 and NEGATIVE 5 are the other half of the contrast. *)

Definition PropRelSpace@{u} (A : Type@{u}) : Type@{u} := A -> A -> Prop.

Definition PropEquiv_at_carrier@{u} (A : Type@{u}) (S : Setoid@{u u} A) :
  Type@{u} := PropEquiv@{u u} S.

(* Control for NEGATIVE 4: one universe up, the [Type]-valued relation space
   is accepted. *)
Definition CRelSpace@{u v} (A : Type@{u}) : Type@{v} := A -> A -> Type@{u}.

(* Control for NEGATIVE 5: one universe up, [Setoid] is accepted. *)
Definition Setoid_above_carrier@{u v} (A : Type@{u}) : Type@{v} := Setoid@{u u} A.

(** ** NEGATIVE 1 (ELIMINATION): Cat's `≈` cannot be truncated

    Stripped and re-run in a copy of the whole file, the message is

      Incorrect elimination of "H" in the inductive type "inhabited":
      the return type has sort "Type" while it should be SProp or Prop.
      Elimination of an inductive object of sort Prop
      is not allowed on a predicate in sort "Type"
      because proofs can be eliminated only to build proofs.

    -- [inhabited] is [Prop]-valued and so eliminates only into [Prop], while
    the family of isomorphisms carried by an [F ≈ G] lands in [Type].  The
    control immediately above ([cat_equiv_is_data]) performs the same
    projection out of the UNTRUNCATED proof and is accepted, so the refusal is
    about the truncation alone. *)

Fail Definition cat_equiv_prop {C D : Category} (F G : C ⟶ D)
  (H : inhabited (F ≈ G)) (x : C) : F x ≅ G x :=
  match H with inhabits p => `1 p x end.

(** ** NEGATIVE 2 (SORT): [(x ≈ y : Prop)] is refused, even at [eq_Setoid]

    Stripped and re-run in a copy of the whole file, the message is

      In environment
      A : Type
      x : A
      y : A
      The term "x ≈ y" has type "Type" while it is expected to have type
      "Prop" (universe inconsistency: Cannot enforce u_eq <= Prop).

    -- [equiv x y] is typed at [Type] whatever relation sits underneath, and
    [eq_Setoid]'s relation IS Coq's [eq].  No ascription narrows the sort after
    the fact; the relation has to be named, which is what
    [PropEquiv_of_relation] takes.  The control is [c_resolution_is_eq] above:
    naming [eq] and going through [eq_PropEquiv] is accepted and computes to
    [x = y]. *)

Fail Definition eq_equiv_ascribed (A : Type) (x y : A) : Prop :=
  (@equiv A (eq_Setoid A) x y : Prop).

(** ** NEGATIVE 3 (ELIMINATION): no blanket [PropEquiv] for [Sets]

    Stripped and re-run in a copy of the whole file, the message is

      Incorrect elimination of "H" in the inductive type "inhabited":
      the return type has sort "Type" while it should be SProp or Prop.
      Elimination of an inductive object of sort Prop
      is not allowed on a predicate in sort "Type"
      because proofs can be eliminated only to build proofs.

    -- the same refusal as NEGATIVE 1, in the shape a blanket instance would
    take.  [pequiv_from] is fine ([inhabits]); [pequiv_to] is what is refused.
    This is why there is no [∀ X : SetoidObject, PropEquiv (is_setoid X)] in
    Instance/Sets/Propositional.v and no [LocallyPropositional Sets], and why
    the algebraic object records of the later phases CARRY the property as a
    field.  The control is [eq_SetoidObject_PropEquiv] above: a PARTICULAR
    [SetoidObject] can of course have it.

    Note what this does and does not measure.  It measures that THIS route --
    truncate `≈` and untruncate it again -- is refused.  For [Cat] the refusal
    is decisive, since the data projected out is a family of isomorphisms.  For
    an arbitrary [SetoidObject] it records the absence of a construction, not a
    proof that none exists. *)

Fail Definition sets_PropEquiv_generic (X : SetoidObject) :
  PropEquiv (is_setoid X) :=
  {| pequiv := fun x y => inhabited (@equiv _ (is_setoid X) x y)
   ; pequiv_to := fun x y H => match H with inhabits h => h end
   ; pequiv_from := fun x y h => inhabits h |}.

(** ** NEGATIVE 4 (UNIVERSE): a [Type]-valued relation space is one level up

    Stripped and re-run in a copy of the whole file, the message is

      In environment
      A : Type
      The term "A → A → Type" has type "Type@{u+1}"
      while it is expected to have type "Type@{u}"
      (universe inconsistency: Cannot enforce u < u because u = u).

    -- against [PropRelSpace] above, which is accepted at [Type@{u}].  This is
    the size fact the solution-set argument of Mac Lane CWM §V.6-V.7 (printed
    p. 128) needs: an index built from relations on a carrier is carrier-sized
    only when those relations are [Prop]-valued.  The control is [CRelSpace],
    the same space at [Type@{v}] with [u < v]. *)

Fail Definition CRelSpace_small@{u} (A : Type@{u}) : Type@{u} :=
  A -> A -> Type@{u}.

(** ** NEGATIVE 5 (UNIVERSE): [Setoid] is one level up, [PropEquiv] is not

    Stripped and re-run in a copy of the whole file, the message is

      In environment
      A : Type
      The term "Setoid A" has type "Type@{u+1}" while it is expected to have
      type "Type@{u}"
      (universe inconsistency: Cannot enforce u < u because u = u).

    -- the same contrast one level of packaging up: the setoid RECORD does not
    fit at its own carrier's universe, while [PropEquiv] of that record does
    ([PropEquiv_at_carrier] above).  The control is [Setoid_above_carrier], the
    same record at [Type@{v}] with [u < v]. *)

Fail Definition Setoid_at_carrier@{u} (A : Type@{u}) : Type@{u} :=
  Setoid@{u u} A.
