Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(** * Finite pointed sets: the unconditional witness *)

(* nLab:      https://ncatlab.org/nlab/show/decidable+equality
   nLab:      https://ncatlab.org/nlab/show/finite+set
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              Springer 1998, §I.7 (printed p. 26)

   Instance/Sets/Pointed.v proves two halves of Mac Lane's proposition over
   explicit hypotheses — decidable image membership for the splitting of a
   monic, an enumerated domain plus a decidable codomain for the splitting of
   an epic — because without them the statements are not constructively
   available ("every epimorphism splits" being the axiom of choice).  This
   file discharges all of them at once, for the class where they are free:
   finite pointed sets with decidable equality.

   [pointed_image_dec] is the general bridge — an enumerated domain and a
   decidable codomain make image membership decidable, by running the
   first-preimage search and reading off the answer — after which
   [finite_monic_split] and [finite_epic_split] state the two halves with no
   hypotheses beyond finiteness.  [pointed_balanced] needed none to begin
   with.

   The witnesses are the two-element pointed set [PointedBool] ([bool] pointed
   at [false]) and the three-element [PointedThree] ([option bool] pointed at
   [None]), both under Leibniz equality, and EVERYTHING BELOW COMPUTES: the
   retraction of a concrete monic and the section of a concrete epic are
   evaluated at each point by [reflexivity], which is why the two splitting
   theorems of Instance/Sets/Pointed.v end in [Defined].  The section is the
   more instructive of the two, since it exhibits both branches of the
   construction: the basepoint is sent to the basepoint by fiat, and [true] to
   the FIRST element of the enumeration lying over it.

   Non-vacuity is settled here as well: [bool_to_three] is monic and not epic,
   [three_to_bool] is epic and not monic, so neither implication of
   [pointed_balanced] is trivial, and the basepoint-fixing [pointed_swap] of
   [PointedThree] is invertible purely by being both — no inverse was
   supplied to the theorem. *)

(** ** Discharging the hypotheses *)

(* Transporting between `≈` at a discrete setoid and Coq's `=`.  Both
   directions are the identity function — [eq_Setoid]'s `≈` IS `=` — but
   naming them lets [discriminate] and [f_equal] be used directly. *)
Definition eq_of_equiv {A : Type} {x y : A}
  (H : @equiv A (eq_Setoid A) x y) : x = y := H.

Definition equiv_of_eq {A : Type} {x y : A}
  (H : x = y) : @equiv A (eq_Setoid A) x y := H.

(* From an enumerated domain and a decidable codomain, image membership is
   decidable: run the search, and read the answer off it.  This is the
   hypothesis of [pointed_monic_split], discharged. *)
Definition pointed_image_dec {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) : ImageDecidable f.
Proof.
  intro b.
  destruct (pointed_search f deq (enum_list E) b) as [a|] eqn:Hs.
  - left.
    exists a.
    exact (pointed_search_correct f deq (enum_list E) b a Hs).
  - right.
    intros [a Ha].
    exact (pointed_search_complete f deq (enum_list E) b a
             (enum_covers E a) Ha Hs).
Defined.

(* Decidability of the basepoint is a special case of decidability of `≈`. *)
Definition DecidablePt_of_DecidableEquiv {Z : PointedSetoid}
  (deq : DecidableEquiv Z) : DecidablePt Z := fun z => deq z (pt Z).

(* Between finite pointed sets the two splitting halves of Mac Lane's
   proposition hold with no further hypotheses. *)
Definition finite_monic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (E : PointedEnumeration X) (deq : DecidableEquiv Y) : Monic f → Section f :=
  fun Hm => pointed_monic_split f (pointed_image_dec f deq E) Hm.

Definition finite_epic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (E : PointedEnumeration X) (deq : DecidableEquiv Y) : Epic f → Retraction f :=
  fun He => pointed_epic_split f deq E He.

(** *** Two concrete finite pointed sets *)

(* The two-element pointed set: [bool] pointed at [false]. *)
Definition PointedBool : PointedSetoid := {|
  pointed_setoid := {| carrier := bool ; is_setoid := eq_Setoid bool |};
  pt := false
|}.

(* The three-element pointed set: [option bool] pointed at [None]. *)
Definition PointedThree : PointedSetoid := {|
  pointed_setoid := {| carrier   := option bool
                     ; is_setoid := eq_Setoid (option bool) |};
  pt := Datatypes.None
|}.

Definition PointedBool_deq : DecidableEquiv PointedBool.
Proof.
  intros x y.
  destruct x, y.
  - left; reflexivity.
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - left; reflexivity.
Defined.

Definition PointedThree_deq : DecidableEquiv PointedThree.
Proof.
  intros x y.
  destruct x as [[|]|], y as [[|]|].
  - left; reflexivity.
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - left; reflexivity.
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - left; reflexivity.
Defined.

Definition PointedBool_enum : PointedEnumeration PointedBool.
Proof.
  refine (Build_PointedEnumeration PointedBool
            (Datatypes.cons false (Datatypes.cons true Datatypes.nil)) _).
  intro x.
  destruct x.
  - right; left; reflexivity.
  - left; reflexivity.
Defined.

Definition PointedThree_enum : PointedEnumeration PointedThree.
Proof.
  refine (Build_PointedEnumeration PointedThree
            (Datatypes.cons Datatypes.None
              (Datatypes.cons (Datatypes.Some false)
                (Datatypes.cons (Datatypes.Some true) Datatypes.nil))) _).
  intro x.
  destruct x as [[|]|].
  - right; right; left; reflexivity.
  - right; left; reflexivity.
  - left; reflexivity.
Defined.

(* Basepoint decidability at each of the two objects — the object-level form
   of the hypothesis [pointed_part_equivalence] asks for globally. *)
Definition PointedBool_dec_pt : DecidablePt PointedBool :=
  DecidablePt_of_DecidableEquiv PointedBool_deq.

Definition PointedThree_dec_pt : DecidablePt PointedThree :=
  DecidablePt_of_DecidableEquiv PointedThree_deq.

(** *** Concrete maps between them, and the theorems exercised *)

(* A map between discrete setoids is respectful for free, so these concrete
   morphisms are built by direct record application rather than through
   [Program]. *)
Definition eq_setoid_map {A B : Type} (f : A -> B) :
  @SetoidMorphism A (eq_Setoid A) B (eq_Setoid B) :=
  {| morphism        := f
   ; proper_morphism := fun x y H => equiv_of_eq (f_equal f (eq_of_equiv H)) |}.

(* [false ↦ None], [true ↦ Some false]: injective, not surjective. *)
Definition bool_to_three_fun (b : bool) : option bool :=
  match b with
  | true => Datatypes.Some false
  | false => Datatypes.None
  end.

Definition bool_to_three_map := eq_setoid_map bool_to_three_fun.

Definition bool_to_three : PointedBool ~{PointedSets}~> PointedThree.
Proof.
  refine (Build_PointedMorphism PointedBool PointedThree bool_to_three_map _).
  reflexivity.
Defined.

(* [None ↦ false], [Some _ ↦ true]: surjective, not injective. *)
Definition three_to_bool_fun (o : option bool) : bool :=
  match o with
  | Datatypes.Some _ => true
  | Datatypes.None => false
  end.

Definition three_to_bool_map := eq_setoid_map three_to_bool_fun.

Definition three_to_bool : PointedThree ~{PointedSets}~> PointedBool.
Proof.
  refine (Build_PointedMorphism PointedThree PointedBool three_to_bool_map _).
  reflexivity.
Defined.

Lemma bool_to_three_injective : PointedInjective bool_to_three.
Proof.
  intros a b H.
  destruct a, b.
  - reflexivity.
  - discriminate (eq_of_equiv H).
  - discriminate (eq_of_equiv H).
  - reflexivity.
Qed.

Definition bool_to_three_monic : Monic bool_to_three :=
  fst (pointed_monic_iff bool_to_three) bool_to_three_injective.

Lemma three_to_bool_surjective : PointedSurjective three_to_bool.
Proof.
  intro b.
  destruct b.
  - exists (Datatypes.Some false).
    reflexivity.
  - exists Datatypes.None.
    reflexivity.
Qed.

Definition three_to_bool_epic : Epic three_to_bool :=
  fst (pointed_epic_iff three_to_bool) three_to_bool_surjective.

(* Non-vacuity, in both directions: a monic that is not epic, and an epic that
   is not monic.  Set_* is therefore genuinely not balanced-by-triviality —
   [pointed_balanced] has content. *)
Lemma bool_to_three_not_epic : ¬ Epic bool_to_three.
Proof.
  intro He.
  destruct (pointed_epic_surjective bool_to_three He (Datatypes.Some true))
    as [a Ha].
  destruct a; discriminate (eq_of_equiv Ha).
Qed.

Lemma three_to_bool_not_monic : ¬ Monic three_to_bool.
Proof.
  intro Hm.
  pose proof (snd (pointed_monic_iff three_to_bool) Hm) as Hinj.
  pose proof (Hinj (Datatypes.Some false) (Datatypes.Some true)
                (equiv_of_eq (@eq_refl bool true))) as H.
  discriminate (eq_of_equiv H).
Qed.

(* The retraction of the monic, COMPUTED by [finite_monic_split]: the two
   points of the image go to their preimages, and the point outside the image
   goes to the basepoint. *)
Definition bool_to_three_retraction : PointedThree ~{PointedSets}~> PointedBool :=
  @section PointedSets PointedBool PointedThree bool_to_three
    (finite_monic_split bool_to_three PointedBool_enum PointedThree_deq
       bool_to_three_monic).

Example bool_to_three_retraction_pt :
  bool_to_three_retraction Datatypes.None = false.
Proof. reflexivity. Qed.

Example bool_to_three_retraction_hit :
  bool_to_three_retraction (Datatypes.Some false) = true.
Proof. reflexivity. Qed.

Example bool_to_three_retraction_miss :
  bool_to_three_retraction (Datatypes.Some true) = false.
Proof. reflexivity. Qed.

(* The section of the epic, COMPUTED by [finite_epic_split]: the basepoint is
   sent to the basepoint by fiat, and [true] to the FIRST element of the
   enumeration of [PointedThree] lying over it. *)
Definition three_to_bool_section : PointedBool ~{PointedSets}~> PointedThree :=
  @retract PointedSets PointedThree PointedBool three_to_bool
    (finite_epic_split three_to_bool PointedThree_enum PointedBool_deq
       three_to_bool_epic).

Example three_to_bool_section_pt :
  three_to_bool_section false = Datatypes.None.
Proof. reflexivity. Qed.

Example three_to_bool_section_true :
  three_to_bool_section true = Datatypes.Some false.
Proof. reflexivity. Qed.

(** *** [pointed_balanced] at a concrete bimorphism *)

(* The basepoint-fixing exchange of the two free points of [PointedThree].
   The name carries the [pointed_] prefix because Structure/Cartesian.v:209
   already exports a generic [swap] combinator for cartesian products; the
   two are unrelated and must not shadow one another. *)
Definition pointed_swap_fun (o : option bool) : option bool :=
  match o with
  | Datatypes.Some b => Datatypes.Some (negb b)
  | Datatypes.None => Datatypes.None
  end.

Definition pointed_swap_map := eq_setoid_map pointed_swap_fun.

Definition pointed_swap : PointedThree ~{PointedSets}~> PointedThree.
Proof.
  refine (Build_PointedMorphism PointedThree PointedThree pointed_swap_map _).
  reflexivity.
Defined.

Lemma pointed_swap_injective : PointedInjective pointed_swap.
Proof.
  intros a b H.
  destruct a as [[|]|], b as [[|]|]; try reflexivity;
  discriminate (eq_of_equiv H).
Qed.

Lemma pointed_swap_surjective : PointedSurjective pointed_swap.
Proof.
  intro o.
  destruct o as [[|]|].
  - exists (Datatypes.Some false).
    reflexivity.
  - exists (Datatypes.Some true).
    reflexivity.
  - exists Datatypes.None.
    reflexivity.
Qed.

(* A concrete corollary of the balance theorem: this map is invertible for no
   reason other than being monic and epic — no inverse was supplied. *)
Definition pointed_swap_isomorphism : IsIsomorphism pointed_swap :=
  snd (pointed_balanced pointed_swap)
    (fst (pointed_monic_iff pointed_swap) pointed_swap_injective,
     fst (pointed_epic_iff pointed_swap) pointed_swap_surjective).

(* The inverse the theorem produced, exercised at a point: its value is forced
   by the right-inverse law together with injectivity. *)
Example pointed_swap_inverse_at_true :
  @two_sided_inverse PointedSets PointedThree PointedThree pointed_swap pointed_swap_isomorphism
    (Datatypes.Some true) ≈ Datatypes.Some false.
Proof.
  apply pointed_swap_injective.
  transitivity (Datatypes.Some true).
  - exact (@is_right_inverse PointedSets PointedThree PointedThree pointed_swap
             pointed_swap_isomorphism (Datatypes.Some true)).
  - reflexivity.
Qed.
