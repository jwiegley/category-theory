Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Natural transformations into a preorder *)

(* nLab:  https://ncatlab.org/nlab/show/preorder
   nLab:  https://ncatlab.org/nlab/show/thin+category
   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer 1998, §I.4, printed p. 19, exercise 4
   Book:  Fong and Spivak, "Seven Sketches in Compositionality", Cambridge
          2019, §3.3.4, Example 3.57 (printed pp. 96-97) and Exercise 3.58
          (printed p. 97)
   Book:  Riehl, "Category Theory in Context", Dover 2016, §1.4,
          Exercise 1.4.iii (printed p. 30)

   Let [P] be a preorder, regarded as the thin category [Proset P] of
   Instance/Proset.v: objects are the elements of the carrier, and there is a
   morphism [x ~> y] exactly when [R x y] holds.  Mac Lane's exercise asks for
   the natural transformations between two functors [S T : C ⟶ Proset P]:

     a natural transformation [S ⟹ T] exists if and only if [S c ≤ T c] for
     every object [c] of [C], and when it exists it is unique.

   Both halves are visible in the [Proset] construction.  A component of a
   transformation at [c] is by definition a morphism [S c ~> T c], which is
   literally a proof of [R (S c) (T c)]; so a transformation carries exactly a
   pointwise family of order witnesses.  Conversely such a family assembles
   into a transformation with no side condition, because the hom-setoid of
   [Proset] is [fun _ _ => True] (all parallel morphisms are identified), so
   every naturality square commutes for free.  Uniqueness is the same
   observation once more: any two transformations [S ⟹ T] agree componentwise
   under [≈], since [≈] on each hom-set of [Proset] is the total relation.

   The library's setoid discipline is what makes "unique" the right word here.
   Two transformations built from *different* proofs of the same pointwise
   order are not equal in Coq's intensional sense, and nothing in this file
   claims they are; they are equal in the hom-setoid of the functor category,
   which is the library's notion of sameness for morphisms throughout (see
   [Transform_Setoid] in Theory/Natural/Transformation.v).  Every comparison
   of two morphisms below uses [≈] WHEREVER THE COMPARISON IS WHAT IS AT
   STAKE — uniqueness, thinness, the isomorphism laws.

   There is exactly one deliberate exception, and an audit of the first
   commit was right to insist it be named rather than covered by a
   universal: [endo_of_monotone_of_endo_fmap] states an [=] between two
   morphisms of [Nat_Proset].  It is stated that way because it is the
   informative form.  Its [≈] counterpart is vacuous — [≈] between [Proset]
   morphisms is the total relation, so the [≈] version would hold of any two
   morphisms whatever — whereas the [=] version says something real: the
   arrow part of the round trip is the ORIGINAL arrow, on the nose.  The
   remaining [=] statements in this file are round-trip identities for the
   translation functions and an object-part agreement, and each is flagged
   where it appears. *)

(* What the exercise buys, and where the dual argument stops

   nLab:  https://ncatlab.org/nlab/show/thin+category
   nLab:  https://ncatlab.org/nlab/show/functor+category
   Book:  Fong and Spivak, "Seven Sketches in Compositionality", Cambridge
          2019, §3.3.4
   Book:  Riehl, "Category Theory in Context", Dover 2016, §1.4

   Existence-and-uniqueness together say that the hom-sets of the functor
   category [[C, Proset P]] are subsingletons: at most one morphism up to [≈]
   between any two objects.  That is precisely thinness, so the functor
   category into a preorder is itself a preorder — the headline of Fong and
   Spivak's Example 3.57, which the pointwise existence lemma alone does not
   state.  The order in question is the pointwise one, [S ≤ T] iff [S c ≤ T c]
   for all [c], and the identification of [[C, Proset P]] with the proset of
   that order is [Fun_Proset_iso] (in [Cat]) and [Fun_Proset_strict_iso] (in
   [StrictCat]) below.  Instantiated at the naturals it says that the category
   of endofunctors of [(ℕ, ≤)] is the preorder of monotone maps
   [ℕ → ℕ] ordered pointwise — [endo_nat_monotone_iso].

   The identification at the naturals has a subtlety the general statement does
   not.  A functor [Proset P ⟶ Proset Q] *is* a monotone map: its object part
   is the map, its arrow part is the monotonicity proof, and the functor laws
   are vacuous in a thin target.  Passing from a monotone map back to a functor
   nonetheless has to supply arrow data, and the choice is unique only up to
   [≈] — which is exactly why the round trip is an isomorphism in [Cat] rather
   than an equality of functors.  Note that [≅[Cat]] in this library already
   IS equivalence of categories, because [Functor_Setoid] identifies naturally
   isomorphic functors (Instance/Cat.v); the on-the-nose statements available
   here are recorded separately as [monotone_of_endo_of_monotone] and
   [endo_of_monotone_of_endo].

   The dual is false, and Fong and Spivak's Exercise 3.58 asks for the
   counterexample: transformations *out of* a preorder need not be unique,
   since nothing about the domain constrains the target's hom-sets.  Below,
   the domain is the preorder [(ℕ, ≤)] and the target is the walking parallel
   pair [Parallel] of Instance/Parallel.v, whose two arrows [ParX ~> ParY] are
   kept apart by a boolean tag in its hom-setoid; the two constant-functor
   transformations built from them are shown non-equivalent in the
   transformation setoid ([proset_out_not_unique]), not merely written
   differently.

   Riehl's Exercise 1.4.iii is the special case in which the domain is also a
   preorder: a natural transformation between monotone maps of preorders is
   unique when it exists.  Everything below quantifies over an arbitrary domain
   category [C], so that case is an instance rather than a separate theorem;
   [proset_to_proset_transform_iff] records it explicitly. *)

(** ** Mac Lane §I.4, exercise 4: existence and uniqueness *)

Section ProsetTransform.

Context {C : Category}.
Context {A : Type}.
Context {R : relation A}.
Context {P : PreOrder R}.

(* The pointwise order on functors into a proset: [S ≤ T] when [S c ≤ T c] for
   every object [c].  Note that [S c] is the object part of the functor applied
   to [c] (via the [fobj] coercion), so this is a relation on [C ⟶ Proset P]
   with values in [Prop], exactly as [R] itself is. *)

Definition proset_pointwise (S T : C ⟶ Proset P) : Prop :=
  ∀ c : C, R (S c) (T c).

(* Right to left: a pointwise family of order witnesses IS a transformation.
   The components are the witnesses themselves, and both naturality fields are
   proofs of [True] because the hom-setoid of [Proset] identifies all parallel
   morphisms.  No hypothesis on [S], [T] or [C] is used. *)

Definition proset_transform {S T : C ⟶ Proset P}
           (H : proset_pointwise S T) : S ⟹ T :=
  @Build_Transform C (Proset P) S T (fun c => H c)
                   (fun _ _ _ => I) (fun _ _ _ => I).

(* Left to right: read the pointwise witnesses off the components. *)

Definition proset_pointwise_of {S T : C ⟶ Proset P}
           (N : S ⟹ T) : proset_pointwise S T :=
  fun c => transform N c.

(* The existence criterion.  [↔] is notation (declared in Lib/Foundation.v)
   for [iffT] of Coq.Classes.CRelationClasses, the Type-valued
   biconditional the library uses for statements whose two directions carry
   computational content — here the two translations just given. *)

Theorem proset_transform_iff (S T : C ⟶ Proset P) :
  (S ⟹ T) ↔ proset_pointwise S T.
Proof. exact (@proset_pointwise_of S T, @proset_transform S T). Qed.

(* The two translations are mutually inverse.  One round trip is a propositional
   equality of order-witness families (it holds by eta), the other an
   equivalence of transformations; the latter cannot be an equality, since
   rebuilding a transformation replaces its naturality proofs.

   The [=] in the first is deliberate and is not a lapse from the library's
   [≈] discipline: it is a round-trip statement about the two translation
   functions, and its [≈] counterpart would be vacuous here, since [≈] between
   two families of [Proset] morphisms is the total relation.  Everywhere the
   comparison of two morphisms is what is at stake — uniqueness, thinness, the
   isomorphism laws — the statements below use [≈].

   AND THE SECOND ROUND TRIP IS VACUOUS, which the first commit advertised as
   though it were evidence of invertibility.  It is not: it is
   [proset_transform_unique] wearing a round-trip costume.  Its proof is
   [fun _ => I], and the same proof establishes `M ≈ N` for ANY two
   transformations between the same functors, related to the translations or
   not.  The informative half of the pair is therefore the [=] statement
   alone; the [≈] statement is kept because the shape of a round trip is
   what a reader looks for, but it carries no information beyond thinness. *)

Theorem proset_pointwise_of_transform {S T : C ⟶ Proset P}
        (H : proset_pointwise S T) :
  proset_pointwise_of (proset_transform H) = H.
Proof. reflexivity. Qed.

Theorem proset_transform_of_pointwise {S T : C ⟶ Proset P} (N : S ⟹ T) :
  proset_transform (proset_pointwise_of N) ≈ N.
Proof. exact (fun _ => I). Qed.

(* Uniqueness: any two transformations [S ⟹ T] are equal in the hom-setoid.
   The proof is [fun _ => I]: componentwise the goal is the trivial relation of
   [Proset]'s hom-setoid.  It is stated all the same, as the exercise does. *)

Theorem proset_transform_unique {S T : C ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (fun _ => I). Qed.

(* The headline of the exercise, both halves in one statement: the hom-setoid
   of [[C, Proset P]] between any two objects is inhabited exactly when the
   pointwise order holds, and has at most one element up to [≈]. *)

Theorem proset_transform_subsingleton (S T : C ⟶ Proset P) :
  ((S ⟹ T) ↔ proset_pointwise S T) ∧ (∀ α β : S ⟹ T, α ≈ β).
Proof. exact (proset_transform_iff S T, @proset_transform_unique S T). Qed.

(** ** Seven Sketches Example 3.57: the functor category is thin *)

(* Thinness of [[C, Proset P]] is uniqueness restated one level up: any two
   parallel morphisms of the functor category agree under [≈].  (The library
   has no [Thin] predicate to instantiate — there is no Structure/Thin.v and no
   such class anywhere in the tree — so the property is stated directly.) *)

Theorem Fun_Proset_thin (S T : [C, Proset P])
        (α β : S ~{[C, Proset P]}~> T) : α ≈ β.
Proof. exact (fun _ => I). Qed.

(* Hence a preorder.  The pointwise order on functors is reflexive and
   transitive because [R] is, so it presents [[C, Proset P]] as a proset. *)

(* Kept a plain [Definition] rather than an [Instance]: registering a
   [PreOrder] for an arbitrary pointwise relation as a global typeclass
   instance would enter resolution for every [PreOrder] goal in the library,
   and nothing here needs it to be found automatically. *)

Definition Fun_Proset_PreOrder : PreOrder proset_pointwise.
Proof.
  constructor.
  - intros S c.
    exact (@PreOrder_Reflexive A R P (S c)).
  - intros S T U H1 H2 c.
    exact (@PreOrder_Transitive A R P (S c) (T c) (U c) (H1 c) (H2 c)).
Defined.

Definition Fun_Proset : Category := Proset Fun_Proset_PreOrder.

(* The comparison, in both directions.  Each is the identity on objects: the
   objects of [Fun_Proset] are by construction the functors [C ⟶ Proset P],
   i.e. the objects of [[C, Proset P]].  Only the morphism parts differ, and
   they are the two translations of the existence criterion. *)

Program Definition Fun_Proset_forward : [C, Proset P] ⟶ Fun_Proset := {|
  fobj := fun S => S;
  fmap := fun S T N => proset_pointwise_of N
|}.

Program Definition Fun_Proset_backward : Fun_Proset ⟶ [C, Proset P] := {|
  fobj := fun S => S;
  fmap := fun S T H => proset_transform H
|}.

(* [[C, Proset P] ≅[Cat] Fun_Proset].  Because both composites are the identity
   on objects definitionally, the natural isomorphisms witnessing the two
   round trips have identity components, and their coherence conditions are
   discharged by thinness of the targets. *)

Theorem Fun_Proset_iso : [C, Proset P] ≅[Cat] Fun_Proset.
Proof.
  unshelve econstructor.
  - exact Fun_Proset_forward.
  - exact Fun_Proset_backward.
  - exists (fun x => @iso_id Fun_Proset x).
    intros; exact I.
  - exists (fun x => @iso_id ([C, Proset P]) x).
    intros; exact (fun _ => I).
Defined.

(* The same comparison in [StrictCat], where functors are compared by
   [Functor_StrictEq_Setoid]: propositional equality of object parts together
   with agreement of the morphism parts in the target hom-setoid.  Here the
   object parts are equal by [eq_refl] — both composites are literally the
   identity on objects — and the morphism condition is trivial because both
   categories are thin.  This is stronger than the [Cat] statement — strict
   equality of functors implies natural isomorphism (Instance/StrictCat.v's
   header) and the converse fails (Instance/Cat.v, which is where that
   failure is actually recorded) — and it is worth having precisely because
   [≅[Cat]] in this library IS equivalence of categories, never an
   on-the-nose isomorphism.  It is still *not* the assertion that the two
   composite functors are equal as records, which would need function
   extensionality to identify their proof fields.

   A reader should also not over-read the strict form HERE.  Because both
   categories are thin, the arrow-agreement leg of the strict hom-setoid is
   the trivial relation, so what this theorem asserts beyond the [Cat] form
   is that the two comparison functors agree with the identity ON OBJECTS,
   definitionally.  That is a real strengthening and it is why the object leg
   is [eq_refl], but it is not a bijection of hom-sets — thin categories have
   nothing to bijate.  The content of the comparison lives in the functors
   themselves, which carry the criterion. *)

Theorem Fun_Proset_strict_iso : [C, Proset P] ≅[StrictCat] Fun_Proset.
Proof.
  unshelve econstructor.
  - exact Fun_Proset_forward.
  - exact Fun_Proset_backward.
  - exists (fun x => eq_refl).
    intros; exact I.
  - exists (fun x => eq_refl).
    intros; exact (fun _ => I).
Defined.

End ProsetTransform.

(** ** Riehl Exercise 1.4.iii: the preorder-to-preorder case *)

(* The development above quantifies over an arbitrary domain category [C], so
   the case in which the domain is itself a preorder — Riehl's exercise, and
   the setting of Seven Sketches' monotone maps — is an instance rather than a
   separate theorem.  It is recorded here explicitly. *)

Corollary proset_to_proset_transform_iff
          {B : Type} {Rb : relation B} (Q : PreOrder Rb)
          {A : Type} {R : relation A} (P : PreOrder R)
          (S T : Proset Q ⟶ Proset P) :
  (S ⟹ T) ↔ (∀ b : B, R (S b) (T b)).
Proof. exact (proset_transform_iff S T). Qed.

Corollary proset_to_proset_transform_unique
          {B : Type} {Rb : relation B} (Q : PreOrder Rb)
          {A : Type} {R : relation A} (P : PreOrder R)
          {S T : Proset Q ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (proset_transform_unique α β). Qed.

(** ** Seven Sketches Example 3.57 at the naturals: monotone maps *)

(* [Nat_Proset] is the preorder [(ℕ, ≤)] as a category: the example
   [LessThanEqualTo_Category] of Instance/Proset.v.  Instance/Poset.v exports a
   same-named example, so the reference below is fully qualified. *)

Definition Nat_Proset : Category :=
  Category.Instance.Proset.LessThanEqualTo_Category.

(* Monotone maps [ℕ → ℕ], ordered pointwise. *)

Definition Monotone : Type :=
  ∃ m : nat → nat,
    ∀ x y : nat, PeanoNat.Nat.le x y → PeanoNat.Nat.le (m x) (m y).

Definition monotone_le : relation Monotone :=
  fun m m' => ∀ n : nat, PeanoNat.Nat.le (`1 m n) (`1 m' n).

Definition monotone_le_PreOrder : PreOrder monotone_le.
Proof.
  constructor.
  - intros m n.
    exact (PeanoNat.Nat.le_refl (`1 m n)).
  - intros m m' m'' H1 H2 n.
    exact (PeanoNat.Nat.le_trans _ _ _ (H1 n) (H2 n)).
Defined.

Definition MonotoneProset : Category := Proset monotone_le_PreOrder.

(* An endofunctor of [(ℕ, ≤)] IS a monotone map: its object part is the map and
   its arrow part is the monotonicity proof.

   Every [Monotone] value in this file is built in tactic mode so that the
   expected type drives the elaboration of the dependent pair.  Written as a
   term, Coq 8.19 and 8.20 infer a NON-dependent [sigT] predicate for the pair
   and then cannot reconcile it with [Monotone], whose predicate genuinely
   mentions the map; taking the goal as given removes that guess. *)

Definition monotone_of_endo (F : Nat_Proset ⟶ Nat_Proset) : Monotone.
Proof.
  exists (fobj[F]).
  intros x y h.
  exact (fmap[F] h).
Defined.

(* Conversely a monotone map determines an endofunctor.  The arrow part has to
   be supplied — it is the monotonicity proof — and the three functor laws are
   proofs of [True] in the thin target. *)

Program Definition endo_of_monotone (m : Monotone) : Nat_Proset ⟶ Nat_Proset := {|
  fobj := `1 m;
  fmap := fun x y h => `2 m x y h
|}.

(* One round trip holds on the nose: rebuilding a monotone map through its
   endofunctor returns it up to eta of the sigma pair. *)

Theorem monotone_of_endo_of_monotone (m : Monotone) :
  monotone_of_endo (endo_of_monotone m) = m.
Proof. destruct m; reflexivity. Qed.

(* The other round trip returns a functor with the same object part and the
   same arrow part — both hold by [eq_refl], recorded below — but with freshly
   built proof fields.  Identifying those with the original's would need
   function extensionality, which this library does not assume; what IS
   available axiom-free is equivalence in [Functor_StrictEq_Setoid], i.e. equal
   object parts plus agreeing arrow parts. *)

Example endo_of_monotone_of_endo_fobj (F : Nat_Proset ⟶ Nat_Proset) :
  fobj[endo_of_monotone (monotone_of_endo F)] = fobj[F] := eq_refl.

Example endo_of_monotone_of_endo_fmap (F : Nat_Proset ⟶ Nat_Proset)
        (x y : nat) (h : PeanoNat.Nat.le x y) :
  fmap[endo_of_monotone (monotone_of_endo F)] h = fmap[F] h := eq_refl.

Theorem endo_of_monotone_of_endo (F : Nat_Proset ⟶ Nat_Proset) :
  endo_of_monotone (monotone_of_endo F) ≈[StrictCat] F.
Proof.
  exists (fun x => eq_refl).
  intros; exact I.
Qed.

(* The comparison functors. *)

Program Definition Endo_Monotone_forward :
  [Nat_Proset, Nat_Proset] ⟶ MonotoneProset := {|
  fobj := monotone_of_endo;
  fmap := fun F G N n => transform N n
|}.

Program Definition Endo_Monotone_backward :
  MonotoneProset ⟶ [Nat_Proset, Nat_Proset] := {|
  fobj := endo_of_monotone;
  fmap := fun m m' H =>
    @Build_Transform Nat_Proset Nat_Proset
      (endo_of_monotone m) (endo_of_monotone m')
      (fun n => H n) (fun _ _ _ => I) (fun _ _ _ => I)
|}.

(* The headline of Example 3.57 at the naturals: the category of endofunctors
   of [(ℕ, ≤)] is the preorder of monotone maps ordered pointwise.

   The strength achieved is an isomorphism in [Cat] — which in this library IS
   equivalence of categories, since [Functor_Setoid] identifies naturally
   isomorphic functors (Instance/Cat.v).  Unlike [Fun_Proset_strict_iso] there
   is no [StrictCat] counterpart here: the composite
   [Endo_Monotone_backward ◯ Endo_Monotone_forward] sends a functor to a
   functor with the same object and arrow parts but rebuilt proof fields, and
   the [StrictCat] hom-setoid would require those two *functors* to be
   propositionally equal as objects of [[Nat_Proset, Nat_Proset]], which is
   function extensionality applied to their [True]-valued fields.  The
   on-the-nose content that IS available is isolated in
   [monotone_of_endo_of_monotone], [endo_of_monotone_of_endo] and the two
   [eq_refl] examples above. *)

Theorem endo_nat_monotone_iso :
  [Nat_Proset, Nat_Proset] ≅[Cat] MonotoneProset.
Proof.
  unshelve econstructor.
  - exact Endo_Monotone_forward.
  - exact Endo_Monotone_backward.
  - unshelve refine (_; _).
    + intro m.
      unshelve econstructor.
      * intro n; exact (PeanoNat.Nat.le_refl (`1 m n)).
      * intro n; exact (PeanoNat.Nat.le_refl (`1 m n)).
      * exact I.
      * exact I.
    + intros; exact I.
  - unshelve refine (_; _).
    + intro F.
      unshelve econstructor.
      * exact (@Build_Transform Nat_Proset Nat_Proset
                 (endo_of_monotone (monotone_of_endo F)) F
                 (fun n => PeanoNat.Nat.le_refl (F n))
                 (fun _ _ _ => I) (fun _ _ _ => I)).
      * exact (@Build_Transform Nat_Proset Nat_Proset
                 F (endo_of_monotone (monotone_of_endo F))
                 (fun n => PeanoNat.Nat.le_refl (F n))
                 (fun _ _ _ => I) (fun _ _ _ => I)).
      * exact (fun _ => I).
      * exact (fun _ => I).
    + intros; exact (fun _ => I).
Defined.

(** ** The criterion has teeth: existence and non-existence *)

(* Neither half of the exercise is vacuous.  The two monotone maps below are
   comparable in one direction and not the other, and the criterion converts
   that numeric fact into the existence — respectively the non-existence — of a
   natural transformation.  In particular [no_transform_id_to_zero] runs the
   forward direction of [proset_transform_iff] to REFUTE the existence of a
   transformation, which a vacuously true criterion could not do. *)

Definition monotone_zero : Monotone.
Proof.
  exists (fun _ : nat => 0%nat).
  intros x y h.
  exact (PeanoNat.Nat.le_refl 0%nat).
Defined.

Definition monotone_id : Monotone.
Proof.
  exists (fun n : nat => n).
  intros x y h.
  exact h.
Defined.

Definition Endo_zero : Nat_Proset ⟶ Nat_Proset := endo_of_monotone monotone_zero.
Definition Endo_id : Nat_Proset ⟶ Nat_Proset := endo_of_monotone monotone_id.

(* [0 ≤ n] holds pointwise, so a transformation exists (and by
   [proset_transform_unique] it is the only one up to [≈]). *)

Definition zero_le_id : proset_pointwise Endo_zero Endo_id.
Proof.
  intro n.
  exact (PeanoNat.Nat.le_0_l n).
Defined.

Definition transform_zero_to_id : Endo_zero ⟹ Endo_id :=
  proset_transform zero_le_id.

(* The converse pointwise order breaks down at [1], so by the criterion there
   is no transformation in the other direction. *)

Theorem not_id_le_zero : ¬ proset_pointwise Endo_id Endo_zero.
Proof.
  intro H.
  specialize (H 1%nat).
  simpl in H.
  inversion H.
Qed.

Theorem no_transform_id_to_zero : ¬ (Endo_id ⟹ Endo_zero).
Proof.
  intro N.
  exact (not_id_le_zero (proset_pointwise_of N)).
Qed.

(** ** Seven Sketches Exercise 3.58, clause 2: the dual is refuted *)

(* Transformations *out of* a preorder need not be unique.  The domain is the
   preorder [(ℕ, ≤)] — a genuine preorder with infinitely many objects and
   non-identity arrows — and the target is the walking parallel pair
   [Parallel] of Instance/Parallel.v, whose hom-setoid compares the boolean tag
   of an arrow and so genuinely tells [ParOne] and [ParTwo] apart.  ([_2] of
   Instance/Two.v would not serve: it is thin, with [TwoXY] the only arrow
   [TwoX ~> TwoY] and [Morphism_equality] for its hom-setoid, so no two
   parallel arrows there are distinguishable.)

   The two functors are the constant functors at [ParX] and [ParY], obtained
   from the diagonal [Diagonal] of Functor/Diagonal.v; the two transformations
   are the images under the diagonal of the two parallel arrows, so their
   naturality is [Diagonal]'s own. *)

Definition par_one : ParX ~{Parallel}~> ParY := (true; ParOne).
Definition par_two : ParX ~{Parallel}~> ParY := (false; ParTwo).

Definition ConstParX : Nat_Proset ⟶ Parallel :=
  @Diagonal Parallel Nat_Proset ParX.
Definition ConstParY : Nat_Proset ⟶ Parallel :=
  @Diagonal Parallel Nat_Proset ParY.

Definition proset_out_one : ConstParX ⟹ ConstParY :=
  fmap[@Diagonal Parallel Nat_Proset] par_one.
Definition proset_out_two : ConstParX ⟹ ConstParY :=
  fmap[@Diagonal Parallel Nat_Proset] par_two.

(* Distinctness in the transformation setoid, which is what the exercise wants:
   not that the two are written differently, but that they cannot be identified
   under [≈].  Testing the components at the object [0] reduces the claim to
   [true = false]. *)

Theorem proset_out_not_unique : ¬ (proset_out_one ≈ proset_out_two).
Proof.
  intro H.
  specialize (H 0%nat).
  simpl in H.
  discriminate.
Qed.

(* For contrast, in the direction the exercise does hold, any pair of functors
   out of [Parallel] has at most one transformation between them once the
   *target* is a preorder — an instance of [proset_transform_unique]. *)

Corollary proset_in_unique {A : Type} {R : relation A} (P : PreOrder R)
          {S T : Parallel ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (proset_transform_unique α β). Qed.
