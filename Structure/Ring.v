Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.

Generalizable All Variables.

(** * Ring and semiring objects in a cartesian category *)

(* Mac Lane, Categories for the Working Mathematician, 2nd ed., Section
   III.6, p. 75 (maclane:III.6:remark1); nLab:
   https://ncatlab.org/nlab/show/ring+object
   https://ncatlab.org/nlab/show/internalization

   Mac Lane's Section III.6 defines monoid and group objects by commuting
   diagrams and then observes that the same device applies to ANY
   algebraic system given by finitary operations and equational laws --
   naming rings and lattices as the next examples.  This file carries out
   the ring half; Structure/Lattice.v carries out the lattice half.

   What "internalization" buys is that one definition, read in different
   ambient categories, is many classical theories at once: a ring object
   in Set is an ordinary ring, in Top a topological ring, in the category
   of schemes a ring scheme, in sheaves a sheaf of rings.  The ambient
   category must supply enough structure to STATE the axioms, and for
   rings that is more than a monoidal product: distributivity uses one
   variable twice (a copy), and annihilation drops a variable (a
   discard).  A cartesian category with a terminal object supplies both,
   which is why this file is developed over [Cartesian] + [Terminal]
   rather than over a bare [Monoidal] -- the same reason Structure/Group.v
   asks for [CartesianMonoidal] where Structure/Monoid.v asks for nothing.

   NAMING.  [RingObject] is ALREADY TAKEN: Theory/Algebra/Rig.v:469
   declares a record of that name for the SET-LEVEL notion (a ring on a
   setoid carrier), and Theory/Algebra/Rig.v:103 likewise takes
   [RigObject].  Both are in scope here, since the [Sets] section below
   compares against them, so the names could not be reused.  The tree
   already carries four distinct "monoid" notions under four names --
   [MonoidObject] (Structure/Monoid.v:124, internal), [MonObject]
   (Construction/Deloop.v:123, a bare setoid monoid), [Monoid]
   (Theory/Algebra/Monoid.v:44, internal in a monoidal category) and
   [Monoid] (Theory/Coq/Monoid.v:37, over [Coq]) -- and the disambiguation
   there runs "full spelling = internal, abbreviation = set-level"
   ([GroupObject] vs [GrpObject]).  Rig.v inverts that convention, so it
   cannot be followed; the classes here are therefore [InternalSemiring]
   and [InternalRing], with the [Internal] prefix stating exactly what
   distinguishes them.  Both names are free tree-wide, as are
   [InternalLattice] and [InternalSemilattice] in the sibling file.

   PRIOR ART.  No in-tree class carries two monoid structures on one
   object AS [Monoid]-TYPED FIELDS -- and that qualifier is the whole
   claim, an earlier revision having billed this as a search "by shape
   rather than by name" when it is a sweep by the field type's NAME.  By
   SHAPE the pattern DOES occur, and in the very file named below: sweeping
   for record bodies with two [_assoc] axioms returns
   Theory/Algebra/Rig.v:103's [RigObject], which carries [(rig_zero,
   rig_add)] and [(rig_one, rig_mul)] on one setoid carrier -- elementwise
   rather than as internal monoid objects, and it is precisely the
   set-level theory this file internalizes.  [GroupObject]
   (Structure/Group.v:112)
   is the only record anywhere with a [MonoidObject] field, and the only
   records with a field of the sibling class [Monoid] of
   Theory/Algebra/Monoid.v are Theory/Algebra/CommutativeMonoid.v:49 and
   Theory/Algebra/Frobenius.v:128 -- each carrying exactly one.  (Note
   that this file's [Monoid] is Structure/Monoid.v's
   [@MonoidObject C CC_Monoidal], not Theory/Algebra/Monoid.v's
   identically named class; only the former is required here.)  The
   closest
   structural analogues are Theory/Algebra/Frobenius.v's [Frobenius] and
   Theory/Algebra/SpecialCommutativeFrobenius.v, which put a monoid and a
   COMONOID on one object -- different variance, and no distributivity.
   The tree's only distributivity is Structure/Distributive.v's
   [Distributive] and Structure/BiCCC.v, which distribute the ambient x
   over the ambient +; that is a property of the AMBIENT category, not two
   operations carried by an object.  Structure/Preadditive.v and
   Structure/Semiadditive.v enrich HOM-SETS in commutative monoids, and
   Theory/Algebra/Rig.v's [EndRig] reads a set-level rig off an
   endomorphism hom of a preadditive category -- adjacent, but a rig on a
   hom-set rather than on an object.  Theory/Algebra/Rig.v itself is the
   set-level theory this file internalizes.

   RELATION TO LAWVERE THEORIES.  Mac Lane's remark is the informal
   version of functorial semantics: an algebraic theory presented by
   finitary operations and equations is a category with finite products,
   and its models in C are the finite-product-preserving functors into C.
   The tree has that machinery -- Theory/Lawvere.v's [LawvereTheory],
   Theory/Lawvere/Model.v's [Model] record (functor + [CartesianFunctor] +
   [TerminalFunctor] witnesses) and the category [Models] built there as a
   full subcategory of the functor category.  The present classes are the
   hand-written instances of that pattern at the theories of semirings and
   rings.  NOT DELIVERED: no bridge theorem is proved -- neither
   [MonoidObject ~= Models(Th_Mon)] nor its ring analogue -- and no
   Lawvere theory of rings is constructed here.  The connection is
   recorded as a pointer, deliberately.

   WHAT IS DELIVERED, and at what strength.

   (1) [InternalSemiring r]: an additive [Monoid] on r that is
       commutative, a multiplicative [Monoid] on r, two distributivity
       laws and two annihilation laws.  This is Seven Sketches Definition
       5.36 / Theory/Algebra/Rig.v's [RigObject] clause for clause,
       internalized; multiplication is NOT assumed commutative.

   (2) [InternalRing r]: additive [Monoid] + commutativity + a negation
       [ir_neg] with the LEFT inverse law only, multiplicative [Monoid],
       and the two distributivity laws.  Annihilation is NOT a field.

   (3) The two annihilation laws are THEOREMS for a ring
       ([ring_annihilate_l], [ring_annihilate_r]), so
       [InternalRing_InternalSemiring] is a genuine derivation and not a
       repackaging.  The engine is [ring_cancel_idem]: an arrow k into r
       with k = k + k is the zero arrow.  That is the usual cancellation
       argument carried out on morphisms -- no elements anywhere -- and it
       spends the additive associativity, the additive unit law and the
       inverse law once each (the inverse law through an intermediate step
       that is then reused twice).  The right inverse law is derived
       ([ring_neg_right]), from commutativity.

   (4) The additive half of an internal ring IS a group object:
       [InternalRing_GroupObject : @GroupObject C CC_CartesianMonoidal r],
       built by passing [ir_add] through UNCHANGED, with no transport
       anywhere.  Read the inverse fields precisely: the ring's own
       [ir_neg_left] and [ring_neg_right] are REJECTED at those
       positions, [GroupObject] wanting the [bimap]/[diagonal]/
       [eliminate] spelling where the ring states the [fork]/[one] one.
       The bridging lemmas [ir_neg_left_split] and [ir_neg_right_split]
       supply the accepted statements, and it is THOSE that meet the
       field types by conversion ([bimap] = [split], [Delta] = [id fork
       id], [eliminate] = [one]).

   (5) The [Sets] instances.  [Sets_InternalSemiring] turns a [RigObject]
       into an internal semiring in [Sets] and [Rig_of_InternalSemiring]
       turns one back; likewise [Sets_InternalRing] /
       [Ring_of_InternalRing] for [RingObject].  Round trips are measured
       STRICT-FIRST.  Rig-side: all five DATA fields return by [eq_refl]
       ([rig_round_setoid], [rig_round_zero], [rig_round_add],
       [rig_round_one], [rig_round_mul]) while the WHOLE RECORD does not,
       pinned as a [Fail] -- the law fields are rebuilt proof terms.
       Internal-side: the unit and the multiplication agree at [eq_refl]
       ON VALUES ([semiring_round_zero], [semiring_round_add]) but the
       [Monoid] record does not, also pinned -- the [SetoidMorphism]s are
       rebuilt with different [proper_morphism] certificates.  Both
       [Fail]s were stripped and confirmed to be genuine CONVERSION
       failures ("cannot unify"), not typing or universe errors.

   ENGINEERING FINDING, and it shapes every statement below.  At
   [CC_Monoidal] the tensor IS the product: [bimap f g = split f g],
   [to unit_left = exr], [to unit_right = exl] and [to tensor_assoc =
   (exl o exl) /\ ((exr o exl) /\ exr)] all hold by [eq_refl], recorded as
   the four [Example]s opening the file.  But [mappend]'s type is
   [mon (x) mon ~> mon], i.e. [fobj tensor (mon, mon) ~> mon], which is
   only CONVERTIBLE with [mon x mon] and not syntactically equal: two
   separately elaborated occurrences of [mappend[M] o swap] record
   different object arguments in their [compose] nodes (one via
   [fst (r, r)], one via [product_obj r r]), and [rewrite] then cannot
   match one against the other.  Every occurrence of [mappend] and
   [mempty] below is therefore ascribed -- [(mappend[M] : r x r ~> r)],
   [(mempty[M] : 1 ~> r)] -- which forces one syntactic form throughout.
   The ascription is visible in [Print Module] output and invisible to
   [Check]; either way it is cosmetic, and the alternative (a pair of
   ascribed accessor definitions) was rejected because the sibling
   Structure/Lattice.v would then either duplicate them or acquire a
   dependency on this file.

   UNIVERSES, measured in the constraint blocks AND in the binders.
   [InternalSemiring@{u u0 u1}] and [InternalRing@{u u0 u1}] are over
   [Category@{u u0 u0}]: the hom and proof universes are IDENTIFIED while
   the OBJECT universe stays free (it appears only in [<=] bounds).  The
   identification is the DONORS' doing and THREE of them force it
   INDEPENDENTLY -- with the levels declared apart under
   [Constraint uh < up], a control naming a hom at those levels is
   accepted while each of [@Cartesian C], [@Terminal C] and
   [@Monoidal C] is rejected, each with a genuine
   "Cannot enforce up = uh".  [MonoidObject] is NOT a fourth donor: its
   signature takes a [Monoidal@{u u0}] argument over
   [C : Category@{u u0 u0}], so [@Monoidal C] is rejected before any
   field of it is consulted and it cannot be probed apart -- whether it
   identifies anything OF ITS OWN is UNKNOWN, not refuted.  Nothing here
   adds to the identification, and it is NOT claimed unavoidable.  Note
   that [dup_left@{u u0}] and
   [dup_right@{u u0}] have EMPTY constraint blocks and yet their binders
   display [Category@{u u0 u0}] -- the identification hides in the binder,
   inherited from [Cartesian].  [InternalRing_GroupObject@{u u0 u1 u2}]
   adds only the BOUNDS [u <= u2], [u0 <= u2] from [GroupObject], never an
   identification.  On the [Sets] side the four passages carry [o < so]
   as their only STRICT constraint, and no [Set] anywhere -- the rest of
   each block is some fifteen [<=] bounds against donor universes
   ([projections], [prod_rect], [Basics.compose], [eq_ind]), among them
   [o <= q], which relates two DECLARED binders, so "nothing else" would
   be wrong even read charitably.  The [Set]-freedom holds only because
   their
   universe binders are written out: unannotated, [Sets_Monoid] minimizes
   to [SetoidObject@{Set Set}] and [Sets_InternalSemiring] to
   [RigObject@{Set Set _}], which would have confined every [Sets] result
   to Set-sized carriers.  This is the minimization hazard
   Instance/Sets/Products.v:409-424 and the #300 erratum record, met
   again.

   NON-VACUITY, proved rather than gestured at.  [Nat_ISemiring] and
   [Int_IRing] are the internal semiring and ring on the naturals and the
   integers, with the unit, zero, sum, product and negation all COMPUTING
   by [eq_refl], and both proved non-degenerate (zero and one are distinct
   -- [nat_semiring_nondegenerate], [int_ring_nondegenerate]), so the
   structures are not collapsed.  That the laws genuinely CONSTRAIN is
   proved two ways.  [nat_plus_not_distributive]: taking the additive
   monoid of the naturals as BOTH halves satisfies every monoid law and
   refutes left distributivity, so the distributivity fields are not
   automatic for an arbitrary pair of commutative monoid objects on one
   carrier.  And [Bool_Or_Monoid] -- disjunction on the two-element setoid
   -- used as both halves satisfies commutativity ([bool_or_comm]) AND
   BOTH distributivity laws ([bool_or_distrib_l], [bool_or_distrib_r])
   while refuting annihilation ([bool_or_not_annihilating]), so the
   annihilation PAIR is not implied by the rest, and [isr_annihilate_l]
   in particular is not.  Only the [_l] shape is refuted here; nothing
   below states [isr_annihilate_r]'s independence separately, though it
   follows from [bool_or_comm].  That much is why the pair must be
   assumed for a semiring and can be derived for a ring.

   WHAT IS NOT DELIVERED.
   - No bridge to Lawvere theories (see above); no theory of rings is
     constructed, and no equivalence with [Models] is stated.
   - No category of internal (semi)rings, no homomorphisms, no forgetful
     functor.  Only the object-level structure is defined.
   - No commutative-ring variant, no ideals, no modules over an internal
     ring, no internal-ring analogue of Instance/Mod.v.
   - No closure results: products of ring objects and exponentials of ring
     objects are NOT proved to be ring objects (Structure/Monoid.v proves
     the monoid analogues, [Product_Monoid] and [Hom_Monoid]; neither is
     lifted here).
   - No instance in any ambient category other than [Sets].  In
     particular no internal ring in [Top], [Coq] or a presheaf category,
     so "a ring object in Top is a topological ring" stays prose.
   - The [Sets] round trips are measured but NOT packaged as an
     equivalence or an isomorphism of categories; there is no category on
     either side to state one in.
   - [InternalRing_InternalSemiring] is a plain [Program Definition] and
     is deliberately NOT registered as an [Instance]: resolution would
     then be free to look for an [InternalRing] whenever an
     [InternalSemiring] is wanted, and the tree's practice (e.g.
     Structure/Biproduct/Cartesian.v) is to leave such passages
     unregistered.
   - Nothing is proved about the relation between [ir_neg] and
     multiplication (no (-a)b = -(ab)), and no uniqueness of negation. *)

Section CartesianMonoid.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Example bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Example unit_right_is_exl {x : C} :
  to (@unit_right C CC_Monoidal x) = exl := eq_refl.

Example tensor_assoc_is_fork {x y z : C} :
  to (@tensor_assoc C CC_Monoidal x y z)
    = (exl ∘ exl) △ ((exr ∘ exl) △ exr) := eq_refl.

Context {m : C}.
Context (M : Monoid m).

Lemma cartesian_monoid_unit_left :
  (mappend[M] : m × m ~> m) ∘ split (mempty[M] : 1 ~> m) id ≈ exr.
Proof. exact (@mempty_left _ _ _ M). Qed.

Lemma cartesian_monoid_unit_right :
  (mappend[M] : m × m ~> m) ∘ split id (mempty[M] : 1 ~> m) ≈ exl.
Proof. exact (@mempty_right _ _ _ M). Qed.

Lemma cartesian_monoid_assoc :
  (mappend[M] : m × m ~> m) ∘ split (mappend[M] : m × m ~> m) id
    ≈ (mappend[M] : m × m ~> m) ∘ split id (mappend[M] : m × m ~> m)
        ∘ ((exl ∘ exl) △ ((exr ∘ exl) △ exr)).
Proof. exact (@mappend_assoc _ _ _ M). Qed.

End CartesianMonoid.

Section Duplication.

Context {C : Category}.
Context `{@Cartesian C}.

Definition dup_left {x : C} : x × (x × x) ~> (x × x) × (x × x) :=
  second exl △ second exr.

Definition dup_right {x : C} : (x × x) × x ~> (x × x) × (x × x) :=
  first exl △ first exr.

Lemma dup_left_fork {x w : C} (a b c : w ~> x) :
  dup_left ∘ (a △ (b △ c)) ≈ (a △ b) △ (a △ c).
Proof. unfold dup_left; unfork; cat. Qed.

Lemma dup_right_fork {x w : C} (a b c : w ~> x) :
  dup_right ∘ ((a △ b) △ c) ≈ (a △ c) △ (b △ c).
Proof. unfold dup_right; unfork; cat. Qed.

Lemma prod_assoc_fork {x w : C} (a b c : w ~> x) :
  ((exl ∘ exl) △ ((exr ∘ exl) △ exr)) ∘ ((a △ b) △ c) ≈ a △ (b △ c).
Proof. unfork; cat. Qed.

End Duplication.

Section Internalize.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Class InternalSemiring (r : C) := {
  isr_add : Monoid r;
  isr_mul : Monoid r;

  isr_add_comm :
    (mappend[isr_add] : r × r ~> r) ∘ swap ≈ mappend[isr_add];

  isr_distrib_l :
    (mappend[isr_mul] : r × r ~> r) ∘ second (mappend[isr_add] : r × r ~> r)
      ≈ (mappend[isr_add] : r × r ~> r)
          ∘ split (mappend[isr_mul] : r × r ~> r) mappend[isr_mul]
          ∘ dup_left;
  isr_distrib_r :
    (mappend[isr_mul] : r × r ~> r) ∘ first (mappend[isr_add] : r × r ~> r)
      ≈ (mappend[isr_add] : r × r ~> r)
          ∘ split (mappend[isr_mul] : r × r ~> r) mappend[isr_mul]
          ∘ dup_right;

  isr_annihilate_l :
    (mappend[isr_mul] : r × r ~> r) ∘ (((mempty[isr_add] : 1 ~> r) ∘ one) △ id)
      ≈ (mempty[isr_add] : 1 ~> r) ∘ one;
  isr_annihilate_r :
    (mappend[isr_mul] : r × r ~> r) ∘ (id △ ((mempty[isr_add] : 1 ~> r) ∘ one))
      ≈ (mempty[isr_add] : 1 ~> r) ∘ one
}.

Class InternalRing (r : C) := {
  ir_add : Monoid r;
  ir_mul : Monoid r;
  ir_neg : r ~> r;

  ir_add_comm :
    (mappend[ir_add] : r × r ~> r) ∘ swap ≈ mappend[ir_add];
  ir_neg_left :
    (mappend[ir_add] : r × r ~> r) ∘ (ir_neg △ id)
      ≈ (mempty[ir_add] : 1 ~> r) ∘ one;

  ir_distrib_l :
    (mappend[ir_mul] : r × r ~> r) ∘ second (mappend[ir_add] : r × r ~> r)
      ≈ (mappend[ir_add] : r × r ~> r)
          ∘ split (mappend[ir_mul] : r × r ~> r) mappend[ir_mul]
          ∘ dup_left;
  ir_distrib_r :
    (mappend[ir_mul] : r × r ~> r) ∘ first (mappend[ir_add] : r × r ~> r)
      ≈ (mappend[ir_add] : r × r ~> r)
          ∘ split (mappend[ir_mul] : r × r ~> r) mappend[ir_mul]
          ∘ dup_right
}.

End Internalize.

Section RingDerived.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context {r : C}.
Context `{R : @InternalRing C _ _ r}.

Lemma ring_neg_right :
  (mappend[ir_add] : r × r ~> r) ∘ (id △ ir_neg)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  rewrite <- (swap_fork ir_neg id).
  rewrite comp_assoc.
  rewrite ir_add_comm.
  apply ir_neg_left.
Qed.

Lemma ring_add_zero_left {x : C} (g : x ~> r) :
  (mappend[ir_add] : r × r ~> r)
      ∘ (((mempty[ir_add] : 1 ~> r) ∘ one[x]) △ g)
    ≈ g.
Proof.
  transitivity ((mappend[ir_add] : r × r ~> r)
                  ∘ split (mempty[ir_add] : 1 ~> r) id ∘ (one[x] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite cartesian_monoid_unit_left.
  now rewrite exr_fork.
Qed.

Lemma ring_cancel_idem {x : C} (k : x ~> r) :
  k ≈ (mappend[ir_add] : r × r ~> r) ∘ (k △ k) →
  k ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  intro Hk.
  assert (HA : (mappend[ir_add] : r × r ~> r) ∘ ((ir_neg ∘ k) △ k)
                 ≈ (mempty[ir_add] : 1 ~> r) ∘ one[x]).
  { rewrite <- (id_left k) at 2.
    rewrite fork_comp, comp_assoc, ir_neg_left, <- comp_assoc.
    now rewrite one_comp. }
  assert (HB : (mappend[ir_add] : r × r ~> r)
                 ∘ (((mempty[ir_add] : 1 ~> r) ∘ one[x]) △ k)
                 ≈ (mempty[ir_add] : 1 ~> r) ∘ one[x]).
  { transitivity ((mappend[ir_add] : r × r ~> r)
                    ∘ split (mappend[ir_add] : r × r ~> r) id
                    ∘ (((ir_neg ∘ k) △ k) △ k)).
    { rewrite <- comp_assoc, split_fork, HA.
      now rewrite id_left. }
    rewrite cartesian_monoid_assoc.
    rewrite <- comp_assoc, prod_assoc_fork.
    rewrite <- comp_assoc, split_fork, id_left, <- Hk.
    exact HA. }
  now rewrite <- HB, ring_add_zero_left.
Qed.

Lemma ring_annihilate_l :
  (mappend[ir_mul] : r × r ~> r)
      ∘ (((mempty[ir_add] : 1 ~> r) ∘ one) △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  apply ring_cancel_idem.
  symmetry.
  transitivity ((mappend[ir_mul] : r × r ~> r)
                  ∘ first (mappend[ir_add] : r × r ~> r)
                  ∘ (((((mempty[ir_add] : 1 ~> r) ∘ one[r])
                        △ ((mempty[ir_add] : 1 ~> r) ∘ one[r]))) △ id)).
  { rewrite ir_distrib_r.
    rewrite <- !comp_assoc, dup_right_fork.
    now rewrite split_fork. }
  rewrite <- comp_assoc, first_fork, ring_add_zero_left.
  reflexivity.
Qed.

Lemma ring_annihilate_r :
  (mappend[ir_mul] : r × r ~> r)
      ∘ (id △ ((mempty[ir_add] : 1 ~> r) ∘ one))
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  apply ring_cancel_idem.
  symmetry.
  transitivity ((mappend[ir_mul] : r × r ~> r)
                  ∘ second (mappend[ir_add] : r × r ~> r)
                  ∘ (id △ ((((mempty[ir_add] : 1 ~> r) ∘ one[r])
                        △ ((mempty[ir_add] : 1 ~> r) ∘ one[r]))))).
  { rewrite ir_distrib_l.
    rewrite <- !comp_assoc, dup_left_fork.
    now rewrite split_fork. }
  rewrite <- comp_assoc, second_fork, ring_add_zero_left.
  reflexivity.
Qed.

Lemma ir_neg_left_split :
  (mappend[ir_add] : r × r ~> r) ∘ split ir_neg id ∘ (id △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one[r].
Proof.
  rewrite <- comp_assoc, split_fork, id_left, id_right.
  apply ir_neg_left.
Qed.

Lemma ir_neg_right_split :
  (mappend[ir_add] : r × r ~> r) ∘ split id ir_neg ∘ (id △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one[r].
Proof.
  rewrite <- comp_assoc, split_fork, id_left, id_right.
  apply ring_neg_right.
Qed.

(* [Structure/Group.v] declares [Notation "'inverse' [ G ]"], which makes
   [inverse] a notation keyword: neither [@inverse] nor a record-literal
   field assignment [inverse := _] parses.  The group object is therefore
   built with the constructor applied positionally. *)
Definition InternalRing_GroupObject :
  @GroupObject C CC_CartesianMonoidal r :=
  @Build_GroupObject C CC_CartesianMonoidal r ir_add ir_neg
    ir_neg_left_split ir_neg_right_split.

Program Definition InternalRing_InternalSemiring :
  @InternalSemiring C _ _ r := {|
  isr_add := ir_add;
  isr_mul := ir_mul
|}.
Next Obligation. exact ir_add_comm. Qed.
Next Obligation. exact ir_distrib_l. Qed.
Next Obligation. exact ir_distrib_r. Qed.
Next Obligation. exact ring_annihilate_l. Qed.
Next Obligation. exact ring_annihilate_r. Qed.

End RingDerived.

Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Section SetsInternal.

Program Definition Sets_Monoid@{o so p} (A : SetoidObject@{o o})
  (u : carrier A) (op : carrier A → carrier A → carrier A)
  (opP : Proper@{o p} (equiv ==> equiv ==> equiv) op)
  (op_assoc : ∀ a b c, op (op a b) c ≈ op a (op b c))
  (unit_l : ∀ a, op u a ≈ a)
  (unit_r : ∀ a, op a u ≈ a) : @Monoid Sets@{o so} _ _ A := {|
  mempty := {| morphism := fun _ => u |};
  mappend := {| morphism := fun p => op (fst p) (snd p) |}
|}.
Next Obligation. proper; simpl in *; now apply opP. Qed.

Program Definition Sets_InternalSemiring@{o so q} (R : RigObject@{o o q}) :
  @InternalSemiring Sets@{o so} _ _ (rig_setoid R) := {|
  isr_add := Sets_Monoid (rig_setoid R) (rig_zero R) (rig_add R)
               (rig_add_respects R) (rig_add_assoc R) (rig_add_zero_l R)
               (rig_add_zero_r R);
  isr_mul := Sets_Monoid (rig_setoid R) (rig_one R) (rig_mul R)
               (rig_mul_respects R) (rig_mul_assoc R) (rig_mul_one_l R)
               (rig_mul_one_r R)
|}.
Next Obligation. now rewrite rig_add_comm. Qed.
Next Obligation. now rewrite rig_distr_l. Qed.
Next Obligation. now rewrite rig_distr_r. Qed.
Next Obligation. now rewrite rig_mul_zero_l. Qed.
Next Obligation. now rewrite rig_mul_zero_r. Qed.

Program Definition Sets_InternalRing@{o so q} (R : RingObject@{o o q}) :
  @InternalRing Sets@{o so} _ _ (rig_setoid R) := {|
  ir_add := Sets_Monoid (rig_setoid R) (rig_zero R) (rig_add R)
              (rig_add_respects R) (rig_add_assoc R) (rig_add_zero_l R)
              (rig_add_zero_r R);
  ir_mul := Sets_Monoid (rig_setoid R) (rig_one R) (rig_mul R)
              (rig_mul_respects R) (rig_mul_assoc R) (rig_mul_one_l R)
              (rig_mul_one_r R);
  ir_neg := {| morphism := ring_neg R |}
|}.
Next Obligation. now rewrite rig_add_comm. Qed.
Next Obligation. now rewrite ring_neg_l. Qed.
Next Obligation. now rewrite rig_distr_l. Qed.
Next Obligation. now rewrite rig_distr_r. Qed.

Program Definition Rig_of_InternalSemiring@{o so} {A : SetoidObject@{o o}}
  (S : @InternalSemiring Sets@{o so} _ _ A) : RigObject@{o o o} := {|
  rig_setoid := A;
  rig_zero := (mempty[isr_add] : _ ~{Sets}~> _) ttt;
  rig_add  := fun a b => (mappend[isr_add] : _ ~{Sets}~> _) (a, b);
  rig_one  := (mempty[isr_mul] : _ ~{Sets}~> _) ttt;
  rig_mul  := fun a b => (mappend[isr_mul] : _ ~{Sets}~> _) (a, b)
|}.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation.
  exact (cartesian_monoid_assoc (@isr_add _ _ _ _ S) ((a, b), c)).
Qed.
Next Obligation. exact (@isr_add_comm _ _ _ _ S (b, a)). Qed.
Next Obligation.
  exact (cartesian_monoid_unit_left (@isr_add _ _ _ _ S) (ttt, a)).
Qed.
Next Obligation.
  exact (cartesian_monoid_assoc (@isr_mul _ _ _ _ S) ((a, b), c)).
Qed.
Next Obligation.
  exact (cartesian_monoid_unit_left (@isr_mul _ _ _ _ S) (ttt, a)).
Qed.
Next Obligation.
  exact (cartesian_monoid_unit_right (@isr_mul _ _ _ _ S) (a, ttt)).
Qed.
Next Obligation. exact (@isr_distrib_l _ _ _ _ S (a, (b, c))). Qed.
Next Obligation. exact (@isr_distrib_r _ _ _ _ S ((a, b), c)). Qed.
Next Obligation. exact (@isr_annihilate_l _ _ _ _ S a). Qed.
Next Obligation. exact (@isr_annihilate_r _ _ _ _ S a). Qed.


Program Definition Ring_of_InternalRing@{o so} {A : SetoidObject@{o o}}
  (R : @InternalRing Sets@{o so} _ _ A) : RingObject@{o o o} := {|
  ring_rig := Rig_of_InternalSemiring
                (@InternalRing_InternalSemiring Sets _ _ A R);
  ring_neg := fun a => (ir_neg : _ ~{Sets}~> _) a
|}.
Next Obligation. proper; now apply proper_morphism. Qed.
Next Obligation. exact (@ir_neg_left _ _ _ _ R a). Qed.

End SetsInternal.

Section SetsRoundTrip.

Context (R : RigObject).

Example rig_round_setoid :
  rig_setoid (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_setoid R := eq_refl.
Example rig_round_zero :
  rig_zero (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_zero R := eq_refl.
Example rig_round_add :
  rig_add (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_add R := eq_refl.
Example rig_round_one :
  rig_one (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_one R := eq_refl.
Example rig_round_mul :
  rig_mul (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_mul R := eq_refl.

Fail Example rig_round_record :
  (Rig_of_InternalSemiring (Sets_InternalSemiring R)) = R := eq_refl.

Context {A : SetoidObject}.
Context (S : @InternalSemiring Sets _ _ A).

Example semiring_round_add (a b : carrier A) :
  (mappend[@isr_add _ _ _ _
     (Sets_InternalSemiring (Rig_of_InternalSemiring S))] : _ ~{Sets}~> _)
    (a, b)
  = (mappend[@isr_add _ _ _ _ S] : _ ~{Sets}~> _) (a, b) := eq_refl.

Example semiring_round_zero :
  (mempty[@isr_add _ _ _ _
     (Sets_InternalSemiring (Rig_of_InternalSemiring S))] : _ ~{Sets}~> _) ttt
  = (mempty[@isr_add _ _ _ _ S] : _ ~{Sets}~> _) ttt := eq_refl.

Fail Example semiring_round_monoid :
  (@isr_add _ _ _ _ (Sets_InternalSemiring (Rig_of_InternalSemiring S)))
    = (@isr_add _ _ _ _ S) := eq_refl.

End SetsRoundTrip.

Section SetsWitness.

Definition Nat_ISemiring : @InternalSemiring Sets _ _ nat_setoid_object :=
  Sets_InternalSemiring Nat_Rig.

Definition Int_IRing : @InternalRing Sets _ _ (rig_setoid Int_Ring) :=
  Sets_InternalRing Int_Ring.

Example nat_zero_computes :
  (mempty[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt = 0%nat
  := eq_refl.
Example nat_one_computes :
  (mempty[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt = 1%nat
  := eq_refl.
Example nat_add_computes :
  (mappend[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) (2%nat, 3%nat)
    = 5%nat := eq_refl.
Example nat_mul_computes :
  (mappend[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) (2%nat, 3%nat)
    = 6%nat := eq_refl.

Lemma nat_semiring_nondegenerate :
  (mempty[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt
    <> (mempty[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Example int_neg_computes :
  (@ir_neg _ _ _ _ Int_IRing : _ ~{Sets}~> _) 7%Z = (-7)%Z := eq_refl.

Lemma int_ring_nondegenerate :
  (mempty[@ir_add _ _ _ _ Int_IRing] : _ ~{Sets}~> _) ttt
    <> (mempty[@ir_mul _ _ _ _ Int_IRing] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Definition int_annihilate_instance := @ring_annihilate_l Sets _ _ _ Int_IRing.

End SetsWitness.

Section LawsConstrain.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

(* [orb] on the two-element setoid is a commutative monoid with unit
   [false].  Used TWICE below, as both the additive and the multiplicative
   half, to show that annihilation is independent of the remaining
   [InternalSemiring] laws. *)
Program Definition Bool_Or_Monoid : @Monoid Sets _ _ bool_setoid_object :=
  Sets_Monoid bool_setoid_object false orb _ _ _ _.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Lemma bool_or_comm :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Or_Monoid].
Proof. intros [[|] [|]]; reflexivity. Qed.

Lemma bool_or_distrib_l :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ second (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Bool_Or_Monoid]
        ∘ dup_left.
Proof. intros [[|] [[|] [|]]]; reflexivity. Qed.

Lemma bool_or_distrib_r :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ first (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Bool_Or_Monoid]
        ∘ dup_right.
Proof. intros [[[|] [|]] [|]]; reflexivity. Qed.

Lemma bool_or_not_annihilating :
  ((mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ (((mempty[Bool_Or_Monoid] : 1 ~{Sets}~> _) ∘ one) △ id)
    ≈ (mempty[Bool_Or_Monoid] : 1 ~{Sets}~> _) ∘ one) → False.
Proof. intro Hx; specialize (Hx true); discriminate. Qed.

Definition Nat_Plus_Monoid : @Monoid Sets _ _ nat_setoid_object :=
  @isr_add _ _ _ _ Nat_ISemiring.

Lemma nat_plus_not_distributive :
  ((mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
      ∘ second (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Nat_Plus_Monoid]
        ∘ dup_left) → False.
Proof. intro Hx; specialize (Hx (1%nat, (0%nat, 0%nat))); discriminate. Qed.

End LawsConstrain.
