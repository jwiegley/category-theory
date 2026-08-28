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

Generalizable All Variables.

(** * Lattice objects in a cartesian category *)

(* Mac Lane, Categories for the Working Mathematician, 2nd ed., Section
   III.6, p. 75 (maclane:III.6:remark1); nLab:
   https://ncatlab.org/nlab/show/lattice
   https://ncatlab.org/nlab/show/internalization

   Section III.6 gives monoid and group objects by commuting diagrams and
   then observes that the same device internalizes ANY algebraic system
   presented by finitary operations and equational laws, naming rings and
   lattices as the next examples.  This file is the lattice half;
   Structure/Ring.v is the ring half, and its header carries the shared
   discussion of internalization and of the Lawvere-theory reading
   (Theory/Lawvere.v, Theory/Lawvere/Model.v's [Model] and [Models]) --
   which is a POINTER in both files and not a theorem: no bridge such as
   [MonoidObject ~= Models(Th_Mon)] is proved, and no Lawvere theory of
   lattices is constructed.

   A lattice needs the same two ambient ingredients a ring does.
   Absorption uses one variable twice, so the ambient category must copy;
   the units bottom and top are morphisms out of the terminal object, so it
   must discard.  Hence [Cartesian] + [Terminal], as in Structure/Group.v
   and Structure/Ring.v, rather than a bare [Monoidal].

   SCOPE OF THE NAME, and a forward reference this file OWNS.  Three open
   issues claim Structure/Lattice.v -- #340 (this one, Mac Lane III.6),
   #389 (Mac Lane IV.6: powerset lattices and Boolean algebras are
   cartesian closed) and #1003 (Riehl 5.5: lattices and semilattices as
   categories over Set).  Instance/Proset/Limit.v:101-109 records that
   claim explicitly and DELIBERATELY RESERVES the vocabulary: it "defines
   no [Meet], [Join], [Lattice] or [BooleanAlgebra] class and creates no
   such module", its [IsGLB] and [IsLUB] being "family-level PREDICATES
   over a bare [PreOrder], not an algebraic structure".  As the
   lowest-numbered issue, #340 defines the vocabulary; that reservation is
   cited here rather than restated.  But read the handover precisely: the
   note goes on to call its four constructors ([Proset_Cartesian],
   [Proset_Cocartesian], [Proset_Terminal], [Proset_Initial]) "exactly the
   interface such a class would later consume", and THIS FILE DOES NOT
   CONSUME THEM.  The classes below are internal-algebraic -- an object of
   an arbitrary cartesian category carrying two operations -- not
   order-theoretic, and the bridge between the two readings (a lattice
   object in [Sets] is a poset with all binary meets and joins) is listed
   below as not delivered.  A later effort wanting the order-theoretic
   reading will still have to build it.

   NAMING.  [InternalLattice] and [InternalSemilattice] follow
   Structure/Ring.v's [InternalRing] / [InternalSemiring]; that file
   explains why the [*Object] convention of [MonoidObject] and
   [GroupObject] could not be used (Theory/Algebra/Rig.v:469 already takes
   [RingObject] for the set-level notion).  All four names are free
   tree-wide, as are [SetoidLattice], [Sets_Monoid_on] and the witness
   names below.

   PRIOR ART.  Nothing in the tree carries two monoid structures on one
   object AS [Monoid]-TYPED FIELDS -- and that qualifier is the whole
   claim, an earlier revision having billed this as a search "by shape
   rather than by name" when it is a sweep by the field type's NAME.  By
   SHAPE the pattern DOES occur: Theory/Algebra/Rig.v:103's [RigObject]
   carries [(rig_zero, rig_add)] and [(rig_one, rig_mul)] on one setoid
   carrier, elementwise rather than as internal monoid objects.
   [GroupObject] (Structure/Group.v)
   is the only record anywhere with a [MonoidObject] field, and the only
   records with a field of the sibling class [Monoid] of
   Theory/Algebra/Monoid.v are Theory/Algebra/CommutativeMonoid.v:49 and
   Theory/Algebra/Frobenius.v:128, each carrying exactly one -- the latter
   pairs its monoid with a COMONOID, which is a different variance and
   carries no absorption.  (This file's [Monoid] is Structure/Monoid.v's
   [@MonoidObject C CC_Monoidal], not the identically named class of
   Theory/Algebra/Monoid.v.)  The only absorption-like
   law in tree is the zero-morphism absorption of
   Structure/Kernel/Universal.v's [ZeroMorphisms], which is about zero
   morphisms and not about two binary operations.  Existing meet/join
   vocabulary is order-theoretic and unrelated to this file's classes:
   Instance/Proset/Limit.v's [IsGLB]/[IsLUB]/[HasAllMeets]/[HasAllJoins],
   Instance/Proset/Order.v's [tmeet]/[tjoin] for total orders, and
   Instance/Two/Monoidal.v:34's [two_meet] on the walking arrow's objects.
   (Instance/FinSet.v:173's [fin_join] and
   Instance/Ab/DirectedColimit.v:488's [fg_join] are a coproduct decoder
   and a subgroup join; neither is lattice vocabulary.)

   WHAT IS DELIVERED, and at what strength.

   (1) [InternalSemilattice x]: a [Monoid] on x that is commutative and
       idempotent.  Idempotence is a FIELD here and must be:
       [bool_xor_not_idempotent] exhibits a commutative monoid object in
       [Sets] -- exclusive-or on the two-element setoid -- that refutes
       it, so it does not follow from the monoid laws plus commutativity.

   (2) [InternalLattice x]: a join [Monoid] and a meet [Monoid] on x, both
       commutative, plus the two absorption laws.  This is the BOUNDED
       lattice: the two monoid units are the bottom and top elements.
       Idempotence is NOT a field.

   (3) Idempotence of both operations is DERIVED from absorption alone
       ([lattice_join_idem], [lattice_meet_idem]) -- neither proof uses a
       unit, a unitor or commutativity, only the two absorption laws and
       the fork calculus.  Each half is then packaged as an
       [InternalSemilattice] ([InternalLattice_join_Semilattice],
       [InternalLattice_meet_Semilattice]).

   (4) The bounds annihilate: [lattice_bot_meet] (bottom meet a is bottom)
       and [lattice_top_join] (top join a is top), each from absorption
       plus the OTHER operation's unit law.  This is the exact parallel of
       Structure/Ring.v's derived [ring_annihilate_l]/[ring_annihilate_r],
       and the parallel is the point: in both files annihilation is a
       theorem rather than an axiom, and in both files the extra structure
       that makes it derivable (additive inverses there, absorption here)
       is what does the work.

   (5) The [Sets] instances.  [SetoidLattice] is the set-level bounded
       lattice on a setoid carrier -- declared HERE, which is off-pattern
       (set-level algebra normally lives under Theory/Algebra/, as
       Theory/Algebra/Rig.v does), because this effort may create only two
       files; a later move is a rename away.  [Sets_InternalLattice] and
       [SetoidLattice_of_InternalLattice] are the two passages.  Round
       trips are measured STRICT-FIRST: all five DATA fields return by
       [eq_refl] ([lat_round_setoid], [lat_round_bot], [lat_round_join],
       [lat_round_top], [lat_round_meet]) while the WHOLE RECORD does not,
       pinned as a [Fail]; on the internal side the unit and the operation
       agree at [eq_refl] on VALUES ([ilattice_round_bot],
       [ilattice_round_join]) while the [Monoid] record does not, also
       pinned.  Both [Fail]s were stripped and confirmed to be genuine
       CONVERSION failures ("cannot unify").  [SetoidLattice] also
       records idempotence as a corollary of absorption
       ([sl_join_idem], [sl_meet_idem]), mirroring (3) at the set level.

   ENGINEERING FINDING, shared with Structure/Ring.v and repeated because
   it shapes every statement below.  At [CC_Monoidal] the tensor IS the
   product -- [bimap f g = split f g] and [to unit_left = exr] hold by
   [eq_refl], recorded as the two [Example]s opening the file -- but
   [mappend]'s type is [mon (x) mon ~> mon], i.e.
   [fobj tensor (mon, mon) ~> mon], only CONVERTIBLE with [mon x mon].  Two
   separately elaborated occurrences of [mappend[M] o swap] then record
   different object arguments in their [compose] nodes and [rewrite]
   cannot match one against the other.  Every [mappend] and [mempty] below
   is therefore ascribed, [(mappend[M] : x x x ~> x)] and
   [(mempty[M] : 1 ~> x)], which forces a single syntactic form.
   [Sets_Monoid_on] is the same helper Structure/Ring.v calls
   [Sets_Monoid]; it is duplicated rather than imported so that neither
   Section III.6 file depends on the other, and the name is kept distinct
   so that importing both files is unambiguous.  [bool_setoid_obj] below
   is a SECOND, undeclared duplication of the same kind: it re-declares
   the two-element setoid this file already imports as
   Instance/Sets.v:563's [bool_setoid_object], with which it agrees by
   [eq_refl].  It is kept only so the witness block reads self-contained,
   and it is recorded here rather than left for a reader to discover.

   UNIVERSES, measured in the constraint blocks AND in the binders.
   [InternalSemilattice@{u u0 u1}] and [InternalLattice@{u u0 u1}] are over
   [Category@{u u0 u0}]: hom and proof universes IDENTIFIED, OBJECT
   universe FREE (it occurs only in [<=] bounds).  The identification is
   the DONORS' doing and THREE force it INDEPENDENTLY -- with the levels
   declared apart under [Constraint uh < up] a control naming a hom at
   those levels is accepted while each of [@Cartesian C], [@Terminal C]
   and [@Monoidal C] is rejected with "Cannot enforce up = uh".
   [MonoidObject] is NOT a fourth donor: [@Monoidal C] appears in its own
   signature and is rejected first, so it cannot be probed apart, and
   whether it identifies anything OF ITS OWN is UNKNOWN.
   Nothing here adds to it and it is NOT claimed unavoidable.  The derived
   results inherit exactly that and add nothing:
   [lattice_join_idem@{u u0 u1}] and [lattice_bot_meet@{u u0 u1}] have the
   same block as the class.  On the [Sets] side [Sets_InternalLattice] and
   [SetoidLattice_of_InternalLattice] carry [o < so] as their only STRICT
   constraint and no [Set] anywhere; the rest of each block is some
   fifteen [<=] bounds against donor universes ([projections],
   [prod_rect], [Basics.compose], [eq_ind]), some relating two DECLARED
   binders, so "nothing else" would be wrong even read charitably.  The
   [Set]-freedom holds only because the universe binders are written
   out; unannotated, [Sets_Monoid_on] minimizes to
   [SetoidObject@{Set Set}], which would have confined every [Sets] result
   to Set-sized carriers.  Same minimization hazard as
   Instance/Sets/Products.v:409-424 and the #300 erratum.

   NON-VACUITY, proved rather than gestured at.  [Bool_Lattice] is the
   two-element bounded lattice (disjunction with bottom [false],
   conjunction with top [true]) and [Bool_ILattice] its image in [Sets];
   bottom, top, join and meet all COMPUTE by [eq_refl], and
   [bool_lattice_nondegenerate] proves bottom and top distinct, so the
   structure is not collapsed.  [Bool_Semilattice] instantiates
   [InternalSemilattice].  That the laws genuinely CONSTRAIN is proved
   twice: [bool_join_not_absorbing] takes the join monoid of that very
   lattice as BOTH halves -- two commutative monoid objects on one carrier
   ([bool_join_comm]) -- and refutes absorption, so the absorption fields are
   not automatic; and [bool_xor_not_idempotent] refutes idempotence for the
   commutative monoid object [Bool_Xor_Monoid], which is why (1) carries it
   as a field.

   WHAT IS NOT DELIVERED.
   - No unbounded lattice.  [InternalLattice] is bounded because it is
     built from two [Monoid] objects, and the tree has no semigroup-object
     notion to build the unit-free variant on; none is introduced here.
   - No distributive lattices, no complements, no Heyting or Boolean
     algebras, and no cartesian-closed structure on a lattice: that is
     #389's Mac Lane Section IV.6 item, and nothing here anticipates it.
   - No order-theoretic reading.  The relation "a <= b iff a meet b = a" is
     not defined, no partial order is extracted, and
     Instance/Proset/Limit.v's [IsGLB]/[IsLUB]/[Proset_Cartesian] are NOT
     consumed -- so the bridge between this algebraic vocabulary and that
     order-theoretic one remains open, as does #1003's reading of
     lattices as categories.
   - No category of internal lattices, no lattice homomorphisms, no
     forgetful functor, and hence no equivalence packaging the [Sets]
     round trips.
   - No instance in any ambient category other than [Sets].  In particular
     no powerset lattice (Instance/Sets/Powerset.v is not required) and no
     lattice of opens from Instance/Top.v, so "the opens of a space form a
     lattice object" stays prose.
   - No closure results: products and exponentials of lattice objects are
     not shown to be lattice objects (Structure/Monoid.v proves the monoid
     analogues [Product_Monoid] and [Hom_Monoid]; neither is lifted).
   - No duality: that a lattice object in C is one in C read with meet and
     join exchanged is not stated, and neither is the self-duality of the
     axioms.
   - No modularity, no Birkhoff-style representation, no completeness. *)

Section Internalize.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Example lat_bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example lat_unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Class InternalSemilattice (x : C) := {
  isl_mon : Monoid x;

  isl_comm : (mappend[isl_mon] : x × x ~> x) ∘ swap ≈ mappend[isl_mon];
  isl_idem : (mappend[isl_mon] : x × x ~> x) ∘ (id △ id) ≈ id
}.

Class InternalLattice (x : C) := {
  il_join : Monoid x;
  il_meet : Monoid x;

  il_join_comm : (mappend[il_join] : x × x ~> x) ∘ swap ≈ mappend[il_join];
  il_meet_comm : (mappend[il_meet] : x × x ~> x) ∘ swap ≈ mappend[il_meet];

  il_absorb_meet :
    (mappend[il_meet] : x × x ~> x)
      ∘ (exl △ (mappend[il_join] : x × x ~> x)) ≈ exl;
  il_absorb_join :
    (mappend[il_join] : x × x ~> x)
      ∘ (exl △ (mappend[il_meet] : x × x ~> x)) ≈ exl
}.

End Internalize.

Section LatticeDerived.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context {x : C}.
Context `{L : @InternalLattice C _ _ x}.

Lemma lattice_join_idem :
  (mappend[il_join] : x × x ~> x) ∘ (id △ id) ≈ id.
Proof.
  assert (HI : (mappend[il_meet] : x × x ~> x)
                 ∘ (id △ ((mappend[il_join] : x × x ~> x) ∘ (id △ id)))
               ≈ id).
  { transitivity ((mappend[il_meet] : x × x ~> x)
                    ∘ (exl △ (mappend[il_join] : x × x ~> x))
                    ∘ (id △ id)).
    { rewrite <- comp_assoc, <- fork_comp.
      now rewrite exl_fork. }
    rewrite il_absorb_meet.
    now rewrite exl_fork. }
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                  ∘ (id △ ((mappend[il_join] : x × x ~> x) ∘ (id △ id)))).
  { rewrite <- comp_assoc, <- fork_comp, exl_fork.
    now rewrite HI. }
  rewrite il_absorb_join.
  now rewrite exl_fork.
Qed.

Lemma lattice_meet_idem :
  (mappend[il_meet] : x × x ~> x) ∘ (id △ id) ≈ id.
Proof.
  assert (HI : (mappend[il_join] : x × x ~> x)
                 ∘ (id △ ((mappend[il_meet] : x × x ~> x) ∘ (id △ id)))
               ≈ id).
  { transitivity ((mappend[il_join] : x × x ~> x)
                    ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                    ∘ (id △ id)).
    { rewrite <- comp_assoc, <- fork_comp.
      now rewrite exl_fork. }
    rewrite il_absorb_join.
    now rewrite exl_fork. }
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ (exl △ (mappend[il_join] : x × x ~> x))
                  ∘ (id △ ((mappend[il_meet] : x × x ~> x) ∘ (id △ id)))).
  { rewrite <- comp_assoc, <- fork_comp, exl_fork.
    now rewrite HI. }
  rewrite il_absorb_meet.
  now rewrite exl_fork.
Qed.

Lemma lattice_join_bot_left {w : C} (g : w ~> x) :
  (mappend[il_join] : x × x ~> x)
      ∘ (((mempty[il_join] : 1 ~> x) ∘ one[w]) △ g) ≈ g.
Proof.
  assert (Hu : (mappend[il_join] : x × x ~> x)
                 ∘ split (mempty[il_join] : 1 ~> x) id ≈ exr)
    by exact (@mempty_left _ _ _ il_join).
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ split (mempty[il_join] : 1 ~> x) id ∘ (one[w] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite Hu.
  now rewrite exr_fork.
Qed.

Lemma lattice_meet_top_left {w : C} (g : w ~> x) :
  (mappend[il_meet] : x × x ~> x)
      ∘ (((mempty[il_meet] : 1 ~> x) ∘ one[w]) △ g) ≈ g.
Proof.
  assert (Hu : (mappend[il_meet] : x × x ~> x)
                 ∘ split (mempty[il_meet] : 1 ~> x) id ≈ exr)
    by exact (@mempty_left _ _ _ il_meet).
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ split (mempty[il_meet] : 1 ~> x) id ∘ (one[w] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite Hu.
  now rewrite exr_fork.
Qed.

(* The bottom element annihilates the meet: it is NOT a field, but a
   consequence of absorption together with the join unit law. *)
Lemma lattice_bot_meet :
  (mappend[il_meet] : x × x ~> x)
      ∘ (((mempty[il_join] : 1 ~> x) ∘ one) △ id)
    ≈ (mempty[il_join] : 1 ~> x) ∘ one.
Proof.
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x]))
                       △ ((mappend[il_meet] : x × x ~> x)
                            ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x]))
                                 △ id)))).
  { now rewrite lattice_join_bot_left. }
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                  ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x])) △ id)).
  { rewrite <- comp_assoc, <- fork_comp.
    now rewrite exl_fork. }
  rewrite il_absorb_join.
  now rewrite exl_fork.
Qed.

(* Dually, the top element annihilates the join. *)
Lemma lattice_top_join :
  (mappend[il_join] : x × x ~> x)
      ∘ (((mempty[il_meet] : 1 ~> x) ∘ one) △ id)
    ≈ (mempty[il_meet] : 1 ~> x) ∘ one.
Proof.
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x]))
                       △ ((mappend[il_join] : x × x ~> x)
                            ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x]))
                                 △ id)))).
  { now rewrite lattice_meet_top_left. }
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ (exl △ (mappend[il_join] : x × x ~> x))
                  ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x])) △ id)).
  { rewrite <- comp_assoc, <- fork_comp.
    now rewrite exl_fork. }
  rewrite il_absorb_meet.
  now rewrite exl_fork.
Qed.

Program Definition InternalLattice_join_Semilattice :
  @InternalSemilattice C _ _ x := {| isl_mon := il_join |}.
Next Obligation. exact il_join_comm. Qed.
Next Obligation. exact lattice_join_idem. Qed.

Program Definition InternalLattice_meet_Semilattice :
  @InternalSemilattice C _ _ x := {| isl_mon := il_meet |}.
Next Obligation. exact il_meet_comm. Qed.
Next Obligation. exact lattice_meet_idem. Qed.

End LatticeDerived.

Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

(** ** Bounded lattices on a setoid carrier *)

Record SetoidLattice := {
  sl_setoid :> SetoidObject;

  sl_bot  : carrier sl_setoid;
  sl_join : carrier sl_setoid → carrier sl_setoid → carrier sl_setoid;
  sl_top  : carrier sl_setoid;
  sl_meet : carrier sl_setoid → carrier sl_setoid → carrier sl_setoid;

  sl_join_respects : Proper (equiv ==> equiv ==> equiv) sl_join;
  sl_meet_respects : Proper (equiv ==> equiv ==> equiv) sl_meet;

  sl_join_assoc : ∀ a b c,
    sl_join (sl_join a b) c ≈ sl_join a (sl_join b c);
  sl_join_comm : ∀ a b, sl_join a b ≈ sl_join b a;
  sl_join_bot_l : ∀ a, sl_join sl_bot a ≈ a;

  sl_meet_assoc : ∀ a b c,
    sl_meet (sl_meet a b) c ≈ sl_meet a (sl_meet b c);
  sl_meet_comm : ∀ a b, sl_meet a b ≈ sl_meet b a;
  sl_meet_top_l : ∀ a, sl_meet sl_top a ≈ a;

  sl_absorb_meet : ∀ a b, sl_meet a (sl_join a b) ≈ a;
  sl_absorb_join : ∀ a b, sl_join a (sl_meet a b) ≈ a
}.

#[export] Existing Instance sl_join_respects.
#[export] Existing Instance sl_meet_respects.

Corollary sl_join_bot_r (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_join L a (sl_bot L) ≈ a.
Proof. rewrite sl_join_comm; apply sl_join_bot_l. Qed.

Corollary sl_meet_top_r (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_meet L a (sl_top L) ≈ a.
Proof. rewrite sl_meet_comm; apply sl_meet_top_l. Qed.

(* Idempotence is derived from the two absorption laws alone -- the
   set-level shadow of [lattice_join_idem] / [lattice_meet_idem]. *)
Corollary sl_join_idem (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_join L a a ≈ a.
Proof.
  rewrite <- (sl_absorb_meet L a (sl_join L a a)) at 2.
  now rewrite sl_absorb_join.
Qed.

Corollary sl_meet_idem (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_meet L a a ≈ a.
Proof.
  rewrite <- (sl_absorb_join L a (sl_meet L a a)) at 2.
  now rewrite sl_absorb_meet.
Qed.

Section SetsInternal.

(* The same helper Structure/Ring.v names [Sets_Monoid].  It is duplicated
   rather than imported so that neither Section III.6 file depends on the
   other, and the name is kept distinct so that importing both is
   unambiguous. *)
Program Definition Sets_Monoid_on@{o so p} (A : SetoidObject@{o o})
  (u : carrier A) (op : carrier A → carrier A → carrier A)
  (opP : Proper@{o p} (equiv ==> equiv ==> equiv) op)
  (op_assoc : ∀ a b c, op (op a b) c ≈ op a (op b c))
  (unit_l : ∀ a, op u a ≈ a)
  (unit_r : ∀ a, op a u ≈ a) : @Monoid Sets@{o so} _ _ A := {|
  mempty := {| morphism := fun _ => u |};
  mappend := {| morphism := fun p => op (fst p) (snd p) |}
|}.
Next Obligation. proper; simpl in *; now apply opP. Qed.

Program Definition Sets_InternalLattice@{o so q} (L : SetoidLattice@{o o q}) :
  @InternalLattice Sets@{o so} _ _ (sl_setoid L) := {|
  il_join := Sets_Monoid_on (sl_setoid L) (sl_bot L) (sl_join L)
               (sl_join_respects L) (sl_join_assoc L) (sl_join_bot_l L)
               (sl_join_bot_r L);
  il_meet := Sets_Monoid_on (sl_setoid L) (sl_top L) (sl_meet L)
               (sl_meet_respects L) (sl_meet_assoc L) (sl_meet_top_l L)
               (sl_meet_top_r L)
|}.
Next Obligation. now rewrite sl_join_comm. Qed.
Next Obligation. now rewrite sl_meet_comm. Qed.
Next Obligation. now rewrite sl_absorb_meet. Qed.
Next Obligation. now rewrite sl_absorb_join. Qed.

Program Definition SetoidLattice_of_InternalLattice@{o so}
  {A : SetoidObject@{o o}} (L : @InternalLattice Sets@{o so} _ _ A) :
  SetoidLattice@{o o o} := {|
  sl_setoid := A;
  sl_bot  := (mempty[il_join] : _ ~{Sets}~> _) ttt;
  sl_join := fun a b => (mappend[il_join] : _ ~{Sets}~> _) (a, b);
  sl_top  := (mempty[il_meet] : _ ~{Sets}~> _) ttt;
  sl_meet := fun a b => (mappend[il_meet] : _ ~{Sets}~> _) (a, b)
|}.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation.
  exact (@mappend_assoc _ _ _ (@il_join _ _ _ _ L) ((a, b), c)).
Qed.
Next Obligation. exact (@il_join_comm _ _ _ _ L (b, a)). Qed.
Next Obligation. exact (@mempty_left _ _ _ (@il_join _ _ _ _ L) (ttt, a)). Qed.
Next Obligation.
  exact (@mappend_assoc _ _ _ (@il_meet _ _ _ _ L) ((a, b), c)).
Qed.
Next Obligation. exact (@il_meet_comm _ _ _ _ L (b, a)). Qed.
Next Obligation. exact (@mempty_left _ _ _ (@il_meet _ _ _ _ L) (ttt, a)). Qed.
Next Obligation. exact (@il_absorb_meet _ _ _ _ L (a, b)). Qed.
Next Obligation. exact (@il_absorb_join _ _ _ _ L (a, b)). Qed.

End SetsInternal.

Section SetsRoundTrip.

Context (L : SetoidLattice).

Example lat_round_setoid :
  sl_setoid (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_setoid L := eq_refl.
Example lat_round_bot :
  sl_bot (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_bot L := eq_refl.
Example lat_round_join :
  sl_join (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_join L := eq_refl.
Example lat_round_top :
  sl_top (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_top L := eq_refl.
Example lat_round_meet :
  sl_meet (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_meet L := eq_refl.

Fail Example lat_round_record :
  (SetoidLattice_of_InternalLattice (Sets_InternalLattice L)) = L := eq_refl.

Context {A : SetoidObject}.
Context (K : @InternalLattice Sets _ _ A).

Example ilattice_round_join (a b : carrier A) :
  (mappend[@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K))]
     : _ ~{Sets}~> _) (a, b)
  = (mappend[@il_join _ _ _ _ K] : _ ~{Sets}~> _) (a, b) := eq_refl.

Example ilattice_round_bot :
  (mempty[@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K))]
     : _ ~{Sets}~> _) ttt
  = (mempty[@il_join _ _ _ _ K] : _ ~{Sets}~> _) ttt := eq_refl.

Fail Example ilattice_round_monoid :
  (@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K)))
    = (@il_join _ _ _ _ K) := eq_refl.

End SetsRoundTrip.

Section BoolWitness.

Definition bool_setoid_obj : SetoidObject := {|
  carrier := bool;
  is_setoid := {| equiv := @eq bool; setoid_equiv := eq_equivalence |}
|}.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

Program Definition Bool_Lattice : SetoidLattice := {|
  sl_setoid := bool_setoid_obj;
  sl_bot  := false;
  sl_join := orb;
  sl_top  := true;
  sl_meet := andb
|}.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Definition Bool_ILattice : @InternalLattice Sets _ _ bool_setoid_obj :=
  Sets_InternalLattice Bool_Lattice.

Example bool_bot_computes :
  (mempty[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt = false
  := eq_refl.
Example bool_top_computes :
  (mempty[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt = true
  := eq_refl.
Example bool_join_computes :
  (mappend[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) (false, true)
    = true := eq_refl.
Example bool_meet_computes :
  (mappend[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) (false, true)
    = false := eq_refl.

Lemma bool_lattice_nondegenerate :
  (mempty[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt
    <> (mempty[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Definition Bool_Semilattice : @InternalSemilattice Sets _ _ bool_setoid_obj :=
  @InternalLattice_join_Semilattice Sets _ _ _ Bool_ILattice.

End BoolWitness.

Section LawsConstrain.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

Definition Bool_Join_Monoid : @Monoid Sets _ _ bool_setoid_obj :=
  @il_join _ _ _ _ Bool_ILattice.

Lemma bool_join_comm :
  (mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Join_Monoid].
Proof. exact (@il_join_comm _ _ _ _ Bool_ILattice). Qed.

Lemma bool_join_not_absorbing :
  ((mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _)
      ∘ (exl △ (mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _)) ≈ exl) → False.
Proof. intro Hx; specialize (Hx (false, true)); discriminate. Qed.

Program Definition Bool_Xor_Monoid : @Monoid Sets _ _ bool_setoid_obj :=
  Sets_Monoid_on bool_setoid_obj false xorb _ _ _ _.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Lemma bool_xor_comm :
  (mappend[Bool_Xor_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Xor_Monoid].
Proof. intros [[|] [|]]; reflexivity. Qed.

Lemma bool_xor_not_idempotent :
  ((mappend[Bool_Xor_Monoid] : _ × _ ~{Sets}~> _) ∘ (id △ id) ≈ id) → False.
Proof. intro Hx; specialize (Hx true); discriminate. Qed.

End LawsConstrain.
