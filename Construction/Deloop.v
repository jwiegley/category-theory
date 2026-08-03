Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Delooping: monoids as one-object categories *)

(* nLab:      https://ncatlab.org/nlab/show/delooping
   nLab:      https://ncatlab.org/nlab/show/monoid
   nLab:      https://ncatlab.org/nlab/show/groupoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §I.2, printed p. 11 (constructions 3 and 4)
   Book:      Awodey, "Category Theory", 2nd ed., §1.4, pp. 12-13
   Book:      Riehl, "Category Theory in Context", Example 1.1.4(ii), pp. 5-6
   Book:      Fong, Spivak, "Seven Sketches in Compositionality", CUP 2019,
              §3.2.1 Example 3.13, printed p. 83

   A monoid is exactly a category with one object.  Mac Lane's third
   construction in §I.2 takes a monoid M to the category [Deloop M] whose sole
   object is a formal point, whose arrows are the elements of M, whose
   composition is the multiplication of M, and whose identity arrow is the unit
   of M; the category laws then read off verbatim as the monoid laws.  His
   fourth construction specializes to groups: when every element has a
   two-sided inverse, every arrow of the one-object category is invertible, so
   the category is a one-object groupoid.  Conversely — the direction Awodey
   and Fong-Spivak both make explicit — for any category C and any object a,
   the endomorphism hom `a ~> a` is a monoid under composition with unit [id].
   This file provides all three, plus the statement that the two constructions
   are mutually inverse in the direction where that can be said on the nose
   ([hom_monoid_Deloop], which holds by [eq_refl]).

   Contents:

       MonObject                 a monoid (carrier setoid, unit, operation)
       Deloop M                  the one-object category B M
       hom_monoid C a            the endomorphism monoid of a in C
       hom_monoid_Deloop         hom_monoid (Deloop M) ttt = M, by eq_refl
       GrpObject                 a monoid with a two-sided inverse operation
       Deloop_group_invertible   every arrow of B G is an isomorphism
       Nat_Plus, Bool_Xor_Grp    inhabitation witnesses for the two records

   The functor-level half of the dictionary — that functors between deloopings
   are exactly monoid homomorphisms, so that a functor `B G ⟶ Vect` is a linear
   representation of G — is deliberately not built here; it belongs with the
   Mac Lane §I.3 material. *)

(* Why "delooping", and what the one-object reading buys

   The name is topological.  Per the nLab (delooping), a delooping of an
   object X is an object B X whose loop space object is X again, so that
   passing from a group G to the one-object groupoid B G (equivalently, to
   its classifying space BG) inverts the formation of loops; the notation
   B is Riehl's and is standard.  The categorical content is Mac Lane's
   observation that the axioms match: associativity of composition is
   associativity of the operation, the two unit laws of a category are the
   two unit laws of a monoid, and the single object carries no information
   whatever.  Fong and Spivak put the equivalence in exactly this form —
   a category with one object *is* a monoid, taking the hom-set at that
   object as the carrier — and it is the reason both directions belong in
   one file rather than sitting apart as unrelated constructions.

   What the reading buys is that everything defined for categories
   immediately specializes to monoids.  The opposite category of a
   delooping is the delooping of the opposite monoid (Riehl, Example
   1.2.2(iii), the device by which right actions are presented as left
   actions); the idempotent-splitting completion of a delooped monoid is
   the category whose objects are the idempotents of the monoid
   (Construction/Karoubi.v); a functor out of a delooping is an action,
   which for groups in Vect is a linear representation.  In the other
   direction, the endomorphism monoid [hom_monoid] is how a category
   sees a single object in isolation, and it is the local invariant that
   Theory/Isomorphism.v's [IsIsomorphism] tests for invertibility of.

   Relationship to what is already in the tree.  [Instance/CMon.v]'s
   [CMonObject] is the *commutative* version of [MonObject] below, in the
   same setoid shape and with the same [Proper] field, and is used for the
   preadditive/biproduct development; it derives its right unit law from
   commutativity, whereas a bare monoid must carry both unit laws as data.
   [Theory/Algebra/Monoid.v] defines a monoid *object* internal to a
   monoidal category, which is the correct notion in general but drags a
   monoidal structure into a construction that needs nothing of the kind;
   the same holds for [Structure/Group.v]'s [GroupObject], an internal
   group object in a cartesian monoidal category, which is why [GrpObject]
   below is a small extension record instead.  [Theory/Bicategory/OneObject.v]
   is the same delooping one level up: it presents a monoidal category as a
   one-object *bicategory*, with the elements-as-arrows dictionary shifted
   from (object, arrow) to (arrow, 2-cell).  Finally
   [Construction/Funny/Comparison.v]'s [ListMon] is the ad-hoc delooping of
   the free monoid on [bool], written for a single counterexample; it is
   [Deloop] applied to one particular monoid, spelled out by hand. *)

(* A monoid: a setoid with a distinguished unit and an associative binary
   operation respecting `≈`, for which the unit is neutral on both sides.
   This is [Instance/CMon.v]'s [CMonObject] minus commutativity, hence with
   the right unit law promoted from a corollary to a field.

   ASSOCIATIVITY ORIENTATION.  The field is stated as

       a * (b * c) ≈ (a * b) * c

   rather than in the more usual left-to-right reading, because that is
   verbatim the orientation of [comp_assoc] in Theory/Category.v.  Delooping
   then supplies the category law by projection instead of by [symmetry], and
   — since [Set Primitive Projections] gives definitional eta for records —
   the round trip [hom_monoid_Deloop] below closes by [eq_refl] rather than
   only up to `≈`.  [mon_op_assoc_sym] restates the law in the other
   orientation for consumers who want it, exactly as [comp_assoc_sym] does
   for categories. *)
Record MonObject := {
  mon_setoid :> SetoidObject;

  mon_unit : carrier mon_setoid;
  mon_op : carrier mon_setoid → carrier mon_setoid → carrier mon_setoid;

  mon_op_respects : Proper (equiv ==> equiv ==> equiv) mon_op;

  mon_op_assoc : ∀ a b c,
    mon_op a (mon_op b c) ≈ mon_op (mon_op a b) c;
  mon_op_unit_l : ∀ a, mon_op mon_unit a ≈ a;
  mon_op_unit_r : ∀ a, mon_op a mon_unit ≈ a
}.

#[export] Existing Instance mon_op_respects.

Arguments mon_unit {_}.
Arguments mon_op {_} _ _.
Arguments mon_op_assoc {_} _ _ _.
Arguments mon_op_unit_l {_} _.
Arguments mon_op_unit_r {_} _.

(* Associativity in the mirrored orientation, the analogue of
   [comp_assoc_sym]. *)
Corollary mon_op_assoc_sym (M : MonObject) (a b c : carrier M) :
  mon_op (mon_op a b) c ≈ mon_op a (mon_op b c).
Proof.
  symmetry.
  apply mon_op_assoc.
Qed.

(* Inverses in a monoid are unique when they exist: if b is a left inverse of
   a and c is a right inverse of a, then b ≈ c, by the classical computation
   b ≈ b * 1 ≈ b * (a * c) ≈ (b * a) * c ≈ 1 * c ≈ c.  This is what makes the
   inverse operation of [GrpObject] below respect `≈` without carrying a
   [Proper] field of its own. *)
Lemma mon_inverse_unique (M : MonObject) (a b c : carrier M) :
  mon_op b a ≈ mon_unit → mon_op a c ≈ mon_unit → b ≈ c.
Proof.
  intros Hba Hac.
  rewrite <- (mon_op_unit_r b).
  rewrite <- Hac.
  rewrite (mon_op_assoc b a c).
  rewrite Hba.
  apply mon_op_unit_l.
Qed.

(** ** Mac Lane's construction 3: the one-object category B M *)

(* The delooping of a monoid M: one object, the elements of M as its arrows,
   multiplication as composition and the unit as the identity.  Every category
   law is a monoid law by projection, so no obligation is generated.

   Mac Lane and Riehl write [B M] for this category; the name here is
   [Deloop], which keeps the single letter B free as an ordinary variable
   throughout the development.

   COMPOSITION ORDER.  `f ∘ g` in this library means "g first, then f"
   (Theory/Category.v: `compose : (y ~> z) → (x ~> y) → (x ~> z)`), and the
   delooping takes `compose f g := mon_op f g`, i.e. the monoid product in the
   same argument order.  So an element of M read as an arrow multiplies on the
   left exactly as it composes on the left; no opposite monoid is introduced.
   (Riehl's Example 1.2.2(iii) — that `(B G)^op` is `B (G^op)` — is the
   statement that the *other* choice deloops the opposite monoid.)

   The sole object is [ttt : poly_unit] rather than [tt : unit], following
   Instance/One.v and Construction/Funny/Comparison.v: [poly_unit] is
   universe-polymorphic, so the object universe of [Deloop M] stays free
   instead of being pinned at [Set]. *)
Definition Deloop (M : MonObject) : Category := {|
  obj     := poly_unit;                        (* the single object *)
  hom     := fun _ _ => carrier M;             (* arrows are elements of M *)
  homset  := fun _ _ => is_setoid M;           (* `≈` is the carrier's own *)
  id      := fun _ => mon_unit;                (* identity is the unit *)
  compose := fun _ _ _ f g => mon_op f g;      (* composition is the product *)

  compose_respects := fun _ _ _ => mon_op_respects M;

  id_left  := fun _ _ => mon_op_unit_l;
  id_right := fun _ _ => mon_op_unit_r;

  comp_assoc     := fun _ _ _ _ => mon_op_assoc;
  comp_assoc_sym := fun _ _ _ _ => mon_op_assoc_sym M
|}.

(** ** The converse: the endomorphism monoid hom(a, a) *)

(* For any category C and object a, the hom-setoid `a ~> a` is a monoid under
   composition, with the identity arrow as unit.  Again every monoid law is a
   category law by projection: [compose_respects], [comp_assoc], [id_left] and
   [id_right] are precisely the four fields required. *)
Definition hom_monoid (C : Category) (a : C) : MonObject := {|
  mon_setoid := {| carrier := a ~> a; is_setoid := @homset C a a |};

  mon_unit := id;
  mon_op   := fun f g => f ∘ g;

  mon_op_respects := @compose_respects C a a a;

  mon_op_assoc  := fun f g h => comp_assoc f g h;
  mon_op_unit_l := @id_left C a a;
  mon_op_unit_r := @id_right C a a
|}.

(** ** The correspondence, on the nose *)

(* Delooping and taking endomorphisms are mutually inverse in the sense that
   can be stated as an equation: the endomorphism monoid of the single object
   of [Deloop M] is M itself, on the nose.  Both the data (carrier, unit,
   operation) and the law fields agree definitionally — the laws because
   [Deloop] took them from M by projection, in the orientation M states them
   in; the records because [Set Primitive Projections] gives eta.

   The opposite composite has no equational form to prove: [Deloop
   (hom_monoid C a)] is a one-object category, whereas C in general has many
   objects, and the honest statement — that it is the full subcategory of C
   on {a} — is a functor-level claim, belonging with the deferred §I.3
   dictionary. *)
Example hom_monoid_Deloop (M : MonObject) : hom_monoid (Deloop M) ttt = M :=
  eq_refl.

(* The three data fields separately, for readers who want to see which parts
   of the round trip are definitional without unfolding the record equation. *)
Example hom_monoid_Deloop_carrier (M : MonObject) :
  carrier (hom_monoid (Deloop M) ttt) = carrier M := eq_refl.

Example hom_monoid_Deloop_unit (M : MonObject) :
  @mon_unit (hom_monoid (Deloop M) ttt) = @mon_unit M := eq_refl.

Example hom_monoid_Deloop_op (M : MonObject) :
  @mon_op (hom_monoid (Deloop M) ttt) = @mon_op M := eq_refl.

(** ** Mac Lane's construction 4: the group case *)

(* A group, as a small extension of [MonObject] by a two-sided inverse
   operation.  As with [MonObject], this is a bare record rather than
   [Structure/Group.v]'s [GroupObject] (a group object internal to a cartesian
   monoidal category): the delooping needs the inverse of an *element*, and
   nothing about the ambient category the group might be internal to.

   [grp_inv] carries no [Proper] field: respecting `≈` is derivable from
   uniqueness of inverses, and is supplied as the instance
   [grp_inv_respects] below. *)
Record GrpObject := {
  grp_monoid :> MonObject;

  grp_inv : carrier grp_monoid → carrier grp_monoid;

  grp_inv_l : ∀ a, mon_op (grp_inv a) a ≈ mon_unit;
  grp_inv_r : ∀ a, mon_op a (grp_inv a) ≈ mon_unit
}.

Arguments grp_inv {_} _.
Arguments grp_inv_l {_} _.
Arguments grp_inv_r {_} _.

(* Inversion respects `≈`.  If a ≈ b then the inverse of a is also a left
   inverse of b, and [mon_inverse_unique] identifies it with the inverse of b.
   This is a derived instance, not an axiom of the record. *)
#[export] Instance grp_inv_respects (G : GrpObject) :
  Proper (equiv ==> equiv) (@grp_inv G).
Proof.
  intros a b Hab.
  assert (Hinv : mon_op (grp_inv a) b ≈ mon_unit).
  { rewrite <- Hab.
    apply grp_inv_l. }
  exact (mon_inverse_unique G b (grp_inv a) (grp_inv b) Hinv (grp_inv_r b)).
Qed.

(* Every obligation from here to the end of the file is a monoid or group law
   verbatim, so the global [cat_simpl] obligation tactic is switched off (the
   Instance/CMon.v idiom): nothing below needs a proof search, and the searches
   [cat_simpl] would run are the wide ones whose behaviour has differed across
   Rocq versions. *)
#[local] Obligation Tactic := idtac.

(* Mac Lane's construction 4: every arrow of the delooping of a group is
   invertible, i.e. [Deloop G] is a one-object groupoid.  The two-sided
   inverse of the arrow f is the group inverse of the element f, and the two
   inverse laws of [IsIsomorphism] are the two group laws verbatim.

   Composed with Theory/Isomorphism.v's [IsIsoToIso] — which is what
   [Deloop_group_iso] below does — this exhibits the single object of
   [Deloop G] as isomorphic to itself in as many ways as G has elements.  That
   its endomorphisms are exactly G is [hom_monoid_Deloop] above; here they are
   in addition all invertible, so they are its automorphisms. *)
#[export] Program Instance Deloop_group_invertible (G : GrpObject)
  (x y : Deloop G) (f : x ~{Deloop G}~> y) : IsIsomorphism f := {
  two_sided_inverse := grp_inv f    (* the group inverse of the element f *)
}.
Next Obligation.
  intros G x y f.                   (* f ∘ f⁻¹ ≈ id  is  a * a⁻¹ ≈ 1 *)
  apply grp_inv_r.
Qed.
Next Obligation.
  intros G x y f.                   (* f⁻¹ ∘ f ≈ id  is  a⁻¹ * a ≈ 1 *)
  apply grp_inv_l.
Qed.

(* The same statement in object form: any two objects of [Deloop G] (there is
   only one) are isomorphic, and each element of G names such an isomorphism. *)
Definition Deloop_group_iso (G : GrpObject) (x y : Deloop G)
  (f : x ~{Deloop G}~> y) : x ≅ y :=
  IsIsoToIso f (Deloop_group_invertible G x y f).

(** ** Witnesses *)

(* Both records are inhabited by ordinary algebra, so nothing above is
   vacuously true: the natural numbers under addition are a monoid that is not
   a group, and the booleans under exclusive or are the group Z/2.  Their
   carrier setoids take Coq's own equality as `≈`, which is why the
   [mon_op_respects] field of each is discharged by instance resolution rather
   than appearing as an obligation — every function respects [eq].

   (Both statements are also the standard-library facts [Nat.add_assoc] and
   [Nat.add_0_r]; they are re-proved inline here because Lib does not put the
   arithmetic development in scope, and the two inductions are shorter than the
   import would be.) *)
Lemma nat_add_assoc (a b c : nat) : (a + (b + c))%nat = ((a + b) + c)%nat.
Proof.
  induction a; simpl; [reflexivity | now rewrite IHa].
Qed.

Lemma nat_add_0_r (a : nat) : (a + 0)%nat = a.
Proof.
  induction a; simpl; [reflexivity | now rewrite IHa].
Qed.

(* (ℕ, +, 0): the free monoid on one generator, and the first monoid Mac Lane
   names.  Its delooping is the category with one object and one arrow per
   natural number — the free category on a single loop (Fong and Spivak's
   Example 3.13 reads the correspondence off this case).  The carrier setoid
   is Lib/Datatypes.v's [nat_setoid], i.e. Leibniz equality on [nat]. *)
Program Definition Nat_Plus : MonObject := {|
  mon_setoid := {| carrier := nat; is_setoid := nat_setoid |};
  mon_unit   := 0%nat;
  mon_op     := Nat.add
|}.
Next Obligation.
  intros a b c.
  apply nat_add_assoc.
Qed.
Next Obligation.
  intros a; reflexivity.            (* 0 + a is a by computation *)
Qed.
Next Obligation.
  intros a.
  apply nat_add_0_r.
Qed.

(* (bool, xor, false): the underlying monoid of Z/2, over Leibniz equality on
   [bool]. *)
Program Definition Bool_Xor : MonObject := {|
  mon_setoid := {| carrier := bool
                 ; is_setoid := {| equiv := eq
                                 ; setoid_equiv := eq_equivalence |} |};
  mon_unit   := false;
  mon_op     := xorb
|}.
Next Obligation.
  intros a b c; now destruct a, b, c.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

(* Z/2 as a group: every element is its own inverse. *)
Program Definition Bool_Xor_Grp : GrpObject := {|
  grp_monoid := Bool_Xor;
  grp_inv    := fun b => b
|}.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

(* Composition in the delooping really is the monoid operation: the two are
   the same function, not merely equivalent.  (The objects must be given
   explicitly — the hom of [Deloop M] is the same setoid at every pair of
   objects, so nothing in `a ∘ b` determines them.) *)
Example deloop_nat_compose (a b : Nat_Plus) :
  @compose (Deloop Nat_Plus) ttt ttt ttt a b = (a + b)%nat := eq_refl.

(* And the inverse supplied by [Deloop_group_invertible] really is the group
   inverse: in Z/2, that of each arrow is the arrow itself. *)
Example deloop_bool_inverse (b : Bool_Xor_Grp) :
  two_sided_inverse
    (IsIsomorphism:=Deloop_group_invertible Bool_Xor_Grp ttt ttt b) = b
  := eq_refl.
