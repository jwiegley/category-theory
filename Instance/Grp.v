Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * The category of groups *)

(* nLab:      https://ncatlab.org/nlab/show/Grp
   nLab:      https://ncatlab.org/nlab/show/group
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_groups

   [Grp] is the category of groups over [Sets]: an object is a setoid
   carrying an associative binary operation [grp_mul] with unit [grp_unit]
   and an inversion [grp_inv]; a morphism is a setoid map preserving the
   unit and the operation; two morphisms are equivalent when their
   underlying maps agree pointwise.  The file is modelled directly on
   Instance/CMon.v, whose [CMonObject] / [CMonHom] / [CMon] triple
   (Instance/CMon.v:32, :58, :140) it mirrors CMon at the hom record and the category; the object records differ by design (commutativity there, inversion here), including
   the universe discipline: nothing here is annotated, so [Grp] is
   universe-polymorphic exactly as [CMon] is.

   AXIOM ECONOMY.  The record below carries the SMALLEST law set that
   still presents a group, and every omission is discharged as a lemma
   rather than assumed:

     - Only the LEFT unit law [grp_mul_unit_l] and the LEFT inverse law
       [grp_mul_inv_l] are fields.  The right-handed forms are derived
       ([grp_mul_inv_r], [grp_mul_unit_r]) by the classical argument that
       runs left inverse + associativity into right inverse and then into
       the right unit law.  This is the group-theoretic strengthening of
       what Instance/CMon.v:49 does with commutativity, where only
       [cmon_plus_zero_r] is derivable.

     - [grp_inv] carries NO respectfulness field.  Congruence of inversion
       for `≈` is a THEOREM ([grp_inv_respects_law], exported as the
       instance [grp_inv_Proper]): from a ≈ b one gets
       grp_inv a * b ≈ grp_inv a * a ≈ grp_unit, and uniqueness of
       one-sided inverses ([grp_inv_unique_l]) then forces
       grp_inv a ≈ grp_inv b.  Only [grp_mul_respects] is a field.  A
       constructor of a [GrpObject] therefore owes four proofs, not seven.

   [GrpHom] does keep unit preservation as a field alongside
   multiplication preservation, matching [CMonHom] (Instance/CMon.v:58)
   and the issue's stated shape.  That field is REDUNDANT, and the file
   says so constructively rather than in prose: [grp_map_unit_from_mul]
   derives it from multiplication preservation alone by cancelling
   f(e) from f(e) * f(e) ≈ f(e) * e, and [Build_GrpHom'] is the resulting
   smart constructor that asks only for the multiplication law.
   Inverse preservation is not a field either: [grp_map_inv] derives it.

   WHAT THIS FILE ESTABLISHES BEYOND THE CATEGORY.  The forgetful functor
   [Grp_Forget] to [Sets] with its faithfulness ([Grp_Forget_Faithful]);
   the one-element group as a zero object ([Grp_Zero], packaged for
   Structure/ZeroObject.v:35, whose [ZeroObject] class wants a [Terminal],
   an [Initial] and a coincidence isomorphism -- here the identity, since
   one record plays both roles, exactly as at Instance/CMon/Biproduct.v:160);
   binary direct products as a [Cartesian] structure ([Grp_Cartesian],
   against the class at Structure/Cartesian.v:121); the characterization
   of monomorphisms as the injections ([Grp_injectivity_is_monic]); the
   reconciliation with the internal [GroupObject] of Structure/Group.v:109
   in both directions; and Riehl's opposite-group endofunctor with its
   inversion natural isomorphism. *)

(* Where the category of groups comes from, and what it is for

   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer GTM 5, 1998, Sections I.5 (Monics, Epis, and Zeros,
          p. 19) and I.6 (Foundations, p. 21)
   Book:  Riehl, "Category Theory in Context", Dover, 2016, Section 1.4
          (Naturality)
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",
          Trans. AMS 58, 1945
   Paper: Mac Lane, "Duality for groups", Bulletin of the AMS 56, 1950

   Groups are the founding example of the subject.  Eilenberg and Mac
   Lane's 1945 paper reaches categories and functors from group theory
   and topology, and Mac Lane's "Duality for groups" (1950) is the
   deliberate exercise of recasting group theory so that only
   homomorphisms and composition appear, in order that reversing every
   arrow should carry each notion to its dual -- the direct product to
   the free product, and so on.  The library already collects that
   dividend structurally (Structure/Cocartesian.v is Structure/Cartesian.v
   read in the opposite category), so it is fitting that the concrete
   category the programme was written about should exist in the tree.

   Two of Mac Lane's Chapter I sections bear directly on what is proved
   below.  Section I.5 is titled "Monics, Epis, and Zeros" and is where
   the three notions this file instantiates for groups are introduced;
   Section I.6, "Foundations", is where the size question raised by
   speaking of THE category of all groups is settled by restricting to
   small groups.  This formalization sidesteps that question the way the
   rest of the library does: [Grp] is universe-polymorphic, and the
   universe level of the carriers is a parameter rather than a decision.

   The zero object is where groups part company with sets.  In [Sets] the
   empty setoid is initial and the singleton is terminal, and they are
   different objects; in [Grp] the one-element group is BOTH, because
   there is no empty group (a group must contain a unit) and because a
   homomorphism out of the trivial group is pinned by [grp_map_unit].
   [Grp_Zero] records the coincidence.  Instance/CMon/Biproduct.v:160
   makes the same observation for commutative monoids, where it is the
   first step of a semiadditive structure; groups go further -- [Grp] is
   not semiadditive, since the direct product is not a biproduct unless
   the groups are abelian, so no biproduct claim is made here.

   Monomorphisms in [Grp] are exactly the injective homomorphisms, and
   this is genuinely a theorem rather than a definition -- the same
   statement is false for epimorphisms in many algebraic categories (the
   inclusion of the integers into the rationals is epic in rings without
   being surjective, Riehl's Exercises 1.2.iv and 1.6.v(ii)).  One direction is soft:
   an injection is monic in any concrete category, and it is proved here
   directly, by evaluating the two competing maps at a point.  Riehl's
   Exercise 1.6.iv is the abstract route to the same direction -- any
   faithful functor reflects monomorphisms, and [Grp_Forget_Faithful]
   supplies the faithful functor.  The other direction needs a PROBE
   group, an object with
   enough maps into the source to detect a difference, and the literature
   offers two standard choices.  One is the free group on one generator,
   the integers, whose homomorphisms into G are in bijection with the
   elements of G; the other is the kernel, mapped into G twice, once by
   inclusion and once trivially.  This file takes the kernel route
   ([Grp_kernel], [Grp_kernel_incl], [Grp_kernel_triv]): it is the
   cheaper of the two in a setoid library, because the kernel is a
   sub-setoid of a carrier already in hand, whereas the integers would
   have to be built along with an integer-power homomorphism and its
   sign-case analysis.  The two probes prove the same statement, and the
   statement proved here is the full biconditional at full strength.

   The last construction is Riehl's.  Category Theory in Context,
   Section 1.4 (Naturality), Example 1.4.4(vi) observes that the opposite
   group is a COVARIANT endofunctor of the category of groups, that it is
   naturally isomorphic to the identity, and that the component at G is
   the map sending g to its inverse -- which "does not define an
   automorphism of G, ... but it does define a homomorphism
   eta_G : G -> G^op, indeed an isomorphism", the elided clause being that
   inversion does not commute with the multiplication of G.
   That sentence is the whole content of [Grp_inv_to] below: inversion is
   an antihomomorphism ([grp_inv_mul]), which is precisely what makes it
   a homomorphism into the opposite group.  Naturality is then
   [grp_map_inv], the derived fact that homomorphisms commute with
   inversion.  [Grp_op_Isomorphism] assembles the two directions into an
   isomorphism in the functor category [[Grp, Grp]].

   Three earlier in-tree treatments of groups are superseded or
   complemented by this file, none of which built the category.
   Structure/Group.v:109 defines [GroupObject], a group internal to a
   cartesian monoidal category -- the right notion for topological
   groups, group schemes and Hopf algebras, but internal-only.
   [Grp_GroupObject] and [GroupObject_GrpObject] below show that at
   C = [Sets] with the cartesian monoidal structure of
   Structure/Monoidal/Internal/Product.v:435 the two notions carry the
   same data, in both directions and with the round trip on the
   operations checked by computation.  Instance/Comp.v:382 defines
   [Group] as a universal-algebra structure (an algebra for a signature
   with equations) with no category attached and, unlike this file,
   at the cost of [functional_extensionality].  Theory/Algebra/Monoid.v
   and Instance/CMon.v supply the unit-and-multiplication half of the
   structure without inverses. *)

(* A group: a setoid together with a unit element, a binary operation and
   an inversion, where only the operation is required to respect `≈` and
   only the left-handed unit and inverse laws are required to hold.  The
   right-handed laws and the respectfulness of inversion are derived
   below. *)
Record GrpObject := {
  grp_setoid :> SetoidObject;

  grp_unit : carrier grp_setoid;
  grp_mul  : carrier grp_setoid → carrier grp_setoid → carrier grp_setoid;
  grp_inv  : carrier grp_setoid → carrier grp_setoid;

  grp_mul_respects : Proper (equiv ==> equiv ==> equiv) grp_mul;

  grp_mul_assoc : ∀ a b c,
    grp_mul (grp_mul a b) c ≈ grp_mul a (grp_mul b c);
  grp_mul_unit_l : ∀ a, grp_mul grp_unit a ≈ a;
  grp_mul_inv_l  : ∀ a, grp_mul (grp_inv a) a ≈ grp_unit
}.

#[export] Existing Instance grp_mul_respects.

Section GrpFacts.

Context (G : GrpObject).

(* The right inverse law, from the left one.  The classical argument:
   a * a⁻¹ is dragged through a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹)), whose inner
   bracket collapses to a⁻¹ by the left laws, leaving a⁻¹⁻¹ * a⁻¹. *)
Lemma grp_mul_inv_r (a : carrier G) : grp_mul G a (grp_inv G a) ≈ grp_unit G.
Proof.
  assert (Hinner : grp_mul G (grp_inv G a) (grp_mul G a (grp_inv G a))
                     ≈ grp_inv G a).
  { rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_l. }
  transitivity (grp_mul G (grp_inv G (grp_inv G a))
                  (grp_mul G (grp_inv G a) (grp_mul G a (grp_inv G a)))).
  - rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    symmetry; apply grp_mul_unit_l.
  - rewrite Hinner.
    apply grp_mul_inv_l.
Qed.

(* The right unit law, from the left one and the right inverse law. *)
Lemma grp_mul_unit_r (a : carrier G) : grp_mul G a (grp_unit G) ≈ a.
Proof.
  transitivity (grp_mul G a (grp_mul G (grp_inv G a) a)).
  - rewrite grp_mul_inv_l.
    reflexivity.
  - rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_l.
Qed.

(* Uniqueness of inverses, right-handed form: anything absorbing a on the
   right is the chosen inverse of a. *)
Lemma grp_inv_unique_r (a b : carrier G) :
  grp_mul G a b ≈ grp_unit G → b ≈ grp_inv G a.
Proof.
  intro Hab.
  transitivity (grp_mul G (grp_unit G) b).
  - symmetry; apply grp_mul_unit_l.
  - rewrite <- (grp_mul_inv_l G a).
    rewrite grp_mul_assoc.
    rewrite Hab.
    apply grp_mul_unit_r.
Qed.

(* Uniqueness of inverses, left-handed form. *)
Lemma grp_inv_unique_l (a b : carrier G) :
  grp_mul G b a ≈ grp_unit G → b ≈ grp_inv G a.
Proof.
  intro Hba.
  transitivity (grp_mul G b (grp_unit G)).
  - symmetry; apply grp_mul_unit_r.
  - rewrite <- (grp_mul_inv_r a).
    rewrite <- grp_mul_assoc.
    rewrite Hba.
    apply grp_mul_unit_l.
Qed.

(* Inversion respects `≈`.  This is the field the record does not carry:
   from a ≈ b, the element grp_inv a is a left inverse of b, and left
   inverses are unique. *)
Lemma grp_inv_respects_law (a b : carrier G) :
  a ≈ b → grp_inv G a ≈ grp_inv G b.
Proof.
  intro Hab.
  apply grp_inv_unique_l.
  rewrite <- Hab.
  apply grp_mul_inv_l.
Qed.

End GrpFacts.

#[export] Instance grp_inv_Proper (G : GrpObject) :
  Proper (equiv ==> equiv) (grp_inv G) := grp_inv_respects_law G.

Section GrpFacts2.

Context (G : GrpObject).

Lemma grp_inv_unit : grp_inv G (grp_unit G) ≈ grp_unit G.
Proof.
  symmetry.
  apply grp_inv_unique_l.
  apply grp_mul_unit_l.
Qed.

Lemma grp_inv_inv (a : carrier G) : grp_inv G (grp_inv G a) ≈ a.
Proof.
  symmetry.
  apply grp_inv_unique_l.
  apply grp_mul_inv_r.
Qed.

(* Inversion is an ANTIhomomorphism: it reverses the order of a product.
   This is the fact that makes inversion a homomorphism into the opposite
   group rather than an automorphism (Riehl, Example 1.4.4(vi)). *)
Lemma grp_inv_mul (a b : carrier G) :
  grp_inv G (grp_mul G a b) ≈ grp_mul G (grp_inv G b) (grp_inv G a).
Proof.
  symmetry.
  apply grp_inv_unique_l.
  rewrite grp_mul_assoc.
  rewrite <- (grp_mul_assoc G (grp_inv G a) a b).
  rewrite grp_mul_inv_l.
  rewrite grp_mul_unit_l.
  apply grp_mul_inv_l.
Qed.

Lemma grp_cancel_l (a b c : carrier G) :
  grp_mul G a b ≈ grp_mul G a c → b ≈ c.
Proof.
  intro Habc.
  transitivity (grp_mul G (grp_mul G (grp_inv G a) a) b).
  - rewrite grp_mul_inv_l.
    symmetry; apply grp_mul_unit_l.
  - rewrite grp_mul_assoc.
    rewrite Habc.
    rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_l.
Qed.

Lemma grp_cancel_r (a b c : carrier G) :
  grp_mul G b a ≈ grp_mul G c a → b ≈ c.
Proof.
  intro Habc.
  transitivity (grp_mul G b (grp_mul G a (grp_inv G a))).
  - rewrite grp_mul_inv_r.
    symmetry; apply grp_mul_unit_r.
  - rewrite <- grp_mul_assoc.
    rewrite Habc.
    rewrite grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_r.
Qed.

End GrpFacts2.

(* A homomorphism of groups: a setoid map on the carriers preserving the
   unit and the operation.  Preservation of inversion is NOT a field; it
   is [grp_map_inv] below. *)
Record GrpHom (G H : GrpObject) := {
  grp_map :> SetoidMorphism (grp_setoid G) (grp_setoid H);

  grp_map_unit : grp_map (grp_unit G) ≈ grp_unit H;
  grp_map_mul : ∀ a b,
    grp_map (grp_mul G a b) ≈ grp_mul H (grp_map a) (grp_map b)
}.

Arguments grp_map {G H} _.
Arguments grp_map_unit {G H} _.
Arguments grp_map_mul {G H} _ _ _.

(* Homomorphisms preserve inversion.  f (a⁻¹) is a left inverse of f a,
   because f carries a⁻¹ * a ≈ e to f(a⁻¹) * f(a) ≈ e; uniqueness of left
   inverses finishes. *)
Lemma grp_map_inv {G H : GrpObject} (f : GrpHom G H) (a : carrier G) :
  grp_map f (grp_inv G a) ≈ grp_inv H (grp_map f a).
Proof.
  apply grp_inv_unique_l.
  rewrite <- grp_map_mul.
  rewrite grp_mul_inv_l.
  apply grp_map_unit.
Qed.

(* The unit-preservation FIELD of [GrpHom] is redundant: it follows from
   multiplication preservation by cancelling f e from
   f e * f e ≈ f (e * e) ≈ f e ≈ f e * e.  The field is retained anyway,
   to mirror [cmon_map_zero] at Instance/CMon.v:61 and to keep the
   projection available without a detour; [Build_GrpHom'] is the
   constructor that exploits the redundancy. *)
Lemma grp_map_unit_from_mul {G H : GrpObject}
      (f : SetoidMorphism (grp_setoid G) (grp_setoid H))
      (Hmul : ∀ a b, f (grp_mul G a b) ≈ grp_mul H (f a) (f b)) :
  f (grp_unit G) ≈ grp_unit H.
Proof.
  apply (grp_cancel_l H (f (grp_unit G))).
  rewrite <- Hmul.
  rewrite grp_mul_unit_l.
  symmetry; apply grp_mul_unit_r.
Qed.

(* Smart constructor: a setoid map preserving multiplication is already a
   group homomorphism. *)
Definition Build_GrpHom' {G H : GrpObject}
        (f : SetoidMorphism (grp_setoid G) (grp_setoid H))
        (Hmul : ∀ a b, f (grp_mul G a b) ≈ grp_mul H (f a) (f b)) :
  GrpHom G H :=
  {| grp_map      := f
   ; grp_map_unit := grp_map_unit_from_mul f Hmul
   ; grp_map_mul  := Hmul |}.

#[local] Obligation Tactic := idtac.

(* The hom-setoid: homomorphisms are compared by their underlying maps,
   pointwise up to the codomain's `≈` (as in [Sets]). *)
#[export]
Program Instance GrpHom_Setoid {G H : GrpObject} : Setoid (GrpHom G H) := {|
  equiv := fun f g => ∀ a, grp_map f a ≈ grp_map g a
|}.
Next Obligation.
  intros G H.
  constructor.
  - intros f a.
    reflexivity.
  - intros f g Hfg a.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (grp_map g a).
    + apply Hfg.
    + apply Hgh.
Qed.

(* The identity homomorphism: the identity setoid map, which preserves the
   unit and the operation on the nose. *)
Program Definition grp_hom_id {G : GrpObject} : GrpHom G G := {|
  grp_map := setoid_morphism_id
|}.
Next Obligation.
  intros G; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G a b; simpl.
  reflexivity.
Qed.

(* Composition of homomorphisms: composition of the underlying setoid maps;
   preservation of unit and operation composes. *)
Program Definition grp_hom_compose {G H K : GrpObject}
        (f : GrpHom H K) (g : GrpHom G H) : GrpHom G K := {|
  grp_map := setoid_morphism_compose (grp_map f) (grp_map g)
|}.
Next Obligation.
  intros G H K f g; simpl.
  unfold Basics.compose.
  rewrite (grp_map_unit g).
  apply (grp_map_unit f).
Qed.
Next Obligation.
  intros G H K f g a b; simpl.
  unfold Basics.compose.
  rewrite (grp_map_mul g).
  apply (grp_map_mul f).
Qed.

Lemma grp_hom_compose_respects {G H K : GrpObject} :
  Proper (equiv ==> equiv ==> equiv) (@grp_hom_compose G H K).
Proof.
  intros f f' Hf g g' Hg a; simpl.
  unfold Basics.compose.
  rewrite (Hg a).
  apply Hf.
Qed.

(* The category of groups.

       objects: groups over setoids
        arrows: unit- and operation-preserving setoid maps
      identity: the identity setoid map
   composition: composition of setoid maps *)
Program Definition Grp : Category := {|
  obj     := GrpObject;
  hom     := GrpHom;
  homset  := @GrpHom_Setoid;
  id      := @grp_hom_id;
  compose := @grp_hom_compose;

  compose_respects := @grp_hom_compose_respects
|}.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.

(* The forgetful functor to [Sets], dropping the group structure. *)
Program Definition Grp_Forget : Grp ⟶ Sets := {|
  fobj := fun G => grp_setoid G;
  fmap := fun _ _ f => grp_map f
|}.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros G a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G H K f g a; simpl.
  reflexivity.
Qed.

(* [Grp_Forget] is faithful by construction, since equivalence of
   homomorphisms in [Grp] IS equivalence of the underlying setoid maps. *)
#[export] Program Instance Grp_Forget_Faithful : Faithful Grp_Forget.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.

(** ** The zero object: the trivial group *)

(* The one-element group on [poly_unit]: unit, operation and inversion are
   all the point, and every law holds by computation. *)
Definition Grp_trivial : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := poly_unit; is_setoid := unit_setoid |};
    grp_unit := ttt;
    grp_mul := fun _ _ => ttt;
    grp_inv := fun _ => ttt
  |}.
  - intros x y Hxy u v Huv.
    reflexivity.
  - intros a b c.
    reflexivity.
  - intros a.
    destruct a.
    reflexivity.
  - intros a.
    reflexivity.
Defined.

(* The unique homomorphism into the trivial group: everything to the
   point. *)
Definition Grp_one (G : GrpObject) : G ~{Grp}~> Grp_trivial.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G Grp_trivial {| morphism := fun _ => ttt |} _ _).
  - intros a b Hab.
    reflexivity.
  - reflexivity.
  - intros a b.
    reflexivity.
Defined.

(* Uniqueness into the trivial group: both images live in [poly_unit]. *)
Lemma Grp_one_unique (G : GrpObject) (f g : G ~{Grp}~> Grp_trivial) : f ≈ g.
Proof.
  intro a.
  destruct (grp_map f a), (grp_map g a).
  reflexivity.
Qed.

Definition Grp_Terminal : @Terminal Grp :=
  @Build_Terminal Grp Grp_trivial Grp_one Grp_one_unique.

(* The unique homomorphism out of the trivial group: the point goes to the
   unit -- the only unit-preserving choice. *)
Definition Grp_zero_hom (G : GrpObject) : Grp_trivial ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom Grp_trivial G {| morphism := fun _ => grp_unit G |} _ _).
  - intros a b Hab.
    reflexivity.
  - reflexivity.
  - intros a b.
    symmetry.
    apply grp_mul_unit_l.
Defined.

(* Uniqueness out of the trivial group: the point IS the unit, and any
   homomorphism sends units to units ([grp_map_unit]).  Note the contrast
   with [Sets], where the initial object is the EMPTY setoid: there is no
   empty group, and this is what makes the trivial group a zero object. *)
Lemma Grp_zero_hom_unique (G : GrpObject)
  (f g : Grp_trivial ~{Grp}~> G) : f ≈ g.
Proof.
  intro a.
  destruct a.
  transitivity (grp_unit G).
  - exact (grp_map_unit f).
  - symmetry.
    exact (grp_map_unit g).
Qed.

Definition Grp_Initial : @Initial Grp :=
  @Build_Terminal (Grp^op) Grp_trivial Grp_zero_hom Grp_zero_hom_unique.

(* The trivial group is a zero object.  The same record [Grp_trivial]
   carries both the terminal and the initial structure, so the coincidence
   isomorphism of Structure/ZeroObject.v is the identity. *)
#[export] Instance Grp_Zero : ZeroObject Grp :=
  @Build_ZeroObject Grp Grp_Terminal Grp_Initial iso_id.

(** ** Binary direct products *)

(* The direct product G × H: the product setoid with componentwise unit,
   operation and inversion. *)
Definition Grp_product (G H : GrpObject) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := (carrier G * carrier H)%type
                   ; is_setoid := @prod_setoid _ _
                       (is_setoid (grp_setoid G))
                       (is_setoid (grp_setoid H)) |};
    grp_unit := (grp_unit G, grp_unit H);
    grp_mul := fun p q =>
      (grp_mul G (fst p) (fst q), grp_mul H (snd p) (snd q));
    grp_inv := fun p => (grp_inv G (fst p), grp_inv H (snd p))
  |}.
  - intros p p' Hp q q' Hq.
    destruct Hp as [Hp1 Hp2], Hq as [Hq1 Hq2].
    split; simpl.
    + now rewrite Hp1, Hq1.
    + now rewrite Hp2, Hq2.
  - intros a b c.
    split; simpl; apply grp_mul_assoc.
  - intros a.
    split; simpl; apply grp_mul_unit_l.
  - intros a.
    split; simpl; apply grp_mul_inv_l.
Defined.

(* Left projection [fst]: a homomorphism on the nose. *)
Definition Grp_exl {G H : GrpObject} : Grp_product G H ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G H) G {| morphism := fun p => fst p |} _ _).
  - intros p q Hpq.
    exact (fst Hpq).
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* Right projection [snd]. *)
Definition Grp_exr {G H : GrpObject} : Grp_product G H ~{Grp}~> H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G H) H {| morphism := fun p => snd p |} _ _).
  - intros p q Hpq.
    exact (snd Hpq).
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* The mediating morphism a ↦ (f a, g a): componentwise a homomorphism. *)
Definition Grp_fork {K G H : GrpObject}
  (f : K ~{Grp}~> G) (g : K ~{Grp}~> H) : K ~{Grp}~> Grp_product G H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom K (Grp_product G H)
       {| morphism := fun a => (grp_map f a, grp_map g a) |} _ _).
  - intros a b Hab.
    split; simpl; now rewrite Hab.
  - split; simpl.
    + apply (grp_map_unit f).
    + apply (grp_map_unit g).
  - intros a b.
    split; simpl.
    + apply (grp_map_mul f).
    + apply (grp_map_mul g).
Defined.

(* The universal property holds because equivalence of pairs in the
   product setoid IS componentwise equivalence, so both halves of
   [ump_products] are projections of that. *)
#[export] Program Instance Grp_Cartesian : @Cartesian Grp := {
  product_obj := Grp_product;
  fork := @Grp_fork;
  exl := @Grp_exl;
  exr := @Grp_exr
}.
Next Obligation.
  intros K G H f f' Hf g g' Hg a.
  split; simpl.
  - exact (Hf a).
  - exact (Hg a).
Qed.
Next Obligation.
  intros K G H f g h.
  split.
  - intro Hh.
    split; intro a.
    + exact (fst (Hh a)).
    + exact (snd (Hh a)).
  - intros [H1 H2] a.
    split; simpl.
    + exact (H1 a).
    + exact (H2 a).
Qed.

(** ** Monomorphisms are exactly the injections *)

(* The kernel of f, as a group: the sub-setoid of elements sent to the
   unit, with the operations inherited from the source.  Closure is where
   the derived facts pay off -- the product of two kernel elements lands
   in the unit by [grp_map_mul] and [grp_mul_unit_l], the inverse by
   [grp_map_inv] and [grp_inv_unit]. *)
Definition grp_kernel_carrier {G H : GrpObject} (f : G ~{Grp}~> H) : Type :=
  { a : carrier G & grp_map f a ≈ grp_unit H }.

(* Two kernel elements are equivalent when their underlying elements are;
   the membership witness is ignored, so no proof irrelevance is needed. *)
Program Definition grp_kernel_setoid {G H : GrpObject} (f : G ~{Grp}~> H) :
  Setoid (grp_kernel_carrier f) := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.
Next Obligation.
  intros G H f.
  constructor.
  - intro p.
    reflexivity.
  - intros p q Hpq.
    now symmetry.
  - intros p q r Hpq Hqr.
    now transitivity (projT1 q).
Qed.

Definition Grp_kernel {G H : GrpObject} (f : G ~{Grp}~> H) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := grp_kernel_carrier f
                   ; is_setoid := grp_kernel_setoid f |};
    grp_unit := existT _ (grp_unit G) (grp_map_unit f);
    grp_mul := fun p q =>
      existT _ (grp_mul G (projT1 p) (projT1 q)) _;
    grp_inv := fun p => existT _ (grp_inv G (projT1 p)) _
  |}.
  - (* the product of two kernel elements is a kernel element *)
    rewrite grp_map_mul, (projT2 p), (projT2 q).
    apply grp_mul_unit_l.
  - (* the inverse of a kernel element is a kernel element *)
    rewrite grp_map_inv, (projT2 p).
    apply grp_inv_unit.
  - intros p p' Hp q q' Hq.
    simpl in *.
    now rewrite Hp, Hq.
  - intros a b c.
    simpl.
    apply grp_mul_assoc.
  - intros a.
    simpl.
    apply grp_mul_unit_l.
  - intros a.
    simpl.
    apply grp_mul_inv_l.
Defined.

(* The two probe maps out of the kernel: the inclusion ... *)
Definition Grp_kernel_incl {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_kernel f ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_kernel f) G {| morphism := fun p => projT1 p |} _ _).
  - intros p q Hpq.
    exact Hpq.
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* ... and the constant map at the unit. *)
Definition Grp_kernel_triv {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_kernel f ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_kernel f) G
       {| morphism := fun _ => grp_unit G |} _ _).
  - intros p q Hpq.
    reflexivity.
  - reflexivity.
  - intros p q.
    symmetry.
    apply grp_mul_unit_l.
Defined.

(* f cannot tell the two probe maps apart: it sends every kernel element
   to the unit by definition of the kernel, and the unit to the unit by
   [grp_map_unit]. *)
Lemma Grp_kernel_probe {G H : GrpObject} (f : G ~{Grp}~> H) :
  f ∘ Grp_kernel_incl f ≈ f ∘ Grp_kernel_triv f.
Proof.
  intro p.
  simpl.
  unfold Basics.compose.
  transitivity (grp_unit H).
  - exact (projT2 p).
  - symmetry.
    apply (grp_map_unit f).
Qed.

(* In [Grp] the monomorphisms are exactly the injections (up to `≈`),
   mirroring [injectivity_is_monic] at Instance/Sets.v:369.  The forward
   direction is soft.  The reverse direction probes f with the kernel:
   monicity collapses the inclusion to the constant map, so the kernel is
   trivial, and f a ≈ f b then puts a * b⁻¹ in the kernel. *)
Theorem Grp_injectivity_is_monic {G H : GrpObject} (f : G ~{Grp}~> H) :
  (∀ a b : carrier G, grp_map f a ≈ grp_map f b → a ≈ b) ↔ Monic f.
Proof.
  split.
  - intro Hinj.
    constructor.
    intros K g1 g2 Hg a.
    apply Hinj.
    exact (Hg a).
  - intros [Hmonic] a b Hab.
    assert (Hker : grp_map f (grp_mul G a (grp_inv G b)) ≈ grp_unit H).
    { rewrite grp_map_mul, grp_map_inv, Hab.
      apply grp_mul_inv_r. }
    pose proof (Hmonic (Grp_kernel f) (Grp_kernel_incl f) (Grp_kernel_triv f)
                  (Grp_kernel_probe f)) as Htriv.
    specialize (Htriv (existT _ (grp_mul G a (grp_inv G b)) Hker)).
    simpl in Htriv.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite grp_mul_inv_r.
    exact Htriv.
Qed.

(** ** The opposite-group functor and inversion (Riehl, Example 1.4.4(vi)) *)

(* G^op: the same setoid with the multiplication reversed.  The unit and
   the inversion are unchanged, since the left laws of G^op are the right
   laws of G. *)
Definition Grp_op_obj (G : GrpObject) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := grp_setoid G;
    grp_unit := grp_unit G;
    grp_mul := fun a b => grp_mul G b a;
    grp_inv := grp_inv G
  |}.
  - intros a a' Ha b b' Hb.
    now rewrite Ha, Hb.
  - intros a b c.
    symmetry.
    apply grp_mul_assoc.
  - intros a.
    apply grp_mul_unit_r.
  - intros a.
    apply grp_mul_inv_r.
Defined.

(* On morphisms the functor is the identity: a homomorphism f already
   satisfies f (b * a) ≈ f b * f a, which is the multiplication law read
   in the opposite groups.  This is why (-)^op is COVARIANT on Grp. *)
Definition Grp_op_map {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_op_obj G ~{Grp}~> Grp_op_obj H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_op_obj G) (Grp_op_obj H) (grp_map f) _ _).
  - apply (grp_map_unit f).
  - intros a b.
    apply (grp_map_mul f).
Defined.

Program Definition Grp_Op : Grp ⟶ Grp := {|
  fobj := Grp_op_obj;
  fmap := @Grp_op_map
|}.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros G a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G H K f g a; simpl.
  reflexivity.
Qed.

(* Inversion as a homomorphism G ~> G^op.  It is NOT an endomorphism of G:
   the multiplication law it satisfies is (a * b)⁻¹ ≈ b⁻¹ * a⁻¹, which is
   the law of G^op read at the images. *)
Definition Grp_inv_to (G : GrpObject) : G ~{Grp}~> Grp_op_obj G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G (Grp_op_obj G) {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - exact (grp_inv_unit G).
  - intros a b.
    exact (grp_inv_mul G a b).
Defined.

(* The same map read backwards, a homomorphism G^op ~> G. *)
Definition Grp_inv_from (G : GrpObject) : Grp_op_obj G ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_op_obj G) G {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - exact (grp_inv_unit G).
  - intros a b.
    exact (grp_inv_mul G b a).
Defined.

(* Naturality in both orientations is [grp_map_inv]: homomorphisms commute
   with inversion. *)
Program Definition Grp_inv_Transform : @Id Grp ⟹ Grp_Op := {|
  transform := Grp_inv_to
|}.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  apply grp_map_inv.
Qed.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.

Program Definition Grp_inv_Transform_inv : Grp_Op ⟹ @Id Grp := {|
  transform := Grp_inv_from
|}.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  apply grp_map_inv.
Qed.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.

(* The identity functor on [Grp] is naturally isomorphic to the
   opposite-group functor, the component at G being inversion.  Both round
   trips are [grp_inv_inv]. *)
Program Definition Grp_op_Isomorphism :
  @Isomorphism ([Grp, Grp]) (@Id Grp) Grp_Op := {|
  to   := Grp_inv_Transform;
  from := Grp_inv_Transform_inv
|}.
Next Obligation.
  intros G a; simpl.
  unfold Basics.compose.
  apply grp_inv_inv.
Qed.
Next Obligation.
  intros G a; simpl.
  unfold Basics.compose.
  apply grp_inv_inv.
Qed.

(** ** Reconciliation with the internal [GroupObject] of Structure/Group.v *)

(* A NOTE ON DUPLICATION, for the reader who greps.  The tree already carries
   a monoidal structure with the same underlying data at Instance/Sets.v:283,
   the exported instance [Sets_Product_Monoidal].  The definition below is a
   DISTINCT, NON-CONVERTIBLE term (their units agree by reflexivity; their
   tensors do not -- one is a Program-built bifunctor, the other the CC_
   composite), assembled through CC_Monoidal because [GroupObject] needs a
   [CartesianMonoidal], which the tree does not otherwise provide for [Sets].
   It is deliberately a plain Definition, not an instance: registering a
   second [@Monoidal Sets] path would change typeclass resolution elsewhere.
   No comparison isomorphism between the two structures is proved here; a
   consumer needing one should build it or unify the two upstream. *)
Definition Sets_prod_Monoidal : @Monoidal Sets :=
  @CC_Monoidal Sets Sets_Cartesian Sets_Terminal.

Definition Sets_CartesianMonoidal : @CartesianMonoidal Sets :=
  @CC_CartesianMonoidal Sets Sets_Cartesian Sets_Terminal.

Program Definition Grp_unit_map (G : GrpObject) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> grp_setoid G :=
  {| morphism := fun _ => grp_unit G |}.

Program Definition Grp_mul_map (G : GrpObject) :
  @product_obj Sets Sets_Cartesian (grp_setoid G) (grp_setoid G)
    ~{Sets}~> grp_setoid G :=
  {| morphism := fun p => grp_mul G (fst p) (snd p) |}.
Next Obligation.
  intros G p q Hpq.
  destruct Hpq as [H1 H2].
  simpl in *.
  now rewrite H1, H2.
Qed.

(* Every law of [MonoidObject] is the corresponding law of [GrpObject]
   read at a point, because in [Sets] the tensor is the product setoid,
   the unitors are the projections and the associator is reassociation of
   pairs -- all of which compute. *)
Definition Grp_MonoidObject (G : GrpObject) :
  @MonoidObject Sets Sets_prod_Monoidal (grp_setoid G).
Proof.
  unshelve notypeclasses refine
    (@Build_MonoidObject Sets Sets_prod_Monoidal (grp_setoid G)
       (Grp_unit_map G) (Grp_mul_map G) _ _ _).
  - intro p; simpl.
    apply grp_mul_unit_l.
  - intro p; simpl.
    apply grp_mul_unit_r.
  - intro p; simpl.
    apply grp_mul_assoc.
Defined.

Program Definition Grp_inverse_map (G : GrpObject) :
  grp_setoid G ~{Sets}~> grp_setoid G := {| morphism := grp_inv G |}.

(* A [GrpObject] IS a group object in [Sets]: the inverse laws of
   Structure/Group.v, whose right-hand side is the constant-at-the-unit
   endomorphism mempty ∘ eliminate, evaluate at a point to
   [grp_mul_inv_l] and [grp_mul_inv_r]. *)
Definition Grp_GroupObject (G : GrpObject) :
  @GroupObject Sets Sets_CartesianMonoidal (grp_setoid G).
Proof.
  unshelve notypeclasses refine
    (@Build_GroupObject Sets Sets_CartesianMonoidal (grp_setoid G)
       (Grp_MonoidObject G) (Grp_inverse_map G) _ _).
  - intro a; simpl.
    apply grp_mul_inv_l.
  - intro a; simpl.
    apply grp_mul_inv_r.
Defined.

(* And conversely, at full strength: a group object in [Sets] is a
   [GrpObject].  The record is destructured rather than projected because
   Structure/Group.v reserves the token [inverse] for its notation, so the
   field cannot be named in a term. *)
Definition GroupObject_GrpObject (X : Sets)
  (GO : @GroupObject Sets Sets_CartesianMonoidal X) : GrpObject.
Proof.
  destruct GO as [mon inv Hleft Hright].
  destruct mon as [me ma Hunitl Hunitr Hassoc].
  unshelve notypeclasses refine {|
    grp_setoid := X;
    grp_unit := me ttt;
    grp_mul := fun a b => ma (a, b);
    grp_inv := fun a => inv a
  |}.
  - intros a a' Ha b b' Hb.
    apply proper_morphism.
    split; assumption.
  - intros a b c.
    exact (Hassoc ((a, b), c)).
  - intros a.
    exact (Hunitl (ttt, a)).
  - intros a.
    exact (Hleft a).
Defined.

(* The two translations are mutually inverse on the operations, by
   computation: the round trip changes no data at all. *)
Example Grp_GroupObject_roundtrip_unit (G : GrpObject) :
  grp_unit (GroupObject_GrpObject (grp_setoid G) (Grp_GroupObject G))
    ≈ grp_unit G.
Proof. reflexivity. Qed.

Example Grp_GroupObject_roundtrip_mul (G : GrpObject) (a b : carrier G) :
  grp_mul (GroupObject_GrpObject (grp_setoid G) (Grp_GroupObject G)) a b
    ≈ grp_mul G a b.
Proof. reflexivity. Qed.

Example Grp_GroupObject_roundtrip_inv (G : GrpObject) (a : carrier G) :
  grp_inv (GroupObject_GrpObject (grp_setoid G) (Grp_GroupObject G)) a
    ≈ grp_inv G a.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** A nontrivial witness: Z/2, and non-vacuity of the machinery *)

(* Everything above is proved for all groups but, before this section, the
   file constructed only the one-element group -- so nothing in the tree
   DEMONSTRATED the biconditional, the products, or the opposite functor on a
   non-degenerate object.  Z/2 on bool closes that gap (the construction and
   the non-vacuity corollaries below were supplied by the audit of the
   previous commit).  The second reconciliation round trip is recorded here
   as well. *)

Program Definition bool_setoid : Setoid bool := {| equiv := @eq bool |}.

Definition Z2 : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := bool ; is_setoid := bool_setoid |};
    grp_unit := false;
    grp_mul  := xorb;
    grp_inv  := fun b => b
  |}.
  - intros x y Hxy u v Huv; simpl in *; subst; reflexivity.
  - intros a b c; simpl; now destruct a, b, c.
  - intros a; simpl; now destruct a.
  - intros a; simpl; now destruct a.
Defined.

(* Z2 is genuinely nontrivial. *)
Lemma Z2_nontrivial : (@equiv _ (grp_setoid Z2) true false) -> False.
Proof. simpl. discriminate. Qed.

(* The unique hom Z2 ~> 1 is NOT injective ... *)
Lemma Z2_to_one_not_injective :
  (forall a b : carrier Z2, grp_map (Grp_one Z2) a ≈ grp_map (Grp_one Z2) b -> a ≈ b) -> False.
Proof.
  intro Hinj.
  apply Z2_nontrivial.
  apply Hinj.
  simpl. reflexivity.
Qed.

(* ... hence NOT monic.  So `Monic` in Grp is a non-vacuous predicate. *)
Theorem Monic_in_Grp_is_not_vacuous : Monic (Grp_one Z2) -> False.
Proof.
  intro Hm.
  apply Z2_to_one_not_injective.
  destruct (Grp_injectivity_is_monic (Grp_one Z2)) as [_ Hback].
  exact (Hback Hm).
Qed.

(* And some map IS monic: the identity on Z2. *)
Theorem Monic_in_Grp_is_inhabited : @Monic Grp Z2 Z2 (@id Grp Z2).
Proof. apply (@id_monic Grp Z2). Qed.

(* The kernel probe is non-degenerate: the kernel of Z2 ~> 1 contains a
   non-unit element. *)
Definition ker_true : carrier (Grp_kernel (Grp_one Z2)).
Proof. exists true. simpl. reflexivity. Defined.

Lemma Grp_kernel_nondegenerate :
  (@equiv _ (grp_setoid (Grp_kernel (Grp_one Z2)))
        ker_true (grp_unit (Grp_kernel (Grp_one Z2)))) -> False.
Proof. simpl. discriminate. Qed.

(* ===================================================================== *)
(* E: the OTHER round trip, GroupObject -> GrpObject -> GroupObject.      *)
(*    Is it provable?  (It is NOT stated in Instance/Grp.v.)              *)
(* ===================================================================== *)

Example rt_back_unit (X : Sets) (GO : @GroupObject Sets Sets_CartesianMonoidal X) :
  @mempty Sets Sets_prod_Monoidal X
     (Grp_MonoidObject (GroupObject_GrpObject X GO))
  ≈ @mempty Sets Sets_prod_Monoidal X GO.
Proof. intro u; destruct u; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.

Example rt_back_mul (X : Sets) (GO : @GroupObject Sets Sets_CartesianMonoidal X) :
  @mappend Sets Sets_prod_Monoidal X
     (Grp_MonoidObject (GroupObject_GrpObject X GO))
  ≈ @mappend Sets Sets_prod_Monoidal X GO.
Proof. intro p; destruct p; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.

Section RTInv.
#[local] Existing Instance Sets_CartesianMonoidal.
Context (X : Sets).
Context `{GO : @GroupObject Sets Sets_CartesianMonoidal X}.
Example rt_back_inv : Grp_inverse_map (GroupObject_GrpObject X GO) ≈ inverse[X].
Proof. intro a; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.
End RTInv.

(* ===================================================================== *)
(* Is Grp_Op an involution on the nose?                                   *)
(* ===================================================================== *)

