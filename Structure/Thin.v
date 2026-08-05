Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Thin categories, and the hom-preorder of a category *)

(* nLab:      https://ncatlab.org/nlab/show/thin+category
   nLab:      https://ncatlab.org/nlab/show/preorder
   Wikipedia: https://en.wikipedia.org/wiki/Preorder
   Book:      Mac Lane, "Categories for the Working Mathematician",
              Springer GTM 5, 2nd ed. 1998, §I.2 (construction 7, def. 4)
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.2
   Book:      Fong and Spivak, "Seven Sketches in Compositionality",
              CUP 2019, §§1.2.2, 1.3.1

   A category is THIN when any two parallel morphisms agree: the hom-setoid
   `x ~> y` has at most one element up to `≈`.  nLab equivalently calls such a
   category a (0,1)-category.  Mac Lane arrives at the same notion from the
   other side: CWM §I.2 builds a category from a preordered set, one arrow
   `x → y` per instance of `x ≤ y`, and defines a linear (total) order in the
   same section.  (The internal numbering — construction 7, definition 4 — is
   as cited by the issue this file answers; the section is the one to read.)

   The predicate below is stated exactly as Structure/Discrete.v:28 states its
   own: a property ASSERTED of a given category, rather than a construction
   BUILDING one.  That is why this file sits in Structure/ next to
   [Discrete] rather than in Instance/ next to [Proset] — Instance/Discrete.v
   records the same split in its header, calling [DiscreteCat] the
   object-level construction and Structure/Discrete.v's [Discrete] the
   predicate, and its [DiscreteCat_Discrete] the bridge.  Here
   Instance/Proset.v:33's [Proset] is the construction, [Thin] is the
   predicate, and [proset_thin] (Instance/Proset/Order.v) is the bridge.

   Thinness is what makes the order-theoretic dictionary of
   Instance/Poset.v:35-109 work: with all parallel arrows identified, every
   diagram commutes and every coherence law holds for free.  The library
   already exploits this pointwise — Instance/Two/Monoidal.v:26's [two_thin]
   discharges the whole [Two_Cartesian] obligation at :87 and the
   [Two_Terminal] one at :102 by a single appeal each (the monoidal structure
   at :105 is then derived from those through [Cartesian_Monoidal]), and
   Construction/Enriched/Two.v:156-159 closes the three enrichment laws the
   same way — but the property itself had no name.  This file gives it one,
   and Instance/Proset/Order.v puts it to work.

   The second half of the file goes back the other way.  Every category C
   carries a preorder on its objects, "x ≤ y when there is an arrow x ~> y".
   Since Coq's [relation] is Prop-valued while a hom lives in [Type], the
   passage squashes: [hom_preorder] uses [inhabited].  That squash is the
   whole content of the round trip measured in Instance/Proset/Order.v — it
   is invertible on a [Proset], whose homs are already Props, and in general
   it is not, which is why [HomChoice] is introduced here as an explicit
   hypothesis rather than assumed.

   NOTE on instance resolution: [hom_PreOrder] is deliberately left a plain
   [Definition] rather than being registered as a typeclass instance, and is
   passed explicitly at each use.  That matches how the tree already handles
   [PreOrder] arguments — Instance/Poset.v:121 hands [PeanoNat.Nat.le_preorder]
   to [Poset] by hand — and it keeps a rule whose conclusion is
   [PreOrder (hom_preorder ?C)] out of the search space for [PreOrder] goals
   whose relation is still a metavariable. *)

(* A category is thin when parallel morphisms are identified by the hom-setoid
   equivalence.  Note that this is `≈`, not `=`: on the library's setoid
   hom-sets that is the right notion, and it is what Instance/Proset.v:39
   supplies for a proset by declaring the equivalence to be [True]. *)
Definition Thin (C : Category) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y), f ≈ g.

(* Thinness is self-dual: reversing arrows neither creates nor merges parallel
   pairs.  Both directions hold on the nose because Construction/Opposite.v:106
   defines hom[C^op] x y as hom[C] y x and reuses the same hom-setoid. *)

Lemma Thin_Opposite {C : Category} : Thin C → Thin (C^op).
Proof. intros T x y f g; exact (T y x f g). Qed.

Lemma Opposite_Thin {C : Category} : Thin (C^op) → Thin C.
Proof. intros T x y f g; exact (T y x f g). Qed.

(* In a thin category every morphism is both monic and epic (the classes at
   Theory/Morphisms.v:104 and :116), because both cancellation laws conclude
   an equation between parallel morphisms.  The converse does not hold: being
   a bimorphism everywhere is far weaker than thinness. *)

Lemma thin_Monic {C : Category} (T : Thin C) {x y : C} (f : x ~> y) : Monic f.
Proof. constructor; intros z g1 g2 _; apply T. Qed.

Lemma thin_Epic {C : Category} (T : Thin C) {x y : C} (f : x ~> y) : Epic f.
Proof. constructor; intros z g1 g2 _; apply T. Qed.

(* A pair of opposing morphisms in a thin category is automatically an
   isomorphism: the two composites are endomorphisms, hence equal to the
   identity.  This is the categorical reading of "x ≤ y and y ≤ x", and it is
   exactly what antisymmetry rules out in Instance/Poset.v — a poset is a
   SKELETAL thin category (Instance/Poset.v:20), the isomorphic objects being
   forced equal.

   Both inverse laws are supplied directly rather than through [Program], so
   that the two appeals to thinness are visible in the term instead of being
   found by the [cat_simpl] obligation tactic (Lib/Tactics.v:225), whose [auto]
   would pick [T] out of the context. *)
Definition thin_iso {C : Category} (T : Thin C) {x y : C}
  (f : x ~> y) (g : y ~> x) : x ≅ y :=
  {| to          := f
   ; from        := g
   ; iso_to_from := T y y (f ∘ g) id
   ; iso_from_to := T x x (g ∘ f) id |}.

(* Conversely an isomorphism supplies the opposing pair, with no thinness
   needed; [to] and [from] are the two morphisms. *)
Definition iso_opposing_pair {C : Category} {x y : C} (i : x ≅ y) :
  (x ~> y) * (y ~> x) := (to i, from i).

(** ** The hom-preorder of a category *)

(* "x ≤ y when C has an arrow x ~> y."  Coq's [relation A] is [A → A → Prop]
   whereas [hom] lands in [Type], so the existence of an arrow is recorded by
   [inhabited]; see the header for what that costs. *)
Definition hom_preorder (C : Category) : relation (obj[C]) :=
  fun x y => inhabited (x ~{C}~> y).

(* It is a preorder: reflexivity is the identity arrow, transitivity is
   composition.  The [inhabited] witnesses may be eliminated here because the
   goal is itself a Prop. *)
Definition hom_PreOrder (C : Category) : PreOrder (hom_preorder C).
Proof.
  constructor.
  - intro x; exact (inhabits (@id C x)).
  - intros x y z Hxy Hyz.
    destruct Hxy as [f], Hyz as [g].
    exact (inhabits (g ∘ f)).
Defined.

(* Opposition on categories is order reversal on hom-preorders, and the two
   relations are not merely pointwise equivalent but CONVERTIBLE: both sides
   reduce to [inhabited (y ~{C}~> x)].  [Basics.flip] is the stdlib operation
   [flip R x y = R y x]. *)
Lemma hom_preorder_op (C : Category) (x y : obj[C]) :
  hom_preorder (C^op) x y = Basics.flip (hom_preorder C) x y.
Proof. reflexivity. Qed.

(* Choosing an arrow from the bare knowledge that one exists.  This is
   elimination of the Prop [inhabited (x ~> y)] into [Type], which Coq's
   elimination rules do not grant: [inhabited] has a [Type]-valued argument in
   its constructor, so its eliminator is restricted to Prop targets, and no
   [match] on the witness can produce a morphism.  The hypothesis is therefore
   taken explicitly wherever it is needed, never assumed.  It is free of charge
   whenever the homs of C are themselves Props — in particular on every
   [Proset], where [proset_HomChoice] discharges it (Instance/Proset/Order.v).

   What is claimed here is only that the obvious definition does not
   typecheck; no impossibility theorem is being asserted. *)
Definition HomChoice (C : Category) : Type :=
  ∀ (x y : obj[C]), hom_preorder C x y → x ~{C}~> y.
