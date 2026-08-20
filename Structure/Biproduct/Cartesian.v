Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Biproducts give both a cartesian and a cocartesian structure *)

(* nLab:      https://ncatlab.org/nlab/show/biproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct
   Book:      Mac Lane, "Categories for the Working Mathematician"
              (2nd ed.), §III.3, book p. 63 (maclane:III.3:remark1)

   Mac Lane's §III.3 roster of concrete coproducts opens with the direct
   sum: in Ab, in R-Mod, and (the semiadditive phenomenon in its purest
   form) in the category of commutative monoids, the coproduct of two
   objects is carried by the SAME object as their product.  This file is
   the piece of vocabulary that observation needs and that the tree did
   not have.

   [Structure/Biproduct.v] already packages "x ⊕ y is at once a product
   and a coproduct" as a record, with both universal properties stated in
   the ∃!-form: [bi_is_product] and [bi_is_coproduct].  What it does not
   do is hand the result back in the vocabulary the rest of the library
   speaks.  Products and coproducts are consumed through
   [Structure/Cartesian.v]'s [Cartesian] class and
   [Structure/Cocartesian.v]'s [Cocartesian] notation — [x × y], [f △ g],
   [exl]/[exr]; [x + y], [f ▽ g], [inl]/[inr] — and neither was reachable
   from a biproduct.  The two definitions below close that gap once and
   for all:

     [biproduct_Cartesian]   : HasBiproducts C → @Cartesian C
     [biproduct_Cocartesian] : HasBiproducts C → @Cocartesian C

   Both are pure repackagings.  [bi_pair]/[bi_copair] supply the two
   mediators, [bi_pair_respects]/[bi_copair_respects] the two
   respectfulness fields, and the single ∃! clause of the biproduct record
   supplies both halves of [ump_products] — its existence half gives the
   two computation rules and its uniqueness half gives the converse.  No
   new mathematical content is introduced; what is introduced is a name.

   WHAT IS PROVED, AND AT WHAT STRENGTH.  The three identifications below
   the definitions hold at LEIBNIZ EQUALITY by [eq_refl], not merely up to
   [≈] or up to isomorphism:

     [biproduct_product_obj]   : x × y IS [biproduct_obj (biproduct x y)]
     [biproduct_coprod_obj]    : x + y IS the same object
     [biproduct_prod_is_coprod]: x × y IS x + y

   The last is the sentence "in a category with biproducts the binary
   product and the binary coproduct are the same object" as a machine
   checked conversion rather than as prose or as a constructed
   isomorphism.  The mediators and the injections likewise return on the
   nose ([biproduct_fork_is_pair], [biproduct_merge_is_copair],
   [biproduct_exl_is_bi_exl] and its three siblings), so a consumer may
   move between the two vocabularies by conversion alone.

   THE ROUND TRIP AGAINST Structure/Semiadditive.v.  The converse passage
   already existed: [cartesian_biproduct] and [cartesian_has_biproducts]
   (Structure/Semiadditive.v:228, :244) turn a preadditive category with
   binary products into one with biproducts.  Composing it with this
   file's [biproduct_Cartesian] returns the original biproduct OBJECT by
   [eq_refl] ([biproduct_roundtrip_obj]) and the original projections by
   [eq_refl] too ([biproduct_roundtrip_exl], [biproduct_roundtrip_exr]).
   It does NOT return the original record: the INJECTIONS are rebuilt as
   the forks [id △ 0] and [0 △ id], which are only [≈]-equal to the
   originals (proved, as [biproduct_roundtrip_inl] and
   [biproduct_roundtrip_inr]), and the law and universal-property fields
   are rebuilt from scratch.  Both strict failures are pinned as
   conversion negatives in Test/ProbeCoproduct.v rather than left as
   assertions.

   AN ENGINEERING FINDING, AND WHY NEITHER DEFINITION IS AN [Instance].
   Registering [biproduct_Cartesian] for typeclass resolution would close
   a resolution cycle with Structure/Semiadditive.v's converse:
   [Cartesian C] would be solved from [HasBiproducts C], which
   [cartesian_has_biproducts] solves from [Cartesian C] and
   [Preadditive C].  Both are plain [Definition]s here and there for that
   reason, and the concrete categories downstream register their own
   [Cartesian]/[Cocartesian] instances directly, so resolution never sees
   the generic bridge at all.

   UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS.  Both definitions read
   [biproduct_Cartesian@{u u0} : ∀ {C : Category@{u u0 u0}} …], so the
   category's HOM and PROOF universes are IDENTIFIED, not merely bounded.
   That is INHERITED from [Cartesian], not introduced here:
   [Cartesian@{u u0}] itself takes a [Category@{u u0 u0}], and that link
   is real.  But read the CAUSE precisely, because an earlier draft of
   this header got it wrong: it said the identification "is already
   present at Structure/Terminal.v's [Terminal]", implying [Terminal] is
   the source.  An audit REFUTED that as causal — a one-field class
   [{ t1 : obj }] declared over an unannotated [Context `{C : Category}]
   with no [Terminal] and no [Cartesian] anywhere in scope comes out at
   [Category@{u u0 u0}] just the same.  The source is universe
   MINIMIZATION of the unannotated generalized binder, which every class
   in this hierarchy shares.  Nor does any of this content REQUIRE the
   identification: the same field shape re-elaborates as
   [Category@{uo uh up}] when the levels are declared apart, so what is
   really present is a bound that minimization collapses.  Negatives 6
   and 7 record that the EXISTING constants [Cartesian] and [Terminal]
   cannot be applied at separated levels — which is true and worth
   pinning — but they establish sharing, not causation.  Nothing else
   is pinned: the object universe
   stays free, and the only other constraints are the two bounds
   [u0 <= projections.u0] and [u0 <= projections.u1] coming from the
   [∃!] in the biproduct record.

   WHAT IS NOT DELIVERED.  No terminal or initial object is claimed from
   the biproduct structure — a zero object is already assumed, so both
   exist, but they are not bundled into the produced structures (the
   [Cartesian] class carries no terminal object, matching
   Instance/Grp.v's [Grp_Cartesian]).  Nothing is said about biproducts of
   families or about additivity; [Structure/Semiadditive.v] owns the
   enrichment story and is only consumed here, never extended.  And no
   claim is made that a category with binary products and binary
   coproducts on a common carrier must have biproducts: the four
   interaction laws are genuine extra data, and the converse is
   Structure/Semiadditive.v's [bicartesian_preadditive], stated there
   under its own hypotheses. *)

Section BiproductCartesian.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{B : @HasBiproducts C Z}.

(** ** The cartesian structure *)

(* The product-side mediator, named so the [Cartesian] record below can be
   built as a literal rather than through [Program] obligations whose
   order is an elaboration detail. *)
Definition biproduct_fork {x y z : C} (f : x ~> y) (g : x ~> z) :
  x ~> biproduct_obj (biproduct y z) :=
  bi_pair (biproduct y z) f g.

Lemma biproduct_fork_respects (x y z : C) :
  Proper (equiv ==> equiv ==> equiv) (@biproduct_fork x y z).
Proof. apply bi_pair_respects. Qed.

(* The universal property: existence gives the two computation rules,
   uniqueness gives the converse. *)
Lemma biproduct_ump {x y z : C} (f : x ~> y) (g : x ~> z)
      (h : x ~> biproduct_obj (biproduct y z)) :
  h ≈ biproduct_fork f g
    ↔ (bi_exl (biproduct y z) ∘ h ≈ f)
    ∧ (bi_exr (biproduct y z) ∘ h ≈ g).
Proof.
  split.
  - intro Hh.
    split.
    + rewrite Hh.
      apply bi_exl_pair.
    + rewrite Hh.
      apply bi_exr_pair.
  - intros [Hl Hr].
    symmetry.
    now apply bi_pair_unique.
Qed.

(* The chosen biproduct object, its two projections and the product-side
   mediator [bi_pair] assemble into a [Cartesian] structure directly. *)
Definition biproduct_Cartesian : @Cartesian C := {|
  product_obj := fun x y => biproduct_obj (biproduct x y);
  fork := @biproduct_fork;
  exl := fun x y => bi_exl (biproduct x y);
  exr := fun x y => bi_exr (biproduct x y);
  fork_respects := biproduct_fork_respects;
  ump_products := @biproduct_ump
|}.

(** ** The cocartesian structure *)

(* Dually — and this is the half Mac Lane's roster is about — the SAME
   object with the two injections and the copairing [bi_copair] is a
   cocartesian structure.  Recall that [Cocartesian C] is notation for
   [@Cartesian (C^op)] (Structure/Cocartesian.v:115), so the field names
   below are the product ones read in the opposite category: [product_obj]
   is the coproduct x + y, [exl]/[exr] are [inl]/[inr], [fork] is the
   copairing ▽, and [ump_products] arrives with its composition order
   flipped, reading [h ∘ inl ≈ f] and [h ∘ inr ≈ g] in C. *)
Definition biproduct_merge {x y z : C} (f : y ~> x) (g : z ~> x) :
  biproduct_obj (biproduct y z) ~> x :=
  bi_copair (biproduct y z) f g.

Lemma biproduct_merge_respects (x y z : C) :
  Proper (equiv ==> equiv ==> equiv) (@biproduct_merge x y z).
Proof. apply bi_copair_respects. Qed.

Lemma biproduct_coump {x y z : C} (f : y ~> x) (g : z ~> x)
      (h : biproduct_obj (biproduct y z) ~> x) :
  h ≈ biproduct_merge f g
    ↔ (h ∘ bi_inl (biproduct y z) ≈ f)
    ∧ (h ∘ bi_inr (biproduct y z) ≈ g).
Proof.
  split.
  - intro Hh.
    split.
    + rewrite Hh.
      apply bi_copair_inl.
    + rewrite Hh.
      apply bi_copair_inr.
  - intros [Hl Hr].
    symmetry.
    now apply bi_copair_unique.
Qed.

(* TWO ELABORATION HAZARDS, both met and both worth recording.

   (1) A [{| … |}] literal ascribed to [@Cocartesian C] is checked field by
   field before the ascription has forced the implicit category, and
   [product_obj]'s type [obj → obj → obj] unifies that category with [C] on
   sight — [obj[C^op]] and [obj[C]] being definitionally equal but not
   syntactically so.  Every later field is then checked at [C], and [fork]
   fails with its arrows pointing the wrong way.  Naming the constructor
   and its category, [@Build_Cartesian (C^op) …], fixes the orientation.

   (2) With the orientation fixed, the OPPOSITE hazard appears in
   [product_obj]'s body: [biproduct_obj] and [biproduct] have their
   category implicit ([Arguments biproduct_obj {C Z x y} _] and
   [Arguments biproduct {C Z _} x y]), so writing them unannotated at an
   expected result type of [obj[C^op]] resolves them AT [C^op], and the
   [fork] field is then checked against a different family of biproducts
   from the one [biproduct_merge] was built over.  The two are printed
   identically — [biproduct_obj (biproduct y z)] either way — so the error
   message is unreadable.  Spelling [@biproduct_obj C Z] and
   [@biproduct C Z B] out is what pins the family. *)
Definition biproduct_Cocartesian : @Cocartesian C :=
  @Build_Cartesian (C^op)
    (fun x y => @biproduct_obj C Z x y (@biproduct C Z B x y))
    (@biproduct_merge)
    (fun x y => @bi_inl C Z x y (@biproduct C Z B x y))
    (fun x y => @bi_inr C Z x y (@biproduct C Z B x y))
    biproduct_merge_respects
    (@biproduct_coump).

(** ** Strict identifications *)

(* The product object IS the biproduct object, on the nose. *)
Example biproduct_product_obj (x y : C) :
  @product_obj C biproduct_Cartesian x y = biproduct_obj (biproduct x y) :=
  eq_refl.

(* And so is the coproduct object. *)
Example biproduct_coprod_obj (x y : C) :
  @Coprod C biproduct_Cocartesian x y = biproduct_obj (biproduct x y) :=
  eq_refl.

(* Hence the binary product and the binary coproduct are the SAME object
   — the defining feature of a biproduct, as a conversion rather than as
   prose or as a constructed isomorphism. *)
Example biproduct_prod_is_coprod (x y : C) :
  @product_obj C biproduct_Cartesian x y
    = @Coprod C biproduct_Cocartesian x y :=
  eq_refl.

(* The two mediators are the biproduct's own, definitionally. *)
Example biproduct_fork_is_pair {x y z : C} (f : x ~> y) (g : x ~> z) :
  @fork C biproduct_Cartesian x y z f g = bi_pair (biproduct y z) f g :=
  eq_refl.

Example biproduct_merge_is_copair {x y z : C} (f : y ~> x) (g : z ~> x) :
  @merge C biproduct_Cocartesian x y z f g
    = bi_copair (biproduct y z) f g :=
  eq_refl.

(* As are the four structural morphisms. *)
Example biproduct_exl_is_bi_exl (x y : C) :
  @exl C biproduct_Cartesian x y = bi_exl (biproduct x y) := eq_refl.

Example biproduct_exr_is_bi_exr (x y : C) :
  @exr C biproduct_Cartesian x y = bi_exr (biproduct x y) := eq_refl.

Example biproduct_inl_is_bi_inl (x y : C) :
  @inl C biproduct_Cocartesian x y = bi_inl (biproduct x y) := eq_refl.

Example biproduct_inr_is_bi_inr (x y : C) :
  @inr C biproduct_Cocartesian x y = bi_inr (biproduct x y) := eq_refl.

End BiproductCartesian.

(** ** The round trip against Structure/Semiadditive.v *)

(* Structure/Semiadditive.v turns a preadditive category with binary
   products into one with biproducts.  Feeding it the products this file
   derives returns the original biproduct object and the original
   projections on the nose; the injections are rebuilt as forks and are
   recovered only up to [≈]. *)
Section BiproductRoundTrip.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.
Context `{B : @HasBiproducts C Z}.

Let Cart : @Cartesian C := biproduct_Cartesian.

Example biproduct_roundtrip_obj (x y : C) :
  biproduct_obj
    (@cartesian_biproduct C Z P Cart x y) = biproduct_obj (biproduct x y) :=
  eq_refl.

Example biproduct_roundtrip_exl (x y : C) :
  bi_exl (@cartesian_biproduct C Z P Cart x y) = bi_exl (biproduct x y) :=
  eq_refl.

Example biproduct_roundtrip_exr (x y : C) :
  bi_exr (@cartesian_biproduct C Z P Cart x y) = bi_exr (biproduct x y) :=
  eq_refl.

(* The injections come back only up to [≈]: the reconstruction defines
   them as [id △ 0] and [0 △ id], which are the original injections by the
   four interaction laws and product uniqueness, not by conversion. *)
Lemma biproduct_roundtrip_inl (x y : C) :
  bi_inl (@cartesian_biproduct C Z P Cart x y) ≈ bi_inl (biproduct x y).
Proof.
  exact (bi_pair_unique (biproduct x y) id zero_mor
           (bi_inl (biproduct x y))
           (bi_exl_inl (biproduct x y)) (bi_exr_inl (biproduct x y))).
Qed.

Lemma biproduct_roundtrip_inr (x y : C) :
  bi_inr (@cartesian_biproduct C Z P Cart x y) ≈ bi_inr (biproduct x y).
Proof.
  exact (bi_pair_unique (biproduct x y) zero_mor id
           (bi_inr (biproduct x y))
           (bi_exl_inr (biproduct x y)) (bi_exr_inr (biproduct x y))).
Qed.

End BiproductRoundTrip.
