Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(* Separating and coseparating families are one notion read twice

   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/cogenerator

   Riehl, "Category Theory in Context", 2nd ed., Definition 4.7.7
   (printed p. 177, PDF p. 197), defines a COSEPARATING set to be a
   separating set in the opposite category, and Mac Lane's §V.7 (book
   p. 127) pairs the two the same way.  This file is that sentence,
   discharged in both directions, plus the joint-faithfulness reading
   that Adjunction/SAFT.v states as prose and proves nowhere.

   WHY A SEPARATE FILE.  Adjunction/SAFT.v sits high in the tree: it
   requires Structure/Complete.v, Structure/Limit/Product.v,
   Construction/Comma/Limit.v and Adjunction/GAFT.v.  Structure/
   Generator.v is a definition file and must stay near the bottom, so
   the bridge to [Cogenerator] lives here instead, and nothing that
   wants only the covariant notion pays for SAFT's closure.

   THE DATA IS THE SAME, THE QUANTIFIERS ARE SWAPPED.  Construction/
   Opposite.v gives [hom x y := hom y x] and
   [compose f g := g ∘ f], both DEFINITIONALLY, so a [Cogenerator
   (C^op)] holds exactly a [Generator C]'s three fields: an index Type,
   the same objects, and a separation clause whose hypothesis
   [∀ j (k : y ~{C^op}~> cog_obj j), k ∘[C^op] f ≈ k ∘[C^op] g] IS
   [∀ j (k : cog_obj j ~> y), f ∘ k ≈ g ∘ k] in C.  What does NOT match
   up on its own is the NAMING of the two object variables: the
   cogenerating clause quantifies (x, y) where the generating clause
   quantifies (y, x), so the bridge must apply the field with the two
   arguments exchanged.  With the exchange, both directions are terms,
   and both round trips hold at [eq_refl] -- record eta with primitive
   projections (Lib.v's flag), plus function eta on the separation
   field, is enough, and no tactic is used.

   TWO SPELLINGS THAT ARE REFUSED, both measured in this worktree with
   the same requirement list.  (1) The naive bridge, without the
   exchange:
     Definition gen_of_cog_naive (G : Cogenerator (C^op)) : Generator C
       := @Build_Generator C (cog_index G) (cog_obj G)
            (@cog_separates (C^op) G).
   is rejected with
     "(cannot unify "x ~{ C }~> y" and "x ~{ C^op }~> y")",
   a CONVERSION refusal: the field is applied at the objects in the
   order the record declares them, and that order is the opposite one.
   (2) The record-builder syntax without an explicit category:
     {| gen_index := cog_index G; gen_obj := cog_obj G; ... |}
   infers [Generator]'s implicit category from the first field that
   fixes it -- [gen_obj := cog_obj G] has type [cog_index G -> C^op] --
   and so builds a [Generator (C^op)], after which every remaining
   field is checked in the wrong category and the separation field is
   rejected with
     "The term "f" has type "x ~{ C^op }~> y" while it is expected to
      have type "y ~{ C^op }~> x"".
   Hence [@Build_Generator C] and [@Build_Cogenerator (C^op)] are
   written out explicitly below.  (This is the same builder trap the
   tree has met before, and the fix is the same: name the record's
   parameter rather than letting a [C^op]-typed field choose it.)

   THE TYPES ARE NOT EQUAL, AND THE ROUND TRIPS DO NOT SAY THEY ARE.
   [Generator C] and [Cogenerator (C^op)] are two distinct inductives
   carrying the same data; [Generator C = Cogenerator (C^op)] at
   [eq_refl] is REFUSED --
     "The term "eq_refl" has type "Generator C = Generator C" while it
      is expected to have type "Generator C = Cogenerator C^op"
      (cannot unify "Generator C" and "Cogenerator C^op")" --
   which is why this file carries a pair of maps and the two [eq_refl]
   round trips rather than one equation of types.  That is the strongest
   statement available here, and it is stronger than an isomorphism: the
   composites are the identity on the nose, not up to anything.

   THE DUAL CHARACTERIZATION.  [cogenerator_jointly_faithful] and
   [jointly_faithful_cogenerator] discharge the SAFT header's prose,
   "equivalently the representables C(-, cog_obj j) are jointly
   faithful", in both directions.  The functors are Functor/Hom.v's
   [Curried_CoHom C], written [Hom ─, A]; each is a functor C^op ⟶ Sets,
   so [JointlyFaithful] is instantiated at C^op and its two arrow
   variables are C^op arrows -- which is exactly why the proof term
   applies [cog_separates] with the objects exchanged, the same
   bookkeeping as the [Generator] bridge above.  Like the covariant
   characterization in Structure/Generator.v, both directions are terms:
   the Sets hom-setoid is pointwise (Instance/Sets.v) and the
   [fmap] of a contravariant representable is precomposition, so the
   two hypotheses are the same statement.

   UNIVERSES, measured with [Set Printing Universes. About ...].  The
   four bridges are free of constraints: [gen_of_cog], [cog_of_gen],
   [gen_op_of_cog] and [cog_of_gen_op] each print an EMPTY block, which
   is the universe-level statement that no data moves.  The two
   characterizations carry the block that Instance/Sets.v's
   [Sets@{o so} : Category@{so o o}] carries -- the strict [u0 < u2]
   ([u0 < u3] for [jointly_faithful_cogenerator], where the level is
   numbered differently) together with [u0 <= compose.u0/u1/u2] and
   [u0 <= ID.u0] -- inherited through the hom-functor, plus the ≤-bounds
   [JointlyFaithful] and [Cogenerator] contribute themselves, the same
   shape as their covariant counterparts in Structure/Generator.v (an
   earlier revision of this sentence said "exactly the Sets block", which
   an audit measured as short by those inherited bounds).  Every
   constant here binds its category as [Category@{_ u0 u0}], the hom
   level identified with the proof level, and none is pinned to [Set].

   NOT DELIVERED.  No cogenerating example: this file exhibits no
   [Cogenerator] of any concrete category, and SAFT.v's consumers all
   take one as data.  No transport lemmas on the dual side -- the
   [separator_iso] / [gen_family_mono] / [gen_extend] trio of
   Structure/Generator.v is NOT mirrored for [Cogenerator], although
   each mirror is one line through the two bridges below.  No change to
   Adjunction/SAFT.v beyond a pointer in its header comment: the record,
   its [Arguments], and [cogenerator_canonical_monic] are untouched, and
   in particular [Cogenerator] is NOT redefined as [Generator (C^op)],
   which would have altered a file with live consumers. *)

Section Dual.

Context {C : Category}.

(** ** A cogenerating family of C^op IS a generating family of C *)

Definition gen_of_cog (G : Cogenerator (C^op)) : Generator C :=
  @Build_Generator C (cog_index G) (cog_obj G)
    (fun x y f g H => @cog_separates (C^op) G y x f g H).

Definition cog_of_gen (G : Generator C) : Cogenerator (C^op) :=
  @Build_Cogenerator (C^op) (gen_index G) (gen_obj G)
    (fun x y f g H => @gen_separates C G y x f g H).

(* Both round trips are the identity on the nose. *)
Example gen_of_cog_of_gen (G : Generator C) :
  gen_of_cog (cog_of_gen G) = G := eq_refl.

Example cog_of_gen_of_cog (G : Cogenerator (C^op)) :
  cog_of_gen (gen_of_cog G) = G := eq_refl.

(** ** The reading the SAFT header states as prose, proved both ways *)

Definition cogenerator_jointly_faithful (G : Cogenerator C) :
  JointlyFaithful (fun j : cog_index G => [Hom ─, cog_obj G j]) :=
  fun x y f g H => cog_separates G f g (fun j k => H j k).

Definition jointly_faithful_cogenerator {J : Type} (F : J -> C)
  (H : JointlyFaithful (fun j : J => [Hom ─, F j])) : Cogenerator C :=
  @Build_Cogenerator C J F (fun x y f g Hk => H y x f g (fun j k => Hk j k)).

End Dual.

(* The same pair of bridges read at the other orientation, which costs
   nothing because C^op^op is C by conversion (Construction/Opposite.v,
   the duality discipline CLAUDE.md describes).  These sit OUTSIDE the
   section above: inside it the category is a section variable and the
   two bridges cannot be instantiated at C^op until it is discharged. *)
Definition gen_op_of_cog {C : Category} (G : Cogenerator C) :
  Generator (C^op) := @gen_of_cog (C^op) G.

Definition cog_of_gen_op {C : Category} (G : Generator (C^op)) :
  Cogenerator C := @cog_of_gen (C^op) G.
