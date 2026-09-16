Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(* The single-object separator, reconciled with Theory/Concrete.v

   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/well-pointed+category

   Issue #447 recorded as its verified current state that the tree
   carried no separating vocabulary at all, only the dual [Cogenerator]
   of Adjunction/SAFT.v:99.  That was STALE.  Measured in this worktree
   with grep -rn 'Separator' --include='*.v', Theory/Concrete.v has
   carried Awodey's single-object notion since the concreteness
   development landed:

     :174  Class Separator (t : C), the same clause as [IsSeparator]
           with the two objects implicit, presented as a one-field class
           so that instance resolution can find it;
     :183  Concrete_of_Separator, which turns a separator into a
           concrete structure whose underlying functor is Hom(t, -) --
           and whose [underlying_faithful] obligation IS the forward
           half of Awodey's characterization, proved but not named;
     :197  Separator_of_Faithful, the backward half, named and proved;
     :218  WellPointedCategory C, the separator condition at the
           terminal object (Awodey's own case, global elements);
     :279  Sets_Separator, the witness the issue asks for -- the
           terminal object of [Sets] separates -- with :287
           [Sets_WellPointed] and :299 [Sets_empty_not_Separator], the
           refutation keeping the class from reading as content-free.

   So this issue's genuinely new material is the FAMILY notion
   ([Generator]), the joint-faithfulness characterization in both
   directions, the transport lemmas, and the duality bridge -- all in
   Structure/Generator.v and Structure/Generator/Dual.v.  What is left
   is to keep the tree from ending with two unrelated spellings of one
   condition, and that is this file: the two bridges below are both
   [:=] terms, since [Separator]'s field and [IsSeparator]'s body differ
   only in which arguments are implicit.

   WHY A THIRD FILE, MEASURED.  Structure/Generator.v does NOT require
   Theory/Concrete.v, and the reason is a name clash that would
   otherwise be imposed on every later file: [bool_setoid_object] is
   defined twice in the tree, at Instance/Sets.v:569 and at
   Theory/Concrete.v:244 (two different [SetoidObject] terms for the
   two-element setoid), so importing Concrete after Sets shadows the
   Sets one.  Structure/Generator.v imports Instance/Sets.v and is the
   interface the witnesses for this issue are built against, so the
   shadowing is contained here instead, where nothing uses either
   spelling.  The same isolation argument as Structure/Generator/Dual.v,
   for a different hazard.

   UNIVERSES, measured with [Set Printing Universes. About ...].  The
   two bridges carry only [u <= u1] and [u0 <= u1], the bound by which
   [IsSeparator]'s result level dominates the category's two levels;
   [Separator] itself (Theory/Concrete.v:174) prints an EMPTY block.
   No constant here is pinned to [Set].

   NOT DELIVERED.  No witness: this file builds no separator of any
   category.  The [Sets] witness is Instance/Sets/Generator.v, which
   proves the terminal-object statement directly and ALSO reads
   Theory/Concrete.v:279's [Sets_Separator] through
   [IsSeparator_of_Separator] as [Sets_terminal_separates_from_Concrete]
   (a first draft of this file carried that read-through itself, under
   the names [Sets_terminal_IsSeparator] / [Sets_terminal_Generator],
   which collided with the witness file's own [Sets_terminal_Generator];
   integration kept the witness file's).  No statement about
   [Concrete] itself: nothing here says a category with a separating
   FAMILY is concrete (it is not, in general -- a family of
   representables is jointly faithful, which is weaker than any single
   functor to [Sets] being faithful, and the coproduct that would
   assemble them is unsound for this purpose, as Structure/Generator.v's
   header records).  No instance declarations: the bridges are plain
   definitions, so declaring an [IsSeparator] does not make
   [Separator]'s instance resolution fire, and vice versa. *)

Section Bridge.

Context {C : Category}.

(** ** The two spellings of Awodey's condition *)

(* [Separator] (Theory/Concrete.v:174) is the class form, whose field
   [separates] takes its two objects implicitly; [IsSeparator]
   (Structure/Generator.v) is the Type-valued form that the
   characterizations consume as a function.  Nothing moves but the
   packaging. *)
Definition Separator_of_IsSeparator (c : C) (H : IsSeparator c) :
  Separator c := @Build_Separator C c (fun x y f g E => H x y f g E).

Definition IsSeparator_of_Separator (c : C) (S : Separator c) :
  IsSeparator c := fun x y f g E => @separates C c S x y f g E.

(* The forward half of Awodey's characterization is already in the tree,
   though only as the [underlying_faithful] obligation of
   Theory/Concrete.v:183's concretization.  Recovering it that way gives
   the same statement as Structure/Generator.v's [separator_faithful],
   and this is the check that the two developments agree. *)
Example separator_faithful_via_concrete (c : C) (H : IsSeparator c) :
  Faithful [Hom c,─] :=
  @underlying_faithful C
    (@Concrete_of_Separator C c (Separator_of_IsSeparator c H)).

End Bridge.
