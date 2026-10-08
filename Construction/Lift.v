Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** * A category read at higher universe levels *)

(* nLab: https://ncatlab.org/nlab/show/universe+enlargement (the general
   notion, a category of one universe re-read in a larger one; this file
   is its trivial case, the same category with nothing improved)

   WHY IT IS NEEDED.  [Category@{o h p}] is a record, and the tree's
   records are not cumulative (Instance/Sets/Classifier.v's
   [Setoid_Lift] says so of setoid objects and rebuilds them;
   Structure/Pullback/Wide/Complete.v says so of the category record): a
   [C : Category@{co ch ch}] is not itself a [Category@{xo xh xh}] when
   co < xo or ch < xh, although its objects, arrows and ≈ re-typecheck at
   the higher levels.  A statement that quantifies over every category at
   the levels (xo, xh), such as Structure/Coequalizer/Absolute.v's
   [AbsoluteCoequalizer] and Structure/Limit/Absolute.v's
   [AbsoluteLimitCone], therefore cannot be applied to C itself, nor to a
   category below (xo, xh); it can be applied to the rebuild, and that is
   what makes those predicates downward closed (#477).

   WHAT IS HERE.
     - [LiftCat C]: C rebuilt as a [Category@{xo xh xh}], with C's
       objects, arrows, ≈, identities and composites, and every law C's
       own.  The [Equivalence] and [Proper] fields are repacked, those
       records not being cumulative either.
     - [Lift_in C : C ⟶ LiftCat C], the identity on objects and on
       arrows on the nose ([Lift_in_fobj], [Lift_in_fmap], at [eq_refl]).
     - [Lift_after T : C ⟶ LiftCat X] for [T : C ⟶ X]: T read into the
       rebuild of X, with T's actions on the nose ([Lift_after_fobj],
       [Lift_after_fmap], at [eq_refl]).  In every datum it is
       [Lift_in X ◯ T], but Theory/Functor.v's [Compose] gives its three
       categories one hom level, so [Lift_in X ◯ T] cannot be formed when
       the lift's hom level is strictly above X's (refused in
       Test/ProbeAbsolute477.v); [Lift_after] is built directly.

   UNIVERSES, by [About].  [LiftCat@{co ch xo xh}] is over
   [C : Category@{co ch ch}] and returns a [Category@{xo xh xh}] under
   the constraints "co <= xo" and "ch <= xh" and no other, and
   [Lift_in@{co ch xo xh}] and its two readbacks carry the same two.
   [Lift_after@{co ch xo xh yo yh}] lifts [X : Category@{xo xh xh}] to
   [@{yo yh}] under "ch <= xh" (from [T] itself), "ch <= yh",
   "xo <= yo" and "xh <= yh", and its two readbacks the same four.  No
   block carries an equation.  The statements of [Lift_in], [Lift_after]
   and the four readbacks name the instance of the lift they speak of
   (six explicit universe instances of this file's constants): a lifted
   level is bounded below alone, and minimization would otherwise set
   it to the level it lifts.

   NOT DELIVERED.  No functor back from [LiftCat C] to C once the hom
   level is lifted: at "ch < xh" the type [LiftCat C ⟶ C] is itself
   refused ("Cannot enforce ch = …", Test/ProbeAbsolute477.v), since
   [Functor]'s [fmap_respects] is typed through [respectful] at the
   target's levels and so bounds the source's hom level by the
   target's; with the objects lifted alone the way back is formable.
   No lift of the proof level apart from the hom level.  Nothing about
   structure that [LiftCat] preserves or reflects beyond what its
   consumers in Structure/Limit/Absolute.v and Structure/Coequalizer/
   Absolute.v use, which is that its arrows, ≈ and composites are C's. *)

Definition LiftCat@{co ch xo xh +} (C : Category@{co ch ch}) :
  Category@{xo xh xh}.
Proof.
  unshelve refine
    {| obj := @obj C;
       hom := fun x y => @hom C x y;
       homset := fun x y =>
         {| equiv := fun f g => @equiv _ (@homset C x y) f g;
            setoid_equiv := _ |};
       id := fun x => @id C x;
       compose := fun x y z f g => @compose C x y z f g |}.
  - constructor.
    + intro f.
      exact (@Equivalence_Reflexive _ _ (@setoid_equiv _ (@homset C x y)) f).
    + intros f g H.
      exact (@Equivalence_Symmetric _ _ (@setoid_equiv _ (@homset C x y))
               f g H).
    + intros f g h H1 H2.
      exact (@Equivalence_Transitive _ _ (@setoid_equiv _ (@homset C x y))
               f g h H1 H2).
  - intros x y z f f2 Hf g g2 Hg.
    exact (@compose_respects C x y z f f2 Hf g g2 Hg).
  - intros x y f. exact (@id_left C x y f).
  - intros x y f. exact (@id_right C x y f).
  - intros x y z w f g h. exact (@comp_assoc C x y z w f g h).
  - intros x y z w f g h. exact (@comp_assoc_sym C x y z w f g h).
Defined.

Definition Lift_in@{co ch xo xh +} (C : Category@{co ch ch}) :
  C ⟶ LiftCat@{co ch xo xh} C.
Proof.
  unshelve refine (@Build_Functor C (LiftCat C)
    (fun x : C => x) (fun (x y : C) (f : x ~{C}~> y) => f) _ _ _).
  - intros x y f g H. exact H.
  - intros x. simpl. reflexivity.
  - intros x y z f g. simpl. reflexivity.
Defined.

Example Lift_in_fobj@{co ch xo xh +} (C : Category@{co ch ch}) (x : C) :
  fobj[Lift_in@{co ch xo xh} C] x = x := eq_refl.

Example Lift_in_fmap@{co ch xo xh +} (C : Category@{co ch ch}) {x y : C}
  (f : x ~{C}~> y) : fmap[Lift_in@{co ch xo xh} C] f = f := eq_refl.

Definition Lift_after@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X) :
  C ⟶ LiftCat@{xo xh yo yh} X.
Proof.
  unshelve refine (@Build_Functor C (LiftCat X)
    (fun x : C => T x) (fun (x y : C) (f : x ~{C}~> y) => fmap[T] f)
    _ _ _).
  - intros x y f g H. exact (@fmap_respects _ _ T x y f g H).
  - intros x. exact (@fmap_id _ _ T x).
  - intros x y z f g. exact (@fmap_comp _ _ T x y z f g).
Defined.

Example Lift_after_fobj@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X) (x : C) :
  fobj[Lift_after@{co ch xo xh yo yh} T] x = T x := eq_refl.

Example Lift_after_fmap@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X)
  {x y : C} (f : x ~{C}~> y) :
  fmap[Lift_after@{co ch xo xh yo yh} T] f = fmap[T] f := eq_refl.
