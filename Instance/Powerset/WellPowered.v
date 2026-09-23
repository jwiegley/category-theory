Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(** * The intersection theorem at the powerset lattice of a setoid *)

(* nLab:      https://ncatlab.org/nlab/show/well-powered+category
   nLab:      https://ncatlab.org/nlab/show/power+set
   Wikipedia: https://en.wikipedia.org/wiki/Power_set

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   book p. 130: a well-powered complete category has the intersection of
   any collection of subobjects of an object.  Structure/WellPowered.v
   proves that as [wellpowered_complete_has_intersections] and its
   [Prop]-class form [wellpowered_complete_has_intersections_prop].  This
   file instantiates it, unconditionally, at a complete category whose
   subobject lattices are NOT degenerate: Instance/Powerset.v's [Subsets X],
   the subsets of a setoid [X] under inclusion.  It is a satellite so that
   Structure/ does not import Instance/Powerset.v.

   WHAT IS DELIVERED.

     - [Subsets_Complete_free X : Complete (Subsets@{o u} X)], at a FREE
       hom level [u].  It is Instance/Powerset.v's [Subsets_Complete] with
       the literal [Set] of that file's hom slot left open: the same term,
       [snd (proset_Complete_iff_all_meets (subset_le_preorder X))
       Subsets_HasAllMeets].  That file's comment on [Subsets_Complete]
       records that the [Set] there became a choice once
       Instance/Discrete.v was annotated, and that the restatement was not
       attempted; this is the restatement, measured below.
     - [Subsets_WellPowered X : WellPowered (Subsets@{o u} X)] for
       [o <= u], by Structure/WellPowered.v's [trivial_small]: the objects
       of [Subsets@{o u} X] sit at [o], at or below the homs.
     - [Subsets_has_intersections] and [Subsets_intersection_all]: the
       consequence at [Subsets X], for every ≈-closed [Prop]-class of
       subobjects and for the class of all subobjects.
     - [Subsets_intersection_all_not_top]: the intersection of ALL
       subobjects of the full subset [subset_top] is not the top subobject
       as soon as [X] has a point, because the subobject named by the empty
       subset ([subsets_sub_bot]) is a member of the class and is not the
       top.  So the theorem is exercised at a lattice with at least two
       distinct subobjects, where Structure/WellPowered.v's
       [Indiscrete_types_has_intersections] has only one.

   UNIVERSES, measured with [Set Printing Universes. About ...], stdlib
   bounds omitted:

     Subsets_Complete_free@{o u ...} :
       ∀ X : SetoidObject@{o o}, Complete@{u0 u1 u o}
       (* Set < o, u <= u0, u1 <= u0, and bounds on internal universes *)
     Subsets_WellPowered@{o u t} :
       ∀ X, WellPowered@{o u u u t} (Subsets@{o u} X)
       (* Set < o, u < t, o <= u *)

   [Subsets_Complete_free] bounds the hom level [u] only by [Complete]'s
   first slot [u0] and by universes internal to the proof, never by [o],
   so completeness holds at every [u]; the well-poweredness witness, and
   with it the consequence, needs [o <= u].  [Set < o] comes from
   [Prop]-valued subsets.

   WHAT THIS DOES NOT SHOW.  Well-poweredness is the trivial kind here:
   the objects sit at or below the homs, so [trivial_small] indexes the
   subobjects by themselves.  Of the instances of the consequence in
   tree, none has BOTH objects strictly above homs AND a non-degenerate
   subobject lattice unconditionally: Structure/WellPowered.v's
   [Indiscrete_types_has_intersections] has objects above homs and one
   subobject per object, this file has the reverse, and Instance/Sets/
   WellPowered.v's [Sets_wellpowered_intersection] has both but takes
   [Untruncate].

   MEASUREMENTS.  Six constants ([.glob] heads), no [Program] obligation;
   five transparent definitions and one [Qed] refutation
   ([Subsets_intersection_all_not_top]); each reports "Closed under the
   global context" by its fully qualified name.  Closure 132 files
   excluding itself, counted over .Makefile.coq.d; Instance/Powerset.v's
   is 87, and the difference is Structure/WellPowered.v's development. *)

Definition Subsets_Complete_free@{o u +} (X : SetoidObject@{o o}) :
  @Complete (Subsets@{o u} X) :=
  snd (proset_Complete_iff_all_meets (subset_le_preorder@{o} X))
    Subsets_HasAllMeets.

Definition Subsets_WellPowered@{o u t | o <= u, u < t +}
  (X : SetoidObject@{o o}) : WellPowered@{o u u u t} (Subsets@{o u} X) :=
  trivial_small _.

(* The consequence at [Subsets X], for a [Prop]-class of subobjects. *)
Definition Subsets_has_intersections@{o u +} (X : SetoidObject@{o o})
  (S : Subsets@{o u} X) (P : SubObj S → Prop)
  (HP : ∀ m m' : SubObj S, m ≈ m' → P m → P m') :
  { w : SubObj S &
    IsIntersection (fun k : { m : SubObj S & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections_prop
    (Subsets_WellPowered X) (Subsets_Complete_free X) S P HP.

(* The class of all subobjects. *)
Definition Subsets_intersection_all@{o u +} (X : SetoidObject@{o o})
  (S : Subsets@{o u} X) :
  { w : SubObj S & IsIntersection (fun m : SubObj S => m) w } :=
  wellpowered_complete_intersection_all
    (Subsets_WellPowered X) (Subsets_Complete_free X) S.

(* The empty subset, as a subobject of the full one.  Every arrow of
   [Subsets X] is monic, the category being thin. *)
Definition subsets_sub_bot@{o u +} (X : SetoidObject@{o o}) :
  @SubObj (Subsets@{o u} X) subset_top :=
  {| sub_dom := (subset_bot : obj[Subsets@{o u} X]);
     sub_mono := (subset_bot_least subset_top
                    : subset_bot ~{Subsets@{o u} X}~> subset_top);
     sub_is_monic := @Build_Monic (Subsets@{o u} X) _ _
                       (subset_bot_least subset_top) (fun _ _ _ _ => I) |}.

(* Non-degeneracy: at a pointed [X], the intersection of all subobjects of
   the full subset lies below [subsets_sub_bot], so it is not the top. *)
Lemma Subsets_intersection_all_not_top@{o u +} (X : SetoidObject@{o o})
  (x : carrier X) :
  `1 (Subsets_intersection_all X (subset_top : obj[Subsets@{o u} X]))
    ≈ sub_top → False.
Proof.
  intros [iso _].
  destruct (inter_le _ _
              (`2 (Subsets_intersection_all X
                     (subset_top : obj[Subsets@{o u} X])))
              (subsets_sub_bot X)) as [k _].
  destruct (k x (from iso x (fun i => match i with end))) as [i _].
  destruct i.
Qed.
