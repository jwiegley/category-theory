Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.

Generalizable All Variables.

(** * The special initial-object theorem at two generic categories *)

(* nLab:      https://ncatlab.org/nlab/show/initial+object
   nLab:      https://ncatlab.org/nlab/show/well-powered+category

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   Theorem 1, book p. 128, applied through the remark under §V.8
   Definition 1, book p. 130: in a well-powered small-complete category
   the intersection hypothesis of the theorem is automatic.  This
   satellite applies Adjunction/SAFT/InitialObject.v's
   [special_initial_object_wellpowered] with every premise supplied in
   tree and no hypothesis left over, at two categories.

   THE POWERSET LATTICE [Subsets X] of a setoid [X] (Instance/
   Powerset.v).  It is complete by Instance/Powerset/WellPowered.v's
   [Subsets_Complete_free] and well-powered by its [Subsets_WellPowered]
   (Structure/WellPowered.v's [trivial_small], with the homs raised to
   the objects, [o <= u]).  Every family cogenerates it, because the
   category is thin: the conclusion [f ≈ g] of [cog_separates] is [True]
   by [eq_refl] (Instance/Powerset.v's [subsets_equiv_is_True]).  So the
   empty family ([Subsets_Cogenerator_empty]) and the one-member family
   on the bottom subset ([Subsets_Cogenerator_bot]) are both
   [Cogenerator]s, and [Subsets_special_initial] takes any.  Its object
   reads back by [eq_refl] as the domain of the wide-pullback
   intersection of all subobjects of [cogen_prod]
   ([Subsets_special_initial_obj]).  It is not degenerate: it is
   isomorphic to [Subsets_Initial]'s bottom subset
   ([Subsets_special_vs_bot], by Structure/Initial.v's
   [initial_unique]), it has no members
   ([Subsets_special_initial_is_empty]), and at a pointed [X] the top
   subset has no arrow into it ([Subsets_special_initial_not_top]).

   AN INDISCRETE CATEGORY OF TYPES, [Indiscrete@{o j j} Type@{j}] with
   [j < o] (Instance/Discrete/Reconstruct.v's [Indiscrete]), objects
   strictly above homs.  It is complete by Structure/WellPowered.v's
   [Indiscrete_Complete] at the object [unit], and well-powered by its
   [Indiscrete_WellPowered] with the index at [Set];
   [Indiscrete_Cogenerator_empty] is the empty family.  It is
   degenerate: every hom is [unit], so every object is initial, and
   [Indiscrete_types_special_initial_obj] reads the object back by
   [eq_refl] as [unit], the object the completeness witness chose.

   WHAT THE TWO WITNESS, AND WHAT THEY DO NOT.  At both, the least
   subobject is COMPUTED, as the wide pullback of Structure/
   WellPowered.v's [complete_intersection] over the small reindexed
   class, and not supplied from a known initial object.  Neither
   exercises [cog_separates]: in a thin category its conclusion holds
   outright, so [cogenerator_canonical_monic] proves a monicity that
   holds anyway.  A witness in which separation does work needs a
   category that is not thin, and none is here;
   Instance/Sets/SpecialInitial.v's [Sets^op] witness is one.

   UNIVERSES, measured with [Set Printing Universes. About …], stdlib
   bounds omitted:

     Subsets_special_initial@{o u t so …} : ∀ X : SetoidObject@{o o},
       Cogenerator@{so o u} (Subsets@{o u} X) → @Initial (Subsets@{o u} X)
       (* Set < o, o <= u, u < t, u <= so, … *)
     Indiscrete_types_special_initial@{j o t …} :
       @Initial (Indiscrete@{o j j} Type@{j})
       (* j < o, j < t, … *)

   [so] is [Complete]'s shape-object universe and the family's index
   universe, as in the theorem; it is bounded below by the hom universe
   [u], and [Subsets_special_initial_empty] keeps it apart from [u]:
   its block reads [u <= u3], [u3] being its instance of [so], and not
   an equation.  [Set < o] is inherited through [Subsets] from
   Instance/Sets/Powerset.v's [Powerset_Prop_obj], whose carrier is
   built from [Prop] ([About Powerset_Prop_obj] reads [Set < o]).

   WHY A SATELLITE.  Its closure is 139 files excluding itself, counted
   over .Makefile.coq.d, against Adjunction/SAFT/InitialObject.v's 110.
   The difference is that file itself and 28 more, every one of them in
   Instance/Powerset/WellPowered.v's closure (the set difference of the
   two closures, measured the same way): the powerset, preorder and
   poset files, and among what they bring the Yoneda, representable,
   F-algebra, category-of-elements, equivalence, sheaf, image and
   classifier files.  Both witnesses sit here, rather than one under
   Instance/Powerset/ and one in the theorem's file, so that the
   theorem's file carries neither.

   NOT DELIVERED.  No witness at a category that is not thin; no
   [Cogenerator] at [Sets] or [Sets^op] (Instance/Sets/Cogenerator.v and
   Instance/Sets/SpecialInitial.v build them); the zero arrow's normal
   form is not read back at either category.

   MEASUREMENTS.  Twelve constants ([Print Module]), no [Program]
   obligation; ten transparent and two [Qed] ([Subsets_special_initial_
   is_empty], [Subsets_special_initial_not_top]); each reports "Closed
   under the global context" by its fully qualified name. *)

(** ** The powerset lattice of a setoid *)

Definition Subsets_Cogenerator_empty@{o u +} (X : SetoidObject@{o o}) :
  Cogenerator (Subsets@{o u} X) :=
  @Build_Cogenerator (Subsets@{o u} X) Empty_set
    (fun e => match e with end) (fun _ _ _ _ _ => I).

Definition Subsets_Cogenerator_bot@{o u +} (X : SetoidObject@{o o}) :
  Cogenerator (Subsets@{o u} X) :=
  @Build_Cogenerator (Subsets@{o u} X) unit
    (fun _ => (subset_bot : obj[Subsets@{o u} X])) (fun _ _ _ _ _ => I).

Definition Subsets_special_initial@{o u t so +| o <= u, u < t, u <= so +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X)) :
  @Initial (Subsets@{o u} X) :=
  special_initial_object_wellpowered (Subsets_WellPowered@{o u t} X)
    (Subsets_Complete_free X : @Complete@{so so u o} (Subsets@{o u} X)) G.

Example Subsets_special_initial_obj@{o u t so d +|
    o <= u, u < t, u <= so, u < d +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X)) :
  @initial_obj _ (Subsets_special_initial X G)
    = Subobject.sub_dom
        (complete_intersection
           (Subsets_Complete_free X : @Complete@{so so u o} (Subsets@{o u} X))
           (wp_class_family
              (Subsets_WellPowered@{o u t} X
                 (cogen_prod@{so d so o u}
                    (Subsets_Complete_free X
                     : @Complete@{so so u o} (Subsets@{o u} X)) G))
              (fun _ => True))) :=
  eq_refl.

Definition Subsets_special_initial_empty@{o u t +| o <= u, u < t +}
  (X : SetoidObject@{o o}) : @Initial (Subsets@{o u} X) :=
  Subsets_special_initial X (Subsets_Cogenerator_empty X).

Definition Subsets_special_initial_bot@{o u t +| o <= u, u < t +}
  (X : SetoidObject@{o o}) : @Initial (Subsets@{o u} X) :=
  Subsets_special_initial X (Subsets_Cogenerator_bot X).

Definition Subsets_special_vs_bot@{o u t so +| o <= u, u < t, u <= so +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X)) :
  @initial_obj _ (Subsets_special_initial X G)
    ≅ @initial_obj _ (Subsets_Initial (X:=X)) :=
  initial_unique _ _.

Lemma Subsets_special_initial_is_empty@{o u t so +| o <= u, u < t, u <= so +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X))
  (x : carrier X) :
  (@initial_obj _ (Subsets_special_initial X G)
     : carrier (Powerset_Prop_obj X)) x → False.
Proof.
  intro Hx.
  destruct (to (Subsets_special_vs_bot X G) x Hx) as [i _]; destruct i.
Qed.

Lemma Subsets_special_initial_not_top@{o u t so +| o <= u, u < t, u <= so +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X))
  (x : carrier X) :
  ((subset_top : obj[Subsets@{o u} X])
     ~{Subsets@{o u} X}~> @initial_obj _ (Subsets_special_initial X G))
  → False.
Proof.
  intro k.
  exact (Subsets_special_initial_is_empty X G x
           (k x (fun i => match i with end))).
Qed.

(** ** An indiscrete category of types *)

Definition Indiscrete_Cogenerator_empty@{o h +} (A : Type@{o}) :
  Cogenerator (Indiscrete@{o h h} A) :=
  @Build_Cogenerator (Indiscrete@{o h h} A) Empty_set
    (fun e => match e with end)
    (fun x y f g _ => match f, g with tt, tt => eq_refl end).

Definition Indiscrete_types_special_initial@{j o t +| j < o, j < t +} :
  @Initial (Indiscrete@{o j j} Type@{j}) :=
  special_initial_object_wellpowered
    (Indiscrete_WellPowered@{o j Set o t} Type@{j})
    (Indiscrete_Complete@{j j j o} (Datatypes.unit : Type@{j}))
    (Indiscrete_Cogenerator_empty Type@{j}).

Example Indiscrete_types_special_initial_obj@{j o t +| j < o, j < t +} :
  @initial_obj (Indiscrete@{o j j} Type@{j}) Indiscrete_types_special_initial
    = (Datatypes.unit : Type@{j}) :=
  eq_refl.
