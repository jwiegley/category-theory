Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.

Generalizable All Variables.

(* The special initial-object theorem at [Sets^op] and at [Sets]

   nLab:  https://ncatlab.org/nlab/show/initial+object
   nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.8, Theorem 1, book p. 128 (PDF pp. 137–138): a small-complete
   category with small hom-sets, a small cogenerating set, and an
   intersection for every set of subobjects of each object has an initial
   object, the intersection of all subobjects of the product of the
   cogenerating set.  Riehl, "Category Theory in Context", 2nd ed., Lemma
   4.7.11, printed p. 177 (PDF pp. 197–198), states the same for a locally
   small complete category with a small coseparating set.  Mac Lane's note
   under §V.8 Definition 1, book p. 130 (PDF p. 139), makes the
   intersection hypothesis automatic for a well-powered small-complete
   category.  Adjunction/SAFT/InitialObject.v proves the theorem over an
   arbitrary category in three hypothesis forms and that corollary; this
   file runs it at the two categories of setoids for which the tree can
   supply the hypotheses, and reads what it returns against the initial
   object each category is already known to have.

   WHAT IS CONSUMED AND BUILT.

   (1) [Sets^op], unconditionally.  Completeness is
       Construction/Product/Limit.v's [Complete_op_of_Cocomplete] of
       Instance/Sets/Cocomplete.v's [Sets_Cocomplete] ([setsop_comp]).  The
       cogenerator is Structure/Generator/Dual.v's [cog_of_gen] of
       Instance/Sets/Generator.v's [Sets_Generator], the singleton
       ([setsop_cog]).  It is a genuine separator of a category that is
       not thin (Theory/Concrete.v's [Sets_two_arrows]), so [cog_separates]
       does real work where the theorem's existence half consumes it,
       inside Adjunction/SAFT.v's [cogenerator_canonical_monic].  The
       least subobject of the cogenerator product [P] is built by hand:
       [setsop_L] is the map [P → 1] into Instance/Sets.v's
       [Sets_Terminal] object, read in [Sets^op] as a mono [1 ↣ P].
       Monicity in [Sets^op] is epicity of [P → 1] in [Sets], which needs
       a point of [P]; [setsop_point] is the coprojection of the one
       element of the singleton factor.  [setsop_L_least] shows every
       subobject of [P] in [Sets^op] lies above it, since all arrows into
       [1] agree.  [setsop_special_initial] is the headline
       [special_initial_object], fed through [intersection_all_of_least].
       [setsop_terminal_IsInitialObj] states the conclusion in the type:
       the singleton is initial in [Sets^op].

   (2) [Sets], under [Untruncate], in three ways, the one hypothesis [U]
       supplying the cogenerator (Instance/Sets/Cogenerator.v's
       [Sets_Cogenerator_untruncate]) and whatever else is needed.
       (a) The least subobject: Theory/Subobject/Lattice.v's [sub_bot] at
           Instance/Sets/SubobjectLattice.v's [Sets_zero_monic], least by
           [sub_bot_least] ([sets_special_initial_untruncate]).
       (b) The well-powered corollary: [special_initial_object_wellpowered]
           with Instance/Sets/WellPowered.v's [Sets_WellPowered_untruncate]
           (#451) ([sets_special_initial_wellpowered]).
       (c) The book's blanket hypothesis: Instance/Sets/WellPowered.v's
           [Sets_wellpowered_intersection] is, as it stands, an inhabitant
           of [HasClassIntersections] at [Sets]
           ([Sets_HasClassIntersections_untruncate] is its eta-expansion),
           and [special_initial_object_book] consumes it
           ([sets_special_initial_book]).

   (3) [Sets], under [IEM], through the least subobject, with
       Instance/Sets/Cogenerator.v's [Sets_Cogenerator_IEM]
       ([sets_special_initial_IEM]).  [sets_special_initial_IEM_at_Set]
       is the instance at carrier universe [Set], accepted.

   THE CIRCULARITY CAVEAT.  In (1), (2a) and (3) the least subobject
   handed to the theorem is BUILT FROM the known initial object: the
   domain of [sub_bot] is [Sets_Initial]'s empty setoid, the domain of
   [setsop_L] is [Sets_Terminal]'s singleton.  The theorem then
   rediscovers that object, and the [eq_refl] readbacks below say exactly
   that and no more.  What those three witnesses exercise is the rest of
   the machinery: completeness, the cogenerator product, the canonical
   monic and with it [cog_separates], the pullbacks of the existence half
   and the equalizer argument of the uniqueness half.  Only (2b) and (2c)
   COMPUTE the least subobject, as an intersection: (2b) as
   Structure/WellPowered.v's [complete_intersection] of the well-powered
   class family, (2c) as Instance/Sets/WellPowered.v's wide pullback over
   a small reindexing of the class.  There the comparison with the known
   initial object is [initial_unique], not [eq_refl].

   STRENGTHS, strict first.
     - [eq_refl], the object IS the known initial object:
       [setsop_special_obj] (the initial object of [Sets^op] returned is
       [@terminal_obj Sets Sets_Terminal]), [sets_special_untruncate_obj]
       and [sets_special_IEM_obj] (it is [@initial_obj Sets Sets_Initial]).
       Test/ProbeSpecialInitial452.v's N17 and N18 show that the first
       and last of these discriminate: with the two objects swapped each
       is refused by conversion ([p452_n17_setsop_obj_empty],
       [p452_n18_sets_iem_obj_singleton]).
     - [eq_refl], the object IS the intersection:
       [sets_special_wellpowered_obj], against
       [Subobject.sub_dom (complete_intersection Sets_Complete
       (wp_class_family (Sets_WellPowered_untruncate U (cogen_prod …))
       (fun _ => True)))], and [sets_special_book_obj], against
       [Subobject.sub_dom (`1 (Sets_wellpowered_intersection U
       (cogen_prod …) (fun _ => unit) (fun _ _ _ t => t)))].
     - [≅], by Structure/Initial.v's [initial_unique]:
       [setsop_special_vs_known] (against [Sets_Terminal] read as an
       [@Initial (Sets^op)], which it is by conversion, since
       [Initial C := @Terminal (C^op)] and [C^op^op] is [C]),
       [sets_special_wellpowered_vs_known] and [sets_special_book_vs_known]
       (against [Sets_Initial]).
     - A theorem: [sets_special_wellpowered_empty], the intersection the
       corollary computes has no elements, read off its own zero arrow
       into [Sets_Initial]'s object.
   Every constant here is closed under the global context (Print
   Assumptions on each); [Untruncate] and [IEM] are hypotheses, not
   axioms.

   UNIVERSES, measured with [Set Printing Universes. About …] against the
   integrated Adjunction/SAFT/InitialObject.v, stdlib bounds left out:

     setsop_special_initial@{o so u} : @Initial Sets@{o so}^op
       (* o < so, so < u *)
     sets_special_initial_untruncate@{o so u} :
       Untruncate@{o} → @Initial Sets@{o so}   (* Set < o, o < so, so < u *)
     sets_special_initial_wellpowered@{o so u u0} :
       Untruncate@{o} → @Initial Sets@{o so}
       (* Set < o, o < so, so < u, u0 <= o *)
     sets_special_initial_book@{o so u u0 u1 u2} :
       Untruncate@{o} → @Initial Sets@{o so}
       (* Set < o, o < so, o < u0, u < u1, u0 < u2, so <= u1, u <= o,
          u <= so *)
     sets_special_initial_IEM@{o so u} :
       IEM@{o} → @Initial Sets@{o so}   (* o < so, so < u *)
     sets_special_initial_IEM_at_Set@{so u} :
       IEM@{Set} → @Initial Sets@{Set so}   (* Set < so, so < u *)

   The [Set < o] of the [Untruncate] witnesses is the cogenerator's
   ([Prop] as a carrier, Instance/Sets/Cogenerator.v), and
   [Sets_WellPowered_untruncate] carries the same bound.  Every binder is
   explicit, and one of them is load-bearing in a way that was measured:
   an unannotated first draft of [setsop_L_least] closed its goal with
   [reflexivity] and pinned the carrier universe to [Set] (About:
   [setsop_L_least@{u} : ∀ v : SubObj@{u Set} (cogen_prod@{Set u Set u
   Set} …)], and [setsop_special_initial] became [@Initial Sets@{Set u}^op]).
   Either change alone removes the pin, both measured in whole-file
   copies: with every binder of the file annotated, [reflexivity] is
   accepted with no [Set]; with every binder removed, [exact eq_refl] in
   place of [reflexivity] is too.  This file does both.

   TWO ROUTES REFUSED, pinned by Test/ProbeSpecialInitial452.v, whose
   import list contains this file's and this file itself, each beside a
   positive control and each read by un-wrapping the refused command in
   its own copy of the WHOLE probe.  In the quotes, a universe the compile
   generated is written <1>, <2>, ..., numbered afresh in each quote in
   order of first appearance, as the probe writes them, so that the
   numerals carry identity and no serial number is a claim:
     - [Sets^op] through the well-powered corollary.  With the datum left
       free, [special_initial_object_wellpowered (C := Sets@{o so}^op) WP
       setsop_comp setsop_cog] is accepted ([p452_setsop_wp_free]); with
       the only co-well-poweredness of [Sets] in tree,
       Instance/Sets/WellPowered.v's [Sets_CoWellPoweredAt_up] (one
       universe up), it is refused, the datum's index living one universe
       above the homs where the corollary needs it at or below them (the
       probe's N15, [p452_n15_setsop_wp_up]):
         "The term "Sets_CoWellPoweredAt_up X" has type
          "WellPoweredAt@{<1> <2> <2> o <1>} X" while it is expected to
          have type "WellPoweredAt@{<3> so <4> o <5>} X" (universe
          inconsistency: Cannot enforce <3> = <5> because <3> <= <6> <
          <5>)."
       The per-object corollary [special_initial_object_wellpowered_at],
       fed [Sets_CoWellPoweredAt_up] at the one object [cogen_prod
       setsop_comp setsop_cog], is refused on universes as well (N16,
       [p452_n16_setsop_wp_at_up]; control [p452_setsop_wp_at_free]).  So
       the hand-built [setsop_L] is what makes [Sets^op] unconditional.
     - [special_initial_object_small] at [Sets]: its universe constraint
       that objects fit the shape universe cannot hold here, objects of
       [Sets@{o so}] living at [so] above [Sets_Complete]'s shape universe
       [o].  With [Sets_Complete] ascribed [Complete@{o o o so}] and
       [Sets_Cogenerator_IEM E] it is refused (N10,
       [p452_n10_small_at_sets]):
         "The term "Sets_Complete : Complete" has type "Complete@{o o o
          so}" while it is expected to have type "Complete@{o o o <1>}"
          (universe inconsistency: Cannot enforce <1> = so because <1> <=
          <2> < so)."
       The form first measured on #452 left [Sets_Complete]'s universes
       to inference and is refused at the same argument, with every
       universe a serial number.  The controls, [sets_special_initial_IEM]
       at the same universes and its body with [Sets_Complete] ascribed
       ([p452_sets_iem], [p452_sets_iem_direct]), are accepted.

   NON-VACUITY.  [Sets^op] and [Sets] are not thin, and every cogenerator
   used here is small, indexed by [unit] ([cog_index setsop_cog = unit]
   is accepted by [eq_refl] in a scratch file, through Structure/
   Generator.v's [Generator_of_separator]), and genuine:
   Instance/Sets/Cogenerator.v's [Sets_terminal_not_cogenerates] shows
   the condition excludes every family of copies of the terminal object
   at [Sets], and [Sets_two_arrows] shows [Sets^op] has distinct
   parallel arrows for [setsop_cog] to separate.  The (2b) object is
   proved empty, not assumed.

   NOT DELIVERED.  No unconditional witness at [Sets]: the missing piece
   is a SMALL cogenerator, since Instance/Sets/Cogenerator.v's
   unconditional [Sets_Cogenerator_large] is large and [cogen_prod] at
   [Sets_Complete] refuses it (that file's header).  No [Sets^op]
   witness through the well-powered corollary, and none of (2b)/(2c) at
   [Sets^op]: co-well-poweredness of [Sets] at the pin is not in tree.  No
   normal form of the zero arrows was measured; at [Sets] their domain is
   empty, so there is no element to evaluate them at.  No comparison with
   Freyd's initial object at [Sets] as a constant here: it is not
   attempted, and [initial_unique (sets_special_initial_wellpowered U)
   Sets_initial_recovered] (Theory/WeaklyInitial/Sets.v) is accepted at
   [Sets@{o so}] in a scratch file, closed under the global context, as
   are Adjunction/SAFT/InitialObject.v's [special_vs_freyd] and
   [freyd_of_cogenerator] at [Sets] under [Untruncate].  (CORRECTION,
   #452 fess audit: an earlier revision said [Sets_initial_recovered] is
   pinned at [Sets@{Set _}]; [About] reads [@Initial Sets@{u0 u}] with
   [u0 < u] and no [Set].)  The thin witnesses of the theorem are not
   here. *)

(** ** Sets^op *)

Definition setsop_comp@{o so +| o < so +} :
  @Complete@{o o o so} (Sets@{o so}^op) :=
  Complete_op_of_Cocomplete Sets_Cocomplete.

Definition setsop_cog@{c o so +| o < so +} :
  Cogenerator@{c so o} (Sets@{o so}^op) :=
  cog_of_gen Sets_Generator.

Definition setsop_point@{o so +| o < so +} :
  carrier (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog).
Proof.
  exact (iprod_proj (cog_obj setsop_cog)
           (cogen_prod_limit setsop_comp setsop_cog) tt ttt).
Defined.

Definition setsop_L@{o so +| o < so +} :
  @SubObj (Sets@{o so}^op)
    (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog).
Proof.
  unshelve refine
    (@Build_SubObj (Sets^op) (cogen_prod setsop_comp setsop_cog)
       (@terminal_obj Sets Sets_Terminal)
       (@one Sets Sets_Terminal (cogen_prod setsop_comp setsop_cog)) _).
  constructor; intros z g1 g2 H u.
  destruct u.
  exact (H setsop_point).
Defined.

Definition setsop_L_least@{o so +| o < so +}
  (v : @SubObj (Sets@{o so}^op)
         (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog)) :
  sub_le setsop_L v.
Proof.
  exists (@one Sets Sets_Terminal (Subobject.sub_dom v)).
  intros p; exact eq_refl.
Defined.

Definition setsop_special_initial@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object setsop_comp setsop_cog setsop_L
    (intersection_all_of_least setsop_L setsop_L_least).

Example setsop_special_obj@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

Definition setsop_special_vs_known@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    ≅[Sets@{o so}^op] @initial_obj (Sets@{o so}^op) Sets_Terminal :=
  initial_unique setsop_special_initial Sets_Terminal.

Definition setsop_terminal_IsInitialObj@{o so +| o < so +} :
  @IsInitialObj (Sets@{o so}^op) (@terminal_obj Sets@{o so} Sets_Terminal) :=
  special_initial_IsInitialObj setsop_comp setsop_cog setsop_L
    (intersection_all_of_least setsop_L setsop_L_least).

(** ** Sets, under Untruncate: the least subobject *)

Definition sets_special_initial_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object Sets_Complete (Sets_Cogenerator_untruncate U)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Example sets_special_untruncate_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_untruncate U)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

(** ** Sets, under Untruncate: the well-powered corollary *)

Definition sets_special_initial_wellpowered@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object_wellpowered (Sets_WellPowered_untruncate U)
    Sets_Complete (Sets_Cogenerator_untruncate U).

Example sets_special_wellpowered_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_wellpowered U)
    = Subobject.sub_dom
        (complete_intersection Sets_Complete
           (wp_class_family
              (Sets_WellPowered_untruncate U
                 (cogen_prod Sets_Complete (Sets_Cogenerator_untruncate U)))
              (fun _ => True))) := eq_refl.

Definition sets_special_wellpowered_vs_known@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_wellpowered U)
    ≅ @initial_obj Sets@{o so} Sets_Initial :=
  initial_unique (sets_special_initial_wellpowered U) Sets_Initial.

Definition sets_special_wellpowered_empty@{o so +| Set < o, o < so +}
  (U : Untruncate@{o})
  (a : carrier
         (@initial_obj Sets@{o so} (sets_special_initial_wellpowered U))) :
  False :=
  match @zero Sets@{o so} (sets_special_initial_wellpowered U)
          (@initial_obj Sets@{o so} Sets_Initial) a with end.

(** ** Sets, under Untruncate: the book's blanket hypothesis *)

Definition Sets_HasClassIntersections_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : HasClassIntersections Sets@{o so} :=
  fun X P HP => Sets_wellpowered_intersection U X P HP.

Definition sets_special_initial_book@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object_book Sets_Complete (Sets_Cogenerator_untruncate U)
    (Sets_HasClassIntersections_untruncate U).

Example sets_special_book_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_book U)
    = Subobject.sub_dom
        (`1 (Sets_wellpowered_intersection U
               (cogen_prod Sets_Complete (Sets_Cogenerator_untruncate U))
               (fun _ => unit) (fun _ _ _ t => t))) := eq_refl.

Definition sets_special_book_vs_known@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_book U)
    ≅ @initial_obj Sets@{o so} Sets_Initial :=
  initial_unique (sets_special_initial_book U) Sets_Initial.

(** ** Sets, under IEM *)

Definition sets_special_initial_IEM@{o so +| o < so +}
  (E : IEM@{o}) : @Initial Sets@{o so} :=
  special_initial_object Sets_Complete (Sets_Cogenerator_IEM E)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Example sets_special_IEM_obj@{o so +| o < so +} (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

Definition sets_special_initial_IEM_at_Set@{so +| Set < so +}
  (E : IEM@{Set}) : @Initial Sets@{Set so} :=
  sets_special_initial_IEM E.
