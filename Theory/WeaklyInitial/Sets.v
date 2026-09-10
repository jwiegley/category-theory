Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Theory.WeaklyInitial.

Generalizable All Variables.

(** * The initial-object characterization at Sets

    The witness for Theory/WeaklyInitial.v's biconditional (#435, Mac Lane
    §V.6 Theorem 1): [Sets] is complete (Instance/Sets/Complete.v:196
    [Sets_Complete]) and has equalizers (Adjunction/GAFT/Sets.v:175
    [Sets_HasEqualizers]), so [initial_iff_weakly_initial_family_complete]
    applies, and the round trip runs — the initial object
    (Instance/Sets.v:275 [Sets_Initial]) becomes the singleton family
    [Sets_wif], Freyd's product-and-equalizer construction turns that back
    into an initial object [Sets_initial_recovered], and
    Structure/Initial.v:138's [initial_unique] gives the canonical
    isomorphism [Sets_roundtrip_iso] with the original.  The DERIVED
    singleton family's index and member read back at [eq_refl], through
    the transparent biconditional; nothing about the recovered initial
    object does.

    A separate leaf because of closure: this file's closure is 53 modules
    (Adjunction/GAFT/Sets.v 15 at the margin, the other six `Require`s 0)
    against Theory/WeaklyInitial.v's 29, and Adjunction/GAFT*.v [Require]
    Theory/WeaklyInitial.v, not this satellite, so there is no cycle.  The
    object-carrier universe lands at [Sets@{Set u}] with `Set < u` on every
    head, exactly as Adjunction/GAFT/Sets.v's header discloses for GAFT;
    the caps `JMeq`, `False_rect` and `projections` arrive with
    [Sets_Complete].  Six `.glob` heads, all `def`, all "Closed under the
    global context", zero `Axioms:` lines, no `Qed`, no `Defined`, none of
    the seven `Require`s droppable, zero name collisions.  NOT delivered:
    a witness at any other category ([FinSet] would need a [Complete
    FinSet] that does not exist); any [eq_refl] reading of the round trip
    beyond the family's index and member (the recovered initial object is
    Freyd's equalizer of endomorphisms, compared with the original only
    through [initial_unique]'s [≅]). *)

Definition Sets_initial_characterization :
  @Initial Sets ↔ WeaklyInitialFamily Sets :=
  initial_iff_weakly_initial_family_complete Sets_Complete Sets_HasEqualizers.

(* The round trip: the initial object, as a singleton family, through
   Freyd's construction, back to an initial object. *)
Definition Sets_wif : WeaklyInitialFamily Sets :=
  fst Sets_initial_characterization Sets_Initial.

Definition Sets_initial_recovered : @Initial Sets :=
  snd Sets_initial_characterization Sets_wif.

Definition Sets_roundtrip_iso :
  @initial_obj Sets Sets_initial_recovered ≅ @initial_obj Sets Sets_Initial :=
  initial_unique Sets_initial_recovered Sets_Initial.

(* The family is the singleton at the empty set, on the nose. *)
Example Sets_wif_index : wif_index Sets_wif = poly_unit := eq_refl.

Example Sets_wif_obj (u : poly_unit) :
  wif_obj Sets_wif u = @initial_obj Sets Sets_Initial := eq_refl.
