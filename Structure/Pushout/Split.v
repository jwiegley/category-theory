Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.

Generalizable All Variables.

(** * When a pushout injection splits *)

(* nLab:      https://ncatlab.org/nlab/show/pushout
   Wikipedia: https://en.wikipedia.org/wiki/Pushout_(category_theory)

   Three lines of generic category theory, factored out of
   Instance/Grp/Pushout.v because nothing in them is about groups.

   THE OBSERVATION.  For a span [y <-f- x -g-> z] with pushout apex [P],
   the first injection [i1 : y ~> P] SPLITS as soon as [f] factors through
   [g] — that is, as soon as there is [r : z ~> y] with [r ∘ g ≈ f].
   Feed the competing cocone [(id[y], r)] to the universal property: its
   commutation obligation [id ∘ f ≈ r ∘ g] is exactly the factorization,
   and the mediator [u] it produces satisfies [u ∘ i1 ≈ id].  So [i1] is a
   section, hence monic by Theory/Morphisms.v's [sections_are_monic].

   WHY THIS IS WORTH NAMING.  It is the constructively cheap fragment of
   the classical refinement "if both legs of the span are monic then both
   pushout injections are monic".  That refinement in full is, for groups,
   the Schreier normal-form theorem for amalgamated free products, whose
   usual proof (van der Waerden's trick) chooses coset transversals; the
   split fragment below needs no normal form, no transversal and no choice
   principle, and it is available in EVERY category with the relevant
   pushout.  Instance/Grp/Pushout.v discusses the gap in detail.

   WHAT IS PROVED, AND AT WHAT STRENGTH.  [pushout_in1_Section] and
   [pushout_in2_Section] produce a [Theory/Morphisms.v] [Section]
   instance — a genuine retraction, exhibited, not merely the existence of
   one — and [pushout_in1_Monic] / [pushout_in2_Monic] read off monicity.
   [pushout_in1_Section_of_Retraction] is the corollary a reader of the
   classical statement wants: if [g] is a SPLIT monomorphism then [i1]
   splits, because [f] then factors through [g] via [f ∘ retraction].
   The retraction produced is [pushout_med] applied to the cocone
   [(id, r)], so it is the mediator of the universal property and not a
   second construction.

   WHAT IS NOT DELIVERED.  Nothing about pushouts along merely monic
   legs; no van Kampen / effective-descent property; no claim that the
   splitting hypothesis is NECESSARY for the injection to be monic (it is
   not — in Grp the injections are monic whenever the legs are, by
   Schreier, and that is exactly the theorem this file does not reach).
   No dual file for pullbacks: the [C^op] instance of these statements is
   available by instantiation but is not spelled out. *)

Section PushoutSplit.

Context {C : Category}.
Context {x y z : C}.
Context {f : x ~> y} {g : x ~> z}.
Context (P : IsPushout f g).

(** ** The first injection *)

(* If [f] factors through [g], the cocone [(id[y], r)] commutes, so the
   pushout hands back a retraction of [pushout_in1]. *)
Lemma pushout_in1_factor_commutes (r : z ~> y) (Hr : r ∘ g ≈ f) :
  id[y] ∘ f ≈ r ∘ g.
Proof.
  rewrite id_left.
  symmetry.
  exact Hr.
Qed.

Definition pushout_in1_retract (r : z ~> y) (Hr : r ∘ g ≈ f)
  : pushout_apex P ~> y :=
  pushout_med P (pushout_in1_factor_commutes r Hr).

Lemma pushout_in1_retract_comp (r : z ~> y) (Hr : r ∘ g ≈ f) :
  pushout_in1_retract r Hr ∘ pushout_in1 P ≈ id.
Proof.
  unfold pushout_in1_retract.
  exact (pushout_med_in1 P (pushout_in1_factor_commutes r Hr)).
Qed.

Definition pushout_in1_Section (r : z ~> y) (Hr : r ∘ g ≈ f)
  : Section (pushout_in1 P) :=
  {| section      := pushout_in1_retract r Hr
   ; section_comp := pushout_in1_retract_comp r Hr |}.

Lemma pushout_in1_Monic (r : z ~> y) (Hr : r ∘ g ≈ f) :
  Monic (pushout_in1 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in1_Section r Hr).
Qed.

(** ** The second injection *)

Lemma pushout_in2_factor_commutes (s : y ~> z) (Hs : s ∘ f ≈ g) :
  s ∘ f ≈ id[z] ∘ g.
Proof.
  rewrite id_left.
  exact Hs.
Qed.

Definition pushout_in2_retract (s : y ~> z) (Hs : s ∘ f ≈ g)
  : pushout_apex P ~> z :=
  pushout_med P (pushout_in2_factor_commutes s Hs).

Lemma pushout_in2_retract_comp (s : y ~> z) (Hs : s ∘ f ≈ g) :
  pushout_in2_retract s Hs ∘ pushout_in2 P ≈ id.
Proof.
  unfold pushout_in2_retract.
  exact (pushout_med_in2 P (pushout_in2_factor_commutes s Hs)).
Qed.

Definition pushout_in2_Section (s : y ~> z) (Hs : s ∘ f ≈ g)
  : Section (pushout_in2 P) :=
  {| section      := pushout_in2_retract s Hs
   ; section_comp := pushout_in2_retract_comp s Hs |}.

Lemma pushout_in2_Monic (s : y ~> z) (Hs : s ∘ f ≈ g) :
  Monic (pushout_in2 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in2_Section s Hs).
Qed.

End PushoutSplit.

(** ** The classical special case: a split leg

    If [g] is a split monomorphism, with retraction [t : z ~> x], then [f]
    factors through [g] as [f ∘ t], because [(f ∘ t) ∘ g ≈ f ∘ (t ∘ g) ≈ f].
    So the OPPOSITE injection splits.  This is the constructively available
    fragment of "monic legs give monic injections". *)

Definition pushout_in1_Section_of_Retraction
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sg : Section g)
  : Section (pushout_in1 P).
Proof.
  unshelve refine (pushout_in1_Section P (f ∘ section) _).
  rewrite <- comp_assoc.
  rewrite section_comp.
  apply id_right.
Defined.

Definition pushout_in2_Section_of_Retraction
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sf : Section f)
  : Section (pushout_in2 P).
Proof.
  unshelve refine (pushout_in2_Section P (g ∘ section) _).
  rewrite <- comp_assoc.
  rewrite section_comp.
  apply id_right.
Defined.

Lemma pushout_in1_Monic_of_Retraction
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sg : Section g) :
  Monic (pushout_in1 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in1_Section_of_Retraction P Sg).
Qed.

Lemma pushout_in2_Monic_of_Retraction
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sf : Section f) :
  Monic (pushout_in2 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in2_Section_of_Retraction P Sf).
Qed.

(** ** Both injections at once

    "Split-monic legs give split-monic injections" — the strength at which
    Mac Lane's monic-legs refinement is available with no normal-form
    theorem.  Note the CROSSING: a splitting of [g] is what splits the
    injection out of [y], and vice versa. *)

Definition pushout_both_Section
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sf : Section f) (Sg : Section g)
  : Section (pushout_in1 P) * Section (pushout_in2 P) :=
  (pushout_in1_Section_of_Retraction P Sg,
   pushout_in2_Section_of_Retraction P Sf).

Lemma pushout_both_Monic
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sf : Section f) (Sg : Section g) :
  Monic (pushout_in1 P) * Monic (pushout_in2 P).
Proof.
  exact (pushout_in1_Monic_of_Retraction P Sg,
         pushout_in2_Monic_of_Retraction P Sf).
Qed.
