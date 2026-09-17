(** * Boundary probe for Structure/Limit/Components.v (issue #355)

    Mac Lane CWM 2nd ed. §IV.2, book p. 90, Exercise 7.

    WHY THIS FILE EXISTS AT ALL.  [Structure/Limit/Components.v] carries
    two [Fail]s of its own (an earlier revision said four; the two
    universe ones there were repaired at the same time as N1/N2 below),
    and they are well formed -- each is stripped and its whole error read,
    each sits beside a control that must succeed.  What an in-file
    negative CANNOT do is survive a rename: a
    whole-file rename moves the [Fail] and the constant it names in
    lockstep, so the guard stays green while the thing it guarded is
    gone.  Every negative below therefore names a constant of the TARGET,
    and the file mirrors ALL 23 of the target's [Require] lines -- a
    probe built on a short prefix of that list is the classic way to
    make a negative pass
    for a reason it never measured (a missing coercion, an absent
    notation), certifying nothing.

    KINDS, separated by the error TEXT rather than by label:
      CONVERSION   ends `(cannot unify "X" and "Y")`
      FORMABILITY  ends `(universe inconsistency: Cannot enforce ...)`
    A [Fail] that SUCCEEDS prints NOTHING under this repo's [coqc], so
    every negative here was stripped and run alone before being trusted.

    WHAT IS PINNED, and what each negative is FOR:

    N1, N2 -- REPAIRED, and recorded as a correction.  An earlier revision
          read:

            "N1 -- the [iprod] reading of part (a) carries a [Set] pin
             that the ELEMENTARY reading does not.  This is the reason
             part (a) is stated first at [IsIndexedProduct] and only then
             read through [iprod]: [iprod] is defined over
             [Limit (DiscreteCat_Functor f)] and so pins the ambient
             category's hom AND proof universes to the literal [Set].  The
             issue's own reviewer check asks that the right-hand side use
             [iprod]; taken alone that would have confined the theorem to
             [Set]-homed categories WITHOUT SAYING SO.  The controls show
             the elementary vocabulary is formable at levels where the
             [iprod] one is not, so the pin is attributable to the DONOR
             and not to anything the target adds.
             N2 -- the same, one layer out, at the target's own corollary.
             Both [Set]-pin negatives report `Cannot enforce Set = uh`,
             which names the declared level, so neither can be passing for
             an unrelated reason."

          The attribution to the DONOR was right, and the donor was one
          step further out than [iprod]: [DiscreteCat_Functor], declared
          with bare binders and minimized to [DiscreteCat@{u Set Set}].
          Annotated in place in the PR "algebraic carriers are sets"
          (2026-09-17), Instance/Discrete.v:81, both commands are ACCEPTED
          and are kept as positive controls at the same levels, so
          dropping the annotation refuses them again and breaks this file.
          Part (a) is still stated first at [IsIndexedProduct], which is
          now a presentational choice and not a universe obligation.
          NO FORMABILITY REFUSAL REMAINS IN THIS FILE.

    N3 -- [component_diagram] is not [summand] of the transported functor
          on the nose; the comparison is at [≈] with identity components.
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Initial.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Structure.Limit.Components.

(** ** Instrument check — must ERROR ("The command has not failed!"). *)
Fail Fail Check Category.

(** ** The former [Set] pin of the [iprod] reading, now lifted.

    Declared with the ambient homs strictly ABOVE [Set], the elementary
    statements elaborate and, since [DiscreteCat_Functor] was annotated,
    so do the [iprod] ones.  The two former negatives are kept here as
    positive controls; see N1/N2 in the header. *)

Section IprodSetPin.

Universe uo uh.
Constraint Set < uh.

Context (Cu : Category@{uo uh uh}).
Context (Js : bool → Category@{uo uh uh}).

(* CONTROLS: the elementary vocabulary IS formable at these levels, and
   the controls are APPLIED -- an unapplied polymorphic constant never
   meets [Cu] and would discriminate nothing. *)

Check (fun (A : Type) (f : A → Cu) (p : Cu)
           (pr : ∀ a : A, p ~{Cu}~> f a) => IsIndexedProduct f p pr).

Check (fun (F : SigmaCat Js ⟶ Cu) (p : Cu) => IsALimit F p).

Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (p : Cu) (pr : ∀ k : bool, p ~{Cu}~> L k)
           (HP : IsIndexedProduct L p pr) => coprod_IsALimit F HL HP).

(* Former N1: the donor is formable here. *)
Check (fun (A : Type) (f : A → Cu)
           (P : Limit (DiscreteCat_Functor f)) => iprod f P).

(* Former N2: and so is the target's own corollary over it. *)
Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (P : Limit (DiscreteCat_Functor L)) =>
         coprod_IsALimit_iprod F HL P).

End IprodSetPin.

(** ** CONVERSION — the transported diagram is not the summand on the
    nose.  The control is the [≈] form, which the target proves. *)

Section DiagramConversion.

Context {J C : Category}.
Context (D : ComponentDecomposition J).
Context (F : J ⟶ C).

(* CONTROL: the [≈] comparison exists and is what the target delivers. *)
Check (component_diagram_equiv D F).

(* N3. *)
Fail Example probe_component_diagram_strict (k : cd_index D) :
  component_diagram D F k = summand (F ◯ cd_compare D) k := eq_refl.

End DiagramConversion.

(** ** POSITIVE CONTROLS naming the rest of the surface, so that a rename
    of any of these breaks this file at a NON-[Fail] line. *)

Check @coprod_IsALimit.
Check @coprod_IsLimitCone.
Check @coprod_Limit.
Check @coprod_limit_iso.
Check @coprod_limit_iso_legs.
Check @coprod_proj_is_restriction.
Check @coprod_IsALimit_HasIndexedProducts.
Check @coprod_Limit_iprod.
(* [coprod_IsALimit_iprod] and [component_diagram] are named by NEGATIVES
   only; without these two controls a rename of either would leave the
   corresponding [Fail] passing for the WRONG reason (reference not
   found), i.e. a vacuous guard.  Found by rename simulation, not by
   inspection. *)
Check @coprod_IsALimit_iprod.
Check @component_diagram.
(* [iprod], [Limit] and [DiscreteCat_Functor] are DONOR names that the
   negatives name and no control did.  Their exposure is narrower than a
   leaf's -- renaming any of them breaks the target too -- but a rename
   would still leave the two formability negatives passing for
   reference-not-found rather than for the universe fact, so they are
   guarded here.  Found by rename simulation, not by inspection. *)
Check @iprod.
Check @Limit.
Check @DiscreteCat_Functor.
Check @ComponentDecomposition.
Check @cd_index.
Check @cd_rep.
Check @cd_part.
Check @cd_join.
Check @cd_sep.
Check @cd_compare.
Check @cd_equivalence.
Check @cd_bundled_equivalence.
Check @components_IsALimit.
Check @components_Limit.
Check @naive_pi0_sum.
Check @naive_pi0_sum_not_connected.
Check @no_ESO_into_naive_pi0_sum.
Check @TwoSum_not_connected.
Check @CoqPair_IsALimit.
Check @CoqPair_med_computes.
