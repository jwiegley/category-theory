Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Adjunction.GAFT.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.SpanningArrow.

Generalizable All Variables.

(** * Probe for Adjunction/SpanningArrow.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.7
    Definition 6 and Lemma 2, printed pp. 127-128.  Issue #448.  The
    variety remark has its own probe, Test/ProbeVarietySpanning448.v.

    The import list above is the target file's own import list,
    unabbreviated.  A short prefix is what makes a probe pass vacuously,
    so nothing is trimmed even where a require is redundant.

    Every statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read; a refutation that holds prints nothing under
    this repo's coqc.  Kinds, under THIS import list:

      CONVERSION  - "cannot unify A and B" parenthetical present.
      TYPING      - the "has type X while it is expected to have type Y"
                    opener with NO such parenthetical.
      INSTANCE    - "(no type class instance found)": the negative must
                    be a [Definition] in a section with NO instance in
                    scope, since a [Check] tolerates the open evar and a
                    section that carries the instance ACCEPTS the term.
      UNIVERSE    - "universe inconsistency".  RECORDED CORRECTION: no
                    negative of this kind remains in the file.  B7 was the
                    only one, and it turned over when
                    [DiscreteCat_Functor] was annotated (PR "algebraic
                    carriers are sets", 2026-09-17); the section that held
                    it now keeps it as a positive control.  The kind is
                    left listed because the section still guards against
                    the refusal coming back.

    One boundary is NOT a refusal and is pinned positively (B1 below):
    [Spanning] with its two [sub_le] arguments exchanged is inhabited by
    EVERY arrow, so a refutation probe on it would be vacuous.

    The instrument check comes first; every library constant a negative
    names has a positive control outside any refutation command. *)

(** ** Instrument check *)

Fail Check spanning_arrow_448_no_such_constant.

(** ** Positive controls *)

Check @SubFactorsThrough.
Check @Spanning.
Check @spanning_arrow.
Check @PreservesWidePullbacks.
Check @SpanningArrowsOutOf.
Check @SubObj.
Check @sub_top.
Check @sub_le.
Check @sub_top_greatest.
Check @sub_dom.
Check @sub_mono.
Check @spanning_sub.
Check @spanning_factor.
Check @spanning_solution_set.
Check @factors_through_top.
Check @SolutionSet.
Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @GAFT.
Check @GAFT_from_spanning.
Check @Complete.
Check @PreservesImageLimit.
Check @HasWidePullbacks.

(** ** Readbacks that HOLD, and the vacuity of the swapped order *)

Section Readbacks.

Context {A X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).
Context {x : X} {a : A} (f : x ~> G a).

(* B1: the flipped order is VACUOUS -- inhabited for every f by
   [sub_top_greatest] -- which is why [Spanning] reads [sub_le sub_top m]
   and not [sub_le m sub_top]. *)
Definition p448_b1_flipped : Type :=
  ∀ m : SubObj a, SubFactorsThrough G f m → sub_le m sub_top.
Example p448_b1_vacuous : p448_b1_flipped.
Proof. intros m _; apply sub_top_greatest. Defined.

(* B6: the two load-bearing [Defined]s, read back at eq_refl.  With
   [factors_through_top] closed by Qed the first is refused; with
   [spanning_solution_set] closed by Qed the last three are. *)
Example p448_t_lift : `1 (factors_through_top G f) = f := eq_refl.
Example p448_t_index :
  sol_index (spanning_solution_set G GP x) = SpanningArrowsOutOf G x
  := eq_refl.
Example p448_t_obj (i : SpanningArrowsOutOf G x) :
  sol_obj (spanning_solution_set G GP x) i = `1 i := eq_refl.
Example p448_t_arr (i : SpanningArrowsOutOf G x) :
  sol_arr (spanning_solution_set G GP x) i = `1 (`2 i) := eq_refl.

(* B2 -- CONVERSION (the message carries the "cannot unify" parenthetical
   on the codomain, "cannot unify "fobj[G] a" and "x""): the factorization
   composite in the wrong order, "The term "fmap[G] (sub_mono m)" has
   type "fobj[G] (sub_dom m) ~{ X }~> fobj[G] a" while it is expected to
   have type "fobj[G] (sub_dom m) ~{ X }~> x"". *)
Fail Definition p448_b2 (m : SubObj a) : Type :=
  { k : x ~> G (sub_dom m) & k ∘ fmap[G] (sub_mono m) ≈ f }.

(* B3 -- TYPING, not INSTANCE: [GP] is an EXPLICIT argument of the
   discharged [spanning_solution_set], so omitting it mis-applies the
   next argument: "The term "z" has type "obj[X]" while it is expected to
   have type "PreservesWidePullbacks G"". *)
Fail Definition p448_b3 (z : X) : SolutionSet G z :=
  spanning_solution_set G z.

(* B5 -- TYPING: the spanning factor lands in the intersection, not in
   [a]: "has type "x ~{ X }~> fobj[G] (sub_dom (spanning_sub G f))" while
   it is expected to have type "x ~{ X }~> fobj[G] a"". *)
Fail Definition p448_b5 : x ~> G a := spanning_factor G GP f.

End Readbacks.

(** ** The missing-instance boundary, in a section WITHOUT the instance *)

Section NoWidePullbacks.

Context {A X : Category}.
Context (G : A ⟶ X).
Context {x : X} {a : A} (f : x ~> G a).

(* B4 -- INSTANCE: "Cannot infer the implicit parameter HWP of
   spanning_sub whose type is "HasWidePullbacks A" (no type class
   instance found)".  Posed in the section that has the instance, the
   same term is ACCEPTED (measured), so the probe must live here. *)
Fail Definition p448_b4 : SubObj a := spanning_sub G f.

End NoWidePullbacks.

(** ** The former Set pin on GAFT, now lifted *)

Section UnannotatedGAFT.

Context {A X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).

(* Former B7, now a positive control.

   RECORDED CORRECTION.  An earlier revision read: "B7 -- UNIVERSE: over
   an UNANNOTATED section, applying [GAFT] to the spanning solution set is
   refused, 'universe inconsistency: Cannot enforce Set = <the section's
   hom universe>' -- a section Context binds rigid universes and GAFT is
   pinned at [Category@{_ Set Set}] through Theory/WeaklyInitial.v's
   [initial_from_weakly_initial].  This is why [GAFT_from_spanning] sits
   in its own section over [Category@{oA Set Set}]; the annotated form is
   the positive control, [GAFT_from_spanning] itself, checked above."

   The chain of attribution was right as far as it went, and one link
   further back was the cause: [initial_from_weakly_initial] carried the
   [Set] because it takes two [Limit (DiscreteCat_Functor …)] premises and
   [DiscreteCat_Functor] was declared with bare binders, minimizing to
   [DiscreteCat@{u Set Set}].  Annotated in place in the PR "algebraic
   carriers are sets" (2026-09-17), Instance/Discrete.v, that [Set] is
   gone from [GAFT]'s statement and this application is ACCEPTED over a
   section whose universes are rigid.  It is kept here as a positive
   control: dropping the annotation refuses it again and breaks this file.
   [GAFT_from_spanning] keeps its own section, which is now a
   presentational choice rather than a universe obligation.

   SECOND CORRECTION, same PR, later commit.  The sentence above ended
   "[GAFT_from_spanning] keeps its own section", and that section is no
   longer annotated either: [Universes oA oX.] and the two
   [Category@{o Set Set}] annotations were DELETED and its [A] and [X] are
   now declared bare, exactly as this probe's are.  So this definition and
   [GAFT_from_spanning] are now THE SAME STATEMENT over the same binders,
   and [p448_b7_via_theorem] below records that by inhabiting this
   section's goal FROM the theorem -- which is the strongest identification
   available, since [GAFT_from_spanning] is [Qed] and no [eq_refl] reaches
   inside it.
   The widening is measured in Adjunction/SpanningArrow.v's header, where
   the BEFORE and AFTER [About]s are quoted side by side; the headline is
   that the BEFORE block carried [Set = oA], demanding a category whose
   OBJECTS as well as homs live in [Set], and the AFTER block carries no
   [Set] at all. *)
Definition p448_b7 (comp : @Complete A)
  (cont : @PreservesImageLimit A X G) :
  { F : X ⟶ A & F ⊣ G } := GAFT G comp cont (spanning_solution_set G GP).

(* The two are now interchangeable, up to the implicit/explicit shape of
   the wide-pullback argument.  If the annotations are ever put back, this
   line stops compiling. *)
Definition p448_b7_via_theorem (comp : @Complete A)
  (cont : @PreservesImageLimit A X G) :
  { F : X ⟶ A & F ⊣ G } := @GAFT_from_spanning A X G HWP GP comp cont.

End UnannotatedGAFT.
