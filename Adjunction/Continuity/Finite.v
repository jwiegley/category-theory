Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Opposite.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Adjoints preserve the terminal object and binary products, packaged *)

(* Awodey §9.6 (awodey:9.6:remark-adjoint-existence-tests): the corollaries
   of RAPL/LAPC that make limit preservation a usable test for the
   non-existence of adjoints, stated in the vocabulary of
   Functor/Structure/Terminal.v and Functor/Structure/Cartesian.v so that
   a refutation is a short contradiction rather than a walk through the
   general cone machinery.  Built for #432 (Instance/Sets/NoAdjoint.v, the
   first consumer, Mac Lane §V.5 Exercise 1).

   Each constant is a two-line composition: Adjunction/Continuity.v:205's
   [right_adjoint_PreservesLimitCone] at the empty or the two-object
   discrete diagram, read through Structure/Limit/Comparison.v's bridges
   [terminal_functor_iff_preserves_terminal] (:807) and
   [cartesian_functor_iff_preserves_binary_products] (:715); the two
   left-adjoint forms are the same two lines for [Opposite_Adjunction F U
   A], in which [F^op] is the right adjoint.  Nothing is re-proved.

   PLACEMENT.  Comparison.v already requires Continuity.v, so these cannot
   live in Continuity.v without a cycle; Comparison.v owns the bridges but
   not the adjunction vocabulary.  A satellite of Continuity.v keeps both
   donors unedited.  Closure 39 files excluding self, Comparison.v 12 at
   the margin, the other seventeen [Require]s 0.

   UNIVERSES.  Each of the four carries [u0 = u2], the hom levels of the
   two categories identified — [Adjunction]'s own equation ([h1 = h2] in
   [Build_Adjunction']'s block; [right_adjoint_PreservesLimitCone] carries
   it already), not this file's; no [Set]; the stdlib caps [EqdepFacts],
   [JMeq], [eq_ind], [eq_ind_r], [eq_rect_r] and [Logic_lemmas.equality]
   are [DiscreteCat_Functor']'s (Comparison.v:535).  Four [.glob] heads,
   all "Closed under the global context"; no [Qed], no [Defined] — [:=]
   terms.

   NOTATION TRAP.  [InitialFunctor F] and [CocartesianFunctor F] are
   NOTATIONS (Functor/Structure/Terminal.v:59, Functor/Structure/
   Cartesian.v:130) and do not parse in a definition's return type; the
   two left-adjoint forms spell them out as [@TerminalFunctor (D^op) (C^op)
   (F^op) _ _] and [@CartesianFunctor (D^op) (C^op) (F^op) _ _], which
   [About] prints back under the notations. *)

Section AdjointPreservation.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* A right adjoint preserves the terminal object: RAPL at the empty
   discrete diagram, read through Structure/Limit/Comparison.v's bridge
   into Functor/Structure/Terminal.v's class. *)
Definition right_adjoint_preserves_terminal `{@Terminal C} `{@Terminal D} :
  @TerminalFunctor C D U _ _ :=
  snd (terminal_functor_iff_preserves_terminal U)
      (right_adjoint_PreservesLimitCone A (DiscreteCat_Functor' nullary_fam)).

(* A right adjoint preserves binary products: RAPL at the two-object
   discrete diagrams, through the cartesian bridge. *)
Definition right_adjoint_preserves_binary_products
  `{@Cartesian C} `{@Cartesian D} : @CartesianFunctor C D U _ _ :=
  snd (cartesian_functor_iff_preserves_binary_products U)
      (fun x y => right_adjoint_PreservesLimitCone A
                    (DiscreteCat_Functor' (binary_fam x y))).

(* A left adjoint preserves the initial object: the same two lines for
   the opposite adjunction, in which [F^op] is the right adjoint.  The
   return type is [InitialFunctor F] spelled out, because that name is a
   notation (Functor/Structure/Terminal.v:59) and does not parse here. *)
Definition left_adjoint_preserves_initial `{@Initial C} `{@Initial D} :
  @TerminalFunctor (D^op) (C^op) (F^op) _ _ :=
  snd (terminal_functor_iff_preserves_terminal (F^op))
      (right_adjoint_PreservesLimitCone (Opposite_Adjunction F U A)
         (DiscreteCat_Functor' nullary_fam)).

(* A left adjoint preserves binary coproducts: [CocartesianFunctor F],
   likewise spelled out (Functor/Structure/Cartesian.v:130). *)
Definition left_adjoint_preserves_binary_coproducts
  `{@Cocartesian C} `{@Cocartesian D} :
  @CartesianFunctor (D^op) (C^op) (F^op) _ _ :=
  snd (cartesian_functor_iff_preserves_binary_products (F^op))
      (fun x y => right_adjoint_PreservesLimitCone (Opposite_Adjunction F U A)
                    (DiscreteCat_Functor' (binary_fam x y))).

End AdjointPreservation.
