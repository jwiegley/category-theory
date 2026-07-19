Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Theory.Lawvere.Sets.

Generalizable All Variables.

(** * The finitary-monad connection, hypothesis-scoped

    nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
    nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

    Classically the underlying-set functor [ev1 T : Models T Sets ⟶ Sets]
    has a left adjoint — the free-model functor — whose existence is a
    consequence of the general adjoint functor theorem (Adjunction/GAFT.v
    is the in-tree source of that argument).  Constructing that left
    adjoint here would need the solution-set work for [Models T Sets],
    which is out of scope for this file; following the SAFT precedent the
    left adjoint enters as DATA: a functor [L] together with an adjunction
    [L ⊣ ev1 T].

    Given that data, everything downstream is direct instantiation of the
    Phase-14 monadicity spine at the adjunction [adj : L ⊣ ev1 T], with
    the binders of Monad/Comparison.v matched as C := Models T Sets,
    D := Sets, F := L, U := ev1 T:

    - [Lawvere_Monad] : the transparently packaged induced monad
      [Adjunction_Induced_Monad adj] on [Sets], with carrier [ev1 T ◯ L],
      ret = η and join = U ε F;

    - [Lawvere_EM_Comparison] : the Eilenberg–Moore comparison functor
      [EM_Comparison adj] from [Models T Sets] into the algebras of that
      monad;

    - [Lawvere_crude_monadicity] : under exactly the crude-monadicity
      hypotheses of Monad/Monadicity/Crude.v — [Models T Sets] has
      coequalizers of reflexive pairs, [ev1 T] preserves them, and
      [ev1 T] reflects isomorphisms — the comparison is an equivalence
      of categories, so [Models T Sets] is monadic over [Sets].

    The full finitary-monad ⟷ Lawvere-theory EQUIVALENCE (that the
    induced monad is finitary, and that every finitary monad on [Sets]
    arises this way from a theory, naturally in both directions) is
    deferred (ledger 2). *)

Section LawvereMonad.

Context (T : LawvereTheory).
Context (L : Sets ⟶ Models T Sets).
Context (adj : L ⊣ ev1 T).

(** The induced monad on [Sets]: ret = η, join = U ε F, packaged
    transparently by [Adjunction_Induced_Monad]. *)

Definition Lawvere_Monad : @Monad Sets (ev1 T ◯ L) :=
  Adjunction_Induced_Monad adj.

(** The Eilenberg–Moore comparison functor at this adjunction. *)

Definition Lawvere_EM_Comparison :
  Models T Sets ⟶ @EilenbergMoore Sets (ev1 T ◯ L) Lawvere_Monad :=
  EM_Comparison adj.

(** ** Scoped monadicity

    The crude-monadicity hypotheses of Monad/Monadicity/Crude.v,
    re-exposed verbatim at this adjunction. *)

Context (RC : HasReflexiveCoequalizers (Models T Sets)).
Context (pres : PreservesReflexiveCoequalizers (ev1 T)).
Context (refl : ReflectsIsos (ev1 T)).

Corollary Lawvere_crude_monadicity :
  EquivalenceOfCategories Lawvere_EM_Comparison.
Proof using RC pres refl.
  exact (crude_monadicity adj RC pres refl).
Defined.

End LawvereMonad.

