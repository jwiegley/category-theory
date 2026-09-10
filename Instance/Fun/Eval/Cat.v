Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Cat.Exponential.

Generalizable All Variables.

(** * The evaluation functor as [Cat]'s exponential evaluation *)

(* Satellite of Instance/Fun/Eval.v (Mac Lane §V.3, maclane:V.3:construction1):
   the two-variable evaluation is [Cat]'s exponential counit, named, and the
   fixed-object evaluation is its partial application.

   WHAT IS DELIVERED (6 constants, every one closed under the global
   context).
     - [CatEval P X : [P, X] ∏ P ⟶ X := @eval Cat Cat_Cartesian Cat_Closed P
       X] — the functor Instance/Cat/Cartesian/Closed.v:34-36 describes in
       prose and leaves unnamed.
     - [CatEval_obj]/[CatEval_map]: its two data fields ARE Instance/Fun/
       Eval.v's [EvalBi]'s, at [eq_refl] — which is why [EvalBi] uses the
       arrow order [fmap[K] f ∘ transform[σ] p].
     - [eval_is_CatEval_partial_obj] at [eq_refl] and
       [eval_is_CatEval_partial_map] at [≈]: the fixed-object [Eval p] is
       the partial application of [Cat]'s own evaluation (the [≈] is
       [eval_partial_map]'s: [Partial_l] carries an [fmap id]).
     - [eval_transpose J P X : [J ∏ P, X] ≅[Cat] [J, [P, X]] :=
       Cat_exp_prod_l J P X] — the issue's "record the parameter/adjunct
       passage" is Instance/Cat/Exponential.v:57's existing isomorphism,
       cited, not rebuilt.

   UNIVERSES (measured by [About] under [Set Printing Universes]).  The
   price of the [Cat] route, and the reason Instance/Fun/Eval.v builds
   [EvalBi] directly: the five [CatEval*] constants carry [u0 = u1],
   [u0 = u5], [u0 = u6] — P's and X's object and hom levels collapse into
   one universe ([Functor@{u0 u0 u0 u5 u6 u6}] with [u0 = u5 = u6]).  The
   binder [P X : Cat] is innocent: [EvalBi] restated at the same binder
   carries NO equation (measured), so the collapse comes from
   [Cat_Closed]'s exponential structure itself, not from being at [Cat].
   At arbitrary [P X : Category], [EvalBi] carries only Instance/Fun.v's
   [jh = ch].  [eval_transpose@{u u0}] lives at [Cat]'s
   single level ([Fun@{u u u u u u u0}]) with no equation.  All six carry
   [Basics.compose], [eq_rect] and [prod_rect] bounds; no word-bounded
   [Set], no [JMeq]/[EqdepFacts]/[eq_rect_r].  This is measured by [About],
   not by a refutation: the route typechecks.

   COUNTS.  6 constants (5 [def], 1 [prf]); one [Qed]; closure 33 files
   excluding self (Instance/Cat/Exponential.v costs 8 at the margin,
   Instance/Fun/Eval.v 1, the other fourteen [Require]s 0).  Precedent for
   an Instance/Fun/ file requiring Instance/Cat/*: Instance/Fun/Discrete.v
   and Instance/Fun/Action.v. *)

Section CatEval.

Context (P X : Cat).

(* [Cat]'s exponential is the functor category (Instance/Cat/Cartesian/
   Closed.v's [Cat_Closed]), so the closed structure's own [eval] IS a
   functor [[P, X] ∏ P ⟶ X].  Named here; it is reachable only at [Cat]'s
   universes, which is why Instance/Fun/Eval.v builds [EvalBi] directly
   (see the header's universe measurement). *)
Definition CatEval : ([P, X] ∏ P) ⟶ X := @eval Cat Cat_Cartesian Cat_Closed P X.

(* Its two data fields ARE [EvalBi]'s, on the nose. *)
Definition CatEval_obj (Hp : ([P, X] ∏ P)) :
  fobj[CatEval] Hp = fobj[EvalBi] Hp := eq_refl.

Definition CatEval_map (Hp Kq : ([P, X] ∏ P)) :
  @fmap _ _ CatEval Hp Kq = @fmap _ _ (@EvalBi P X) Hp Kq := eq_refl.

(* So the fixed-object evaluation is the partial application of [Cat]'s
   own evaluation: on objects on the nose, on arrows up to ≈ (through
   Instance/Fun/Eval.v's [eval_partial_map]). *)
Definition eval_is_CatEval_partial_obj (p : P) (H : [P, X]) :
  fobj[Eval p] H = fobj[Partial_l CatEval p] H := eq_refl.

Lemma eval_is_CatEval_partial_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[Eval p] s ≈ fmap[Partial_l CatEval p] s.
Proof. exact (eval_partial_map p H K s). Qed.

End CatEval.

(* The parameter/adjunct passage the issue asks to record already exists as
   an isomorphism in [Cat]: Instance/Cat/Exponential.v's [Cat_exp_prod_l].
   Cited, not rebuilt. *)
Definition eval_transpose (J P X : Cat) :
  @Isomorphism Cat ([J ∏ P, X]) ([J, [P, X]]) := Cat_exp_prod_l J P X.
