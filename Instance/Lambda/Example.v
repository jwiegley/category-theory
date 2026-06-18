Require Import Category.Lib.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Eval.

Set Equations With UIP.

Generalizable All Variables.

(** * Worked examples for the de Bruijn STLC CEK evaluator *)

(* These [Definition]s exercise the CEK machine of Eval.v on concrete closed
   terms, pinning each [run gas e] to the exact final machine state it computes.
   The proofs are [eq_refl], so each one is a regression test: it typechecks
   precisely when the machine still reduces the term to the stated state, by
   the definitional unfolding of [run]/[loop]/[step].

   CEK machine:  https://en.wikipedia.org/wiki/CEK_Machine
   simply typed lambda calculus:
     https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus *)

Section Example.

Open Scope Ty_scope.

(* A pure function example, with no products: [((λx. x (λ_. ())) (λy. y)) ()].
   Reducing call-by-value, [(λx. x (λ_. ())) (λy. y)] applies [λy. y] to
   [λ_. ()], giving [λ_. ()]; applying that to [()] yields [()].  The machine
   halts at [Closure EUnit] -- the body of the final [λ_. ()] -- under the
   two-entry environment that bound its argument [()] and the earlier [λy. y],
   with the halt continuation [MT]. *)
Definition example1 :
  run 20 (APP (APP (LAM (APP (VAR ZV)
                             (LAM EUnit)))
                   (LAM (VAR ZV)))
              EUnit) =
    MkΣ (Closure EUnit
                 (AddCl (Val EUnit Value.UnitP NoCl)
                        (AddCl (Val (LAM (cod:=_) (VAR ZV))
                                    (Value.LambdaP (VAR ZV)) NoCl) NoCl))) MT :=
  eq_refl.

(* CAUTION: this example documents the product defect FLAGged in Eval.v, NOT a
   correct evaluation.  The two components [(λx. x) ()] are redexes that SHOULD
   each reduce to [()], so a correct CBV machine would return [Pair () ()].
   Instead the [Pair]/[PAIR_SND]/[PAIR_FST] clauses of [step] form a 3-cycle
   that stashes the components away unevaluated and rebuilds the original pair;
   the result below is the *syntactically unchanged* input term.  The equation
   holds at gas 30 only because 30 is a multiple of the cycle length, landing
   the machine back at its start.  See the file header of Eval.v. *)
Definition example_pair :
  run 30 (Pair (APP (LAM (VAR ZV)) EUnit)
               (APP (LAM (VAR ZV)) EUnit)) =
    MkΣ (Closure
           (Pair (APP (LAM (VAR ZV)) EUnit) (APP (LAM (VAR ZV)) EUnit)) NoCl) MT :=
  eq_refl.

(* Projection avoids the [Pair] 3-cycle above: [step] on [Fst]/[Snd] pushes an
   [FST]/[SND] frame, and the [Pair]-against-[FST]/[SND] clauses grab the chosen
   component directly ([Fst (Pair x y)] selects [x]) and then evaluate it.  Here
   the selected component [(λx. x) ()] reduces to [()], so both projections halt
   at [Closure EUnit], the correct call-by-value result. *)
Definition example_fst :
  run 20 (Fst (Pair (APP (LAM (VAR ZV)) EUnit)
                    (APP (LAM (VAR ZV)) EUnit))) =
    MkΣ (Closure EUnit NoCl) MT := eq_refl.

Definition example_snd :
  run 20 (Snd (Pair (APP (LAM (VAR ZV)) EUnit)
                    (APP (LAM (VAR ZV)) EUnit))) =
    MkΣ (Closure EUnit NoCl) MT := eq_refl.

End Example.
