Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Exp.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** The values (canonical forms) of the call-by-value de Bruijn STLC. *)

(* [ValueP e] holds exactly when [e] is a value: a term that cannot reduce any
   further under the call-by-value strategy of [Step] (see [Value_irreducible]
   there).  The value grammar carved out by the constructors below is

     v ::= ()              (EUnit)
         | (v, v)          (Pair of values)
         | λ. e            (LAM, never reduced under)

   matching the standard CBV grammar for unit, products, and functions.  The
   eliminators -- [Fst], [Snd], [APP] -- are deliberately absent: a projection
   or application is a redex (or contains one), never a value.  [VAR] is absent
   too: progress ([strong_progress]) is stated for closed terms ([Exp []]),
   where no free variable can occur, so variables need not be values.  (nLab
   has no page for "value" in this PL sense: ncatlab.org/nlab/show/value is the
   mathematical "value of a function".)

   The predicate lands in [Set] rather than [Prop] so that downstream
   evaluators ([Eval]) may compute with the witness; [ValueP_irrelevance]
   recovers proof irrelevance constructively, so the [Set] placement costs no
   uniqueness. *)
Section Value.

Import ListNotations.

Open Scope Ty_scope.

(* [ValueP] is an inductive predicate that indicates whether an expression
   represents a value, i.e., that it does not reduce any further. *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Set :=
  | UnitP : ValueP EUnit                          (* () is a value *)
  | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} :
    ValueP x → ValueP y → ValueP (Pair x y)       (* a pair of values is a value *)
  | LambdaP {dom cod} (e : Exp (dom :: Γ) cod) :
    ValueP (LAM e).                               (* an abstraction is a value *)

Derive Signature for ValueP.

#[local] Hint Constructors ValueP : core.

Fixpoint ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP _ v) :
  H1 = H2.
Proof.
  dependent elimination H1;
  dependent elimination H2.
  - reflexivity.
  - f_equal;
    now apply ValueP_irrelevance.
  - f_equal;
    now apply ValueP_irrelevance.
Qed.

Lemma ValueP_dec {Γ τ} (e : Exp Γ τ) :
  ValueP Γ e ∨ ¬ ValueP Γ e.
Proof.
  induction e; try solve [now left|now right].
  destruct IHe1, IHe2.
  - left.
    now constructor.
  - right.
    intro.
    dependent elimination H.
    contradiction.
  - right.
    intro.
    dependent elimination H.
    contradiction.
  - right.
    intro.
    dependent elimination H.
    contradiction.
Qed.

End Value.

Arguments ValueP {Γ τ} _.
Arguments UnitP {Γ}.
Arguments PairP {Γ τ1 τ2 x y} _ _.
Arguments LambdaP {Γ dom cod} _.
