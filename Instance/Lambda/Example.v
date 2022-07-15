Require Import
  Category.Instance.Lambda.Lib
  Category.Instance.Lambda.Ty
  Category.Instance.Lambda.Exp
  Category.Instance.Lambda.Sub
  Category.Instance.Lambda.Sem
  Category.Instance.Lambda.Norm
  Category.Instance.Lambda.Eval.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Example.

Import ListNotations.

Open Scope Ty_scope.

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

Definition example_pair :
  run 30 (Pair (APP (LAM (VAR ZV)) EUnit)
               (APP (LAM (VAR ZV)) EUnit)) =
    MkΣ (Closure
           (Pair (APP (LAM (VAR ZV)) EUnit) (APP (LAM (VAR ZV)) EUnit)) NoCl) MT :=
  eq_refl.

Definition example_fst :
  run 20 (Fst (Pair (APP (LAM (VAR ZV)) EUnit)
                    (APP (LAM (VAR ZV)) EUnit))) =
    MkΣ (Closure EUnit NoCl) MT := eq_refl.

Definition example_snd :
  run 20 (Snd (Pair (APP (LAM (VAR ZV)) EUnit)
                    (APP (LAM (VAR ZV)) EUnit))) =
    MkΣ (Closure EUnit NoCl) MT := eq_refl.

End Example.
