Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ty Category.Instance.Lambda.Exp
  Category.Instance.Lambda.Ren Category.Instance.Lambda.Sub
  Category.Instance.Lambda.Sem Category.Instance.Lambda.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* The generated decisions still compute, not merely prove decidability. *)
Local Definition decided {A : Set} {x y : A} (d : {x = y} + {x <> y}) : bool :=
  if d then true else false.
Example ty_yes : decided (Ty_EqDec TyUnit TyUnit) = true := eq_refl.
Example ty_no : decided (Ty_EqDec TyUnit (TyPair TyUnit TyUnit)) = false := eq_refl.
Example var_yes : decided (@Var_EqDec [TyUnit] TyUnit ZV ZV) = true := eq_refl.
Example exp_yes : decided (@Exp_EqDec [] TyUnit EUnit EUnit) = true := eq_refl.
Example ren_yes : decided (@Ren_EqDec [] [] NoRen NoRen) = true := eq_refl.
Example sub_yes : decided (@Sub_EqDec [] [] NoSub NoSub) = true := eq_refl.
Example sub_lookup : get (Push (@EUnit []) NoSub) ZV = EUnit := eq_refl.

(* Keep the signatures usable on sigma domains strictly above Set.  With the
   universes of rocq-prover/rocq#22721 the signatures have no universes of
   their own: they take [sigma@{Set}], and [sigma@{u}] is accepted there. *)
Section Larger.
  Universe u.
  Constraint Set < u.
  Definition large_subterm (x : @Equations.Init.sigma@{u} Ty (fun _ => Ty)) : Prop :=
    Ty_direct_subterm_sig x.
  Definition large_ren (x : @Equations.Init.sigma@{u} Env (fun _ => Env)) : Set :=
    Ren_sig x.
End Larger.

Definition joint_clients :=
  (@Ty_EqDec, @Var_EqDec, @Exp_EqDec, @Ren_EqDec, @Sub_EqDec, @SemExp, @Lambda_Closed).
