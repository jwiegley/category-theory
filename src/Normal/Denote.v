Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapPositive.

Module Import MP := FMapPositive.
Module M := MP.PositiveMap.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Normal.Arrow.

Generalizable All Variables.

Section NormalDenote.

Context `{Env}.

Import EqNotations.

Fixpoint arrowsD_work dom (fs : list arr_idx) :
  option (∃ cod, objs dom ~> objs cod) :=
  match fs with
  | nil => Some (dom; @id _ (objs dom))
  | a :: fs =>
    match arrs a with
    | Some (x; (y; f)) =>
      match fs with
      | nil =>
        match Eq_eq_dec x dom with
        | left edom =>
          Some (y; rew [fun x => objs x ~> objs y] edom in f)
        | _ => None
        end
      | _ =>
        match arrowsD_work dom fs with
        | Some (mid; g) =>
          match Eq_eq_dec mid x with
          | left emid =>
            (* jww (2017-08-06): This associates the wrong way, which doesn't
               technically matter, but does make the normalized results look
               funny. At some point, the correct orientation should be
               done. *)
            Some (y; f ∘ rew [fun y => objs dom ~> objs y] emid in g)
          | _ => None
          end
        | _ => None
        end
      end
    | _ => None
    end
  end.

Definition arrowsD dom cod (fs : list arr_idx) :
  option (objs dom ~> objs cod) :=
  match arrowsD_work dom fs with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | left ecod => Some (rew [fun y => objs dom ~> objs y] ecod in f)
    | right _ => None
    end
  | _ => None
  end.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => arrowsD x y (arrows f) ≈ arrowsD x y (arrows g)
  | And p q       => exprAD p ∧ exprAD q
  | Or p q        => exprAD p + exprAD q
  | Impl p q      => exprAD p -> exprAD q
  end.

End NormalDenote.
