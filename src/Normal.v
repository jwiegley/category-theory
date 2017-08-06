Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.

Generalizable All Variables.

Section Normal.

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Import EqNotations.

(*
Inductive Arrow : Term -> Set :=

  | Here  : ∀ a, Arrow (Morph a)
  | Left  : ∀ f g, Arrow f -> Arrow (Compose f g)
  | Right : ∀ f g, Arrow g -> Arrow (Compose f g).

Definition Arrow_inv_t : forall t, Arrow t -> Type.
Proof.
  intros [] H.
  - exact False.
  - exact (H = Here a).
  - exact ((∃ H', H = Left f g H') + (∃ H', H = Right f g H')).
Defined.

Lemma Arrow_inv t f : Arrow_inv_t t f.
Proof.
  destruct f; simpl; equalities; simpl_eq; auto.
  - left. exists f0; auto.
  - right. exists f0; auto.
Defined.

Lemma Arrow_Morph `(H : Arrow (Morph a)) : H = Here a.
Proof. exact (Arrow_inv _ H). Defined.

Lemma Arrow_Compose `(H : Arrow (Compose f g)) :
  (∃ H', H = Left f g H') + (∃ H', H = Right f g H').
Proof. exact (Arrow_inv _ H). Defined.

Fixpoint get_arrow `(f : Arrow t) : arr_idx :=
  match f with
  | Here a      => a
  | Left _ _ x  => get_arrow x
  | Right _ _ x => get_arrow x
  end.

Function arrow_bequiv {t t' : Term} (p : Arrow t) (q : Arrow t') : bool :=
  match get_arrow p, get_arrow q with
  | (o, f), (o', f') => Eq_eqb o o' && Eq_eqb f f'
  end.

Function arrows (t : Term) : list (Arrow t) :=
  match t with
  | Identity _    => nil
  | Morph x y a   => [Here x y a]
  | Compose m f g => map (Left m f g) (arrows f) ++
                     map (Right m f g) (arrows g)
  end.

Function arrows_bequiv {t t' : Term}
         (ps : list (Arrow t)) (qs : list (Arrow t')) : bool :=
  match ps, qs with
  | nil, nil => true
  | cons p ps, cons q qs =>
    arrow_bequiv p q &&& arrows_bequiv ps qs
  | _, _ => false
  end.
*)

Function arrows (t : Term) : list arr_idx :=
  match t with
  | Identity    => nil
  | Morph a     => [a]
  | Compose f g => arrows f ++ arrows g
  end.

Fixpoint arrowsD_work dom (fs : list arr_idx) :
  option (∃ cod, objs dom ~{C}~> objs cod) :=
  match fs with
  | nil => Some (dom; @id _ (objs dom))
  | a :: fs =>
    match arrs a with
    | Some (x; (y; f)) =>
      match fs with
      | nil =>
        match Eq_eq_dec x dom with
        | left edom =>
          Some (y; rew [fun x => objs x ~{ C }~> objs y] edom in f)
        | _ => None
        end
      | _ =>
        match arrowsD_work dom fs with
        | Some (mid; g) =>
          match Eq_eq_dec mid x with
          | left emid =>
            Some (y; f ∘ rew [fun y => objs dom ~{ C }~> objs y] emid in g)
          | _ => None
          end
        | _ => None
        end
      end
    | _ => None
    end
  end.

Fixpoint arrowsD dom cod (fs : list arr_idx) :
  option (objs dom ~{C}~> objs cod) :=
  match arrowsD_work dom fs with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | left ecod =>
      Some (rew [fun y => objs dom ~{ C }~> objs y] ecod in f)
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

End Normal.
