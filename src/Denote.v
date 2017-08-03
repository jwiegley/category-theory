Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.

Generalizable All Variables.

Section Denote.

Import EqNotations.

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Fixpoint term_denote dom cod (e : Term) : option (objs dom ~{C}~> objs cod) :=
  match e with
  | Identity _ =>
      match Eq_eq_dec cod dom with
      | left edom =>
        Some (rew [fun x => objs x ~{ C }~> objs cod] edom in @id _ (objs cod))
      | right _ => None
      end
  (* jww (2017-08-02): Why does morph need [obj_idx] arguments? *)
  | Morph _ _ a =>
    match arrs a with
    | Some (x'; (y'; f)) =>
      match Eq_eq_dec x' dom, Eq_eq_dec y' cod with
      | left edom, left ecod =>
        Some (rew [fun x => objs x  ~{ C }~> objs cod] edom in
              rew [fun y => objs x' ~{ C }~> objs y] ecod in f)
      | _, _ => None
      end
    | _ => None
    end
  | Compose m f g =>
    match term_denote m cod f, term_denote dom m g with
    | Some f, Some g => Some (f ∘ g)
    | _, _ => None
    end
  end.

Fixpoint expr_denote (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => term_denote x y f ≈ term_denote x y g
  | Not p         => expr_denote p -> False
  | And p q       => expr_denote p ∧ expr_denote q
  | Or p q        => expr_denote p + expr_denote q
  | Impl p q      => expr_denote p -> expr_denote q
  end.

End Denote.

(*
Context {C : Category}.
Variable x : C.
Variables f g h : x ~> x.

Definition objs := (fun _ : obj_idx => x).

Eval simpl in @expr_denote C objs
  (fun i => if Pos.eqb i 1 then Some (1; (1; f)) else
            if Pos.eqb i 2 then Some (1; (1; g)) else Some (1; (1; h)))%positive
  (Equiv 1 1 (@Compose 1 (@Morph 1) (@Compose 1 (@Morph 2) (@Morph 3)))
             (@Compose 1 (@Compose 1 (@Morph 1) (@Morph 2)) (@Morph 3)))%positive.
*)