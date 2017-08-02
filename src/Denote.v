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
Variable get_arr : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Fixpoint term_denote {dom cod} (e : Term dom cod) :
  option (objs dom ~{C}~> objs cod) :=
  match e with
  | Identity _ => Some id
  | @Morph x y a =>
    match get_arr a with
    | Some (x'; (y'; f)) =>
      match Eq_eq_dec x' x, Eq_eq_dec y' y with
      | left edom, left ecod =>
        Some (rew [fun x => objs x  ~{ C }~> objs y] edom in
              rew [fun y => objs x' ~{ C }~> objs y] ecod in f)
      | _, _ => None
      end
    | _ => None
    end
  | Compose f g =>
    match term_denote f, term_denote g with
    | Some f, Some g => Some (f ∘ g)
    | _, _ => None
    end
  end.

Fixpoint expr_denote (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv _ _ f g => term_denote f ≈ term_denote g
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
  (Equiv 1 1 (@Compose 1 1 1 (@Morph 1 1 1) (@Compose 1 1 1 (@Morph 1 1 2) (@Morph 1 1 3)))
             (@Compose 1 1 1 (@Compose 1 1 1 (@Morph 1 1 1) (@Morph 1 1 2)) (@Morph 1 1 3)))%positive.
*)
