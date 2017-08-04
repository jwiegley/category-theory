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
Require Import Solver.Normal.

Generalizable All Variables.

Section Denote.

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Import EqNotations.

Fixpoint termD dom cod (e : Term) : option (objs dom ~{C}~> objs cod) :=
  match e with
  | Identity _ =>
      match Eq_eq_dec cod dom with
      | left edom =>
        Some (rew [fun x => objs x ~{ C }~> objs cod] edom in @id _ (objs cod))
      | right _ => None
      end
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
  | Compose mid f g =>
    match termD mid cod f, termD dom mid g with
    | Some f, Some g => Some (f ∘ g)
    | _, _ => None
    end
  end.

Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => termD x y f ≈ termD x y g
  (* | Not p         => exprD p -> False *)
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Fixpoint arrowsD dom cod `(fs : list (Arrow t)) :
  option (objs dom ~{C}~> objs cod) :=
  match fs with
  | nil =>
    match Eq_eq_dec cod dom with
    | left edom =>
      Some (rew [fun x => objs x ~{ C }~> objs cod] edom in @id _ (objs cod))
    | right _ => None
    end
  | cons f nil =>
    match arrs (snd (get_arrow f)) with
    | Some (x'; (y'; f)) =>
      match Eq_eq_dec x' dom, Eq_eq_dec y' cod with
      | left edom, left ecod =>
        Some (rew [fun x => objs x  ~{ C }~> objs cod] edom in
              rew [fun y => objs x' ~{ C }~> objs y] ecod in f)
      | _, _ => None
      end
    | _ => None
    end
  | cons f fs =>
    let '(x, a) := get_arrow f in
    match arrowsD dom x fs with
    | Some g =>
      match arrs a with
      | Some (x'; (y'; f)) =>
        match Eq_eq_dec x' x, Eq_eq_dec y' cod with
        | left edom, left ecod =>
          Some (rew [fun x => objs x  ~{ C }~> objs cod] edom in
                rew [fun y => objs x' ~{ C }~> objs y] ecod in f ∘ g)
        | _, _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => arrowsD x y (arrows f) ≈ arrowsD x y (arrows g)
  (* | Not p         => exprD p -> False *)
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Theorem arrowsD_sound {p dom cod f} :
  arrowsD dom cod (arrows p) = Some f ->
  ∃ f', f ≈ f' ∧ termD dom cod p = Some f'.
Proof.
Admitted.

Lemma arrowsD_apply dom cod (f g : Term) :
  arrows_bequiv (arrows f) (arrows g) = true ->
  arrowsD dom cod (arrows f) ||| false = true ->
  arrowsD dom cod (arrows f) = arrowsD dom cod (arrows g) ->
  termD dom cod f ≈ termD dom cod g.
Proof.
  intros.
  destruct (arrowsD dom cod (arrows f)) eqn:?; [|discriminate].
  destruct (arrowsD_sound Heqo), p.
  rewrite e0; clear e0.
  rewrite H1 in Heqo; clear H1.
Admitted.

Lemma exprAD_sound (e : Expr) : exprAD e -> exprD e.
Proof.
  destruct e; auto; intros.
  red in X; red.
  apply arrowsD_apply; auto.
Abort.

End Denote.
