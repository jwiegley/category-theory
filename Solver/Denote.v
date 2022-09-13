Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Solver.Expr.

Generalizable All Variables.

Section Denote.

Context `{Functors}.

Import ListNotations.

Open Scope nat_scope.

Definition helper_arr `{@Arrows C} {f : nat} :
  (let '(dom, cod) := nth f tys (0, 0)
   in objD dom ~> objD cod)
    → objD (fst (nth f tys (0, 0))) ~>
      objD (snd (nth f tys (0, 0))).
Proof. destruct (nth f tys (0, 0)); auto. Defined.

Definition helper_fun {F : nat} :
  (let '(dom, cod) := nth F args (0, 0)
   in catD dom ⟶ catD cod)
    → catD (fst (nth F args (0, 0))) ~>
      catD (snd (nth F args (0, 0))).
Proof. destruct (nth F args (0, 0)); auto. Defined.

Import EqNotations.

Program Definition lookup_arr (cat : nat) (dom : Obj) (f : nat) :
  option (∃ cod, objD dom ~{catD cat}~> objD cod) :=
  let arrows := ith cat cat_arrs def_arrs in
  match eq_dec (fst (nth f tys (0, 0))) dom with
  | left H =>
      Some (snd (nth f tys (0, 0));
            rew [fun x => objD x ~> _] H in
              @helper_arr _ arrows f (ith f arrs _))
  | _ => None
  end.

Program Definition lookup_fun (dom : nat) (F : nat) :
  option (∃ cod, catD dom ⟶ catD cod) :=
  match PeanoNat.Nat.eq_dec (fst (nth F args (0, 0))) dom with
  | left H =>
      Some (snd (nth F args (0, 0));
            rew [fun x => catD x ⟶ _] H in
              @helper_fun F (ith F funs _))
  | _ => None
  end.
Next Obligation.
  exact Id.
Defined.

Axiom fobjs_dom :
  ∀ `(F : C ⟶ D) `{@Objects C} `{@Objects D} d,
    fobj[F] (objD (fobjs d)) = objD d.
Axiom fobjs_cod :
  ∀ `(F : C ⟶ D) `{@Objects C} `{@Objects D} c,
    fobj[F] (objD c) = objD (fobjs c).

Program Fixpoint termD_work (cat : nat) (dom : Obj) (e : Term) :
  option (∃ cod, objD dom ~{catD cat}~> objD cod) :=
  match e with
  | Ident => Some (dom; id)
  | Morph a => lookup_arr cat dom a
  | Comp f g =>
    match termD_work cat dom g with
    | Some (mid; g) =>
      match termD_work cat mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  | Fmap F d f =>
    match lookup_fun d F with
    | Some (c; F) =>
      match eq_dec c cat with
      | left H =>
        match termD_work d (fobjs dom) f with
        | Some (y; g) => Some (fobjs y; _)
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.
Next Obligation.
  pose (has_objects (Arrows:=ith d cat_arrs def_arrs)).
  rewrite <- (fobjs_dom F dom).
  rewrite <- (fobjs_cod F s).
  apply fmap.
  apply g.
Defined.

Definition termD cat dom cod (e : Term) :
  option (objD dom ~{catD cat}~> objD cod) :=
  match termD_work cat dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left ecod =>
      Some (rew [fun y => objD dom ~> objD y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv cat d c f g =>
    match termD cat d c f, termD cat d c g with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p → exprD q
  end.

End Denote.
