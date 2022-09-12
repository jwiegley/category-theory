Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.
Set Transparent Obligations.

Inductive Obj : Set :=
  | Ob : nat → Obj
  | Pair : Obj → Obj → Obj.

Derive NoConfusion NoConfusionHom Subterm EqDec for Obj.

Fixpoint objD' {C: Category} `{@Cartesian C}
  (d : C) (objs : list C) (x : Obj) :=
  match x with
  | Ob n => nth n objs d
  | Pair x y => objD' d objs x × objD' d objs y
  end.

Definition arrD' {C: Category} `{@Cartesian C}
  (d : C) (objs : list C) '(dom, cod) :=
  objD' d objs dom ~> objD' d objs cod.

Class Objects := {
  cat     : Category;
  cart    : @Cartesian cat;
  (* Note that we one extra object here (doubling the last), just for the
     convenience of always knowing by the type that there must be one more
     than [num_objs] available. This saves us from having to maintain
     [num_objs] as the "size minus one". *)
  def_obj : cat;
  objs    : list cat;
  objD   := objD' def_obj objs;
}.
#[export] Existing Instance cart.

Class Arrows := {
  has_objects : Objects;

  arrD  := arrD' def_obj objs;
  tys    : list (Obj * Obj);
  arrs   : ilist (B:=arrD) tys;
}.
#[export] Existing Instance has_objects.

Inductive Term : Set :=
  | Ident : Term
  | Morph (a : nat) : Term
  | Comp (f g : Term) : Term

  (* Cartesian structure *)
  | Fork (f g : Term) : Term
  | Exl : Term
  | Exr : Term.

Derive NoConfusion NoConfusionHom Subterm EqDec for Term.

Inductive Expr : Set :=
  | Top
  | Bottom
  | Equiv (x y : Obj) (f g : Term)
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr).

Derive NoConfusion NoConfusionHom Subterm for Expr.
