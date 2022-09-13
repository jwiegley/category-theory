Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.

Definition Obj := nat.

Definition objD' {C : Category} (d : C) (objs : list C) (n : Obj) : C :=
  List.nth n objs d.

Definition arrD' {C : Category} (d : C) (objs : list C) '(dom, cod) :=
  objD' d objs dom ~> objD' d objs cod.

Class Objects (cat : Category) := {
  def_obj : cat;
  objs : list cat;
  objD := objD' def_obj objs;
}.

Class Arrows (cat : Category) := {
  has_objects : Objects cat;

  arrD := arrD' def_obj objs;
  tys  : list (Obj * Obj);
  arrs : ilist (B:=arrD) tys;
}.
#[export] Existing Instance has_objects.

Definition catD' (d : Cat) (cats : list Cat) (n : nat) : Cat :=
  List.nth n cats d.

Definition funD' (d : Cat) (cats : list Cat) '(dom, cod) :=
  catD' d cats dom ⟶ catD' d cats cod.

Class Categories := {
  def_cat : Cat;
  cats : list Cat;
  catD := catD' def_cat cats;
  def_arrs : Arrows def_cat;
  cat_arrs : ilist (B:=Arrows) cats;
}.

Class Functors := {
  has_cats : Categories;

  funD := funD' def_cat cats;
  args : list (nat * nat);
  funs : ilist (B:=funD) args;

  (* fobjs : list (nat * nat); *)
  fobjs : nat → nat;

  (* fobj[F] (objD (fobjs d)) = objD d *)
  (* fobj[F] (objD c) = objD (fobjs c) *)
}.
#[export] Existing Instance has_cats.

Inductive Term : Set :=
  | Ident
  | Morph (a : nat)
  | Comp (f g : Term)
  | Fmap (F : nat) (d : Obj) (f : Term).

Inductive Expr : Set :=
  | Top
  | Bottom
  | Equiv (cat : nat) (d c : Obj) (f g : Term)
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr).
