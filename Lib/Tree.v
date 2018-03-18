Set Warnings "-notation-overridden".

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Lib.TList.
(* Require Import Category.Lib.IList. *)

Generalizable All Variables.

Section Tree.

Variables A : Type.

Inductive tree : Type :=
  | Leaf : tree
  | Node (f : A) : tree
  | Branch (f g : tree) : tree.

Fixpoint inorder (t : tree) : list A :=
  match t with
  | Leaf => nil
  | Node f => f :: nil
  | Branch f g => inorder f ++ inorder g
  end.

End Tree.

Section TTree.

Record TreeDesc := {
  indexType : Type;
  valueType : Type;
  valueDom : valueType -> indexType;
  valueCod : valueType -> indexType;
}.

Context {td : TreeDesc}.

Inductive ttree : indexType td -> indexType td -> Type :=
  | TLeaf (d : indexType td) : ttree d d
  | TNode (f : valueType td) : ttree (valueDom td f) (valueCod td f)
  | TBranch (d m c : indexType td) (f : ttree d m) (g : ttree m c) : ttree d c.

Fixpoint tinorder `(t : ttree d c) : tlist (fun _ _ => valueType td) d c :=
  match t with
  | TLeaf _ => tnil
  | TNode f => f ::: tnil
  | TBranch d m c f g => tinorder f +++ tinorder g
  end.

Record Related := {
  forgetIndex : Type;
  forgetType : Type;
  project : valueType td -> forgetType;
  recover : forgetType -> option (valueType td);
  project_recover (x : valueType td) : recover (project x) = Some x;
  recover_project (x : forgetType) y : recover x = Some y -> project y = x
}.

Context {rd : Related}.
Context `{EqDec (indexType td)}.

Context {E : Type}.

Variable tleaf : E.
Variable tnode : forall f : forgetType rd, E.
Variable tbranch : E -> E -> E.

Fixpoint tfold `(t : ttree d c) : E :=
  match t with
  | TLeaf _ => tleaf
  | TNode f => tnode (project rd f)
  | TBranch d m c f g => tbranch (tfold f) (tfold g)
  end.

Import EqNotations.

Context {D : indexType td -> indexType td -> Type}.

Variable leaf : forall d, D d d.
Variable node : forall f : valueType td, D (valueDom td f) (valueCod td f).
Variable branch : forall d m c, D d m -> D m c -> D d c.

Fixpoint fold_work d (e : tree (forgetType rd)) : option (∃ c, D d c) :=
  match e with
  | Leaf _ => Some (d; leaf d)
  | Node _ a =>
    match recover rd a with
    | Some f =>
      match eq_dec (valueDom td f) d with
      | left H =>
        Some (valueCod td f; rew [fun x => D x _] H in node f)
      | _ => None
      end
    | _ => None
    end
  | Branch _ f g =>
    match fold_work d f with
    | Some (m; f) =>
      match fold_work m g with
      | Some (c; g) => Some (c; branch d m c f g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition fold d c (e : tree (forgetType rd)) : option (D d c) :=
  match fold_work d e with
  | Some (y; e) =>
    match eq_dec y c with
    | Specif.left H => Some (rew [fun y => D _ y] H in e)
    | _ => None
    end
  | _ => None
  end.

End TTree.

Section Functions.

Context {td : TreeDesc}.
Context `{EqDec (indexType td)}.
Context {rd : @Related td}.

Fixpoint demote `(t : ttree d c) : tree (forgetType rd) :=
  tfold (Leaf _) (Node _) (Branch _) t.

Definition promote (d c : indexType td) (e : tree (forgetType rd)) :
  option (ttree d c) := fold TLeaf TNode TBranch d c e.

(*
Inductive trose : indexType td -> indexType td -> Type :=
  | RLeaf (d : indexType td) : trose d d
  | RNode (f : valueType td) (arity : nat)
          (tys : Vector.t (indexType td * indexType td) arity)
          (xs : list (trose (valueDom td f) (valueCod td f)))  :
      trose (valueDom td f) (valueCod td f)
  | RBranch (d m c : indexType td) (f : trose d m) (g : trose m c) : trose d c.
*)

End Functions.
