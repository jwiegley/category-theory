Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Equations.Equations.
Require Import Equations.EqDec.

Require Import Category.Lib.
Require Import Category.Lib.TList.

Generalizable All Variables.

Section Tree.

Variables A : Type.

Inductive tree : Type :=
  | Leaf (f : A) : tree
  | Branch (f g : tree) : tree.

Fixpoint prefold {C : Type} (f : A -> C -> C) (z : C) (t : tree) : C :=
  match t with
  | Leaf x => f x z
  | Branch l r => prefold f (prefold f z r) l
  end.

Fixpoint preorder_direct (t : tree) : list A :=
  match t with
  | Leaf f => f :: nil
  | Branch f g => preorder_direct f ++ preorder_direct g
  end.

Definition preorder : tree -> list A := prefold cons nil.

Lemma prefold_app xs ys t :
  prefold cons (xs ++ ys)%list t = (prefold cons xs t ++ ys)%list.
Proof.
  generalize dependent ys.
  generalize dependent xs.
  induction t; simpl; intros; auto.
  now rewrite IHt2, IHt1.
Qed.

Lemma preorder_spec t :
  preorder t = preorder_direct t.
Proof.
  unfold preorder.
  induction t; simpl; auto.
  rewrite IHt2.
  replace (preorder_direct t2)
    with ([] ++ preorder_direct t2)%list at 1 by auto.
  now rewrite prefold_app, IHt1.
Qed.

End Tree.

Section TTree.

Variables A B : Type.
Variables dom cod : B -> A.

Inductive ttree : A -> A -> Type :=
  | TLeaf (f : B) : ttree (dom f) (cod f)
  | TBranch (d m c : A) (f : ttree d m) (g : ttree m c) : ttree d c.

Arguments TBranch {d m c} f g.

Equations tprefold {C : A -> A -> Type} {d c}
          (f : forall i (x : B), C (cod x) i -> C (dom x) i)
          {i} (z : C c i) (t : ttree d c) : C d i :=
  tprefold f z (TLeaf x) := f _ x z;
  tprefold f z (TBranch l r) := tprefold f (tprefold f z r) l.

Definition tpreorder {d c} : ttree d c -> tlist (fun _ _ => B) d c :=
   tprefold (C:=tlist (fun _ _ => B)) (fun _ x l => x ::: l) tnil.

Fixpoint tpreorder_direct {d c} (t : ttree d c) : tlist (fun _ _ => B) d c :=
  match t with
  | TLeaf f => f ::: tnil
  | TBranch f g => tpreorder_direct f +++ tpreorder_direct g
  end.

Lemma tprefold_app {d c i j} (t : ttree d c)
      (xs : tlist (fun _ _ => B) c i) (ys : tlist (fun _ _ => B) i j) :
  tprefold (C:=tlist (fun _ _ => B)) (fun _ x l => x ::: l) (xs +++ ys) t
    = tprefold (C:=tlist (fun _ _ => B)) (fun _ x l => x ::: l) xs t +++ ys.
Proof.
  generalize dependent ys.
  generalize dependent xs.
  generalize dependent j.
  generalize dependent i.
  generalize dependent c.
  generalize dependent d.
  induction t; simpl; intros; auto.
    rewrite !tprefold_equation_1.
    now rewrite tlist_app_comm_cons.
  rewrite !tprefold_equation_2.
  now rewrite IHt2, IHt1.
Qed.

Lemma tpreorder_spec d c (t : ttree d c) :
  tpreorder t = tpreorder_direct t.
Proof.
  unfold tpreorder.
  generalize dependent c.
  generalize dependent d.
  induction t; simpl; auto.
  rewrite tprefold_equation_2.
  rewrite IHt2.
  replace (tpreorder_direct t2)
    with (tnil +++ tpreorder_direct t2)%list at 1 by auto.
  rewrite tprefold_app.
  now rewrite IHt1.
Qed.

End TTree.
