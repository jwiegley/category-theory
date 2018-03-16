Set Warnings "-notation-overridden".

Require Export Coq.PArith.PArith.
Require Export Coq.omega.Omega.

Require Export Category.Lib.

Generalizable All Variables.

Inductive STerm {A : Type} : Type :=
  | SIdent : STerm
  | SMorph (a : A) : STerm
  | SComp (f : STerm) (g : STerm) : STerm.

Arguments STerm : clear implicits.

Fixpoint sterm_size `(t : STerm A) : nat :=
  match t with
  | SIdent    => 1%nat
  | SMorph _  => 1%nat
  | SComp f g => 1%nat + sterm_size f + sterm_size g
  end.

Fixpoint sterm_map {A B : Type} (f : A -> B) (t : STerm A) : STerm B :=
  match t with
  | SIdent    => SIdent
  | SMorph a  => SMorph (f a)
  | SComp l r => SComp (sterm_map f l) (sterm_map f r)
  end.

Inductive SExpr {A : Type} : Type :=
  | STop
  | SBottom
  | SEquiv (x y : positive) (f g : STerm A)
  | SAnd   (p q : SExpr)
  | SOr    (p q : SExpr)
  | SImpl  (p q : SExpr).

Arguments SExpr : clear implicits.

Fixpoint sexpr_size `(t : SExpr A) : nat :=
  match t with
  | STop           => 1%nat
  | SBottom        => 1%nat
  | SEquiv _ _ f g => 1%nat + sterm_size f + sterm_size g
  | SAnd p q       => 1%nat + sexpr_size p + sexpr_size q
  | SOr p q        => 1%nat + sexpr_size p + sexpr_size q
  | SImpl p q      => 1%nat + sexpr_size p + sexpr_size q
  end.

Remark all_sexprs_have_size {A} e : (0 < sexpr_size (A:=A) e)%nat.
Proof. induction e; simpl; omega. Qed.

Fixpoint arrows {a} (t : STerm a) : list a :=
  match t with
  | SIdent    => List.nil
  | SMorph a  => [a]
  | SComp f g => arrows f ++ arrows g
  end.

Definition unarrows `(fs : list A) : STerm A :=
  List.fold_right (fun f rest => SComp (SMorph f) rest) SIdent fs.

Lemma unarrows_arrows `(f : list A) : arrows (unarrows f) = f.
Proof. induction f; simpl; auto; now f_equal. Qed.
