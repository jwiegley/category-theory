Set Warnings "-notation-overridden".

Require Export Solver.Env.
Require Import Category.Instance.Coq.

Unset Equations WithK.

Generalizable All Variables.

Inductive Term {A : Type} : Type :=
  | Ident : Term
  | Morph (a : A) : Term
  | Comp (f : Term) (g : Term) : Term.

Arguments Term : clear implicits.

Fixpoint term_size `(t : Term A) : nat :=
  match t with
  | Ident    => 1%nat
  | Morph _  => 1%nat
  | Comp f g => 1%nat + term_size f + term_size g
  end.

Fixpoint term_map {A B : Type} (f : A -> B) (t : Term A) : Term B :=
  match t with
  | Ident    => Ident
  | Morph a  => Morph (f a)
  | Comp l r => Comp (term_map f l) (term_map f r)
  end.

Inductive Expr {A : Type} : Type :=
  | Top
  | Bottom
  | Equiv (x y : obj_idx) (f g : Term A)
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr).

Arguments Expr : clear implicits.

Fixpoint expr_size `(t : Expr A) : nat :=
  match t with
  | Top           => 1%nat
  | Bottom        => 1%nat
  | Equiv _ _ f g => 1%nat + term_size f + term_size g
  | And p q       => 1%nat + expr_size p + expr_size q
  | Or p q        => 1%nat + expr_size p + expr_size q
  | Impl p q      => 1%nat + expr_size p + expr_size q
  end.

Remark all_exprs_have_size {A} e : (0 < expr_size (A:=A) e)%nat.
Proof. induction e; simpl; omega. Qed.

(** Syntactic terms are endofunctors on Coq. *)

Program Definition TermF : Coq ⟶ Coq := {|
  fmap := @term_map
|}.
Next Obligation.
  proper.
  induction x1; simpl; auto.
    now rewrite H.
  now rewrite IHx1_1, IHx1_2.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  now rewrite IHx0_1, IHx0_2.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  now rewrite IHx0_1, IHx0_2.
Qed.

Global Program Instance TermF_Map : EndoFunctor TermF :=
  Functor_EndoFunctor (F:=TermF).

(** A lawful way of saying that Term is Foldable. *)

Fixpoint arrows {a} (t : Term a) : list a :=
  match t with
  | Ident    => nil
  | Morph a  => [a]
  | Comp f g => arrows f ++ arrows g
  end.

Definition unarrows `(fs : list A) : Term A :=
  List.fold_right (fun f rest => Comp (Morph f) rest) Ident fs.

Lemma unarrows_arrows `(f : list A) : arrows (unarrows f) = f.
Proof. induction f; simpl; auto; now f_equal. Qed.

Global Program Instance Term_Foldable : TermF ⟹ listF := {
  transform := fun _ => arrows
}.
Next Obligation.
  induction x0; simpl; auto.
  rewrite <- IHx0_1, <- IHx0_2.
  now rewrite List.map_app.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  rewrite IHx0_1, IHx0_2.
  now rewrite List.map_app.
Qed.

(** Term is also Traversable.

    jww (2018-03-10): For the moment this is too painful to do this generally,
    so we do it for the few cases that we need. *)

Fixpoint Term_option_sequence {a} (x : Term (option a)) : option (Term a) :=
  match x with
  | Ident => Some Ident
  | Morph a => map[optionF] Morph a
  | Comp f g =>
    match Term_option_sequence f with
    | None => None
    | Some f' =>
      match Term_option_sequence g with
      | None => None
      | Some g' =>
        Some (Comp f' g')
      end
    end
  end.

Global Program Instance Term_option_Traversable :
  TermF ○ optionF ⟹ optionF ○ TermF := {
  transform := fun _ => Term_option_sequence
}.
Next Obligation.
  intros.
  induction x0; simpl; auto.
  - destruct a; auto.
  - rewrite <- IHx0_1, <- IHx0_2.
    clear IHx0_1 IHx0_2.
    do 2 destruct (Term_option_sequence _); auto.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  - destruct a; auto.
  - rewrite IHx0_1, IHx0_2.
    clear IHx0_1 IHx0_2.
    do 2 destruct (Term_option_sequence _); auto.
Qed.

(** The category of syntactic terms, equivalent up to normalization. *)

Definition Term_equiv `{Setoid A} (f g : Term A) : Type :=
  arrows f = arrows g.
Arguments Term_equiv {A _} f g /.

Program Instance Term_equivalence `{Setoid A} :
  Equivalence Term_equiv.

Instance Term_Setoid `{Setoid A} : Setoid (Term A) := {|
  equiv := Term_equiv;
  setoid_equiv := Term_equivalence
|}.

Program Instance Comp_Proper `{Setoid A} :
  Proper (equiv ==> equiv ==> equiv) (@Comp A).
Next Obligation.
  proper.
  simpl in *.
  now rewrite X, X0.
Qed.

Program Instance Terms (A : Type) `{Setoid A} : Category := {|
  obj := obj_idx;
  hom := fun _ _ => Term A;
  id := fun _ => Ident;
  compose := fun _ _ _ => Comp
|}.
Next Obligation. now rewrite List.app_nil_r. Defined.
Next Obligation. now rewrite List.app_assoc. Defined.
Next Obligation. now rewrite List.app_assoc. Defined.
