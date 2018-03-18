Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

Generalizable All Variables.

Inductive type : Type :=
  | Func : type -> type -> type
  | Ty : type.                 (* Ty = type given below by [var t] *)

Fixpoint typeD (var : type -> Type) (t : type) : Type :=
  match t with
  | Ty => var Ty
  | Func x y => typeD var x -> typeD var y
  end.

Inductive Scope (var : type -> Type) (t : type) : type -> Type :=
  | Here : Scope var t t
  | Next u : var u -> Scope var t u.

Arguments Here {_ _}.
Arguments Next {_ _ _} _.

Program Fixpoint map_scope {var var' : type -> Type}
        (f : forall t, var t -> var' t)
        {d ty} (e : Scope var d ty) : Scope var' d ty :=
  match e with
  | Here => Here
  | Next x => Next (f _ x)
  end.

Inductive Lambda (var : type -> Type) : type -> Type :=
  | Var : forall t : type, var t -> Lambda var t
  | Abs : forall d c : type,
      Lambda (Scope var d) c -> Lambda var (Func d c)
  | App : forall d c : type,
      Lambda var (Func d c) -> Lambda var d -> Lambda var c.

Arguments Var {var _} _.
Arguments Abs {var _ _} _.
Arguments App {var _ _} _ _.

Fixpoint lambda_size {var : type -> Type} {ty} (e : Lambda var ty) : nat :=
  match e with
  | Var x => 1
  | Abs x => 1 + lambda_size x
  | App func arg => 1 + lambda_size func + lambda_size arg
  end.

Fixpoint map_lambda {var var' : type -> Type}
         (f : forall t, var t -> var' t)
         {ty} (e : Lambda var ty) : Lambda var' ty :=
  match e with
  | Var x => Var (f _ x)
  | Abs x => Abs (map_lambda (fun _ => map_scope f) x)
  | App func arg => App (map_lambda f func) (map_lambda f arg)
  end.

Lemma map_lambda_size {var var' : type -> Type}
      (f : forall t, var t -> var' t)
      {ty} (e : Lambda var ty) :
  lambda_size (map_lambda f e) = lambda_size e.
Proof.
  generalize dependent var'.
  induction e; simpl; auto.
Defined.

Definition instantiate {var : type -> Type}
           {d c} (v : var d) (e : Lambda (Scope var d) c) :
  Lambda var c :=
  let go _ x :=
      match x with
      | Here => v
      | Next x => x
      end in
  map_lambda go e.

Corollary instantiate_size {var : type -> Type} {d c} (v : var d)
          (e : Lambda (Scope var d) c) :
  lambda_size (instantiate v e) = lambda_size e.
Proof.
  unfold instantiate.
  apply map_lambda_size.
Defined.

Import EqNotations.

Ltac simpl_eq :=
  unfold eq_rect_r, eq_rect, eq_ind_r, eq_ind, eq_sym, prod_rect,
         EqdepFacts.internal_eq_rew_r_dep,
         EqdepFacts.internal_eq_sym_involutive,
         EqdepFacts.internal_eq_sym_internal in *.

Program Fixpoint lamD {t : type} (var : type -> Type)
        (e : Lambda (typeD var) t)
        {measure (lambda_size e)} : typeD var t :=
  match e as e' in Lambda _ t'
  return forall H : t' = t, e' = rew <- H in e -> typeD var t' with
  | Var x => fun _ _ => x
  | Abs body => fun _ _ => fun arg => lamD var (instantiate arg body)
  | App func arg => fun _ _ => lamD var func (lamD var arg)
  end eq_refl eq_refl.
Next Obligation.
  rewrite instantiate_size.
  simpl_eq; subst; simpl; abstract omega.
Defined.
Next Obligation. simpl_eq; subst; simpl; abstract omega. Defined.
Next Obligation. simpl_eq; subst; simpl; abstract omega. Defined.

Print Assumptions lamD.

(* ∀ (f : () -> ()) (t : ()), f t : () *)
Definition example1 :
  Lambda (fun _ => nat) (Func Ty (Func Ty Ty)) :=
  Abs (Abs (App (Abs (Var Here)) (Var Here))).

Notation "^" := Var.
Infix "@" := App (left associativity, at level 50).
Notation "\ x : t , e" :=
  (@Abs _ t _ e) (no associativity, at level 51, x at level 0).

Eval cbv beta iota delta zeta in
    lamD (fun _ => unit) ((\x : Ty, ^Here) @ ^tt).

Eval cbv beta iota delta zeta in
    lamD (fun _ => nat) (@Abs _ Ty Ty (^(Next 5)) @ ^5).

Definition Let_In {d c var} (x : Lambda var d) (e : Lambda (Scope var d) c) :
  Lambda var c := App (Abs e) x.
