Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Wf.

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

Fixpoint scope_map {var var' : type -> Type}
        (f : forall t, var t -> var' t)
        {d ty} (e : Scope var d ty) : Scope var' d ty :=
  match e with
  | Here => Here
  | Next x => Next (f _ x)
  end.

(** The lambda calculus

    This variant of the lambda calculus uses the "Bound" approach to lexical
    binding. It lacks the elegance of PHOAS when constructing terms in Coq
    directly, but if you are parsing an expression into this form, it has
    the benefit of no higher-order functions.

    Using Scope, referencing an unbound variable is a type error, and
    referencing a bound variable of the wrong type is also a type error.
    The type of free variables is given by [var] at the outermost level. *)

Inductive Lam (var : type -> Type) : type -> Type :=
  | Var : forall t   : type, var t -> Lam var t
  | Abs : forall d c : type, Lam (Scope var d) c -> Lam var (Func d c)
  | App : forall d c : type, Lam var (Func d c) -> Lam var d -> Lam var c.

Arguments Var {var _} _.
Arguments Abs {var _ _} _.
Arguments App {var _ _} _ _.

Fixpoint lam_size {var : type -> Type} {ty} (e : Lam var ty) : nat :=
  match e with
  | Var x => 1
  | Abs x => 1 + lam_size x
  | App func arg => 1 + lam_size func + lam_size arg
  end.

Fixpoint lam_map {var var' : type -> Type} (f : forall t, var t -> var' t)
         {ty} (e : Lam var ty) : Lam var' ty :=
  match e with
  | Var x => Var (f _ x)
  | Abs x => Abs (lam_map (fun _ => scope_map f) x)
  | App func arg => App (lam_map f func) (lam_map f arg)
  end.

Lemma lam_map_size {var var' : type -> Type}
      (f : forall t, var t -> var' t) {ty} (e : Lam var ty) :
  lam_size (lam_map f e) = lam_size e.
Proof.
  generalize dependent var'.
  induction e; simpl; auto.
Defined.

(** Instantiating a bound variable is function application. *)

Definition instantiate {var : type -> Type}
           {d c} (v : var d) (e : Lam (Scope var d) c) :
  Lam var c :=
  let go _ x :=
      match x with
      | Here => v
      | Next x => x
      end in
  lam_map go e.

Corollary instantiate_size {var : type -> Type} {d c} (v : var d)
          (e : Lam (Scope var d) c) :
  lam_size (instantiate v e) = lam_size e.
Proof.
  unfold instantiate.
  apply lam_map_size.
Defined.

Import EqNotations.

Ltac simpl_eq :=
  unfold eq_rect_r, eq_rect, eq_ind_r, eq_ind, eq_sym, prod_rect,
         EqdepFacts.internal_eq_rew_r_dep,
         EqdepFacts.internal_eq_sym_involutive,
         EqdepFacts.internal_eq_sym_internal in *.

Program Fixpoint lamD {t : type} (var : type -> Type)
        (e : Lam (typeD var) t)
        {measure (lam_size e)} : typeD var t :=
  match e as e' in Lam _ t'
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
  Lam (fun _ => nat) (Func Ty (Func Ty Ty)) :=
  Abs (Abs (App (Abs (Var Here)) (Var Here))).

Notation "^" := Var.
Infix "@" := App (left associativity, at level 50).
Notation "\ x : t , e" :=
  (@Abs _ t _ e) (no associativity, at level 51, x at level 0, only parsing).

Eval cbv beta iota delta zeta in
    lamD (fun _ => unit) ((\x : Ty, ^Here) @ ^tt).

Eval cbv beta iota delta zeta in
    lamD (fun _ => nat) (@Abs _ Ty Ty (^(Next 5)) @ ^5).
