Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Unset Universe Polymorphism.
Set Transparent Obligations.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive type : Set :=
  | Ty : type
  | Func : type -> type -> type.

Notation "x --> y" := (Func x y) (at level 55, right associativity) : type_scope.

Fixpoint typeD (var : type -> Type) (t : type) : Type :=
  match t with
  | Ty => var Ty
  | Func x y => typeD var x -> typeD var y
  end.

(** The lambda calculus

    This variant of the lambda calculus uses the "Bound" approach to lexical
    binding. It lacks the elegance of PHOAS when constructing terms in Coq
    directly, but if you are parsing an expression into this form, it has
    the benefit of no higher-order functions.

    Using Scope, referencing an unbound variable is a type error, and
    referencing a bound variable of the wrong type is also a type error.
    The type of free variables is given by [var] at the outermost level. *)

Inductive preterm : Set :=
  | Var (i : nat)
  | Abs (d : type) (body : preterm)
  | App (arg body : preterm).

Notation "% x" := (Var x) (at level 20).
Infix "@" := App (at level 25, left associativity).
Notation "\ A => M" := (Abs A M) (at level 35).

Reserved Notation "E |- Pt := A" (at level 60).

Require Import Coq.Lists.List.

Definition Env := list (option type).
Definition EmptyEnv : Env := nil.
Definition VarD E x (A : type) := nth_error E x = Some (Some A).
Definition VarUD E x := nth_error E x = None \/
                        nth_error E x = Some (None : option type).
Notation "E |= x := A" := (VarD E x A) (at level 60).
Notation "E |= x :!"   := (VarUD E x) (at level 60).

Definition decl (A : type) E := Some A :: E.

Infix "[#]" := decl (at level 20, right associativity).

Inductive Typing : Env -> preterm -> type -> Set :=
  | TVar: ∀ Γ x α,                            (* x : α ∈ Γ *)
         Γ |= x := α                          (* --------- *)
      -> Γ |- %x := α                         (* Γ ⊢ x : α *)

  | TAbs: ∀ Γ α β t,                          (*  Γ ∪ {x : α} ⊢ t : β  *)
         α [#] Γ |- t := β                    (* --------------------- *)
      -> Γ |- \α => t := α --> β              (* Γ ⊢ λx : α. t : α → β *)

  | TApp: ∀ Γ α β t u,                        (* Γ ⊢ t : α → β   Γ ⊢ u : α *)
         Γ |- t := α --> β  ->  Γ |- u := α   (* ------------------------- *)
      -> Γ |- t @ u := β                      (*       Γ ⊢ t u : β         *)

  where "Γ |- t := α" := (Typing Γ t α).

Record term : Set := mkterm {
  env    : Env;
  tm     : preterm;
  ty     : type;
  typing : Typing env tm ty
}.

Lemma Type_unique : ∀ Pt E T1 T2
  (D1 : Typing E Pt T1) (D2 : Typing E Pt T2), T1 = T2.
Proof.
  intros.
  generalize dependent E.
  generalize dependent T1.
  generalize dependent T2.
  induction Pt; simpl; intros.
  - inversion_clear D1.
    inversion H; subst; clear H.
    inversion_clear D2.
    inversion H; subst; clear H.
    rewrite H1 in H2.
    now inversion_clear H2.
  - inversion_clear D1.
    inversion_clear D2.
    f_equal.
    now eapply IHPt; eauto.
  - inversion_clear D1.
    inversion_clear D2.
    specialize (IHPt1 _ _ _ H H1).
    specialize (IHPt2 _ _ _ H0 H2).
    subst.
    now inversion_clear IHPt1.
Qed.

Lemma typing_unique : ∀ E Pt T (D1 D2 : Typing E Pt T),
  D1 = D2.
Proof.
  intros.
  apply Eqdep_dec.eq_dep_eq_dec.
    apply type_eq_dec.
Admitted.

Lemma term_eq : ∀ M N,
  env M = env N -> tm M = tm N -> M = N.
Proof.
  intros.
  destruct M, N; simpl in *; subst.
  pose proof (Type_unique _ _ _ _ typing0 typing1); subst.
  f_equal.
  apply typing_unique.
Qed.

Theorem autoType E Pt :
  { N : term | env N = E & tm N = Pt} +
  { ~ exists N : term, env N = E /\ tm N = Pt}.
Proof.
(*
  destruct ({ α : type & Typing E Pt α } + { ~ exists α : type, Typing E Pt α }).
  generalize dependent E.

  induction Pt; intros.
  - left.
    exists {| env := E; tm := %i; ty := Ty; typing := TVar _ _ _ |}.
*)
Abort.

Inductive Scope (var : type -> Type) (t : type) : type -> Type :=
  | Here : Scope var t t
  | Next u : var u -> Scope var t u.

Arguments Here {_ _}.
Arguments Next {_ _ _} _.

Fixpoint scope_map {var var' : type -> Type} (f : ∀ t, var t -> var' t)
        {d ty} (e : Scope var d ty) : Scope var' d ty :=
  match e with
  | Here => Here
  | Next x => Next (f _ x)
  end.

Arguments Var {var _} _.
Arguments Abs {var _ _} _.
Arguments App {var _ _} _ _.

Fixpoint lam_size {var : type -> Type} {ty} (e : Lam var ty) : nat :=
  match e with
  | Var x => 1
  | Abs x => 1 + lam_size x
  | App func arg => 1 + lam_size func + lam_size arg
  end.

Fixpoint lam_map {var var' : type -> Type} (f : ∀ t, var t -> var' t)
         {ty} (e : Lam var ty) : Lam var' ty :=
  match e with
  | Var x => Var (f _ x)
  | Abs x => Abs (lam_map (fun _ => scope_map f) x)
  | App func arg => App (lam_map f func) (lam_map f arg)
  end.

Lemma lam_map_size {var var' : type -> Type}
      (f : ∀ t, var t -> var' t) {ty} (e : Lam var ty) :
  lam_size (lam_map f e) = lam_size e.
Proof.
  generalize dependent var'.
  induction e; simpl; auto.
Defined.

(** Instantiating a bound variable is function application. *)

Definition instantiate {var : type -> Type}
           {d c} (v : var d) (e : Lam (Scope var d) c) : Lam var c :=
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
        (e : Lam (typeD var) t) {measure (lam_size e)} : typeD var t :=
  match e as e' in Lam _ t'
  return ∀ H : t' = t, e' = rew <- H in e -> typeD var t' with
  | Var x        => fun _ _ => x
  | Abs body     => fun _ _ => fun arg => lamD var (instantiate arg body)
  | App func arg => fun _ _ => lamD var func (lamD var arg)
  end eq_refl eq_refl.
Next Obligation.
  rewrite instantiate_size.
  simpl_eq; subst; simpl; abstract omega.
Defined.
Next Obligation. simpl_eq; subst; simpl; abstract omega. Defined.
Next Obligation. simpl_eq; subst; simpl; abstract omega. Defined.

(* ∀ (f : () -> ()) (t : ()), f t : () *)
Definition example1 :
  Lam (fun _ => nat) (Func Ty (Func Ty Ty)) :=
  Abs (Abs (App (Abs (Var Here)) (Var Here))).

Notation "^" := Var.
Infix "@" := App (left associativity, at level 50).
Notation "\ x : t , e" :=
  (@Abs _ t _ e) (no associativity, at level 51, x at level 0, only parsing).

(*
Eval cbv beta iota delta zeta in
    lamD (fun _ => Datatypes.unit) ((\x : Ty, ^Here) @ ^tt).

Eval cbv beta iota delta zeta in
    lamD (fun _ => Datatypes.nat) (@Abs _ Ty Ty (^(Next 5%nat)) @ ^5%nat).
*)

Require Import Coq.Strings.String.

Open Scope string_scope.

Inductive ty : Type :=
  | Name : string -> ty
  | Func : ty → ty → ty.

Inductive tm : Type :=
  | var : string → tm
  | app : tm → tm → tm
  | abs : string → ty → tm → tm.

Inductive value : tm → Prop :=
  | v_abs : ∀ x T t,
      value (abs x T t).

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var x' =>
      if string_dec x x' then s else t
  | abs x' T t1 =>
      abs x' T (if string_dec x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

 Inductive substi (s:tm) (x:string) : tm → tm → Prop :=
  | s_var1 :
      substi s x (var x) s
  | s_var2 : ∀ x0,
      substi s x (var x0) (var x0)
  | s_abs : ∀ T t1,
      substi s x (abs x T t1) s
  | s_app : ∀ t1 t2,
      substi s x (app t1 t2) s.

Hint Constructors substi.

Theorem substi_correct : ∀ s x t t',
  [x:=s]t = t' ↔ substi s x t t'.
Proof.
  split; intros.
  - induction t.
    + simpl in H.
      destruct (string_dec x s0); subst.
        constructor.
      constructor.
Admitted.

Reserved Notation "t1 '===>' t2" (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_AppAbs : ∀ x T t12 v2,
         value v2 →
         (app (abs x T t12) v2) ===> [x:=v2]t12
  | ST_App1 : ∀ t1 t1' t2,
         t1 ===> t1' →
         app t1 t2 ===> app t1' t2
  | ST_App2 : ∀ v1 t2 t2',
         value v1 →
         t2 ===> t2' →
         app v1 t2 ===> app v1 t2'

where "t1 '===>' t2" := (step t1 t2).

Hint Constructors step.

(* Notation multistep := (multi step). *)
(* Notation "t1 '===>*' t2" := (multistep t1 t2) (at level 40). *)

Reserved Notation "Gamma '|-' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=
  | T_Var : ∀ Gamma x T,
      Gamma x = Some T →
      Gamma |- tvar x ∈ T
  | T_Abs : ∀ Gamma x T11 T12 t12,
      Gamma & {{x --> T11}} |- t12 ∈ T12 →
      Gamma |- tabs x T11 t12 ∈ TArrow T11 T12
  | T_App : ∀ T11 T12 Gamma t1 t2,
      Gamma |- t1 ∈ TArrow T11 T12 →
      Gamma |- t2 ∈ T11 →
      Gamma |- tapp t1 t2 ∈ T12
  | T_True : ∀ Gamma,
       Gamma |- ttrue ∈ TBool
  | T_False : ∀ Gamma,
       Gamma |- tfalse ∈ TBool
  | T_If : ∀ t1 t2 t3 T Gamma,
       Gamma |- t1 ∈ TBool →
       Gamma |- t2 ∈ T →
       Gamma |- t3 ∈ T →
       Gamma |- tif t1 t2 t3 ∈ T

where "Gamma '|-' t '∈' T" := (has_type Gamma t T).

Hint Constructors has_type.

Program Definition Lambda : Category := {|
  obj     := type;
  hom     := fun x y => ∀ var : type -> Type, Lam var (Func x y);
  homset  := fun x y => {| equiv := fun f g =>
    ∀ v, lamD v (f _) = lamD v (g _)
  |};
  id      := fun x => fun v => \ v : x, ^ Here;
  compose := fun x y z f g => fun v => Abs (f (Scope v x) @ (g (Scope v x) @ (^ Here)));
|}.
Next Obligation.
  equivalence.
  congruence.
Qed.
Next Obligation.
  proper.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.
Next Obligation.
  simpl.
