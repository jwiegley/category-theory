Set Warnings "-notation-overridden".

Require Import Equations.Equations.
Require Import Equations.EqDec.

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Instance.Lambda.Stlc.

Generalizable All Variables.
Set Primitive Projections.
Unset Universe Polymorphism.
Set Transparent Obligations.

(*
Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive type : Set :=
  | Ty : type
  | Func : type -> type -> type.

Derive NoConfusion Subterm EqDec for type.

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

Derive NoConfusion Subterm EqDec for preterm.

Notation "% x" := (Var x) (at level 20).
Infix "@" := App (at level 25, left associativity).
Notation "\ A => M" := (Abs A M) (at level 35).

Reserved Notation "E |- t := A" (at level 60).

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
Notation "E ∪ { A }" := (decl A E) (at level 20, right associativity).

Inductive Typing : Env -> preterm -> type -> Set :=
  | TVar: ∀ Γ x α,                            (* x : α ∈ Γ *)
         Γ |= x := α                          (* --------- *)
      -> Γ |- %x := α                         (* Γ ⊢ x : α *)

  | TAbs: ∀ Γ α β t,                          (*  Γ ∪ {x : α} ⊢ t : β  *)
         Γ ∪ {α} |- t := β                    (* --------------------- *)
      -> Γ |- \α => t := α --> β              (* Γ ⊢ λx : α. t : α → β *)

  | TApp: ∀ Γ α β t u,                        (* Γ ⊢ t : α → β   Γ ⊢ u : α *)
         Γ |- t := α --> β  ->  Γ |- u := α   (* ------------------------- *)
      -> Γ |- t @ u := β                      (*       Γ ⊢ t u : β         *)

  where "Γ |- t := α" := (Typing Γ t α).

Derive NoConfusion Signature for Typing.

Record term : Set := mkterm {
  env    : Env;
  tm     : preterm;
  ty     : type;
  typing : Typing env tm ty
}.

Lemma Type_unique : ∀ t E T1 T2
  (D1 : Typing E t T1) (D2 : Typing E t T2), T1 = T2.
Proof.
  intros.
  generalize dependent E.
  generalize dependent T1.
  generalize dependent T2.
  induction t; simpl; intros.
  - inversion_clear D1.
    inversion H; subst; clear H.
    inversion_clear D2.
    inversion H; subst; clear H.
    rewrite H1 in H2.
    now inversion_clear H2.
  - inversion_clear D1.
    inversion_clear D2.
    f_equal.
    now eapply IHt; eauto.
  - inversion_clear D1.
    inversion_clear D2.
    specialize (IHt1 _ _ _ H H1).
    specialize (IHt2 _ _ _ H0 H2).
    subst.
    now inversion_clear IHt1.
Qed.

Definition option_dec {A} (H : ∀ a b : A, {a = b} + {a <> b}) :
  ∀ a b : option A, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma typing_unique : ∀ E t T (D1 D2 : Typing E t T), D1 = D2.
Proof.
  intros.
  induction D1.
  - dependent elimination D2.
    f_equal.
    apply Eqdep_dec.UIP_dec; intros.
    apply option_dec; intros.
    apply option_dec; intros.
    now apply type_eq_dec.
  - dependent elimination D2.
    f_equal.
    now apply IHD1.
  - dependent elimination D2.
    pose proof (Type_unique _ _ _ _ D1_1 t3).
    pose proof (Type_unique _ _ _ _ D1_2 t4).
    subst.
    f_equal.
      now apply IHD1_1.
    now apply IHD1_2.
Qed.

Lemma term_eq : ∀ M N, env M = env N -> tm M = tm N -> M = N.
Proof.
  intros.
  destruct M, N; simpl in *; subst.
  pose proof (Type_unique _ _ _ _ typing0 typing1); subst.
  f_equal.
  now apply typing_unique.
Qed.

Theorem autoType E t :
  { N : term | env N = E & tm N = t } +
  { ~ exists N : term, env N = E /\ tm N = t }.
Proof.
  induction t.
  - destruct (nth_error E i) eqn:?.
      destruct o.
        left.
        unshelve eexists
          {| env    := E
           ; tm     := %i
           ; ty     := t
           ; typing := TVar _ _ _ _ |}; auto.
      right.
      intro.
      destruct H, H; subst.
      admit.
    admit.
  - destruct IHt.
      left.
      destruct s; subst.
      unshelve eexists
        {| env    := env x
         ; tm     := \d => tm x
         ; ty     := d --> ty x
         ; typing := TAbs _ _ _ (tm x) _ |}; eauto.
      admit.
    right.
    intro.
    apply n; clear n.
    destruct H, H; subst.
    unshelve eexists
      {| env    := env x
       ; tm     := t
       ; ty     := ty x
       ; typing := _ |}; eauto.
    admit.
  - destruct IHt1.
      destruct IHt2.
        left.
        destruct s, s0; subst.
        unshelve eexists
          {| env    := env x
           ; tm     := tm x @ tm x0
           ; ty     := _
           ; typing := _ |}; eauto.
      right.
Admitted.
(*
      destruct s; subst.
      intro.
      apply n; clear n.
      destruct H, H.
      now eexists
        {| env    := env x
         ; tm     := t2
         ; ty     := _
         ; typing := _ |}; eauto.
    destruct IHt2.
      right.
      destruct s; subst.
      intro.
      apply n; clear n.
      destruct H, H.
      now eexists
        {| env    := env x
         ; tm     := t1
         ; ty     := _
         ; typing := _ |}; eauto.
    right.
    intro.
    apply n; clear n.
    destruct H, H; subst.
    now eexists
      {| env    := env x
       ; tm     := t1
       ; ty     := _
       ; typing := _ |}; eauto.
}
*)

Fixpoint subst (z : nat) (u e : preterm) {struct e} : preterm :=
  match e with
    | Var i => Var i
    | Abs e1 => Abs (subst z u e1)
    | App e1 e2 => App (subst z u e1) (subst z u e2)
  end.

Program Definition identity (Γ : Env) (x : type) :
  Typing Γ (\x => %0) (x --> x) :=
  TAbs _ _ _ _ (TVar _ _ _ _).

Fixpoint lift (t : preterm) : preterm :=
  match t with
  | Var i        => Var (S i)
  | Abs d body   => Abs d (lift body)
  | App arg body => App (lift arg) (lift body)
  end.

Definition lifted (Γ : Env) (x α : type) (t : preterm) :
  Γ |- t := α -> Γ ∪ {x} |- t := α.
Proof.
  intros.
  induction t.
  - constructor.
    inversion H; subst.
    inversion H2; subst.
    unfold VarD.
Abort.

Definition composition (Γ : Env) (x y z : type) (f g : preterm)
           (Tf : Typing Γ f (y --> z))
           (Tg : Typing Γ g (x --> y)) :
  Typing Γ (\x => f @ (g @ %0)) (x --> z).
Proof.
  constructor.
  apply TApp with (α := y); auto.
    admit.
  apply TApp with (α := x); auto.
    admit.
  apply TVar.
  constructor.
Admitted.
*)

Program Definition Lambda : Category := {|
  obj     := type;
  hom     := fun x y => ∃ Γ (t : preterm), Typing Γ t (x --> y);
  homset  := fun x y => {| equiv := fun f g => _ |};
  id      := fun x => (_; (_; identity _ x));
  compose := fun x y z f g =>
    (_; (_; composition _ _ _ _ _ _ (`2`2 f) (`2`2 g)))
|}.
Admit Obligations.
