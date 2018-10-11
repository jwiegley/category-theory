Require Import Metalib.Metatheory.
(** syntax *)
Definition index := nat.

Inductive typ : Set :=  (*r types *)
 | typ_base : typ (*r base type *)
 | typ_arrow (T1:typ) (T2:typ) (*r function types *).

Inductive exp : Set :=  (*r expressions *)
 | var_b (_:nat) (*r variables *)
 | var_f (x:var) (*r variables *)
 | abs (e:exp) (*r abstractions *)
 | app (e1:exp) (e2:exp) (*r applications *).

Definition ctx : Set := list ( atom * typ ).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => var_b nat
        | inleft (right _) => e_5
        | inright _ => var_b (nat - 1)
      end
  | (var_f x) => var_f x
  | (abs e) => abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (app e1 e2) => app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_var_f : forall (x:var),
     (lc_exp (var_f x))
 | lc_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (var_f x) )  )  ->
     (lc_exp (abs e))
 | lc_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (app e1 e2)).
(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (var_b nat) => {}
  | (var_f x) => {{x}}
  | (abs e) => (fv_exp e)
  | (app e1 e2) => (fv_exp e1) \u (fv_exp e2)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (var_b nat) => var_b nat
  | (var_f x) => (if eq_var x x5 then e_5 else (var_f x))
  | (abs e) => abs (subst_exp e_5 x5 e)
  | (app e1 e2) => app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
end.


Definition is_value (e : exp) : Prop :=
  match e with
  | abs _   => True
  | _       => False
  end.

Module StlcNotations.
Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation open e1 e2     := (open_exp_wrt_exp e1 e2).
End StlcNotations.


(** definitions *)

(* defns JTyping *)
Inductive typing : ctx -> exp -> typ -> Prop :=    (* defn typing *)
 | typing_var : forall (G:ctx) (x:var) (T:typ),
      uniq  G  ->
      binds  x T G  ->
     typing G (var_f x) T
 | typing_abs : forall (L:vars) (G:ctx) (e:exp) (T1 T2:typ),
      ( forall x , x \notin  L  -> typing  (( x ~ T1 )++ G )   ( open_exp_wrt_exp e (var_f x) )  T2 )  ->
     typing G (abs e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2.

(* defns JEval *)
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_beta : forall (e1 e2:exp),
     lc_exp (abs e1) ->
     lc_exp e2 ->
     step (app  ( (abs e1) )  e2)  (open_exp_wrt_exp  e1 e2 )
 | step_app : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (app e1 e2) (app e1' e2).


(** infrastructure *)
Hint Constructors typing step lc_exp.
