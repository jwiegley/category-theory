(*************************************************************************)
(*                                                                       *)
(* Lecture 3                                                             *)
(*                                                                       *)
(*************************************************************************)

Require Import Metalib.Metatheory.

(** Next, we import the definitions of the simply-typed lambda calculus. *)
Require Import Stlc.Definitions.

(** And some auxiliary lemmas about these definitions. *)
Require Import Stlc.Lemmas.

Import StlcNotations.

(* This file draws heavily on the generated lemmas in Stlc.Lemmas. *)

(*************************************************************)
(*   Connection to nominal representation of terms           *)
(*************************************************************)

(* A named representation of STLC terms.
   No debruijn indices, and binders include the names of free variables. *)

Inductive n_exp : Set :=
 | n_var (x:var)
 | n_abs (x:var) (e:n_exp)
 | n_app (e1:n_exp) (e2:n_exp).

Parameter X : var.
Parameter Y : var.
Parameter neqXY : X <> Y.

Definition example_X : n_exp := n_abs X (n_var X).
Definition example_Y : n_exp := n_abs Y (n_var Y).

Lemma names_matter : example_X <> example_Y.
Proof.
  unfold example_X, example_Y. intro H. inversion H. apply neqXY. auto.
Qed.

(* --- an environment-based interpreter for named terms ------- *)

(*
   The result of this interpreter is a "closure" --- a lambda expression
   paired with a substitution for all of the free variables in the term.
   We call such substitutions "environments".

*)


Inductive nom_env : Set :=
  | nom_nil  : nom_env
  | nom_cons : atom -> n_exp -> nom_env -> nom_env -> nom_env.

Inductive nom_val : Set :=
  | nom_closure : atom -> nom_env -> n_exp -> nom_val.


Fixpoint rho_lookup x rho : option (n_exp * nom_env) :=
  match rho with
  | nom_nil => None
  | nom_cons y e r rho' =>  if (x == y) then Some (e,r) else rho_lookup x rho'
  end.

Inductive res (a : Set) : Set :=
  | val     : a -> res a
  | timeout : res a
  | stuck   : res a.

Fixpoint nom_interp (n:nat) (e:n_exp) (rho: nom_env) : res nom_val :=
  match n with
  | 0 => timeout _
  | S m =>
    match e with
    | n_var x =>  match (rho_lookup x rho) with
                | Some (e',r') => nom_interp m e' r'
                | None   => stuck _
                end
    | n_app e1 e2 =>
      match nom_interp m e1 rho with
      | val _ (nom_closure x rho' e1') =>
              nom_interp m e1' (nom_cons x e2 rho rho')
      | r       => r
      end
    | n_abs x e   => val _ (nom_closure x rho e)
    end
  end.

(* --- translation from nominal terms and values to LN terms --- *)
(*
    Our goal is to prove the correctness of this interpreter. In otherwords,
    we want to show that if it produces a value, then we can translate to an
    evaluation of LN terms.

    The property that we ultimately want to prove looks something like this:

<<
   Lemma nom_soundness0 : forall n e v,
      val _ v = nom_interp n e nom_nil  ->
      bigstep (nom_to_exp e) (nom_val_to_exp v).
>>

    where we straightforwardly translate nominal terms to LN terms.
    (Note that we cannot write the function in the other direction --- there
    are many equally valid names that we can choose for the bound variable.)
*)

Fixpoint nom_to_exp (ne : n_exp) : exp :=
  match ne with
  | n_var x => var_f x
  | n_app e1 e2 => app (nom_to_exp e1) (nom_to_exp e2)
  | n_abs x e1 => abs (close_exp_wrt_exp x (nom_to_exp e1))
end.

(* The following function for environments substitutes all of the mappings in
   the environment in a LN expression, using the LN substitution function.
   This is good because we don't need to define capture-avoiding substitution for
   nominal terms.
 *)

Fixpoint nom_envsubst (ne:nom_env) : exp -> exp :=
  match ne with
  | nom_nil => fun e => e
  | nom_cons x e' r' rho =>
    fun e => nom_envsubst rho ([ x ~> nom_envsubst r' (nom_to_exp e')] e)
  end.


Fixpoint nom_val_to_exp (cv:nom_val) : exp :=
  match cv with
  | nom_closure x rho e =>
    nom_envsubst rho (nom_to_exp (n_abs x e))
  end.


(* ----------------- closed values, environments and terms ------------------- *)

(*
    To prove the soundness lemma, we will need to strengthen it so
    that it says something about non-empty environments.


<<
   Lemma nom_soundness1 : forall n rho e v,
      val _ v = nom_interp n e rho  ->
      .... ->
      bigstep (nom_envsubst rho (nom_to_exp e)) (nom_val_to_exp v).
>>

   However, this lemma will not be true for all environments and nominal terms,
   we need to make sure that
     (1) the domain of the environment includes definitions for all
         of the free variables in e, and
     (2) the range of the environment includes only *closed* nominal values.

*)

Fixpoint dom_rho (rho :nom_env) :=
  match rho with
  | nom_nil => {}
  | nom_cons x _ _ rho => {{x}} \u dom_rho rho
  end.

Inductive closed_env : nom_env -> Prop :=
     | closed_nil : closed_env nom_nil
     | closed_cons : forall x e r rho,
         closed_env r ->
         fv_exp (nom_to_exp e) [<=] dom_rho r ->
         closed_env rho -> closed_env (nom_cons x e r rho).

Inductive closed_val : nom_val -> Prop :=
  | closed_closure : forall x rho e,
      closed_env rho ->
      fv_exp (nom_to_exp e) [<=] add x (dom_rho rho) ->
      closed_val (nom_closure x rho e).
Hint Constructors closed_env closed_val.

(* Our definition of closed_env means that any value that we lookup
   from this environment will be closed. *)

Lemma rho_lookup_closed_val : forall x rho e r,
    closed_env rho ->
    Some (e,r) = rho_lookup x rho ->
    fv_exp (nom_to_exp e) [<=] dom_rho r.
Proof.
  induction rho; intros; simpl in *.
  - inversion H0.
  - inversion H. subst.
    destruct (x == a).
    inversion H0. eauto.
    eapply IHrho2; eauto.
Qed.

(* Furthermore, we can also prove that closed values have no
   free variables after translation.

   This proof is done by mutual induction on the closed_val/closed_env
   derivation. So before we can do that, we need to ask Coq to
   derive the appropriate induction scheme.
*)

Lemma fv_closed_env :
  (forall rho, closed_env rho -> forall e, fv_exp e [<=] dom_rho rho ->
                                fv_exp (nom_envsubst rho e) [=] {}).
Proof.
  induction rho; intros; simpl in *.
  + fsetdec.
  + inversion H.
    eapply IHrho2; auto.
    rewrite fv_exp_subst_exp_upper.
    rewrite IHrho1; auto.
    fsetdec.
Qed.

(* ----------------- nom_envsubst reductions ------------------- *)

(* We can think of a an environment as a multi-substitution for locally
   nameless terms.

   Therefore, the nom_envsubst function inherits many of the properties of the
   subst_exp function.

 *)

Lemma nom_envsubst_open : forall rho e e',
 (forall v, lc_exp (nom_val_to_exp v)) ->
 (nom_envsubst rho (open e e')) = (open (nom_envsubst rho e) (nom_envsubst rho e')).
Proof.
  induction rho; intros; default_simp.
  rewrite subst_exp_open_exp_wrt_exp; eauto.
  admit. (* lc *)
Admitted.


Lemma nom_envsubst_fresh_eq : forall rho e,
    closed_env rho ->
    fv_exp e [=] {} ->
    nom_envsubst rho e = e.
Proof.
  induction rho. simpl. auto.
  intros. simpl.
  inversion H.
  rewrite subst_exp_fresh_eq; auto.
  rewrite H0. auto.
Qed.


Lemma nom_envsubst_var : forall x rho e rho',
    closed_env rho ->
    Some (e,rho') = rho_lookup x rho ->
    nom_envsubst rho (var_f x) = nom_envsubst rho' (nom_to_exp e).
Proof.
  induction rho.
  - intros. simpl in *. inversion H0.
  - intros. simpl in *.
     inversion H. subst.
     destruct (x == a).
     + inversion H0. subst. clear H0.
    simpl.
    rewrite (nom_envsubst_fresh_eq rho2); auto.
    apply fv_closed_env; auto.
  + eapply IHrho2; auto.
Qed.

Lemma nom_envsubst_abs : forall rho e,
 nom_envsubst rho (abs e) = abs (nom_envsubst rho e).
Proof.
  induction rho; simpl; eauto.
Qed.

Lemma nom_envsubst_app : forall rho e1 e2,
 nom_envsubst rho (app e1 e2) = app (nom_envsubst rho e1) (nom_envsubst rho e2).
Proof.
  induction rho; simpl; eauto.
Qed.

(* ----------------------------------------- *)

(*
Lemma fv_closed :
  (forall v, closed_val v -> fv_exp (nom_val_to_exp v) [=] {}).
Proof.
  intros v CV. inversion CV.
  simpl.
  rewrite envsubst_abs.
  rewrite H0.



Scheme closed_val_ind' := Induction for closed_val Sort Prop
 with  closed_env_ind' := Induction for closed_env Sort Prop.
Combined Scheme closed_nom from closed_val_ind', closed_env_ind'.


Lemma fv_closed_mutual :
  (forall v, closed_val v -> fv_exp (nom_val_to_exp v) [=] {}) /\
  (forall rho, closed_env rho -> forall e, fv_exp e [<=] dom_rho rho ->
                                fv_exp (nom_envsubst rho e) [=] {}).
Proof.
  eapply closed_nom; intros.
  + simpl. rewrite H. fsetdec.
    simpl.
    rewrite fv_exp_close_exp_wrt_exp.
    fsetdec.
  + simpl in *. fsetdec.
  + simpl in *.
    rewrite H0. fsetdec.
    rewrite fv_exp_subst_exp_upper.
    rewrite H.
    fsetdec.
Qed.

Lemma fv_closed :
  (forall v, closed_val v -> fv_exp (nom_val_to_exp v) [=] {}).
Proof.
  eapply fv_closed_mutual.
Qed.

Lemma fv_closed_env :
  (forall rho, closed_env rho -> forall e, fv_exp e [<=] dom_rho rho ->
                                fv_exp (nom_envsubst rho e) [=] {}).
Proof.
  eapply fv_closed_mutual.
Qed.
*)

(* Now we can use these results to show that the interpreter
   produces closed values from appropriate environments and terms. *)

Lemma nom_interp_closed : forall n rho e v,
    val _ v = nom_interp n e rho ->
    closed_env rho ->
    fv_exp (nom_to_exp e) [<=] dom_rho rho ->
    closed_val v.
Proof.
  induction n.
  intros; simpl in *. inversion H.
  intros.  destruct e; simpl in *.
  - Case "var".
    destruct (rho_lookup x rho) eqn:?;
    inversion H;  auto.
    destruct p.
    admit. (* eapply rho_lookup_closed_val with (x:=x); eauto. *)
  - Case "abs".
    inversion H.  subst.
    econstructor; eauto.
    rewrite fv_exp_close_exp_wrt_exp in H1.
    rewrite <- H1.
    fsetdec.

  - Case "app".
    destruct (nom_interp n e1 rho) eqn:?; try solve [inversion H].
    assert (C1: closed_val n0). eapply IHn; eauto. fsetdec.
    destruct n0 as [x rho' e1'].
    inversion C1.
    destruct  (nom_interp n e2 rho) eqn:?; try solve [inversion H].
    assert (C2: closed_val n0). eapply IHn; eauto. fsetdec.
    eapply IHn; eauto.
    admit.
Admitted.



(* ----------------- interpreter soundness for values ------------------- *)

(* The next step is to show that nominal values bigstep to themselves.
   In otherwords, we want to show that:

<<
   Lemma nom_soundness_val : forall v,
       bigstep (nom_val_to_exp v) (nom_val_to_exp v).
>>

  To prove this lemma, we need to show that these nominal values translate
  LN values, and that these values are locally closed.

*)

Lemma nom_val_to_exp_is_value : forall v, is_value (nom_val_to_exp v).
Proof.
  destruct v. simpl. rewrite nom_envsubst_abs.
  simpl. auto.
Qed.

Hint Resolve nom_val_to_exp_is_value.

Lemma nom_to_exp_lc : forall ne, lc_exp (nom_to_exp ne).
Proof.
  induction ne; simpl; auto.
  eapply lc_abs_exists with (x1 := x).
  rewrite open_exp_wrt_exp_close_exp_wrt_exp.
  auto.
Qed.


(* Need the mutual induction scheme for the next lemma! *)
Scheme nom_val_ind' := Induction for nom_val Sort Prop
 with  nom_env_ind' := Induction for nom_env Sort Prop.
Combined Scheme nom_mutual from nom_val_ind', nom_env_ind'.


Lemma nom_val_to_exp_lc_mutual :
  (forall v, lc_exp (nom_val_to_exp v)) /\
  (forall rho, forall e, lc_exp e -> lc_exp (nom_envsubst rho e)).
Proof.
  eapply nom_mutual.
  - intros. simpl.
    eapply H.
    eapply lc_abs_exists with (x1:=a).
    rewrite open_exp_wrt_exp_close_exp_wrt_exp.
    eapply nom_to_exp_lc.
  - intros. simpl. auto.
  - intros; simpl in *.
    eapply H0; eauto.
    eapply subst_exp_lc_exp; eauto.
Qed.

Lemma nom_val_to_exp_lc : forall v,
    lc_exp (nom_val_to_exp v).
Proof.
  eapply nom_val_to_exp_lc_mutual.
Qed.
Lemma nom_envsubst_lc : (forall rho, forall e, lc_exp e -> lc_exp (nom_envsubst rho e)).
  eapply nom_val_to_exp_lc_mutual.
Qed.

Hint Resolve nom_to_exp_lc nom_val_to_exp_lc nom_envsubst_lc.

Lemma nom_soundness_val : forall v,
       bigstep (nom_val_to_exp v) (nom_val_to_exp v).
Proof.
  eauto.
Qed.

(* ----------------- interpreter soundness ------------------- *)

(* Finally, we get to the actual soundness function for the interpreter. *)


Lemma nom_soundness : forall n rho e v,
    val _ v = nom_interp n e rho  ->
    closed_env rho ->
    fv_exp (nom_to_exp e) [<=] dom_rho rho ->
    bigstep (nom_envsubst rho (nom_to_exp e)) (nom_val_to_exp v).
Proof.
  induction n.
  intros; simpl in *. inversion H.
  intros.  destruct e; simpl in *.
  - Case "var".
    remember (rho_lookup x rho) as l.
    destruct l; inversion H.
    erewrite nom_envsubst_var; eauto.
  - Case "abs".
    inversion H.
    replace (nom_envsubst rho (abs (close_exp_wrt_exp x (nom_to_exp e)))) with
            (nom_val_to_exp (nom_closure x rho e)); auto.
  - Case "app".
    remember (nom_interp n e1 rho) as r1.
    remember (nom_interp n e2 rho) as r2.
    destruct r1; try solve [inversion H].
    destruct (nom_interp_closed _ _ _ _ Heqr1); eauto; try fsetdec.
    apply IHn in Heqr1; auto; try fsetdec.

    destruct r2; try solve [inversion H].
    destruct (nom_interp_closed _ _ _ _ Heqr2); eauto; try fsetdec.
    apply IHn in Heqr2; auto; try fsetdec.

    simpl in Heqr1.
    rewrite nom_envsubst_abs in Heqr1.

    apply IHn in H; eauto; simpl; try fsetdec.
    simpl in H.

    rewrite subst_exp_spec in H.
    rewrite nom_envsubst_open in H; eauto.

    replace (nom_envsubst rho1 (abs (close_exp_wrt_exp x0 (nom_to_exp e0)))) with
            (nom_val_to_exp (nom_closure x0 rho1 e0)) in H; auto.

    rewrite nom_envsubst_fresh_eq in H; eauto.

    rewrite nom_envsubst_app.
    eauto.
Qed.

Lemma completeness : forall e v rho,
    bigstep (nom_envsubst rho (nom_to_exp e)) (nom_val_to_exp v) ->
    exists n, nom_interp n e rho = val _ v.
Proof.
Admitted.
