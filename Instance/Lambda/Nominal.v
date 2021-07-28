(** A nominal representation of STLC terms.

    This version looks a lot like we expect a representation of
    the lambda calculus to look like. Unlike the LN version,
    the syntax does not distinguish between bound and free
    variables and abstractions include the name of binding
    variables.  *)

(*************************************************************)
(** * Imports                                                *)
(*************************************************************)

(** Some of our proofs are by induction on the *size* of
    terms. We'll use Coq's [omega] tactic to easily dispatch
    reasoning about natural numbers. *)
Require Export Omega.

(** We will use the [atom] type from the metatheory library to
    represent variable names. *)
Require Export Metalib.Metatheory.

(** Although we are not using LNgen, some of the tactics from
    its library are useful for automating reasoning about
    names.  *)
Require Export Metalib.LibLNgen.


(** Some fresh variables *)
Notation X := (fresh nil).
Notation Y := (fresh (X :: nil)).
Notation Z := (fresh (X :: Y :: nil)).

(*************************************************************)
(** * A nominal representation of terms                      *)
(*************************************************************)

Inductive n_exp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_exp)
 | n_app (t1:n_exp) (t2:n_exp).

(** For example, we can encode the expression [(\X.Y X)] as below.  *)

Definition demo_rep1 := n_abs X (n_app (n_var Y) (n_var X)).

(** For example, we can encode the expression [(\Z.Y Z)] as below.  *)

Definition demo_rep2 := n_abs Z (n_app (n_var Y) (n_var Z)).


(** As usual, the free variable function needs to remove the
    bound variable in the [n_abs] case. *)
Fixpoint fv_nom (n : n_exp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => remove x (fv_nom n)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  end.

(** The tactics for reasoning about lists and sets of atoms are useful here
    too. *)

Example fv_nom_rep1 : fv_nom demo_rep1 [=] {{ Y }}.
Proof.
  simpl.
  assert (~ In Y (X :: nil)).     (* assert that Y is not the same variable as X *)
  apply Atom.fresh_not_in.
  apply elim_not_In_cons in H.
  fsetdec.
Qed.

(** What makes this a *nominal* representation is that our
    operations are based on the following swapping function for
    names.  Note that this operation is symmetric: [x] becomes
    [y] and [y] becomes [x]. *)

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

(** The main insight of nominal representations is that we can
    rename variables, without capture, using a simple
    structural induction. Note how in the [n_abs] case we swap
    all variables, both bound and free.

    For example:

      (swap x y) (\z. (x y)) = \z. (y x))

      (swap x y) (\x. x) = \y.y

      (swap x y) (\y. x) = \x.y

*)
Fixpoint swap (x:atom) (y:atom) (t:n_exp) : n_exp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  end.


(** Because swapping is a simple, structurally recursive
    function, it is highly automatable using the [default_simp]
    tactic from LNgen library.

    This tactic "simplifies" goals using a combination of
    common proof steps, including case analysis of all disjoint
    sums in the goal. Because atom equality returns a sumbool,
    this makes this tactic useful for reasoning by cases about
    atoms.

    For more information about the [default_simp] tactic, see
    [metalib/LibDefaultSimp.v].

    WARNING: this tactic is not always safe. It's a power tool
    and can put your proof in an irrecoverable state. *)

Example swap1 : forall x y z, x <> z -> y <> z ->
    swap x y (n_abs z (n_app (n_var x)(n_var y))) = n_abs z (n_app (n_var y) (n_var x)).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.

Example swap2 : forall x y, x <> y ->
    swap x y (n_abs x (n_var x)) = n_abs y (n_var y).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.

Example swap3 : forall x y, x <> y ->
     swap x y (n_abs y (n_var x)) = n_abs x (n_var y).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.


(** We define the "alpha-equivalence" relation that declares
    when two nominal terms are equivalent (up to renaming of
    bound variables).

    Note the two different rules for [n_abs]: either the
    binders are the same and we can directly compare the
    bodies, or the binders differ, but we can swap one side to
    make it look like the other.  *)

Inductive aeq : n_exp -> n_exp -> Prop :=
 | aeq_var : forall x,
     aeq (n_var x) (n_var x)
 | aeq_abs_same : forall x t1 t2,
     aeq t1 t2 -> aeq (n_abs x t1) (n_abs x t2)
 | aeq_abs_diff : forall x y t1 t2,
     x <> y ->
     x `notin` fv_nom t2 ->
     aeq t1 (swap y x t2) ->
     aeq (n_abs x t1) (n_abs y t2)
 | aeq_app : forall t1 t2 t1' t2',
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_app t1 t2) (n_app t1' t2').

Hint Constructors aeq.


Example aeq1 : forall x y, x <> y -> aeq (n_abs x (n_var x)) (n_abs y (n_var y)).
Proof.
  intros.
  eapply aeq_abs_diff; auto.
  simpl; unfold swap_var; default_simp.
Qed.

(*************************************************************)
(** ** Properties about swapping                             *)
(*************************************************************)


(** Now let's look at some simple properties of swapping. *)

Lemma swap_id : forall n x,
    swap x x n = n.
Proof.
  induction n; simpl; unfold swap_var;  default_simp.
Qed.

(** Demo: We will need the next two properties later in the tutorial,
    so we show that even though there are many cases to consider,
    [default_simp] can find these proofs. *)

Lemma fv_nom_swap : forall z y n,
  z `notin` fv_nom n ->
  y `notin` fv_nom (swap y z n).
Proof.
  (* WORKINCLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. (* /WORKINCLASS *)

Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  (* WORKINCLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. (* /WORKINCLASS *)

(*************************************************************)
(** ** Exercises                                             *)
(*************************************************************)


(** *** Recommended Exercise: [swap] properties

    Prove the following properties about swapping, either
    explicitly (by destructing [x == y]) or automatically
    (using [default_simp]).  *)

Lemma swap_symmetric : forall t x y,
    swap x y t = swap y x t.
Proof.
  (* ADMITTED *)
  induction t;  simpl; unfold swap_var; default_simp.
Qed.   (* /ADMITTED *)

Lemma swap_involutive : forall t x y,
    swap x y (swap x y t) = t.
Proof.
  (* ADMITTED *)
  induction t;  simpl; unfold swap_var; default_simp.
Qed.   (* /ADMITTED *)

(** *** Challenge exercise: equivariance

    Equivariance is the property that all functions and
    relations are preserved under swapping. (Hint:
    [default_simp] will be slow on some of these properties, and
    sometimes won't be able to do them automatically.)  *)
Lemma swap_var_equivariance : forall v x y z w,
    swap_var x y (swap_var z w v) =
    swap_var (swap_var x y z) (swap_var x y w) (swap_var x y v).
Proof.
  (* ADMITTED *)
  unfold swap_var; default_simp.
Qed.   (* /ADMITTED *)

Lemma swap_equivariance : forall t x y z w,
    swap x y (swap z w t) = swap (swap_var x y z) (swap_var x y w) (swap x y t).
Proof.
  (* ADMITTED *)
  induction t; intros; simpl.
  - rewrite swap_var_equivariance. auto.
  - rewrite swap_var_equivariance. rewrite IHt. auto.
  - rewrite IHt1. rewrite IHt2. auto.
Qed. (* /ADMITTED *)

Lemma notin_fv_nom_equivariance : forall x0 x y t ,
  x0 `notin` fv_nom t ->
  swap_var x y x0  `notin` fv_nom (swap x y t).
Proof.
  (* ADMITTED *)
  induction t; intros; simpl in *.
  - unfold swap_var; default_simp.
  - unfold swap_var in *. default_simp.
  - destruct_notin. eauto.
Qed. (* /ADMITTED *)

(* HINT: For a helpful fact about sets of atoms, check AtomSetImpl.union_1 *)

Lemma in_fv_nom_equivariance : forall x y x0 t,
  x0 `in` fv_nom t ->
  swap_var x y x0 `in` fv_nom (swap x y t).
Proof.
  (* ADMITTED *)
  induction t; intros; simpl in *.
  - unfold swap_var; default_simp; fsetdec.
  - unfold swap_var in *. default_simp; fsetdec.
  - destruct (AtomSetImpl.union_1 H); fsetdec.
Qed. (* ADMITTED *)


Lemma aeq_equivariance : forall x y t1 t2,
    aeq t1 t2 ->
    aeq (swap x y t1) (swap x y t2).
Proof.
  (* ADMITTED *)
  induction 1; intros; simpl in *; auto.
  destruct (swap_var x y x0 == swap_var x y y0).
  - rewrite e. eapply aeq_abs_same.
    rewrite swap_equivariance in IHaeq.
    rewrite e in IHaeq.
    rewrite swap_id in IHaeq.
    auto.
  - rewrite swap_equivariance in IHaeq.
    eapply aeq_abs_diff; auto.
    eapply notin_fv_nom_equivariance; auto.
Qed. (* /ADMITTED *)



(*************************************************************)
(** * An abstract machine for cbn evaluation                 *)
(*************************************************************)

(** The advantage of named terms is an efficient operational
    semantics! Compared to LN or de Bruijn representation, we
    don't need always need to modify terms (such as via open or
    shifting) as we traverse binders. Instead, as long as the
    binder is "sufficiently fresh" we can use the name as is,
    and only rename (via swapping) when absolutely
    necessary. *)

(** Below, we define an operational semantics based on an
    abstract machine. As before, it will model execution as a
    sequence of small-step transitions. However, transition
    will be between _machine configurations_, not just
    expressions.

    Our abstract machine configurations have three components:

    - the current expression being evaluated the heap (aka
    - environment): a mapping between variables and expressions
    - the stack: the evaluation context of the current
    - expression

    Because we have a heap, we don't need to use substitution
    to define our semantics! To implement [x ~> e] we add a
    definition that [x] maps to [e] in the heap and then look
    up the definition when we get to [x] during evaluation.  *)


Definition heap := list (atom * n_exp).

Inductive frame : Set := | n_app2 : n_exp -> frame.
Notation  stack := (list frame).

Definition configuration := (heap * n_exp * stack)%type.

(** The (small-step) semantics is a _function_ from
    configurations to configurations, until completion or
    error. *)

Inductive Step a := Error    : Step a
                  | Done     : Step a
                  | TakeStep : a -> Step a.

Definition isVal (t : n_exp) :=
  match t with
  | n_abs _ _ => true
  | _         => false
  end.

Definition machine_step (avoid : atoms) (c : configuration) : Step configuration :=
  match c with
    (h, t, s) =>
    if isVal t then
      match s with
      | nil => Done _
      | n_app2 t2 :: s' =>
        match t with
        | n_abs x t1 =>
          (* if the bound name [x] is not fresh, we need to rename it *)
          if AtomSetProperties.In_dec x (dom h `union` avoid)  then
            let (y,_) := atom_fresh (dom h `union` avoid) in
             TakeStep _ ((y,t2)::h, swap x y t1, s')
          else
            TakeStep _ ((x,t2)::h, t1, s')
        | _ => Error _ (* non-function applied to argument *)
        end
      end
    else match t with
         | n_var x => match get x h with
                     | Some t1  => TakeStep _ (h, t1, s)
                     | None    => Error _ (* Unbound variable *)
                     end
         | n_app t1 t2 => TakeStep _ (h, t1, n_app2 t2 :: s)
         | _ => Error _ (* unreachable (value in nonValueStep) *)
         end
  end.

Definition initconf (t : n_exp) : configuration := (nil,t,nil).


(** Example: evaluation of  "(\y. (\x. x) y) Z"

<<
     machine                                       corresponding term

      {}, (\y. (\x. x) y) Z , nil                  (\y. (\x. x) y) Z
  ==> {}, (\y. (\x. x) y), n_app2 Z :: nil         (\y. (\x. x) y) Z
  ==> {y -> Z}, (\x.x) y, nil                      (\x. x) Z
  ==> {y -> Z}, (\x.x), n_app2 y :: nil            (\x. x) Z
  ==> {x -> y, y -> Z}, x, nil                     Z
  ==> {x -> y, y -> Z}, y, nil                     Z
  ==> {x -> y, y -> Z}, Z, nil                     Z
  ==> Done
>>

(Note that the machine takes extra steps compared to the
substitution semantics.)

We will prove that this machine implements the substitution
semantics in the next section.

*)

(** ** Recommended Exercise [values_are_done]

    Show that values don't step using this abstract machine.
    (This is a simple proof.)
*)

Lemma values_are_done : forall D t,
    isVal t = true -> machine_step D (initconf t) = Done _.
Proof.
(* ADMITTED *)
  intros D t VV.
  destruct t; simpl in *; try discriminate.
  auto.
Qed. (* /ADMITTED *)


(*************************************************************)
(** * Size based reasoning                                   *)
(*************************************************************)


(** Some properties about nominal terms require calling the
    induction hypothesis not on a direct subterm, but on one
    that has first had a swapping applied to it.

    However, swapping names does not change the size of terms,
    so that means we can prove such properties by induction on
    that size.  *)

Fixpoint size (t : n_exp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  end.

Lemma swap_size_eq : forall x y t,
    size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

Hint Rewrite swap_size_eq.

(* HIDE *)
(** ** Nominal induction *)

Lemma nominal_induction_size :
     forall n, forall t, size t <= n ->
     forall P : n_exp -> Type,
    (forall x, P (n_var x)) ->
    (forall x t, (forall y, P (swap x y t)) -> P (n_abs x t)) ->
    (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
    P t.
Proof.
  induction n.
  intros t SZ; destruct t; intros; simpl in SZ; omega.
  intros t SZ P VAR ABS APP; destruct t; simpl in *.
  - auto.
  - apply ABS.
    intros y.
    apply IHn; eauto; rewrite swap_size_eq; try omega.
  - apply APP.
    apply IHn; eauto; omega.
    apply IHn; eauto; omega.
Defined.

Definition nominal_induction
  : forall (P : n_exp -> Type),
    (forall x : atom, P (n_var x)) ->
    (forall (x : atom) (t : n_exp),
        (forall y : atom, P (swap x y t)) -> P (n_abs x t)) ->
    (forall t1 t2 : n_exp, P t1 -> P t2 -> P (n_app t1 t2)) ->
    forall t : n_exp, P t :=
  fun P VAR APP ABS t =>
  nominal_induction_size (size t) t ltac:(auto) P VAR APP ABS.
(* /HIDE *)

(** ** Capture-avoiding substitution *)

(** We need to use size to define capture avoiding
    substitution. Because we sometimes swap the name of the
    bound variable, this function is _not_ structurally
    recursive. So, we add an extra argument to the function
    that decreases with each recursive call. *)

Fixpoint subst_rec (n:nat) (t:n_exp) (u :n_exp) (x:atom)  : n_exp :=
  match n with
  | 0 => t
  | S m => match t with
          | n_var y => if (x == y) then u else t
          | n_abs y t1 => if (x == y) then t
                        else let (z,_) := atom_fresh (fv_nom u \u fv_nom t) in
                             n_abs z (subst_rec m (swap y z t1) u x)
          | n_app t1 t2 => n_app (subst_rec m t1 u x) (subst_rec m t2 u x)
          end
  end.

(** Our real substitution function uses the size of the size of the term
    as that extra argument. *)
Definition subst (u : n_exp) (x:atom) (t:n_exp) :=
  subst_rec (size t) t u x.

(** This next lemma uses course of values induction [lt_wf_ind] to prove that
    the size of the term [t] is enough "fuel" to completely calculate a
    substitution. Providing larger numbers produces the same result. *)
Lemma subst_size : forall n (u : n_exp) (x:atom) (t:n_exp),
    size t <= n -> subst_rec n t u x = subst_rec (size t) t u x.
Proof.
  intro n. eapply (lt_wf_ind n). clear n.
  intros n IH u x t SZ.
  destruct t; simpl in *; destruct n; try omega.
  - default_simp.
  - default_simp.
    rewrite <- (swap_size_eq x0 x1).
    rewrite <- (swap_size_eq x0 x1) in SZ.
    apply IH. omega. omega.
  - simpl.
    rewrite (IH n); try omega.
    rewrite (IH n); try omega.
    rewrite (IH (size t1 + size t2)); try omega.
    rewrite (IH (size t1 + size t2)); try omega.
    auto.
Qed.

(** ** Challenge Exercise [subst]

    Use the definitions above to prove the following results about the
    nominal substitution function.  *)

Lemma subst_eq_var : forall u x,
    subst u x (n_var x) = u.
Proof.
  (* ADMITTED *)
  intros. unfold subst. default_simp.
Qed. (* /ADMITTED *)

Lemma subst_neq_var : forall u x y,
    x <> y ->
    subst u x (n_var y) = n_var y.
Proof.
  (* ADMITTED *)
  intros. unfold subst. default_simp.
Qed. (* /ADMITTED *)

Lemma subst_app : forall u x t1 t2,
    subst u x (n_app t1 t2) = n_app (subst u x t1) (subst u x t2).
Proof. (* ADMITTED *)
  intros. unfold subst.
  simpl.
  rewrite (subst_size (size t1 + size t2)).
  rewrite (subst_size (size t1 + size t2)).
  auto.
  omega.
  omega.
Qed. (* /ADMITTED *)

Lemma subst_abs : forall u x y t1,
    subst u x (n_abs y t1) =
       if (x == y) then (n_abs y t1)
       else let (z,_) := atom_fresh (fv_nom u \u fv_nom (n_abs y t1)) in
       n_abs z (subst u x (swap y z t1)).
Proof. (* ADMITTED *)
  intros. unfold subst. default_simp.
  rewrite swap_size_eq. auto.
Qed. (* /ADMITTED *)

(* HIDE *)


Fixpoint aeq_f  (n: nat) (L : atoms) (t1 : n_exp) (t2 : n_exp) : bool :=
  match n with
  | 0 => false
  | S m =>
    match t1 , t2 with
    | n_var x , n_var y => if (x == y) then true else false
    | n_abs x1 t1, n_abs x2 t2 =>
      if (x1 == x2) then aeq_f m L t1 t2
      else let (y,_) := atom_fresh L in
           aeq_f m ({{y}} \u L) (swap y x1 t1) (swap y x2 t2)
  | n_app t1 t2 , n_app t1' t2' =>
    if aeq_f m L t1 t1' then aeq_f m L t2 t2' else false
  | _ , _ => false
    end
end.

Definition is_aeq t1 t2 := aeq_f (size t1) (fv_nom t1 \u fv_nom t2).

(************)

Lemma aeq_refl : forall n, aeq n n.
Proof.
  induction n; auto.
Qed.

Lemma subst_equivariance : forall u x y z t,
    swap x y (subst u z t) = subst (swap x y u) (swap_var x y z) (swap x y t).
Proof.
  intros.
  eapply nominal_induction with (t := t).

  Focus 2.
  intros.
  rewrite subst_abs. default_simp.
  rewrite subst_abs. default_simp.
  rewrite subst_abs. default_simp.
  rewrite <- e.
Admitted.

Lemma subst_same : forall t y, aeq (subst (n_var y) y t)  t.
Proof.
  intros t y. eapply nominal_induction with (t := t).
  - intros. destruct (x == y). subst. rewrite subst_eq_var. auto.
  rewrite subst_neq_var. auto. auto.
  - intros.
    rewrite subst_abs. destruct (y == x).
    eapply aeq_abs_same. eapply aeq_refl.
    destruct atom_fresh.
    simpl in n0.
    destruct (x0 == x). subst. rewrite swap_id.
    eapply aeq_abs_same.
Admitted.
(*
Definition impossible {A:Type} (t:n_exp)(pf: size t <= 0) : A.
destruct t; simpl in pf; omega.
Defined.

Fixpoint nominal_recursion_size {A : Type} L
  (n : nat) (t : n_exp) (pf : size t <= n)
          (VAR : atom -> A)
          (ABS : forall x, x `notin` L -> A -> A)
          (APP : A -> A -> A)
           : A :=
  match n with
  | 0 => impossible t _
  | S m => match t with
          | n_var x => VAR x
          | n_abs y t0 =>
            let (z,Pf) := atom_fresh L in
            let ABS'   := fun x Fr => ABS x _ in
            ABS z Pf (nominal_recursion_size
                        (add z L) m (swap z y t0) _ VAR ABS' APP)
          | n_app t0 t1 =>
            APP (nominal_recursion_size L m t0 _ VAR ABS APP)
                (nominal_recursion_size L m t1 _ VAR ABS APP)
          end
  end.
*)


(*
Inductive typ := typ_base | typ_arrow : typ -> typ -> typ.

Definition ctx := list (atom * typ).

Inductive typing : ctx -> n_exp -> typ -> Prop :=
 | typing_var : forall (G:ctx) (x:var) (T:typ),
     uniq G ->
     binds x T G  ->
     typing G (n_var x) T
 | typing_abs : forall (G:ctx) x (T1:typ) (e:n_exp) (T2:typ),
     typing ([(x, T1)] ++ G) e T2  ->
     typing G (n_abs x e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:n_exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (n_app e1 e2) T2 .

Inductive typing_stack (G : ctx) : stack -> typ -> typ -> Prop :=
| typing_stack_nil : forall T, typing_stack G nil T T
| typing_stack_app2 : forall s e T T1 T2,
    typing G e T1 ->
    typing_stack G s T T2 ->
    typing_stack G ((n_app2 e)::s) T (typ_arrow T1 T2).

Inductive typing_heap : ctx -> heap -> Prop :=
 | typing_heap_nil : typing_heap nil nil
 | typing_heap_cons : forall G h x e T,
     typing G e T ->
     typing_heap G h ->
     typing_heap ((x, T)::G) ((x,e)::h).

Inductive typing_conf : conf -> typ -> Prop :=
 | typing_conf_witness:
     forall h e s G T1 T2,
       typing_heap G h ->
       typing_stack G s T1 T2 ->
       typing G e T1 ->
       typing_conf (h,e,s) T2.

Lemma preservation : forall T h e s conf',
    machine_step (dom h) (h,e,s) = TakeStep _ conf' ->
    typing_conf (h,e,s)  T ->
    typing_conf conf' T.
Proof.
  intros.
  destruct conf' as [[h' e'] s']. inversion H0. subst.
  simpl in *.
  destruct (isVal e) eqn:?.
  - destruct s eqn:?. inversion H.
    destruct f.
    destruct e eqn:?. inversion H.
    destruct AtomSetProperties.In_dec.
    + destruct atom_fresh.
      inversion H. subst. clear H.
      simpl in *.
      inversion H7. subst. clear H7.
      inversion H6. subst. clear H6.
      econstructor; eauto.
      instantiate (1 :=  [(x0,T3)] ++ G).
      eapply typing_heap_cons; eauto.
*)



Lemma aeq_fv_nom : forall t1 t2,
    aeq t1 t2 ->
    fv_nom t1 [=] fv_nom t2.
Proof.
  induction 1; simpl in *; try fsetdec.
  unfold AtomSetImpl.Equal.
  intro a.
  rewrite remove_iff.
  rewrite remove_iff.
  rewrite IHaeq.
  clear IHaeq H1.
  split.
  + intros [K1 K2].
    apply (in_fv_nom_equivariance y x) in K1.
    rewrite swap_involutive in K1.
    unfold swap_var in K1.
    destruct (a == y); subst. contradiction.
    destruct (a == x); subst. contradiction.
    split. auto. auto.
  + intros [K1 K2].
    apply (in_fv_nom_equivariance y x) in K1.
    pose (J := notin_fv_nom_equivariance x y x t2 H0). clearbody J.
    unfold swap_var in *.
    default_simp.
Qed.

Lemma aeq_sym : forall t1 t2,
    aeq t1 t2 -> aeq t2 t1.
Proof.
  induction 1; auto.
  - eapply aeq_abs_diff; auto.
    rewrite aeq_fv_nom; eauto.
    pose (J := notin_fv_nom_equivariance x y x t2 H0). clearbody J.
    unfold swap_var in J. default_simp.
    eapply aeq_equivariance in IHaeq.
    rewrite swap_involutive in IHaeq.
    rewrite swap_symmetric.
    auto.
Qed.

Lemma swap_fresh : forall t x0 y0 z,
  z `notin` fv_nom t -> x0 `notin` fv_nom t -> z <> y0 -> z <> x0 ->
  aeq (swap z x0 (swap y0 z t)) (swap y0 x0 t).
Proof.
  intro t; induction t.
  intros x0 y0 z; intros; simpl in *; unfold swap_var in *.
  default_simp; try fsetdec.
  intros x0 y0 z; intros; simpl in *; unfold swap_var in *.
Admitted.

Lemma aeq_trans_aux : forall n t2 t1 t3, size t2 <= n -> aeq t1 t2 -> aeq t2 t3 -> aeq t1 t3.
Proof.
  induction n;
  intros t2 t1 t3 SZ A1 A2;
  destruct t2; simpl in *; try omega; intros.
  - inversion A1. inversion A2. subst. auto.
  - inversion A1; inversion A2; subst.
    + eapply aeq_abs_same; eauto.
      eapply IHn; eauto; try omega.
    + eapply aeq_abs_diff; eauto.
      eapply IHn; eauto; try omega.
    + eapply aeq_abs_diff; eauto.
      rewrite <- aeq_fv_nom; eauto.
      assert (aeq (swap x x0 t2) (swap x x0 t6)).
      eapply aeq_equivariance; auto.
      eapply IHn; eauto.
      rewrite swap_size_eq. omega.
    + destruct (x0 == y0).
      ++ subst. eapply aeq_abs_same.
         assert (aeq (swap x y0 t2) (swap x y0 (swap y0 x t6))).
         eapply aeq_equivariance; auto.
         rewrite (swap_symmetric _ y0 x) in H.
         rewrite swap_involutive in H.
         eapply IHn; eauto.
         rewrite swap_size_eq. omega.
      ++ assert (x0 `notin` fv_nom t6).
         { apply (aeq_equivariance y0 x) in H10.
         rewrite swap_involutive in H10.
         rewrite <- (aeq_fv_nom _ _ H10); eauto.
         replace x0 with (swap_var y0 x x0).
         eapply notin_fv_nom_equivariance. auto.
         unfold swap_var; default_simp. }
         eapply aeq_abs_diff; eauto.
         * apply (aeq_equivariance x x0) in H10.
           pose (K := swap_fresh t6 x0 y0 x H8 H H7 ltac:(auto)). clearbody K.
           admit.
  - inversion A1; inversion A2; subst.
    eapply aeq_app. eapply IHn; eauto. omega.
    eapply IHn; eauto. omega.
Admitted.


(* /HIDE *)
