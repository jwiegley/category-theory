Require Import Category.Lib.
Require Import Theory.Category.

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.tuple.

Set Primitive Projections.
Set Universe Polymorphism.

(* Unset Transparent Obligations. *)
Notation "''I_' n" := (ordinal n).

(* The category whose objects are "standard finite sets" [n] = { 0, ... n-1} and
   whose morphisms are all functions between them. *)

Program Definition stdfinset : Category :=
  {|
    obj     := nat;
    hom     := fun n m => ('I_m)^n;
    homset  := fun _ _ => {| equiv := eq |}; 
    Category.id      := fun n => [ffun k => k];
    compose := fun _ _ _ f g => [ffun x => f (g x)]
  |}.
  (* Right identity law - 
       The main lemma of this proof is function extensionality (ffunP).
       ffunE simplifies ([ffun x => t] a) to t[x/a]; 
       presumably the reason this needs to be explicitly called as lemma
       is to prevent term explosion through unnecessary simplification. *)
Next Obligation. apply/ffunP; intro i; rewrite ! ffunE; done. Qed.
(* Left identity law, same proof as before *)
Next Obligation. apply/ffunP; intro i; rewrite ! ffunE; done. Qed.
(* Associativity of composition law, same proof as before *)
Next Obligation. apply/ffunP; intro i; rewrite ! ffunE; done. Qed.
(* Associativity of composition law, same proof as before *)
Next Obligation. apply/ffunP; intro i; rewrite ! ffunE; done. Qed.


(* fgraph f := sequence of elements of f, viewed as a tuple. *)
(* pairmap f a s := [f a x1, f x1 x2, .... ] *)

(* If R is a transitive relation, then for any list xs, 
   (forall i j, i < i -> R xs[i] xs[j]) iff (forall i,  R (xs[i]) (xs[i+1]). *)
Open Scope nat_scope.
Proposition pairmap_trans_pairwise (A : Type) (R : rel A) (tr : transitive R) (xs : seq A) :
  pairwise R xs = if xs is x :: xs then
                    foldr andb true (pairmap R x xs) else true.
Proof.
  (* Convert boolean equality to logical bi-implication*)
  apply/idP/idP;
  (* reduce to the nontrivial case where the list xs is nonempty. *)
  destruct xs as [ | a l]; [ done | | done | ];
  (* Write xs := [a :: l] and induct on the tail list l; again, the 
     case where l is empty is trivial so solve that case and 
     write l := [b :: l] to reduce to the case [a :: b :: l]. *)
    revert a; induction l as [ | b l IH]; [ done | | done | ].
  (* Left-to-right implication *)
  { intro a.
    (* bookkeeping to translate Boolean conjunction into propositional conjunction *)
    move/andP; intros [H1 H2'];
      move/andP : H2' => [H2 H3]; simpl; apply/andP; split.
    (* First goal, R a b, is already in the assumption H1. *)
    { simpl in H1. move/andP: H1 => [ X ?]; exact: X. }
    { apply: IH. simpl; apply/andP; split.
      { exact: H2. }
      { exact: H3. }
    }
  }
  (* Right-to-left implication *)
  intros a. simpl.
     (* There are three goals here. 
        - R a b, which is an assumption 
        - all (R a) l, which we address last
        - pairwise R [b :: l] which follows immediately from the induction hypothesis on l 
          and an assumption. 
        We do some bookkeeping to convert Boolean conjunction to logical conjunction, and 
        take care of the first and third goals.
        *)
  move/andP; intros [Rab H2]; rewrite Rab; simpl.
  apply IH in H2; apply/andP; split; [ | exact: H2 ].
     (* This leaves only all (R a) l. 
        The lemma sub_all states that if P and Q are predicates, 
        and P => Q (P is a subpredicate of Q)
        then (all P) => (all Q), i.e, P holds for all elements in a list
        only if Q does. Thus it suffices to prove that (R b _) => (R a _).
        But this is immediate by the transitivitity of R.
        *) 
     rewrite /= in H2; move/andP : H2 => [] z _; apply: sub_all z.
     rewrite /subpred => x; apply: tr; done.
Qed.

(* For t a tuple, we have pairwise R t iff forall i j : 'I_n, R (tnth t i) (tnth t j) *)

Proposition tuple_pairwiseP (A : Type) (n : nat) (t : n.-tuple A) (R : rel A) :
  reflect {in ord_enum n &, { homo @tnth n _ t : i j / i < j >-> R i j } } (pairwise R t). 
Proof.
  revert n t; destruct n.
  (* We address the case of a 0-tuple separately because some math-comp lemmas
     are defined only for tuples of length n.+1.
  *)
  { intro t; rewrite tuple0; simpl; apply: ReflectT; done. }
  intro t.
  (* There is already a Boolean reflection lemma which 
     provides a logical specification of the behavior of the function pairwise,
     so all we have to do is prove that our logical specification is equivalent
     to the one already in the standard library.
   *)
  apply: (iffP (pairwiseP (thead t))); intros H i j.
  {
    intros i_in_enum j_in_enum ineq.
    assert (z := H i j). rewrite size_tuple in z.
    assert (k := (z (ltn_ord i) (ltn_ord j) ineq)).
    rewrite 2! (tnth_nth (thead t)). done.
  }
  { 
    rewrite size_tuple; intros ibd jbd;
      set i' := Ordinal ibd; set j' := Ordinal jbd.
    rewrite -[i]/(nat_of_ord i') -[j]/(nat_of_ord j') - 2! tnth_nth;
      intro ineq.
    apply: H; [ | | exact: ineq];
      apply: mem_ord_enum.
  } 
Qed.

Proposition tnth_tuple_of_finfun (A : Type) (n : nat) (f : A^n) (i : 'I_n) :
            tnth (tuple_of_finfun f) i = f i.
Proof.
  by rewrite -{2}(tuple_of_finfunK f) /finfun_of_tuple ffunE. 
Qed.  

Proposition tuple_of_finfun_fgraph (T : Type) (n : nat) (f : T^n):
  tuple_of_finfun f = (tcast (card_ord _) (fgraph f)).
Proof.
  apply eq_from_tnth; intro i.
  by rewrite tnth_tuple_of_finfun tcastE -enum_rank_ord tnth_fgraph enum_rankK.
Qed.

Definition monotonic {n m : nat} (f : 'I_m^n) : bool :=
  pairwise (fun i j : 'I_m => leq i j) (tuple_of_finfun f).

Definition monotonicP {n m : nat} (f : 'I_m^n) :
  reflect (forall i j : 'I_n, i <= j -> f i <= f j) (monotonic f).
Proof.
  rewrite /monotonic.
  (* There is already a logical specification of the behavior of the pairwise function
     in the standard library so we just have to prove our specificiation is 
     equivalent to that one. *)
  apply/(iffP (tuple_pairwiseP _ _ _ _)); intro H.
  { intros i j ineq.
    assert (k := (H i j (mem_ord_enum i) (mem_ord_enum j))).
    (* Go by cases on the disjunction i <= j -> i = j or i < j. *)
    (* Bookkeeping to convert between Boolean/logical disjunction. *)
    rewrite leq_eqVlt in ineq ; move/orP : ineq; intro ineq; destruct ineq as [eq | lt].
    { (* Case i = j. *)
      (* N. b. - Since the type bool satisfies UIP, 
         if P : A -> bool is a predicate on A, 
         given two elements (x,e) and (x', e') of { x : A | P x = true },
         (x, e) = (x', e') iff x = x' because e = e' always,
         as there is a unique proof of true = true. 
         Thus the inclusion of a subtype into the parent type is always injective.
         This is recorded in the lemma val_inj. *)
      move/eqP: eq; intro eq; by rewrite (val_inj eq). }
    assert (z := k lt).
    rewrite 2! tnth_tuple_of_finfun in z.
    exact: z.
  }
  intros i j _ _ ineq.
  rewrite 2! tnth_tuple_of_finfun. apply: H; exact: ltnW.
Qed.
    
Proposition monotonic_fold_equiv (n m : nat) (f : 'I_m^n) :
  monotonic f = let fg := tuple.tval (tuple_of_finfun f) in
                    if fg is x :: xs then
                      foldr andb true (pairmap (fun i j : 'I_m => leq i j) x xs) else true.
Proof.
  apply: pairmap_trans_pairwise; rewrite /nat_of_ord; by apply: leq_trans.
Qed.

Proposition idmap_monotonic (n : nat) : @monotonic n _ (finfun id).
Proof.
  apply/monotonicP => i j.
  by rewrite 2! ffunE.
Qed.

Record monotonic_fn_sig (n m : nat) := { fun_of_monotonic_fn :> 'I_m^n ;
                                         _ : monotonic fun_of_monotonic_fn }.
Arguments fun_of_monotonic_fn {n} {m} _.

(* The following definition
   records monotonic_fn with the hint database for subtypes,
   which means that we can apply lemmas about general subtypes to
   monotonic functions. For example, we can "apply val_inj" to conclude
   that two monotonic functions are equal if the underlying (finite) functions are equal
   after the monotonicity property is forgotten. 
   Monotonic functions are also equipped with a Boolean comparison function "==" automatically
   which is inherited from the underlying comparison function for finfuns.
 *)
Canonical Structure monotonic_fn (n m : nat) := [subType for (@fun_of_monotonic_fn n m) ].
Definition monotonic_fn_eqMixin (n m : nat) := [eqMixin of (monotonic_fn n m) by <:].
Canonical Structure monotonic_fn_eqType (n m : nat) := EqType (monotonic_fn n m)
                                                         (monotonic_fn_eqMixin n m).

Definition comp {aT : finType} {rT sT : Type} (f : {ffun aT -> rT}) (g : rT -> sT) :
  {ffun aT -> sT} :=  [ffun x => g (f x)].

Proposition comp_assoc {aT : finType} {rT sT mT: Type}
            (f : {ffun aT -> rT}) (g : rT -> sT) (h : sT -> mT) :
  comp f (g \; h) = comp (comp f g) h.
Proof.
  apply: eq_ffun; simpl; intro; apply: f_equal; by rewrite ffunE.
Qed.

Definition comp_mon (n m k : nat) (g : @monotonic_fn m k) (f : @monotonic_fn n m):
  @monotonic_fn n k.
Proof.
  exists (comp (fun_of_monotonic_fn f) (fun_of_monotonic_fn g)).
  apply/monotonicP.
  intros i j ineq; simpl.
  rewrite 2! ffunE.
  (* We make use of our logical specification of the "monotonic" function. *)
  move/monotonicP : (valP g). intro H; apply: H.
  by move/monotonicP : (valP f); intro H; apply H.
Defined.

Definition id_mon (n : nat) : @monotonic_fn n n :=
  Sub (finfun (@id 'I_n)) (idmap_monotonic n).

Program Definition finord : Category :=
  {|
    obj := nat;
    hom := fun n m => @monotonic_fn n m;
    homset := fun _ _ => {| equiv := eq |};
    Category.id := id_mon;
    compose := comp_mon;
    |}.
Next Obligation. apply: val_inj; simpl; apply ffunP; intro i; rewrite 2! ffunE; done. Qed.
Next Obligation. apply: val_inj; simpl; apply ffunP; intro i; rewrite 2! ffunE; done. Qed.
Next Obligation. apply: val_inj; simpl; apply ffunP; intro i; rewrite 4! ffunE; done. Qed.
Next Obligation. apply: val_inj; simpl; apply ffunP; intro i; rewrite 4! ffunE; done. Qed.
(* Done. *)

Notation Δ := finord.
