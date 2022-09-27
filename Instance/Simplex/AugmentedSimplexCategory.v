Require Import Category.Lib.
Require Import Theory.Category.

Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
(* Require Import Category.Instance.Simplex.Ordinals. *)

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.tuple.

Require Import Coq.Logic.FinFun.


Set Primitive Projections.
Set Universe Polymorphism.

(* Unset Transparent Obligations. *)

Notation "''I_' n" := (ordinal n).

(* First, we define the
   category whose objects are "standard finite sets" [n] = { 0, ... n-1} and
   whose morphisms are all functions between them. *)
Module stdfinset.
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
Open Scope nat_scope.

(* This file defines the coface and codegeneracy maps of the simplex category Δ
   (including the proofs that they are monotonic)
   and proves that the simplicial identities hold. 

   Letting [n] denote the n-th finite ordinal {0,... n-1},
   and letting i ∈ [n+1],
   the i-th coface map δ_i : [n] -> [n+1] 
   is the unique monotonic injection
   whose image does not contain i; that is, 
   δ_i(x) = x if x < i, else δ_i(x) = x+1 if x >= i. 

   We define δ_i in terms of the lift and bump functions from the 
   ssreflect fintype library.

   Again, letting i ∈ [n+1],
   the i-th codegeneracy map σ_i : [n+2] -> [n+1], (denoted σ_i), is
   the unique monotonic surjection such that the preimage of i contains two elements;
   that is, σ_i(x) = x if  x <= i; else, σ_i(x) = x-1 if x > i.

   These functions satisfy the following equations, called the simplicial identities:
   
   δ_j ∘ δ_i = δ_i ∘ δ_(j-1)   ;  i < j
   σ_j ∘ σ_i = σ_i ∘ σ_(j+1)   ;  i <= j
   σ_j ∘ δ_i = δ_i ∘ σ_(j-1)   ;  i < j
   σ_j ∘ δ_j = id = σ_j ∘ δ_(j+1)
   σ_j ∘ δ_i = δ_(i-1) ; i > j+1

   which we prove in this file. 
   References for this material include "Simplicial Objects in Algebraic Topology"
   by Peter May, or "Simplicial Homotopy Theory" by Goerss and Jardine.

   The above five equations are taken from page 1 of May's book, except
   that in his book they occur dualized, i.e., they are meant to be interpreted
   in the opposite category to our simplex category.
*)

Definition δ_stdfinset {n : nat} (i : 'I_(n.+1)) :
  @hom stdfinset n n.+1 := [ffun j : 'I_n => lift i j].

Lemma σ_subproof (n : nat) (i : 'I_(n.+1)) : forall j : 'I_(n.+2), unbump i j < n.+1.
Proof.
  intro j; rewrite ltnS -leq_bump. unfold bump.
  destruct i as [ival ibd]; simpl.
  rewrite -[ival <= n]ltnS ibd -ltnS; unfold addn; simpl.
  by (destruct j).
Qed.

Definition σ_stdfinset {n : nat} (i : 'I_(n.+1)) :
  @hom stdfinset n.+2 n.+1 := [ffun j : 'I_(n.+2) => Ordinal (σ_subproof n i j)].

Proposition predn_subproof (n : nat) (i : 'I_(n.+2)) : predn i < n.+1.
Proof.
  destruct i as [ival ibd]; destruct ival; done.
Qed.

Definition ord_predn {n : nat} (i : 'I_(n.+2)) : 'I_(n.+1) := Sub (predn i) (predn_subproof n i).
Definition ord_upcast {n : nat} (i : 'I_n) : 'I_n.+1.
Proof.
  destruct i as [ival ibd]; exists ival; auto with arith.
Defined.

Local Remove Hints ltnW : core.

Ltac stdfinset_simpl :=
  do ! (match goal with
        | [ |- @eq (ordinal _) _ _] => apply: val_inj; simpl
        | [ |- eqfun _ _ ] => unfold eqfun
        | [ |- @eq (@finfun_of _ _ _) _ _ ] => apply: eq_ffun
        | [ |- _ ] => fail_if_unchanged ltac:(rewrite ! ffunE)
        | [ |- _ ] => fail_if_unchanged simpl
         end).

Local Create HintDb stdfinset discriminated.
Local Hint Extern 0 => stdfinset_simpl : stdfinset.
Local Hint Extern 5 => (fail_if_unchanged ltac:(simpl)) : simplex.

(* Definitions of the face and degeneracy maps *)
Local Notation δ := δ_stdfinset.

(*   δ_j ∘ δ_i = δ_i ∘ δ_(j-1)   ;  i < j *)
Proposition δi_δj_stdfinset {n : nat} : forall i : 'I_(n.+1), forall j : 'I_(n.+2),
  forall (t : i < j),
    @compose stdfinset n n.+1 n.+2 (δ j) (δ i) =
      @compose stdfinset n n.+1 n.+2 (δ (ord_upcast i))
                                     (δ (ord_predn j)).
Proof.
  intros [ival ibd] [jval jbd] ineq; simpl in ineq.
  stdfinset_simpl. intros [xval xbd]; stdfinset_simpl.
  exact: δi_δj_nat.
Qed.

(*   σ_j ∘ σ_i = σ_i ∘ σ_(j+1)   ;  i <= j *)

Local Notation σ := σ_stdfinset.
Proposition σi_σj {n : nat} :
  forall (i j : 'I_(n.+1)), i <= j ->
  @compose stdfinset n.+3 n.+2 n.+1 (σ j) (σ (ord_upcast i)) =
      @compose stdfinset n.+3 n.+2 n.+1 (σ i)
                                     (σ (lift ord0 j)).
Proof.
  stdfinset_simpl.
  intros [ival ibd] [jval jbd] ineq; simpl in ineq; stdfinset_simpl.
  intros [xval xbd]. stdfinset_simpl.
  unfold bump. arith_simpl.
  exact: σi_σj_nat.
Qed.

Proposition δi_σj_1 {n : nat} :
  forall (i : 'I_n.+2) (j : 'I_n.+2), (i < j) ->
    @compose stdfinset n.+2 n.+3 n.+2 (σ j) (δ (ord_upcast i)) =
      @compose stdfinset n.+2 n.+1 n.+2 (δ i) (σ (ord_predn j)).
Proof.
  intros i j ineq; destruct i as [ival ibd], j as [jval jbd]; simpl in ineq.
  stdfinset_simpl. intros [xval xbd].
  stdfinset_simpl.
  exact: δi_σj_iltj_nat.
Qed.

Proposition σi_δi {n : nat} :
  forall (i : 'I_n.+1), @compose stdfinset n.+1 n.+2 n.+1 (σ i) (δ (ord_upcast i)) =
                          @Category.id stdfinset n.+1.
Proof.
  intros [ival ibd]. stdfinset_simpl. intros [xval xbd]. stdfinset_simpl.
  exact: bumpK.
Qed.

Proposition σSi_δi {n : nat} :
  forall (i : 'I_n.+1), @compose stdfinset n.+1 n.+2 n.+1 (σ i) (δ (lift ord0 i)) =
                          @Category.id stdfinset n.+1.
Proof.
  intros [ival ibd]. stdfinset_simpl. intros [xval xbd]. stdfinset_simpl.
  rewrite {2}/bump; stdfinset_simpl.
  exact: δSi_σi_eq_id_nat.
Qed.

Proposition δi_σj_2 {n : nat} : forall i : 'I_(n.+3), forall j : 'I_(n.+1),
  forall (t : i > j.+1),
    @compose stdfinset n.+2 n.+3 n.+2 (σ (ord_upcast j)) (δ i) =
      @compose stdfinset n.+2 n.+1 n.+2 (δ (ord_predn i)) (σ j).
Proof. 
  intros [ival ibd] [jval jbd]; simpl; intro ineq.
  stdfinset_simpl; intros [xval xbd].
  stdfinset_simpl.
  exact: δi_σj_i_gt_addnj1_nat.
Qed.

Definition surjective {A B : finType} (f : {ffun A -> B}) := 
  [forall y : B, y \in (image f A)].

(* Definition surjective {n m : nat} (f : 'I_m^n) := [forall y : 'I_m, mem (image f 'I_n) y]. *)

Proposition surjectiveP {A B : finType} (f : {ffun A -> B}) :
  reflect (Surjective f) (surjective f).
Proof.
  unfold surjective, Surjective.
  apply: (iffP forallP).
  { intros H y. set in_img := H y. exists (iinv in_img). exact: f_iinv. }
  { intros H x. simpl. apply (rwP mapP). set z:= (H x); destruct z as [a pf].
    unshelve eapply ex_intro2;
    [ exact: a | exact: mem_enum | 
             symmetry; rewrite -pf; by apply: f_equal ]. 
  }
Defined.

Proposition not_surj_has {n m : nat} (f : 'I_m^n) :
  has (λ x : 'I_m, x \notin [seq f x | x : 'I_n]) (enum 'I_m) = ~~ surjective f.
Proof.
  assert (z : enum 'I_m = tval (ord_tuple m)) by done; rewrite z; clear z.
  rewrite -(@existsb_tnth m  _ _ (ord_tuple m)); unfold surjective; rewrite negb_forall.
  apply: eq_existsb; intro x; by rewrite tnth_ord_tuple.
Qed.

Proposition existsPS (A : finType) (P : pred A) :  [exists x, P x] -> { x : A & P x }.
Proof.
  (* set j := [pick x : A | P x]. *)
  intro H.
  destruct (pickP P) as [x i | e].
  { exists x; exact: i. }
  { apply (rwP existsP) in H. apply False_rect; induction H;
      rewrite ( e x) in H; discriminate. }
Defined.

Proposition gtest_not_in_img {n m: nat} (f : 'I_m^n) (p : ~~ surjective f) : 'I_m.
Proof.
  unfold surjective in p; rewrite negb_forall in p.
  apply existsPS in p; destruct p as [x Px].
  exact: [ arg max_ ( i > x | i \notin (image f 'I_n) ) (nat_of_ord i) ].
Defined.
  
Local Notation compose := (@compose stdfinset).

Proposition facemap_factors_subpf {n m : nat} (f : 'I_(m.+1)^n) (i : 'I_m.+1)
  (p : i \notin (image f 'I_n)) : forall x : 'I_n, unbump i (f x) < m.
Proof.
  intro x.
  assert (am1 : ~ i = f x );
    [ intro r; rewrite r in p; apply (rwP negP) in p;
      contradiction p; exact: image_f |].
  destruct (f x) as [yval ybd]; unfold unbump; simpl.
  remember (i < yval) as b eqn:Heqn; apply symmetry in Heqn; destruct b.
  { rewrite subn1; clear am1; rewrite ltnS in ybd. 
    by rewrite (ltn_predK Heqn). }
  { apply (negbT) in Heqn. rewrite -ltnNge ltnS leq_eqVlt in Heqn.
    apply (rwP orP) in Heqn; destruct Heqn as [eq | lt].
    { apply (rwP eqP) in eq. contradiction am1; by apply: val_inj. }
    { destruct i as [ival ibd]; clear p am1. simpl in lt; rewrite ltnS in ibd.
      rewrite subn0. by apply (@leq_trans ival). }
  }
Qed.
  (* ∃ g : 'I_m^n, f = compose (δ i) g. *)
Proposition facemap_factoring_map {n m : nat} (f : 'I_(m.+1)^n) (i : 'I_m.+1)
  (p : i \notin (image f 'I_n)) : 'I_m^n.
Proof.
  apply finfun; intro x; set y := f x; simpl in y.
  refine (Sub (unbump i y) _); exact: facemap_factors_subpf.
Defined.

Proposition facemap_factoring_eq {n m : nat} (f : 'I_(m.+1)^n) (i : 'I_m.+1)
  (p : i \notin (image f 'I_n)) :
  let g := facemap_factoring_map f i p in
  f = compose (δ i) g.
Proof.
  simpl.
  apply ffunP; intro x; simpl; rewrite ! ffunE.
  unfold lift; apply val_inj; simpl. 
  rewrite unbumpKcond.
  set z:= ( _ == _ ); cut (z = false); [ intro RW; by rewrite RW |]; unfold z; clear z.
  apply (introF (eqP)); intro eq; apply val_inj in eq.
  apply (rwP negP) in p; apply p; rewrite -eq.
  exact: image_f.
Qed.

Definition hitstwice {n m : nat} (f : 'I_(m.+1)^n) (i : 'I_m.+1) :=
  [exists x : 'I_n, exists y : 'I_n, (x < y) && (f x == i) && (f y == i) ].

Definition degeneracy_factoring_map {n m : nat} (f : 'I_(m.+1)^n) (i : 'I_m.+1)
  (p : hitstwice f i) : 'I_(m.+2)^n.
Proof.
  apply finfun; intro x.
  unfold hitstwice in p.
  apply existsPS in p; destruct p as [x1 p].
  assert (z : i < m.+2) by abstract(destruct i as [ival ibd]; by apply (@leq_trans m.+1)).
  set i' := Ordinal z.
  exact: (if x == x1 then i' else (lift i' (f x))).
Defined.

Proposition degeneracy_factoring_map_eq {n m : nat} (f : 'I_(m.+1)^n) (i : 'I_m.+1)
  (p : hitstwice f i) :
  let g := degeneracy_factoring_map f i p in
  f = compose (σ i) g. 
Proof.
  simpl. apply ffunP; intro x; rewrite ! ffunE; apply val_inj; unfold degeneracy_factoring_map;
    simpl.
  set k := existsPS _ _ _; destruct k as [x1 k'].
  remember (x == x1) as b eqn:Heqn; apply symmetry in Heqn; destruct b; rewrite Heqn.
  { simpl. apply (rwP existsP) in k'; destruct k' as [x2 conj].
    apply (rwP andP) in conj; destruct conj as  [conj _];
      apply (rwP andP) in conj; destruct conj as [ _ fx1i].
    apply (rwP eqP) in Heqn. rewrite Heqn. apply (rwP eqP) in fx1i. rewrite fx1i.
    unfold unbump. by rewrite ltnn subn0. }
  { by symmetry; apply: bumpK. }
Qed.

Definition not_surjective_cd_nonzero {n : nat} (f : 'I_0^n) : surjective f.
Proof.
  apply (rwP (surjectiveP f)); intros [yval ybd]; discriminate.
Qed.


End stdfinset.

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

