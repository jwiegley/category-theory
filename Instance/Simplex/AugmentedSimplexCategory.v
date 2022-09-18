Require Import Theory.Category.

Require Import 
        ssreflect ssrfun ssrbool
        mathcomp.ssreflect.seq
        mathcomp.ssreflect.ssrnat
        mathcomp.ssreflect.eqtype
        mathcomp.ssreflect.fintype
        mathcomp.ssreflect.finfun
        mathcomp.ssreflect.tuple
        mathcomp.ssreflect.ssrnat.

Set Primitive Projections.
Set Universe Polymorphism.
(* Unset Transparent Obligations. *)
Notation "''I_' n" := (ordinal n).
Definition stdfinsetcat : Category.
Proof.
  unshelve refine (Build_Category' (fun n m : nat => ('I_m)^n)%type
           (fun n => [ffun k => k ]) (fun n m k f g => [ ffun x => f (g x) ])).
  exact Morphism_equality.
  move => n m k f f' -> g g' ->. reflexivity.
  move => n m f /=; apply/ffunP => x /=; by rewrite 2!ffunE.
  move => ? ? ?; apply/ffunP => ?; by rewrite 2!ffunE.
  move => a b c d h g f; apply/ffunP => x; by rewrite 4!ffunE.
Defined.

(* fgraph f := sequence of elements of f, viewed as a tuple. *)
(* pairmap f a s := [f a x1, f x1 x2, .... ] *)

Proposition pairmap_trans_pairwise (A : Type) (R : rel A) (tr : transitive R) (xs : seq A) :
  pairwise R xs = if xs is x :: xs then
                    foldr andb true (pairmap R x xs) else true.
Proof.
  apply/idP/idP; case: xs => //; move => a l; elim: l a => // b l IH a /=;
          [ by (move/andP => [] => /andP [] -> _; apply: IH) |].
  move/andP => [] Rab; rewrite Rab => /= H.
  move/IH : H => H; apply/andP; split => //.
  rewrite /= in H; move/andP : H => [] z _; apply: sub_all z.
  rewrite /subpred => x; by apply: tr.
Qed.

(* For t a tuple, we have pairwise R t iff forall i j : 'I_n, R (tnth t i) (tnth t j) *)
Proposition tuple_pairwiseP (A : Type) (n : nat) (t : n.-tuple A) (R : rel A) :
  reflect {in ord_enum n &, { homo @tnth n _ t : i j / i < j >-> R i j } } (pairwise R t). 
Proof.
  case: n t.
  { move => t; rewrite tuple0 /=; apply: ReflectT. by move => i. }
  move => n t;  apply: (iffP (pairwiseP (thead t))); move => H i j.
  { move => i_in_enum j_in_enum ineq; 
    move : (H i j) ; rewrite size_tuple => z; 
    move : (z (ltn_ord i) (ltn_ord j) ineq) => k; 
    by rewrite 2! (tnth_nth (thead t)). }
  rewrite size_tuple. move => ibd jbd. set i' := Ordinal ibd; set j' := Ordinal jbd.
  rewrite -[i]/(nat_of_ord i') -[j]/(nat_of_ord j')  - 2! tnth_nth => ineq.
  by apply: H => //; apply: mem_ord_enum.
Qed.

Proposition tnth_tuple_of_finfun (A : Type) (n : nat) (f : A^n) (i : 'I_n) :
            tnth (tuple_of_finfun f) i = f i.
Proof.
  by rewrite -{2}(tuple_of_finfunK f) /finfun_of_tuple ffunE. 
Qed.  

Proposition tuple_of_finfun_fgraph (T : Type) (n : nat) (f : T^n):
  tuple_of_finfun f = (tcast (card_ord _) (fgraph f)).
Proof.
  apply eq_from_tnth => i.
  by rewrite tnth_tuple_of_finfun tcastE -enum_rank_ord tnth_fgraph enum_rankK.
Qed.

Definition monotonic {n m : nat} (f : 'I_m^n) : bool :=
  pairwise (fun i j : 'I_m => leq i j) (tuple_of_finfun f).

Definition monotonicP {n m : nat} (f : 'I_m^n) :
  reflect (forall i j : 'I_n, i <= j -> f i <= f j) (monotonic f).
Proof.
  rewrite /monotonic;
  apply/(iffP (tuple_pairwiseP _ _ _ _)) => H.
  { move => i j ineq. have k := (H i j (mem_ord_enum i) (mem_ord_enum j)).
    rewrite leq_eqVlt in ineq ; move/orP : ineq; case.
    { move/eqP => e. by rewrite (val_inj e). }
    move => x; move : (k x). by rewrite 2! tnth_tuple_of_finfun.
  }
  move => i j _ _ ineq. rewrite 2! tnth_tuple_of_finfun. apply: H; exact: ltnW.
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

(* Idea - use Canonical structures to handle monotonicity? *)
(* Structure monotonic_fn {n m : nat} := *)
(*   Monotonic { fn_of : 'I_m^n ; monotonicity : monotonic fn_of }. *)

(* Canonical Structure id_mon (n : nat) : @monotonic_fn n n := *)
(*   Monotonic _ _ (finfun (@id 'I_n)) (idmap_monotonic n). *)

(* Proposition idmap_monotonic (n : nat) : @monotonic n _ (finfun id). *)
(* Proof.                           *)
(*   rewrite /monotonic. *)
(*   apply/tuple_pairwiseP => ival jval i_in_enum j_in_enum ineq. *)
(*   rewrite 2! tnth_tuple_of_finfun 2! ffunE. *)
(*   by apply: ltnW. *)
(* Qed. *)

Record monotonic_fn_sig (n m : nat) := { fun_of_monotonic_fn :> 'I_m^n ;
                                         _ : monotonic fun_of_monotonic_fn }.
Arguments fun_of_monotonic_fn {n} {m} _.

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
  apply: eq_ffun => x /=.
  apply: f_equal; by rewrite ffunE.
Qed.

Definition comp_mon (n m k : nat) (g : @monotonic_fn m k) (f : @monotonic_fn n m):
  @monotonic_fn n k.
Proof.
  exists (comp (fun_of_monotonic_fn f) (fun_of_monotonic_fn g)).
  apply/monotonicP => i j ineq /=. rewrite 2! ffunE.
  move/monotonicP : (valP g) ; apply.
  by move/monotonicP : (valP f) ; apply.
Defined.

Definition id_mon (n : nat) : @monotonic_fn n n :=
  Sub (finfun (@id 'I_n)) (idmap_monotonic n).

Definition finord : Category.
Proof.
  unshelve refine (Build_Category' (fun n m => @monotonic_fn n m)
                                   id_mon comp_mon).
  exact Morphism_equality.
  move=> ? ? ? ? ? -> ? ? ->; reflexivity.
  by move=> n m [f fmon]; apply: val_inj => /=; apply ffunP => x; rewrite 2! ffunE.
  by move=> n m [f fmon]; apply: val_inj => /=; apply ffunP => x; rewrite 2! ffunE.
  move => a b c d [f fmon] [g gmon] [h hmon] ; apply: val_inj => /=.
  rewrite -comp_assoc. apply ffunP => z. by rewrite ! ffunE.
Defined.

Notation Δ := finord.
