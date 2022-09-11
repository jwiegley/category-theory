Require Import Coq.PArith.PArith.
Require Import Coq.Vectors.Vector.

Require Import Category.Lib.
Require Import Category.Lib.IListVec.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.

Set Transparent Obligations.

(** Lists in Ltac *)

Ltac addToList x xs :=
  let rec go ys :=
    lazymatch ys with
    | tt => constr:((x, xs))
    | (x, _) => xs
    | (_, ?ys') => go ys'
    end in
  go xs.

Example test_addToList : True.
Proof.
  let xs1 := addToList 1%nat tt in
  let xs2 := addToList 2%nat xs1 in
  let xs3 := addToList 3%nat xs2 in
  let xs4 := addToList 2%nat xs3 in
  (pose xs1 as l1;
   pose xs2 as l2;
   pose xs3 as l3;
   pose xs4 as l4).
  assert (l1 = (1%nat, ())) by auto.
  assert (l2 = (2%nat, (1%nat, ()))) by auto.
  assert (l3 = (3%nat, (2%nat, (1%nat, ())))) by auto.
  assert (l4 = (3%nat, (2%nat, (1%nat, ())))) by auto.
  exact I.
Qed.

Ltac listSize xs :=
  lazymatch xs with
  | tt => constr:(0%nat)
  | (_, ?xs') =>
    let n := listSize xs' in
    constr:((S n)%nat)
  end.

Example test_listSize : True.
Proof.
  let xs1 := addToList 1%nat tt in
  let xs2 := addToList 2%nat xs1 in
  let xs3 := addToList 3%nat xs2 in
  let xs4 := addToList 2%nat xs3 in
  let ls0  := listSize tt in
  let ls1  := listSize xs1 in
  let ls2  := listSize xs2 in
  let ls3  := listSize xs3 in
  let ls4  := listSize xs4 in
  (pose ls0 as s0;
   pose ls1 as s1;
   pose ls2 as s2;
   pose ls3 as s3;
   pose ls4 as s4).
  assert (s0 = 0%nat) by auto.
  assert (s1 = 1%nat) by auto.
  assert (s2 = 2%nat) by auto.
  assert (s3 = 3%nat) by auto.
  assert (s4 = 3%nat) by auto.
  exact I.
Qed.

Ltac lookup x xs :=
  lazymatch xs with
  | (x, _) => constr:(1%positive)
  | (_, ?xs') =>
    let xn := lookup x xs' in
    constr:(Pos.succ xn)
  end.

Example test_lookup : True.
Proof.
  Fail (
    let xs1 := addToList 1%nat tt in
    let lk1 := lookup 2%nat xs1 in
    pose lk1
  ).
  let xs1 := addToList 1%nat tt in
  let xs2 := addToList 2%nat xs1 in
  let xs3 := addToList 3%nat xs2 in
  let xs4 := addToList 4%nat xs3 in
  let lk2 := lookup 2%nat xs4 in
  let lk3 := lookup 3%nat xs4 in
  let lk4 := lookup 4%nat xs4 in
  (pose lk2 as f2;
   pose lk3 as f3;
   pose lk4 as f4).
  assert (f2 = Pos.succ (Pos.succ 1)) by auto.
  assert (f3 = Pos.succ 1) by auto.
  assert (f4 = 1%positive) by auto.
  exact I.
Qed.

Ltac lookupFin n x xs :=
  lazymatch n with
  | S ?n' =>
    lazymatch xs with
    | (x, _) => constr:(@Fin.F1 n')
    | (_, ?xs') =>
      let xn := lookupFin n' x xs' in
      constr:(Fin.FS xn)
    end
  end.

Example test_lookupFin : True.
Proof.
  Fail (
    let xs1 := addToList 1%nat tt in
    let ls1  := listSize xs1 in
    let lk1 := lookupFin ls1 2%nat xs1 in
    (pose lk1)
  ).
  let xs1 := addToList 1%nat tt in
  let xs2 := addToList 2%nat xs1 in
  let xs3 := addToList 3%nat xs2 in
  let xs4 := addToList 4%nat xs3 in
  let ls1  := listSize xs1 in
  let ls2  := listSize xs2 in
  let ls3  := listSize xs3 in
  let ls4  := listSize xs4 in
  let lk2 := lookupFin ls2 2%nat xs2 in
  let lk3 := lookupFin ls3 2%nat xs3 in
  let lk4 := lookupFin ls4 2%nat xs4 in
  (pose lk2 as f2;
   pose lk3 as f3;
   pose lk4 as f4).
  assert (f2 = Fin.F1) by auto.
  assert (f3 = Fin.FS Fin.F1) by auto.
  assert (f4 = Fin.FS (Fin.FS Fin.F1)) by auto.
  exact I.
Qed.

(** Lists of lists in Ltac *)

Ltac addToCatList c cs :=
  let rec go xs :=
    lazymatch xs with
    | tt => constr:(((c, tt, tt), cs))
    | ((c, _, _), _) => constr:(cs)
    | (_, ?xs') => go xs'
    end in
  go cs.

Example test_addToCatList (C D : Category) : True.
Proof.
  let xs1 := addToCatList C tt in
  let xs2 := addToCatList D xs1 in
  let xs3 := addToCatList C xs2 in
  (pose xs1 as l1;
   pose xs2 as l2;
   pose xs3 as l3).
  assert (l1 = ((C, (), ()), ())) by auto.
  assert (l2 = ((D, (), ()), ((C, (), ()), ()))) by auto.
  assert (l3 = ((D, (), ()), ((C, (), ()), ()))) by auto.
  exact I.
Qed.

Ltac lookupCat c cs :=
  lazymatch cs with
  | ((c, _, _), _) => constr:(1%positive)
  | (_, ?cs') =>
    let cn := lookupCat c cs' in
    constr:(Pos.succ cn)
  end.

Example test_lookupCat (C D E : Category) : True.
Proof.
  Fail (
    let xs1 := addToCatList D tt in
    let lk1 := lookupCat C xs1 in
    pose lk1
  ).
  let xs1 := addToCatList C tt in
  let xs2 := addToCatList D xs1 in
  let xs3 := addToCatList E xs2 in
  let lk1 := lookupCat C xs3 in
  let lk2 := lookupCat D xs3 in
  let lk3 := lookupCat E xs3 in
  (pose lk1 as f1;
   pose lk2 as f2;
   pose lk3 as f3).
  assert (f1 = Pos.succ (Pos.succ 1)) by auto.
  assert (f2 = Pos.succ 1) by auto.
  assert (f3 = 1%positive) by auto.
  exact I.
Qed.

Ltac catLists c cs :=
  lazymatch cs with
  | ((c, ?os, ?fs), _) => constr:((os, fs))
  | (_, ?cs') => catLists c cs'
  end.

Example test_catLists (C D E : Category) : True.
Proof.
  Fail (
    let xs1 := addToCatList D tt in
    let lk1 := catLists C xs1 in
    pose lk1
  ).
  let xs1 := addToCatList C tt in
  let lk1 := catLists C xs1 in
  (pose lk1 as f1).
  assert (f1 = ((), ())) by auto.
  exact I.
Qed.

Ltac updateCat c cs f :=
  let rec go xs :=
    lazymatch xs with
    | ((c, ?os, ?fs), ?xs') =>
      let res := f os fs in
      match res with
      | (?os', ?fs') =>
        constr:(((c, os', fs'), xs'))
      end
    | tt => constr:(tt)
    | (?x, ?xs') =>
      let xs' := go xs' in
      constr:((x, xs'))
    end in
  go cs.

Example test_updateCat (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let lk1 := updateCat C cs1 ltac:(fun os fs =>
               let os' := addToList 1%nat os in
               let fs' := addToList 3%nat fs in
               constr:((os', fs'))) in
  (pose lk1 as f1).
  assert (f1 = (C, (1%nat, ()), (3%nat, ()), ())) by auto.
  exact I.
Qed.

Ltac addToObjList c cs o :=
  updateCat c cs
    ltac:(fun os fs =>
            let os' := addToList o os in
            constr:((os', fs))).

Example test_addToObjList (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let lk1 := addToObjList C cs1 1%nat in
  (pose lk1 as f1).
  assert (f1 = ((C, (1%nat, ()), tt), ())) by auto.
  exact I.
Qed.

Ltac addToArrList c cs f :=
  updateCat c cs
    ltac:(fun os fs =>
            let fs' := addToList f fs in
            constr:((os, fs'))).

Example test_addToArrList (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let lk1 := addToArrList C cs1 1%nat in
  (pose lk1 as f1).
  assert (f1 = ((C, tt, (1%nat, ())), ())) by auto.
  exact I.
Qed.

Ltac lookupObjPos c cs o :=
  let res := catLists c cs in
  match res with
  | (?os, _) => lookup o os
  end.

Example test_lookupObjPos (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let cs2 := addToObjList C cs1 123%nat in
  let cs3 := addToObjList C cs2 456%nat in
  let cs4 := addToObjList C cs3 789%nat in
  let lk1 := lookupObjPos C cs4 456%nat in
  (pose lk1 as f1).
  assert (f1 = Pos.succ 1) by auto.
  exact I.
Qed.

Ltac lookupObj c cs o :=
  let res := catLists c cs in
  match res with
  | (?os, _) =>
    let n := listSize os in
    lookupFin (S n) o os
  end.

Example test_lookupObj (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let cs2 := addToObjList C cs1 123%nat in
  let cs3 := addToObjList C cs2 456%nat in
  let cs4 := addToObjList C cs3 789%nat in
  let lk1 := lookupObj C cs4 456%nat in
  (pose lk1 as f1).
  assert (f1 = Fin.FS Fin.F1) by auto.
  exact I.
Qed.

Ltac lookupArrPos c cs f :=
  let res := catLists c cs in
  match res with
  | (_, ?fs) =>
    lookup f fs
  end.

Example test_lookupArrPos (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let cs2 := addToArrList C cs1 123%nat in
  let cs3 := addToArrList C cs2 456%nat in
  let cs4 := addToArrList C cs3 789%nat in
  let lk1 := lookupArrPos C cs4 456%nat in
  (pose lk1 as f1).
  assert (f1 = Pos.succ 1) by auto.
  exact I.
Qed.

Ltac lookupArr c cs f :=
  let res := catLists c cs in
  match res with
  | (_, ?fs) =>
    let n := listSize fs in
    lookupFin (S n) f fs
  end.

Example test_lookupArr (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let cs2 := addToArrList C cs1 123%nat in
  let cs3 := addToArrList C cs2 456%nat in
  let cs4 := addToArrList C cs3 789%nat in
  let lk1 := lookupArr C cs4 456%nat in
  (pose lk1 as f1).
  assert (f1 = Fin.FS Fin.F1) by auto.
  exact I.
Qed.

(** Variable capture *)

Ltac allObjs c cs o :=
  lazymatch o with
  | ?x × ?y => let cs := allObjs c cs x in allObjs c cs y
  | ?x      => addToObjList c cs x
  end.

Example test_allObjs
  (C : Category) `{@Cartesian C}
  (x y z w : C) :
  True.
Proof.
  let cs := addToCatList C tt in
  let v := allObjs C cs constr:(x) in
  pose v as p.
  assert (p = (C, (x, ()), (), ())) as H0 by auto.
  clear p H0.

  let cs := addToCatList C tt in
  let v := allObjs C cs constr:(x × y) in
  pose v as p.
  assert (p = (C, (y, (x, ())), (), ())) as H0 by auto.
  clear p H0.

  let cs := addToCatList C tt in
  let v := allObjs C cs constr:((x × y) × (z × w)) in
  pose v as p.
  assert (p = (C, (w, (z, (y, (x, ())))), (), ())) as H0 by auto.
  clear p H0.

  exact I.
Qed.

Ltac allVars cs e :=
  lazymatch e with
  | @id ?c ?o       => let cs := addToCatList c cs in
                       addToObjList c cs o
  | @exl ?c _ ?x ?y => let cs := addToCatList c cs in
                       let cs := addToObjList c cs x in
                       addToObjList c cs y
  | @exr ?c _ ?x ?y => let cs := addToCatList c cs in
                       let cs := addToObjList c cs x in
                       addToObjList c cs y

  | ?f ∘ ?g => let cs := allVars cs f in allVars cs g
  | ?X ≈ ?Y => let cs := allVars cs X in allVars cs Y
  | ?f △ ?g => let cs := allVars cs f in allVars cs g
  | ?P → ?Q => let cs := allVars cs P in allVars cs Q
  | ?f      =>

    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
        let cs := addToCatList c cs in
        let cs := allObjs c cs x in
        let cs := allObjs c cs y in
        addToArrList c cs f
    end
  end.

Example test_allVars
  (C : Category) `{@Cartesian C}
  (x y z w : C)
  (f f' : y ~> z)
  (g g' : x ~> y)
  (k : y × z ~> w)
  (h : x ~> y × z) :
  True.
Proof.
  let v := allVars tt constr:(id[x]) in
  pose v as p.
  assert (p = (C, (x, ()), (), ())) as H0 by auto.
  clear p H0.

  let v := allVars tt constr:(f ∘ g) in
  pose v as p.
  assert (p = (C, (x, (z, (y, ()))), (g, (f, ())), ())) as H0 by auto.
  clear p H0.

  let v := allVars tt constr:(f ≈ f') in
  pose v as p.
  assert (p = (C, (z, (y, ())), (f', (f, ())), ())) as H0 by auto.
  clear p H0.

  let v := allVars tt constr:(f ≈ f' → g ≈ g') in
  pose v as p.
  assert (p = (C, (x, (z, (y, ()))), (g', (g, (f', (f, ())))), ())) as H0
    by auto.
  clear p H0.

  let v := allVars tt constr:(f) in
  pose v as p.
  assert (p = (C, (z, (y, ())), (f, ()), ())) as H0 by auto.
  clear p H0.

  let v := allVars tt constr:(exl ∘ h) in
  pose v as p.
  assert (p = (C, (x, (z, (y, ()))), (h, ()), ())) as H0 by auto.
  clear p H0.

  let v := allVars tt constr:(exr ∘ h) in
  pose v as p.
  assert (p = (C, (x, (z, (y, ()))), (h, ()), ())) as H0 by auto.
  clear p H0.

  let v := allVars tt constr:(k ∘ h) in
  pose v as p.
  assert (p = (C, (x, (w, (z, (y, ())))), (h, (k, ())), ())) as H0 by auto.
  clear p H0.

  let v := allVars tt constr:(f △ f') in
  pose v as p.
  assert (p = (C, (z, (y, ())), (f', (f, ())), ())) as H0 by auto.
  clear p H0.

  exact I.
Qed.

(** Term capture *)

Ltac reifyObj cs o :=
  lazymatch o with
  | ?x × ?y =>
    let xo := reifyObj cs x in
    let yo := reifyObj cs y in
    constr:(@SPair xo yo)
  | ?x =>
    lazymatch type of x with
    | @obj ?c =>
      let o := lookupObjPos c cs x in
      constr:(@SOb o)
    end
  end.

Example test_reifyObj
  (C : Category) `{@Cartesian C}
  (x y z w : C)
  (f : y ~> z)
  (k : y × z ~> w) :
  True.
Proof.
  let v := allVars tt constr:(f) in
  let o := reifyObj v constr:(y) in
  pose v as pv;
  pose o as po.
  assert (pv = (C, (z, (y, ())), (f, ()), ())) as Hv by auto.
  assert (po = SOb (Pos.succ 1)) as Ho by auto.
  clear pv po Hv Ho.

  let v := allVars tt constr:(k) in
  let o := reifyObj v constr:(y × z) in
  pose v as pv;
  pose o as po.
  assert (pv = (C, (w, (z, (y, ()))), (k, ()), ())) as Hv by auto.
  assert (po = SPair (SOb (Pos.succ (Pos.succ 1))) (SOb (Pos.succ 1))) as Ho by auto.
  clear pv po Hv Ho.

  exact I.
Qed.

Ltac reifyTerm cs t :=
  lazymatch t with
  | @id _ _ => constr:(@SIdent)
  | @compose _ _ _ _ ?f ?g =>
    let ft := reifyTerm cs f in
    let gt := reifyTerm cs g in
    constr:(@SComp ft gt)
  | @exl _ _ _ _ => constr:(@SExl)
  | @exr _ _ _ _ => constr:(@SExr)
  | ?f △ ?g =>
    let ft := reifyTerm cs f in
    let gt := reifyTerm cs g in
    constr:(@SFork ft gt)
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let fn := lookupArrPos c cs f in
      constr:(@SMorph fn)
    end
  end.

Example test_reifyTerm
  (C : Category) `{@Cartesian C}
  (x y z w : C)
  (f f' : y ~> z)
  (g : x ~> y)
  (k : y × z ~> w)
  (h : x ~> y × z) :
  True.
Proof.
  let t := reifyTerm tt constr:(id[x]) in
  pose t as pt.
  assert (pt = SIdent) as H0 by auto.
  clear pt H0.

  let v := allVars tt constr:(f) in
  let t := reifyTerm v constr:(f) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (z, (y, ())), (f, ()), ())) as Hv by auto.
  assert (pt = SMorph 1) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(f ∘ g) in
  let t := reifyTerm v constr:(f ∘ g) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (x, (z, (y, ()))), (g, (f, ())), ())) as Hv by auto.
  assert (pt = SComp (SMorph (Pos.succ 1)) (SMorph 1)) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(f ∘ id) in
  let t := reifyTerm v constr:(f ∘ id) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (z, (y, ())), (f, ()), ())) as Hv by auto.
  assert (pt = SComp (SMorph 1) SIdent) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(id ∘ f) in
  let t := reifyTerm v constr:(id ∘ f) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (y, (z, ())), (f, ()), ())) as Hv by auto.
  assert (pt = SComp SIdent (SMorph 1)) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(exl ∘ h) in
  let t := reifyTerm v constr:(exl ∘ h) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (x, (z, (y, ()))), (h, ()), ())) as Hv by auto.
  assert (pt = SComp SExl (SMorph 1)) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(exr ∘ h) in
  let t := reifyTerm v constr:(exr ∘ h) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (x, (z, (y, ()))), (h, ()), ())) as Hv by auto.
  assert (pt = SComp SExr (SMorph 1)) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(k ∘ h) in
  let t := reifyTerm v constr:(k ∘ h) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (x, (w, (z, (y, ())))), (h, (k, ())), ())) as Hv by auto.
  assert (pt = SComp (SMorph (Pos.succ 1)) (SMorph 1)) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(f △ f') in
  let t := reifyTerm v constr:(f △ f') in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (z, (y, ())), (f', (f, ())), ())) as Hv by auto.
  assert (pt = SFork (SMorph (Pos.succ 1)) (SMorph 1)) as Ht by auto.
  clear pv pt Hv Ht.

  exact I.
Qed.

Ltac reifyExpr cs t :=
  lazymatch t with
  | True => constr:(@STop)
  | False => constr:(@SBottom)
  | ?F ≈ ?G =>
    let f := reifyTerm cs F in
    let g := reifyTerm cs G in
    lazymatch type of F with
    | ?x ~{?c}~> ?y =>
      let xn := reifyObj cs x in
      let yn := reifyObj cs y in
      constr:(@SEquiv xn yn f g)
    end
  | ?P ∧ ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(@SAnd p q)
  | ?P ∨ ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(@SOr p q)
  | ?P → ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(@SImpl p q)
  end.

Example test_reifyExpr
  (C : Category)
  (x y z : C)
  (f : y ~> z)
  (g : x ~> y) :
  True.
Proof.
  let t := reifyExpr tt constr:(True) in
  pose t as pt.
  assert (pt = STop) as H0 by auto.
  clear pt H0.

  let t := reifyExpr tt constr:(False) in
  pose t as pt.
  assert (pt = SBottom) as H0 by auto.
  clear pt H0.

  let v := allVars tt constr:(f ≈ f ∘ id) in
  let t := reifyExpr v constr:(f ≈ f ∘ id) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (z, (y, ())), (f, ()), ())) as Hv by auto.
  assert (pt = SEquiv (SOb (Pos.succ 1)) (SOb 1) (SMorph 1) (SComp (SMorph 1) SIdent))
    as Ht by auto.
  clear pv pt Hv Ht.

  let t := reifyExpr tt constr:(True ∧ True) in
  pose t as pt.
  assert (pt = SAnd STop STop) as H0 by auto.
  clear pt H0.

  let t := reifyExpr tt constr:(True ∨ True) in
  pose t as pt.
  assert (pt = SOr STop STop) as H0 by auto.
  clear pt H0.

  let t := reifyExpr tt constr:(True → True) in
  pose t as pt.
  assert (pt = SImpl STop STop) as H0 by auto.
  clear pt H0.

  exact I.
Qed.

(** Build environment *)

(* This [foldr1] is not like what you're used to. The type is roughly:

     foldr1 {A B} : NonEmpty A → (A → B) → (A → B → B) → B

   It's really more a foldr on non-empty lists that takes a function over the
   last element as its base case. Very special purpose for this code. *)

Ltac foldr1 xs z f :=
  let rec go xs :=
    lazymatch xs with
    | (?x, tt) =>
      let z' := z x in f x z'
    | (?x, ?xs') =>
      let rest := go xs' in
      let x'   := f x rest in constr:(x')
    end in go xs.

(* [foldri1] behaves much like [foldr1], but it increments a [positive]
   counter as it goes and passes this index to both function arguments.

     foldri1 {A B} :
       NonEmpty A → (positive → A → B) → (positive → A → B → B) → B

   jww (2022-09-11): At the moment this function isn't needed, but when this
   code move to support multiple categories in a single expression (such as
   involving functors), it will be needed. *)

Ltac foldri1 xs z f :=
  let rec go n xs :=
    lazymatch xs with
    | (?x, tt) =>
      let z' := z n x in f n x z'
    | (?x, ?xs') =>
      let rest := go (Pos.succ n) xs' in
      let x'   := f n x rest in constr:(x')
    end in go 1%positive xs.

Import VectorNotations.

Ltac build_objs cs andThen :=
  foldri1 cs
    ltac:(fun _ci cv =>
      match cv with
      | (?c, ?os, ?fs) =>
        andThen c ltac:(
          foldr1 os
            ltac:(fun ov => constr:(ov :: Vector.nil c))
            ltac:(fun ov os => constr:(ov :: os))) fs
      end)
    ltac:(fun _ci cv _k =>
      (* jww (2022-09-11): Right now we only use the first category *)
      match cv with
      | (?c, ?os, ?fs) =>
        andThen c ltac:(
          foldr1 os
            ltac:(fun ov => constr:(ov :: Vector.nil c))
            ltac:(fun ov os => constr:(ov :: os))) fs
      end).

Ltac build_arrs c cs fs objs andThen :=
  andThen ltac:(
    foldr1 fs
      ltac:(fun f =>
        lazymatch type of f with
        | ?x ~{?c}~> ?y =>
          let xn := reifyObj cs x in
          let yn := reifyObj cs y in
          constr:(icons (B:=arrD objs) (sobjD xn, sobjD yn) f
                    (inil (B:=arrD objs)))
        end)
      ltac:(fun f fs =>
        lazymatch type of f with
        | ?x ~{?c}~> ?y =>
          let xn := reifyObj cs x in
          let yn := reifyObj cs y in
          constr:(icons (B:=arrD objs) (sobjD xn, sobjD yn) f fs)
        end)).

Ltac find_vars :=
  lazymatch goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    pose cs;
    build_objs cs ltac:(fun c objs fs =>
      pose objs;
      build_arrs c cs fs objs ltac:(fun arrs =>
        pose arrs))
  end.

Example ex_find_vars (C : Category) `{@Cartesian C}
  (x y : C) (f : x ~> y) (g : y ~> x) :
  g ≈ g → f ≈ f.
Proof.
  intros.
  find_vars.
  reflexivity.
Qed.

Definition vec_size {A n} (l : Vector.t A n) : nat := n.

Ltac reify_terms_and_then tacGoal :=
  match goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    let g  := reifyExpr cs G in
    build_objs cs ltac:(fun c objs fs =>
      build_arrs c cs fs objs ltac:(fun arrs =>
        let env :=
            constr:({|
              cat      := c;
              num_objs := ltac:(vm_compute (S (vec_size objs)));
              objs     := objs;
              num_arrs := ltac:(vm_compute (S (vec_size (vec_of arrs))));
              tys      := ltac:(vm_compute (vec_of arrs));
              arrs     := arrs |}) in
        tacGoal env g))
  end.

Ltac reify := reify_terms_and_then ltac:(fun env g => pose env; pose g).

Ltac reify_and_change :=
  reify_terms_and_then ltac:(fun env g => change (@sexprD env g)).

Example ex_reify_and_change
  (C : Category) `{@Cartesian C} (x y z w : C)
  (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z) :
  g ∘ h ≈ i ->
  f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  reify_and_change.
  vm_compute.
  (* match goal with *)
  (* | [ |- @equiv _ (@homset _ _ _) ?X ?Y ] => idtac *)
  (* end. *)
  cat; try apply comp_assoc.
Qed.

Example ex_reify_and_change_cartesian
  (C : Category) `{@Cartesian C} (x y z w : C)
  (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z) :
  g ∘ h ≈ i ->
  f ∘ (id ∘ exl ∘ (id ∘ g ∘ h) △ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  reify_and_change.
  vm_compute.
  (* match goal with *)
  (* | [ |- @equiv _ (@homset _ _ _) ?X ?Y ] => idtac *)
  (* end. *)
  cat; try apply comp_assoc.
Qed.
