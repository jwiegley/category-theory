Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.

Import ListNotations.

Open Scope nat_scope.

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
  let xs1 := addToList 1 tt in
  let xs2 := addToList 2 xs1 in
  let xs3 := addToList 3 xs2 in
  let xs4 := addToList 2 xs3 in
  (pose xs1 as l1;
   pose xs2 as l2;
   pose xs3 as l3;
   pose xs4 as l4).
  assert (l1 = (1, ())) by auto.
  assert (l2 = (2, (1, ()))) by auto.
  assert (l3 = (3, (2, (1, ())))) by auto.
  assert (l4 = (3, (2, (1, ())))) by auto.
  exact I.
Qed.

Ltac listSize xs :=
  lazymatch xs with
  | tt => constr:(0)
  | (_, ?xs') =>
    let n := listSize xs' in
    constr:((S n))
  end.

Example test_listSize : True.
Proof.
  let xs1 := addToList 1 tt in
  let xs2 := addToList 2 xs1 in
  let xs3 := addToList 3 xs2 in
  let xs4 := addToList 2 xs3 in
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
  assert (s0 = 0) by auto.
  assert (s1 = 1) by auto.
  assert (s2 = 2) by auto.
  assert (s3 = 3) by auto.
  assert (s4 = 3) by auto.
  exact I.
Qed.

Ltac lookup x xs :=
  lazymatch xs with
  | (x, _) => constr:(0)
  | (_, ?xs') =>
    let xn := lookup x xs' in
    constr:(S xn)
  end.

Example test_lookup : True.
Proof.
  Fail (
    let xs1 := addToList 1 tt in
    let lk1 := lookup 2 xs1 in
    pose lk1
  ).
  let xs1 := addToList 1 tt in
  let xs2 := addToList 2 xs1 in
  let xs3 := addToList 3 xs2 in
  let xs4 := addToList 4 xs3 in
  let lk2 := lookup 2 xs4 in
  let lk3 := lookup 3 xs4 in
  let lk4 := lookup 4 xs4 in
  (pose lk2 as f2;
   pose lk3 as f3;
   pose lk4 as f4).
  assert (f2 = 2) by auto.
  assert (f3 = 1) by auto.
  assert (f4 = 0) by auto.
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
  | ((c, _, _), _) => constr:(0)
  | (_, ?cs') =>
    let cn := lookupCat c cs' in
    constr:(S cn)
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
  assert (f1 = 2) by auto.
  assert (f2 = 1) by auto.
  assert (f3 = 0) by auto.
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
               let os' := addToList 1 os in
               let fs' := addToList 3 fs in
               constr:((os', fs'))) in
  (pose lk1 as f1).
  assert (f1 = (C, (1, ()), (3, ()), ())) by auto.
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
  let lk1 := addToObjList C cs1 1 in
  (pose lk1 as f1).
  assert (f1 = ((C, (1, ()), tt), ())) by auto.
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
  let lk1 := addToArrList C cs1 1 in
  (pose lk1 as f1).
  assert (f1 = ((C, tt, (1, ())), ())) by auto.
  exact I.
Qed.

Ltac lookupObj c cs o :=
  let res := catLists c cs in
  match res with
  | (?os, _) => lookup o os
  end.

Example test_lookupObj (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let cs2 := addToObjList C cs1 123 in
  let cs3 := addToObjList C cs2 456 in
  let cs4 := addToObjList C cs3 789 in
  let lk1 := lookupObj C cs4 456 in
  (pose lk1 as f1).
  assert (f1 = 1) by auto.
  exact I.
Qed.

Ltac lookupArr c cs f :=
  let res := catLists c cs in
  match res with
  | (_, ?fs) => lookup f fs
  end.

Example test_lookupArr (C D E : Category) : True.
Proof.
  let cs1 := addToCatList C tt in
  let cs2 := addToArrList C cs1 123 in
  let cs3 := addToArrList C cs2 456 in
  let cs4 := addToArrList C cs3 789 in
  let lk1 := lookupArr C cs4 456 in
  (pose lk1 as f1).
  assert (f1 = 1) by auto.
  exact I.
Qed.

(** Variable capture *)

Ltac allObjs c cs o :=
  lazymatch o with
  | ?x => addToObjList c cs x
  end.

Example test_allObjs (C : Category) (x y z w : C) : True.
Proof.
  let cs := addToCatList C tt in
  let v := allObjs C cs constr:(x) in
  pose v as p.
  assert (p = (C, (x, ()), (), ())) as H0 by auto.
  clear p H0.

  exact I.
Qed.

Ltac allVars cs e :=
  lazymatch e with
  | @id ?c ?o => let cs := addToCatList c cs in addToObjList c cs o

  | ?f ∘ ?g => let cs := allVars cs f in allVars cs g
  | ?X ≈ ?Y => let cs := allVars cs X in allVars cs Y
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
  (C : Category)
  (x y z : C)
  (f f' : y ~> z)
  (g g' : x ~> y) : True.
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

  exact I.
Qed.

(** Term capture *)

Ltac reifyObj cs o :=
  lazymatch o with
  | ?x =>
    lazymatch type of x with
    | @obj ?c =>
      lookupObj c cs x
    end
  end.

Example test_reifyObj (C : Category) (y z : C) (f : y ~> z) : True.
Proof.
  let v := allVars tt constr:(f) in
  let o := reifyObj v constr:(y) in
  pose v as pv;
  pose o as po.
  assert (pv = (C, (z, (y, ())), (f, ()), ())) as Hv by auto.
  assert (po = 1) as Ho by auto.
  clear pv po Hv Ho.

  exact I.
Qed.

Ltac reifyTerm cs t :=
  lazymatch t with
  | @id _ _ => constr:(@Ident)
  | @compose _ _ _ _ ?f ?g =>
    let ft := reifyTerm cs f in
    let gt := reifyTerm cs g in
    constr:(@Comp ft gt)
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let fn := lookupArr c cs f in
      constr:(@Morph fn)
    end
  end.

Example test_reifyTerm
  (C : Category)
  (x y z : C)
  (f f' : y ~> z)
  (g : x ~> y) : True.
Proof.
  let t := reifyTerm tt constr:(id[x]) in
  pose t as pt.
  assert (pt = Ident) as H0 by auto.
  clear pt H0.

  let v := allVars tt constr:(f) in
  let t := reifyTerm v constr:(f) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (z, (y, ())), (f, ()), ())) as Hv by auto.
  assert (pt = Morph 0) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(f ∘ g) in
  let t := reifyTerm v constr:(f ∘ g) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (x, (z, (y, ()))), (g, (f, ())), ())) as Hv by auto.
  assert (pt = Comp (Morph 1) (Morph 0)) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(f ∘ id) in
  let t := reifyTerm v constr:(f ∘ id) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (z, (y, ())), (f, ()), ())) as Hv by auto.
  assert (pt = Comp (Morph 0) Ident) as Ht by auto.
  clear pv pt Hv Ht.

  let v := allVars tt constr:(id ∘ f) in
  let t := reifyTerm v constr:(id ∘ f) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (y, (z, ())), (f, ()), ())) as Hv by auto.
  assert (pt = Comp Ident (Morph 0)) as Ht by auto.
  clear pv pt Hv Ht.

  exact I.
Qed.

Ltac reifyExpr cs t :=
  lazymatch t with
  | True  => constr:(@Top)
  | False => constr:(@Bottom)
  | ?F ≈ ?G =>
    let f := reifyTerm cs F in
    let g := reifyTerm cs G in
    lazymatch type of F with
    | ?x ~{?c}~> ?y =>
      let xn := reifyObj cs x in
      let yn := reifyObj cs y in
      constr:(@Equiv xn yn f g)
    end
  | ?P ∧ ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(@And p q)
  | ?P ∨ ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(@Or p q)
  | ?P → ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(@Impl p q)
  end.

Example test_reifyExpr
  (C : Category)
  (x y z : C)
  (f : y ~> z)
  (g : x ~> y) : True.
Proof.
  let t := reifyExpr tt constr:(True) in
  pose t as pt.
  assert (pt = Top) as H0 by auto.
  clear pt H0.

  let t := reifyExpr tt constr:(False) in
  pose t as pt.
  assert (pt = Bottom) as H0 by auto.
  clear pt H0.

  let v := allVars tt constr:(f ≈ f ∘ id) in
  let t := reifyExpr v constr:(f ≈ f ∘ id) in
  pose v as pv;
  pose t as pt.
  assert (pv = (C, (z, (y, ())), (f, ()), ())) as Hv by auto.
  assert (pt = Equiv 1 0 (Morph 0) (Comp (Morph 0) Ident))
    as Ht by auto.
  clear pv pt Hv Ht.

  let t := reifyExpr tt constr:(True ∧ True) in
  pose t as pt.
  assert (pt = And Top Top) as H0 by auto.
  clear pt H0.

  let t := reifyExpr tt constr:(True ∨ True) in
  pose t as pt.
  assert (pt = Or Top Top) as H0 by auto.
  clear pt H0.

  let t := reifyExpr tt constr:(True → True) in
  pose t as pt.
  assert (pt = Impl Top Top) as H0 by auto.
  clear pt H0.

  exact I.
Qed.

(** Build environment *)

Ltac foldr xs z f :=
  let rec go xs :=
    lazymatch xs with
    | tt => z
    | (?x, ?xs') =>
      let rest := go xs' in f x rest
    end in go xs.

Ltac toList A xs :=
  foldr xs (@nil A) ltac:(fun x xs => constr:(x :: xs)).

Example test_toList
  (C : Category)
  (x y z : C)
  (f : y ~> z) :
  True.
Proof.
  let v := toList C tt in
  pose v as pv.
  assert (pv = []) as H0 by auto.
  clear pv H0.

  let v := toList C (y, ()) in
  pose v as pv.
  assert (pv = [y]) as H0 by auto.
  clear pv H0.

  let v := toList C (z, (y, ())) in
  pose v as pv.
  assert (pv = [z; y]) as H0 by auto.
  clear pv H0.

  exact I.
Qed.

Ltac build_objs cs andThen :=
  match cs with
  | ((?c, (?o, ?os), ?fs), tt) =>
    match type of o with
    | @obj ?C =>
        andThen c o ltac:(toList C (o, os)) fs
    end
  | _ =>
    fail "Solver only works with a single category"
  end.

Ltac build_arrs c cs fs def_obj objs andThen :=
  andThen ltac:(
    foldr fs
      (inil (B:=arrD' def_obj objs))
      ltac:(fun f fs =>
        lazymatch type of f with
        | ?x ~{?c}~> ?y =>
          let xn := reifyObj cs x in
          let yn := reifyObj cs y in
          constr:(icons (B:=arrD' def_obj objs) (xn, yn) f fs)
        end)).

Ltac find_vars :=
  lazymatch goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    pose cs;
    build_objs cs ltac:(fun c def_obj objs fs =>
      pose objs;
      build_arrs c cs fs def_obj objs ltac:(fun arrs =>
        pose arrs))
  end.

Example ex_find_vars (C : Category) (x y : C) (f : x ~> y) (g : y ~> x) :
  g ≈ g → f ≈ f.
Proof.
  intros.
  find_vars.
  reflexivity.
Qed.

Ltac reify_terms_and_then tacGoal :=
  match goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    let g  := reifyExpr cs G in
    build_objs cs ltac:(fun c def_obj objs fs =>
      build_arrs c cs fs def_obj objs ltac:(fun arrs =>
        let objects :=
            constr:({|
              def_obj := def_obj;
              objs    := objs |}) in
        let arrows :=
            constr:({|
              has_objects := objects;
              tys  := ltac:(vm_compute arrs);
              arrs := arrs |}) in
        tacGoal arrows g))
  end.

Ltac reify := reify_terms_and_then ltac:(fun env g => pose env; pose g).

Ltac reify_and_change :=
  reify_terms_and_then ltac:(fun env g => change (@exprD _ env g)).

Example ex_reify_and_change
  (C : Category) (x y z w : C)
  (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z) :
  g ∘ h ≈ i ->
  f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  reify_and_change.
  vm_compute.
  cat; try apply comp_assoc.
Qed.
