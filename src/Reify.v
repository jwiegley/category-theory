Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Expr.
Require Import Solver.Normal.
Require Import Solver.Denote.
Require Import Solver.Logic.

Generalizable All Variables.

Import ListNotations.

(** Lists in Ltac *)

Ltac addToList x xs :=
  let rec go ys :=
    lazymatch ys with
    | tt => constr:((x, xs))
    | (x, _) => xs
    | (_, ?ys') => go ys'
    end in
  go xs.

Ltac listSize xs :=
  lazymatch xs with
  | tt => constr:(0%nat)
  | (_, ?xs') =>
    let n := listSize xs' in
    constr:((S n)%nat)
  end.

Ltac lookup x xs :=
  lazymatch xs with
  | (x, _) => constr:(1%positive)
  | (_, ?xs') =>
    let xn := lookup x xs' in
    constr:(Pos.succ xn)
  end.

Ltac lookupCat c cs :=
  lazymatch cs with
  | ((c, _, _), _) => constr:(1%positive)
  | (_, ?cs') =>
    let cn := lookupCat c cs' in
    constr:(Pos.succ cn)
  end.

(** Lists of lists in Ltac *)

Ltac addToCatList c cs :=
  let rec go xs :=
    lazymatch xs with
    | tt => constr:(((c, tt, tt), cs))
    | ((c, _, _), _) => constr:(cs)
    | (_, ?xs') => go xs'
    end in
  go cs.

Ltac catLists c cs :=
  lazymatch cs with
  | ((c, ?os, ?fs), _) => constr:((os, fs))
  | (_, ?cs') => catLists c cs'
  end.

Ltac updateCat c cs os fs :=
  let rec go xs :=
    lazymatch xs with
    | ((c, _, _), ?xs') => constr:(((c, os, fs), xs'))
    | tt => constr:(tt)
    | (?x, ?xs') =>
      let xs' := go xs' in
      constr:((x, xs'))
    end in
  go cs.

Ltac addToObjList c cs o :=
  let res := catLists c cs in
  match res with
  | (?os, ?fs) =>
    let os' := addToList o os in
    updateCat c cs os' fs
  end.

Ltac addToArrList c cs f :=
  let res := catLists c cs in
  match res with
  | (?os, ?fs) =>
    let fs' := addToList f fs in
    updateCat c cs os fs'
  end.

Ltac lookupObj c cs o :=
  let res := catLists c cs in
  match res with
  | (?os, _) => lookup o os
  end.

Ltac lookupArr c cs f :=
  let res := catLists c cs in
  match res with
  | (_, ?fs) => lookup f fs
  end.

(** Variable capture *)

Ltac allVars cs e :=
  lazymatch e with
  | @id ?c ?o => let cs := addToCatList c cs in addToObjList c cs o
  | ?f ∘ ?g   => let cs := allVars cs f in allVars cs g
  | ?P -> ?Q  => let cs := allVars cs P in allVars cs Q
  | ?X ≈ ?Y   => let cs := allVars cs X in allVars cs Y
  | ?f => lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let cs := addToCatList c cs in
      let cs := addToObjList c cs x in
      let cs := addToObjList c cs y in
      addToArrList c cs f
    end
  end.

(** Term capture *)

Ltac reifyTerm cs t :=
  lazymatch t with
  | @id ?c ?x =>
    let cn := lookupCat c cs in
    let xn := lookupObj c cs x in
    constr:(Identity xn)
  | @compose ?c _ _ _ ?f ?g =>
    let cn := lookupCat c cs in
    let ft := reifyTerm cs f in
    let gt := reifyTerm cs g in
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let xn := lookupObj c cs x in
      constr:(Compose xn ft gt)
    end
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let cn := lookupCat c cs in
      let fn := lookupArr c cs f in
      let xn := lookupObj c cs x in
      let yn := lookupObj c cs y in
      constr:(Morph xn yn fn)
    end
  end.

Ltac reifyExpr cs t :=
  lazymatch t with
  | True => constr:(Top)
  | False => constr:(Bottom)
  | ?F ≈ ?G =>
    let f := reifyTerm cs F in
    let g := reifyTerm cs G in
    lazymatch type of F with
    | ?x ~{?c}~> ?y =>
      let xn := lookupObj c cs x in
      let yn := lookupObj c cs y in
      constr:(Equiv xn yn f g)
    end
  (* | ~ ?P => *)
  (*   let p := reifyTerm env P in *)
  (*   constr:(Not p) *)
  | ?P ∧ ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(And p q)
  | ?P ∨ ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(Or p q)
  | ?P -> ?Q =>
    let p := reifyExpr cs P in
    let q := reifyExpr cs Q in
    constr:(Impl p q)
  end.

(** Build environment *)

Ltac foldri xs z f :=
  let rec go n xs :=
    lazymatch xs with
    | (?x, tt) => let z' := z x in f n x z'
    | (?x, ?xs') =>
      let rest := go (Pos.succ n) xs' in
      let x'   := f n x rest in constr:(x')
    end in go 1%positive xs.

Ltac objects_function xs :=
  let rec loop o xs' :=
    lazymatch xs' with
    | (?x, tt) => constr:(fun (_ : obj_idx) => x)
    | (?x, ?xs'') =>
      let f := loop (Pos.succ o) xs'' in
      constr:(fun (o' : obj_idx) =>
                if (o =? o')%positive then x else f o')
    end in
  loop 1%positive xs.

Program Definition Unused : Category := {|
  obj     := unit : Type;
  hom     := fun _ _ => True;
  homset  := Morphism_equality;
  id      := fun x => _;
  compose := fun x y z f g => _
|}.
Next Obligation.
  unfold Unused_obligation_1.
  unfold Unused_obligation_2.
  now destruct f.
Defined.

Ltac build_env cs :=
  foldri cs
    ltac:(fun cv =>
            constr:((Unused : Category,
                     (fun o : obj_idx => tt : Unused),
                     (fun f : arr_idx => (tt, tt)),
                     (fun f : arr_idx => @None (() ~{Unused}~> ())))))
    ltac:(fun ci cv k =>
      match cv with
      | (?cat, ?os, ?fs) =>
        let ofun := foldri os
          ltac:(fun ov => constr:(fun _ : obj_idx => ov))
          ltac:(fun oi ov ok =>
                  constr:(fun o => if (o =? oi)%positive
                                   then ov else ok o)) in
        let xyfun := foldri fs
          ltac:(fun fv => match type of fv with
            | ?x ~{cat}~> ?y =>
              let xn := lookup x os in
              let yn := lookup y os in
              constr:(fun (_ : arr_idx) => (xn, yn))
            end)
          ltac:(fun fi fv fk => match type of fv with
            | ?x ~{cat}~> ?y =>
              let xn := lookup x os in
              let yn := lookup y os in
              constr:(fun (f : arr_idx) =>
                        if (f =? fi)%positive then (xn, yn) else fk f)
            end) in
        let ffun := foldri fs
          ltac:(fun fv => match type of fv with
            | ?x ~{cat}~> ?y =>
              constr:((fun (f : arr_idx) =>
                         @None (∃ x y, ofun x ~{cat}~> ofun y)))
            end)
          ltac:(fun fi fv fk => match type of fv with
            | ?x ~{cat}~> ?y =>
              let xn := lookup x os in
              let yn := lookup y os in
              constr:((fun (f : arr_idx) =>
                         if (f =? fi)%positive
                         then Some (xn; (yn; fv))
                         else fk f))
            end) in
        constr:((cat, ofun, xyfun, ffun))
      end).

Ltac find_vars :=
  lazymatch goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    pose cs;
    let env := build_env cs in
    pose env
  end.

Example sample_1 : ∀ (C : Category) (x y : C) (f : x ~> y) (g : y ~> x),
  g ≈ g -> f ≈ f.
Proof.
  intros.
  revert X; find_vars; compute [Pos.succ] in p0.
Abort.

Definition term_wrapper {A : Type} (x : A) : A := x.

Ltac reify_terms_and_then tacGoal :=
  match goal with
  | [ |- ?G ] =>
    let cs  := allVars tt G in
    let g   := reifyExpr cs G in
    let env := build_env cs in
    match env with
    | (?cat, ?ofun, ?xyfun, ?ffun) =>
      change (@exprD cat ofun ffun g);
      cbv beta iota zeta delta [Pos.succ];
      tacGoal env g
    end
  end.

Ltac reify := reify_terms_and_then
  ltac:(fun env g =>
          match env with
          | (?cat, ?ofun, ?xyfun, ?ffun) =>
            pose cat; pose ofun; pose xyfun; pose ffun; pose g
          end).

Ltac categorical :=
  reify_terms_and_then ltac:(fun env g => apply expr_sound; now vm_compute).

(*
Ltac normalize :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H =>
      match env with
      | (?cat, ?ofun, ?xyfun, ?ffun) =>
        let H1 := fresh "H" in
        assert (H1 : arrows_beq (arrows r1) (arrows r2) = true)
          by (vm_compute; reflexivity);
        (* If we reorganize the arguments and "apply .. in H", this operation is
           about 8% slower than if we pose it in the context and clear H. *)
        let N := fresh "N" in
        pose proof (normalize_denote_terms_impl cat ofun xyfun ffun
                      (TermDom xyfun r1) (TermCod xyfun r1) r1 r2 H1) as N;
        clear H H1;
        cbv beta iota zeta delta
          [ normalize normalize_denote normalize_denote_chain
            convert_arr arr_dom arr_cod fst snd Pos.succ app
            Pos.eq_dec positive_rec positive_rect Pos.eqb
            Eq_eq_dec Pos_Eq prod_rect
            ArrowList_append TermDom TermCod sumbool_rec sumbool_rect
            eq_rect eq_ind_r eq_ind eq_sym ] in N;
        red in N;
        rename N into H
      end)
    ltac:(fun env r1 r2 =>
      match env with
      | (?cat, ?ofun, ?xyfun, ?ffun) =>
        apply (normalize_denote_terms cat ofun xyfun ffun
                 (TermDom xyfun r1) (TermCod xyfun r1) r1 r2);
        [ vm_compute; reflexivity
        | vm_compute; reflexivity
        | vm_compute; reflexivity
        | vm_compute; reflexivity
        | idtac ]
      end);
  unfold term_wrapper in *; simpl in *.
*)

Example sample_2 :
  ∀ (C : Category) (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z),
    g ∘ id ∘ id ∘ id ∘ h ≈ i ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  Time categorical.
Qed.

Print Assumptions sample_2.
