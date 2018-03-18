Set Warnings "-notation-overridden".

Require Import Coq.PArith.PArith.
Require Import Coq.Vectors.Vector.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Env.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.

Generalizable All Variables.

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

Ltac lookupFin n x xs :=
  lazymatch n with
  | 0%nat => constr:(@Fin.F1 0%nat)
  | S ?n' =>
    lazymatch xs with
    | (x, _) => constr:(@Fin.F1 n')
    | (_, ?xs') =>
      let xn := lookupFin n' x xs' in
      constr:(Fin.FS xn)
    end
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
  | (?os, _) =>
    let n := listSize os in
    lookupFin n o os
  end.

Ltac lookupObjPos c cs o :=
  let res := catLists c cs in
  match res with
  | (?os, _) =>
    lookup o os
  end.

Ltac lookupArr c cs f :=
  let res := catLists c cs in
  match res with
  | (_, ?fs) =>
    let n := listSize fs in
    lookupFin n f fs
  end.

Ltac lookupArrPos c cs f :=
  let res := catLists c cs in
  match res with
  | (_, ?fs) =>
    lookup f fs
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

Ltac reifyTerm env cs t :=
  lazymatch t with
  (* | @id ?c ?x => *)
  | @id _ _ =>
    (* let xn := lookupObj c cs x in *)
    constr:(@SIdent)
  (* | @compose ?c ?x ?y ?z ?f ?g => *)
  | @compose _ _ _ _ ?f ?g =>
    let ft := reifyTerm env cs f in
    let gt := reifyTerm env cs g in
    (* let xn := lookupObj c cs x in *)
    (* let yn := lookupObj c cs y in *)
    (* let zn := lookupObj c cs z in *)
    constr:(@SComp ft gt)
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let fn := lookupArrPos c cs f in
      constr:(@SMorph fn)
    end
  end.

Ltac reifyExpr env cs t :=
  lazymatch t with
  | True => constr:(@STop)
  | False => constr:(@SBottom)
  | ?F ≈ ?G =>
    let f := reifyTerm env cs F in
    let g := reifyTerm env cs G in
    lazymatch type of F with
    | ?x ~{?c}~> ?y =>
      let xn := lookupObjPos c cs x in
      let yn := lookupObjPos c cs y in
      constr:(@SEquiv xn yn f g)
    end
  | ?P ∧ ?Q =>
    let p := reifyExpr env cs P in
    let q := reifyExpr env cs Q in
    constr:(@SAnd p q)
  | ?P ∨ ?Q =>
    let p := reifyExpr env cs P in
    let q := reifyExpr env cs Q in
    constr:(@SOr p q)
  | ?P -> ?Q =>
    let p := reifyExpr env cs P in
    let q := reifyExpr env cs Q in
    constr:(@SImpl p q)
  end.

(** Build environment *)

Program Definition Unused : Category := {|
  obj     := Datatypes.unit : Type;
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

Ltac foldr xs z f :=
  let rec go xs :=
    lazymatch xs with
    | tt => z
    | (?x, ?xs') =>
      let rest := go xs' in
      let x'   := f x rest in constr:(x')
    end in go xs.

Ltac foldri1 xs z f :=
  let rec go n xs :=
    lazymatch xs with
    | (?x, tt) => let z' := z x in f n x z'
    | (?x, ?xs') =>
      let rest := go (Pos.succ n) xs' in
      let x'   := f n x rest in constr:(x')
    end in go 1%positive xs.

Import VectorNotations.

Ltac build_objs cs andThen :=
  foldri1 cs
    ltac:(fun cv =>
      constr:((Unused : Category,
               (nil Unused),
               (inil (B:=dep_arr (nil Unused))))))
    ltac:(fun ci cv _k =>
      match cv with
      | (?c, ?os, ?fs) =>
        andThen c fs ltac:(foldr os
          constr:(nil c)
          ltac:(fun ov os => constr:(ov :: os)))
      end).

Ltac build_arrs c cs fs objs andThen :=
  andThen ltac:(foldr fs
    constr:(inil (B:=dep_arr objs))
    ltac:(fun f fs =>
            lazymatch type of f with
            | ?x ~{?c}~> ?y =>
              let xn := lookupObj c cs x in
              let yn := lookupObj c cs y in
              constr:(icons (B:=dep_arr objs) (xn, yn) f fs)
            end)).

Ltac find_vars :=
  lazymatch goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    pose cs;
    build_objs cs ltac:(fun c fs objs =>
      build_arrs c cs fs objs ltac:(fun arrs =>
        pose objs;
        pose arrs))
  end.

Example sample_1 : ∀ (C : Category) (x y : C) (f : x ~> y) (g : y ~> x),
  g ≈ g -> f ≈ f.
Proof.
  intros.
  Set Printing All.
  find_vars.
  Unset Printing All.
  reflexivity.
Qed.

Definition vec_size {A n} (l : Vector.t A n) : nat := n.

Ltac reify_terms_and_then tacGoal :=
  match goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    build_objs cs ltac:(fun c fs objs =>
      build_arrs c cs fs objs ltac:(fun arrs =>
        let env :=
            constr:({| cat := c
                     ; num_objs := ltac:(vm_compute (vec_size objs))
                     ; objs := objs
                     ; num_arrs := ltac:(vm_compute (vec_size (vec_of arrs)))
                     ; tys := ltac:(vm_compute (vec_of arrs))
                     ; arrs := arrs |}) in
        let g := reifyExpr env cs G in
        tacGoal env g))
  end.

Ltac reify := reify_terms_and_then ltac:(fun env g => pose env; pose g).

Ltac reify_and_change :=
  reify_terms_and_then ltac:(fun env g => change (@sexprD env g)).

Example sample_0 :
  ∀ (C : Category) (x y z w : C)
    (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z),
    g ∘ h ≈ i ->
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  reify_and_change.
  vm_compute.
  (* match goal with *)
  (* | [ |- @equiv _ (@homset _ _ _) ?X ?Y ] => idtac *)
  (* end. *)
  cat.
  apply comp_assoc.
Qed.
