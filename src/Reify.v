Set Warnings "-notation-overridden".

Require Import Solver.Logic.

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
  | (?os, _) => lookup o os
  end.

Ltac lookupArr c cs f :=
  let res := catLists c cs in
  match res with
  | (_, ?fs) =>
    let n := listSize fs in
    lookupFin n f fs
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
  | @id ?c ?x =>
    let xn := lookupObj c cs x in
    constr:(@Ident _ (@tys env) xn)
  | @compose ?c ?x ?y ?z ?f ?g =>
    let ft := reifyTerm env cs f in
    let gt := reifyTerm env cs g in
    let xn := lookupObj c cs x in
    let yn := lookupObj c cs y in
    let zn := lookupObj c cs z in
    constr:(@Comp _ (@tys env) xn yn zn ft gt)
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let fn := lookupArr c cs f in
      constr:(@Morph _ (@tys env) fn)
    end
  end.

Ltac reifyExpr env cs t :=
  lazymatch t with
  | True => constr:(@Top env)
  | False => constr:(@Bottom env)
  | ?F ≈ ?G =>
    let f := reifyTerm env cs F in
    let g := reifyTerm env cs G in
    lazymatch type of F with
    | ?x ~{?c}~> ?y =>
      let xn := lookupObj c cs x in
      let yn := lookupObj c cs y in
      constr:(@Equiv env xn yn f g)
    end
  | ?P ∧ ?Q =>
    let p := reifyExpr env cs P in
    let q := reifyExpr env cs Q in
    constr:(@And env p q)
  | ?P ∨ ?Q =>
    let p := reifyExpr env cs P in
    let q := reifyExpr env cs Q in
    constr:(@Or env p q)
  | ?P -> ?Q =>
    let p := reifyExpr env cs P in
    let q := reifyExpr env cs Q in
    constr:(@Impl env p q)
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

Ltac build_env cs :=
  foldri1 cs
    ltac:(fun cv =>
            constr:((Unused : Category,
                     (fun o : obj_idx => tt : Unused),
                     (inil (B:=@dep_arr Unused
                                 (fun _ : obj_idx => tt : Unused))))))
    ltac:(fun ci cv k =>
      match cv with
      | (?c, ?os, ?fs) =>
        let ofun := foldri1 os
          ltac:(fun ov => constr:(fun _ : obj_idx => ov))
          ltac:(fun oi ov ok =>
                  constr:(fun o => if (o =? oi)%positive
                                   then ov else ok o)) in
        let alist := foldr fs
          constr:((inil (B:=@dep_arr c ofun)))
          ltac:(fun f fs =>
                  lazymatch type of f with
                  | ?x ~{?c}~> ?y =>
                    let xn := lookupObj c cs x in
                    let yn := lookupObj c cs y in
                    constr:((icons (A:=obj_pair) (B:=@dep_arr c ofun)
                                   (xn, yn) f fs))
                  end) in
        constr:((c, ofun, alist))
      end).

Ltac find_vars :=
  lazymatch goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    pose cs;
    let ofun := build_env cs in
    pose ofun
  end.

Example sample_1 : ∀ (C : Category) (x y : C) (f : x ~> y) (g : y ~> x),
  g ≈ g -> f ≈ f.
Proof.
  intros.
  revert X; find_vars; compute [Pos.succ] in p0.
  reflexivity.
Qed.

Definition vec_size {A n} (l : Vector.t A n) : nat := n.

Ltac reify_terms_and_then tacGoal :=
  match goal with
  | [ |- ?G ] =>
    let cs  := allVars tt G in
    let env := build_env cs in
    match env with
    | (?c, ?ofun, ?alist) =>
      let env :=
          constr:({| cat := c
                   ; objs := ofun
                   ; num_arrs := vec_size (vec_of alist)
                   ; tys := vec_of alist
                   ; arrs := alist |}) in
      let g := reifyExpr env cs G in
      change (@exprD env g);
      cbv beta iota zeta delta [Pos.succ];
      tacGoal env g
    end
  end.

Ltac reify := reify_terms_and_then
  ltac:(fun env g => pose env; pose g).

Ltac categorical := reify_terms_and_then
  ltac:(fun env g => apply expr_sound; now vm_compute).

(*
Ltac normalize := reify_terms_and_then
  ltac:(fun env g => apply exprAD_sound; vm_compute).
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
    g ∘ h ≈ i ->
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  (* revert X. *)
  (* revert X0. *)
  (* revert X1. *)
  (* revert X2. *)
  (* revert X3. *)
  (* revert X4. *)
  (* revert X5. *)
  (* revert X6. *)
  (* revert X7. *)
  (* Time normalize.               (* 0.07s *) *)
  (* Undo. *)
  Time categorical.             (* 0.096s *)
Qed.

Print Assumptions sample_2.

Example sample_3 :
  ∀ (C : Category) (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z),
    g ∘ id ∘ id ∘ id ∘ h ≈ i ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ h ≈ i ->
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  revert X7.
  (* reify. *)
  (* red; intros. *)
  (* rewrite termD_arrows. *)
  (* simpl arrows. *)
  cat.
Qed.
