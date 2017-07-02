Set Warnings "-notation-overridden".

Require Import Coq.NArith.NArith.
Require Import Coq.FSets.FMaps.

Require Import Category.Lib.
Require Import Category.Lib.Nomega.
Require Import Category.Lib.FMapExt.
Require Import Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Module PO := PairOrderedType N_as_OT N_as_OT.
Module M  := FMapList.Make(PO).
Module Import FMapExt := FMapExt PO M.

(* An arrows-only meta-category defines identity arrows as those which, when
   composed to the left or right of another arrow, result in that same arrow.
   This definition requires that all such composition be present. *)

Record Metacategory := {
  arrow := N;
  pairs : M.t arrow;

  composite (f g h : arrow) := M.find (f, g) pairs = Some h;
  defined (f g : arrow) := ∃ h, composite f g h;

  composite_defined {f g h : arrow} (H : composite f g h) :
    defined f g := (h; H);

  (*a ∀ edges (X, Y) and (Y, Z), ∃ an edge (X, Z) which is equal to the
     composition of those edges. *)
  composite_correct {f g h fg gh : arrow} :
    composite f g fg ->
    composite g h gh -> ∃ fgh, composite fg h fgh;

  composition_law {f g h fg gh : arrow} :
    composite f g fg ->
    composite g h gh ->
    ∀ fgh, composite fg h fgh ↔ composite f gh fgh;

  is_identity (u : arrow) :=
    (∀ f, defined f u -> composite f u f) ∧
    (∀ g, defined u g -> composite u g g);

  identity_law (x y f : arrow) : composite x y f ->
    ∃ u u', is_identity u -> is_identity u' ->
      composite f u f ∧ composite u' f f
}.

Section Category.

Context (M : Metacategory).

Record object := {
  obj_arr : arrow M;
  obj_def : composite M obj_arr obj_arr obj_arr;
  obj_id  : is_identity M obj_arr
}.

Record morphism (dom cod : object) := {
  mor_arr : arrow M;
  mor_dom : composite M mor_arr (obj_arr dom) mor_arr;
  mor_cod : composite M (obj_arr cod) mor_arr mor_arr
}.

Arguments mor_arr {_ _} _.
Arguments mor_dom {_ _} _.
Arguments mor_cod {_ _} _.

Definition identity (x : object) : morphism x x :=
  {| mor_arr := obj_arr x
   ; mor_dom := obj_def x
   ; mor_cod := obj_def x |}.

Lemma composition_left {x y z : object}
      {f : morphism y z} {g : morphism x y} {fg : arrow M} :
  composite M (mor_arr f) (mor_arr g) fg ->
  composite M (obj_arr z) (mor_arr f) (mor_arr f) ->
  composite M (obj_arr z) fg fg.
Proof.
  intros.
  destruct z, obj_id0, f, g; simpl in *.
  specialize (c0 _ (composite_defined M H0)); clear H0.
  destruct (composite_correct M c0 H).
  spose (fst (composition_law M c0 H _) e) as X.
  unfold composite, arrow in *.
  rewrite X, <- H, <- e; reflexivity.
Qed.

Lemma composition_right {x y z : object}
      {f : morphism y z} {g : morphism x y} {fg : arrow M} :
  composite M (mor_arr f) (mor_arr g) fg ->
  composite M (mor_arr g) (obj_arr x) (mor_arr g) ->
  composite M fg (obj_arr x) fg.
Proof.
  intros.
  destruct x, obj_id0, f, g; simpl in *.
  specialize (c _ (composite_defined M H0)); clear H0.
  destruct (composite_correct M H c).
  spose (fst (composition_law M H c _) e) as X.
  unfold composite, arrow in *.
  rewrite e, <- H, <- X; reflexivity.
Qed.

Definition composition {x y z : object}
           (f : morphism y z) (g : morphism x y) : morphism x z :=
  let fg := composite_correct M (mor_dom f) (mor_cod g) in
  {| mor_arr := `1 fg
   ; mor_dom   := composition_right (f:=f) (`2 fg) (mor_dom g)
   ; mor_cod   := composition_left  (g:=g) (`2 fg) (mor_cod f) |}.

Global Program Instance morphism_preorder : PreOrder morphism := {
  PreOrder_Reflexive  := identity;
  PreOrder_Transitive := fun _ _ _ g f => composition f g
}.

Global Program Instance morphism_setoid (x y : object) :
  Setoid (morphism x y) := {
  equiv := fun f g => mor_arr f = mor_arr g
}.

Lemma composition_respects {x y z : object} :
  Proper (equiv ==> equiv ==> equiv) (@composition x y z).
Proof.
  proper.
  destruct x0, y0, x1, y1; simpl in *; subst.
  repeat destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite e in e0.
  inversion_clear e0.
  reflexivity.
Qed.

Lemma composition_identity_left {x y : object} (f : morphism x y) :
  composition (identity y) f ≈ f.
Proof.
  destruct f; simpl.
  destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite mor_cod0 in e.
  inversion_clear e.
  reflexivity.
Qed.

Lemma composition_identity_right {x y : object} (f : morphism x y) :
  composition f (identity x) ≈ f.
Proof.
  destruct f; simpl.
  destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite mor_dom0 in e.
  inversion_clear e.
  reflexivity.
Qed.

Lemma composition_associative {x y z w : object}
      (f : morphism z w) (g : morphism y z) (h : morphism x y) :
  composition f (composition g h) ≈ composition (composition f g) h.
Proof.
  destruct f, g, h; simpl.
  repeat destruct (composite_correct _ _ _); simpl in *.
  spose (fst (composition_law M e1 e x3) e2) as X1.
  unfold composite, arrow in *.
  rewrite e0 in X1.
  inversion_clear X1.
  reflexivity.
Qed.

(* Every meta-category, defined wholly in terms of the axioms of category
   theory, gives rise to a category interpreted in the context of set
   theory. *)

Program Definition Category_from_Metacategory : Category := {|
  obj     := object;
  hom     := morphism;
  homset  := fun _ _ => {| equiv := fun f g => mor_arr f = mor_arr g |};
  id      := @identity;
  compose := @composition;

  compose_respects := @composition_respects;

  id_left    := @composition_identity_left;
  id_right   := @composition_identity_right;
  comp_assoc := @composition_associative;
  comp_assoc_sym := fun x y z w f g h =>
    symmetry (@composition_associative x y z w f g h);
|}.

End Category.

Arguments mor_arr _ {_ _} _.
Arguments mor_dom _ {_ _} _.
Arguments mor_cod _ {_ _} _.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, y at level 100, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Lemma mapsto_inv : ∀ elt f g (fg : elt) x y z m,
  M.MapsTo (f, g) fg (M.add (x, y) z m) ->
    (x = f ∧ y = g ∧ z = fg) ∨ M.MapsTo (f, g) fg m.
Proof.
  intros.
  apply add_mapsto_iffT in H.
  destruct H; simpl in *; intuition.
Defined.

Lemma find_inv : ∀ f g (fg : N) x y z m,
  M.find (f, g) (M.add (x, y) z m) = Some fg ->
    (x = f ∧ y = g ∧ z = fg) ∨ M.find (f, g) m = Some fg.
Proof.
  intros.
  destruct (N.eq_dec x f).
    destruct (N.eq_dec y g).
      destruct (N.eq_dec z fg).
        subst; left; intuition.
      contradiction n.
      rewrite F.add_eq_o in H.
        inversion_clear H.
        reflexivity.
      simpl; intuition.
    rewrite F.add_neq_o in H; intuition.
  rewrite F.add_neq_o in H; intuition.
Defined.

Global Program Instance sigT_proper {A : Type} :
  Proper (pointwise_relation A Basics.arrow ==> Basics.arrow) (@sigT A).
Next Obligation.
  proper.
  destruct X0.
  apply X in x1.
  exists x0.
  assumption.
Defined.

Lemma find_mapsto_iff_ex {elt k m} :
  (∃ v : elt, M.MapsTo (elt:=elt) k v m) ->
  (∃ v : elt, M.find (elt:=elt) k m = Some v).
Proof.
  apply sigT_proper.
  intros ??.
  apply F.find_mapsto_iff.
  assumption.
Defined.

Ltac destruct_maps :=
  repeat match goal with
  | [ H : M.find (?X, ?Y) (M.empty _) = Some ?F |- _ ] =>
    inversion H
  | [ H : M.find (?X, ?Y) (M.add _ _ _) = Some ?F |- _ ] =>
    apply find_inv in H;
    (destruct H as [[? [? ?]]|]; [subst; try nomega|])
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    vm_compute; eexists; reflexivity

  | [ H : M.find _ _ = Some _ |- _ ] =>
    apply F.find_mapsto_iff in H
  | [ |- M.find _ _ = Some _ ] =>
    apply F.find_mapsto_iff
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    apply find_mapsto_iff_ex

  | [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
    contradiction (proj1 (F.empty_mapsto_iff _ _) H)

  | [ H : M.MapsTo (?X, ?Y) ?F (M.add _ _ _) |- _ ] =>
    apply mapsto_inv in H; destruct H as [[? [? ?]]|]

  | [ H : ?X = ?Y |- context[M.MapsTo (?Y, _)] ] =>
    rewrite <- H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo (_, ?Y)] ] =>
    rewrite <- H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo _ ?Y] ] =>
    rewrite <- H; cbn

  | [ |- ∃ _, M.MapsTo (?X, ?Y) _ _ ] =>
    match goal with
      [ |- context[M.add (X, Y) ?F _ ] ] =>
      exists F
    end
  | [ |- M.MapsTo (?X, ?Y) ?F (M.add (?X, ?Y) ?F _) ] =>
    simplify_maps
  | [ |- M.MapsTo _ _ (M.add _ _ _) ] =>
    simplify_maps; right; split; [idtac|]
  end;
  try congruence.

Local Obligation Tactic := simpl; intros.

Ltac elimobj X :=
  elimtype False;
  unfold composite in X; simpl in X;
  clear -X;
  destruct_maps; nomega.

Lemma peano_rect' : ∀ P : N → Type, P 0%N → (∀ n : N, P (N.succ n)) → ∀ n : N, P n.
Proof.
  intros.
  induction n using N.peano_rect.
    apply X.
  apply X0.
Defined.

(*
Ltac reflect_on_maps :=
  try split; intros; simpl in *; destruct_maps; subst;
  first [ nomega
        | repeat eexists; clear;
          first [ instantiate (1 := 0%N); vm_compute; reflexivity
                | instantiate (1 := 1%N); vm_compute; reflexivity
                | instantiate (1 := 2%N); vm_compute; reflexivity
                | instantiate (1 := 3%N); vm_compute; reflexivity
                | instantiate (1 := 4%N); vm_compute; reflexivity
                | instantiate (1 := 5%N); vm_compute; reflexivity] ].
*)

(* Local Obligation Tactic := reflect_on_maps. *)

Inductive term :=
  | Var : positive -> term
  | Value : N -> term.

Definition term_beq (x y : term) : bool :=
  match x, y with
  | Var x, Var y => (x =? y)%positive
  | Value x, Value y => (x =? y)%N
  | _, _ => false
  end.

Lemma term_beq_sound x y : term_beq x y = true -> x = y.
Proof.
  induction x, y; simpl; intros; intuition.
  - apply Pos.eqb_eq in H; subst; reflexivity.
  - apply N.eqb_eq in H; subst; reflexivity.
Defined.

Program Definition term_eq_dec (x y : term) : {x = y} + {x ≠ y} :=
  match x, y with
  | Var x,   Var y   => if Pos.eq_dec x y then left _ else right _
  | Value x, Value y => if N.eq_dec   x y then left _ else right _
  | _, _ => right _
  end.
Next Obligation. congruence. Defined.
Next Obligation. congruence. Defined.
Next Obligation. congruence. Defined.
Next Obligation. congruence. Defined.
Next Obligation.
  destruct H.
  destruct x, y, wildcard', wildcard'0; try discriminate.
    specialize (H0 p1 p2).
    intuition.
  specialize (H n1 n2).
  intuition.
Defined.
Next Obligation.
  split; intros;
  unfold not; intros;
  destruct H1;
  discriminate.
Defined.
Next Obligation.
  split; intros;
  unfold not; intros;
  destruct H1;
  discriminate.
Defined.

Section denotation.

Definition subst_term (p : positive) (n : term) (t : term) : term :=
  match t with
  | Var x   => if (x =? p)%positive then n else t
  | Value _ => t
  end.

Fixpoint subst_term_all (xs : list (positive * term)) t : term :=
  match xs with
  | nil => t
  | cons (p, n) xs => subst_term p n (subst_term_all xs t)
  end.

Definition term_denote (vars : positive -> N) (x : term) : N :=
  match x with
  | Var n => vars n
  | Value n => n
  end.

Inductive map_expr : Set :=
  | Empty : map_expr
  | Add   : term -> term -> term -> map_expr -> map_expr.

Fixpoint subst_map_expr (p : positive) (n : term) (t : map_expr) : map_expr :=
  match t with
  | Empty => Empty
  | Add x y f m => Add (subst_term p n x) (subst_term p n y)
                       (subst_term p n f) (subst_map_expr p n m)
  end.

Fixpoint subst_map_expr_all (xs : list (positive * term)) t : map_expr :=
  match xs with
  | nil => t
  | cons (p, n) xs => subst_map_expr p n (subst_map_expr_all xs t)
  end.

Fixpoint map_expr_denote (vars : positive -> N) (m : map_expr) : M.t N :=
  match m with
  | Empty => M.empty N
  | Add x y f m' => M.add (term_denote vars x, term_denote vars y)
                          (term_denote vars f) (map_expr_denote vars m')
  end.

Inductive formula :=
  | Maps    : term -> term -> term -> map_expr -> formula
  | MapsAny : term -> term -> map_expr -> formula
  | Impl    : formula -> formula -> formula.

Fixpoint subst_formula (p : positive) (n : term) (t : formula) : formula :=
  match t with
  | Maps x y f m => Maps (subst_term p n x) (subst_term p n y)
                         (subst_term p n f) (subst_map_expr p n m)
  | MapsAny x y m => MapsAny (subst_term p n x) (subst_term p n y)
                             (subst_map_expr p n m)
  | Impl a b => Impl a (subst_formula p n b)
  end.

Fixpoint subst_formula_all (xs : list (positive * term)) t : formula :=
  match xs with
  | nil => t
  | cons (p, n) xs => subst_formula p n (subst_formula_all xs t)
  end.

Fixpoint formula_denote (vars : positive -> N) (t : formula) : Prop :=
  match t with
  | Maps x y f m =>
    M.MapsTo (term_denote vars x, term_denote vars y) (term_denote vars f)
             (map_expr_denote vars m)
  | MapsAny x y m =>
    M.In (term_denote vars x, term_denote vars y) (map_expr_denote vars m)
  | Impl p q => formula_denote vars p -> formula_denote vars q
  end.

Inductive subterm : formula -> formula -> Prop :=
  | Impl1 : forall t1 t2, subterm t1 (Impl t1 t2)
  | Impl2 : forall t1 t2, subterm t2 (Impl t1 t2).

Lemma subterm_wf : well_founded subterm.
Proof.
  constructor; intros.
  inversion H; subst; simpl in *;
  induction y;
  induction t1 || induction t2;
  simpl in *;
  constructor; intros;
  inversion H0; subst; clear H0;
  try (apply IHy1; constructor);
  try (apply IHy2; constructor).
Defined.

Section partial.
  Variable P : Prop.

  Inductive partial : Set :=
  | Proved : P -> partial
  | Uncertain : partial.
End partial.

Notation "[ P ]" := (partial P) : type_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Local Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "'Reduce' [ T ] v" := (if v then Proved T _ else Uncertain T)
  (at level 100) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x ||[ T ] y" := (if x then Proved T _ else Reduce[T] y) (at level 100) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.
Notation "x &&[ T ] y" := (if x then Reduce[T] y else Uncertain T) (at level 100) : partial_scope.

Local Open Scope lazy_bool_scope.

Fixpoint map_contains (x y : term) (m : map_expr) : option term :=
  match m with
  | Empty => None
  | Add x' y' f' m' =>
    match term_eq_dec x x' with
    | left _ =>
      match term_eq_dec y y' with
      | left _  => Some f'
      | right _ => map_contains x y m'
      end
    | right _ => map_contains x y m'
    end
  end.

Local Obligation Tactic := program_simpl.

Lemma no_subst_term vars p x t :
  term_denote vars x = vars p
    -> term_denote vars (subst_term p x t) = term_denote vars t.
Proof.
  generalize dependent p.
  induction t; simpl; intros; auto.
  - destruct (Pos.eq_dec p p0); subst.
      rewrite Pos.eqb_refl; auto.
    apply Pos.eqb_neq in n; rewrite n; auto.
Qed.

Lemma no_subst_map_expr vars p x t :
  term_denote vars x = vars p
    -> map_expr_denote vars (subst_map_expr p x t) = map_expr_denote vars t.
Proof.
  generalize dependent p.
  induction t; simpl; intros; auto.
  - rewrite IHt, !no_subst_term; auto.
Qed.

Lemma no_subst_formula vars p x t :
  term_denote vars x = vars p
    -> formula_denote vars (subst_formula p x t) = formula_denote vars t.
Proof.
  generalize dependent p.
  induction t; simpl; intros; auto.
  - rewrite !no_subst_term, !no_subst_map_expr; auto.
  - rewrite !no_subst_term, !no_subst_map_expr; auto.
  -intuition.
   rewrite IHt2; auto.
Qed.

Lemma subst_map_expr_all_Empty defs :
  subst_map_expr_all defs Empty = Empty.
Proof.
  induction defs; simpl; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_map_expr_all_Add defs x y f m :
  subst_map_expr_all defs (Add x y f m) =
  Add (subst_term_all defs x) (subst_term_all defs y)
      (subst_term_all defs f) (subst_map_expr_all defs m).
Proof.
  induction defs; simpl; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_formula_all_Maps defs x y f m :
  subst_formula_all defs (Maps x y f m) =
  Maps (subst_term_all defs x) (subst_term_all defs y)
       (subst_term_all defs f) (subst_map_expr_all defs m).
Proof.
  induction defs; simpl; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_formula_all_MapsAny defs x y m :
  subst_formula_all defs (MapsAny x y m) =
  MapsAny (subst_term_all defs x) (subst_term_all defs y)
          (subst_map_expr_all defs m).
Proof.
  induction defs; simpl; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_formula_all_Impl defs p q :
  subst_formula_all defs (Impl p q) = Impl p (subst_formula_all defs q).
Proof.
  induction defs; simpl; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Defined.

Definition check_def (defs : list (positive * term)) (t v : term) : bool :=
  match t with
  | Var t =>
    let fix check xs v v' :=
        match xs return bool with
        | nil => true
        | cons (x, x') xs =>
          match Pos.eq_dec v x with
          | left _ =>
            match term_eq_dec v' x' with
            | left _  => true
            | right _ => false
            end
          | right _ => check xs v v'
          end
        end in
    check defs t v
  | _ => true
  end.

(* The only job of formula_forward at the moment is to accumulate variable
   definitions. *)
Program Definition formula_forward (t : formula)
        (vars : positive -> N) (defs : list (positive * term))
        (hyp : formula)
        (cont : ∀ vars' defs', [formula_denote vars' (subst_formula_all defs' t)]) :
  [formula_denote vars hyp -> formula_denote vars (subst_formula_all defs t)] :=
  let mk v v' xs :=
      match v return list (positive * term) with
      | Var v => cons (v, v') xs
      | _ => xs
      end in
  match hyp with
  | Maps x y f m =>
    let fix go n : [formula_denote vars (Maps x y f n)
                      -> formula_denote vars (subst_formula_all defs t)] :=
        match n with
        | Empty => Yes
        | Add x' y' f' m' =>
          match check_def defs x x' with | true =>
          match check_def defs y y' with | true =>
          match check_def defs f f' with | true =>
            cont vars (mk x x' (mk y y' (mk f f' defs))) && go m'
          | false => Reduce (go m') end
          | false => Reduce (go m') end
          | false => Reduce (go m') end
        end in go m
  | MapsAny x y m =>
    let fix go n : [formula_denote vars (MapsAny x y n)
                      -> formula_denote vars (subst_formula_all defs t)] :=
        match n with
        | Empty => Yes
        | Add x' y' f' m' =>
          match check_def defs x x' with | true =>
          match check_def defs y y' with | true =>
            cont vars (mk x x' (mk y y' defs)) && go m'
          | false => Reduce (go m') end
          | false => Reduce (go m') end
        end in go m
  | Impl _ _ => Reduce (cont vars defs)
  end.
Next Obligation.
  simplify_maps.
  clear go cont.
  destruct H2.
  simpl in *.
  destruct x, y, f; simpl in *;
  repeat (rewrite no_subst_formula in H; auto); auto.
Defined.
Next Obligation.
  simplify_maps.
  clear go cont.
  destruct H1.
  simpl in *.
  destruct x, y, f; simpl in *;
  repeat (rewrite no_subst_formula in H; auto); auto.
Admitted.
Next Obligation.
  simplify_maps.
  clear go cont.
  destruct H1.
  simpl in *.
  destruct x, y, f; simpl in *;
  repeat (rewrite no_subst_formula in H; auto); auto.
Admitted.
Next Obligation.
  simplify_maps.
  clear go cont.
  destruct H1.
  simpl in *.
  destruct x, y, f; simpl in *;
  repeat (rewrite no_subst_formula in H; auto); auto.
Admitted.
Next Obligation.
  apply F.empty_in_iff in H.
  contradiction.
Defined.
Next Obligation.
  simpl in H1.
  apply F.add_in_iff in H1.
  destruct H1; auto.
  clear H0 go cont.
  destruct H1.
  simpl in *.
  destruct x, y; simpl in *;
  repeat (rewrite no_subst_formula in H; auto); auto.
Defined.
Next Obligation.
  apply F.add_in_iff in H0.
  destruct H0; auto.
  clear H go cont.
  destruct H0.
  simpl in *.
Admitted.
Next Obligation.
  apply F.add_in_iff in H0.
  destruct H0; auto.
  clear H go cont.
  destruct H0.
  simpl in *.
Admitted.

Lemma map_contains_MapsTo vars x y f m :
  Some f = map_contains x y m ->
  M.MapsTo (term_denote vars x, term_denote vars y)
           (term_denote vars f) (map_expr_denote vars m).
Proof.
  intros.
  apply F.find_mapsto_iff.
  induction m; simpl; intros.
    discriminate.
  simpl in *.
  destruct (term_eq_dec x t); subst.
    destruct (term_eq_dec y t0); subst.
      inversion H; subst.
      simplify_maps.
    rewrite F.add_neq_o; auto; simpl.
    admit.
  rewrite F.add_neq_o; auto; simpl.
  admit.
Admitted.

Lemma subst_formula_all_Impl_impl {defs p q t} :
  Impl p q = subst_formula_all defs t ->
    ∃ q', Impl p q' = t ∧ q = subst_formula_all defs q'.
Proof.
  intros.
  induction t.
  - induction defs; simpl in *.
      discriminate.
    destruct a.
    rewrite subst_formula_all_Maps in H; simpl in H.
    discriminate.
  - induction defs; simpl in *.
      discriminate.
    destruct a.
    rewrite subst_formula_all_MapsAny in H; simpl in H.
    discriminate.
  - rewrite subst_formula_all_Impl in H; simpl in H.
    inversion H; subst.
    eexists.
    split; reflexivity.
Qed.

Lemma formula_denote_Impl_forward {vars defs p q} :
  [formula_denote vars p → formula_denote vars (subst_formula_all defs q)]
    -> [formula_denote vars (Impl p q)].
Proof.
  intros.
  simpl in *.
Abort.

Lemma subterm_subst_formula_all defs p x :
  subterm x (Impl p x) ->
  subterm (subst_formula_all defs x) (Impl p x).
Proof.
Abort.

Program Fixpoint formula_backward (t : formula)
        (vars : positive -> N) (defs : list (positive * term))
        {wf subterm t} : [formula_denote vars (subst_formula_all defs t)] :=
  match t with
  | Maps x y f m =>
    match map_contains (subst_term_all defs x) (subst_term_all defs y)
                       (subst_map_expr_all defs m) with
    | Some f' => Reduce (term_eq_dec f' (subst_term_all defs f))
    | None => No
    end
  | MapsAny x y m =>
    match map_contains (subst_term_all defs x) (subst_term_all defs y)
                       (subst_map_expr_all defs m) with
    | Some _ => Yes
    | None => No
    end
  | Impl p q =>
    _ (formula_forward q vars defs p
                       (fun vars' defs' => formula_backward q vars' defs'))
  end.
Next Obligation.
  rewrite subst_formula_all_Maps; simpl.
  apply map_contains_MapsTo; auto.
Defined.
Next Obligation.
  rewrite subst_formula_all_MapsAny; simpl.
  apply in_mapsto_iff.
  eexists.
  apply map_contains_MapsTo; auto.
  apply Heq_anonymous.
Defined.
Next Obligation.
  rewrite subst_formula_all_Impl; auto.
Defined.
Next Obligation.
  destruct q; constructor.
Defined.
Next Obligation. apply measure_wf, subterm_wf. Defined.

Goal
  if formula_backward
       (Impl (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Value 1%N) Empty))
             (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Value 1%N) Empty)))
       (fun v => 9%N) nil then True else False.
Proof.
  vm_compute.
  constructor.
Qed.

Definition formula_tauto : forall (vars : positive -> N) (t : formula),
  [formula_denote vars t].
Proof.
  intros; refine (Reduce (formula_backward t vars nil)); auto.
Defined.

Require Import Coq.quote.Quote.

Definition partialOut (P : Prop) (x : [P]) :=
  match x return (match x with
                  | Proved _ _ => P
                  | Uncertain _ => True
                  end) with
  | Proved _ pf => pf
  | Uncertain _ => I
  end.

Ltac inList x xs :=
  match xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => constr:(1%positive)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(Pos.succ n)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    lazymatch xs' with
    | (?x, tt) => constr:(fun _ : positive => x)
    | (?x, ?xs'') =>
      let f := loop (Pos.succ n) xs'' in
      constr:(fun m : positive => if (m =? n)%positive then x else f m)
    end in
  loop (1%positive) xs.

Ltac allVar xs e :=
  match e with
  | N0 => xs
  | Npos _ => xs
  | ?x => addToList x xs
  end.

Ltac allVars xs e :=
  match e with
  | M.MapsTo (?X, ?Y) ?F _ =>
    let xs := allVar xs X in
    let xs := allVar xs Y in
    allVar xs F
  | M.In (?X, ?Y) _ =>
    let xs := allVar xs X in
    allVar xs Y
  | ?P -> ?Q =>
    let xs := allVars xs P in
    allVars xs Q
  | _ => xs
  end.

Ltac reifyValue env t :=
  match t with
  | N0 => constr:(Value N0)
  | Npos ?X =>
    constr:(Value (Npos X))
  | ?X =>
    let v := lookup X env in
    constr:(Var v)
  end.

Ltac reifyMapTerm env t :=
  match t with
  | M.empty _ => constr:(Empty)
  | M.add (?X, ?Y) ?F ?M =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    let f := reifyValue env F in
    let m := reifyMapTerm env M in
    constr:(Add x y f m)
  end.

Ltac reifyTerm env t :=
  match t with
  | M.MapsTo (?X, ?Y) ?F ?M =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    let f := reifyValue env F in
    let m := reifyMapTerm env M in
    constr:(Maps x y f m)
  | M.In (?X, ?Y) ?M =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    let m := reifyMapTerm env M in
    constr:(MapsAny x y m)
  | ?P -> ?Q =>
    let p := reifyTerm env P in
    let q := reifyTerm env Q in
    constr:(Impl p q)
  end.

Ltac reify' :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    pose xs;
    pose env;
    pose r1
  end.

Ltac reify :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    pose xs;
    pose env;
    pose r1;
    change (formula_denote env r1)
  end.

Lemma formula_sound vars t :
  (if formula_tauto vars t then True else False) -> formula_denote vars t.
Proof.
  unfold formula_tauto.
  destruct t; simpl; intros.
  - induction m; simpl in *.
      contradiction.
    destruct (formula_backward (Maps _ _ _ (Add _ _ _ m)) vars []) eqn:?; auto.
    contradiction.
  - induction m; simpl in *.
      contradiction.
    destruct (formula_backward (MapsAny _ _ (Add _ _ _ m)) vars []) eqn:?; auto.
    contradiction.
  - destruct (formula_backward (Impl _ _) vars []) eqn:?; auto.
    contradiction.
Qed.

Ltac solve_map := reify; apply formula_sound; vm_compute; auto.

Example map_decide_test  x y f :
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))) ->
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))).
Proof. solve_map. Qed.

Time Program Definition Zero : Metacategory := {|
  pairs := [map]
|}.

Ltac prepare_maps :=
  repeat lazymatch goal with
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    apply find_mapsto_iff_ex, in_mapsto_iffT
  | [ |- M.find _ _ = Some _ ] =>
    apply F.find_mapsto_iff
  | [ H : M.find _ (M.empty _) = Some _ |- _ ] => inversion H
  | [ H : M.find _ _ = Some ?F |- _ ] =>
    apply F.find_mapsto_iff in H; revert H
  | [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
    contradiction (proj1 (F.empty_mapsto_iff _ _) H)
  end.

Ltac map_decide := prepare_maps; solve_map.

Local Obligation Tactic :=
  repeat eexists; simpl; try split; intros;
  first [ map_decide
        | instantiate (1:=0%N); map_decide
        | instantiate (1:=1%N); map_decide
        | instantiate (1:=2%N); map_decide
        | instantiate (1:=3%N); map_decide
        | instantiate (1:=4%N); map_decide
        | instantiate (1:=5%N); map_decide ].

Time Program Definition One : Metacategory := {|
  pairs := [map (0, 0) +=> 0 ]%N
|}.

Local Obligation Tactic := simpl; intros.

Time Program Definition Two : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1

           ;    (2, 0) +=> 2
           ;    (1, 2) +=> 2 ]%N
|}.
Next Obligation.
  prepare_maps.
  reify.
  compute [Pos.succ] in *.
  apply formula_sound.
  vm_compute.
  simpl.

Time Program Definition Three : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (2, 2) +=> 2

           ;    (3, 0) +=> 3
           ;    (1, 3) +=> 3

           ;    (4, 1) +=> 4
           ;    (2, 4) +=> 4

           ;    (5, 0) +=> 5
           ;    (2, 5) +=> 5
           ;    (4, 3) +=> 5 ]%N
|}.

Time Program Definition Four : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (2, 2) +=> 2
           ;    (3, 3) +=> 3

           ;    (4, 0) +=> 4
           ;    (1, 4) +=> 4

           ;    (5, 1) +=> 5
           ;    (2, 5) +=> 5

           ;    (6, 2) +=> 6
           ;    (3, 6) +=> 6

           ;    (7, 0) +=> 7
           ;    (2, 7) +=> 7

           ;    (8, 1) +=> 8
           ;    (3, 8) +=> 8

           ;    (9, 0) +=> 9
           ;    (3, 9) +=> 9

           ;    (5, 4) +=> 7
           ;    (6, 5) +=> 8
           ;    (7, 6) +=> 9
           ;    (8, 4) +=> 9 ]%N
|}.

Ltac reflect_on_pairs X Y F D C :=
  repeat (
    destruct X using peano_rect';
    first
      [ elimobj D | elimobj C
      | repeat (
          destruct Y using peano_rect';
          first
            [ elimobj D | elimobj C
            | repeat (
                destruct F using peano_rect';
                first
                  [ elimobj D | elimobj C
                  | intuition idtac
                  | reflect_on_pairs ]) ]) ]);
  intuition.

Require Import Category.Instance.Two.

Monomorphic Lemma object_Two_rect :
  ∀ (P : object Two -> Type),
  (∀ x, obj_arr Two x = 0%N -> P x) ->
  (∀ x, obj_arr Two x = 1%N -> P x) ->
  ∀ (x : object Two), P x.
Proof.
  intros; destruct x.
  repeat (destruct obj_arr0 using peano_rect'; elimobj obj_def0 || auto).
Defined.

Program Definition Two_2_object (x : object Two) : TwoObj.
Proof.
  induction x using object_Two_rect.
  - exact TwoX.
  - exact TwoY.
Defined.

Monomorphic Lemma morphism_Two_rect :
  ∀ {x y : object Two} (P : morphism Two x y -> Type),
  (∀ f, obj_arr Two x = 0%N -> obj_arr Two y = 0%N -> mor_arr Two f = 0%N -> P f) ->
  (∀ f, obj_arr Two x = 1%N -> obj_arr Two y = 1%N -> mor_arr Two f = 1%N -> P f) ->
  (∀ f, obj_arr Two x = 0%N -> obj_arr Two y = 1%N -> mor_arr Two f = 2%N -> P f) ->
  ∀ (f : morphism Two x y), P f.
Proof.
  intros; destruct x, y, f.
  reflect_on_pairs obj_arr0 obj_arr1 mor_arr0 mor_dom0 mor_cod0.
Defined.

Program Definition Two_2_morphism (x y : object Two) (f : morphism Two x y) :
  TwoHom (Two_2_object x) (Two_2_object y).
Proof.
  induction f using morphism_Two_rect;
  destruct x, y, f; simpl in *; subst; simpl.
  - exact TwoIdX.
  - exact TwoIdY.
  - exact TwoXY.
Defined.

Local Obligation Tactic := intros.

Program Definition Two_to_Two : Category_from_Metacategory Two ⟶ _2 := {|
  fobj := Two_2_object;
  fmap := Two_2_morphism
|}.
Next Obligation.
  proper.
  destruct x0, y0; simpl in X; subst.
  apply f_equal.
  apply f_equal2;
  apply Eqdep_dec.UIP_dec;
  decide equality;
  apply N.eq_dec.
Qed.
Next Obligation.
  simpl.
  induction x using object_Two_rect;
  destruct x;
  simpl in H; subst;
  vm_compute; reflexivity.
Qed.
Next Obligation.
  simpl in *.
  induction f using morphism_Two_rect;
  induction g using morphism_Two_rect;
  destruct x, y, z, f, f0;
  simpl in H, H0, H1, H2, H3, H4; subst;
  (elimtype False; simpl in *; discriminate)
    || (vm_compute; reflexivity).
Qed.

Local Obligation Tactic :=
  program_simpl;
  try solve [ subst; unfold composite; simpl;
              subst; vm_compute; reflexivity ].

Program Definition _2_Two_object (x : TwoObj) : object Two :=
  match x with
  | TwoX => {| obj_arr := 0%N; obj_def := _; obj_id  := _ |}
  | TwoY => {| obj_arr := 1%N; obj_def := _; obj_id  := _ |}
  end.
Next Obligation.
  unfold is_identity, defined, composite;
  simpl; split; intros; destruct H; subst;
  rewrite e; destruct_maps.
Defined.
Next Obligation.
  unfold is_identity, defined, composite;
  simpl; split; intros; destruct H; subst;
  rewrite e; destruct_maps.
Defined.

Program Definition _2_Two_morphism (x y : TwoObj) (f : TwoHom x y) :
  morphism Two (_2_Two_object x) (_2_Two_object y) :=
  match x as x' in TwoObj
  return x = x' -> morphism Two (_2_Two_object x) (_2_Two_object y) with
  | TwoX => fun _ =>
    match y as y' in TwoObj
    return y = y' -> morphism Two (_2_Two_object x) (_2_Two_object y) with
    | TwoX => fun _ => {| mor_arr := 0%N; mor_dom := _; mor_cod := _ |}
    | TwoY => fun _ => {| mor_arr := 2%N; mor_dom := _; mor_cod := _ |}
    end eq_refl
  | TwoY => fun _ =>
    match y as y' in TwoObj
    return y = y' -> morphism Two (_2_Two_object x) (_2_Two_object y) with
    | TwoY => fun _ => {| mor_arr := 1%N; mor_dom := _; mor_cod := _ |}
    | TwoX => fun _ => !
    end eq_refl
  end eq_refl.
Next Obligation. inversion f. Defined.

Local Obligation Tactic := program_simpl.

Program Definition Two_from_Two : _2 ⟶ Category_from_Metacategory Two := {|
  fobj := _2_Two_object;
  fmap := _2_Two_morphism
|}.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation.
  destruct f; simpl;
  destruct x; simpl;
  spose (TwoHom_inv _ _ g) as H; subst;
  contradiction || reflexivity.
Defined.

Require Import Category.Instance.Cat.

Program Instance Two_iso_2 : Category_from_Metacategory Two ≅ _2 := {
  to   := Two_to_Two;
  from := Two_from_Two
}.
Next Obligation.
  unshelve eexists; intros.
    induction x; reflexivity.
  induction f; reflexivity.
Qed.
Next Obligation.
  unshelve eexists; intros.
    induction x using object_Two_rect;
    destruct x; simpl in H; subst.
    { isomorphism; simpl.
      - construct; [exact 0%N|..]; auto.
      - construct; [exact 0%N|..]; auto.
      - reflexivity.
      - reflexivity.
    }
    { isomorphism; simpl.
      - construct; [exact 1%N|..]; auto.
      - construct; [exact 1%N|..]; auto.
      - reflexivity.
      - reflexivity.
    }
  induction f using morphism_Two_rect;
  destruct x, y, f;
  simpl in H, H0, H1; subst;
  vm_compute; reflexivity.
Qed.
