Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Equations.Equations.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Sound.
Require Import Solver.Normal.

Generalizable All Variables.

Section Categories.

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrmap : M.t (∃ x y, objs x ~{C}~> objs y).

Definition arrs (a : arr_idx) := M.find a arrmap.

(* A reified arrow is a list of morphism indices within the current
   environment that denotes a known arrow. *)
Inductive ReifiedArrow (dom : obj_idx) : obj_idx -> list arr_idx -> Type :=
  | IdentityArrow : ReifiedArrow dom dom []
  | SingleArrow : forall (f : arr_idx) (cod : obj_idx)
                         (f' : objs dom ~> objs cod),
      arrs f = Some (dom; (cod; f'))
        -> ReifiedArrow dom cod [f]
  | ComposedArrow : forall (mid cod : obj_idx) f g gs,
      ReifiedArrow mid cod [f]
        -> ReifiedArrow dom mid (g :: gs)
        -> ReifiedArrow dom cod (f :: g :: gs).

Equations ReifiedArrow_comp {dom mid cod}
          `(f : ReifiedArrow mid cod (x :: xs))
          `(g : ReifiedArrow dom mid (y :: ys)) :
  ReifiedArrow dom cod (x :: xs ++ y :: ys) :=
  ReifiedArrow_comp (SingleArrow a _ a' f) g :=
    ComposedArrow _ _ _ _ _ _ (SingleArrow _ a _ a' f) g;
  ReifiedArrow_comp (ComposedArrow f g) h :=
    ComposedArrow _ _ _ _ _ _ f (ReifiedArrow_comp g h).

Definition getArrList {dom cod} `(a : ReifiedArrow dom cod fs) :
  list arr_idx := fs.
Arguments getArrList {dom cod fs} a /.

Equations getArrMorph {dom cod} `(a : ReifiedArrow dom cod fs) :
  objs dom ~{C}~> objs cod :=
  getArrMorph IdentityArrow := id;
  getArrMorph (SingleArrow f _) := f;
  getArrMorph (ComposedArrow f g) := getArrMorph f ∘ getArrMorph g.

Definition ReifiedArrow_size {dom cod} `(a : ReifiedArrow dom cod fs) : nat :=
  length (getArrList a).

(*
Equations ReifiedArrow_getArrMorph_comp {dom mid cod}
          `(f : ReifiedArrow mid cod (x :: xs))
          `(g : ReifiedArrow dom mid (y :: ys)) :
  getArrMorph (ReifiedArrow_comp f g) ≈ getArrMorph f ∘ getArrMorph g :=
  ReifiedArrow_getArrMorph_comp f g by rec xs (MR lt (@length arr_idx)) :=
  ReifiedArrow_getArrMorph_comp SingleArrow g := reflexivity _;
  ReifiedArrow_getArrMorph_comp (ComposedArrow f f') g := _.
Next Obligation.
  rewrite ReifiedArrow_comp_equation_2.
  rewrite !getArrMorph_equation_3.
  rewrite ReifiedArrow_getArrMorph_comp; cat.
  constructor.
Admitted.
*)

Lemma ReifiedArrow_getArrMorph_comp {dom mid cod}
          `(f : ReifiedArrow mid cod (x :: xs))
          `(g : ReifiedArrow dom mid (y :: ys)) :
  getArrMorph (ReifiedArrow_comp f g) ≈ getArrMorph f ∘ getArrMorph g.
Proof.
  dependent induction f; intros.
    rewrite ReifiedArrow_comp_equation_1; cat.
  rewrite ReifiedArrow_comp_equation_2.
  rewrite !getArrMorph_equation_3.
  rewrite IHf2; cat.
Qed.

Definition ReifiedArrowEx dom cod := ∃ fs, ReifiedArrow dom cod fs.

Equations ReifiedArrow_comp_ex {dom mid cod}
          (f : ∃ xs, ReifiedArrow mid cod xs)
          (g : ∃ xs, ReifiedArrow dom mid xs) :
  ∃ xs, ReifiedArrow dom cod xs :=
  ReifiedArrow_comp_ex (existT IdentityArrow) g := g;
  ReifiedArrow_comp_ex f (existT IdentityArrow) := f;
  ReifiedArrow_comp_ex (existT (SingleArrow a _ a' f)) (existT g) :=
    (_; ComposedArrow _ _ _ _ _ _ (SingleArrow _ a _ a' f) g);
  ReifiedArrow_comp_ex (existT (ComposedArrow f g)) (existT h) :=
    (_; ComposedArrow _ _ _ _ _ _ f (ReifiedArrow_comp g h)).

Lemma ReifiedArrow_comp_ex_comp {dom mid cod bs cs} f g :
  getArrMorph `2 (ReifiedArrow_comp_ex (bs; f) (cs; g))
    ≈ getArrMorph (cod:=cod) f ∘
      getArrMorph (dom:=dom) (cod:=mid) g.
Proof.
  destruct g.
  - destruct f.
    + rewrite ReifiedArrow_comp_ex_equation_1; cat.
    + rewrite ReifiedArrow_comp_ex_equation_2; cat.
    + rewrite ReifiedArrow_comp_ex_equation_5; cat.
  - destruct f.
    + rewrite ReifiedArrow_comp_ex_equation_1; cat.
    + rewrite ReifiedArrow_comp_ex_equation_3; cat.
    + rewrite ReifiedArrow_comp_ex_equation_6; cat.
      rewrite !getArrMorph_equation_3.
      rewrite ReifiedArrow_getArrMorph_comp; cat.
  - destruct f.
    + rewrite ReifiedArrow_comp_ex_equation_1; cat.
    + rewrite ReifiedArrow_comp_ex_equation_4; cat.
    + rewrite ReifiedArrow_comp_ex_equation_7; cat.
      rewrite !getArrMorph_equation_3.
      rewrite ReifiedArrow_getArrMorph_comp; cat.
Qed.

Lemma ReifiedArrow_comp_ex_assoc {x y z w : obj_idx}
      `(f : ReifiedArrow z w fs) 
      `(g : ReifiedArrow y z gs)
      `(h : ReifiedArrow x y hs) :
  getArrMorph `2
    (ReifiedArrow_comp_ex (fs; f) (ReifiedArrow_comp_ex (gs; g) (hs; h))) ≈
  getArrMorph `2
    (ReifiedArrow_comp_ex (ReifiedArrow_comp_ex (fs; f) (gs; g)) (hs; h)).
Proof.
  destruct h; intros.
  - destruct g.
    + rewrite ReifiedArrow_comp_ex_equation_1; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_2; cat.
      * rewrite ReifiedArrow_comp_ex_equation_5; cat.
    + rewrite ReifiedArrow_comp_ex_equation_2; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_3; cat.
      * rewrite ReifiedArrow_comp_ex_equation_6; cat.
    + rewrite ReifiedArrow_comp_ex_equation_5; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_4; cat.
      * rewrite ReifiedArrow_comp_ex_equation_7; cat.
  - destruct g.
    + rewrite ReifiedArrow_comp_ex_equation_1; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_2; cat.
      * rewrite ReifiedArrow_comp_ex_equation_5; cat.
    + rewrite ReifiedArrow_comp_ex_equation_3; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_3; cat.
      * rewrite !ReifiedArrow_comp_ex_equation_6.
        rewrite !ReifiedArrow_comp_ex_equation_7.
        rewrite !getArrMorph_equation_3.
        comp_left.
        rewrite !ReifiedArrow_getArrMorph_comp.
        comp_left.
        now rewrite !getArrMorph_equation_3.
    + rewrite ReifiedArrow_comp_ex_equation_6; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_4; cat.
      * rewrite !ReifiedArrow_comp_ex_equation_7.
        rewrite !getArrMorph_equation_3.
        comp_left.
        rewrite !ReifiedArrow_getArrMorph_comp.
        comp_left.
        rewrite !getArrMorph_equation_3.
        comp_left.
        now rewrite !ReifiedArrow_getArrMorph_comp.
  - destruct g.
    + rewrite ReifiedArrow_comp_ex_equation_1; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_2; cat.
      * rewrite ReifiedArrow_comp_ex_equation_5; cat.
    + rewrite ReifiedArrow_comp_ex_equation_4; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_3; cat.
      * rewrite !ReifiedArrow_comp_ex_equation_6.
        rewrite !ReifiedArrow_comp_ex_equation_7.
        rewrite !getArrMorph_equation_3.
        comp_left.
        rewrite !ReifiedArrow_getArrMorph_comp.
        comp_left.
        now rewrite !getArrMorph_equation_3.
    + rewrite ReifiedArrow_comp_ex_equation_7; cat.
      destruct f.
      * rewrite ReifiedArrow_comp_ex_equation_1; cat.
      * rewrite ReifiedArrow_comp_ex_equation_4; cat.
      * rewrite !ReifiedArrow_comp_ex_equation_7.
        rewrite !getArrMorph_equation_3.
        comp_left.
        rewrite !ReifiedArrow_getArrMorph_comp.
        comp_left.
        rewrite !getArrMorph_equation_3.
        comp_left.
        now rewrite !ReifiedArrow_getArrMorph_comp.
Qed.

Global Program Instance ReifiedArrow_Setoid dom cod :
  Setoid (ReifiedArrowEx dom cod) := {
  equiv := fun f g => getArrMorph `2 f ≈ getArrMorph `2 g
}.

Program Definition Reified : Category := {|
  obj     := obj_idx;
  hom     := fun dom cod => ∃ xs, ReifiedArrow dom cod xs;
  homset  := ReifiedArrow_Setoid;
  id      := fun dom => ([]; IdentityArrow dom);
  compose := fun _ _ _ => ReifiedArrow_comp_ex
|}.
Next Obligation. proper; now rewrite !ReifiedArrow_comp_ex_comp, X, X0. Qed.
Next Obligation. rewrite ReifiedArrow_comp_ex_comp; cat. Qed.
Next Obligation. apply ReifiedArrow_comp_ex_assoc. Qed.
Next Obligation. symmetry; apply ReifiedArrow_comp_ex_assoc. Qed.

(*
Lemma ReifiedArrow_app {dom mid cod}
      (a : ReifiedArrow dom cod)
      (f : ReifiedArrow mid cod)
      (g : ReifiedArrow dom mid) :
  getArrList a = getArrList f ++ getArrList g -> a ≈ f ∘[Reified] g.
Proof.
  destruct a, f, g; simpl in *; intros.
  subst.
  unfold arrowsD in e.
  simpl in e.
  destruct_arrows.
  destruct (arrowsD_compose objs arrmap Heqo), s, s, p, p.
  clear Heqo.
  rewrite <- e; clear e.
  rewrite e2; clear e2.
  unfold arrowsD in e0.
  simpl in e0.
  destruct_arrows.
  rewrite <- e0; clear e0.
  unfold arrowsD in e1.
  simpl in e1.
  destruct_arrows.
  rewrite <- e1; clear e1.
  inversion e4; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Pos.eq_dec].
  subst.
  rewrite e3 in Heqo.
  inversion Heqo.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; [|apply Pos.eq_dec].
  subst.
  reflexivity.
Qed.

Program Definition arr_uncons {dom cod} `(f : ReifiedArrow dom cod) :
  ∃ mid (g : ReifiedArrow mid cod) (h : ReifiedArrow dom mid),
    f ≈ g ∘[Reified] h ∧
    match getArrList f with
    | x :: xs => getArrList g = [x] ∧ getArrList h = xs
    | nil => getArrList g = nil ∧ getArrList h = nil
    end :=
  match f with
  | mkArr nil g H =>
    match Pos.eq_dec dom cod with
    | left _ => (dom; (f; (f; _)))
    | right _ => !
    end
  | mkArr (x :: xs) f' H =>
    match Normal.arrs objs arrmap x with
    | None => !
    | Some (mid; (cod'; g)) =>
      match Pos.eq_dec cod cod' with
      | left _ =>
        match arrowsD objs arrmap dom mid xs with
        | None => !
        | Some h => (mid; (mkArr [x] g _; (mkArr xs h _; _)))
        end
      | right _ => !
      end
    end
  end.
Next Obligation.
  split; auto.
  unfold arrowsD in H; simpl in H.
  rewrite Pos_eq_dec_refl in H.
  simpl_eq.
  rewrite <- H; cat.
Qed.
Next Obligation.
  unfold arrowsD in H; simpl in H.
  destruct (Pos.eq_dec dom cod); subst; contradiction.
Qed.
Next Obligation.
  replace (x :: xs) with ([x] ++ xs) in * by reflexivity.
  unfold arrowsD in H.
  destruct_arrows.
  destruct (arrowsD_compose objs arrmap Heqo), s, s, p, p.
  simpl in e0.
  rewrite <- Heq_anonymous in e0.
  discriminate.
Qed.
Next Obligation.
  replace (x :: xs) with ([x] ++ xs) in * by reflexivity.
  unfold arrowsD in H.
  destruct_arrows.
  destruct (arrowsD_compose objs arrmap Heqo), s, s, p, p.
  unfold arrowsD in Heq_anonymous.
  rewrite e1 in Heq_anonymous.
  simpl in e0.
  rewrite <- Heq_anonymous0 in e0.
  simpl in *.
  destruct (Pos.eq_dec x0 mid); subst.
    discriminate.
  destruct (Pos.eq_dec mid x0); subst.
    contradiction.
  discriminate.
Qed.
Next Obligation.
  unfold arrowsD in *.
  simpl in *.
  rewrite <- Heq_anonymous0 in *.
  do 2 rewrite Pos_eq_dec_refl.
  reflexivity.
Qed.
Next Obligation.
  replace (x :: xs) with ([x] ++ xs) in * by reflexivity.
  unfold arrowsD in H.
  destruct_arrows.
  destruct (arrowsD_compose objs arrmap Heqo), s, s, p, p.
  simpl in e0.
  rewrite <- Heq_anonymous0 in e0.
  destruct (Pos.eq_dec mid x0); subst; [|discriminate].
  simpl_eq.
  inversion e0; clear e0.
  rewrite H in e.
  apply Eqdep_dec.inj_pair2_eq_dec in H1.
    subst.
    unfold arrowsD in Heq_anonymous.
    rewrite e1 in Heq_anonymous.
    rewrite Pos_eq_dec_refl in Heq_anonymous.
    simpl_eq.
    inversion Heq_anonymous.
    subst.
    assumption.
  apply Pos.eq_dec.
Qed.
Next Obligation.
  replace (x :: xs) with ([x] ++ xs) in * by reflexivity.
  unfold arrowsD in H.
  destruct_arrows.
  destruct (arrowsD_compose objs arrmap Heqo), s, s, p, p.
  simpl in e0.
  rewrite <- Heq_anonymous0 in e0.
  destruct (Pos.eq_dec mid x0); subst; [|discriminate].
  simpl_eq.
  inversion e0.
  subst.
  contradiction.
Qed.

Lemma arr_rect {dom} (P : ∀ cod, ReifiedArrow dom cod → Type) :
  (∀ f, f ≈[Reified] id -> P dom f)
    → (∀ mid cod (x : arr_idx) (xs : list arr_idx)
         (f' : objs mid ~> objs cod)
         (g' : objs dom ~> objs mid)
         (Hf' : arrowsD objs arrmap mid cod [x] ≈ Some f')
         (Hg' : arrowsD objs arrmap dom mid xs  ≈ Some g')
         f g h,
              f ≈ mkArr [x] f' Hf'
           -> g ≈ mkArr xs g' Hg'
           -> h ≈ f ∘[Reified] g
           -> P mid g
           -> P cod h)
    → ∀ cod (a : ReifiedArrow dom cod), P cod a.
Proof.
  intros.
  destruct a.
  generalize dependent dom.
  generalize dependent cod.
  induction f; simpl; intros.
    destruct (ReifiedArrow_nil (mkArr [] f' e) eq_refl).
    subst; simpl_eq.
    simpl in *; subst.
    apply X.
    assumption.
  destruct (ReifiedArrow_cons (mkArr (a :: f) f' e) a f eq_refl), s, s, p.
  unshelve refine
           (X0 x cod a f (getArrMorph x0) (getArrMorph x1) _ _
               x0 x1 _ (reflexivity _) (reflexivity _) _ _); auto.
  - rewrite <- e0.
    destruct x0.
    apply e2.
  - rewrite <- e1.
    destruct x1.
    apply e2.
  - simpl.
    clear X X0 IHf.
    replace (a :: f) with ([a] ++ f) in e by reflexivity.
    unfold arrowsD in e.
    destruct_arrows.
    destruct (arrowsD_compose objs arrmap Heqo), s, s, p, p.
    destruct (Eq_eq_dec x2 cod); subst; [|contradiction].
    rewrite <- e, e2; clear e e2 Heqo.
    rewrite <- e0 in e3; clear e0.

    destruct x0, x1; simpl in *.
    unfold arrowsD in *.
    do 2 destruct_arrows.
    rewrite <- e, <- e0; clear e e0.
    inversion e4; subst; clear e4.
    apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply Pos.eq_dec].
    rewrite Heqo in e3.
    inversion e3; subst; clear e3.
    apply Eqdep_dec.inj_pair2_eq_dec in H0; [|apply Pos.eq_dec].
    subst.
    reflexivity.
  - destruct x1.
    simpl in e1; subst.
    eapply IHf; eauto.
Defined.

Program Definition arr_break {dom cod} (n : nat) `(f : ReifiedArrow dom cod) :
  ∃ mid (g : ReifiedArrow mid cod) (h : ReifiedArrow dom mid),
    f ≈ g ∘[Reified] h.
Proof.
  generalize dependent cod.
  induction n; intros.
    exists cod, (@id Reified _), f; cat.
  generalize dependent cod.
  induction f using @arr_rect.
    exists dom, (@id Reified _), (@id Reified _); cat.
  clear IHf1.
  destruct (IHn mid f2), s, s.
  exists x0, (f1 ∘[Reified] x1), x2.
  rewrite <- comp_assoc.
  rewrite <- e.
  assumption.
Defined.

Definition arr_size {dom cod} (f : ReifiedArrow dom cod) : nat :=
  length (getArrList f).

Lemma arr_break_size {dom cod n f} :
  (0 < arr_size f)%nat -> (0 < n)%nat ->
  match @arr_break dom cod n f with
  | (mid; (g; (h; H))) =>
    (arr_size h < arr_size f)%nat
  end.
Proof.
  intros.
  generalize dependent cod.
  induction f using @arr_rect; intros.
Abort.
*)

End Categories.

(*
Section Normalization.

Variable arrs : arr_idx -> (obj_idx * obj_idx).

Definition arr_dom (f : arr_idx) : obj_idx := fst (arr_def f).
Definition arr_cod (f : arr_idx) : obj_idx := snd (arr_def f).

Notation Term    := (Term arrs).
Notation TermDom := (TermDom arrs).
Notation TermCod := (TermCod arrs).

Program Definition Term_Category {C objs arrs} : Category := {|
  obj := obj_idx;
  hom := fun x y => ∃ f f', @termD C objs arrs x y f = Some f';
  homset := fun x y => {| equiv := fun f g => `1 `2 f ≈ `1 `2 g |};
  id := fun x => (Identity x; (@id C (objs x); _));
  compose := fun x y z f g => (Compose y `1 f `1 g; (`1 `2 f ∘ `1 `2 g; _))
|}.
Next Obligation. now equalities. Defined.
Next Obligation. now rewrite X2, X0. Defined.

Program Definition Term_Category' {C objs arrs} : Category := {|
  obj := obj_idx;
  hom := fun _ _ => Term;
  homset := fun x y => {| equiv := fun f g =>
    @termD C objs arrs x y f ≈ @termD C objs arrs x y g |};
  id := Identity;
  compose := fun _ y _ => Compose y
|}.
Next Obligation.
  equivalence.
  - destruct (termD objs arrs x y x0) eqn:?; auto.
    reflexivity.
  - destruct (termD objs arrs x y x0) eqn:?;
    destruct (termD objs arrs x y y0) eqn:?; auto.
    now symmetry.
  - destruct (termD objs arrs x y x0) eqn:?;
    destruct (termD objs arrs x y y0) eqn:?;
    destruct (termD objs arrs x y z) eqn:?; auto.
      now transitivity h0.
    contradiction.
Defined.
Next Obligation.
  proper.
  destruct (termD objs arrs y z x0) eqn:?;
  destruct (termD objs arrs x y x1) eqn:?;
  destruct (termD objs arrs y z y0) eqn:?;
  destruct (termD objs arrs x y y1) eqn:?; auto.
  now rewrite X, X0.
Defined.
Next Obligation.
  equalities'; auto.
  equalities.
  destruct (termD objs arrs x y f) eqn:?; cat.
Qed.
Next Obligation.
  equalities'; auto.
  equalities.
  destruct (termD objs arrs x y f) eqn:?; cat.
Qed.
Next Obligation.
  destruct (termD objs arrs z w f) eqn:?;
  destruct (termD objs arrs y z g) eqn:?;
  destruct (termD objs arrs x y h) eqn:?; cat.
Qed.
Next Obligation.
  destruct (termD objs arrs z w f) eqn:?;
  destruct (termD objs arrs y z g) eqn:?;
  destruct (termD objs arrs x y h) eqn:?; cat.
Qed.

Existing Instance Term_Category'.

(* This describes the morphisms of a path, or free, category over a quiver of
   Arrows, while our environment describes a quiver (where vertices are all
   object indices, and edges are all arrow indices associated pairs of object
   indices). The denotation of an ArrowList to some category C is a forgetful
   functor from the path category over this quiver to C. Note that this
   functor is only total if the denotation of the quiver itself is total. *)
Inductive ArrowList : Set :=
  | IdentityOnly (o : obj_idx) : ArrowList
  | ArrowChain (a : arr_idx) : ArrowList -> ArrowList.

Function ArrowList_beq (xs ys : ArrowList) : bool :=
  match xs, ys with
  | IdentityOnly o1, IdentityOnly o2 => Eq_eqb o1 o2
  | ArrowChain a1 xs1, ArrowChain a2 ys2 =>
    Eq_eqb a1 a2 &&& ArrowList_beq xs1 ys2
  | _, _ => false
  end.

Fixpoint ArrowList_beq_eq x y :
  ArrowList_beq x y = true <-> x = y.
Proof.
  destruct x, y; simpl; split; intros;
  equalities; try discriminate.
  - inversion_clear H.
    now apply Eq_eqb_refl.
  - now apply ArrowList_beq_eq in H1; subst.
  - equalities.
    inversion_clear H.
    now apply Eq_eqb_refl.
  - inversion_clear H.
    now apply ArrowList_beq_eq.
Qed.

Function ArrowList_to_list (xs : ArrowList) : list arr_idx * obj_idx :=
  match xs with
  | IdentityOnly x => ([], x)
  | ArrowChain f fs =>
    match ArrowList_to_list fs with
    | (fs, dom) => (f :: fs, dom)
    end
  end.

Function ArrowList_from_list (xs : list arr_idx) (x : obj_idx) : ArrowList :=
  match xs with
  | nil => IdentityOnly x
  | f :: fs => ArrowChain f (ArrowList_from_list fs x)
  end.

Lemma ArrowList_to_from_list xs x :
  ArrowList_to_list (ArrowList_from_list xs x) = (xs, x).
Proof.
  induction xs; simpl; auto.
  now rewrite IHxs.
Defined.

Lemma ArrowList_from_to_list xs :
  let '(x, y) := ArrowList_to_list xs in
  ArrowList_from_list x y = xs.
Proof.
  induction xs; simpl; intros; subst; auto.
  destruct (ArrowList_to_list xs); simpl in *.
  now rewrite IHxs.
Defined.

Definition ArrowList_cod (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain f _ => arr_cod f
  end.

Function ArrowList_dom (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain _ xs => ArrowList_dom xs
  end.

Inductive ForallAligned : list Arrow → Prop :=
    Align_nil : ForallAligned []
  | Align_singleton : ∀ (a : Arrow), ForallAligned [a]
  | Align_cons2 : ∀ (a b : Arrow) (l : list Arrow),
      arr_dom a = arr_cod b ->
      ForallAligned (b :: l) → ForallAligned (a :: b :: l).

Lemma ForallAligned_inv {x xs y} :
  ForallAligned (x :: y :: xs)
    -> arr_dom x = arr_cod y /\
       ForallAligned (y :: xs).
Proof.
  generalize dependent x.
  generalize dependent y.
  induction xs; intros;
  inversion H; subst; intuition.
Qed.

Lemma ForallAligned_app {x xs y ys} :
  ForallAligned (x :: xs ++ y :: ys)
    <-> ForallAligned (x :: xs) /\ ForallAligned (y :: ys) /\
        arr_cod y = arr_dom (last xs x).

Definition ListOfArrows_rect : ∀ (P : Arrow -> list Arrow → Type),
  (∀ (x : Arrow), P x []) →
  (∀ (x y : Arrow) (l : list Arrow), P y l → P x (y :: l)) →
  ∀ (x : Arrow) (l : list Arrow), P x l.
Proof.
  intros.
  generalize dependent x.
  induction l; auto.
Defined.

Definition ArrowList_append (xs ys : ArrowList) : ArrowList :=
  match xs, ys with
  | IdentityOnly f,  IdentityOnly g  => IdentityOnly g
  | IdentityOnly f,  ArrowChain g xs => ArrowChain g xs
  | ArrowChain f xs, IdentityOnly g  => ArrowChain f xs
  | ArrowChain f xs, ArrowChain g ys => ArrowChain f (xs ++ g :: ys)
  end.

Lemma ArrowList_append_chains a a0 l l0 :
  ArrowList_dom (ArrowChain a l) = ArrowList_cod (ArrowChain a0 l0) ->
  ArrowList_append (ArrowChain a l) (ArrowChain a0 l0) =
  ArrowChain a (l ++ a0 :: l0).
Proof.
  generalize dependent a0.
  generalize dependent l0.
  simpl.
  induction l using rev_ind; simpl; intros; auto.
Qed.

Lemma ArrowList_append_well_typed {dom mid cod f1 f2} :
  ArrowList_dom f1 = mid ->
  ArrowList_cod f2 = mid ->
  ArrowList_well_typed mid cod f1 ->
  ArrowList_well_typed dom mid f2 ->
    ArrowList_well_typed dom cod (ArrowList_append f1 f2).
Proof.
  generalize dependent mid.
  generalize dependent f2.
  induction f1 using ArrowList_list_rect; intros.
  - simpl in *.
    equalities; subst.
    destruct f2 using ArrowList_list_rect; simpl in *; auto.
  - simpl in *; equalities; subst.
    destruct f2.
      simpl in *; subst; intuition.
    simpl in *; equalities.
    + induction l using rev_ind.
        simpl in *; equalities.
        inversion H2; subst.
        now inversion H.
      rewrite !last_app_cons in *; simpl in *.
      replace (match l ++ [x] with
               | [] => a0
               | _ :: _ => x
               end) with x by (destruct l; auto); auto.
    + constructor; auto.
  - clear IHf1.
    equalities; subst.
    destruct f2.
      constructor; simpl in H1; intuition.
      simpl in *; subst; intuition.
    rewrite ArrowList_append_chains by congruence.
    simpl; constructor.
      simpl in H1; intuition.
    rewrite last_app_cons, last_cons.
    pose proof (ArrowList_well_typed_dom H2) as H5.
    simpl in H5.
    replace (match l ++ a :: l0 with
             | [] => a2
             | _ :: _ => last l0 a
             end) with (last l0 a) by (destruct l; auto);
    intuition; rewrite !app_comm_cons.
    apply ForallAligned_app.
    inversion H1.
    inversion H2.
    intuition.
Qed.

Fixpoint normalize `(p : Term a b) : ArrowList :=
  match p with
  | Identity _ x        => IdentityOnly x
  | Morph _ f           => ArrowChain f []
  | Compose _ x y z f g => ArrowList_append (normalize f) (normalize g)
  end.

Lemma ArrowList_append_dom f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_dom (ArrowList_append f g) = ArrowList_dom g.
Proof.
  destruct g, f; simpl; intros; auto.
  now rewrite last_app_cons, last_cons.
Qed.

Lemma ArrowList_append_cod f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_cod (ArrowList_append f g) = ArrowList_cod f.
Proof.
  destruct f, g; simpl; intros; auto.
Qed.

(*
Lemma ArrowList_normalize_dom_cod_sound {p dom cod} :
  Term_well_typed dom cod p ->
  ArrowList_dom (normalize p) = dom /\
  ArrowList_cod (normalize p) = cod.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros; intuition; subst;
  rewrite H0 in H;
  rewrite ArrowList_append_dom ||
  rewrite ArrowList_append_cod; auto;
  specialize (IHp1 _ _ H);
  specialize (IHp2 _ _ H2);
  intuition; congruence.
Qed.

Corollary ArrowList_specific_sound p :
  Term_well_typed (TermDom p) (TermCod p) p ->
  ArrowList_dom (normalize p) = TermDom p /\
  ArrowList_cod (normalize p) = TermCod p.
Proof. apply ArrowList_normalize_dom_cod_sound. Qed.
*)

Lemma ArrowList_id_left x y :
  ArrowList_append (IdentityOnly x) y = y.
Proof.
  simpl.
  destruct y; simpl; intros; subst; auto.
Qed.

Lemma ArrowList_id_right f y :
  ArrowList_dom f = y ->
  ArrowList_append f (IdentityOnly y) = f.
Proof.
  destruct f; simpl; intros; subst; auto.
Qed.

Lemma ArrowList_append_assoc x y z :
  ArrowList_append (ArrowList_append x y) z =
  ArrowList_append x (ArrowList_append y z).
Proof.
  destruct x, y, z; simpl; auto; intros;
  try destruct a;
  try destruct a0; subst; auto;
  now rewrite <- app_assoc.
Qed.

(* We show here that ArrowList morphisms are just one way of representing a
   free category. However, we still forget identities and which way
   composition was associated, so really it's a normalized free category. *)
Program Definition ArrowList_Category : Category := {|
  obj := obj_idx;
  hom := fun x y =>
    ∃ l : ArrowList, ArrowList_well_typed x y l;
  homset := fun x y => {| equiv := fun f g => `1 f = `1 g |};
  id := fun x => (IdentityOnly x; _);
  compose := fun _ _ _ f g => (ArrowList_append (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left y (`1 f);
  id_right := fun x _ f => ArrowList_id_right (`1 f) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc (`1 f) (`1 g) (`1 h)
|}.
Next Obligation. equivalence; simpl in *; congruence. Qed.
Next Obligation.
  pose proof (ArrowList_well_typed_dom X0).
  pose proof (ArrowList_well_typed_cod X).
  eapply ArrowList_append_well_typed; eauto.
Qed.
Next Obligation. proper; simpl in *; subst; reflexivity. Qed.
Next Obligation.
  now apply ArrowList_well_typed_dom in X.
Qed.
Next Obligation. apply ArrowList_append_assoc; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.

(* In the category whose morphisms are Terms, homset equivalence is up to
   normalized terms. *)
Program Definition Term_Category : Category := {|
  obj := obj_idx;
  hom := Term;
  homset := fun x y => {| equiv := fun f g => normalize f = normalize g |};
  id := Identity arrs;
  compose := fun x y z f g => Compose arrs x y z f g;
  id_left := fun _ y f => ArrowList_id_left y (normalize f);
  id_right := fun x _ f => ArrowList_id_right (normalize f) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc (normalize f) (normalize g) (normalize h)
|}.
Next Obligation.
  pose proof (Term_well_typed_dom arrs X).
  pose proof (Term_well_typed_dom arrs X0).
  pose proof (Term_well_typed_cod arrs X).
  pose proof (Term_well_typed_cod arrs X0).
  destruct f, g; simpl in *; intuition idtac; congruence.
Qed.
Next Obligation.
  eapply ArrowList_normalize_dom_cod_sound; eauto.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.

Lemma ArrowList_well_typed_sound {f dom cod} :
  Term_well_typed dom cod f
    -> ArrowList_well_typed dom cod (normalize f).
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction f; simpl; intros; intuition.
    constructor; constructor.
  specialize (IHf1 _ _ H).
  specialize (IHf2 _ _ H2).
  pose proof (ArrowList_well_typed_dom IHf1).
  pose proof (ArrowList_well_typed_cod IHf2).
  apply (ArrowList_append_well_typed H1 H3 IHf1 IHf2).
Qed.

Set Transparent Obligations.

Program Instance Term_to_ArrowList :
  Term_Category ⟶ ArrowList_Category := {
  fobj := fun x => x;
  fmap := fun x y f => (normalize _; _)
}.
Next Obligation. now apply ArrowList_well_typed_sound. Qed.

Fixpoint denormalize (f : ArrowList) : Term :=
  match f with
  | IdentityOnly x => Identity x
  | ArrowChain f xs =>
    fold_left (fun acc x => (fun y => Compose y x) \o acc)
              (map Morph xs) Datatypes.id (Morph f)
  end.

Lemma normalize_denormalize {dom cod f} :
  ArrowList_well_typed dom cod f
    -> normalize (denormalize f) = f.
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros; auto.
  rewrite <- ArrowList_append_chains at 2.
  - rewrite <- (IHl (arr_cod x)); clear IHl.
    + simpl.
      now rewrite map_app, fold_left_app.
    + simpl in H |- *;
      equalities.
      * rewrite app_comm_cons in H1.
        now apply ForallAligned_app in H1.
      * rewrite app_comm_cons in H1.
        now apply ForallAligned_app in H1.
  - simpl in *; equalities.
    rewrite app_comm_cons in H1.
    now apply ForallAligned_app in H1.
Qed.

Theorem denormalize_well_typed dom cod f :
  ArrowList_well_typed dom cod f
    -> Term_well_typed dom cod (denormalize f).
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros.
    simpl in *; intuition.
  assert (ArrowList_well_typed
            (arr_cod x) cod (ArrowChain a l)). {
    clear IHl.
    simpl in *; equalities.
    - rewrite app_comm_cons in H1.
      now apply ForallAligned_app in H1.
    - rewrite app_comm_cons in H1.
      now apply ForallAligned_app in H1.
  }
  rewrite <- ArrowList_append_chains by (simpl in *; intuition).
  specialize (IHl (arr_cod x) a H0).
  simpl in *; equalities.
  rewrite app_comm_cons in H4.
  apply ForallAligned_app in H4; equalities.
  rewrite map_app, fold_left_app; simpl.
  rewrite H4.
  intuition; subst.
  - clear -H.
    induction l using rev_ind; simpl; auto.
    rewrite map_app, fold_left_app; simpl.
    now rewrite last_rcons in *.
  - now rewrite H4 in IHl.
  - now rewrite last_rcons.
Qed.

Program Instance ArrowList_to_Term :
  ArrowList_Category ⟶ Term_Category := {
  fobj := fun x => x;
  fmap := fun x y f => (denormalize (`1 f); _)
}.
Next Obligation. apply denormalize_well_typed; auto. Qed.
Next Obligation.
  proper.
  simpl in *; subst.
  reflexivity.
Qed.
Next Obligation.
  erewrite !normalize_denormalize; eauto.
  pose proof (ArrowList_well_typed_dom X0).
  pose proof (ArrowList_well_typed_cod X).
  eapply ArrowList_append_well_typed; eauto.
Qed.

Fixpoint ArrowList_from_list (xs : obj_idx * list Arrow) : ArrowList :=
  match xs with
  | (x, nil) => IdentityOnly x
  | (_, x :: xs) => ArrowChain x xs
  end.

Lemma ArrowList_to_from_list xs :
  ArrowList_to_list (ArrowList_from_list xs) = xs.
Proof.
  destruct xs.
  induction l; simpl; auto.
  simpl in IHl.
  f_equal.
  destruct l; simpl in *.
    admit.
  inversion_clear IHl.
  destruct l; auto.
  f_equal.
  f_equal.
Abort.

Definition ArrowList_length (x : ArrowList) : nat :=
  match x with
  | IdentityOnly x => 0
  | ArrowChain x xs => 1 + length xs
  end.

Function ArrowList_beqn (n : nat) (x y : ArrowList) : bool :=
  match n with
  | O => true
  | S n' =>
    match x, y with
    | IdentityOnly cod1, IdentityOnly cod2 => Eq_eqb cod1 cod2
    | ArrowChain x1 nil, ArrowChain x2 (_ :: _) =>
      match n' with
      | O => Eq_eqb x1 x2
      | S x => false
      end
    | ArrowChain x1 (_ :: _), ArrowChain x2 nil =>
      match n' with
      | O => Eq_eqb x1 x2
      | S x => false
      end
    | ArrowChain x1 (y1 :: ys1), ArrowChain x2 (y2 :: ys2) =>
      Eq_eqb x1 x2 &&&
      ArrowList_beqn n' (ArrowChain y1 ys1) (ArrowChain y2 ys2)
    | _, _ => false
    end
  end.

Function ArrowList_drop (n : nat) (xs : ArrowList) : ArrowList :=
  match n with
  | O => xs
  | S n' =>
    match xs with
    | IdentityOnly o => IdentityOnly o
    | ArrowChain f nil => IdentityOnly (arr_cod f)
    | ArrowChain f (x :: xs) => ArrowList_drop n' (ArrowChain x xs)
    end
  end.

End Normalization.

Section Denotation.

Set Transparent Obligations.

Context (C : Category).

Variable objs : obj_idx -> C.
Variable arrs : arr_idx -> (obj_idx * obj_idx).
Variable get_arr : ∀ f : arr_idx,
  option (∃ x y, (arr_dom arrs f = x) ∧
                 (arr_cod arrs f = y) ∧ (objs x ~{C}~> objs y)).

Lemma denote_dom_cod {f dom cod f'} :
  denote dom cod f = Some f' ->
  TermDom arrs f = dom /\ TermCod arrs f = cod.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction f; intros dom cod; simpl; intros.
  - equalities.
  - destruct (get_arr a) eqn:?; [|discriminate].
    destruct s, s.
    equalities.
  - specialize (IHf2 dom (TermCod arrs f2)).
    specialize (IHf1 (TermCod arrs f2) cod).
    equalities; intros.
    destruct (denote (TermCod arrs f2) cod f1) eqn:?; [|discriminate].
    destruct (denote dom (TermCod arrs f2) f2) eqn:?; [|discriminate].
    destruct (IHf1 _ eq_refl).
    destruct (IHf2 _ eq_refl).
    intuition.
Qed.

Definition Term_defined dom cod (e : Term) : Type :=
  ∃ f, denote dom cod e = Some f.

Theorem Term_defined_is_well_typed {e dom cod} :
  Term_defined dom cod e ->
  Term_well_typed arrs dom cod e.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction e; simpl in *;
  intros dom cod [f H]; simpl in H; equalities;
  try (destruct (get_arr a); [|discriminate]; equalities).
  destruct (denote _ _ e1) eqn:?; [|discriminate].
  destruct (denote _ _ e2) eqn:?; [|discriminate].
  specialize (IHe1 (TermCod arrs e2) cod (h; Heqo)).
  specialize (IHe2 dom (TermCod arrs e2) (h0; Heqo0)).
  intuition; symmetry.
  eapply Term_well_typed_dom; eauto.
Qed.

Lemma denote_well_typed {p dom cod f} :
  denote dom cod p = Some f -> Term_well_typed arrs dom cod p.
Proof.
  generalize dependent f.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros ????; equalities;
  try (destruct (get_arr a); [|discriminate]; equalities).
  destruct (denote _ _ p2) eqn:?;
  destruct (denote _ _ p1) eqn:?; intros; try discriminate.
  pose proof (denote_dom_cod Heqo).
  pose proof (denote_dom_cod Heqo0).
  firstorder.
Qed.

Program Definition TermDef_Category : Category := {|
  obj := obj_idx;
  hom := fun x y => ∃ l : Term, Term_defined x y l;
  homset := fun x y => {| equiv := fun f g =>
    normalize (`1 f) = normalize (`1 g) |};
  id := fun x => (Identity x; _);
  compose := fun _ _ _ f g => (Compose (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left y (normalize (`1 f));
  id_right := fun x _ f => ArrowList_id_right arrs (normalize (`1 f)) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc
      (normalize (`1 f)) (normalize (`1 g)) (normalize (`1 h))
|}.
Next Obligation.
  eexists; simpl; equalities.
Defined.
Next Obligation.
  destruct X, X0.
  unshelve eexists; eauto.
    exact (x0 ∘ x).
  simpl.
  destruct (denote_dom_cod e).
  destruct (denote_dom_cod e0).
  equalities; subst.
  now rewrite e, e0.
Defined.
Next Obligation.
  eapply ArrowList_normalize_dom_cod_sound; eauto.
  eapply Term_defined_is_well_typed; eauto.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.

Fixpoint normalize_denote_chain dom cod (a : Arrow) (gs : list Arrow) :
  option (objs dom ~{C}~> objs cod).
Proof.
  destruct gs as [|g gs].
    destruct (get_arr a); [|exact None].
    destruct (Eq_eq_dec (arr_dom arrs a) dom); [|exact None].
    destruct (Eq_eq_dec (arr_cod arrs a) cod); [|exact None].
    equalities; exact (Some b0).
  destruct (Pos.eq_dec (arr_cod arrs a) cod); [|exact None].
  destruct (normalize_denote_chain dom (arr_dom arrs a) g gs); [|exact None].
  destruct (get_arr a); [|exact None].
  apply Some.
  equalities.
  exact (b0 ∘ h).
Defined.

Corollary normalize_denote_chain_cod :
  ∀ (gs : list Arrow) f dom cod f',
    normalize_denote_chain dom cod f gs = Some f' ->
    cod = arr_cod arrs f.
Proof.
  destruct gs; simpl; intros; equalities;
  destruct (get_arr f); equalities; discriminate.
Qed.

Theorem normalize_denote_chain_compose {x xs y ys dom cod f} :
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    arr_dom arrs (last xs x) = mid ∧
    arr_cod arrs y = mid ∧
    normalize_denote_chain mid cod x xs = Some g ∧
    normalize_denote_chain dom mid y ys = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  generalize dependent y.
  apply ListOfArrows_rect with (x:=x) (l:=xs); simpl; intros.
  - equalities.
    destruct (normalize_denote_chain dom (arr_dom arrs x0) y ys) eqn:?;
    equalities.
    destruct (get_arr x0); [|discriminate].
    equalities.
    exists _, h0, h.
    inversion_clear H.
    equalities.
      reflexivity.
    pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); auto.
  - equalities.
    destruct (normalize_denote_chain
                dom (arr_dom arrs x0) y (l ++ y0 :: ys)) eqn:?;
    equalities.
    try discriminate.
    destruct (get_arr x0); [|discriminate].
    destruct (X _ _ _ Heqo), s, s.
    equalities; subst.
    inversion_clear H.
    exists _, (h0 ∘ x2), x3.
    clear X.
    intuition.
    + now rewrite a, comp_assoc.
    + pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); subst.
      replace (match l with
               | [] => y
               | _ :: _ => last l x0
               end) with (last l y); auto.
      induction l; auto.
      now rewrite !last_cons.
    + now rewrite a2.
Qed.

Theorem normalize_denote_chain_compose_r {x xs y ys dom cod f} :
  (∃ mid g h, f ≈ g ∘ h ∧
     arr_dom arrs (last xs x) = mid ∧
     arr_cod arrs y = mid ∧
     normalize_denote_chain mid cod x xs = Some g ∧
     normalize_denote_chain dom mid y ys = Some h) ->
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f.
Proof.
  generalize dependent f.
  generalize dependent cod.
  generalize dependent y.
  apply ListOfArrows_rect with (x:=x) (l:=xs); simpl; intros.
  - repeat equalities.
      destruct (normalize_denote_chain dom (arr_dom arrs x0) y ys) eqn:?; [|discriminate].
      destruct (get_arr x0); [|discriminate].
      simpl_eq.
      equalities.
      simpl in a2.
      inversion_clear b0.
      inversion_clear a2.
    destruct (get_arr x0); [|discriminate].
    
    exists _, h0, h.
    inversion_clear H.
    equalities.
      reflexivity.
    pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); auto.
  - equalities.
    destruct (normalize_denote_chain
                dom (arr_dom arrs x0) y (l ++ y0 :: ys)) eqn:?;
    equalities.
    try discriminate.
    destruct (get_arr x0); [|discriminate].
    destruct (X _ _ _ Heqo), s, s.
    equalities; subst.
    inversion_clear H.
    exists _, (h0 ∘ x2), x3.
    clear X.
    intuition.
    + now rewrite a, comp_assoc.
    + pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); subst.
      replace (match l with
               | [] => y
               | _ :: _ => last l x0
               end) with (last l y); auto.
      induction l; auto.
      now rewrite !last_cons.
    + now rewrite a2.
Qed.

Lemma normalize_denote_chain_dom_cod :
  ∀ (gs : list Arrow) f dom cod f',
    normalize_denote_chain dom cod f gs = Some f' ->
    cod = arr_cod arrs f /\
    dom = arr_dom arrs (last gs f).
Proof.
  induction gs using rev_ind; intros.
    simpl in H.
    destruct (get_arr f); [|discriminate].
    now equalities.
  rewrite last_rcons.
  apply normalize_denote_chain_compose in H.
  equalities; subst.
    now specialize (IHgs _ _ _ _ a2).
  simpl in b0.
  destruct (get_arr x); [|discriminate].
  now equalities.
Qed.

Theorem normalize_denote_chain_append_dom_cod : ∀ x xs y ys dom cod f,
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  arr_dom arrs (last xs x) = arr_cod arrs y.
Proof.
  intros; destruct (normalize_denote_chain_compose H); equalities.
Qed.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Definition normalize_denote dom cod (xs : ArrowList) :
  option (objs dom ~{C}~> objs cod).
Proof.
  destruct xs as [o|f fs].
  - destruct (Eq_eq_dec o dom); [|exact None].
    destruct (Eq_eq_dec o cod); [|exact None].
    subst; exact (Some id).
  - exact (normalize_denote_chain dom cod f fs).
Defined.

Definition normalize_denote' dom cod (xs : ArrowList) :
  option (objs dom ~{C}~> objs cod).
Proof.
  generalize dependent cod.
  destruct xs using ArrowList_list_rect; intros.
  - destruct (Eq_eq_dec x dom); [|exact None].
    destruct (Eq_eq_dec x cod); [|exact None].
    subst; exact (Some (@id _ (objs cod))).
  - destruct (get_arr a); [|exact None].
    equalities.
    destruct (Eq_eq_dec (arr_dom arrs a) dom); [|exact None].
    destruct (Eq_eq_dec (arr_cod arrs a) cod); [|exact None].
    subst; exact (Some b0).
  - destruct (get_arr a1); [|exact None].
    destruct s, s, p, p; subst.
    destruct (IHxs (arr_dom arrs a1)); [|exact None].
    destruct (Eq_eq_dec (arr_cod arrs a1) cod); [|exact None].
    subst; exact (Some (h ∘ h0)).
Defined.

Program Fixpoint normalize_denote'' dom cod (xs : ArrowList) {measure (ArrowList_length xs)} :
  option (objs dom ~{C}~> objs cod) :=
  match xs with
  | IdentityOnly x =>
    match Eq_eq_dec x dom, Eq_eq_dec x cod with
    | left edom, left ecod =>
      Some (rew [fun x => objs x ~{ C }~> objs cod] edom in
            rew [fun y => objs x ~{ C }~> objs y] ecod in @id _ (objs x))
    | _, _ => None
    end
  | ArrowChain a nil =>
    match get_arr a with
    | Some (x; (y; (Hdom, (Hcod, f)))) =>
      match Eq_eq_dec (arr_dom arrs a) dom, Eq_eq_dec (arr_cod arrs a) cod with
      | left edom, left ecod =>
        Some (rew [fun x => objs x ~{ C }~> objs cod] edom in
              rew [fun y => objs (arr_dom arrs a) ~{ C }~> objs y] ecod in
              rew <- [fun x => objs x ~{ C }~> objs (arr_cod arrs a)] Hdom in
              rew <- [fun y => objs x ~{ C }~> objs y] Hcod in f)
      | _, _ => None
      end
    | _ => None
    end
  | ArrowChain a1 (a2 :: xs) =>
    match get_arr a1 with
    | Some (x1; (y1; (Hdom1, (Hcod1, f1)))) =>
      match normalize_denote dom x1 (ArrowChain a2 xs) with
      | Some f2 =>
        match Eq_eq_dec (arr_cod arrs a1) cod with
        | left ecod =>
          Some (rew [fun y => objs dom ~{ C }~> objs y] ecod in
                (rew <- [fun y => objs x1 ~> objs y] Hcod1 in f1 ∘ f2))
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.

Theorem normalize_list_cod {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_cod arrs p = cod.
Proof.
  intros; destruct p as [o|g []]; simpl in *; equalities;
  (destruct (get_arr g); [|discriminate]; equalities).
Qed.

Theorem normalize_list_dom {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_dom arrs p = dom.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; simpl in *; intros; equalities.
    destruct (get_arr a); discriminate.
  destruct (normalize_denote_chain _ _ _ _) eqn:Heqe; try discriminate.
  rewrite <- (IHp _ _ Heqe); clear IHp.
  induction l using rev_ind; simpl in *; equalities.
  rewrite !last_rcons.
  destruct l; auto.
Qed.

Theorem normalize_denote_well_typed {p dom cod f} :
  normalize_denote dom cod p = Some f
    -> ∃ p', p = normalize p' ∧ Term_well_typed arrs dom cod p'.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; simpl in *; intros; equalities.
  - exists (Identity cod).
    simpl; intuition.
  - exists (Morph a).
    simpl; intuition.
  - destruct (get_arr a); discriminate.
  - destruct (get_arr a); discriminate.
  - destruct (normalize_denote_chain _ _ _ _) eqn:?; try discriminate.
    destruct (IHp _ _ Heqo), p.
    exists (Compose (Morph a1) x).
    simpl.
    inversion_clear H.
    intuition.
    + now rewrite <- e.
    + eapply Term_well_typed_cod; eauto.
    + symmetry.
      eapply Term_well_typed_cod; eauto.
    + erewrite Term_well_typed_cod; eauto.
Qed.

Theorem normalize_compose {x y dom cod f} :
  ArrowList_cod arrs y = ArrowList_dom arrs x ->
  normalize_denote dom cod (ArrowList_append x y) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    ArrowList_dom arrs x = mid ∧
    ArrowList_cod arrs y = mid ∧
    normalize_denote mid cod x = Some g ∧
    normalize_denote dom mid y = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction x using ArrowList_list_rect; intros.
  - simpl in H.
    rewrite <- H.
    exists cod, (@id _ _), f.
    rewrite ArrowList_id_left in H0; auto.
    rewrite (normalize_list_cod H0) in *.
    cat; simpl; equalities.
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id _ _).
      rewrite <- H0.
      pose proof (normalize_list_dom H0).
      rewrite (ArrowList_id_right arrs) in * by auto.
      rewrite H, H1; clear H H1.
      cat; simpl in *; repeat equalities;
      destruct (get_arr a); discriminate.
    + rewrite (ArrowList_append_chains arrs) in H0 by auto.
      apply (normalize_denote_chain_compose H0).
    + rewrite (ArrowList_append_chains arrs) in H0 by auto.
      apply (normalize_denote_chain_compose H0).
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id _ _).
      rewrite (ArrowList_id_right arrs) in H0 by auto.
      rewrite (normalize_list_dom H0); subst.
      rewrite H0.
      pose proof (normalize_list_dom H0).
      cat; simpl in *; repeat equalities.
    + rewrite (ArrowList_append_chains arrs) in H0 by auto.
      apply (normalize_denote_chain_compose H0).
    + rewrite (ArrowList_append_chains arrs) in H0 by auto.
      apply (normalize_denote_chain_compose H0).
Qed.

Theorem normalize_compose_r {x y dom cod f} :
  ArrowList_cod arrs y = ArrowList_dom arrs x ->
  ∃ mid g h, f ≈ g ∘ h ∧
    ArrowList_dom arrs x = mid ∧
    ArrowList_cod arrs y = mid ∧
    normalize_denote mid cod x = Some g ∧
    normalize_denote dom mid y = Some h ->
  normalize_denote dom cod (ArrowList_append x y) = Some f.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction x using ArrowList_list_rect; intros.
  - simpl in H.
    rewrite <- H.
    exists cod, (@id _ _), f.
    rewrite ArrowList_id_left; auto.
    cat; simpl; equalities.
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id _ _).
      intros; equalities.
    + rewrite (ArrowList_append_chains arrs) by auto.
      admit.
    + rewrite (ArrowList_append_chains arrs) by auto.
      admit.
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id _ _).
      rewrite (ArrowList_id_right arrs) by auto.
      cat; simpl in *; repeat equalities.
    + rewrite (ArrowList_append_chains arrs) by auto.
      admit.
    + rewrite (ArrowList_append_chains arrs) by auto.
      admit.
Qed.

Theorem normalize_sound {p dom cod f} :
  Term_well_typed arrs dom cod p ->
  normalize_denote dom cod (normalize p) = Some f ->
  ∃ f', f ≈ f' ∧ denote dom cod p = Some f'.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; simpl in *; intros; equalities.
  - exists f; repeat equalities; reflexivity.
  - exists f.
    destruct (get_arr a); [|discriminate].
    repeat equalities; reflexivity.
  - apply normalize_compose in H0; equalities; subst.
    + destruct (Eq_eq_dec (ArrowList_dom arrs (normalize p1))
                          (TermCod arrs p2)).
      * rewrite <- e in *.
        destruct (IHp1 _ _ _ H1 a2), (IHp2 _ _ _ H2 b0).
        equalities.
        rewrite e3, e1.
        eexists; intuition.
        now rewrite <- e0, <- e2.
      * pose proof (ArrowList_normalize_dom_cod_sound arrs H2);
        equalities.
        now rewrite a1 in H3.
    + clear IHp1 IHp2.
      pose proof (ArrowList_normalize_dom_cod_sound arrs H1).
      pose proof (ArrowList_normalize_dom_cod_sound arrs H2).
      equalities.
      now rewrite H3.
Qed.

Theorem normalize_sound_r {p dom cod f} :
  Term_well_typed arrs dom cod p ->
  denote dom cod p = Some f ->
  ∃ f', f ≈ f' ∧ normalize_denote dom cod (normalize p) = Some f'.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; simpl in *; intros; equalities.
  - exists f; repeat equalities; reflexivity.
  - exists f.
    destruct (get_arr a); [|discriminate].
    repeat equalities; reflexivity.
  - destruct (denote (TermCod arrs p2) cod p1) eqn:?; [|discriminate].
    destruct (denote dom (TermCod arrs p2) p2) eqn:?; [|discriminate].
    destruct (IHp1 _ _ _ H1 Heqo), p; clear IHp1.
    destruct (IHp2 _ _ _ H2 Heqo0), p; clear IHp2.
    exists (x ∘ x0).
    split.
      inversion_clear H0; cat.
    admit.
Admitted.

(*
Lemma normalize_denote_append_some dom mid cod p1 p2 f g :
  normalize_denote mid cod p1 ≈ Some f ∧ normalize_denote dom mid p2 ≈ Some g ->
  normalize_denote dom cod (ArrowList_append p1 p2) ≈ Some (f ∘ g).
Proof.
  intros [].
  generalize dependent cod.
  generalize dependent dom.
  induction p1 using ArrowList_list_rect; simpl; intros.
  - destruct p2 using ArrowList_list_rect; simpl in *;
    revert e; revert e0;
    do 2 equalities'; repeat equalities; try reflexivity.
    + do 4 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction.
      rewrite <- e, <- e0; cat.
    + destruct (get_arr a); auto.
      revert e.
      revert e0.
      do 6 equalities'; repeat equalities; simpl_eq; auto.
      rewrite <- e; cat.
    + simpl_eq.
      destruct (normalize_denote_chain dom (arr_dom arrs a1) a2 l); auto.
      destruct (get_arr a1); auto.
      equalities.
      rewrite <- e; cat.
  - destruct p2 using ArrowList_list_rect; simpl in *;
    revert e; revert e0;
    do 2 equalities'; repeat equalities; try reflexivity.
    + do 4 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction;
      destruct (get_arr a); auto.
      equalities.
      rewrite <- e0; cat.
    + do 4 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction;
      destruct (get_arr a0); auto;
      destruct (get_arr a); auto; equalities.
      destruct e1.
      rewrite e, e0; reflexivity.
    + do 4 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction;
      destruct (get_arr a); auto;
      destruct (get_arr a1); auto;
      destruct (normalize_denote_chain dom (arr_dom arrs a1) a2 l);
      auto; equalities.
      destruct e1.
      rewrite e, e0; reflexivity.
  - destruct p2 using ArrowList_list_rect; simpl in *;
    revert e; revert e0;
    do 2 equalities'; repeat equalities; try reflexivity.
    + destruct (normalize_denote_chain mid (arr_dom arrs a1) a2 l);
      destruct (get_arr a1); auto.
      equalities; simpl_eq.
      rewrite <- e, <- e0; cat.
    + admit.
    + admit.
Admitted.

Lemma normalize_denote_append_none dom cod p1 p2 :
  normalize_denote dom cod p1 = None ∨ normalize_denote dom cod p2 = None ->
  normalize_denote dom cod (ArrowList_append p1 p2) ≈ None.
Proof.
  intros [].
  generalize dependent cod.
  generalize dependent dom.
  induction p1 using ArrowList_list_rect; simpl; intros.
  - revert e.
    do 2 equalities'; repeat equalities; try reflexivity.
    destruct p2; simpl.
    + do 2 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction.
    + destruct (normalize_denote_chain dom cod a l).
*)

Theorem denote_normalize {p dom cod} :
  (* Term_well_typed_bool arrs dom cod p = true -> *)
  denote dom cod p ≈ normalize_denote dom cod (normalize p).
Proof.
  destruct (denote dom cod p) eqn:?.
    destruct (normalize_denote dom cod (normalize p)) eqn:?.
      apply normalize_sound in Heqo0.
        destruct Heqo0.
        equalities.
        red.
        rewrite e0 in Heqo.
        rewrite e.
        now inversion_clear Heqo.
      now apply denote_well_typed in Heqo.
    admit.
  
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; intros.
  - repeat equalities; reflexivity.
  - simpl in *.
    destruct (get_arr a); auto.
    destruct s, s.
    simpl_eq.
    destruct p, p, e, e0.
    repeat destruct (Pos.eq_dec _ _); auto.
    destruct e, e0; cat.
  - simpl normalize.
    simpl denote.
    specialize (IHp1 (TermCod arrs p2) cod).
    specialize (IHp2 dom (TermCod arrs p2)).
    repeat destruct (denote _ _ _); symmetry.
Admitted.

Theorem normalize_apply dom cod : ∀ f g,
  Term_well_typed_bool arrs dom cod f = true ->
  Term_well_typed_bool arrs dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  denote dom cod f ≈ denote dom cod g.
Proof.
  intros.
  apply Term_well_typed_bool_sound in H.
  apply Term_well_typed_bool_sound in H0.
  pose proof (ArrowList_well_typed_sound arrs H).
  apply (ArrowList_beq_eq arrs) in H1.
  destruct (normalize_denote dom cod (normalize f)) eqn:?; try discriminate.
  destruct (normalize_sound H Heqo), p.
  rewrite e0; clear e0.
  rewrite H1 in Heqo; clear H1.
  destruct (normalize_sound H0 Heqo), p.
  rewrite e1; clear e1.
  red.
  rewrite <- e, <- e0.
  reflexivity.
Qed.

Corollary normalize_denote_terms dom cod : ∀ f g,
  Term_well_typed_bool arrs dom cod f = true ->
  Term_well_typed_bool arrs dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  normalize_denote dom cod (normalize f)
    ≈ normalize_denote dom cod (normalize g) ->
  denote dom cod f ≈ denote dom cod g.
Proof. intros; apply normalize_apply; auto. Qed.

Corollary normalize_denote_terms_impl dom cod : ∀ f g,
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f)
    ≈ normalize_denote dom cod (normalize g).
Proof.
  intros.
  apply (ArrowList_beq_eq arrs) in H.
  now rewrite H.
Qed.

End Denotation.

Section Rewriting.

Context (C : Category).

Variable objs : obj_idx -> C.
Variable arrs : arr_idx -> (obj_idx * obj_idx).
Variable get_arr : ∀ f : arr_idx,
  option (∃ x y, (arr_dom arrs f = x) ∧
                 (arr_cod arrs f = y) ∧ (objs x ~{C}~> objs y)).

Function substitute_subterm (e f : ArrowList)
         {measure ArrowList_length e} : option ArrowList :=
   match e, f with
   | ArrowChain x xs, ArrowChain y ys =>
     if Eq_eqb x y
     then match xs, ys with
          | nil, nil => Some (IdentityOnly (arr_cod arrs x))
          | x' :: xs', nil => Some (ArrowChain x' xs')
          | x' :: xs', y' :: ys' =>
            substitute_subterm (ArrowChain x' xs') (ArrowChain y' ys')
          | _, _ => None
          end
     else None
   | _, _ => None
   end.
Proof. simpl; intros; apply le_n_S, le_n. Defined.

Function substitute_term (e f t : ArrowList) {measure ArrowList_length e} :
  ArrowList :=
   match e, f with
   | ArrowChain x xs, ArrowChain y ys =>
     match substitute_subterm e f with
     | Some rest => ArrowList_append t rest
     | None =>
       match xs with
       | nil => e
       | cons x' xs' =>
         ArrowChain x (match substitute_term (ArrowChain x' xs') f t with
                       | IdentityOnly _  => nil
                       | ArrowChain z zs => z :: zs
                       end)
       end
     end
   | _, _ => e
   end.
Proof. simpl; intros; apply le_n_S, le_n. Defined.

Compute substitute_term
          (ArrowChain 10%positive [11; 12; 1; 2; 3; 16; 17; 18]%positive)
          (ArrowChain 1%positive [2; 3]%positive)
          (ArrowChain 4%positive [5; 6]%positive).

Definition ArrowList_equiv dom cod (f' g' : ArrowList) : Prop :=
  normalize_denote C objs arrs get_arr dom cod f' =
  normalize_denote C objs arrs get_arr dom cod g'.

Program Instance ArrowList_equiv_eqv dom cod :
  CRelationClasses.Equivalence (ArrowList_equiv dom cod).
Next Obligation.
  intros; unfold ArrowList_equiv in *; congruence.
Defined.
Next Obligation.
  intros; unfold ArrowList_equiv in *; congruence.
Defined.

Program Instance ArrowList_setoid dom cod : Setoid ArrowList := {
  equiv := ArrowList_equiv dom cod
}.

Program Instance normalize_denote_Proper dom cod :
  CMorphisms.Proper (ArrowList_equiv dom cod ==> equiv)
                    (normalize_denote C objs arrs get_arr dom cod).
Next Obligation.
  proper.
  unfold ArrowList_equiv in *.
  rewrite H.
  destruct (normalize_denote C objs arrs get_arr dom cod y); auto.
  reflexivity.
Defined.

Program Instance substitute_term_Proper dom cod dom' cod' :
  CMorphisms.Proper (ArrowList_equiv dom cod
                       ==> ArrowList_equiv dom' cod'
                       ==> ArrowList_equiv dom' cod'
                       ==> ArrowList_equiv dom cod)
                    substitute_term.
Next Obligation.
  proper.
Admitted.

(*
Lemma substitute_term_sound dom cod (f g : ArrowList) :
  ArrowList_beq f g ->
  (exists f, normalize_denote C objs arrs get_arr dom cod f' = Some f) ->
  (exists g, normalize_denote C objs arrs get_arr dom cod g' = Some g) ->
  ArrowList_equiv dom cod f' g' -> f' = g'.
Proof.
  intros.
  induction f' using ArrowList_list_rect.
  - destruct g' using ArrowList_list_rect;
    unfold ArrowList_equiv in H1;
    destruct H, H0;
    simpl in *.
    + equalities.
    + exfalso.
      destruct (get_arr a); [|discriminate].
      equalities.
      simpl_eq.
      destruct e.
      unfold 
  revert H.
  apply substitute_term_ind; intros; subst; try reflexivity.
  - assert (ArrowList_equiv dom cod (ArrowChain x xs) t).
    rewrite H.
    assert (ArrowList_equiv dom cod (ArrowChain x xs)
                            (ArrowList_append (ArrowChain y ys) rest)).
      clear H.
      destruct rest.
        rewrite (ArrowList_id_right arrs).
        admit.
        admit.
      rewrite (ArrowList_append_chains arrs).
      admit.
    rewrite substitute_subterm_equation in e3.
    destruct (Eq_eqb x y) eqn:?; [|discriminate].
    apply Eq_eqb_eq in Heqb; subst.
  - specialize (H H0).
    rewrite e5 in H; clear e5.
    admit.
  - specialize (H H0).
    rewrite e5 in H; clear e5.
    admit.
Abort.
*)

End Rewriting.

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
    constr:(Compose ft gt)
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let cn := lookupCat c cs in
      let fn := lookupArr c cs f in
      constr:(Morph fn)
    end
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

Definition convert_arr (C : Category) (dom cod : C) (fv : dom ~> cod)
           (objs : obj_idx -> C) (domi codi : obj_idx)
           (Hdomo : objs domi = dom) (Hcodo : objs codi = cod)
           (arrs : arr_idx -> (obj_idx * obj_idx)) (f : arr_idx) :
  option (∃ x y, (arr_dom arrs f = x) ∧ (arr_cod arrs f = y) ∧
                 (objs x ~{C}~> objs y)).
Proof.
  destruct (Eq_eq_dec (arr_dom arrs f) domi); [|exact None].
  destruct (Eq_eq_dec (arr_cod arrs f) codi); [|exact None].
  apply Some.
  exists domi, codi; subst; intuition idtac.
Defined.

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
                         @None (∃ x y, (arr_dom xyfun f = x) ∧
                                       (arr_cod xyfun f = y) ∧
                                       (ofun x ~{cat}~> ofun y))))
            end)
          ltac:(fun fi fv fk => match type of fv with
            | ?x ~{cat}~> ?y =>
              let xn := lookup x os in
              let yn := lookup y os in
              constr:((fun (f : arr_idx) =>
                         if (f =? fi)%positive
                         then convert_arr cat x y fv ofun xn yn
                                          eq_refl eq_refl xyfun f
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

Ltac reify_terms_and_then tacHyp tacGoal :=
  repeat match goal with
  | [ H : ?S ≈ ?T |- _ ] =>
    let cs  := allVars tt S in
    let cs  := allVars cs T in
    let r1  := reifyTerm cs S in
    let r2  := reifyTerm cs T in
    let env := build_env cs in
    let env := eval compute [Pos.succ TermDom TermCod] in env in
    match env with
    | (?cat, ?ofun, ?xyfun, ?ffun) =>
      change (denote cat ofun xyfun ffun
                     (TermDom xyfun r1) (TermCod xyfun r1) r1 ≈
              denote cat ofun xyfun ffun
                     (TermDom xyfun r2) (TermCod xyfun r2) r2) in H;
      cbv beta iota zeta delta [TermDom TermCod Pos.succ] in H;
      tacHyp env r1 r2 H;
      lazymatch type of H with
      | ?U ≈ ?V => change (term_wrapper (U ≈ V)) in H
      end
    end
  | [ |- ?S ≈ ?T ] =>
    let cs  := allVars tt S in
    let cs  := allVars cs T in
    let r1  := reifyTerm cs S in
    let r2  := reifyTerm cs T in
    let env := build_env cs in
    let env := eval compute [Pos.succ TermDom TermCod] in env in
    match env with
    | (?cat, ?ofun, ?xyfun, ?ffun) =>
      change (denote cat ofun xyfun ffun
                     (TermDom xyfun r1) (TermCod xyfun r1) r1 ≈
              denote cat ofun xyfun ffun
                     (TermDom xyfun r2) (TermCod xyfun r2) r2);
      cbv beta iota zeta delta [TermDom TermCod Pos.succ];
      tacGoal env r1 r2
    end
  end.

Ltac reify :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H => pose env; pose r1; pose r2; pose H)
    ltac:(fun env r1 r2   => pose env; pose r1; pose r2).

Ltac categorical :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H => idtac)
    ltac:(fun env r1 r2 =>
      match env with
      | (?cat, ?ofun, ?xyfun, ?ffun) =>
        apply (normalize_apply cat ofun xyfun ffun
                               (TermDom xyfun r1) (TermCod xyfun r1) r1 r2);
        vm_compute; reflexivity
      end).

Ltac normalize :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H =>
      match env with
      | (?cat, ?ofun, ?xyfun, ?ffun) =>
        let H1 := fresh "H" in
        assert (H1 : ArrowList_beq (normalize r1) (normalize r2) = true)
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
  (* reify. *)
  Time normalize.               (* 0.315s *)
  Time categorical.             (* 0.45s *)
Qed.

(* Ltac cat_rewrite H := *)

Print Assumptions sample_2.

Require Import Category.Theory.Adjunction.

Local Obligation Tactic :=
  cat_simpl; proper; simpl in *;
  try erewrite !normalize_denormalize; eauto;
  try (eapply ArrowList_append_well_typed;
       [ eapply ArrowList_well_typed_dom
       | eapply ArrowList_well_typed_cod | | ]); eauto.

Hint Resolve ArrowList_well_typed_sound.
Hint Resolve denormalize_well_typed.

(* This adjunction establishes that Term is our free category, with ArrowList
   equivalent up to normalization of terms with a canonical mapping back into
   Term by "denormalization".

   Since the objects of both categories are the same, the monad this gives
   rise to is uninteresting. *)
Program Instance Term_ArrowList_Adjunction
        (arr_def : arr_idx → obj_idx ∧ obj_idx) :
  ArrowList_to_Term arr_def ⊣ Term_to_ArrowList arr_def := {
  adj := fun x y =>
    {| to   := {| morphism := fun f => (normalize (_ f); _) |}
     ; from := {| morphism := _ |} |}
}.

Print Assumptions Term_ArrowList_Adjunction.

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

Generalizable All Variables.

Ltac simpl_eq :=
  repeat unfold eq_rect_r, eq_rect, eq_ind_r, eq_ind, eq_sym,
                prod_rect in *.

Open Scope lazy_bool_scope.

Definition rev_list_rect (A : Type) (P : list A → Type) (H : P [])
           (H0 : ∀ (a : A) (l : list A), P (rev l) → P (rev (a :: l)))
           (l : list A) : P (rev l) :=
  list_rect (λ l0 : list A, P (rev l0)) H
            (λ (a : A) (l0 : list A) (IHl : P (rev l0)), H0 a l0 IHl) l.

Definition rev_rect (A : Type) (P : list A → Type)
           (H : P []) (H0 : ∀ (x : A) (l : list A), P l → P (l ++ [x]))
           (l : list A) : P l :=
  (λ E : rev (rev l) = l,
     eq_rect (rev (rev l)) (λ l0 : list A, P l0)
        (rev_list_rect A P H
        (λ (a : A) (l0 : list A) (H1 : P (rev l0)), H0 a (rev l0) H1)
        (rev l)) l E) (rev_involutive l).

Lemma last_rcons A (x y : A) l :
  last (l ++ [x]) y = x.
Proof.
  induction l; simpl.
    reflexivity.
  rewrite IHl; clear IHl.
  destruct l; auto.
Qed.

Lemma last_app_cons A (x : A) xs y ys :
  last (xs ++ y :: ys) x = last (y :: ys) x.
Proof.
  generalize dependent y.
  generalize dependent xs.
  induction ys using rev_ind; simpl; intros.
    apply last_rcons.
  rewrite last_rcons.
  rewrite app_comm_cons.
  rewrite app_assoc.
  rewrite last_rcons.
  destruct ys; auto.
Qed.

Lemma last_cons A (x : A) y ys :
  last (y :: ys) x = last ys y.
Proof.
  generalize dependent x.
  induction ys using rev_ind; simpl; intros.
    reflexivity.
  rewrite !last_rcons.
  destruct ys; auto.
Qed.

Lemma match_last {A} {a : A} {xs x} :
  match xs with
  | [] => a
  | _ :: _ => last xs x
  end = last xs a.
Proof.
  induction xs; auto.
  rewrite !last_cons; reflexivity.
Qed.

Lemma Forall_app {A} p (l1 l2: list A) :
  Forall p (l1 ++ l2) <-> (Forall p l1 /\ Forall p l2).
Proof.
  intros.
  rewrite !Forall_forall.
  split; intros.
    split; intros;
    apply H; apply in_or_app.
      left; trivial.
    right; trivial.
  apply in_app_or in H0.
  destruct H, H0; eauto.
Qed.

Lemma last_Forall A (x y : A) l P :
  last l x = y -> Forall P l -> P x -> P y.
Proof.
  generalize dependent x.
  destruct l using rev_ind; simpl; intros.
    now subst.
  rewrite last_rcons in H; subst.
  apply Forall_app in H0.
  destruct H0.
  now inversion H0.
Qed.

Fixpoint list_beq {A : Type} (eq_A : A → A → bool) (X Y : list A)
         {struct X} : bool :=
  match X with
  | [] => match Y with
          | [] => true
          | _ :: _ => false
          end
  | x :: x0 =>
      match Y with
      | [] => false
      | x1 :: x2 => eq_A x x1 &&& list_beq eq_A x0 x2
      end
  end.

Lemma list_beq_eq {A} (R : A -> A -> bool) xs ys :
  (∀ x y, R x y = true -> x = y) ->
  list_beq R xs ys = true -> xs = ys.
Proof.
  generalize dependent ys.
  induction xs; simpl; intros.
    destruct ys; congruence.
  destruct ys.
    discriminate.
  destruct (R a a0) eqn:Heqe.
    apply H in Heqe; subst.
    erewrite IHxs; eauto.
  discriminate.
Qed.

Lemma list_beq_refl {A} (R : A -> A -> bool) xs :
  (∀ x, R x x = true) -> list_beq R xs xs = true.
Proof.
  intros.
  induction xs; auto; simpl.
  now rewrite H.
Qed.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Qed.

Lemma Nat_eq_dec' : ∀ (x y : nat), x = y \/ x ≠ y.
Proof. intros; destruct (Nat.eq_dec x y); auto. Qed.

Lemma Nat_eq_dec_refl (x : nat) :
  Nat.eq_dec x x = left (@eq_refl (nat) x).
Proof.
  destruct (Nat.eq_dec x x); [| contradiction].
  refine (K_dec_on_type (nat) x (Nat_eq_dec' x)
            (fun H => @left _ _ H = @left _ _ (@eq_refl (nat) x)) _ _); auto.
Qed.

Lemma Nat_eqb_refl (x : nat) : Nat.eqb x x = true.
Proof. now apply Nat.eqb_eq. Qed.

Lemma Pos_eq_dec' : ∀ x y : positive, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Pos.eq_dec x y); auto.
Qed.

Lemma Pos_eq_dec_refl n : Pos.eq_dec n n = left (@eq_refl positive n).
Proof.
  destruct (Pos.eq_dec n n).
    refine (K_dec_on_type positive n (Pos_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl positive n)) _ _).
    reflexivity.
  contradiction.
Qed.

Fixpoint Pos_eqb_refl (x : positive) : Pos.eqb x x = true :=
  match x with
  | xI x => Pos_eqb_refl x
  | xO x => Pos_eqb_refl x
  | xH => eq_refl
  end.

Definition nth_safe {a} (xs : list a) (n : nat) (H : (n < length xs)%nat) : a.
Proof.
  induction xs; simpl in *; auto.
  contradiction (Nat.nlt_0_r n).
Defined.

Definition nth_pos {a} (xs : list a) (n : positive) (default : a) : a.
Proof.
  generalize dependent n.
  induction xs; intros.
    exact default.
  destruct n using Pos.peano_rect.
    exact a0.
  exact (IHxs n).
Defined.

Definition within_bounds {A} (x : positive) (xs : list A) : Prop :=
  (Nat.pred (Pos.to_nat x) < length xs)%nat.

Definition Pos_to_fin {n} (x : positive) :
  (Nat.pred (Pos.to_nat x) < n)%nat -> Fin.t n := Fin.of_nat_lt.

Definition nth_pos_bounded {a} (xs : list a) (n : positive)
           (H : within_bounds n xs) : a.
Proof.
  generalize dependent n.
  induction xs; intros.
    unfold within_bounds in H; simpl in H; omega.
  destruct n using Pos.peano_rect.
    exact a0.
  clear IHn.
  apply IHxs with (n:=n).
  unfold within_bounds in *.
  simpl in H.
  rewrite Pos2Nat.inj_succ in H.
  simpl in H.
  apply lt_S_n.
  rewrite Nat.succ_pred_pos; auto.
  apply Pos2Nat.is_pos.
Defined.

Lemma Fin_eq_dec' : ∀ n (x y : Fin.t n), x = y \/ x ≠ y.
Proof. intros; destruct (Fin.eq_dec x y); auto. Qed.

Lemma Fin_eq_dec_refl n (x : Fin.t n) :
  Fin.eq_dec x x = left (@eq_refl (Fin.t n) x).
Proof.
  destruct (Fin.eq_dec x x).
    refine (K_dec_on_type (Fin.t n) x (Fin_eq_dec' n x)
              (fun H => @left _ _ H = @left _ _ (@eq_refl (Fin.t n) x)) _ _).
    reflexivity.
  contradiction.
Qed.

Fixpoint Fin_eqb_refl n (x : Fin.t n) : Fin.eqb x x = true :=
  match x with
  | @Fin.F1 m'    => Nat_eqb_refl m'
  | @Fin.FS n0 p' => Fin_eqb_refl n0 _
  end.

Lemma Fin_eqb_eq n (x y : Fin.t n) (H : Fin.eqb x y = true) : x = y.
Proof.
  induction x.
    revert H.
    apply Fin.caseS with (p:=y); intros; eauto.
    simpl in H; discriminate.
  revert H.
  apply Fin.caseS' with (p:=y); intros; eauto.
    simpl in H; discriminate.
  simpl in H.
  f_equal.
  now apply IHx.
Defined.

Import EqNotations.

Fixpoint nth_fin {a} (xs : list a) (n : Fin.t (length xs)) : a :=
  match xs as xs' return length xs = length xs' -> a with
  | nil => fun H => Fin.case0 _ (rew H in n)
  | cons x xs' => fun H =>
    match n in Fin.t n' return length xs = n' -> a with
    | Fin.F1 => fun _ => x
    | @Fin.FS n0 x => fun H0 =>
        nth_fin
          xs' (rew (eq_add_S n0 (length xs')
                             (rew [fun n => n = S (length xs')] H0 in H)) in x)
    end eq_refl
  end eq_refl.

Class Equality (A : Type) := {
  Eq_eq := @eq A;
  Eq_eq_refl x := eq_refl;

  Eq_eqb : A -> A -> bool;
  Eq_eqb_refl x : Eq_eqb x x = true;

  Eq_eqb_eq x y : Eq_eqb x y = true -> x = y;

  Eq_eq_dec  (x y : A) : { x = y } + { x ≠ y };
  Eq_eq_dec_refl x : Eq_eq_dec x x = left (@Eq_eq_refl x)
}.

Program Instance Pos_Eq : Equality positive := {
  Eq_eqb         := Pos.eqb;
  Eq_eqb_refl    := Pos_eqb_refl;

  Eq_eqb_eq x y  := proj1 (Pos.eqb_eq x y);

  Eq_eq_dec      := Pos.eq_dec;
  Eq_eq_dec_refl := Pos_eq_dec_refl
}.

Program Instance Fin_Eq (n : nat) : Equality (Fin.t n) := {
  Eq_eqb         := Fin.eqb;
  Eq_eqb_refl    := Fin_eqb_refl n;

  Eq_eqb_eq x y  := proj1 (Fin.eqb_eq n x y);

  Eq_eq_dec      := Fin.eq_dec;
  Eq_eq_dec_refl := Fin_eq_dec_refl n
}.

Program Instance option_Eq `{Equality A} : Equality (option A) := {
  Eq_eqb         := _;
  Eq_eqb_refl x  := _;

  Eq_eqb_eq x y  := _;

  Eq_eq_dec      := _;
  Eq_eq_dec_refl := _
}.
Next Obligation.
  destruct X.
    destruct X0.
      exact (Eq_eqb a a0).
    exact false.
  destruct X0.
    exact false.
  exact true.
Defined.
Next Obligation.
  destruct x; simpl; auto.
  apply Eq_eqb_refl.
Defined.
Next Obligation.
  destruct x, y; simpl in H0.
  - now apply Eq_eqb_eq in H0; subst.
  - discriminate.
  - discriminate.
  - reflexivity.
Defined.
Next Obligation.
  destruct x, y.
  - destruct (Eq_eq_dec a a0); subst.
      left; reflexivity.
    right; intros.
    inversion H0.
    contradiction.
  - right; intros; discriminate.
  - right; intros; discriminate.
  - left; reflexivity.
Defined.
Next Obligation.
  destruct x; simpl; auto.
  rewrite Eq_eq_dec_refl.
  unfold eq_rec_r, eq_rec; simpl_eq.
  remember (Eq_eq_refl a) as p.
  clear -p.
Admitted.

Program Instance list_Eq `{Equality A} : Equality (list A) := {
  Eq_eqb         := list_beq Eq_eqb;
  Eq_eqb_refl x  := list_beq_refl Eq_eqb x Eq_eqb_refl;

  Eq_eqb_eq x y  := list_beq_eq Eq_eqb x y Eq_eqb_eq;

  Eq_eq_dec      := list_eq_dec Eq_eq_dec;
  Eq_eq_dec_refl := _
}.
Next Obligation.
  induction x; simpl; auto.
  unfold sumbool_rec, sumbool_rect.
  rewrite Eq_eq_dec_refl, IHx.
  reflexivity.
Qed.

Program Instance prod_Eq `{Equality A} `{Equality B} : Equality (prod A B) := {
  Eq_eqb           := prod_eqb Eq_eqb Eq_eqb;
  Eq_eqb_refl      := _;

  Eq_eqb_eq x y    := _;

  Eq_eq_dec        := prod_eq_dec Eq_eq_dec Eq_eq_dec;
  Eq_eq_dec_refl x := prod_eq_dec_refl _ _ x Eq_eq_dec Eq_eq_dec
}.
Next Obligation.
  unfold prod_eqb; simpl.
  now rewrite !Eq_eqb_refl.
Defined.
Next Obligation.
  unfold prod_eqb in H1; simpl in H1.
  apply andb_true_iff in H1.
  destruct H1.
  apply Eq_eqb_eq in H1.
  apply Eq_eqb_eq in H2.
  now subst.
Defined.

Ltac equalities' :=
  match goal with
  | [ H : (_ &&& _) = true |- _ ]      => rewrite <- andb_lazy_alt in H
  | [ |- (_ &&& _) = true ]            => rewrite <- andb_lazy_alt
  | [ H : (_ && _) = true |- _ ]       => apply andb_true_iff in H
  | [ |- (_ && _) = true ]             => apply andb_true_iff; split
  | [ H : _ /\ _ |- _ ]                => destruct H
  | [ H : _ ∧ _ |- _ ]                 => destruct H
  | [ H : ∃ _, _ |- _ ]                => destruct H

  | [ H : context[Pos.eq_dec ?N ?M] |- _ ] =>
    replace (Pos.eq_dec N M) with (Eq_eq_dec N M) in H
  | [ |- context[Pos.eq_dec ?N ?M] ] =>
    replace (Pos.eq_dec N M) with (Eq_eq_dec N M)
  | [ H : context[(?N =? ?M)%positive] |- _ ] =>
    replace ((N =? M)%positive) with (Eq_eqb N M) in H
  | [ |- context[(?N =? ?M)%positive] ] =>
    replace ((N =? M)%positive) with (Eq_eqb N M)

  | [ H : context[@Fin.eq_dec ?N ?X ?Y] |- _ ] =>
    replace (@Fin.eq_dec N X Y) with (Eq_eq_dec X Y) in H
  | [ |- context[Fin.eq_dec ?N ?X ?Y] ] =>
    replace (@Fin.eq_dec N X Y) with (Eq_eq_dec X Y)
  | [ H : context[@Fin.eqb ?N ?X ?Y] |- _ ] =>
    replace (@Fin.eqb ?N ?X ?Y) with (Eq_eqb X Y) in H
  | [ |- context[@Fin.eqb ?N ?X ?Y] ] =>
    replace (@Fin.eqb ?N ?X ?Y) with (Eq_eqb X Y)

  | [ |- Eq_eqb ?X ?X = true ]     => apply Eq_eqb_refl
  | [ H : Eq_eqb _ _ = true |- _ ] => apply Eq_eqb_eq in H
  | [ |- Eq_eqb _ _ = true ]       => apply Eq_eqb_eq

  | [ H : context[match Eq_eq_dec ?X ?X with _ => _ end] |- _ ] =>
    rewrite (Eq_eq_dec_refl X) in H
  | [ |- context[match Eq_eq_dec ?X ?X with _ => _ end] ] =>
    rewrite (Eq_eq_dec_refl X)
  | [ H : context[match Eq_eq_dec ?X ?Y with _ => _ end] |- _ ] =>
    destruct (Eq_eq_dec X Y); subst
  | [ |- context[match Eq_eq_dec ?X ?Y with _ => _ end] ] =>
    destruct (Eq_eq_dec X Y); subst

  | [ H : list_beq _ _ _ = true |- _ ] => apply list_beq_eq in H
  | [ |- list_beq _ _ _ = true ]       => apply list_beq_eq
  end.

Ltac equalities :=
  try equalities';
  repeat (
    equalities';
    subst; simpl; auto;
    try discriminate;
    try tauto;
    try intuition idtac;
    subst; simpl; auto).

Set Universe Polymorphism.

Program Instance option_setoid `{Setoid A} : Setoid (option A) := {
  equiv := fun x y => match x, y with
    | Some x, Some y => x ≈ y
    | None, None => True
    | _, _ => False
    end
}.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation.
  equivalence.
  - destruct x; reflexivity.
  - destruct x, y; auto.
    symmetry; auto.
  - destruct x, y, z; auto.
      transitivity a0; auto.
    contradiction.
Qed.

Unset Universe Polymorphism.

Section Representation.

Definition cat_idx := positive.
Definition obj_idx := positive.
Definition arr_idx := positive.

Variable arr_def : arr_idx -> (obj_idx * obj_idx).

Definition arr_dom (f : arr_idx) : obj_idx := fst (arr_def f).
Definition arr_cod (f : arr_idx) : obj_idx := snd (arr_def f).

(* This describes the morphisms of a magmoid, which forms a quotient category
   under denotation. *)
Inductive Term : obj_idx -> obj_idx-> Set :=
  | Identity (o : obj_idx) : Term o o
  | Morph    x y (a : arr_idx) : Term x y
  | Compose x y z (f : Term y z) (g : Term x y) : Term x z.

Definition TermDom `(e : Term a b) : obj_idx := a.
Definition TermCod `(e : Term a b) : obj_idx := b.

End Representation.

Section Normalization.

Variable arrs : arr_idx -> (obj_idx * obj_idx).

Notation arr_dom := (arr_dom arrs).
Notation arr_cod := (arr_cod arrs).

Notation Term    := (Term arrs).
Notation TermDom := (TermDom arrs).
Notation TermCod := (TermCod arrs).

(* This describes the morphisms of a path, or free, category over a quiver of
   Arrows, while our environment describes a quiver (where vertices are all
   object indices, and edges are all arrow indices associated pairs of object
   indices). The denotation of an ArrowList to some category C is a forgetful
   functor from the path category over this quiver to C. Note that this
   functor is only total if the denotation of the quiver itself is total. *)
Inductive ArrowList : Set :=
  | IdentityOnly (o : obj_idx) : ArrowList
  | ArrowChain (a : arr_idx) : ArrowList -> ArrowList.

Function ArrowList_beq (xs ys : ArrowList) : bool :=
  match xs, ys with
  | IdentityOnly o1, IdentityOnly o2 => Eq_eqb o1 o2
  | ArrowChain a1 xs1, ArrowChain a2 ys2 =>
    Eq_eqb a1 a2 &&& ArrowList_beq xs1 ys2
  | _, _ => false
  end.

Fixpoint ArrowList_beq_eq x y :
  ArrowList_beq x y = true <-> x = y.
Proof.
  destruct x, y; simpl; split; intros;
  equalities; try discriminate.
  - inversion_clear H.
    now apply Eq_eqb_refl.
  - now apply ArrowList_beq_eq in H1; subst.
  - equalities.
    inversion_clear H.
    now apply Eq_eqb_refl.
  - inversion_clear H.
    now apply ArrowList_beq_eq.
Qed.

Function ArrowList_to_list (xs : ArrowList) : list arr_idx * obj_idx :=
  match xs with
  | IdentityOnly x => ([], x)
  | ArrowChain f fs =>
    match ArrowList_to_list fs with
    | (fs, dom) => (f :: fs, dom)
    end
  end.

Function ArrowList_from_list (xs : list arr_idx) (x : obj_idx) : ArrowList :=
  match xs with
  | nil => IdentityOnly x
  | f :: fs => ArrowChain f (ArrowList_from_list fs x)
  end.

Lemma ArrowList_to_from_list xs x :
  ArrowList_to_list (ArrowList_from_list xs x) = (xs, x).
Proof.
  induction xs; simpl; auto.
  now rewrite IHxs.
Defined.

Lemma ArrowList_from_to_list xs :
  let '(x, y) := ArrowList_to_list xs in
  ArrowList_from_list x y = xs.
Proof.
  induction xs; simpl; intros; subst; auto.
  destruct (ArrowList_to_list xs); simpl in *.
  now rewrite IHxs.
Defined.

Definition ArrowList_cod (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain f _ => arr_cod f
  end.

Function ArrowList_dom (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain _ xs => ArrowList_dom xs
  end.

Inductive ForallAligned : list Arrow → Prop :=
    Align_nil : ForallAligned []
  | Align_singleton : ∀ (a : Arrow), ForallAligned [a]
  | Align_cons2 : ∀ (a b : Arrow) (l : list Arrow),
      arr_dom a = arr_cod b ->
      ForallAligned (b :: l) → ForallAligned (a :: b :: l).

Lemma ForallAligned_inv {x xs y} :
  ForallAligned (x :: y :: xs)
    -> arr_dom x = arr_cod y /\
       ForallAligned (y :: xs).
Proof.
  generalize dependent x.
  generalize dependent y.
  induction xs; intros;
  inversion H; subst; intuition.
Qed.

Lemma ForallAligned_app {x xs y ys} :
  ForallAligned (x :: xs ++ y :: ys)
    <-> ForallAligned (x :: xs) /\ ForallAligned (y :: ys) /\
        arr_cod y = arr_dom (last xs x).

Definition ListOfArrows_rect : ∀ (P : Arrow -> list Arrow → Type),
  (∀ (x : Arrow), P x []) →
  (∀ (x y : Arrow) (l : list Arrow), P y l → P x (y :: l)) →
  ∀ (x : Arrow) (l : list Arrow), P x l.
Proof.
  intros.
  generalize dependent x.
  induction l; auto.
Defined.

Definition ArrowList_append (xs ys : ArrowList) : ArrowList :=
  match xs, ys with
  | IdentityOnly f,  IdentityOnly g  => IdentityOnly g
  | IdentityOnly f,  ArrowChain g xs => ArrowChain g xs
  | ArrowChain f xs, IdentityOnly g  => ArrowChain f xs
  | ArrowChain f xs, ArrowChain g ys => ArrowChain f (xs ++ g :: ys)
  end.

Lemma ArrowList_append_chains a a0 l l0 :
  ArrowList_dom (ArrowChain a l) = ArrowList_cod (ArrowChain a0 l0) ->
  ArrowList_append (ArrowChain a l) (ArrowChain a0 l0) =
  ArrowChain a (l ++ a0 :: l0).
Proof.
  generalize dependent a0.
  generalize dependent l0.
  simpl.
  induction l using rev_ind; simpl; intros; auto.
Qed.

Lemma ArrowList_append_well_typed {dom mid cod f1 f2} :
  ArrowList_dom f1 = mid ->
  ArrowList_cod f2 = mid ->
  ArrowList_well_typed mid cod f1 ->
  ArrowList_well_typed dom mid f2 ->
    ArrowList_well_typed dom cod (ArrowList_append f1 f2).
Proof.
  generalize dependent mid.
  generalize dependent f2.
  induction f1 using ArrowList_list_rect; intros.
  - simpl in *.
    equalities; subst.
    destruct f2 using ArrowList_list_rect; simpl in *; auto.
  - simpl in *; equalities; subst.
    destruct f2.
      simpl in *; subst; intuition.
    simpl in *; equalities.
    + induction l using rev_ind.
        simpl in *; equalities.
        inversion H2; subst.
        now inversion H.
      rewrite !last_app_cons in *; simpl in *.
      replace (match l ++ [x] with
               | [] => a0
               | _ :: _ => x
               end) with x by (destruct l; auto); auto.
    + constructor; auto.
  - clear IHf1.
    equalities; subst.
    destruct f2.
      constructor; simpl in H1; intuition.
      simpl in *; subst; intuition.
    rewrite ArrowList_append_chains by congruence.
    simpl; constructor.
      simpl in H1; intuition.
    rewrite last_app_cons, last_cons.
    pose proof (ArrowList_well_typed_dom H2) as H5.
    simpl in H5.
    replace (match l ++ a :: l0 with
             | [] => a2
             | _ :: _ => last l0 a
             end) with (last l0 a) by (destruct l; auto);
    intuition; rewrite !app_comm_cons.
    apply ForallAligned_app.
    inversion H1.
    inversion H2.
    intuition.
Qed.

Fixpoint normalize `(p : Term a b) : ArrowList :=
  match p with
  | Identity _ x        => IdentityOnly x
  | Morph _ f           => ArrowChain f []
  | Compose _ x y z f g => ArrowList_append (normalize f) (normalize g)
  end.

Lemma ArrowList_append_dom f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_dom (ArrowList_append f g) = ArrowList_dom g.
Proof.
  destruct g, f; simpl; intros; auto.
  now rewrite last_app_cons, last_cons.
Qed.

Lemma ArrowList_append_cod f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_cod (ArrowList_append f g) = ArrowList_cod f.
Proof.
  destruct f, g; simpl; intros; auto.
Qed.

(*
Lemma ArrowList_normalize_dom_cod_sound {p dom cod} :
  Term_well_typed dom cod p ->
  ArrowList_dom (normalize p) = dom /\
  ArrowList_cod (normalize p) = cod.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros; intuition; subst;
  rewrite H0 in H;
  rewrite ArrowList_append_dom ||
  rewrite ArrowList_append_cod; auto;
  specialize (IHp1 _ _ H);
  specialize (IHp2 _ _ H2);
  intuition; congruence.
Qed.

Corollary ArrowList_specific_sound p :
  Term_well_typed (TermDom p) (TermCod p) p ->
  ArrowList_dom (normalize p) = TermDom p /\
  ArrowList_cod (normalize p) = TermCod p.
Proof. apply ArrowList_normalize_dom_cod_sound. Qed.
*)

Lemma ArrowList_id_left x y :
  ArrowList_append (IdentityOnly x) y = y.
Proof.
  simpl.
  destruct y; simpl; intros; subst; auto.
Qed.

Lemma ArrowList_id_right f y :
  ArrowList_dom f = y ->
  ArrowList_append f (IdentityOnly y) = f.
Proof.
  destruct f; simpl; intros; subst; auto.
Qed.

Lemma ArrowList_append_assoc x y z :
  ArrowList_append (ArrowList_append x y) z =
  ArrowList_append x (ArrowList_append y z).
Proof.
  destruct x, y, z; simpl; auto; intros;
  try destruct a;
  try destruct a0; subst; auto;
  now rewrite <- app_assoc.
Qed.

(* We show here that ArrowList morphisms are just one way of representing a
   free category. However, we still forget identities and which way
   composition was associated, so really it's a normalized free category. *)
Program Definition ArrowList_Category : Category := {|
  obj := obj_idx;
  hom := fun x y =>
    ∃ l : ArrowList, ArrowList_well_typed x y l;
  homset := fun x y => {| equiv := fun f g => `1 f = `1 g |};
  id := fun x => (IdentityOnly x; _);
  compose := fun _ _ _ f g => (ArrowList_append (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left y (`1 f);
  id_right := fun x _ f => ArrowList_id_right (`1 f) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc (`1 f) (`1 g) (`1 h)
|}.
Next Obligation. equivalence; simpl in *; congruence. Qed.
Next Obligation.
  pose proof (ArrowList_well_typed_dom X0).
  pose proof (ArrowList_well_typed_cod X).
  eapply ArrowList_append_well_typed; eauto.
Qed.
Next Obligation. proper; simpl in *; subst; reflexivity. Qed.
Next Obligation.
  now apply ArrowList_well_typed_dom in X.
Qed.
Next Obligation. apply ArrowList_append_assoc; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.

(* In the category whose morphisms are Terms, homset equivalence is up to
   normalized terms. *)
Program Definition Term_Category : Category := {|
  obj := obj_idx;
  hom := Term;
  homset := fun x y => {| equiv := fun f g => normalize f = normalize g |};
  id := Identity arrs;
  compose := fun x y z f g => Compose arrs x y z f g;
  id_left := fun _ y f => ArrowList_id_left y (normalize f);
  id_right := fun x _ f => ArrowList_id_right (normalize f) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc (normalize f) (normalize g) (normalize h)
|}.
Next Obligation.
  pose proof (Term_well_typed_dom arrs X).
  pose proof (Term_well_typed_dom arrs X0).
  pose proof (Term_well_typed_cod arrs X).
  pose proof (Term_well_typed_cod arrs X0).
  destruct f, g; simpl in *; intuition idtac; congruence.
Qed.
Next Obligation.
  eapply ArrowList_normalize_dom_cod_sound; eauto.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.

Lemma ArrowList_well_typed_sound {f dom cod} :
  Term_well_typed dom cod f
    -> ArrowList_well_typed dom cod (normalize f).
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction f; simpl; intros; intuition.
    constructor; constructor.
  specialize (IHf1 _ _ H).
  specialize (IHf2 _ _ H2).
  pose proof (ArrowList_well_typed_dom IHf1).
  pose proof (ArrowList_well_typed_cod IHf2).
  apply (ArrowList_append_well_typed H1 H3 IHf1 IHf2).
Qed.

Set Transparent Obligations.

Program Instance Term_to_ArrowList :
  Term_Category ⟶ ArrowList_Category := {
  fobj := fun x => x;
  fmap := fun x y f => (normalize _; _)
}.
Next Obligation. now apply ArrowList_well_typed_sound. Qed.

Fixpoint denormalize (f : ArrowList) : Term :=
  match f with
  | IdentityOnly x => Identity x
  | ArrowChain f xs =>
    fold_left (fun acc x => (fun y => Compose y x) \o acc)
              (map Morph xs) Datatypes.id (Morph f)
  end.

Lemma normalize_denormalize {dom cod f} :
  ArrowList_well_typed dom cod f
    -> normalize (denormalize f) = f.
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros; auto.
  rewrite <- ArrowList_append_chains at 2.
  - rewrite <- (IHl (arr_cod x)); clear IHl.
    + simpl.
      now rewrite map_app, fold_left_app.
    + simpl in H |- *;
      equalities.
      * rewrite app_comm_cons in H1.
        now apply ForallAligned_app in H1.
      * rewrite app_comm_cons in H1.
        now apply ForallAligned_app in H1.
  - simpl in *; equalities.
    rewrite app_comm_cons in H1.
    now apply ForallAligned_app in H1.
Qed.

Theorem denormalize_well_typed dom cod f :
  ArrowList_well_typed dom cod f
    -> Term_well_typed dom cod (denormalize f).
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros.
    simpl in *; intuition.
  assert (ArrowList_well_typed
            (arr_cod x) cod (ArrowChain a l)). {
    clear IHl.
    simpl in *; equalities.
    - rewrite app_comm_cons in H1.
      now apply ForallAligned_app in H1.
    - rewrite app_comm_cons in H1.
      now apply ForallAligned_app in H1.
  }
  rewrite <- ArrowList_append_chains by (simpl in *; intuition).
  specialize (IHl (arr_cod x) a H0).
  simpl in *; equalities.
  rewrite app_comm_cons in H4.
  apply ForallAligned_app in H4; equalities.
  rewrite map_app, fold_left_app; simpl.
  rewrite H4.
  intuition; subst.
  - clear -H.
    induction l using rev_ind; simpl; auto.
    rewrite map_app, fold_left_app; simpl.
    now rewrite last_rcons in *.
  - now rewrite H4 in IHl.
  - now rewrite last_rcons.
Qed.

Program Instance ArrowList_to_Term :
  ArrowList_Category ⟶ Term_Category := {
  fobj := fun x => x;
  fmap := fun x y f => (denormalize (`1 f); _)
}.
Next Obligation. apply denormalize_well_typed; auto. Qed.
Next Obligation.
  proper.
  simpl in *; subst.
  reflexivity.
Qed.
Next Obligation.
  erewrite !normalize_denormalize; eauto.
  pose proof (ArrowList_well_typed_dom X0).
  pose proof (ArrowList_well_typed_cod X).
  eapply ArrowList_append_well_typed; eauto.
Qed.

Fixpoint ArrowList_from_list (xs : obj_idx * list Arrow) : ArrowList :=
  match xs with
  | (x, nil) => IdentityOnly x
  | (_, x :: xs) => ArrowChain x xs
  end.

Lemma ArrowList_to_from_list xs :
  ArrowList_to_list (ArrowList_from_list xs) = xs.
Proof.
  destruct xs.
  induction l; simpl; auto.
  simpl in IHl.
  f_equal.
  destruct l; simpl in *.
    admit.
  inversion_clear IHl.
  destruct l; auto.
  f_equal.
  f_equal.
Abort.

Definition ArrowList_length (x : ArrowList) : nat :=
  match x with
  | IdentityOnly x => 0
  | ArrowChain x xs => 1 + length xs
  end.

Function ArrowList_beqn (n : nat) (x y : ArrowList) : bool :=
  match n with
  | O => true
  | S n' =>
    match x, y with
    | IdentityOnly cod1, IdentityOnly cod2 => Eq_eqb cod1 cod2
    | ArrowChain x1 nil, ArrowChain x2 (_ :: _) =>
      match n' with
      | O => Eq_eqb x1 x2
      | S x => false
      end
    | ArrowChain x1 (_ :: _), ArrowChain x2 nil =>
      match n' with
      | O => Eq_eqb x1 x2
      | S x => false
      end
    | ArrowChain x1 (y1 :: ys1), ArrowChain x2 (y2 :: ys2) =>
      Eq_eqb x1 x2 &&&
      ArrowList_beqn n' (ArrowChain y1 ys1) (ArrowChain y2 ys2)
    | _, _ => false
    end
  end.

Function ArrowList_drop (n : nat) (xs : ArrowList) : ArrowList :=
  match n with
  | O => xs
  | S n' =>
    match xs with
    | IdentityOnly o => IdentityOnly o
    | ArrowChain f nil => IdentityOnly (arr_cod f)
    | ArrowChain f (x :: xs) => ArrowList_drop n' (ArrowChain x xs)
    end
  end.

End Normalization.

Section Denotation.

Set Transparent Obligations.

Context (C : Category).

Variable objs : obj_idx -> C.
Variable arrs : arr_idx -> (obj_idx * obj_idx).
Variable get_arr : ∀ f : arr_idx,
  option (∃ x y, (arr_dom arrs f = x) ∧
                 (arr_cod arrs f = y) ∧ (objs x ~{C}~> objs y)).

Fixpoint denote dom cod (e : Term) : option (objs dom ~{C}~> objs cod) :=
  match e with
  | Identity o =>
    match Eq_eq_dec o dom, Eq_eq_dec o cod with
    | left edom, left ecod =>
      Some (rew [fun x => objs x ~{ C }~> objs cod] edom in
            rew [fun y => objs o ~{ C }~> objs y] ecod in @id _ (objs o))
    | _, _ => None
    end
  | Morph a =>
    match get_arr a with
    | Some (x; (y; (Hdom, (Hcod, f)))) =>
      match Eq_eq_dec (arr_dom arrs a) dom,
            Eq_eq_dec (arr_cod arrs a) cod with
      | left edom, left ecod =>
        Some (rew [fun x => objs x ~{ C }~> objs cod] edom in
              rew [fun y => objs (arr_dom arrs a) ~{ C }~> objs y] ecod in
              rew <- [fun x => objs x ~{ C }~> objs (arr_cod arrs a)] Hdom in
              rew <- [fun y => objs x ~{ C }~> objs y] Hcod in f)
      | _, _ => None
      end
    | _ => None
    end
  | Compose f g =>
    match denote (TermCod arrs g) cod f,
          denote dom (TermCod arrs g) g with
    | Some f, Some g => Some (f ∘ g)
    | _, _ => None
    end
  end.

Lemma denote_dom_cod {f dom cod f'} :
  denote dom cod f = Some f' ->
  TermDom arrs f = dom /\ TermCod arrs f = cod.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction f; intros dom cod; simpl; intros.
  - equalities.
  - destruct (get_arr a) eqn:?; [|discriminate].
    destruct s, s.
    equalities.
  - specialize (IHf2 dom (TermCod arrs f2)).
    specialize (IHf1 (TermCod arrs f2) cod).
    equalities; intros.
    destruct (denote (TermCod arrs f2) cod f1) eqn:?; [|discriminate].
    destruct (denote dom (TermCod arrs f2) f2) eqn:?; [|discriminate].
    destruct (IHf1 _ eq_refl).
    destruct (IHf2 _ eq_refl).
    intuition.
Qed.

Definition Term_defined dom cod (e : Term) : Type :=
  ∃ f, denote dom cod e = Some f.

Theorem Term_defined_is_well_typed {e dom cod} :
  Term_defined dom cod e ->
  Term_well_typed arrs dom cod e.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction e; simpl in *;
  intros dom cod [f H]; simpl in H; equalities;
  try (destruct (get_arr a); [|discriminate]; equalities).
  destruct (denote _ _ e1) eqn:?; [|discriminate].
  destruct (denote _ _ e2) eqn:?; [|discriminate].
  specialize (IHe1 (TermCod arrs e2) cod (h; Heqo)).
  specialize (IHe2 dom (TermCod arrs e2) (h0; Heqo0)).
  intuition; symmetry.
  eapply Term_well_typed_dom; eauto.
Qed.

Lemma denote_well_typed {p dom cod f} :
  denote dom cod p = Some f -> Term_well_typed arrs dom cod p.
Proof.
  generalize dependent f.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros ????; equalities;
  try (destruct (get_arr a); [|discriminate]; equalities).
  destruct (denote _ _ p2) eqn:?;
  destruct (denote _ _ p1) eqn:?; intros; try discriminate.
  pose proof (denote_dom_cod Heqo).
  pose proof (denote_dom_cod Heqo0).
  firstorder.
Qed.

Program Definition TermDef_Category : Category := {|
  obj := obj_idx;
  hom := fun x y => ∃ l : Term, Term_defined x y l;
  homset := fun x y => {| equiv := fun f g =>
    normalize (`1 f) = normalize (`1 g) |};
  id := fun x => (Identity x; _);
  compose := fun _ _ _ f g => (Compose (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left y (normalize (`1 f));
  id_right := fun x _ f => ArrowList_id_right arrs (normalize (`1 f)) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc
      (normalize (`1 f)) (normalize (`1 g)) (normalize (`1 h))
|}.
Next Obligation.
  eexists; simpl; equalities.
Defined.
Next Obligation.
  destruct X, X0.
  unshelve eexists; eauto.
    exact (x0 ∘ x).
  simpl.
  destruct (denote_dom_cod e).
  destruct (denote_dom_cod e0).
  equalities; subst.
  now rewrite e, e0.
Defined.
Next Obligation.
  eapply ArrowList_normalize_dom_cod_sound; eauto.
  eapply Term_defined_is_well_typed; eauto.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.

Fixpoint normalize_denote_chain dom cod (a : Arrow) (gs : list Arrow) :
  option (objs dom ~{C}~> objs cod).
Proof.
  destruct gs as [|g gs].
    destruct (get_arr a); [|exact None].
    destruct (Eq_eq_dec (arr_dom arrs a) dom); [|exact None].
    destruct (Eq_eq_dec (arr_cod arrs a) cod); [|exact None].
    equalities; exact (Some b0).
  destruct (Pos.eq_dec (arr_cod arrs a) cod); [|exact None].
  destruct (normalize_denote_chain dom (arr_dom arrs a) g gs); [|exact None].
  destruct (get_arr a); [|exact None].
  apply Some.
  equalities.
  exact (b0 ∘ h).
Defined.

Corollary normalize_denote_chain_cod :
  ∀ (gs : list Arrow) f dom cod f',
    normalize_denote_chain dom cod f gs = Some f' ->
    cod = arr_cod arrs f.
Proof.
  destruct gs; simpl; intros; equalities;
  destruct (get_arr f); equalities; discriminate.
Qed.

Theorem normalize_denote_chain_compose {x xs y ys dom cod f} :
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    arr_dom arrs (last xs x) = mid ∧
    arr_cod arrs y = mid ∧
    normalize_denote_chain mid cod x xs = Some g ∧
    normalize_denote_chain dom mid y ys = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  generalize dependent y.
  apply ListOfArrows_rect with (x:=x) (l:=xs); simpl; intros.
  - equalities.
    destruct (normalize_denote_chain dom (arr_dom arrs x0) y ys) eqn:?;
    equalities.
    destruct (get_arr x0); [|discriminate].
    equalities.
    exists _, h0, h.
    inversion_clear H.
    equalities.
      reflexivity.
    pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); auto.
  - equalities.
    destruct (normalize_denote_chain
                dom (arr_dom arrs x0) y (l ++ y0 :: ys)) eqn:?;
    equalities.
    try discriminate.
    destruct (get_arr x0); [|discriminate].
    destruct (X _ _ _ Heqo), s, s.
    equalities; subst.
    inversion_clear H.
    exists _, (h0 ∘ x2), x3.
    clear X.
    intuition.
    + now rewrite a, comp_assoc.
    + pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); subst.
      replace (match l with
               | [] => y
               | _ :: _ => last l x0
               end) with (last l y); auto.
      induction l; auto.
      now rewrite !last_cons.
    + now rewrite a2.
Qed.

Theorem normalize_denote_chain_compose_r {x xs y ys dom cod f} :
  (∃ mid g h, f ≈ g ∘ h ∧
     arr_dom arrs (last xs x) = mid ∧
     arr_cod arrs y = mid ∧
     normalize_denote_chain mid cod x xs = Some g ∧
     normalize_denote_chain dom mid y ys = Some h) ->
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f.
Proof.
  generalize dependent f.
  generalize dependent cod.
  generalize dependent y.
  apply ListOfArrows_rect with (x:=x) (l:=xs); simpl; intros.
  - repeat equalities.
      destruct (normalize_denote_chain dom (arr_dom arrs x0) y ys) eqn:?; [|discriminate].
      destruct (get_arr x0); [|discriminate].
      simpl_eq.
      equalities.
      simpl in a2.
      inversion_clear b0.
      inversion_clear a2.
    destruct (get_arr x0); [|discriminate].
    
    exists _, h0, h.
    inversion_clear H.
    equalities.
      reflexivity.
    pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); auto.
  - equalities.
    destruct (normalize_denote_chain
                dom (arr_dom arrs x0) y (l ++ y0 :: ys)) eqn:?;
    equalities.
    try discriminate.
    destruct (get_arr x0); [|discriminate].
    destruct (X _ _ _ Heqo), s, s.
    equalities; subst.
    inversion_clear H.
    exists _, (h0 ∘ x2), x3.
    clear X.
    intuition.
    + now rewrite a, comp_assoc.
    + pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); subst.
      replace (match l with
               | [] => y
               | _ :: _ => last l x0
               end) with (last l y); auto.
      induction l; auto.
      now rewrite !last_cons.
    + now rewrite a2.
Qed.

Lemma normalize_denote_chain_dom_cod :
  ∀ (gs : list Arrow) f dom cod f',
    normalize_denote_chain dom cod f gs = Some f' ->
    cod = arr_cod arrs f /\
    dom = arr_dom arrs (last gs f).
Proof.
  induction gs using rev_ind; intros.
    simpl in H.
    destruct (get_arr f); [|discriminate].
    now equalities.
  rewrite last_rcons.
  apply normalize_denote_chain_compose in H.
  equalities; subst.
    now specialize (IHgs _ _ _ _ a2).
  simpl in b0.
  destruct (get_arr x); [|discriminate].
  now equalities.
Qed.

Theorem normalize_denote_chain_append_dom_cod : ∀ x xs y ys dom cod f,
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  arr_dom arrs (last xs x) = arr_cod arrs y.
Proof.
  intros; destruct (normalize_denote_chain_compose H); equalities.
Qed.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Definition normalize_denote dom cod (xs : ArrowList) :
  option (objs dom ~{C}~> objs cod).
Proof.
  destruct xs as [o|f fs].
  - destruct (Eq_eq_dec o dom); [|exact None].
    destruct (Eq_eq_dec o cod); [|exact None].
    subst; exact (Some id).
  - exact (normalize_denote_chain dom cod f fs).
Defined.

Definition normalize_denote' dom cod (xs : ArrowList) :
  option (objs dom ~{C}~> objs cod).
Proof.
  generalize dependent cod.
  destruct xs using ArrowList_list_rect; intros.
  - destruct (Eq_eq_dec x dom); [|exact None].
    destruct (Eq_eq_dec x cod); [|exact None].
    subst; exact (Some (@id _ (objs cod))).
  - destruct (get_arr a); [|exact None].
    equalities.
    destruct (Eq_eq_dec (arr_dom arrs a) dom); [|exact None].
    destruct (Eq_eq_dec (arr_cod arrs a) cod); [|exact None].
    subst; exact (Some b0).
  - destruct (get_arr a1); [|exact None].
    destruct s, s, p, p; subst.
    destruct (IHxs (arr_dom arrs a1)); [|exact None].
    destruct (Eq_eq_dec (arr_cod arrs a1) cod); [|exact None].
    subst; exact (Some (h ∘ h0)).
Defined.

Program Fixpoint normalize_denote'' dom cod (xs : ArrowList) {measure (ArrowList_length xs)} :
  option (objs dom ~{C}~> objs cod) :=
  match xs with
  | IdentityOnly x =>
    match Eq_eq_dec x dom, Eq_eq_dec x cod with
    | left edom, left ecod =>
      Some (rew [fun x => objs x ~{ C }~> objs cod] edom in
            rew [fun y => objs x ~{ C }~> objs y] ecod in @id _ (objs x))
    | _, _ => None
    end
  | ArrowChain a nil =>
    match get_arr a with
    | Some (x; (y; (Hdom, (Hcod, f)))) =>
      match Eq_eq_dec (arr_dom arrs a) dom, Eq_eq_dec (arr_cod arrs a) cod with
      | left edom, left ecod =>
        Some (rew [fun x => objs x ~{ C }~> objs cod] edom in
              rew [fun y => objs (arr_dom arrs a) ~{ C }~> objs y] ecod in
              rew <- [fun x => objs x ~{ C }~> objs (arr_cod arrs a)] Hdom in
              rew <- [fun y => objs x ~{ C }~> objs y] Hcod in f)
      | _, _ => None
      end
    | _ => None
    end
  | ArrowChain a1 (a2 :: xs) =>
    match get_arr a1 with
    | Some (x1; (y1; (Hdom1, (Hcod1, f1)))) =>
      match normalize_denote dom x1 (ArrowChain a2 xs) with
      | Some f2 =>
        match Eq_eq_dec (arr_cod arrs a1) cod with
        | left ecod =>
          Some (rew [fun y => objs dom ~{ C }~> objs y] ecod in
                (rew <- [fun y => objs x1 ~> objs y] Hcod1 in f1 ∘ f2))
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.

Theorem normalize_list_cod {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_cod arrs p = cod.
Proof.
  intros; destruct p as [o|g []]; simpl in *; equalities;
  (destruct (get_arr g); [|discriminate]; equalities).
Qed.

Theorem normalize_list_dom {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_dom arrs p = dom.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; simpl in *; intros; equalities.
    destruct (get_arr a); discriminate.
  destruct (normalize_denote_chain _ _ _ _) eqn:Heqe; try discriminate.
  rewrite <- (IHp _ _ Heqe); clear IHp.
  induction l using rev_ind; simpl in *; equalities.
  rewrite !last_rcons.
  destruct l; auto.
Qed.

Theorem normalize_denote_well_typed {p dom cod f} :
  normalize_denote dom cod p = Some f
    -> ∃ p', p = normalize p' ∧ Term_well_typed arrs dom cod p'.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; simpl in *; intros; equalities.
  - exists (Identity cod).
    simpl; intuition.
  - exists (Morph a).
    simpl; intuition.
  - destruct (get_arr a); discriminate.
  - destruct (get_arr a); discriminate.
  - destruct (normalize_denote_chain _ _ _ _) eqn:?; try discriminate.
    destruct (IHp _ _ Heqo), p.
    exists (Compose (Morph a1) x).
    simpl.
    inversion_clear H.
    intuition.
    + now rewrite <- e.
    + eapply Term_well_typed_cod; eauto.
    + symmetry.
      eapply Term_well_typed_cod; eauto.
    + erewrite Term_well_typed_cod; eauto.
Qed.

Theorem normalize_compose {x y dom cod f} :
  ArrowList_cod arrs y = ArrowList_dom arrs x ->
  normalize_denote dom cod (ArrowList_append x y) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    ArrowList_dom arrs x = mid ∧
    ArrowList_cod arrs y = mid ∧
    normalize_denote mid cod x = Some g ∧
    normalize_denote dom mid y = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction x using ArrowList_list_rect; intros.
  - simpl in H.
    rewrite <- H.
    exists cod, (@id _ _), f.
    rewrite ArrowList_id_left in H0; auto.
    rewrite (normalize_list_cod H0) in *.
    cat; simpl; equalities.
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id _ _).
      rewrite <- H0.
      pose proof (normalize_list_dom H0).
      rewrite (ArrowList_id_right arrs) in * by auto.
      rewrite H, H1; clear H H1.
      cat; simpl in *; repeat equalities;
      destruct (get_arr a); discriminate.
    + rewrite (ArrowList_append_chains arrs) in H0 by auto.
      apply (normalize_denote_chain_compose H0).
    + rewrite (ArrowList_append_chains arrs) in H0 by auto.
      apply (normalize_denote_chain_compose H0).
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id _ _).
      rewrite (ArrowList_id_right arrs) in H0 by auto.
      rewrite (normalize_list_dom H0); subst.
      rewrite H0.
      pose proof (normalize_list_dom H0).
      cat; simpl in *; repeat equalities.
    + rewrite (ArrowList_append_chains arrs) in H0 by auto.
      apply (normalize_denote_chain_compose H0).
    + rewrite (ArrowList_append_chains arrs) in H0 by auto.
      apply (normalize_denote_chain_compose H0).
Qed.

Theorem normalize_compose_r {x y dom cod f} :
  ArrowList_cod arrs y = ArrowList_dom arrs x ->
  ∃ mid g h, f ≈ g ∘ h ∧
    ArrowList_dom arrs x = mid ∧
    ArrowList_cod arrs y = mid ∧
    normalize_denote mid cod x = Some g ∧
    normalize_denote dom mid y = Some h ->
  normalize_denote dom cod (ArrowList_append x y) = Some f.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction x using ArrowList_list_rect; intros.
  - simpl in H.
    rewrite <- H.
    exists cod, (@id _ _), f.
    rewrite ArrowList_id_left; auto.
    cat; simpl; equalities.
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id _ _).
      intros; equalities.
    + rewrite (ArrowList_append_chains arrs) by auto.
      admit.
    + rewrite (ArrowList_append_chains arrs) by auto.
      admit.
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id _ _).
      rewrite (ArrowList_id_right arrs) by auto.
      cat; simpl in *; repeat equalities.
    + rewrite (ArrowList_append_chains arrs) by auto.
      admit.
    + rewrite (ArrowList_append_chains arrs) by auto.
      admit.
Qed.

Theorem normalize_sound {p dom cod f} :
  Term_well_typed arrs dom cod p ->
  normalize_denote dom cod (normalize p) = Some f ->
  ∃ f', f ≈ f' ∧ denote dom cod p = Some f'.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; simpl in *; intros; equalities.
  - exists f; repeat equalities; reflexivity.
  - exists f.
    destruct (get_arr a); [|discriminate].
    repeat equalities; reflexivity.
  - apply normalize_compose in H0; equalities; subst.
    + destruct (Eq_eq_dec (ArrowList_dom arrs (normalize p1))
                          (TermCod arrs p2)).
      * rewrite <- e in *.
        destruct (IHp1 _ _ _ H1 a2), (IHp2 _ _ _ H2 b0).
        equalities.
        rewrite e3, e1.
        eexists; intuition.
        now rewrite <- e0, <- e2.
      * pose proof (ArrowList_normalize_dom_cod_sound arrs H2);
        equalities.
        now rewrite a1 in H3.
    + clear IHp1 IHp2.
      pose proof (ArrowList_normalize_dom_cod_sound arrs H1).
      pose proof (ArrowList_normalize_dom_cod_sound arrs H2).
      equalities.
      now rewrite H3.
Qed.

Theorem normalize_sound_r {p dom cod f} :
  Term_well_typed arrs dom cod p ->
  denote dom cod p = Some f ->
  ∃ f', f ≈ f' ∧ normalize_denote dom cod (normalize p) = Some f'.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; simpl in *; intros; equalities.
  - exists f; repeat equalities; reflexivity.
  - exists f.
    destruct (get_arr a); [|discriminate].
    repeat equalities; reflexivity.
  - destruct (denote (TermCod arrs p2) cod p1) eqn:?; [|discriminate].
    destruct (denote dom (TermCod arrs p2) p2) eqn:?; [|discriminate].
    destruct (IHp1 _ _ _ H1 Heqo), p; clear IHp1.
    destruct (IHp2 _ _ _ H2 Heqo0), p; clear IHp2.
    exists (x ∘ x0).
    split.
      inversion_clear H0; cat.
    admit.
Admitted.

(*
Lemma normalize_denote_append_some dom mid cod p1 p2 f g :
  normalize_denote mid cod p1 ≈ Some f ∧ normalize_denote dom mid p2 ≈ Some g ->
  normalize_denote dom cod (ArrowList_append p1 p2) ≈ Some (f ∘ g).
Proof.
  intros [].
  generalize dependent cod.
  generalize dependent dom.
  induction p1 using ArrowList_list_rect; simpl; intros.
  - destruct p2 using ArrowList_list_rect; simpl in *;
    revert e; revert e0;
    do 2 equalities'; repeat equalities; try reflexivity.
    + do 4 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction.
      rewrite <- e, <- e0; cat.
    + destruct (get_arr a); auto.
      revert e.
      revert e0.
      do 6 equalities'; repeat equalities; simpl_eq; auto.
      rewrite <- e; cat.
    + simpl_eq.
      destruct (normalize_denote_chain dom (arr_dom arrs a1) a2 l); auto.
      destruct (get_arr a1); auto.
      equalities.
      rewrite <- e; cat.
  - destruct p2 using ArrowList_list_rect; simpl in *;
    revert e; revert e0;
    do 2 equalities'; repeat equalities; try reflexivity.
    + do 4 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction;
      destruct (get_arr a); auto.
      equalities.
      rewrite <- e0; cat.
    + do 4 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction;
      destruct (get_arr a0); auto;
      destruct (get_arr a); auto; equalities.
      destruct e1.
      rewrite e, e0; reflexivity.
    + do 4 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction;
      destruct (get_arr a); auto;
      destruct (get_arr a1); auto;
      destruct (normalize_denote_chain dom (arr_dom arrs a1) a2 l);
      auto; equalities.
      destruct e1.
      rewrite e, e0; reflexivity.
  - destruct p2 using ArrowList_list_rect; simpl in *;
    revert e; revert e0;
    do 2 equalities'; repeat equalities; try reflexivity.
    + destruct (normalize_denote_chain mid (arr_dom arrs a1) a2 l);
      destruct (get_arr a1); auto.
      equalities; simpl_eq.
      rewrite <- e, <- e0; cat.
    + admit.
    + admit.
Admitted.

Lemma normalize_denote_append_none dom cod p1 p2 :
  normalize_denote dom cod p1 = None ∨ normalize_denote dom cod p2 = None ->
  normalize_denote dom cod (ArrowList_append p1 p2) ≈ None.
Proof.
  intros [].
  generalize dependent cod.
  generalize dependent dom.
  induction p1 using ArrowList_list_rect; simpl; intros.
  - revert e.
    do 2 equalities'; repeat equalities; try reflexivity.
    destruct p2; simpl.
    + do 2 equalities'; repeat equalities; simpl_eq;
      try reflexivity; try contradiction.
    + destruct (normalize_denote_chain dom cod a l).
*)

Theorem denote_normalize {p dom cod} :
  (* Term_well_typed_bool arrs dom cod p = true -> *)
  denote dom cod p ≈ normalize_denote dom cod (normalize p).
Proof.
  destruct (denote dom cod p) eqn:?.
    destruct (normalize_denote dom cod (normalize p)) eqn:?.
      apply normalize_sound in Heqo0.
        destruct Heqo0.
        equalities.
        red.
        rewrite e0 in Heqo.
        rewrite e.
        now inversion_clear Heqo.
      now apply denote_well_typed in Heqo.
    admit.
  
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; intros.
  - repeat equalities; reflexivity.
  - simpl in *.
    destruct (get_arr a); auto.
    destruct s, s.
    simpl_eq.
    destruct p, p, e, e0.
    repeat destruct (Pos.eq_dec _ _); auto.
    destruct e, e0; cat.
  - simpl normalize.
    simpl denote.
    specialize (IHp1 (TermCod arrs p2) cod).
    specialize (IHp2 dom (TermCod arrs p2)).
    repeat destruct (denote _ _ _); symmetry.
Admitted.

Theorem normalize_apply dom cod : ∀ f g,
  Term_well_typed_bool arrs dom cod f = true ->
  Term_well_typed_bool arrs dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  denote dom cod f ≈ denote dom cod g.
Proof.
  intros.
  apply Term_well_typed_bool_sound in H.
  apply Term_well_typed_bool_sound in H0.
  pose proof (ArrowList_well_typed_sound arrs H).
  apply (ArrowList_beq_eq arrs) in H1.
  destruct (normalize_denote dom cod (normalize f)) eqn:?; try discriminate.
  destruct (normalize_sound H Heqo), p.
  rewrite e0; clear e0.
  rewrite H1 in Heqo; clear H1.
  destruct (normalize_sound H0 Heqo), p.
  rewrite e1; clear e1.
  red.
  rewrite <- e, <- e0.
  reflexivity.
Qed.

Corollary normalize_denote_terms dom cod : ∀ f g,
  Term_well_typed_bool arrs dom cod f = true ->
  Term_well_typed_bool arrs dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  normalize_denote dom cod (normalize f)
    ≈ normalize_denote dom cod (normalize g) ->
  denote dom cod f ≈ denote dom cod g.
Proof. intros; apply normalize_apply; auto. Qed.

Corollary normalize_denote_terms_impl dom cod : ∀ f g,
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f)
    ≈ normalize_denote dom cod (normalize g).
Proof.
  intros.
  apply (ArrowList_beq_eq arrs) in H.
  now rewrite H.
Qed.

End Denotation.

Section Rewriting.

Context (C : Category).

Variable objs : obj_idx -> C.
Variable arrs : arr_idx -> (obj_idx * obj_idx).
Variable get_arr : ∀ f : arr_idx,
  option (∃ x y, (arr_dom arrs f = x) ∧
                 (arr_cod arrs f = y) ∧ (objs x ~{C}~> objs y)).

Function substitute_subterm (e f : ArrowList)
         {measure ArrowList_length e} : option ArrowList :=
   match e, f with
   | ArrowChain x xs, ArrowChain y ys =>
     if Eq_eqb x y
     then match xs, ys with
          | nil, nil => Some (IdentityOnly (arr_cod arrs x))
          | x' :: xs', nil => Some (ArrowChain x' xs')
          | x' :: xs', y' :: ys' =>
            substitute_subterm (ArrowChain x' xs') (ArrowChain y' ys')
          | _, _ => None
          end
     else None
   | _, _ => None
   end.
Proof. simpl; intros; apply le_n_S, le_n. Defined.

Function substitute_term (e f t : ArrowList) {measure ArrowList_length e} :
  ArrowList :=
   match e, f with
   | ArrowChain x xs, ArrowChain y ys =>
     match substitute_subterm e f with
     | Some rest => ArrowList_append t rest
     | None =>
       match xs with
       | nil => e
       | cons x' xs' =>
         ArrowChain x (match substitute_term (ArrowChain x' xs') f t with
                       | IdentityOnly _  => nil
                       | ArrowChain z zs => z :: zs
                       end)
       end
     end
   | _, _ => e
   end.
Proof. simpl; intros; apply le_n_S, le_n. Defined.

Compute substitute_term
          (ArrowChain 10%positive [11; 12; 1; 2; 3; 16; 17; 18]%positive)
          (ArrowChain 1%positive [2; 3]%positive)
          (ArrowChain 4%positive [5; 6]%positive).

Definition ArrowList_equiv dom cod (f' g' : ArrowList) : Prop :=
  normalize_denote C objs arrs get_arr dom cod f' =
  normalize_denote C objs arrs get_arr dom cod g'.

Program Instance ArrowList_equiv_eqv dom cod :
  CRelationClasses.Equivalence (ArrowList_equiv dom cod).
Next Obligation.
  intros; unfold ArrowList_equiv in *; congruence.
Defined.
Next Obligation.
  intros; unfold ArrowList_equiv in *; congruence.
Defined.

Program Instance ArrowList_setoid dom cod : Setoid ArrowList := {
  equiv := ArrowList_equiv dom cod
}.

Program Instance normalize_denote_Proper dom cod :
  CMorphisms.Proper (ArrowList_equiv dom cod ==> equiv)
                    (normalize_denote C objs arrs get_arr dom cod).
Next Obligation.
  proper.
  unfold ArrowList_equiv in *.
  rewrite H.
  destruct (normalize_denote C objs arrs get_arr dom cod y); auto.
  reflexivity.
Defined.

Program Instance substitute_term_Proper dom cod dom' cod' :
  CMorphisms.Proper (ArrowList_equiv dom cod
                       ==> ArrowList_equiv dom' cod'
                       ==> ArrowList_equiv dom' cod'
                       ==> ArrowList_equiv dom cod)
                    substitute_term.
Next Obligation.
  proper.
Admitted.

(*
Lemma substitute_term_sound dom cod (f g : ArrowList) :
  ArrowList_beq f g ->
  (exists f, normalize_denote C objs arrs get_arr dom cod f' = Some f) ->
  (exists g, normalize_denote C objs arrs get_arr dom cod g' = Some g) ->
  ArrowList_equiv dom cod f' g' -> f' = g'.
Proof.
  intros.
  induction f' using ArrowList_list_rect.
  - destruct g' using ArrowList_list_rect;
    unfold ArrowList_equiv in H1;
    destruct H, H0;
    simpl in *.
    + equalities.
    + exfalso.
      destruct (get_arr a); [|discriminate].
      equalities.
      simpl_eq.
      destruct e.
      unfold 
  revert H.
  apply substitute_term_ind; intros; subst; try reflexivity.
  - assert (ArrowList_equiv dom cod (ArrowChain x xs) t).
    rewrite H.
    assert (ArrowList_equiv dom cod (ArrowChain x xs)
                            (ArrowList_append (ArrowChain y ys) rest)).
      clear H.
      destruct rest.
        rewrite (ArrowList_id_right arrs).
        admit.
        admit.
      rewrite (ArrowList_append_chains arrs).
      admit.
    rewrite substitute_subterm_equation in e3.
    destruct (Eq_eqb x y) eqn:?; [|discriminate].
    apply Eq_eqb_eq in Heqb; subst.
  - specialize (H H0).
    rewrite e5 in H; clear e5.
    admit.
  - specialize (H H0).
    rewrite e5 in H; clear e5.
    admit.
Abort.
*)

End Rewriting.

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
    constr:(Compose ft gt)
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let cn := lookupCat c cs in
      let fn := lookupArr c cs f in
      constr:(Morph fn)
    end
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

Definition convert_arr (C : Category) (dom cod : C) (fv : dom ~> cod)
           (objs : obj_idx -> C) (domi codi : obj_idx)
           (Hdomo : objs domi = dom) (Hcodo : objs codi = cod)
           (arrs : arr_idx -> (obj_idx * obj_idx)) (f : arr_idx) :
  option (∃ x y, (arr_dom arrs f = x) ∧ (arr_cod arrs f = y) ∧
                 (objs x ~{C}~> objs y)).
Proof.
  destruct (Eq_eq_dec (arr_dom arrs f) domi); [|exact None].
  destruct (Eq_eq_dec (arr_cod arrs f) codi); [|exact None].
  apply Some.
  exists domi, codi; subst; intuition idtac.
Defined.

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
                         @None (∃ x y, (arr_dom xyfun f = x) ∧
                                       (arr_cod xyfun f = y) ∧
                                       (ofun x ~{cat}~> ofun y))))
            end)
          ltac:(fun fi fv fk => match type of fv with
            | ?x ~{cat}~> ?y =>
              let xn := lookup x os in
              let yn := lookup y os in
              constr:((fun (f : arr_idx) =>
                         if (f =? fi)%positive
                         then convert_arr cat x y fv ofun xn yn
                                          eq_refl eq_refl xyfun f
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

Ltac reify_terms_and_then tacHyp tacGoal :=
  repeat match goal with
  | [ H : ?S ≈ ?T |- _ ] =>
    let cs  := allVars tt S in
    let cs  := allVars cs T in
    let r1  := reifyTerm cs S in
    let r2  := reifyTerm cs T in
    let env := build_env cs in
    let env := eval compute [Pos.succ TermDom TermCod] in env in
    match env with
    | (?cat, ?ofun, ?xyfun, ?ffun) =>
      change (denote cat ofun xyfun ffun
                     (TermDom xyfun r1) (TermCod xyfun r1) r1 ≈
              denote cat ofun xyfun ffun
                     (TermDom xyfun r2) (TermCod xyfun r2) r2) in H;
      cbv beta iota zeta delta [TermDom TermCod Pos.succ] in H;
      tacHyp env r1 r2 H;
      lazymatch type of H with
      | ?U ≈ ?V => change (term_wrapper (U ≈ V)) in H
      end
    end
  | [ |- ?S ≈ ?T ] =>
    let cs  := allVars tt S in
    let cs  := allVars cs T in
    let r1  := reifyTerm cs S in
    let r2  := reifyTerm cs T in
    let env := build_env cs in
    let env := eval compute [Pos.succ TermDom TermCod] in env in
    match env with
    | (?cat, ?ofun, ?xyfun, ?ffun) =>
      change (denote cat ofun xyfun ffun
                     (TermDom xyfun r1) (TermCod xyfun r1) r1 ≈
              denote cat ofun xyfun ffun
                     (TermDom xyfun r2) (TermCod xyfun r2) r2);
      cbv beta iota zeta delta [TermDom TermCod Pos.succ];
      tacGoal env r1 r2
    end
  end.

Ltac reify :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H => pose env; pose r1; pose r2; pose H)
    ltac:(fun env r1 r2   => pose env; pose r1; pose r2).

Ltac categorical :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H => idtac)
    ltac:(fun env r1 r2 =>
      match env with
      | (?cat, ?ofun, ?xyfun, ?ffun) =>
        apply (normalize_apply cat ofun xyfun ffun
                               (TermDom xyfun r1) (TermCod xyfun r1) r1 r2);
        vm_compute; reflexivity
      end).

Ltac normalize :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H =>
      match env with
      | (?cat, ?ofun, ?xyfun, ?ffun) =>
        let H1 := fresh "H" in
        assert (H1 : ArrowList_beq (normalize r1) (normalize r2) = true)
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
  (* reify. *)
  Time normalize.               (* 0.315s *)
  Time categorical.             (* 0.45s *)
Qed.

(* Ltac cat_rewrite H := *)

Print Assumptions sample_2.

Require Import Category.Theory.Adjunction.

Local Obligation Tactic :=
  cat_simpl; proper; simpl in *;
  try erewrite !normalize_denormalize; eauto;
  try (eapply ArrowList_append_well_typed;
       [ eapply ArrowList_well_typed_dom
       | eapply ArrowList_well_typed_cod | | ]); eauto.

Hint Resolve ArrowList_well_typed_sound.
Hint Resolve denormalize_well_typed.

(* This adjunction establishes that Term is our free category, with ArrowList
   equivalent up to normalization of terms with a canonical mapping back into
   Term by "denormalization".

   Since the objects of both categories are the same, the monad this gives
   rise to is uninteresting. *)
Program Instance Term_ArrowList_Adjunction
        (arr_def : arr_idx → obj_idx ∧ obj_idx) :
  ArrowList_to_Term arr_def ⊣ Term_to_ArrowList arr_def := {
  adj := fun x y =>
    {| to   := {| morphism := fun f => (normalize (_ f); _) |}
     ; from := {| morphism := _ |} |}
}.

Print Assumptions Term_ArrowList_Adjunction.
*)
