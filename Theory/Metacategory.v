Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.FSets.FMapFacts.
Require Import Category.Lib.FMapExt.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This module defines an "arrows-only" metacategory, and shows that such a
   metacategory is sufficient to define a category. The axioms defined by Mac
   Lane are used, with the "defined set of composable pairs" and "composite
   assignments" both encoded using a key-value map provided by FMap, since
   that provides just the structure we need. Natural numbers are used to
   differentiate arrows. *)

Module PNN := PairUsualDecidableType Nat_as_DT Nat_as_DT.

Module Metacategory (M : WSfun PNN).

Module Import FMapExt := FMapExt PNN M.
Module P := FMapExt.P.
Module F := P.F.

Definition defined x y := M.In (elt:=nat) (x, y).

(* Mac Lane: "Since the objects of a metacategory correspond exactly to its
   identity arrows, it is technically possible to dispense altogether with the
   objects and deal only with arrows." *)
Record Metacategory := {
  (* "The data for an arrows-only metacategory C consist of arrows," *)
  arr := nat;

  (* "certain ordered pairs ⟨g, f⟩, called the composable pairs of arrows," *)
  pairs : M.t arr;

  (* "and an operation assigning to each composable pair ⟨g, f⟩ an arrow g∙f,
     called their composite. We say 'g∙f is defined' for '⟨g, f⟩ is a
     composable pair'". *)
  composite (f g h : arr) := M.MapsTo (f, g) h pairs;

  (* "With these data one defines an identity of C to be an arrow u such that
     f∙u = f whenever the composite f∙u is defined and u∙g = g whenever u∙g is
     defined." *)
  identity (u : arr) :=
    (∀ (f : arr), composite f u f) ∧ (∀ (g : arr), composite u g g);

  (* "The data are then required to satisfy the following three axioms:" *)

  (* First axiom: *)

  (* "The composite (k∙g)∙f is defined if and only if the composite k∙(g∙f) is
     defined. When either is defined, they are equal (and this triple
     composite is written as k∙g∙f)." *)
  composition_law (k g f kg gf : arr) :
    composite k g kg ->
    composite g f gf ->
    ∀ kgf, composite kg f kgf ↔ composite k gf kgf;

  (* Second axiom: *)

  (* "The triple composite k∙g∙f is defined whenever both composites k∙g and
     g∙f are defined." *)
  triple_composition (k g f kg gf : arr) :
    composite k g kg ->
    composite g f gf -> (exists kgf : arr, composite kg f kgf)%type;

  (* Third axiom: *)

  (* "For each arrow g of C there exist identity arrows u and u' of C such
     that u'∙g and g∙u are defined." *)
  identity_law (g : arr) :
    ∃ u,  identity u  ->
    ∃ u', identity u' ->
      defined g u pairs ∧ defined u' g pairs;
}.

Definition composite_defined (M : Metacategory) (f g h : arr M) :
  composite M f g h -> defined f g (pairs M) := fun H =>
  proj2 (@in_mapsto_iff _ _ _) (ex_intro _ h H).

Program Definition defined_composite (M : Metacategory) (f g : arr M) :
  defined f g (pairs M) -> ∃ h : arr M, composite M f g h.
Proof.
  intro H.
  unfold defined in H.
  destruct (M.find (f, g) (pairs M)) eqn:Heqe.
    exists n.
    apply (M.find_2 Heqe).
  apply F.in_find_iff in H.
  contradiction.
Defined.

Lemma identity_morphism (M : Metacategory) (i : arr M) :
  identity M i -> composite M i i i.
Proof. intro H; apply H. Qed.

Lemma identity_composition_between (M : Metacategory) :
  ∀ f g u,
    identity M u ->
    defined f u (pairs M) ->
    defined u g (pairs M) ->
    defined f g (pairs M).
Proof.
  intros.
  destruct H.
  pose proof (@triple_composition M f u g f g (c f) (c0 g)) as H3;
  simpl in H3.
  destruct H3.
  apply composite_defined with (h:=x).
  exact H.
Defined.

Lemma identity_composition_left (M : Metacategory) :
  ∀ f g fg u,
    identity M u ->
    composite M f g fg ->
    defined u f (pairs M) ->
    defined u fg (pairs M).
Proof.
  intros.
  destruct H.
  apply composite_defined with (h:=fg); auto.
Qed.

Lemma identity_composition_right (M : Metacategory) :
  ∀ f g fg u,
    identity M u ->
    composite M f g fg ->
    defined g u (pairs M) ->
    defined fg u (pairs M).
Proof.
  intros.
  destruct H.
  apply composite_defined with (h:=fg); auto.
Qed.

Local Obligation Tactic := intros.

Global Program Definition FromArrows (M : Metacategory) : Category := {|
  (* The objects of the category are given by all the identity arrows of the
     arrows-only metacategory. *)
  obj := ∃ i : arr M, identity M i;

  (* The morphisms of the category from id[x] to id[y] are given by those
     arrows whose domain composes with id[x], and whose codomain composes with
     id[y]. *)
  hom := fun x y =>
    ∃ f : arr M, defined f ``x (pairs M) ∧ defined ``y f (pairs M);

  homset := fun _ _ => {| Setoid.equiv := fun f g => `1 f = `1 g |}
|}.
Next Obligation.
  equivalence; simpl in *; subst.
Qed.
Next Obligation.                (* id *)
  destruct x as [i [Hil Hir]].
  exists i.
  split; apply composite_defined with (h:=i); auto.
Defined.
Next Obligation.                (* compose *)
  destruct x as [x x_id];
  destruct y as [y y_id];
  destruct z as [z z_id];
  destruct f as [f [fl fr]];
  destruct g as [g [gl gr]]; simpl in *.
  pose proof (identity_composition_between M f g y y_id fl gr).
  destruct (defined_composite _ _ _ H) as [fg Hfg].
  exists fg; split.
    eapply identity_composition_right; eauto.
  eapply identity_composition_left; eauto.
Defined.
Next Obligation.
  proper.
  unfold FromArrows_obligation_3; simpl.
  destruct e3, e4, e5; simpl in *; subst;
  destruct (defined_composite _ _ _); reflexivity.
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x, y, f, i, i0, p; simpl in *; subst.
  destruct (defined_composite _ _ _).
  pose proof (c2 x1).
  unfold composite in c3, H.
  apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x, y, f, i, i0, p; simpl in *; subst.
  destruct (defined_composite _ _ _).
  pose proof (c x1).
  unfold composite in c3, H.
  apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x as [x [xl_id xr_id]];
  destruct y as [y [yl_id yr_id]];
  destruct z as [z [zl_id zr_id]];
  destruct w as [w [wl_id wr_id]];
  destruct f as [f [fl fr]];
  destruct g as [g [gl gr]];
  destruct h as [h [hl hr]];
  simpl in *.
  repeat destruct (defined_composite _ _ _).
  unfold composite in *.
  pose proof (fst (composition_law M f g h x2 x0 c1 c x3) c2).
  simpl in H.
  apply (FMapExt.F.MapsTo_fun c0 H).
Qed.
Next Obligation.
  symmetry; apply FromArrows_obligation_7.
Qed.

Notation "[map ]" := (M.empty _) (at level 9).
Notation "x +=> y" := (M.add x y) (at level 9).
Notation "[map a ; .. ; b ]" := (a .. (b [map]) ..).

Ltac structure :=
  simpl in *;
  repeat (
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H; subst
    | [ |- ?X = ?Y → False ] =>
      let H := fresh "H" in
      intro H; inversion H; tauto
    | [ H : M.MapsTo _ _ _ |- _ ] => simplify_maps
    | [ |- M.MapsTo _ _ _ ] => simplify_maps
    | [ |- _ ↔ _ ] => split; intros
    | [ |- _ /\ _ ] => split
    | [ |- _ \/ _ ] => solve [ left; structure | right; structure ]
    end; intuition idtac; try congruence).

Ltac check_structure :=
  first [ unfold defined;
          repeat (unshelve eexists; try assumption; intros []);
          split; apply in_mapsto_iff;
          eexists; intuition
        | unshelve (structure; eexists; structure); exact 0%nat
        | structure ].

Local Obligation Tactic := program_simpl; check_structure.

Program Definition ZeroArrows : Metacategory := {|
  pairs := [map]
|}.

Program Definition OneArrow : Metacategory := {|
  pairs := [map (0, 0) +=> 0 ]%nat
|}.

Program Definition TwoArrows : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1

           ;    (0, 2) +=> 2
           ;    (2, 1) +=> 2 ]%nat
|}.

Program Definition ThreeArrows : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (2, 2) +=> 2

           ;    (0, 3) +=> 3
           ;    (3, 1) +=> 3

           ;    (1, 4) +=> 4
           ;    (4, 2) +=> 4

           ;    (3, 4) +=> 5

           ;    (0, 5) +=> 5
           ;    (5, 2) +=> 5 ]%nat
|}.

Definition Three : Category := FromArrows ThreeArrows.

Require Import Coq.Arith.PeanoNat.

Definition cardinality (M : Metacategory) : nat :=
  M.cardinal (P.filter (fun '(dom, cod) v =>
                          ((dom =? v)%nat && (cod =? v)%nat)%bool)
                       (pairs M)).

(* jww (2017-06-10): This needs automation. A computational tactic that
   reflects on map structures would be valuable here, since we are computing
   on known results. *)
Lemma ThreeArrows_card_3 : cardinality ThreeArrows = 3%nat.
Proof.
  assert (P.transpose_neqkey
            M.Equal
            (λ (k : M.key) (e : nat) (m : M.t nat),
             if (let '(dom, cod) := k in
                 λ v : nat, (dom =? v)%nat && (cod =? v)%nat) e
             then k +=> e m
             else m)).
    intros ??????.
    destruct k, k'.
    assert (n ≠ n1 \/ n0 ≠ n2).
      destruct (Nat.eq_dec n n1); subst.
        right; congruence.
      left; assumption.
    destruct ((n =? e)%nat && (n0 =? e)%nat) eqn:Heqe.
      apply andb_true_iff in Heqe.
      destruct Heqe.
      apply Nat.eqb_eq in H1.
      apply Nat.eqb_eq in H2.
      subst.
      destruct ((n1 =? e')%nat && (n2 =? e')%nat) eqn:Heqe2.
        apply andb_true_iff in Heqe2.
        destruct Heqe2.
        apply Nat.eqb_eq in H1.
        apply Nat.eqb_eq in H2.
        subst.
        apply add_associative.
        intros; congruence.
      reflexivity.
    destruct ((n1 =? e')%nat && (n2 =? e')%nat) eqn:Heqe2.
      apply andb_true_iff in Heqe2.
      destruct Heqe2.
      apply Nat.eqb_eq in H1.
      apply Nat.eqb_eq in H2.
      subst.
      reflexivity.
    reflexivity.

  assert (Proper (eq ==> eq ==> M.Equal ==> M.Equal)
                 (λ (k : M.key) (e : nat) (m : M.t nat),
                  if (let '(dom, cod) := k in
                      λ v : nat, (dom =? v)%nat && (cod =? v)%nat) e
                  then k +=> e m
                  else m)).
    intros ?????????.
    destruct x, y; subst.
    inversion H0; clear H0; subst.
    destruct ((n1 =? y0)%nat && (n2 =? y0)%nat) eqn:Heqe.
      apply andb_true_iff in Heqe.
      destruct Heqe.
      apply Nat.eqb_eq in H0.
      apply Nat.eqb_eq in H1.
      subst.
      rewrite H2; reflexivity.
    assumption.

  unfold cardinality; simpl.
  unfold P.filter; simpl.
  repeat (rewrite P.fold_add; eauto; relational; simpl);
  try (apply not_in_mapsto_iff; intros;
       repeat (unfold not; intros; simplify_maps; try congruence)).
  rewrite P.fold_Empty; auto; [| apply M.empty_1 ].

  assert (P.transpose_neqkey eq (λ (_ : M.key) (_ : nat), S)) by proper.

  rewrite P.cardinal_fold.
  repeat (rewrite P.fold_add; eauto; relational; simpl);
  try (apply not_in_mapsto_iff; intros;
       repeat (unfold not; intros; simplify_maps; try congruence)).
  rewrite P.fold_Empty; auto; apply M.empty_1.
Qed.

(* Definition objects_of (M : Metacategory) : *)
(*   ∀ P : nat → Type, P 0%nat → (∀ n : nat, P n → P (S n)) → ∀ n : nat, P n *)

Require Import Category.Theory.Functor.

Local Obligation Tactic := program_simpl.

Program Definition FromThree {C : Category} (c : C) : Three ⟶ C := {|
  fobj := fun x =>
   match x with
   | existT _ 0%nat _ => c
   | existT _ 1%nat _ => c
   | existT _ 2%nat _ => c
   | _ => False_rect _ _
   end
|}.
Next Obligation.
  destruct x. specialize (H1 X); contradiction.
  destruct x. specialize (H X); contradiction.
  destruct x. specialize (H0 X); contradiction.
  destruct X.
  pose proof (c0 0%nat).
  unfold composite in H2; simpl in H2.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. discriminate.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. discriminate.
  simplify_maps. structure.
Qed.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

End Metacategory.
