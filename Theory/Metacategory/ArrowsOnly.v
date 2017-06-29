Set Warnings "-notation-overridden".

Require Import Coq.FSets.FMaps.
Require Import Coq.omega.Omega.

Require Import Category.Lib.
Require Import Category.Lib.FMapExt.
Require Import Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Module PO := PairOrderedType Nat_as_OT Nat_as_OT.
Module M := FMapList.Make(PO).
Module FMapExt := FMapExt PO M.

(* An arrows-only meta-category defines identity arrows as those which, when
   composed to the left or right of another arrow, result in that same arrow.
   This definition requires that all such composition be present. *)

Record Metacategory := {
  num_arrows : nat;
  arrow := nat;

  pairs : M.t arrow;
  pairs_correct : ∀ f g h, M.MapsTo (f, g) h pairs ->
    (f < num_arrows /\ g < num_arrows /\ h < num_arrows)%nat;

  composite (f g h : arrow) := M.MapsTo (f, g) h pairs;

  (* ∀ edges (X, Y) and (Y, Z), ∃ an edge (X, Z) which is equal to the
     composition of those edges. *)
  composite_correct (k g f kg gf : arrow) :
    composite k g kg ->
    composite g f gf -> ∃ kgf, composite kg f kgf;

  composition_law (k g f kg gf : arrow) :
    composite k g kg ->
    composite g f gf ->
    ∀ kgf, composite kg f kgf ↔ composite k gf kgf;

  identity (u : arrow) := (∀ f, composite f u f) ∧ (∀ g, composite u g g)
}.

(* Every meta-category, defined wholly in terms of the axioms of category
   theory, gives rise to a category interpreted in the context of set
   theory. *)

Program Definition Category_from_Metacategory (M : Metacategory) :
  Category := {|
  obj     := ∃ i : arrow M, identity M i;
  hom     := fun x y =>
    ∃ f : arrow M, composite M f (`1 x) f ∧ composite M (`1 y) f f;
  homset  := fun _ _ => {| Setoid.equiv := fun f g => `1 f = `1 g |};

  id      := fun x =>
    let f := `1 x in (f; (fst (`2 x) f, snd (`2 x) f));

  compose := fun x y z f g =>
    let fg := `1 (composite_correct
                    M (`1 f) (`1 y) (`1 g) (`1 f) (`1 g)
                    (fst (`2 y) (`1 f)) (snd (`2 y) (`1 g))) in
    (fg; (fst (`2 x) fg, snd (`2 z) fg))
|}.
Next Obligation. equivalence; simpl in *; congruence. Qed.
Next Obligation. proper; simpl in *; subst; auto. Qed.
Next Obligation.
  destruct X; simpl in *.
  destruct (composite_correct M _ _ _ _ _ _ _); simpl.
  eapply FMapExt.F.MapsTo_fun; eauto.
Qed.
Next Obligation.
  destruct X0; simpl in *.
  destruct (composite_correct M _ _ _ _ _ _ _); simpl.
  eapply FMapExt.F.MapsTo_fun; eauto.
Qed.
Next Obligation.
  destruct X1, X0; simpl in *.
  repeat destruct (composite_correct M _ _ _ _ _ _ _); simpl.
  spose (fst (composition_law M _ _ _ _ _ m1 m x3) m2) as X1.
  eapply FMapExt.F.MapsTo_fun; eauto.
Qed.
Next Obligation.
  symmetry.
  destruct X1, X0; simpl in *.
  repeat destruct (composite_correct M _ _ _ _ _ _ _); simpl.
  spose (fst (composition_law M _ _ _ _ _ m1 m x3) m2) as X1.
  eapply FMapExt.F.MapsTo_fun; eauto.
Qed.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, y at level 100, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac cleanup :=
  try FMapExt.simplify_maps;
  repeat (right; intuition; try discriminate; FMapExt.simplify_maps).

Program Definition Two : Metacategory := {|
  num_arrows := 3;
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (1, 2) +=> 2
           ;    (2, 0) +=> 2 ]%nat
|}.
Next Obligation.
  destruct f, g, h; simpl in *;
  repeat (
    FMapExt.simplify_maps; simplify;
    try omega;
    simpl in *;
    try discriminate;
    try omega).
Qed.
Next Obligation.
  unfold arrow in *.
  repeat (match goal with
  | [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H
  | [ H : _ + _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : _ ∧ _ |- _ ] => destruct H
  | [ H : ¬ (_ /\ _) |- _ ] =>
    pose proof (proj1 (not_and_implication _ _) H eq_refl);
    contradiction
  | [ |- ∃ _, M.MapsTo (?X, ?Y) _ _ ] =>
    match goal with
      [ |- context[M.add (X, Y) ?F _ ] ] =>
        exists F
    end
  end; subst; simpl in *);
  try discriminate;
  try congruence; cleanup.
Qed.
Next Obligation.
  split; intros;
  repeat FMapExt.simplify_maps;
  simpl in *;
  destruct H0, H1, H2; subst;
  intuition idtac;
  try discriminate;
  try omega; cleanup.
Qed.

(*
Require Import Category.Instance.Two.

Lemma composite_0_x_0 : forall x, composite Two 0%nat x 0%nat -> 0%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
Defined.

Lemma composite_x_0_0 : forall x, composite Two x 0%nat 0%nat -> 0%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
  discriminate.
Defined.

Lemma composite_1_x_1 : forall x, composite Two 1%nat x 1%nat -> 1%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
Defined.

Lemma composite_x_1_1 : forall x, composite Two x 1%nat 1%nat -> 1%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
Defined.

Lemma composite_2_x_2 : forall x, composite Two 2%nat x 2%nat -> 0%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
  discriminate.
Defined.

Lemma composite_x_2_2 : forall x, composite Two x 2%nat 2%nat -> 1%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
  discriminate.
  discriminate.
Defined.

Local Obligation Tactic := program_simpl; simpl in *.

Lemma not_identity : ∀ x, (2 <= x)%nat -> identity Two x -> False.
Proof.
Admitted.

Program Definition Two_to_Two : Category_from_Metacategory Two ⟶ _2 := {|
  fobj := fun x => match `1 x with
    | 0%nat => TwoX
    | 1%nat => TwoY
    | _     => False_rect _ (not_identity (`1 x) _ (`2 x))
    end;
  fmap := fun x y f => match `1 x, `1 y, `1 f with
    | 0%nat, 0%nat, 0%nat => TwoIdX
    | 1%nat, 1%nat, 1%nat => TwoIdY
    | 0%nat, 1%nat, 2%nat => TwoXY
    | _, _, _ => !
    end
|}.
Next Obligation.
  destruct x. contradiction.
  destruct x. contradiction.
  omega.
Qed.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation.
  repeat match goal with
  | [ H : Some _ = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : PO.eq _ _ |- _ ] =>
    destruct H; simpl in *; subst
  | [ H : ~ PO.eq _ _ |- _ ] =>
    unfold PO.eq in H; simpl in H;
    apply Decidable.not_and in H
  | [ H : M.find _ (M.add _ _ _) = Some _ |- _ ] =>
    rewrite FMapExt.F.add_o in H;
    destruct (PO.eq_dec _ _)
  | [ H : M.find _ (M.empty _) = Some _ |- _ ] =>
    inversion H
  | [ |- Decidable.decidable (?X = ?Y) ] =>
    destruct (Nat.eq_dec X Y); [left|right]; assumption
  end.
  - omega.
  - omega.
  - eapply not_identity; eauto.
  - eapply not_identity; eauto.
Defined.
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
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
*)
