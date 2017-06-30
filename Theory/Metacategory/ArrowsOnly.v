Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Fin.
Require Import Coq.FSets.FMaps.
Require Import Coq.omega.Omega.

Require Import Category.Lib.
Require Import Category.Lib.FMapExt.
Require Import Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Module PO := PairOrderedType Nat_as_OT Nat_as_OT.
Module Import M := FMapList.Make(PO).
Module Import FMapExt := FMapExt PO M.

(* An arrows-only meta-category defines identity arrows as those which, when
   composed to the left or right of another arrow, result in that same arrow.
   This definition requires that all such composition be present. *)

Record Metacategory := {
  num_arrows : nat;
  arrow := Fin.t num_arrows;

  pairs : M.t arrow;

  composite (f g h : arrow) := M.MapsTo (` (to_nat f), ` (to_nat g)) h pairs;
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

  identity_law (f : arrow) :
    ∃ u u', is_identity u -> is_identity u' ->
      composite f u f ∧ composite u' f f
}.

Lemma MapsTo_dec (M : Metacategory) : ∀ elt k e (m : M.t elt),
  (∀ x y : elt, {x = y} + {x ≠ y}) ->
  { M.MapsTo k e m } + { ~ M.MapsTo k e m }.
Proof.
  intros.
  destruct (M.find k m) eqn:?.
    apply F.find_mapsto_iff in Heqo.
    destruct (X e e0); subst.
      left; assumption.
    right; unfold not; intros.
    pose proof (F.MapsTo_fun H Heqo).
    contradiction.
  apply F.not_find_in_iff in Heqo.
  right.
  apply not_in_mapsto_iff.
  assumption.
Qed.

(* Every meta-category, defined wholly in terms of the axioms of category
   theory, gives rise to a category interpreted in the context of set
   theory. *)

Local Obligation Tactic := intros.

Section Metacategory.

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
  spose (fst (composition_law M c0 H _) m) as X.
  pose proof (F.MapsTo_fun H m); subst.
  apply X.
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
  spose (fst (composition_law M H c _) m) as X.
  pose proof (F.MapsTo_fun H X); subst.
  apply m.
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
Next Obligation. equivalence; congruence. Qed.

Lemma composition_identity_left {x y : object} (f : morphism x y) :
  composition (identity y) f ≈ f.
Proof.
  destruct f; simpl.
  destruct (composite_correct _ _ _); simpl in *.
  eapply F.MapsTo_fun; eauto.
Qed.

Lemma composition_identity_right {x y : object} (f : morphism x y) :
  composition f (identity x) ≈ f.
Proof.
  destruct f; simpl.
  destruct (composite_correct _ _ _); simpl in *.
  eapply F.MapsTo_fun; eauto.
Qed.

Lemma composition_associative {x y z w : object}
      (f : morphism z w) (g : morphism y z) (h : morphism x y) :
  composition f (composition g h) ≈ composition (composition f g) h.
Proof.
  destruct f, g, h; simpl.
  repeat destruct (composite_correct _ _ _); simpl in *.
  spose (fst (composition_law M m1 m x3) m2) as X1.
  eapply F.MapsTo_fun; eauto.
Qed.

Lemma composition_respects {x y z : object} :
  Proper (equiv ==> equiv ==> equiv) (@composition x y z).
Proof.
  proper.
  destruct x0, y0, x1, y1; simpl in *; subst.
  repeat destruct (composite_correct _ _ _); simpl in *.
  eapply F.MapsTo_fun; eauto.
Qed.

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

End Metacategory.

Arguments mor_arr _ {_ _} _.
Arguments mor_dom _ {_ _} _.
Arguments mor_cod _ {_ _} _.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x (@of_nat_lt y _ _))
  (at level 9, y at level 100, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac cleanup :=
  try simplify_maps;
  repeat (right; intuition; try discriminate; simplify_maps).

Local Obligation Tactic := program_simpl; try abstract omega.

Lemma mapsto_inv : ∀ n f g (fg : Fin.t n) x y z m,
  M.MapsTo (f, g) fg (M.add (x, y) z m) ->
    (f = x ∧ g = y ∧ fg = z) ∨ M.MapsTo (f, g) fg m.
Proof.
Admitted.

Ltac destruct_maps :=
  repeat lazymatch goal with
  | [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
    contradiction (proj1 (F.empty_mapsto_iff _ _) H)

  | [ H : M.MapsTo (?X, ?Y) ?F (M.add _ _ _) |- _ ] =>
    apply mapsto_inv in H; destruct H as [[? [? ?]]|]

  | [ H : ?X = ?Y |- context[M.MapsTo (` (to_nat ?X), _)] ] =>
    rewrite H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo (_, ` (to_nat ?X))] ] =>
    rewrite H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo (?X, _)] ] =>
    rewrite H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo (_, ?X)] ] =>
    rewrite H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo _ ?X] ] =>
    rewrite H; cbn

  | [ |- ∃ _, M.MapsTo (?X, ?Y) _ _ ] =>
    match goal with
      [ |- context[M.add (X, Y) ?F _ ] ] =>
      exists F
    end
  | [ |- M.MapsTo (?X, ?Y) ?F (M.add (?X, ?Y) ?F _) ] =>
    simplify_maps
  | [ |- M.MapsTo _ _ (M.add _ _ _) ] =>
    simplify_maps; right; split; [omega|]
  end;
  try congruence.

(*
Require Export FMapDec.fmap_decide.

Module Import O <: OptionalDecidableType.
  Monomorphic Definition X := Fin.t 3.
  Monomorphic Definition o_eq_dec : option (forall (x y: X), {x = y} + {x <> y}).
  Proof. apply Some, Fin.eq_dec. Defined.
End O.

Module Export FMapDecide := FMapDecide PO M O.
*)

Program Definition Two : Metacategory := {|
  num_arrows := 3;
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (1, 2) +=> 2
           ;    (2, 0) +=> 2 ]%nat
|}.
Next Obligation. destruct_maps. Qed.
Next Obligation.
  split; intros;
  destruct_maps;
  subst; discriminate.
Qed.
Next Obligation.
  destruct f using caseS'.
    eexists; eexists; intros.
    simplify; simpl in *.
    instantiate (1:=F1); simpl; destruct_maps.
    instantiate (1:=F1); simpl; destruct_maps.
  destruct f using caseS'.
    eexists; eexists; intros.
    simplify; simpl in *.
    instantiate (1:=FS F1); simpl; destruct_maps.
    instantiate (1:=FS F1); simpl; destruct_maps.
  destruct f using caseS'.
    eexists; eexists; intros.
    simplify; simpl in *.
    instantiate (1:=F1); simpl; destruct_maps.
    instantiate (1:=FS F1); simpl; destruct_maps.
  inversion f.
Qed.

Require Import Category.Instance.Two.

Local Obligation Tactic := program_simpl; simpl in *.

Program Definition Two_2_object (x : object Two) : TwoObj.
Proof.
  destruct x.
  destruct obj_arr0 using caseS'.
    exact TwoX.
  destruct p using caseS'.
    exact TwoY.
  destruct p using caseS'.
    unfold composite in obj_def0.
    cbn in obj_def0.
    apply mapsto_inv in obj_def0; destruct obj_def0 as [[? [? ?]]|].
      discriminate.
    apply mapsto_inv in m; destruct m as [[? [? ?]]|].
      discriminate.
    apply mapsto_inv in m; destruct m as [[? [? ?]]|].
      discriminate.
    apply mapsto_inv in m; destruct m as [[? [? ?]]|].
      discriminate.
    destruct_maps.
  inversion p.
Defined.

Program Definition Two_2_morphism (x y : object Two) (f : morphism Two x y) :
  TwoHom (Two_2_object x) (Two_2_object y).
Proof.
Admitted.

Program Definition Two_to_Two : Category_from_Metacategory Two ⟶ _2 := {|
  fobj := Two_2_object;
  fmap := Two_2_morphism
|}.
Next Obligation.
  proper.
  destruct x0, y0; simpl in *; subst.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
