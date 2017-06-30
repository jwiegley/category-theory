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
  | [ H : M.find (?X, ?Y) (M.add _ _ _) = Some ?F |- _ ] =>
    apply find_inv in H; destruct H as [[? [? ?]]|]
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

Program Definition Two : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (1, 2) +=> 2
           ;    (2, 0) +=> 2 ]%N
|}.
Next Obligation. destruct_maps; nomega. Defined.
Next Obligation. split; intros; destruct_maps; subst; nomega. Qed.
Next Obligation.
  destruct_maps; subst;
  eexists; eexists; intros; clear; split;
  first [ instantiate (1 := 0%N); vm_compute; reflexivity
        | instantiate (1 := 1%N); vm_compute; reflexivity ].
Defined.

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
