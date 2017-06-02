Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.DecidableTypeEx.
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
    composite g f gf -> ∃ kgf : arr, composite kg f kgf;

  (* Third axiom: *)

  (* "For each arrow g of C there exist identity arrows u and u' of C such
     that u'∙g and g∙u are defined." *)
  identity_law (g : arr) :
    ∃ u u' : arr,
      identity u ∧ identity u' ∧
      defined g  u pairs ∧ defined u' g pairs;
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
  apply composite_defined with (h:=``H3).
  exact `2 H3.
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

Global Program Definition FromArrows (M : Metacategory) := {|
  (* The objects of the category are given by all the identity arrows of the
     arrows-only metacategory. *)
  ob  := { i : arr M & identity M i };

  (* The morphisms of the category from id[x] to id[y] are given by those
     arrows whose domain composes with id[x], and whose codomain composes with
     id[y]. *)
  hom := fun x y =>
    { f : arr M & defined f ``x (pairs M) & defined ``y f (pairs M) };

  homset := fun _ _ => {| Setoid.equiv :=
    fun f g => `1 (sigT_of_sigT2 f) = `1 (sigT_of_sigT2 g) |}
|}.
Next Obligation.
  equivalence; simpl in *; subst.
  destruct x, y, z; subst; reflexivity.
Qed.
Next Obligation.                (* id *)
  destruct A as [i [Hil Hir]].
  exists i; apply composite_defined with (h:=i); auto.
Defined.
Next Obligation.                (* compose *)
  destruct A as [x x_id];
  destruct B as [y y_id];
  destruct C as [z z_id];
  destruct f as [f fl fr];
  destruct g as [g gl gr]; simpl in *.
  pose proof (identity_composition_between M f g y y_id fl gr).
  destruct (defined_composite _ _ _ H) as [fg Hfg].
  exists fg.
    eapply identity_composition_right; eauto.
  eapply identity_composition_left; eauto.
Defined.
Next Obligation.
  proper.
  unfold FromArrows_obligation_3; simpl.
  destruct x, y, x0, y0; simpl in *; subst.
  destruct (defined_composite _ _ _); reflexivity.
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct X, Y, f, i, i0; simpl in *; subst.
  destruct (defined_composite _ _ _).
  pose proof (c2 x1).
  unfold composite in c3, H.
  apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct X, Y, f, i, i0; simpl in *; subst.
  destruct (defined_composite _ _ _).
  pose proof (c x1).
  unfold composite in c3, H.
  apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct X as [x [xl_id xr_id]];
  destruct Y as [y [yl_id yr_id]];
  destruct Z as [z [zl_id zr_id]];
  destruct W as [w [wl_id wr_id]];
  destruct f as [f fl fr];
  destruct g as [g gl gr];
  destruct h as [h hl hr];
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

End Metacategory.
