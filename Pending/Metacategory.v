Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition prod_dec (x y : nat * nat) : {x = y} + {x <> y}.
Proof.
  destruct x, y.
  destruct (PeanoNat.Nat.eq_dec n n1), (PeanoNat.Nat.eq_dec n0 n2).
  - left; congruence.
  - right; congruence.
  - right; congruence.
  - right; congruence.
Defined.

Definition defined (x y : nat) (xs : set (nat * nat)) :=
  set_mem prod_dec (x, y) xs = true.

(* Mac Lane: "Since the objects of a metacategory correspond exactly to its
   identity arrows, it is technically possible to dispense altogether with the
   objects and deal only with arrows." *)
Record Metacategory := {
  (* "The data for an arrows-only metacategory C consist of arrows," *)
  arr := nat;

  (* "certain ordered pairs ⟨g, f⟩, called the composable pairs of arrows," *)
  pairs : set (arr * arr);

  (* "and an operation assigning to each composable pair ⟨g, f⟩ an arrow g∙f,
     called their composite. We say 'g∙f is defined' for '⟨g, f⟩ is a
     composable pair'". *)
  composite x y : defined x y pairs -> arr;

  (* "With these data one defines an identity of C to be an arrow u such that
     f∙u = f whenever the composite f∙u is defined and u∙g = g whenever u∙g is
     defined." *)
  identity u :=
    (∀ (f : arr) (H : defined f u pairs), composite f u H = f) *
    (∀ (g : arr) (H : defined u g pairs), composite u g H = g);

  (* "The data are then required to satisfy the following three axioms:" *)

  (* First axiom: *)

  (* "The composite (k∙g)∙f is defined if and only if the composite k∙(g∙f) is
     defined." *)
  composition_law :
    ∀ k g f (kg : defined k g pairs) (gf : defined g f pairs),
      defined (composite k g kg) f pairs <-->
      defined k (composite g f gf) pairs;

   (* "When either is defined, they are equal (and this triple composite is
      written as k∙g∙f)." *)
  triple_equality :
    ∀ k g f
      (kg : defined k g pairs)
      (gf : defined g f pairs)
      (kg_f : defined (composite k g kg) f pairs)
      (k_gf : defined k (composite g f gf) pairs),
      composite (composite k g kg) f kg_f = composite k (composite g f gf) k_gf;

  (* Second axiom: *)

  (* "The triple composite k∙g∙f is defined whenever both composites k∙g and
     g∙f are defined." *)
  triple_composition :
    ∀ k g f (kg : defined k g pairs) (gf : defined g f pairs),
      defined (composite k g kg) f pairs;

  (* Third axiom: *)

  (* "For each arrow g of C there exist identity arrows u and u' of C such
     that u'∙g and g∙u are defined." *)
  identity_law :
    ∀ (g : arr),
      { u  : arr & identity u  & defined g  u pairs } *
      { u' : arr & identity u' & defined u' g pairs };

  (* The domain of any arrow is the identity arrow it composes with; and
     likewise for the codomain. We then relate these to the meaning of
     identity and composition. *)
  dom : arr -> arr;
  dom_law f g : dom f = g <--> identity g * defined f g pairs;

  cod : arr -> arr;
  cod_law f g : cod f = g <--> identity g * defined g f pairs;

  dom_cod f g : defined f g pairs <--> { x : arr & dom f = x & cod g = x };

  dom_composite f g (H : defined f g pairs) x :
    dom (composite f g H) = x <--> dom g = x;
  cod_composite f g (H : defined f g pairs) x :
    cod (composite f g H) = x <--> cod f = x;
}.

Lemma identity_morphism (M : Metacategory) :
  ∀ i, identity M i
    -> { H : defined i i (pairs M) & composite M i i H = i }.
Proof.
  intros.
  destruct H.
  destruct (@identity_law M i), s, s0, p, p0.
  specialize (e0 _ d).
  specialize (e1 _ d).
  rewrite e0 in e1; subst.
  exact (d; e0).
Defined.

Lemma identity_composition_between (M : Metacategory) :
  ∀ f g u,
    identity M u ->
    defined f u (pairs M) ->
    defined u g (pairs M) ->
    defined f g (pairs M).
Proof.
  intros.
  destruct H.
  pose proof (e f H0).
  pose proof (e0 g H1).
  pose proof (@triple_composition M f u g H0 H1) as H3;
  simpl in H3.
  rewrite H in H3.
  apply H3.
Defined.

Lemma identity_composition_left (M : Metacategory) :
  ∀ f g u,
    identity M u ->
    ∀ (H : defined f g (pairs M)),
    defined u f (pairs M) ->
    defined u (composite M f g H) (pairs M).
Proof.
Admitted.

Lemma identity_composition_right (M : Metacategory) :
  ∀ f g u,
    identity M u ->
    ∀ (H : defined f g (pairs M)),
    defined g u (pairs M) ->
    defined (composite M f g H) u (pairs M).
Proof.
Admitted.

Local Obligation Tactic := intros.

(*
Program Definition Metacategory_Category (M : Metacategory) : Category := {|
  (* The objects of the category are given by all the identity arrows of the
     arrows-only metacategory. *)
  ob  := { i : arr M & identity M i };

  (* The morphisms of the category from id[x] to id[y] are given by those
     arrows whose domain composes with id[x], and whose codomain composes with
     id[y]. *)
  hom := fun x y => { f : arr M & dom M f = ``x & cod M f = ``y };

  homset := fun _ _ => {| equiv :=
    fun f g => `1 (sigT_of_sigT2 f) = `1 (sigT_of_sigT2 g) |}
|}.
Next Obligation.
  equivalence; simpl in *; subst.
  destruct x, y, z; subst; reflexivity.
Qed.
Next Obligation.                (* id *)
  destruct A; simpl.
  pose (`1 (identity_morphism M x i)).
  destruct i.
  exists x.
    apply dom_law; intuition.
  apply cod_law; intuition.
Defined.
Next Obligation.                (* compose *)
  destruct A as [x x_id];
  destruct B as [y y_id];
  destruct C as [z z_id];
  destruct f as [f fl fr];
  destruct g as [g gl gr]; simpl in *.
  exists (composite M f g (snd (dom_cod M f g) (existT2 _ _ y fl gr))).
    apply dom_composite; assumption.
  apply cod_composite; assumption.
Defined.
Next Obligation.
  unfold Metacategory_Category_obligation_3; simpl.
  proper.
  destruct x, y, x0, y0; simpl in *; subst.
  refine (f_equal _ _).
  refine (f_equal _ _).
  refine (f_equal2 _ _ _);
  apply (Eqdep_dec.UIP_dec PeanoNat.Nat.eq_dec).
Qed.
*)
