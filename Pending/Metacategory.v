Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Record Metacategory := {
  arrs : nat;

  composition : Fin.t arrs -> Fin.t arrs -> option (Fin.t arrs);

  is_identity u :=
    (∀ (f k : Fin.t arrs), composition f u = Some k -> k = f) *
    (∀ (g k : Fin.t arrs), composition u g = Some k -> k = g);

  identity_law :
    ∀ (g : Fin.t arrs),
      { u  : Fin.t arrs & is_identity u  &
      { u' : Fin.t arrs & is_identity u' &
        (composition g  u = Some g) *
        (composition u' g = Some g) } };

  composition_law :
    ∀ k g f kg gf,
      ((composition k g = Some kg) *
       (composition g f = Some gf)) <-->
      { kgf : Fin.t arrs
      & (composition kg f = Some kgf) *
        (composition k gf = Some kgf) }
}.

Lemma identity_morphism (M : Metacategory) :
  ∀ i (H : is_identity M i), composition M i i = Some i.
Proof.
  intros.
  destruct H.
  destruct (@identity_law M i), p, s, p, p0.
  specialize (e _ _ e6); subst; assumption.
Defined.

Lemma identity_composition_between (M : Metacategory) :
  ∀ f g u fu ug
    (H : is_identity M u)
    (fu : composition M f u = Some fu)
    (ug : composition M u g = Some ug),
      { fg : Fin.t (arrs M) & composition M f g = Some fg }.
Proof.
  intros.
  destruct H.
  pose proof (e f _ fu0).
  pose proof (e0 g _ ug0).
  subst.
  destruct (fst (@composition_law M f u g f g) (fu0, ug0)), p.
  exists x.
  assumption.
Defined.

Lemma identity_composition_left (M : Metacategory) :
  ∀ f g u fg uf
    (H : is_identity M u)
    (_ : composition M f g = Some fg)
    (_ : composition M u f = Some uf),
      composition M u fg = Some fg.
Proof.
  intros.
  destruct H.
  destruct (fst (@composition_law M u f g uf fg) (H1, H0)), p.
  specialize (e0 _ _ e2); subst; assumption.
Defined.

Lemma identity_composition_right (M : Metacategory) :
  ∀ f g u fg gu
    (H : is_identity M u)
    (_ : composition M f g = Some fg)
    (_ : composition M g u = Some gu),
      composition M fg u = Some fg.
Proof.
  intros.
  destruct H.
  destruct (fst (@composition_law M f g u fg gu) (H0, H1)), p.
  specialize (e _ _ e1); subst; assumption.
Defined.

Local Obligation Tactic := intros.

(*
Program Definition Metacategory_Category (M : Metacategory) : Category := {|
  (* The objects of the category are given by all the identity arrows of the
     arrows-only metacategory. *)
  ob  := { i : Fin.t (arrs M) & is_identity M i };

  (* The morphisms of the category from id[x] to id[y] are given by those
     arrows whose domain composes with id[x], and whose codomain composes with
     id[y]. *)
  hom := fun x y =>
    { f : Fin.t (arrs M)
    & (composition M f (``x) = Some f) *
      (composition M (``y) f = Some f) };

  homset := fun _ _ => {| equiv := fun f g => ``f = ``g |};

  id := fun x =>
          let morph := identity_morphism M (``x) (`2 x) in
          (``x; (morph, morph))
|}.
Next Obligation.
  equivalence; simpl in *; subst; reflexivity.
Qed.
Next Obligation.                (* compose *)
  simpl in *.
  destruct A as [x x_id].
  destruct B as [y y_id].
  destruct C as [z z_id].
  destruct f as [f [fl fr]].
  destruct g as [g [gl gr]].
  simpl in *.
  set (fg := identity_composition_between M f g y f g y_id fl gr).
  exact (``fg;
         (identity_composition_right M f g x (``fg) g x_id (`2 fg) gl,
          identity_composition_left M f g z (``fg) f z_id (`2 fg) fr)).
Defined.
Next Obligation.
  proper.
  simpl in *; subst.
  unfold identity_composition_between; simpl.
  destruct e0; simpl.
  unfold eq_rec_r, eq_rec, eq_rect, eq_sym.
  do 2 destruct (e0 x4 x4).
  do 2 destruct (e2 x1 x1).
  destruct (composition_law M x4 x8 x1 x4 x1); simpl.
  destruct s.
  destruct s.
  destruct p0, p1.
  rewrite e3 in e5.
  inversion e5; subst.
  refine (f_equal _ _).
  refine (f_equal _ _).
  apply Eqdep_dec.UIP_dec.
  intros.
  destruct x3, y3; intuition.
Next Obligation.
  simpl in *.
  unfold Metacategory_Category_obligation_2; simpl in *.
  destruct X, Y, f, p; simpl in *.
Admitted.                       (* DEFERRED *)
Next Obligation.
Admitted.                       (* DEFERRED *)
Next Obligation.
Admitted.                       (* DEFERRED *)
Next Obligation.
Admitted.                       (* DEFERRED *)
*)
