Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Adjunction.
Require Export Category.Construction.Comma.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Theorem Lawvere_Adjunction `{C : Category} `{D : Category}
        (G : C ⟶ D) (F : D ⟶ C) :
  F ⊣ G  <-->  (F ↓ Identity) ≅[Cat] (Identity ↓ G).
Proof.
  split; intros.

  destruct X.
  refine {| to   := _; from := _ |}.

  Unshelve. Focus 4.
  refine {| fobj := _; fmap := _ |}.

  Unshelve. Focus 4.
  simpl in *; intros.
  destruct X.
  exists x.
  apply adj_iso.
  exact h.

  Unshelve. Focus 4.
  simpl in *; intros.
  destruct X, Y; simpl in *.
  assumption.

  intros.
  destruct X, Y; simpl.
  proper.

  destruct X; cat.

  intros.
  destruct X, Y, Z; simpl; cat.

  Unshelve. Focus 4.
  refine {| fobj := _; fmap := _ |}.

  Unshelve. Focus 4.
  simpl; intros.
  destruct X.
  exists x.
  apply adj_iso.
  exact h.

  Unshelve. Focus 4.
  destruct X, Y; simpl; intros.
  assumption.

  destruct X, Y.
  proper.

  destruct X; simpl; cat.

  destruct X, Y, Z; cat.

  simpl; autounfold; simpl; intros.
  destruct X; simpl.
  exists (id, id); simpl.
  exists (id, id); simpl.
  cat.

  simpl; autounfold; simpl; intros.
  destruct X; simpl.
  exists (id, id); simpl.
  exists (id, id); simpl.
  cat.

  econstructor.

  Unshelve. Focus 5.
  intros;
  destruct X; simpl in *.
  autounfold in *; simpl in *.
  econstructor.

  Unshelve. Focus 4.
  simpl.
  econstructor.

  Unshelve. Focus 2.
  intros.
  pose (existT _ (a, b) X : {p : D * C & fst p ~{ D }~> G (snd p)}) as X0.
  pose proof (iso_to_from X0).
  destruct to, from; simpl in *.
  clear -fobj0 fmap0 H X X0.
  destruct (fobj0 X0) eqn:Heqe.
  unfold X0 in *.
  destruct x; simpl in *.
  destruct F, G; simpl in *.
  ?.

  proper.
  destruct to, from; simpl in *.
  ?.

  simpl; intros.
  autounfold.

  Unshelve. Focus 3.
  simpl.
  econstructor.

  Unshelve. Focus 2.
  intros.
  pose (existT _ (a, b) X : {p : D * C & F (fst p) ~{ C }~> snd p}) as X0.
  pose proof (iso_from_to X0).
  destruct to, from; simpl in *.
  clear -fobj fmap H X X0.
  destruct (fobj X0) eqn:Heqe.
  unfold X0 in *.
  destruct x; simpl in *.
  destruct F, G; simpl in *.
  ?.

  proper.
  destruct to, from; simpl in *.
  ?.

  simpl; intros.
  destruct to, from; simpl in *.
  ?.

  simpl; intros.
  autounfold.
  destruct to, from; simpl in *.
  ?.

  simpl; intros.
  ?.

  simpl; intros.
  ?.

  simpl; intros.
  ?.

  simpl; intros.
  ?.

  Unshelve.
?
