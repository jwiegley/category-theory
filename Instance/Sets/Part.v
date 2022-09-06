Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The category of partial maps, built on the category of setoids. *)

Program Definition Part : Category := {|
  obj := Sets;
  hom := fun x y =>
    @SetoidMorphism x (is_setoid x) (option y) (@option_setoid _ (is_setoid y));
  homset := fun x y =>
    @SetoidMorphism_Setoid x {| is_setoid := @option_setoid _ (is_setoid y) |}
|}.
Next Obligation.
  construct.
  - exact (Some X).
  - proper.
Defined.
Next Obligation.
  construct.
  - destruct (g X) as [b|].
    + exact (f b).
    + exact None.
  - proper.
    destruct f, g; simpl.
    spose (proper_morphism0 _ _ X) as X1.
    destruct (morphism0 x0); auto;
    destruct (morphism0 y0); auto.
    + spose (proper_morphism _ _ X1) as X2.
      destruct (morphism c); auto;
      destruct (morphism c0); auto.
    + contradiction.
    + contradiction.
Defined.
Next Obligation.
  proper.
  specialize (X0 x2).
  destruct (x1 x2); auto.
  - specialize (X c).
    destruct (x0 c); auto;
    destruct (y1 x2); auto;
    destruct y0; simpl in *;
    spose (proper_morphism _ _ X0) as X1.
    + destruct (morphism c); auto;
      destruct (morphism c1); try tauto.
      now transitivity c2.
    + destruct (morphism c); auto;
      destruct (morphism c0); tauto.
  - destruct (y1 x2); auto.
    contradiction.
Qed.
Next Obligation.
  intros.
  destruct (f x0); auto.
  reflexivity.
Qed.
Next Obligation.
  intros.
  destruct (f x0); auto.
  reflexivity.
Qed.
Next Obligation.
  intros.
  destruct (h x0); auto.
  destruct (g c); auto.
  destruct (f c0); auto.
  reflexivity.
Qed.
Next Obligation.
  intros.
  destruct (h x0); auto.
  destruct (g c); auto.
  destruct (f c0); auto.
  reflexivity.
Qed.

Require Import Category.Structure.Cartesian.


Arguments option_setoid A {_}.
Arguments sum_setoid A B {_ _}.

#[export]
Program Instance Part_Cartesian : @Cartesian Part := {
  product_obj := fun x y =>
    {| carrier := sum (carrier x) (sum (carrier y) (carrier x * carrier y)) |}
}.
Next Obligation.
  destruct x, y.
  proper.
Defined.
Next Obligation.
  construct.
  - destruct (f H) as [b|].
    + destruct (g H) as [c|].
      * exact (Some (Datatypes.inr (Datatypes.inr (b, c)))).
      * exact (Some (Datatypes.inl b)).
    + destruct (g H) as [c|].
      * exact (Some (Datatypes.inr (Datatypes.inl c))).
      * exact None.
  - proper.
    try rename H into X.
    destruct f, g; simpl in *.
    spose (proper_morphism _ _ X) as X1.
    destruct (morphism x0);
    destruct (morphism y0); try tauto;
    spose (proper_morphism0 _ _ X) as X2;
    destruct (morphism0 x0);
    destruct (morphism0 y0); try tauto.
Defined.
Next Obligation.
  unfold Part_Cartesian_obligation_1.
  construct.
  - destruct H.
    + exact (Some c).
    + destruct s.
      * exact None.
      * destruct p.
        exact (Some c).
  - proper.
    destruct x0, y0; try tauto.
    destruct s, s0; try tauto.
    try rename H into X.
    destruct p, p0, X; auto.
Defined.
Next Obligation.
  unfold Part_Cartesian_obligation_1.
  construct.
  - destruct H.
    + exact None.
    + destruct s.
      * exact (Some c).
      * destruct p.
        exact (Some c0).
  - proper.
    destruct x0, y0; try tauto.
    destruct s, s0; try tauto.
    try rename H into X.
    destruct p, p0, X; auto.
Defined.
Next Obligation.
  proper.
  try rename H into X.
  specialize (X x2).
  try rename H0 into X0.
  specialize (X0 x2).
  destruct (x0 x2), (x1 x2), (y0 x2), (y1 x2); auto.
Qed.
Next Obligation.
  split; intros.
  - try rename H into X.
    split; intros.
    + specialize (X x0).
      destruct (h x0), (f x0), (g x0); try tauto;
      destruct s; try tauto;
      destruct s; try tauto.
      destruct p, X; auto.
    + specialize (X x0).
      destruct (h x0), (f x0), (g x0); try tauto;
      destruct s; try tauto;
      destruct s; try tauto.
      destruct p, X; auto.
  - try rename H into X.
    destruct X.
    specialize (y0 x0).
    specialize (y1 x0).
    destruct (h x0), (f x0), (g x0); try tauto;
    destruct s; try tauto;
    destruct s; try tauto;
    destruct p; simpl in *; auto.
Qed.

(** This is an invalid definition, since there are three ways we could produce
    an [option c], but no way to decide which. *)
Definition to {a b c} :
  (a + (b + (a * b)) → option c) → (a → option (b → option c)) :=
  fun f a => Some (fun b => f (inr (inr (a, b)))).

(** Meanwhile, there is only one scenario that yields an [option c] here,
    leaving us unable to use the information at hand for the other two. *)
Definition from {a b c} :
  (a → option (b → option c)) → (a + (b + (a * b)) → option c) :=
  fun f x =>
    match x with
    | inl _            => None
    | inr (inl _)      => None
    | inr (inr (a, b)) =>
      match f a with
      | None => None
      | Some k => k b
      end
    end.

Lemma to_from {a b c} :
  Basics.compose to from = @Datatypes.id (a → option (b → option c)).
Proof.
  extensionality f.
  simpl.
  extensionality x.
  unfold to, from.
  destruct (f x).
  - f_equal.
    (** Stuck proving False. *)
Abort.

Lemma to_from_impossible {a b c} :
  Basics.compose to from = @Datatypes.id (a → option (b → option c))
    → inhabited a → False.
Proof.
  intros.
  pose proof (equal_f H).
  pose proof (equal_f (H1 (fun _ => None))).
  simpl in H2.
  destruct H0.
  specialize (H2 X).
  unfold to, from in H2.
  discriminate.
Qed.

Lemma from_to {a b c} :
  Basics.compose from to = @Datatypes.id (a + (b + (a * b)) → option c).
Proof.
  extensionality f.
  simpl.
  extensionality x.
  unfold to, from.
  destruct x; simpl.
    (** Stuck proving a fact we can't determine. *)
  - admit.
  - destruct s; simpl.
    + admit.
    + destruct p; auto.
Abort.

Lemma from_to_impossible {a b c} :
  Basics.compose from to = @Datatypes.id (a + (b + (a * b)) → option c)
    → inhabited a ∨ inhabited b → inhabited c → False.
Proof.
  intros.
  pose proof (equal_f H).
  destruct H1.
  pose proof (equal_f (H2 (fun _ => Some X))).
  simpl in H1.
  unfold to, from in H1.
  destruct H0, i.
  - specialize (H1 (inl X0)).
    discriminate.
  - specialize (H1 (inr (inl X0))).
    discriminate.
Qed.
