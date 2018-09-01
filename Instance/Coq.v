Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.Endo.
Require Export Category.Theory.Monad.
Require Export Category.Theory.Morphisms.
Require Export Category.Structure.BiCCC.
Require Export Category.Structure.Constant.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance Coq : Category := {
  obj     := Type;
  hom     := fun A B : Type => A -> B;
  homset  := fun _ _ => {| equiv := fun f g => forall x, f x = g x |};
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation. proper; congruence. Qed.

Program Instance Coq_Terminal : @Terminal Coq := {
  terminal_obj := unit : Type;
  one := fun _ a => tt
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

Program Instance Coq_Cartesian : @Cartesian Coq := {
  product_obj := fun x y => x * y : Type;
  fork := fun _ _ _ f g x => (f x, g x);
  exl  := fun _ _ p => fst p;
  exr  := fun _ _ p => snd p
}.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  intros; simplify; intros.
  - rewrite H; reflexivity.
  - rewrite H; reflexivity.
  - intros; simplify.
    rewrite <- H, <- H0.
    rewrite <- surjective_pairing; reflexivity.
Qed.

Program Instance Coq_Closed : @Closed Coq _ := {
  exponent_obj := Basics.arrow;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (a, b) |}
     ; from := {| morphism := fun f p => f (fst p) (snd p) |} |}
}.
Next Obligation. proper; extensionality X0; congruence. Qed.
Next Obligation. proper; congruence. Qed.

Program Instance Coq_Initial : Initial Coq := {
  terminal_obj := False;
  one := fun _ _ => False_rect _ _
}.
Next Obligation. contradiction. Qed.

Program Instance Coq_Cocartesian : @Cocartesian Coq := {
  product_obj := sum;
  fork := fun _ _ _ f g x =>
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := fun _ _ p => Datatypes.inl p;
  exr  := fun _ _ p => Datatypes.inr p
}.
Next Obligation.
  split; intros.
    split; intros;
    rewrite H; reflexivity.
  destruct x0; firstorder.
Qed.

Lemma injectivity_is_monic `(f : x ~> y) :
  (∀ x y, f x = f y → x = y) ↔ Monic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    apply HA, HB.
  - intros HA ?? HB.
    pose (fun (_ : unit) => x0) as const_x.
    pose (fun (_ : unit) => y0) as const_y.
    destruct HA.
    specialize (monic unit const_x const_y).
    unfold const_x in monic.
    unfold const_y in monic.
    eapply monic; eauto.
    simpl; intuition.
    exact tt.
Qed.

Lemma surjectivity_is_epic `(f : x ~> y) :
  (∀ y, exists x, f x = y)%type ↔ Epic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    specialize (HA x0).
    destruct HA as [? HA].
    rewrite <- HA.
    apply HB.
  - intros HA ?.
    destruct HA.
    specialize epic with (z := Prop).
    specialize epic with (g1 := fun y0 => (exists x0, f x0 = y0)%type).
    simpl in *.
    specialize epic with (g2 := fun y => True).
    erewrite epic.
      constructor.
    intros.
    Axiom propositional_extensionality : forall P : Prop, P -> P = True.
    apply propositional_extensionality.
    exists x0.
    reflexivity.
Qed.

Program Definition option_Functor : Coq ⟶ Coq := {|
  fmap := option_map
|}.
Next Obligation.
  proper.
  destruct x1; simpl; auto.
  now rewrite H.
Qed.
Next Obligation. now destruct x0. Qed.
Next Obligation. now destruct x0. Qed.

Program Instance optionF : EndoFunctor option :=
  Functor_EndoFunctor (F:=option_Functor).

Global Program Instance option_Monad : @Monad Coq option_Functor := {
  ret := @Some;
  join := fun _ x =>
    match x with
    | Some (Some x) => Some x
    | _ => None
    end
}.
Next Obligation.
  destruct x0; simpl; auto.
  destruct o; auto.
  destruct o; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
  destruct o; auto.
Qed.

Program Definition list_Functor : Coq ⟶ Coq := {|
  fmap := List.map
|}.
Next Obligation.
  proper.
  induction x1; simpl; auto.
  now rewrite H, IHx1.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  now rewrite IHx0.
Qed.
Next Obligation.
  induction x0; simpl; auto.
  now rewrite IHx0.
Qed.

Program Instance listF : EndoFunctor list :=
  Functor_EndoFunctor (F:=list_Functor).
