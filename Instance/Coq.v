Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Structure.BiCCC.
Require Export Category.Structure.Constant.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance Coq : Category := {
  ob      := Type;
  hom     := fun A B : Type => A -> B;
  homset  := fun _ _ => {| equiv := fun f g => forall x, f x = g x |};
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation. proper; congruence. Qed.

Program Instance Coq_Terminal : @Terminal Coq := {
  One := unit : Type;
  one := fun _ a => tt
}.
Next Obligation. destruct (f x), (g x); reflexivity. Qed.

Program Instance Coq_Cartesian : @Cartesian Coq := {
  Prod := prod;
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
  Exp := Basics.arrow;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (a, b) |}
     ; from := {| morphism := fun f p => f (fst p) (snd p) |} |}
}.
Next Obligation. proper; extensionality X0; congruence. Qed.
Next Obligation. proper; congruence. Qed.

Program Instance Coq_Initial : Initial Coq := {
  One := False;
  one := fun _ _ => False_rect _ _
}.
Next Obligation. contradiction. Qed.

Program Instance Coq_Cocartesian : @Cocartesian Coq := {
  Prod := sum;
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
  destruct x; firstorder.
Qed.

Lemma injectivity_is_monic `(f : X ~> Y) :
  (∀ x y, f x = f y → x = y) ↔ Monic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    apply HA, HB.
  - intros HA ?? HB.
    autounfold in *.
    simpl in *.
    pose (fun (_ : unit) => x) as const_x.
    pose (fun (_ : unit) => y) as const_y.
    destruct HA.
    specialize (monic unit const_x const_y).
    unfold const_x in monic.
    unfold const_y in monic.
    eapply monic; eauto.
    simpl; intuition.
    exact tt.
Qed.

Lemma surjectivity_is_epic `(f : X ~> Y) :
  (∀ y, exists x, f x = y)%type ↔ Epic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    specialize (HA x).
    destruct HA as [? HA].
    rewrite <- HA.
    apply HB.
  - intros HA ?.
    destruct HA.
    specialize epic with (Z := Prop).
    specialize epic with (g1 := fun y0 => (exists x0, f x0 = y0)%type).
    simpl in *.
    specialize epic with (g2 := fun y => True).
    erewrite epic.
      constructor.
    intros.
    Axiom propositional_extensionality : forall P : Prop, P -> P = True.
    apply propositional_extensionality.
    exists x.
    reflexivity.
Qed.
