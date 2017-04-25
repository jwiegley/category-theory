Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Structure.BiCCC.
Require Export Category.Structure.Constant.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Instance Coq : Category := {
  ob      := Type;
  hom     := fun A B : Type => A -> B;
  homset  := fun _ _ => {| equiv := fun f g => forall x, f x = g x |};
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
}.
Obligation 1. equivalence; congruence. Qed.
Obligation 2. proper; congruence. Qed.

Program Instance Coq_Terminal : @Terminal _ := {
  One := unit : Type;
  one := fun _ a => tt
}.
Next Obligation. destruct (f x), (g x); reflexivity. Qed.

Program Instance Coq_Cartesian : @Cartesian _ := {
  Prod := prod;
  fork := fun _ _ _ f g x => (f x, g x);
  exl  := fun _ _ p => fst p;
  exr  := fun _ _ p => snd p
}.
Next Obligation. congruence. Qed.
Next Obligation.
  split; intros; intuition;
  try (rewrite H; simpl; reflexivity).
  rewrite <- H0, <- H1, <- surjective_pairing; reflexivity.
Qed.

Program Instance Coq_Closed : @Closed _ _ := {
  Exp := Basics.arrow;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (a, b) |}
     ; from := {| morphism := fun f p => f (fst p) (snd p) |} |}
}.
Next Obligation. proper; extensionality b; intuition. Qed.
Next Obligation. proper; congruence. Qed.

Program Instance Coq_Initial : Initial _ := {
  Zero := False;
  zero := fun _ _ => False_rect _ _
}.

Program Instance Coq_Cocartesian : @Cocartesian _ := {
  Coprod := sum;
  merge := fun _ _ _ f g x =>
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  inl  := fun _ _ p => Datatypes.inl p;
  inr  := fun _ _ p => Datatypes.inr p
}.
Next Obligation.
  split; intros.
    split; intros;
    rewrite H; reflexivity.
  destruct x; firstorder.
Qed.

Lemma injectivity_is_monic `(f : X ~> Y) :
  (∀ x y, f x = f y → x = y) <-> Monic f.
Proof.
  split.
  - intros HA.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    apply HA, HB.
  - intros HA ?? HB.
    autounfold in *.
    simpl in *.
    pose (fun (_ : unit) => x) as const_x.
    pose (fun (_ : unit) => y) as const_y.
    specialize (HA unit const_x const_y).
    unfold const_x in HB.
    unfold const_y in HB.
    simpl in HB.
    eapply HA; eauto.
    Unshelve.
    eexact tt.
Qed.

Lemma surjectivity_is_epic `(f : X ~> Y) :
  (∀ y, ∃ x, f x = y)%type <-> Epic f.
Proof.
  split.
  - intros HA.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    specialize (HA x).
    destruct HA as [? HA].
    rewrite <- HA.
    apply HB.
  - intros HA ?.
    unfold Epic in HA.
    specialize HA with (Z := Prop).
    specialize HA with (g1 := fun y0 => (∃ x0, f x0 = y0)%type).
    simpl in *.
    specialize HA with (g2 := fun y  => True).
    erewrite HA.
      constructor.
    intros.
    apply propositional_extensionality.
    exists x.
    reflexivity.
Qed.
