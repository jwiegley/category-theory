Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Record SetoidObject@{o p} : Type@{max(o+1,p+1)} := {
  carrier :> Type@{o};
  is_setoid :> Setoid@{o p} carrier
}.
#[export] Existing Instance is_setoid.

Record SetoidMorphism@{o h op hp} `{Setoid@{o op} x} `{Setoid@{o op} y} := {
  morphism :> x → y : Type@{h};
  proper_morphism :>
    Proper@{o op} (respectful@{o op o op o op} equiv equiv) morphism
}.
#[export] Existing Instance proper_morphism.

Arguments SetoidMorphism {_} _ {_} _.
Arguments Build_SetoidMorphism {_} _ {_} _ _ _.
Arguments morphism {_ _ _ _ _} _.

Definition SetoidMorphism_equiv@{o h op hp} {x y : SetoidObject@{o op}} :
  crelation@{h hp} (SetoidMorphism@{o h op hp} x y) :=
  fun f g => ∀ x, @equiv@{o op} _ y (f x) (g x).

Arguments SetoidMorphism_equiv {x y} _ _ /.

#[export]
Program Instance SetoidMorphism_Setoid@{o h op hp so sh sp}
  {x y : SetoidObject@{o op} : Type@{so}} :
  Setoid@{sh sp} (SetoidMorphism@{o h op hp} x y) := {|
  equiv := SetoidMorphism_equiv@{o h op hp};
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    apply X.
  - transitivity (y0 x1).
    + apply X.
    + apply X0.
Qed.

Definition setoid_morphism_id@{o h op hp} {x : SetoidObject@{o op}} :
  SetoidMorphism@{o h op hp} x x := {|
  morphism := Datatypes.id
|}.

#[export] Hint Unfold setoid_morphism_id : core.

Program Definition setoid_morphism_compose@{o h op hp}
  {x y z : SetoidObject@{o op}}
  (g : SetoidMorphism@{o h op hp} y z)
  (f : SetoidMorphism@{o h op hp} x y) : SetoidMorphism@{o h op hp} x z := {|
  morphism := Basics.compose g f
|}.

#[export] Hint Unfold setoid_morphism_compose : core.

Program Definition setoid_morphism_compose_respects@{o op so sh sp}
  {x y z : SetoidObject@{o op} : Type@{so}} :
  Proper@{sh sp} (equiv@{sh sp} ==> equiv@{sh sp} ==> equiv@{sh sp})
    (@setoid_morphism_compose x y z).
Proof.
  unfold Proper, respectful.
  simpl; intros.
  rewrite X.
  apply proper_morphism, X0.
Qed.

(* The category of setoids.

       objects: setoids
        arrows: setoid homomorphisms
      identity: typical identity of sets
   composition: composition of set maps, preserving equivalence
 *)
Program Definition Sets@{o h op hp so sh sp} : Category@{so sh sp} := {|
  obj     := SetoidObject@{o op} : Type@{so};
  hom     := λ x y, SetoidMorphism@{o h op hp} x y : Type@{sh};
  homset  := @SetoidMorphism_Setoid@{o h op hp so sh sp};
  id      := @setoid_morphism_id@{o h op hp};
  compose := @setoid_morphism_compose@{o h op hp};

  compose_respects := @setoid_morphism_compose_respects@{o op so sh sp}
|}.

Require Import Category.Theory.Isomorphism.

(* An isomorphism between arrows in a category C is an isomorphism of objects
   in the category of set(oid)s, taking [hom] to the be the carrier type, and
   arrow equivalence to be the setoid. By using Sets in this way, we gain the
   fact that the arrows on both sides are respectful of C's notion of arrow
   equivalence. *)
Notation "x ≊ y" := ({| carrier := x |} ≅[Sets] {| carrier := y |})
  (at level 99) : category_scope.

#[export]
Program Instance isomorphism_to_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (to iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct to; simpl in *.
  rewrite X; reflexivity.
Qed.

#[export]
Program Instance isomorphism_from_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (from iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct from; simpl in *.
  rewrite X; reflexivity.
Qed.

Ltac morphism :=
  unshelve (refine {| morphism := _ |}; simpl; intros).

Require Import Category.Structure.Terminal.

#[export]
Program Instance Unit_Setoid : Setoid poly_unit := {
  equiv := fun x y => x = y
}.

#[export]
Program Instance Sets_Terminal : @Terminal Sets := {
  terminal_obj := {| carrier := poly_unit |};
  one := fun _ => {| morphism := fun _ => ttt |};
  one_unique := fun x f g => _
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

Require Import Category.Structure.Initial.

#[export]
Program Instance False_Setoid : Setoid False.

#[export]
Program Instance Sets_Initial : @Initial Sets := {
  terminal_obj := {| carrier := False |};
  one := _
}.
Next Obligation.
  construct.
  - contradiction.
  - proper.
Qed.
Next Obligation. contradiction. Qed.

Require Import Category.Structure.Monoidal.

#[export]
Program Instance Sets_Product_Monoidal : @Monoidal Sets := {
  I      := {| carrier := poly_unit |};
  tensor := {|
    fobj := fun p =>
      {| carrier := carrier (fst p) * carrier (snd p)
       ; is_setoid := _
       |};
    fmap := fun x y f =>
      {| morphism := fun p => (fst f (fst p), snd f (snd p))
       ; proper_morphism := _ |}
  |}
}.
Next Obligation.
  construct.
  - repeat intro.
    destruct s, s0.
    try rename X into H.
    try rename X0 into H0.
    exact (fst H ≈ fst H0 ∧ snd H ≈ snd H0).
  - simpl.
    equivalence.
Defined.
Next Obligation.
  proper; simpl in *.
  - destruct s.
    now rewrites.
  - destruct s0.
    now rewrites.
Qed.
Next Obligation.
  construct.
  - construct.
    + try rename X into H.
      now destruct H.
    + proper.
  - construct.
    + split; [ exact ttt | assumption ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct p.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + try rename X into H.
      now destruct H.
    + proper.
  - construct.
    + split; [ assumption | exact ttt ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct p.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + simplify; auto.
    + proper.
  - construct.
    + simplify; auto.
    + proper.
  - simpl.
    simplify; simpl; cat.
  - simpl.
    simplify; simpl; cat.
Defined.

Definition unit_setoid_object@{t u} : SetoidObject@{t u} :=
  {| carrier   := poly_unit@{t}
   ; is_setoid := unit_setoid@{t u} |}.

Lemma injectivity_is_monic {X Y : SetoidObject} (f : X ~{Sets}~> Y) :
  (∀ x y : X, f x ≈ f y → x ≈ y) ↔ Monic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    apply HA, HB.
  - intros HA ?? HB.
    given (const_x : unit_setoid_object ~{ Sets }~> X). {
      construct.
      - apply x.
      - proper.
    }
    given (const_y : unit_setoid_object ~{ Sets }~> X). {
      construct.
      - apply y.
      - proper.
    }
    destruct HA.
    specialize (monic unit_setoid_object const_x const_y).
    unfold const_x in monic.
    unfold const_y in monic.
    simpl in *.
    eapply monic; eauto.
    constructor.
Qed.

Inductive Surjective@{o h op hp sh} {A B : SetoidObject@{o op}}
  (h : SetoidMorphism@{o h op hp} A B) (b : B) : Type@{o} :=
  | obv : Surjective
  | surj (a : A) : h a ≈ b → Surjective.

Lemma surjectivity_is_epic@{o h op hp so sh sp}
  {A B : SetoidObject@{o op}}
  (h : A ~{Sets@{o h op hp so sh sp}}~> B) :
  (∀ b : B, ∃ a : A, h a ≈ b)%type ↔ Epic@{sh sp} h.
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
  - (* This constructive proof was given by
       aws (https://mathoverflow.net/users/30790/aws)
       In the category of sets epimorphisms are surjective - Constructive Proof?
       URL (version: 2014-08-18): https://mathoverflow.net/q/178786 *)
    intros [epic] ?.
    given (C : SetoidObject@{o op}). {
      refine {|
        carrier := Type;
        is_setoid := {|
          equiv p q := p ↔ q
        |}
      |}.
      equivalence.
    }
(*
    given (f : B ~{Sets}~> C). {
      refine {|
        morphism := λ b, ∃ a, h a ≈ b
      |}.
    }
    given (g : B ~{Sets}~> C). {
      refine {|
        morphism := λ _, True
      |}.
    }
    specialize (epic C f g).
    enough ((f ∘[Sets] h) ≈ (g ∘[Sets] h)). {
      specialize (epic X b); clear X.
      unfold f, g in epic.
      simpl in *.
      now rewrite epic.
    }
    intro.
    unfold f, g; simpl.
*)
Abort.
