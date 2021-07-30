Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Theory.Unique.
Require Export Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section KanExtension.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.

Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ◯ F;
  fmap := fun _ _ f => {| transform := fun z => transform[f] (F z) |}
|}.
Next Obligation. apply naturality. Qed.
Next Obligation. apply naturality_sym. Qed.

Class RightKan := {
  (* jww (2017-06-09): Rename this to ran_functor, RightKan to Ran, and then a
     coercion from Ran to functor? *)
  Ran : [A, C] ⟶ [B, C];

  ran_adjoint : Induced ⊣ Ran
}.

Class LocalRightKan (X : A ⟶ C) := {
  LocalRan : B ⟶ C;

  ran_transform : LocalRan ◯ F ⟹ X;

  ump_ran (M : B ⟶ C) (μ : M ◯ F ⟹ X) :
    @Unique Fun _ _ (fun δ => μ ≈ ran_transform ∙ δ ⊲ F)
}.

(* Wikipedia: "There is also a local definition of 'the Kan extension of a
   given functor F along p' which can exist even if the entire functor defined
   above [global Kan extension] does not. This is a generalization of the fact
   that a particular diagram of shape C can have a limit even if not every
   such diagram does. It is also a special case of the fact discussed at
   adjoint functor that an adjoint functor can fail to exist completely, but
   may still be partially defined. If the local Kan extension of every single
   functor exists for some given p : C → C' and D, then these local Kan
   extensions fit together to define a functor which is the global Kan
   extension." *)

Global Program Instance RightKan_to_LocalRightKan {R : RightKan} (X : A ⟶ C) :
  LocalRightKan X := {|
  LocalRan := Ran X;
  ran_transform :=
    let adj_from := from (@adj _ _ _ _ ran_adjoint (Ran X) X) nat_id in
    {| transform  := transform[adj_from]
     ; naturality := naturality[adj_from] |}
|}.
Next Obligation.
  srewrite_r (naturality[from (@adj _ _ _ _ ran_adjoint (Ran X) X) nat_id]).
  reflexivity.
Qed.
Next Obligation.
  exists (to (@adj _ _ _ _ (@ran_adjoint R) M X) μ).
  - intros.
    spose (@from_adj_nat_l _ _ _ _ ran_adjoint) as X0.
    rewrite <- X0; clear X0.
    spose (@iso_from_to _ _ _ (@adj _ _ _ _ ran_adjoint M X) μ A0) as X0.
    unfold nat_compose; simpl in *.
    rewrites.
    sapply (proper_morphism (@from _ _ _ (@adj _ _ _ _ ran_adjoint M X))).
    simpl; intros; cat.
  - intros.
    assert (μ ≈ (adj[ran_adjoint])⁻¹ v). {
      intro.
      specialize (X0 A0).
      rewrite X0; clear X0.
      srewrite_r (@from_adj_nat_l _ _ _ _ ran_adjoint).
      destruct (adj[ran_adjoint]); simpl in *.
      destruct from; simpl in *.
      apply proper_morphism; simpl.
      now apply nat_id_left.
    }
    clear -X1.
    destruct (adj[ran_adjoint]); simpl in *.
    intros.
    rewrite <- (iso_to_from v).
    destruct to; simpl in *.
    apply proper_morphism.
    simpl.
    now apply X1.
Qed.

Class LeftKan := {
  Lan : [A, C] ⟶ [B, C];

  lan_adjoint : Lan ⊣ Induced
}.

Class LocalLeftKan (X : A ⟶ C) := {
  LocalLan : B ⟶ C;

  lan_transform : X ⟹ LocalLan ◯ F;

  ump_lan (M : B ⟶ C) (ε : X ⟹ M ◯ F) :
    @Unique Fun _ _  (fun δ => ε ≈ δ ⊲ F ∙ lan_transform)
}.

Global Program Instance LeftKan_to_LocalLeftKan {R : LeftKan} (X : A ⟶ C) :
  LocalLeftKan X := {|
  LocalLan := Lan X;
  lan_transform :=
    let adj_to := to (@adj _ _ _ _ lan_adjoint X (Lan X)) nat_id in
    {| transform  := transform[adj_to]
     ; naturality := naturality[adj_to] |}
|}.
Next Obligation.
  srewrite_r (naturality[to (@adj _ _ _ _ lan_adjoint X (Lan X)) nat_id]).
  reflexivity.
Qed.
Next Obligation.
  exists (from (@adj _ _ _ _ (@lan_adjoint R) X M) ε).
  - intros.
    spose (@to_adj_nat_r _ _ _ _ lan_adjoint) as X0.
    rewrite <- X0; clear X0.
    spose (@iso_to_from _ _ _ (@adj _ _ _ _ lan_adjoint X M) ε A0) as X0.
    unfold nat_compose; simpl in *.
    rewrites.
    sapply (proper_morphism (@to _ _ _ (@adj _ _ _ _ lan_adjoint X M))).
    simpl; intros; cat.
  - intros.
    assert (ε ≈ (to adj[lan_adjoint]) v). {
      intro.
      specialize (X0 A0).
      rewrite X0; clear X0.
      srewrite_r (@to_adj_nat_r _ _ _ _ lan_adjoint).
      destruct (to adj[lan_adjoint]); simpl in *.
      apply proper_morphism; simpl.
      now apply nat_id_right.
    }
    clear -X1.
    destruct (adj[lan_adjoint]); simpl in *.
    intros.
    rewrite <- (iso_from_to v).
    destruct from; simpl in *.
    apply proper_morphism.
    simpl.
    now apply X1.
Qed.

End KanExtension.

Arguments RightKan {_ _} F _.
Arguments Ran {_ _} F {_ _}.

Arguments LocalRightKan {_ _} F {_} _.
Arguments LocalRan {_ _} F {_} _ {_}.

Arguments LeftKan {_ _} F _.
Arguments Lan {_ _} F {_ _}.

Arguments LocalLeftKan {_ _} F {_} _.
Arguments LocalLan {_ _} F {_} _ {_}.

(* jww (2017-06-02): TODO *)
(* A functor F : C → D possesses a left adjoint if and only if the right Kan
   extension of Id : C → C along F exists and is preserved by F. In this case,
   a left adjoint is given by Ran F Id and this Kan extension is even
   preserved by any functor C → E whatsoever, i.e. is an absolute Kan
   extension. *)
