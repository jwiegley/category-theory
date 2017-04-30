Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ObjectEquivalence.

Context `{C : Category}.

(* Two objects in C are isomorphic, if there is an isomorphism between theme.
   Note that this definition has computational content, so we can make use of
   the morphisms. *)
Class ObjectEquivalence (X Y : C) : Type := {
  eqv_to   :> X ~> Y;
  eqv_from :  Y ~> X;

  eqv_transport_to   : X ~> Y -> Y ~> X;
  eqv_transport_from : Y ~> X -> X ~> Y;

  eqv_to_from : eqv_to ∘ eqv_transport_from eqv_from ≈ eqv_tf_iso;
  eqv_from_to : eqv_from ∘ eqv_to ≈ eqv_ft_iso
}.

Arguments eqv_to {X Y} _.
Arguments eqv_from {X Y} _.
Arguments eqv_to_from {X Y} _.
Arguments eqv_from_to {X Y} _.

Infix "∼" := ObjectEquivalence (at level 91) : category_scope.

Global Program Instance object_equivalence :
  Equivalence ObjectEquivalence.
Next Obligation.
  intros.
  eapply Build_ObjectEquivalence with
    (eqv_to:=id)
    (eqv_from:=id)
    (eqv_tf_iso:={| to:= id; from := id |})
    (eqv_ft_iso:={| to:= id; from := id |}); simpl.
  Unshelve. all:cat.
Qed.
Next Obligation.
  intros; destruct X.
  eapply Build_ObjectEquivalence with
    (eqv_to:=eqv_from0)
    (eqv_from:=eqv_to0)
    (eqv_tf_iso:=eqv_ft_iso0)
    (eqv_ft_iso:=eqv_tf_iso0);
  assumption.
Qed.
Next Obligation.
  intros; destruct X, X0.
  refine
    {| eqv_to     := eqv_to1 ∘ eqv_to0
     ; eqv_from   := eqv_from0 ∘ eqv_from1
     ; eqv_tf_iso := eqv_tf_iso1
     ; eqv_ft_iso := eqv_ft_iso0 |}.
    rewrite <- comp_assoc.
    rewrite (comp_assoc eqv_to0).
    rewrite eqv_to_from0; cat.
    destruct eqv_tf_iso0, eqv_tf_iso1; simpl in *.
  rewrite <- comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ from1).
  rewrite iso_from_to1; cat.
Defined.

Global Program Instance arrow_ObjectEquivalence :
  Proper
    (respectful ObjectEquivalence
       (respectful ObjectEquivalence Basics.arrow)) ObjectEquivalence.
Next Obligation.
  proper.
  transitivity x; auto.
    symmetry; assumption.
  transitivity x0; auto.
Defined.

Global Program Instance flip_arrow_ObjectEquivalence :
  Proper
    (respectful ObjectEquivalence
       (respectful ObjectEquivalence
                              (Basics.flip Basics.arrow))) ObjectEquivalence.
Next Obligation.
  proper.
  transitivity y; auto.
  transitivity y0; auto.
  symmetry; assumption.
Defined.

Definition ob_equiv : crelation C := fun X Y => X ≅ Y.

Global Program Instance ob_setoid : Setoid C.

Definition isomorphism_equiv {X Y : C} : crelation (X ≅ Y) :=
  fun f g => (to f ≈ to g) * (from f ≈ from g).

Global Program Instance isomorphism_equiv_equivalence {X Y : C} :
  Equivalence (@isomorphism_equiv X Y).
Next Obligation. firstorder. Defined.
Next Obligation. firstorder. Defined.

Global Program Instance isomorphism_setoid {X Y : C} : Setoid (X ≅ Y) := {
  equiv := isomorphism_equiv;
  setoid_equiv := isomorphism_equiv_equivalence
}.

End ObjectEquivalence.

Infix "≅" := (@ObjectEquivalence _) (at level 91) : category_scope.
Notation "F ≅[ C ] G" := (@ObjectEquivalence C F G)
  (at level 91, only parsing) : category_scope.

Arguments to {_ X Y} _.
Arguments from {_ X Y} _.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

Coercion to : ObjectEquivalence >-> hom.

Hint Unfold isomorphism_equiv.
