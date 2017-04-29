Set Warnings "-notation-overridden".

Require Export Lib.Foundation.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ChoiceFacts.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Class CSetoid A := {
  cequiv : crelation A;
  setoid_cequiv :> CRelationClasses.Equivalence cequiv
}.

Arguments cequiv {A _} : simpl never.

Infix "≋" := cequiv (at level 79) : category_scope.

Program Instance csetoid_refl `(sa : CSetoid A) :
  CRelationClasses.Reflexive cequiv.
Obligation 1. apply setoid_cequiv. Defined.

Program Instance csetoid_sym `(sa : CSetoid A) :
  CRelationClasses.Symmetric cequiv.
Obligation 1. apply setoid_cequiv; auto. Defined.

Program Instance csetoid_trans `(sa : CSetoid A) :
  CRelationClasses.Transitive cequiv.
Obligation 1.
  apply setoid_cequiv.
  destruct sa; simpl in *.
  destruct setoid_cequiv0.
  eapply Equivalence_Transitive; eauto.
Defined.

Program Instance CSetoid_is_Setoid `(S : CSetoid A) : Setoid A := {
  equiv := fun x y => inhabited (@cequiv A S x y)
}.
Next Obligation.
  constructor; repeat intro.
  - apply inhabits.
    reflexivity.
  - destruct H.
    apply inhabits.
    symmetry; assumption.
  - destruct H, H0.
    apply inhabits.
    transitivity y; assumption.
Qed.

Arguments equiv {A _} : simpl never.

Delimit Scope csignature_scope with csignature.

Notation "f +++> g" := (CMorphisms.respectful f g)%csignature
  (right associativity, at level 55) : csignature_scope.
Notation "f ===> g" := (CMorphisms.respectful f g)%csignature
  (right associativity, at level 55) : csignature_scope.
Notation "f ---> g" := (CMorphisms.respectful (Basics.flip f) g)%csignature
  (right associativity, at level 55) : csignature_scope.

Arguments CMorphisms.Proper {A}%type R%csignature m.
Arguments CMorphisms.respectful {A B}%type (R R')%csignature _ _.

Program Instance cequiv_proper1 `{CSetoid A} `{CSetoid B} {f : A -> B}
        (P : CMorphisms.Proper (cequiv ===> cequiv) f) :
  Proper (equiv ==> equiv) f.
Next Obligation.
  repeat intro.
  destruct H, H0, H1.
  apply inhabits; auto.
Qed.

Program Instance cequiv_proper2 `{CSetoid A} `{CSetoid B} `{CSetoid C} {f : A -> B -> C}
        (P : CMorphisms.Proper (cequiv ===> cequiv ===> cequiv) f) :
  Proper (equiv ==> equiv ==> equiv) f.
Next Obligation.
  repeat intro.
  destruct H, H0, H1, H2, H3.
  apply inhabits; auto.
  apply P; auto.
Qed.

Lemma nonconstructive_cequiv (A : Type) `{CSetoid A} (x y : A) :
  x ≈ y -> inhabited (x ≋ y).
Proof.
  intros.
  destruct H0.
  apply inhabits.
  assumption.
Qed.

Lemma nonconstructive_cequiv_inv (A : Type) `{CSetoid A} (x y : A) :
  inhabited (x ≋ y) -> x ≈ y.
Proof.
  intros.
  destruct H0.
  apply inhabits.
  assumption.
Qed.

Lemma forall_inhabited {A} (P : A -> Type) :
  inhabited (∀ x, P x) -> ∀ x, inhabited (P x).
Proof.
  intros.
  destruct H.
  apply inhabits, X.
Qed.

Definition inhabited_forall' :=
  ∀ A (P : A -> Type), (∀ x, inhabited (P x)) -> inhabited (∀ x, P x).

(* These next two proofs were provided courtesy of Gaetan Gilbert. *)

Lemma choice_to_inhab : DependentFunctionalChoice -> inhabited_forall'.
Proof.
  intros choose.
  intros A P HP.
  assert (HP' : forall x, exists y : P x, True).
    intros x.
    destruct (HP x) as [Hx].
    exists Hx; trivial.
  pose proof (choose _ _ _ HP') as [f _].
  constructor; exact f.
Qed.

Lemma inhab_to_choice : inhabited_forall' -> DependentFunctionalChoice.
Proof.
  intros choose.
  apply non_dep_dep_functional_choice.
  intros A B R H.
  assert (H' : forall x, inhabited {y : B | R x y}).
    intros x.
    destruct (H x) as [y Hx].
    constructor; exists y; exact Hx.
  apply choose in H'.
  destruct H' as [f].
  exists (fun x => proj1_sig (f x)).
  intros x;apply proj2_sig.
Qed.

Lemma inhabited_forall : inhabited_forall'.
Proof.
  apply choice_to_inhab.
  apply non_dep_dep_functional_choice.
  repeat intro.
  apply choice, H.
Qed.

Tactic Notation "simplify" "equiv" :=
  unfold equiv; simpl;
  unfold cequiv; simpl;
  autounfold; simpl;
  try first
      [ apply nonconstructive_cequiv
      | apply inhabited_forall ].

Tactic Notation "simplify" "equiv" "in" ident(H) :=
  unfold equiv in H; simpl in H;
  unfold cequiv in H; simpl in H;
  autounfold in H; simpl in H.

Hint Constructors CRelationClasses.Equivalence.

Hint Unfold CRelationClasses.Reflexive.
Hint Unfold CRelationClasses.Symmetric.
Hint Unfold CRelationClasses.Transitive.

Hint Extern 1 (CRelationClasses.Reflexive ?X) =>
  unfold CRelationClasses.Reflexive; auto.
Hint Extern 1 (CRelationClasses.Symmetric ?X) =>
  unfold CRelationClasses.Symmetric; intros; auto.
Hint Extern 1 (CRelationClasses.Transitive ?X) =>
  unfold CRelationClasses.Transitive; intros; auto.
Hint Extern 1 (CRelationClasses.Equivalence ?X) =>
  apply CRelationClasses.Build_Equivalence.
Hint Extern 1 (CMorphisms.Proper _ _) => unfold CMorphisms.Proper; auto.
Hint Extern 8 (CMorphisms.respectful _ _ _ _) =>
  unfold CMorphisms.respectful; auto.

Hint Extern 4 (?A ≋ ?A) => reflexivity : category_laws.
Hint Extern 6 (?X ≋ ?Y) =>
  apply CRelationClasses.Equivalence_Symmetric : category_laws.
Hint Extern 7 (?X ≋ ?Z) =>
  match goal with
    [H : ?X ≋ ?Y, H' : ?Y ≋ ?Z |- ?X ≋ ?Z] => transitivity Y
  end : category_laws.
