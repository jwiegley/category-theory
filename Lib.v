Set Warnings "-notation-overridden".

Require Export
  Coq.Unicode.Utf8
  Coq.Init.Datatypes
  Coq.Setoids.Setoid
  Coq.Classes.CMorphisms
  Coq.Classes.CRelationClasses
  Coq.Classes.CEquivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Classes.Equivalence
  Coq.Classes.SetoidClass
  Coq.Logic.JMeq
  Coq.Program.Tactics
  Coq.Logic.ProofIrrelevance
  FunctionalExtensionality.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Close Scope nat_scope.
Delimit Scope category_scope with category.
Open Scope category_scope.

Infix "\o" := Basics.compose (at level 40, left associativity) : category_scope.

Infix "≈" := equiv (at level 79) : category_scope.
Infix "≋" := CEquivalence.equiv (at level 79) : category_scope.

Infix "<-->" := CRelationClasses.iffT (at level 100) : category_scope.

Notation "` x" := (@projT1 _ _ x) (at level 0) : category_scope.
Notation "( x ; y )" := (existT _ x y) (at level 0) : category_scope.

Tactic Notation "given" "(" ident(H) ":" lconstr(type) ")" :=
  refine (let H := (_ : type) in _).

Axiom propositional_extensionality : forall P : Prop, P -> P = True.

(* Proof irrelevant equality. *)
Definition proof_eq {P : Prop} (x y : P) := (x = y)%type.

Hint Unfold proof_eq.
Hint Unfold Basics.compose.
Hint Unfold Basics.arrow.
Hint Unfold Basics.impl.
Hint Unfold Datatypes.id.

Program Instance proof_eq_equivalence {P : Prop} : Equivalence (@proof_eq P).

Hint Constructors Equivalence.

Hint Unfold Reflexive.
Hint Unfold Symmetric.
Hint Unfold Transitive.

Hint Extern 1 (Proper _ _) => unfold Proper; auto.
Hint Extern 1 (Reflexive ?X) => unfold Reflexive; auto.
Hint Extern 1 (Symmetric ?X) => unfold Symmetric; intros; auto.
Hint Extern 1 (Transitive ?X) => unfold Transitive; intros; auto.
Hint Extern 1 (Equivalence ?X) => apply Build_Equivalence.
Hint Extern 8 (respectful _ _ _ _) => unfold respectful; auto.

Hint Extern 4 (?A ≈ ?A) => reflexivity : category_laws.
Hint Extern 6 (?X ≈ ?Y) => apply Equivalence_Symmetric : category_laws.
Hint Extern 7 (?X ≈ ?Z) =>
  match goal with
    [H : ?X ≈ ?Y, H' : ?Y ≈ ?Z |- ?X ≈ ?Z] => transitivity Y
  end : category_laws.

Ltac cat :=
  autorewrite with categories; auto with category_laws; try reflexivity.

Ltac equivalence := constructor; repeat intro; simpl; cat; intuition.
Ltac proper := repeat intro; simpl; cat; intuition.

Global Obligation Tactic :=
  program_simpl; autounfold;
  try solve [repeat match goal with
  | [ |- Proper _ _ ] => proper
  | [ |- respectful _ _ _ _ ] => proper
  | [ |- Equivalence _ ] => equivalence
  | _ => simpl; intros; cat; intuition
  end].
