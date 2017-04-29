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
  Coq.Logic.ProofIrrelevance
  FunctionalExtensionality
  Coq.Program.Program.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Close Scope nat_scope.
Delimit Scope category_scope with category.
Open Scope category_scope.

Infix "\o" := Basics.compose (at level 40, left associativity) : category_scope.

Infix "<-->" := CRelationClasses.iffT (at level 100) : category_scope.

Notation "`` x" := (@projT1 _ _ x) (at level 0) : category_scope.
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

Arguments Basics.compose {_ _ _} _ _ /.
Arguments Basics.arrow _ _ /.
Arguments Basics.impl _ _ /.
Arguments Datatypes.id {_} _ /.

Program Instance proof_eq_equivalence {P : Prop} : Equivalence (@proof_eq P).

Hint Constructors Equivalence.

Hint Unfold Reflexive.
Hint Unfold Symmetric.
Hint Unfold Transitive.

Hint Extern 1 (Reflexive ?X) => unfold Reflexive; auto.
Hint Extern 1 (Symmetric ?X) => unfold Symmetric; intros; auto.
Hint Extern 1 (Transitive ?X) => unfold Transitive; intros; auto.
Hint Extern 1 (Equivalence ?X) => apply Build_Equivalence.
Hint Extern 1 (Proper _ _) => unfold Proper; auto.
Hint Extern 8 (respectful _ _ _ _) => unfold respectful; auto.

(* Hint Extern 4 (?A ≈ ?A) => reflexivity : category_laws. *)
(* Hint Extern 6 (?X ≈ ?Y) => apply Equivalence_Symmetric : category_laws. *)
(* Hint Extern 7 (?X ≈ ?Z) => *)
(*   match goal with *)
(*     [H : ?X ≈ ?Y, H' : ?Y ≈ ?Z |- ?X ≈ ?Z] => transitivity Y *)
(*   end : category_laws. *)

Ltac cat :=
  try split;
  autorewrite with categories;
  auto with category_laws;
  try reflexivity.

Ltac equivalence := constructor; repeat intro; simpl; cat; intuition.
Ltac proper := repeat intro; simpl; cat; intuition.

Global Obligation Tactic :=
  program_simpl; autounfold;
  try solve [
    repeat match goal with
    | [ |- Equivalence _ ] => equivalence
    | [ |- CRelationClasses.Equivalence _ ] => equivalence
    | [ |- Proper _ _ ] => proper
    | [ |- respectful _ _ _ _ ] => proper
    | [ |- CMorphisms.Proper _ _ ] => proper
    | [ |- CMorphisms.respectful _ _ _ _ ] => proper
    | _ => simpl; intros; cat; intuition
    end].
