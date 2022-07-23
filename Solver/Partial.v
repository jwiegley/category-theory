Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Generalizable All Variables.

(** This code is from Certified Programming with Dependent Types (CPDT). *)

Inductive partial (P : Type) : Type :=
| Proved : P -> partial P
| Uncertain : partial P.

Notation "[ P ]" := (partial P) : type_scope.

Declare Scope partial_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

#[local] Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.
