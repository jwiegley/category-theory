Require Export Category.Lib.Foundation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv : Equivalence equiv
}.
#[export] Existing Instance setoid_equiv.

Coercion setoid_equiv : Setoid >-> Equivalence.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

Delimit Scope signature_scope with signature.

Notation "f ++> g" := (respectful f g)%signature
  (right associativity, at level 55) : signature_scope.
Notation "f ==> g" := (respectful f g)%signature
  (right associativity, at level 55) : signature_scope.
Notation "f --> g" := (respectful (Basics.flip f) g)%signature
  (right associativity, at level 55) : signature_scope.

Arguments Proper {A}%type R%signature m.
Arguments respectful {A B}%type (R R')%signature _ _.

Definition eq_equivalence@{t u} {A : Type@{t}} : @Equivalence@{t u} A (@eq A) :=
  @Build_Equivalence@{t u} A
    (@eq A) (@eq_Reflexive A)
    (@eq_Symmetric A)
    (@eq_Transitive A).

Inductive poly_unit@{u} : Type@{u} := ttt.

Definition unit_setoid@{t u} : Setoid@{t u} poly_unit@{t} :=
  {| equiv := @eq poly_unit@{t}
   ; setoid_equiv := @eq_equivalence@{t u} poly_unit@{t} |}.

Definition eq_Setoid@{u} (A : Type@{u}) : Setoid@{u u} A :=
  Build_Setoid@{u _} A (λ f g, eq f g) eq_equivalence@{u u}.

#[export]
Program Instance funext_Setoid
        {T : Type} (t : T → Type) (a b : T) `{Setoid (t b)} :
  Setoid (t a → t b) | 9 := {|
  equiv := λ f g, ∀ x, f x ≈ g x
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    now apply X.
  - now rewrite X, X0.
Qed.

#[export]
Program Instance Fin_Setoid {n} : Setoid (Fin.t n) := {|
  equiv := eq
|}.

Class Unique `{S : Setoid A} (P : A → Type) := {
  unique_obj : A;
  unique_property : P unique_obj;
  uniqueness      : ∀ v : A, P v → unique_obj ≈ v;
}.

Arguments unique_obj {_ _ _} _.
Arguments unique_property {_ _ _} _.
Arguments uniqueness {_ _ _} _.

Notation "∃! x .. y , P" := (Unique (fun x => .. (Unique (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : category_theory_scope.
