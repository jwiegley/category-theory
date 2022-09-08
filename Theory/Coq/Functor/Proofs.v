Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Strong.
Require Import Category.Instance.Coq.

Generalizable All Variables.

Definition EndoFunctor := @AFunctor Coq Coq.

(** Every lawful endofunctor on Coq is trivially an instance of
    [Category.Theory.Coq.Functor.Functor]. *)
Program Definition EndoFunctor_Functor `(H : EndoFunctor F) :
  Coq.Functor.Functor F := {|
  Coq.Functor.fmap := λ _ _ f, fmap[H] f;
|}.

Coercion EndoFunctor_Functor : EndoFunctor >-> Coq.Functor.Functor.

Definition IsFunctor `(Coq.Functor.Functor F) : Type := EndoFunctor F.

(* We can define this instance by appealing to the general [Id] functor. All
   that is required is for the object and function mappings to coincide. *)
Program Definition Identity_IsFunctor' : IsFunctor Identity_Functor :=
  ToAFunctor Id.

(* If [F] and [G] are both functors in Coq, we know that the composition is
   also a valid functor, and so we can map [Compose_Functor] directly to this
   composition. *)
Definition Compose_IsFunctor `{HF : EndoFunctor F} `{HG : EndoFunctor G} :
  IsFunctor (@Compose_Functor _ HF _ HG) :=
  ToAFunctor (Compose (FromAFunctor HF) (FromAFunctor HG)).

Program Definition prod_Functor {x} : IsFunctor (prod_Functor x) := {|
  a_fmap := prod_Functor x;
|}.
Next Obligation.
  proper.
  now rewrite H.
Qed.

Program Definition arrow_Functor {x} : IsFunctor (arrow_Functor x) := {|
  a_fmap := arrow_Functor x;
|}.
Next Obligation.
  proper.
  extensionality r.
  now rewrite H.
Qed.

(* jww (2022-09-07): TODO
Program Definition Maybe_Functor : IsFunctor Maybe_Functor := {|
  a_fmap := Maybe_Functor;
|}.
Next Obligation.
  proper.
  destruct x1; simpl; auto.
  now rewrite H.
Qed.
Next Obligation.
  now destruct x0.
Qed.
Next Obligation.
  now destruct x0.
Qed.
*)

Program Definition list_Functor : IsFunctor list_Functor := {|
  a_fmap := list_Functor;
|}.
Next Obligation.
  proper.
  induction x1; simpl; congruence.
Qed.
Next Obligation.
  induction x0; simpl; congruence.
Qed.
Next Obligation.
  induction x0; simpl; congruence.
Qed.
