Set Warnings "-notation-overridden".

Require Export Lib.Setoid.
Require Export Lib.Tactics.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The only inductive types from the standard library used in this development
   are products and sums, so we must show how they interact with constructive
   setoids. *)

Program Instance prod_setoid {A B} `{Setoid A} `{Setoid B} :
  Setoid (A * B) := {
  equiv := fun x y => equiv (fst x) (fst y) * equiv (snd x) (snd y)
}.

Program Instance pair_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv ==> equiv) (@pair A B).

Program Instance fst_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@fst A B).

Program Instance snd_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@snd A B).

Program Instance sum_setoid {A B} `{Setoid A} `{Setoid B} :
  Setoid (A + B) := {
  equiv := fun x y =>
    match x with
    | inl x =>
      match y with
      | inl y => equiv x y
      | inr y => False
      end
    | inr x =>
      match y with
      | inl y => False
      | inr y => equiv x y
      end
    end
}.
Next Obligation.
  equivalence; destruct x, y; try destruct z; intuition.
Qed.

Program Instance inl_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@inl A B).

Program Instance inr_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@inr A B).
