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

Corollary let_fst {X Y} (A : X * Y) : (let (x, _) := A in x) = fst A.
Proof. reflexivity. Qed.

Corollary let_snd {X Y} (A : X * Y) : (let (_, y) := A in y) = snd A.
Proof. reflexivity. Qed.

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

(* Products can be compared for boolean equality if their members can be. *)
Definition prod_eqb {A B} (A_eqb : A -> A -> bool) (B_eqb : B -> B -> bool)
           (x y : A * B) : bool :=
  A_eqb (fst x) (fst y) && B_eqb (snd x) (snd y).

(* Products can be compared for decidable equality if their members can be. *)
Program Definition prod_eq_dec {A B}
        (A_eq_dec : forall x y : A, {x = y} + {x ≠ y})
        (B_eq_dec : forall x y : B, {x = y} + {x ≠ y})
        (x y : A * B) : {x = y} + {x ≠ y} :=
  match A_eq_dec (fst x) (fst y) with
  | in_left =>
    match B_eq_dec (snd x) (snd y) with
    | in_left  => in_left
    | in_right => in_right
    end
  | in_right => in_right
  end.
Next Obligation. congruence. Qed.
