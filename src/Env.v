Set Warnings "-notation-overridden".

Require Export Coq.FSets.FMapPositive.

Module Export MP := FMapPositive.
Module M := MP.PositiveMap.

Require Export Solver.Lib.

Unset Equations WithK.

Require Export Category.Theory.Category.
Require Export Category.Theory.EndoFunctor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Monad.Kleisli.
Require Import Category.Instance.Coq.

Generalizable All Variables.

Definition obj_idx : Type := positive.
Definition arr_idx : Type := positive.

Class Env := {
  cat : Category;
  objs : obj_idx -> cat;
  arrmap : M.t (∃ x y, objs x ~{cat}~> objs y);
  arrs (a : arr_idx) : option (∃ x y, objs x ~{cat}~> objs y) :=
    M.find a arrmap
}.

(* jww (2018-03-10): Why doesn't this work? *)
(* Instance obj_idx_Equality : Equality obj_idx := Pos_Eq. *)

Instance obj_idx_Equality : Equality obj_idx := {
  Eq_eqb         := Pos.eqb;
  Eq_eqb_refl    := Pos_eqb_refl;

  Eq_eqb_eq x y  := proj1 (Pos.eqb_eq x y);

  Eq_eq_dec      := Pos.eq_dec;
  Eq_eq_dec_refl := Pos_eq_dec_refl
}.

Instance arr_idx_Setoid : Setoid arr_idx := {
  equiv := Eq_eq;
  setoid_equiv := eq_equivalence
}.

Import EqNotations.

Section Env.

Context `{Env}.

Definition option_ex_equiv {dom}
           (x y : option (∃ cod : obj_idx, objs dom ~{ cat }~> objs cod)) :=
  match x, y with
  | Some (cf; f), Some (cg; g) =>
    match eq_dec cf cg with
    | Specif.left H => f ≈ rew <- [fun x => _ ~> objs x] H in g
    | _ => False
    end
  | None, None => True
  | _, _ => False
  end.

Instance option_ex_equivalence {dom} : Equivalence (@option_ex_equiv dom).
Proof.
  unfold option_ex_equiv.
  equivalence.
  - destruct x; cat.
    now rewrite eq_dec_refl.
  - destruct x, y; cat; desh.
    now rewrite eq_dec_refl.
  - destruct x, y, z; cat; repeat desh.
      now transitivity e0.
    contradiction.
Qed.

Global Program Instance option_ex_Setoid {dom} :
  Setoid (option (∃ cod : obj_idx, objs dom ~{ cat }~> objs cod)) := {
  equiv := option_ex_equiv
}.

(** option over type-aligned structures forms a monad. *)

Definition option_compose {C : Category} {dom mid cod}
           (f : option (@hom C mid cod))
           (g : option (@hom C dom mid)) : option (@hom C dom cod) :=
  match f, g with
  | Some f, Some g => Some (f ∘ g)
  | _, _ => None
  end.

Global Program Instance optionM : @Monad Coq optionF := {
  ret := @Some;
  join := fun _ x =>
    match x with
    | Some (Some x) => Some x
    | _ => None
    end
}.
Next Obligation.
  destruct x0; simpl; auto.
  destruct o; auto.
  destruct o; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
Qed.
Next Obligation.
  destruct x0; simpl; auto.
  destruct o; auto.
Qed.

Global Program Instance optional_compose_Proper
       {C : Category} {dom mid cod} :
  Proper (equiv ==> equiv ==> equiv) (@option_compose C dom mid cod).
Next Obligation.
  repeat intro.
  destruct x, x0, y, y0; simpl; auto.
  now rewrite X, X0.
Qed.

End Env.

Import EqNotations.

(** Every monoid defines a category where composition is mappend.

    jww (2018-03-10): This is only specialized to lists for now. *)

Program Definition list_cat A B `{H : Setoid B} : Category := {|
  obj := A;
  hom := fun _ _ => list B;
  homset := fun x y => {| equiv := @list_equiv B H |};
  id := fun _ => [];
  compose := fun _ _ _ f g => f ++ g;
  id_left := fun _ _ => reflexivity (R:=list_equiv);
  id_right := fun _ _ l =>
    rew <- [fun l => list_equiv l _] (app_nil_r l)
      in reflexivity (R:=list_equiv) l;
  comp_assoc := fun _ _ _ _ x y z =>
    rew [fun l => list_equiv _ l] (app_assoc x y z)
      in reflexivity (R:=list_equiv) (x ++ y ++ z);
  comp_assoc_sym := fun _ _ _ _ x y z =>
    rew [fun l => list_equiv l _] (app_assoc x y z)
      in reflexivity (R:=list_equiv) (x ++ y ++ z)
|}.
