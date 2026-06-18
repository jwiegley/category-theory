Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* Regression test for issue #139 ("CartesianMonoidal cleanup").

   Issue #139 observed that the library appeared to be missing the forward
   direction "every cartesian category is a monoidal category", and that the
   file Monoidal/Cartesian.v misleadingly held the *reverse* (Heunen-Vicary)
   result instead.  The forward direction in fact already existed, as
   CC_Monoidal in Monoidal/Internal/Product.v; it is now surfaced under the
   discoverable name Cartesian_Monoidal in Monoidal/Cartesian.v.

   These checks pin that down: the forward direction is available generically
   under its discoverable name, its tensor is the categorical product and its
   unit the terminal object, and it agrees definitionally with the monoidal
   structure that a concrete cartesian category (Coq) actually uses. *)

Section Issue139.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(* Theorem 1, generically: a cartesian category with a terminal object is
   monoidal.  Before #139 this construction had no discoverable name. *)
Definition issue_139_cartesian_is_monoidal : @Monoidal C := Cartesian_Monoidal.

(* The tensor of that monoidal structure is exactly the categorical product. *)
Example issue_139_tensor_is_product (x y : C) :
  (x ⨂[Cartesian_Monoidal] y)%object = (x × y)%object.
Proof. reflexivity. Qed.

(* ...and its unit is exactly the terminal object. *)
Example issue_139_unit_is_terminal :
  @I C Cartesian_Monoidal = 1%object.
Proof. reflexivity. Qed.

End Issue139.

(* End-to-end: the surfaced construction is definitionally the monoidal
   structure that the concrete cartesian category Coq already uses
   (Instance/Coq.v builds Coq_Monoidal from Coq_Cartesian + Coq_Terminal). *)
Example issue_139_coq_monoidal :
  Coq_Monoidal = @Cartesian_Monoidal Coq Coq_Cartesian Coq_Terminal.
Proof. reflexivity. Qed.
