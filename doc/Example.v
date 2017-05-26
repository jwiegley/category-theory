Inductive RoofObj : Type := RNeg | RZero | RPos.

Inductive RoofHom : RoofObj -> RoofObj -> Type :=
  | IdNeg   : RoofHom RNeg  RNeg
  | ZeroNeg : RoofHom RZero RNeg
  | IdZero  : RoofHom RZero RZero
  | ZeroPos : RoofHom RZero RPos
  | IdPos   : RoofHom RPos  RPos.

Definition caseRoofNegNeg (p : RoofHom RNeg RNeg) :
  forall (P : RoofHom RNeg RNeg -> Type)
         (PIdNeg : P IdNeg), P p :=
  match p with
  | IdNeg => fun _ P => P
  end.

Lemma RNeg_RNeg_id (f : RoofHom RNeg RNeg) : f = IdNeg.
Proof.
  pattern f.
  apply caseRoofNegNeg.
  reflexivity.
Qed.

Print Assumptions RNeg_RNeg_id.
(* Look ma, no axioms. *)

Lemma RNeg_RNeg_id' (f : RoofHom RNeg RNeg) : f = IdNeg.
Proof.
  Fail reflexivity.             (* expected *)
  Fail destruct f.              (* :( *)
  Require Import Coq.Program.Equality.
  dependent destruction f.
  reflexivity.
Qed.

Print Assumptions RNeg_RNeg_id'. (* :( *)

(*
Axioms:
JMeq_eq : forall (A : Type) (x y : A), x ~= y -> x = y
*)
