(*
Definition Ctxt : list (Tuple nat Type).

Inductive Term (Γ : Ctxt) (a : Type) : Type :=
  | Var : (x : nat) -> Pair x a ∈ Γ -> Term Γ a

Global Instance Lamdba : Category Type (fun X Y => X -> Y) :=
{ id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
; eqv     := fun X Y f g => forall {x : X}, f x = g x
}.
Proof.
  (* The proofs of all of these follow trivially from their definitions. *)
  - (* eqv_equivalence *)  crush.
  - (* compose_respects *) crush.
  - (* right_identity *)   crush.
  - (* left_identity *)    crush.
  - (* comp_assoc *)       crush.
Defined.
*)