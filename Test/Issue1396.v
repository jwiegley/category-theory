From Category Require Import Instance.Sets Theory.Coq.Monad.Proofs.

(* These names used to resolve separately, but taking the pair forced
   Basics.arrow.u0 both equal to and strictly below ID.u0. Use the actual
   constants rather than constructing another category or identity monad. *)
Check Category.Theory.Category.Build_Category'_Coq.
Check Category.Theory.Coq.Monad.Proofs.Identity_IsMonad.
Definition combined :=
  (Category.Theory.Category.Build_Category'_Coq,
   Category.Theory.Coq.Monad.Proofs.Identity_IsMonad).

Definition category_only := Category.Theory.Category.Build_Category'_Coq.
Definition monad_only := Category.Theory.Coq.Monad.Proofs.Identity_IsMonad.

From Category Require Import Lib Theory.Category.

Section FunctionData.
  Let C := Build_Category'_Coq.
  Context (A B D : obj[C]) (f : B -> D) (g : A -> B).

  Example hom_is_arrow : @hom C A B = (A -> B) := eq_refl.
  Example id_is_identity : @id C A = (fun x : A => x) := eq_refl.
  Example compose_is_composition : @compose C A B D f g = (fun x => f (g x)) := eq_refl.
  Example equiv_is_pointwise (g' : A -> B) :
    @equiv _ (@homset C A B) g g' = (forall x, g x = g' x) := eq_refl.
End FunctionData.
