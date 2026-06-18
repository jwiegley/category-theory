Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.

Generalizable All Variables.

(** The fold (codiagonal) functor [Id, Id] : C ∐ C ⟶ C. *)

(* nLab: https://ncatlab.org/nlab/show/codiagonal
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   This is the copairing of the identity functor with itself, the functor out
   of the coproduct category C ∐ C (defined in Construction/Coproduct.v) that
   collapses both summands back onto C. On objects it sends both inl x and
   inr x to x (sum_obj); on morphisms it is the identity on each summand's
   hom-set, the cross-summand homs being empty (False) and so eliminated by [!].
   It is the unique functor [Id, Id] : C ∐ C ⟶ C with [Id, Id] ∘ inl = Id and
   [Id, Id] ∘ inr = Id, furnished by the universal property of the coproduct in
   Cat (a functor C ∐ C ⟶ E is the same as a pair of functors C ⟶ E and
   C ⟶ E). It is the Cat-level analogue, and dual, of the binary diagonal
   Δ : C ⟶ C ∏ C of Functor/Diagonal.v.

   Note this is the codiagonal *functor* out of the coproduct *category*, which
   needs nothing of C; it should not be confused with the codiagonal *morphism*
   ∇ : x + x ~> x inside a cocartesian category (merge id id, the copairing
   id ▽ id of Structure/Cocartesian.v). Accordingly the [@Cocartesian C]
   hypothesis below is not used by the construction and is retained only to
   record the intended cocartesian setting; the functor is well defined for any
   category C. *)

Section Coproduct.

Context {C : Category}.
Context `{@Cocartesian C}.

(* Object action: both inl x and inr x are sent to x. [const C] is the (non-
   dependent) motive of [sum_rect]; both branches are the identity on objects. *)
Definition sum_obj : C ∐ C → C :=
  sum_rect (const C) Datatypes.id Datatypes.id.

Section sum_map.

#[local] Set Transparent Obligations.

(* Morphism action: identity on each summand's hom-set (the [_] branches solve
   x ~> y from f : x ~> y in C); the off-diagonal homs are False, so [!] derives
   the goal from the impossible hypothesis. *)
Program Definition sum_map (a : C ∐ C) (b : C ∐ C) (f : a ~> b) :
  sum_obj a ~> sum_obj b :=
  match a, b with
  | Datatypes.inl x, Datatypes.inl y => _
  | Datatypes.inl _, Datatypes.inr _ => !
  | Datatypes.inr x, Datatypes.inl _ => !
  | Datatypes.inr x, Datatypes.inr y => _
  end.

End sum_map.

#[export]
Program Instance CoproductFunctor : C ∐ C ⟶ C := {
  fobj := sum_obj;    (* inl x, inr x ↦ x *)
  fmap := sum_map;    (* identity on each summand's morphisms *)
}.
Next Obligation.
  proper; destruct x, y; simpl; tauto.
Qed.
Next Obligation.
  destruct x; simpl; reflexivity.
Qed.
Next Obligation.
  destruct x, y, z; simpl; cat; tauto.
Qed.

End Coproduct.
