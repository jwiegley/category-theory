Require Export Functors.

Open Scope type_scope.

Generalizable All Variables.

Class Product `(C : Category)
  (P : C) `(p1 : P ~> A) `(p2 : P ~> B) :=
{ product_ump :
    forall (X : C) (x1 : X ~> A) (x2 : X ~> B),
       exists (u : X ~> P), x1 = p1 ∘ u /\ x2 = p2 ∘ u
    /\ forall (v : X ~> P), p1 ∘ v = x1 /\ p2 ∘ v = x2 -> v = u
}.

(* Tuples in the Arr category satisfy the UMP for products.
*)
Program Instance Tuple_Product {X Y : Set}
  : Product Arr (X * Y) (@fst X Y) (@snd X Y).
Obligation 1. (* product ump *)
  exists (fun x => (x1 x, x2 x)).
  intros. constructor.
    intros. unfold fst. reflexivity.
  split.
    intros. unfold snd. reflexivity.
  intros.
  inversion H.
  extensionality e.
  rewrite <- H0.
  rewrite <- H1.
  destruct (v e).
  reflexivity.
Defined.

Definition Tuple_map {Z X Y} (f : X → Y) (p : Z * X) : Z * Y :=
  match p with
  | pair z x => @pair Z Y z (f x)
  end.

Program Instance Tuple_Functor {Z} : Arr ⟶ Arr :=
{ fobj := fun X => Z * X
; fmap := @Tuple_map Z
}.
Obligation 1. extensionality e. crush. Defined.
Obligation 2. extensionality e. crush. Defined.

Definition Tuple_bimap {X Y W Z} (f : X → W) (g : Y → Z)
  (p : X * Y) : W * Z :=
  match p with
  | pair z x => @pair W Z (f z) (g x)
  end.
