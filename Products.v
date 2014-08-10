Require Export Hask.Category.
Require Export Hask.Functors.

Open Scope type_scope.

Generalizable All Variables.

Record Pullback {C : Category} {X Y} (Z : C) (f : X ~> Z) (g : Y ~> Z) :=
{ pullback_obj : C
; pullback_fst : pullback_obj ~> X
; pullback_snd : pullback_obj ~> Y
; pullback_ump_1 : f ∘ pullback_fst = g ∘ pullback_snd
; pullback_ump_2 : ∀ Q (q1 : Q ~> X) (q2 : Q ~> Y),
    {    u : Q ~> pullback_obj & pullback_snd ∘ u = q2 ∧ pullback_fst ∘ u = q1
    ∧ ∀ (v : Q ~> pullback_obj), pullback_snd ∘ v = q2 ∧ pullback_fst ∘ v = q1 → v = u }
}.

Class HasInitial {C : Category} :=
{ init_obj    : C
; init_mor    : ∀ {X}, init_obj ~> X
; initial_law : ∀ {X} (f g : init_obj ~> X), f = g
}.

Class HasTerminal {C : Category} :=
{ term_obj     : C
; term_mor     : ∀ {X}, X ~> term_obj
; terminal_law : ∀ {X} (f g : X ~> term_obj), f = g
}.

Definition Product {C : Category} `{@HasTerminal C} {X Y} :=
    @Pullback C X Y term_obj term_mor term_mor.

Lemma uniqueness_of_products (C : Category) `{h : @HasTerminal C}
  : ∀ {X Y} (p q : @Product C h X Y),
  let    ump1 := pullback_ump_2 q (fst p) (snd p)
  in let ump2 := pullback_ump_2 p (fst q) (snd q)
  in projT1 ump1 ∘ projT1 ump2 = id ∧ projT1 ump2 ∘ projT1 ump1 = id.
Proof.
  intros.
  split.
    destruct ump1.
    destruct ump2.
    simpl.
    destruct a.
    destruct H0.
    destruct a0.
    destruct H3.
Abort.

(*
(* Tuples in the Sets category satisfy the UMP for products.
*)
Program Instance Pair {X Y : Set}
  : Product Sets (X * Y) (@fst X Y) (@snd X Y).
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

Program Instance Tuple_Functor {Z} : Sets ⟶ Sets :=
{ fobj := fun X => Z * X
; fmap := @Tuple_map Z
}.
Obligation 1. extensionality e. crush. Defined.
Obligation 2. extensionality e. crush. Defined.
*)