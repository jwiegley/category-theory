Require Export Hask.Functors.

(* Maybe indicates optional values. *)

Set Universe Polymorphism.
Section Maybe.

Inductive Maybe {A : Type} : Type :=
  | Nothing : @Maybe A
  | Just    : A -> @Maybe A.

Program Instance Maybe_Functor : Arr ⟶ Arr :=
{ fmap := fun _ _ f x => match x with
   | Nothing => Nothing
   | Just x' => Just (f x')
  end
}.
Obligation 1. simple_solver. Defined.
Obligation 2. simple_solver. Defined.

End Maybe. (* jww (2014-08-06): Hiding instance for now *)

(* Either is the canonical coproduct type in Arr. *)

Inductive Either {E X : Type} :=
  | Left  : E → @Either E X
  | Right : X → @Either E X.

Program Instance Either_Bifunctor : Arr ⟶ Arr ⟹ Arr :=
{ fobj := fun Z =>
  {| fobj := @Either Z
   ; fmap := fun _ _ f e => match e with
      | Left x  => Left x
      | Right x => Right (f x)
      end
   |}
; fmap := fun _ _ f =>
  {| transport := fun _ e => match e with
      | Left x  => Left (f x)
      | Right x => Right x
      end
   |}
}.
Obligation 1. extensionality e. crush. Defined.
Obligation 2. extensionality e. crush. Defined.
Obligation 3. extensionality e. crush. Defined.
Obligation 4.
  apply nat_irrelevance.
  extensionality e.
  extensionality f. crush.
Defined.
Obligation 5.
  apply nat_irrelevance.
  extensionality e.
  unfold compose. simpl.
  eapply functional_extensionality. crush.
Defined.

(* jww (2014-08-07): TODO: Apparently I've lost the connection between values
   and typeclass instances for objects in Arr, owing to recently added towers
   of abstraction. *)

Example either_fmap_ex1 :
  let fmap' f := @fmap _ _ Either_Bifunctor _ _ f _ in
  ∀ n : nat, fmap' S (Left n)  = Left (S n)
           ∧ fmap' S (Right n) = @Right nat nat n.
Proof. split; reflexivity. Qed.

Example either_fmap1_ex1 :
  let fmap1' f := @fmap1 _ _ _ Either_Bifunctor _ _ _ f in
  ∀ n : nat, fmap1' S (Left n)  = Left n
           ∧ fmap1' S (Right n) = @Right nat nat (S n).
Proof. split; reflexivity. Qed.

Example either_bimap_ex1 :
  let bimap' f g := @bimap _ _ _ Either_Bifunctor _ _ f _ _ g in
  ∀ n, bimap' S pred (Left n) = Left (S n).
Proof. reflexivity. Qed.

Example either_bimap_ex2 :
  let bimap' f g := @bimap _ _ _ Either_Bifunctor _ _ f _ _ g in
  ∀ n, bimap' S pred (Right n) = Right (pred n).
Proof. reflexivity. Qed.
