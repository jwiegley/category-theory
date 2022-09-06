Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.

Generalizable All Variables.

Section Applicative.

Context `{F : Coq ⟶ Coq}.

Reserved Notation "f <*> g" (at level 29, left associativity).

Class Applicative := {
  pure : ∀ {a : Type}, a → F a;
  ap   : ∀ {a b : Type}, F (a → b) → F a → F b
    where "F <*> g" := (ap F g);

  ap_id : ∀ a : Type, ap (pure (@id Coq a)) = id;
  ap_comp : ∀ (a b c : Type) (v : F (a → b)) (u : F (b → c)) (w : F a),
    pure (fun F g x => F (g x)) <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo : ∀ (a b : Type) (x : a) (F : a → b),
    pure F <*> pure x = pure (F x);
  ap_interchange : ∀ (a b : Type) (y : a) (u : F (a → b)),
    u <*> pure y = pure (fun F => F y) <*> u;

  ap_fmap : ∀ (a b : Type) (f : a → b),
    ap (pure f) = @fmap _ _ F _ _ f
}.

End Applicative.

Arguments pure {F _ _} _.
Arguments ap   {F _ _ _} _ x.

Coercion Applicative_Functor `{@Applicative F} : Coq ⟶ Coq := F.

Notation "pure[ F ]" := (@pure F _ _) (at level 19, F at next level).
Notation "pure[ F G ]" := (@pure (fun x => F (G x)) _ _) (at level 9).

Notation "ap[ F ]" := (@ap F _ _ _) (at level 9).
Notation "ap[ F G ]" := (@ap (fun x => F (G x)) _ _ _) (at level 9).

Infix "<*>" := ap (at level 29, left associativity).
Notation "x <**> F" := (ap F x) (at level 29, left associativity).
Notation "x <**[ F ]> f" := (@ap F _ _ _ f x) (at level 29, left associativity).
Infix "<*[ F ]>" :=
  (@ap F _ _ _) (at level 29, left associativity, only parsing).

Notation "[| F x y .. z |]" := (.. (F <$> x <*> y) .. <*> z)
    (at level 9, left associativity, F at level 9,
     x at level 9, y at level 9, z at level 9, only parsing).

Definition liftA2 `{Applicative} {A B C : Type}
  (f : A → B → C) (x : F A) (y : F B) : F C := ap (fmap[F] f x) y.

Infix "*>" := (liftA2 (const id)) (at level 29, left associativity).
Infix "<*" := (liftA2 const) (at level 29, left associativity).

Section CoqApplicative.

Context {F : Coq ⟶ Coq}.
Context {J : @Applicative F}.

(* Every Applicative endofunctor on Coq is a strong lax monoidal functor. *)

(* This definition has universe problems. *)
(* Program Definition Coq_Product_Monoidal : @Monoidal Coq := *)
(*   @Product_Monoidal Coq Coq_Cartesian Coq_Terminal. *)

(*
Program Definition Coq_Product_Monoidal : @Monoidal Coq := {|
  tensor :=
    {| fobj := fun x : Type =>
         {| fobj := fun y : Type => x * y
          ; fmap := fun _ _ f x => (fst x, f (snd x)) |}
     ; fmap := fun _ _ f =>
                 {| transform := _ |} |};
  I  := unit : Type
|}.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  proper.
  destruct x0.
  unfold Coq_Product_Monoidal_obligation_4.
  congruence.
Qed.
Next Obligation.
  isomorphism.
  - exact snd.
  - exact (fun x => (tt, x)).
  - reflexivity.
  - destruct x, u; reflexivity.
Qed.
Next Obligation.
  isomorphism.
  - exact fst.
  - exact (fun x => (x, tt)).
  - reflexivity.
  - destruct x, u; reflexivity.
Qed.
Next Obligation. isomorphism; simpl; intros; intuition. Qed.

Program Definition applicative_is_strong :
  @StrongFunctor Coq Coq_Product_Monoidal F := {|
  strength := fun _ _ x => fmap[F] (λ y, (fst x, y)) (snd x)
|}.
*)

(*
Program Definition Coq_Product_Monoidal_F : @Monoidal Coq := {|
  tensor :=
    {| fobj := fun x : Type =>
         {| fobj := fun y : Type => F x * F y
          ; fmap := fun _ _ f x => (fst x, fmap[F] f (snd x)) |}
     ; fmap := fun _ _ f =>
                 {| transform := _ |} |};
  I  := F (unit : Type)
|}.
Next Obligation.
  proper; simpl.
  f_equiv.
  pose proof (@fmap_respects _ _ F X0 y x y); simpl in X1.
  apply X1, H.
Qed.
Next Obligation.
  proper; simpl.
  f_equiv.
  pose proof (@fmap_id _ _ F X0); simpl in X1.
  apply X1.
Qed.
Next Obligation.
  proper; simpl.
  f_equiv.
  pose proof (@fmap_comp _ _ F x0 y z); simpl in X1.
  apply X1.
Qed.
Next Obligation.
  intuition.
  apply (fmap[F] f); assumption.
Qed.
*)

(* Definition applicative_is_lax : *)
(*   @LaxMonoidalFunctor Coq Coq Coq_Product_Monoidal Coq_Product_Monoidal_F F := {| *)
(*   pure := fun _ => @I Coq Coq_Product_Monoidal_F; *)
(*   ap_functor_nat := _ *)
(* |}. *)

(* Theorem applicative_is_strong_lax : *)
(*   StrongLaxMonoidalFunctor Coq Product_Monoidal F *)
(*                            applicative_is_strong applicative_is_lax. *)

End CoqApplicative.
