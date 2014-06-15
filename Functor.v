Definition id {X} (a : X) : X := a.

Theorem id_inj : forall {X} (x y : X),
  x = y -> id x = id y.
Proof.
  intros. apply H.  Qed.

Theorem id_inj_r : forall {X} (x y : X),
  id x = id y -> x = y.
Proof.
  intros. apply H.  Qed.

Definition compose {A B C} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Notation "f ∘ g" := (compose f g) (at level 75).

(* Even though we have the Category class in Category.v, the Functors
   and Monads I'm interested in reasoning about are all endofunctors on
   Coq, so there is no reason to carry around that extra machinery. *)

Class Functor (F : Type -> Type) :=
{ fmap : forall {X Y}, (X -> Y) -> F X -> F Y
; fun_identity : forall {X} (x : F X), fmap id x = id x
; fun_composition : forall {X Y Z} (x : F X) (f : Y -> Z) (g : X -> Y),
    (fmap f ∘ fmap g) x = fmap (f ∘ g) x
}.

Theorem fmap_fmap_id
  : forall {X} (F : Type -> Type) (f_dict : Functor F) (x : F (F X)),
  fmap (fmap id) x = x.
Proof.
  intros. assert (fmap (@id X) = @id (F X)).
    

Class Applicative (F : Type -> Type) :=
{ is_functor :> Functor F

; eta : forall {X}, X -> F X
; apply : forall {X Y}, F (X -> Y) -> F X -> F Y

; app_identity : forall {X} (v : F X), apply (eta id) v = v
; app_composition : forall {X Y Z} (v : F (X -> Y)) (u : F (Y -> Z)) (w : F X),
    apply (apply (apply (eta compose) u) v) w = apply u (apply v w)
; app_homomorphism : forall {X Y} (x : X) (f : X -> Y),
    apply (eta f) (eta x) = eta (f x)
; app_interchange : forall {X Y} (y : X) (u : F (X -> Y)),
    apply u (eta y) = apply (eta (fun f => f y)) u
}.

Notation "f <*> g" := (apply f g) (at level 70).

Class Monad (M : Type -> Type) :=
{ is_applicative :> Applicative M

; mu : forall {X}, M (M X) -> M X

; monad_law_1 : forall {X} (x : M (M (M X))), (mu ∘ fmap mu) x = (mu ∘ mu) x
; monad_law_2 : forall {X} (x : M X), (mu ∘ fmap eta) x = x
; monad_law_3 : forall {X} (x : M X), (mu ∘ eta) x = x
; monad_law_4 : forall {X Y} (x : X) (f : X -> Y), (eta ∘ f) x = (fmap f ∘ eta) x
; monad_law_5 : forall {X Y} (x : M (M X)) (f : X -> Y),
    (mu ∘ fmap (fmap f)) x = (fmap f ∘ mu) x
}.

Definition bind {M X Y} {m_dict : Monad M} (x : M X) (f : (X -> M Y)) : M Y :=
  mu (fmap f x).

Notation "m >>= f" := (bind m f) (at level 70).
