Axiom ext_eq : forall {T1 T2 : Type} (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.

Theorem ext_eqS : forall (T1 T2 : Type) (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.
  intros; rewrite (ext_eq f1 f2); auto.
Qed.

Ltac ext_eq := (apply ext_eq || apply ext_eqS); intro.

Definition id {X} (a : X) : X := a.

Theorem id_def : forall {X} (x : X) (f : X -> X),
  f = id -> f x = x.
Proof. intros. unfold id in H. rewrite H. reflexivity.  Qed.

Theorem id_inj : forall {X} (x y : X),
  x = y -> id x = id y.
Proof. intros. apply H.  Qed.

Theorem id_inj_r : forall {X} (x y : X),
  id x = id y -> x = y.
Proof. intros. apply H.  Qed.

Definition compose {A B C}
  (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Notation "f ∘ g" := (compose f g) (at level 65).

Theorem comp_assoc : forall {A B C D} (f : C -> D) (g : B -> C) (h : A -> B),
  f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof.
  intros. compute. reflexivity.
Qed.

Theorem comp_ident : forall {A B C} {x : A} {y : C} (f : B -> C) (g : A -> B),
  (f ∘ g) x = y -> f (g x) = y.
Proof.
  intros. compute. assumption.
Qed.

Theorem comp_ident2 : forall {A B C D} {x : A} {y : D}
  (f : C -> D) (g : B -> C) (h : A -> B),
  (f ∘ g) (h x) = y -> f (g (h x)) = y.
Proof.
  intros. compute. assumption.
Qed.

(* Even though we have the Category class in Category.v, the Functors
   and Monads I'm interested in reasoning about are all endofunctors on
   Coq, so there is no reason to carry around that extra machinery. *)

Class Functor (F : Type -> Type) :=
{ fmap : forall {X Y}, (X -> Y) -> F X -> F Y

; fun_identity : forall {X}, fmap (@id X) = id
; fun_composition : forall {X Y Z} (f : Y -> Z) (g : X -> Y),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.

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
; app_fmap_unit : forall {X Y} (f : X -> Y), apply (eta f) = fmap f
}.

Notation "f <*> g" := (apply f g) (at level 70).

Theorem fmap_unit_eq
  : forall (F : Type -> Type) (app_dict : Applicative F)
      (A B : Type) (f : A -> B) (x : A),
  fmap f (eta x) = eta (f x).
Proof.
  intros.
  symmetry.
  rewrite <- app_fmap_unit.
  rewrite -> app_interchange.
  rewrite -> app_homomorphism.
  reflexivity.
Qed.

Theorem app_fmap_id
  : forall (F : Type -> Type) (app_dict : Applicative F)
      (A B : Type) (f : A -> B) (x : F A),
   apply (eta id) x = fmap id x.
Proof.
  intros. rewrite app_fmap_unit. reflexivity.
Qed.

Class Monad (M : Type -> Type) :=
{ is_applicative :> Applicative M

; mu : forall {X}, M (M X) -> M X

; monad_law_1 : forall {X}, mu ∘ fmap mu = (@mu (M X)) ∘ mu
; monad_law_2 : forall {X}, mu ∘ fmap (@eta M is_applicative (M X)) = id
; monad_law_2_x : forall {X} (x : M (M X)), mu (fmap (@eta M is_applicative (M X)) x) = x
; monad_law_3 : forall {X}, (@ mu (M X)) ∘ eta = id
; monad_law_3_x : forall {X} {x : M X}, mu (eta x) = x
; monad_law_4 : forall {X Y} (f : X -> Y), eta ∘ f = fmap f ∘ eta
; monad_law_5 : forall {X Y} (f : X -> Y), mu ∘ fmap (fmap f) = fmap f ∘ mu
}.

Definition bind {M X Y} {m_dict : Monad M}
  (x : M X) (f : (X -> M Y)) : M Y := mu (fmap f x).

Notation "m >>= f" := (bind m f) (at level 70).
