Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Coq.Category.

Generalizable All Variables.

Class Functor (F : Coq → Coq) :=
  fmap : ∀ {x y : Coq} (f : x ~> y), F x ~> F y.

Class IsFunctor (F : Coq → Coq) `{Functor F} := {
  fmap_id {x} :
    fmap id[x] = id;
  fmap_comp {x y z} {f : y ~> z} {g : x ~> y} :
    fmap (f ∘ g) = fmap f ∘ fmap g
}.

Definition IsFunctor_Functor {F H} :
  @IsFunctor F H → Functor F := λ _, H.

Coercion IsFunctor_Functor : IsFunctor >-> Functor.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : morphism_scope.
Infix "<$[ M ]>" := (@fmap M _ _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <$ m" := (fmap (const x) m)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "fmap[ M ]" := (@fmap M _ _ _)
  (at level 9, format "fmap[ M ]") : morphism_scope.
Notation "fmap[ M N ]" := (@fmap (λ X, M (N X)) _ _ _)
  (at level 9, format "fmap[ M  N ]") : morphism_scope.
Notation "fmap[ M N O ]" := (@fmap (λ X, M (N (O X))) _ _ _)
  (at level 9, format "fmap[ M  N  O ]") : morphism_scope.

Ltac erew F :=
  let H := fresh "H" in unshelve epose proof F as H; eauto;
  cbn in H; unshelve erewrite H; eauto; clear H.
Ltac erew_r F :=
  let H := fresh "H" in unshelve epose proof F as H; eauto;
  cbn in H; unshelve erewrite <- H; eauto; clear H.

(* "Coq functors" are endofunctors on the category Coq. *)
Program Definition Coq_Functor `{IsFunctor F} : Coq ⟶ Coq := {|
  Theory.Functor.fobj := F;
  Theory.Functor.fmap := @fmap F _;
|}.
Next Obligation.
  now rewrite fmap_id.
Qed.
Next Obligation.
  now srewrite @fmap_comp.
Qed.

(* Coq endofunctors always compose to form another endofunctor. *)
#[global]
Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F ∘ G) := {
  fmap := λ _ _, fmap[F] ∘ fmap[G]
}.

Corollary compose_fmap  `{Functor F} `{Functor G} {x y} (f : x ~> y) :
  fmap[F ∘ G] f = fmap[F] (fmap[G] f).
Proof. reflexivity. Qed.

#[global]
Ltac functor_laws :=
  repeat match goal with
    | [ |- context[fmap[?F] (λ x, x)] ] =>
      rewrite fmap_id
    | [ |- context[fmap[?F] id] ] =>
      rewrite fmap_id
    | [ |- context[fmap[?F] (_ ∘ _)] ] =>
      rewrite fmap_comp
    | [ |- context[fmap[?F ∘ ?G] _] ] =>
      rewrite compose_fmap
    end.

#[local] Obligation Tactic := intros; functor_laws; intuition eauto; cat.

#[global]
Program Instance Compose_IsFunctor `{IsFunctor F} `{IsFunctor G} :
  IsFunctor (F ∘ G).
