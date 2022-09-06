Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Functor.Applicative.
Require Import Category.Theory.Coq.Category.
Require Import Category.Theory.Coq.Functor.

Generalizable All Variables.

Reserved Notation "f <*> g" (at level 29, left associativity).

Class Applicative (F : Coq → Coq) `{Functor F} := {
  pure {a} : a ~> F a;
  ap {a b} : F (a ~> b) → F a ~> F b
    where "f <*> g" := (ap f g)
}.

Notation "pure[ M ]" := (@pure M _ _)
  (at level 9, format "pure[ M ]") : morphism_scope.
Notation "pure[ M N ]" := (@pure (fun X => M (N X)) _ _)
  (at level 9, format "pure[ M  N ]") : morphism_scope.

Notation "ap[ M ]" := (@ap M _ _ _)
  (at level 9, format "ap[ M ]") : morphism_scope.
Notation "ap[ M N ]" := (@ap (fun X => M (N X)) _ _ _)
  (at level 9, format "ap[ M  N ]") : morphism_scope.
Notation "ap[ M N O ]" := (@ap (fun X => M (N (O X))) _ _ _)
  (at level 9, format "ap[ M  N  O ]") : morphism_scope.

Infix "<*>" := ap (at level 29, left associativity) : morphism_scope.
Infix "<*[ M ]>" := (@ap M _ _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "x <**> f" := (ap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <**[ M ]> f" := (@ap M _ _ _ f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Definition liftA2 `{Applicative F} `(f : a → b → c) (x : F a) (y : F b) : F c :=
  ap (fmap f x) y.

Infix "*>" := (liftA2 (const id))
  (at level 29, left associativity) : morphism_scope.
Infix "<*" := (liftA2 const)
  (at level 29, left associativity) : morphism_scope.

Class IsApplicative (F : Coq → Coq) `{@Applicative F H} `{@IsFunctor F H} := {
  ap_id {a} :
    ap (pure id[a]) = id;
  ap_assoc {a b c} {v : F (a ~> b)} {u : F (b ~> c)} {w : F a} :
    pure compose <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo {a b} {f : a ~> b} :
    ap (pure f) ∘ pure = pure ∘ f;
  ap_interchange {a b} {y : a} {u : F (a ~> b)} :
    u <*> pure y = pure ($ y) <*> u;
  ap_fmap {a b} :
    ap ∘ pure = fmap (x:=a) (y:=b)
}.

Definition IsApplicative_Applicative `{@IsApplicative F H A IS} :
  Applicative F := A.

Coercion IsApplicative_Applicative : IsApplicative >-> Applicative.

Definition IsApplicative_IsFunctor `{@IsApplicative F H A IS} :
  IsFunctor F := IS.

Coercion IsApplicative_IsFunctor : IsApplicative >-> IsFunctor.

Corollary ap_comp `{Applicative F} `{f : a ~> F (b ~> c)} {x} :
  (ap[F] ∘ f) x = ap (f x).
Proof. reflexivity. Qed.

Corollary pure_comp `{Applicative F} `{f : a ~> b} {x} :
  (pure[F] ∘ f) x = pure (f x).
Proof. reflexivity. Qed.

Corollary ap_homo_x `{IsApplicative F} {a b} {f : a ~> b} {x} :
  pure f <*> pure x = pure (f x).
Proof.
  pose proof (@ap_homo F _ _ _ _ _ _ f).
  cbv in H3.
  eapply equal_f in H3; eauto.
Qed.

Lemma fmap_pure `{IsApplicative F} {a b} (f : a → b) :
  fmap f ∘ pure = pure ∘ f.
Proof.
  rewrite <- ap_fmap.
  apply ap_homo.
Qed.

Lemma fmap_pure_x `{IsApplicative F} {a b} (f : a → b) {x} :
  fmap f (pure x) = pure (f x).
Proof.
  rewrite <- ap_fmap.
  cbv.
  apply ap_homo_x.
Qed.

#[export]
Instance Compose_Applicative `{Applicative F} `{Applicative G} :
  Applicative (F ∘ G)  := {
  pure := λ _, pure[F] ∘ pure;
  ap   := λ _ _, ap[F] ∘ fmap ap
}.

Corollary compose_ap  `{Applicative F} `{Applicative G} {x y} :
  ap[F ∘ G] = ap[F] ∘ fmap[F] (@ap G _ _ x y).
Proof. reflexivity. Qed.

Ltac erew F :=
  let H := fresh "H" in unshelve epose proof F as H; eauto;
  cbn in H; unshelve erewrite H; eauto; clear H.
Ltac erew_r F :=
  let H := fresh "H" in unshelve epose proof F as H; eauto;
  cbn in H; unshelve erewrite <- H; eauto; clear H.

Ltac applicative_laws :=
  repeat (match goal with
    | [ |- context[(ap[?F] ∘ _) _] ] =>
      rewrite ap_comp || erew @ap_comp
    | [ |- context[(pure[?F] ∘ _) _] ] =>
      rewrite pure_comp || erew @pure_comp
    | [ |- context[fmap[?F] _ (pure[?F] _)] ] =>
      rewrite fmap_pure_x || erew @fmap_pure_x
    | [ |- context[fmap[?F] _ ∘ pure[?F]] ] =>
      rewrite fmap_pure || erew @fmap_pure
    | [ |- context[ap[?F] (pure[?F] id)] ] =>
      rewrite ap_id || erew @ap_id
    | [ |- context[ap[?F] (pure[?F] _)] ] =>
      rewrite ap_fmap || erew @ap_fmap
    | [ |- context[pure[?F] _ <*> pure[?F] _] ] =>
      rewrite ap_homo_x || erew @ap_homo_x
    | [ |- context[ap (pure[?F] _) ∘ pure[?F]] ] =>
      rewrite ap_homo || erew @ap_homo
    | [ |- context[_ <*> pure[?F] _] ] =>
      rewrite ap_interchange || erew @ap_interchange
    | [ |- context[ap[?F ∘ ?G] _] ] =>
      rewrite compose_ap || erew @compose_ap
    end; functor_laws; try f_equal).

#[local]
Obligation Tactic := program_simpl; applicative_laws; intuition eauto; cat.

(*
#[export]
Program Instance Compose_IsApplicative `{IsApplicative F} `{IsApplicative G} :
  IsApplicative (F ∘ G) := {
  ap_id          := _;
  ap_assoc       := _;
  ap_homo        := _;
  ap_interchange := _;
  ap_fmap        := _;
}.
Next Obligation. Admitted.
Next Obligation.
  spose (@comp_assoc Coq) as X; rewrite X.
  spose (@ap_homo F _ _ _ _ _ _ (ap[_] (pure[_] f))) as Y.
  setoid_rewrite Y.
  spose (@comp_assoc Coq) as Z; rewrite <- Z.
  rewrite ap_homo; cat.
Next Obligation.
  (* Discharge w *)
  rewrite <- ap_assoc.
  f_equal.
  clear w.
  (* Discharge v *)
  rewrite <- !ap_fmap.
  rewrite <- ap_assoc.
  symmetry.
  rewrite <- ap_assoc.
  f_equal.
  clear v.
  (* Discharge u *)
  applicative_laws.
  clear u.
  (* Trivial rewriting *)
  extensionality x.
  extensionality y.
  extensionality z.
  simpl.
  rewrite <- ap_assoc.
  applicative_laws.
Qed.
Next Obligation.
  extensionality x.
  applicative_laws.
Qed.
*)
