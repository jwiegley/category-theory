Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Kleisli.

Context `{@Monad C M}.

#[local] Obligation Tactic := program_simpl.

Program Definition Kleisli : Category := {|
  obj     := C;
  hom     := fun x y => x ~> M y;
  homset  := fun x y => @homset C x (M y);
  id      := @ret C M _;
  compose := fun x y z f g => join ∘ fmap[M] f ∘ g
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. rewrite join_fmap_ret; cat. Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite <- fmap_ret; cat.
  rewrite comp_assoc.
  rewrite join_ret; cat.
Qed.
Next Obligation.
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc join (fmap (fmap _))).
  rewrite join_fmap_fmap; cat.
Qed.
Next Obligation.
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc join (fmap (fmap _))).
  rewrite join_fmap_fmap; cat.
Qed.

Definition kleisli_compose `(f : b ~> M c) `(g : a ~> M b) :
  a ~> M c := @compose Kleisli _ _ _ f g.

Notation "f <=< g" :=
  (kleisli_compose f g) (at level 40, left associativity) : morphism_scope.
Notation "f >=> g" :=
  (kleisli_compose g f) (at level 40, left associativity) : morphism_scope.

(* We can now re-express the monad laws in terms of this category, making the
   monoid relationship clearer. *)

Corollary monad_id_left `(f : x ~{C}~> M y) : ret <=< f ≈ f.
Proof. unfold kleisli_compose; cat. Qed.

Corollary monad_id_right `(f : x ~> M y) : f <=< ret ≈ f.
Proof. unfold kleisli_compose; cat. Qed.

Corollary monad_comp_assoc `(f : z ~> M w) `(g : y ~> M z) `(h : x ~> M y) :
  f <=< (g <=< h) ≈ (f <=< g) <=< h.
Proof. unfold kleisli_compose; cat. Qed.

End Kleisli.

Notation "f <=< g" :=
  (@compose Kleisli _ _ _ f g) (at level 40, left associativity) : morphism_scope.
Notation "f >=> g" :=
  (@compose Kleisli _ _ _ g f) (at level 40, left associativity) : morphism_scope.

Notation "f >=[ M ]=> g" := (@kleisli_compose _ M _ _ _ f _ g)
  (at level 40, left associativity) : morphism_scope.
Notation "f <=[ M ]=< g" := (@kleisli_compose _ M _ _ _ g _ f)
  (at level 40, left associativity) : morphism_scope.
