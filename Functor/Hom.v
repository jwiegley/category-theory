Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* Bifunctors can be curried:

  C × D ⟶ E --> C ⟶ [D, E] ~~~ (C, D) → E --> C → D → E

  Where ~~~ should be read as "Morally equivalent to".

  Note: We do not need to define Bifunctors as a separate class, since they
  can be derived from functors mapping to a category of functors. So in the
  following two definitions, [P] is effectively our bifunctor.

  The trick to [bimap] is that both the [Functor] instances we need (for
  [fmap] and [fmap1]), and the [Natural] instance, can be found in the
  category of functors we're mapping to by applying [P]. *)

Program Definition Hom `(C : Category) : C^op ∏ C ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom C (fst p) (snd p)
                    ; is_setoid := @homset (C) (fst p) (snd p) |};
  fmap := fun x y (f : x ~{C^op ∏ C}~> y) =>
            {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.
Next Obligation. now rewrite !comp_assoc. Qed.

Program Definition Curried_Hom `(C : Category) : C^op ⟶ [C, Sets] := {|
  fobj := fun x => {|
    fobj := fun y => {| carrier := @hom C x y
                      ; is_setoid := @homset C x y |};
    fmap := fun y z (f : y ~{C}~> z) =>
              {| morphism := fun (g : x ~{C}~> y) =>
                               (f ∘ g) : x ~{C}~> z |}
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ op f |}
  |}
|}.
Next Obligation.
  simpl; intros.
  unfold op.
  apply comp_assoc.
Qed.

Coercion Curried_Hom : Category >-> Functor.

Notation "[Hom A , ─]" := (@Curried_Hom _ A) : functor_scope.

#[export] Instance Yoneda_Faithful (C : Category) : Faithful (Curried_Hom C).
Proof.
  constructor.
  intros c c' f g same_nat_iso.
  simpl in same_nat_iso.
  specialize same_nat_iso with c id. now rewrite 2 id_left in same_nat_iso.
Qed.

#[export] Instance Yoneda_Full (C : Category) : Full (Curried_Hom C).
Proof.
  unshelve econstructor; simpl in *.
  - exact (fun c d f => f c id).
  - abstract(auto).
  - abstract(intros c; simpl; now autorewrite with categories).
  - abstract(intros; destruct f as [ftrans fnat ?]; simpl in *;
             rewrite <- (id_right (g x id)), <- fnat at 1; reflexivity).
  - abstract(intros x y [Ftrans Fnat ?] c f; simpl in *;
    unfold op;
    now rewrite Fnat, id_right).
Defined.

Program Definition CoHom_Alt `(C : Category) : C ∏ C^op ⟶ Sets :=
  Hom C ◯ Swap.

Program Definition CoHom `(C : Category) : C ∏ C^op ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom (C^op) (fst p) (snd p)
                    ; is_setoid := @homset (C^op) (fst p) (snd p) |};
  fmap := fun x y (f : x ~{C ∏ C^op}~> y) =>
    {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.

Program Definition Curried_CoHom `(C : Category) : C ⟶ [C^op, Sets] := {|
  fobj := fun x => {|
    fobj := fun y => {| carrier := @hom (C^op) x y
                      ; is_setoid := @homset (C^op) x y |};
    fmap := fun y z (f : y ~{C^op}~> z) =>
              {| morphism := fun (g : x ~{C^op}~> y) =>
                               (f ∘ g) : x ~{C^op}~> z |}
  |};
  fmap := fun x y (f : x ~{C}~> y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ op f |}
  |}
|}.
Next Obligation.
  simpl; intros.
  symmetry.
  now rewrite !comp_assoc.
Qed.

Notation "[Hom ─ , A ]" := (@Curried_CoHom _ A) : functor_scope.
