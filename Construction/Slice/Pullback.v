Set Warnings "-notation-overridden".
Set Warnings "-local-declaration".

Require Import Category.Lib.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Pullback.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Module SliceFunctors.

Context `{C : Category}.
Context `{A : @Cartesian C}.

Program Definition Bang_Functor `(f : a ~> b) : @Slice C a ⟶ @Slice C b := {|
  fobj := λ '(o; h), (o; f ∘ h);
  fmap := λ x y f, (_; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  now rewrite X.
Qed.

Notation "f !" := (Bang_Functor f) (at level 90) : category_scope.

Hypothesis pullbacks : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Z), Pullback f g.

Program Definition Star_Functor `(f : c ~> a) :
  @Slice C a ⟶ @Slice C c := {|
  fobj := λ '(_; h),
            let pull : Pullback h f := pullbacks h f in
            (Pull h f pull; pullback_snd h f pull);
  fmap := λ '(a; x) '(b; y) '(g; H),
            let ypb : Pullback y f := pullbacks y f in
            let xpb : Pullback x f := pullbacks x f in
            let uniq :=
                  ump_pullbacks
                    _ _ ypb _
                    (g ∘ pullback_fst x f xpb)
                    (pullback_snd x f xpb)
                    ltac:(rewrite comp_assoc, H;
                          exact (pullback_commutes x f xpb)) in
            (unique_obj uniq; snd (unique_property uniq))
|}.
Next Obligation.
  proper; simpl in *.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks0 _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  intuition eauto.
  now rewrites.
Qed.
Next Obligation.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  now cat.
Qed.
Next Obligation.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks0 _ _ _ _); simpl).
  repeat (destruct (ump_pullbacks1 _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  split.
  - rewrite comp_assoc.
    rewrite a1.
    now comp_left.
  - rewrite comp_assoc.
    now rewrite b0.
Qed.

(* Program Definition Production {a c : C} : C ⟶ C := {| *)
(*   fobj := λ o, o × c ^ a; *)
(*   fmap := _ *)
(* |}. *)
(* Next Obligation. now apply first_id. Qed. *)
(* Next Obligation. now apply first_comp. Qed. *)

(* Program Definition Base_Functor_Adjunction `(f : a ~> b) : *)
(*   Star_Functor f ⊣ Bang_Functor f := {| *)
(*   adj := λ _ _, {| to   := _ *)
(*                  ; from := _ |} *)
(* |}. *)
(* Next Obligation. *)
(*   construct. *)

End SliceFunctors.
