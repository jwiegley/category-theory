Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(** Functors between slice categories induced by a base morphism. *)

(* nLab: https://ncatlab.org/nlab/show/base+change
   nLab: https://ncatlab.org/nlab/show/dependent+sum
   nLab: https://ncatlab.org/nlab/show/over+category
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   A morphism f : a ~> b in C induces two functors between the slice categories
   C ̸ a and C ̸ b:

   - Bang_Functor f : C ̸ a ⟶ C ̸ b is the dependent sum Σ_f (also written f_!,
     "lower shriek"), defined by post-composition with f: it sends an object
     (o; h) with h : o ~> a to (o; f ∘ h), an object over b. This needs no extra
     structure on C.

   - Star_Functor f : C ̸ a ⟶ C ̸ c is the base change (pullback) functor f*,
     defined by pulling back along f: given f : c ~> a, it sends an object (o; h)
     with h : o ~> a to (Pull h f; pullback_snd h f), the fiber product o ×_a c
     equipped with its projection to c. This requires that the relevant
     pullbacks exist in C, which is assumed below as the Hypothesis [pullbacks].

   These two functors are adjoint, dependent sum on the left and base change on
   the right: for a single f : a ~> b,

       Bang_Functor f ⊣ Star_Functor f,   i.e.   Σ_f ⊣ f*

   (a slice C ̸ b having pullbacks along f exactly makes f* the right adjoint of
   post-composition Σ_f). When C is locally cartesian closed, f* itself has a
   further right adjoint Π_f (the dependent product), giving Σ_f ⊣ f* ⊣ Π_f.
   The adjunction is sketched in the commented Base_Functor_Adjunction stub
   below; note that the live statement should read Bang_Functor f ⊣ Star_Functor
   f, since dependent sum is the LEFT adjoint. *)

Section SliceFunctors.

Context `{C : Category}.
Context `{A : @Cartesian C}.   (* only used by the commented Production functor *)

#[local] Set Transparent Obligations.

(* Dependent sum Σ_f (= f_!): post-compose the structure morphism with f. *)
Program Definition Bang_Functor `(f : a ~> b) : @Slice C a ⟶ @Slice C b := {|
  fobj := λ '(o; h), (o; f ∘ h);
  fmap := λ x y f, (_; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  now rewrite X.
Qed.

(* Postfix notation for Σ_f, mirroring the standard f_! ("lower shriek"). *)
Notation "f !" := (Bang_Functor f) (at level 90) : category_scope.

(* C has all binary pullbacks; this is what makes base change f* below total. *)
Hypothesis pullbacks : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Z), Pullback f g.

(* Base change f*: pull the structure morphism back along f, taking the
   resulting projection onto c as the new structure morphism over c. *)
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
