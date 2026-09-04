(* Boundary probe for Instance/Adj.v and Instance/Adj/Forgetful.v.

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7,
   book p. 101: the category of adjunctions, whose arrows are the conjugate
   pairs <sigma, tau>.  His display puts sigma FORWARD on the left adjoints
   and tau BACKWARD on the right adjoints.

   THE ONE DESIGN DECISION OF Instance/Adj.v IS THAT VARIANCE, and it is
   expressed by the ORDER of the two adjunction arguments handed to
   [Conjugate]: the hom x -> y is [Conjugate (adjobj_adj y) (adjobj_adj x)].
   Nothing in a type checker complains if that order is flipped -- the
   result is simply a different, and wrong, category.  This file pins it.

   Each negative below was stripped one at a time and compiled alone.  A
   negative that passes prints nothing, so reading its error text requires
   stripping it first.

   These facts were measured while Instance/Adj.v was built but could be
   pinned nowhere at the time; this file is where they are pinned. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* Instrument: this file's negatives are only as good as the harness.  A
   name that exists nowhere must be refused. *)
Fail Check p395_no_such_constant_anywhere.

Section Variance.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A  : F  ⊣ U).
Context {F' : D ⟶ C} {U' : C ⟶ D} (A' : F' ⊣ U').

(* CONTROLS.  The constants the negative names must appear outside it, or a
   rename would leave the negative vacuously green. *)
Check @Conjugate.
Check A.
Check A'.
Check (fun (x : D) => F x).
Check (fun (a : C) => U a).

(* POSITIVE: with the adjunction arguments SWAPPED, Mac Lane's labelling
   typechecks -- sigma forward on the left adjoints, tau backward on the
   right adjoints. *)
Check (fun (s : F ⟹ F') (t : U' ⟹ U) => Conjugate A' A s t).

(* NEGATIVE 1 (TYPING).  The OTHER labelling does not fit the same slots.
   Stripped, this reports a plain "has type ... while it is expected to have
   type ...", with no universe clause: [Conjugate A' A] demands its third
   argument at [F ⟹ F'], so handing it [F' ⟹ F] is a type mismatch and
   not a unification complaint about universes. *)
Fail Check (fun (s : F' ⟹ F) (t : U ⟹ U') => Conjugate A' A s t).

End Variance.

Section HomShape.

Context {C D : Category}.

(* CONTROLS for the names the next negative mentions. *)
Check @ConjPair.
Check @conj_left.
Check @conj_right.
Check @conj_pair_law.
Check @adjobj_adj.

(* The hom of [Adj C D] IS the conjugate-pair record, on the nose. *)
Example adj_hom_is_conjpair (x y : AdjObj C D) :
  (x ~{Adj C D}~> y) = @ConjPair C D x y := eq_refl.

(* And the law field is the SWAPPED application, which is the variance the
   negative above guards. *)
Example adj_law_is_swapped (x y : AdjObj C D) (f : x ~{Adj C D}~> y) :
  Conjugate (adjobj_adj y) (adjobj_adj x) (conj_left f) (conj_right f)
  := conj_pair_law f.

End HomShape.

Section ForgetfulShape.

(* CONTROLS. *)
Check @AdjForgetLeft.
Check @AdjForgetRight.

(* The left forgetful functor is covariant onto the left adjoints; the
   right one is displayed on the OPPOSITE category, which is how Mac Lane's
   [A^(adj)X]^op -> X^A is rendered.  Both types are pinned here so that a
   later change of variance breaks this file rather than passing quietly. *)
Example adj_forget_left_type (C D : Category) :
  AdjForgetLeft C D = AdjForgetLeft C D := eq_refl.

Check (fun C D : Category => AdjForgetLeft C D : Adj C D ⟶ [D, C]).
Check (fun C D : Category => AdjForgetRight C D : (Adj C D)^op ⟶ [C, D]).

(* NEGATIVE 2 (TYPING).  The right forgetful functor is NOT covariant on
   [Adj C D]; ascribing it there is refused.  This is the contravariance,
   pinned. *)
Fail Check (fun C D : Category => AdjForgetRight C D : Adj C D ⟶ [C, D]).

End ForgetfulShape.
