Set Warnings "-notation-overridden".

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Require Export Category.Structure.BiCCC.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section These.

Context `{C : Category}.
Context `{CA : @Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Initial C}.
Context `{@Closed C _}.

(*
(** The type [These x y] in Haskell is algebraically equivalent to [x + y + x * y].
    The following definition proves that [These] with [zero] is a monoidal tensor on
    any category C. *)
Program Definition These_Monoidal : @Monoidal C := {|
  I := 0;
  tensor :=
    {| fobj := fun '(x, y) => x + y + x × y
     ; fmap := fun '(x1, x2) '(y1, y2) '(f1, f2) =>
                 cover (cover f1 f2) (@split C CA _ _ _ _ f1 f2) |}
|}.
Next Obligation.
  rewrite split_id.
  rewrite !cover_id.
  reflexivity.
Qed.
Next Obligation.
  rewrite cover_comp.
  f_equiv.
    now rewrite cover_comp.
  now rewrite split_comp.
Qed.
Next Obligation.
  refine (iso_compose coprod_zero_r _).
  apply coprod_respects_iso; auto.
    now apply coprod_zero_l.
  now apply prod_zero_l.
Defined.
Next Obligation.
  refine (iso_compose coprod_zero_r _).
  apply coprod_respects_iso.
    now apply coprod_zero_r.
  now apply prod_zero_r.
Defined.
Next Obligation.
  refine (iso_compose _ coprod_assoc).
  refine (iso_compose _ coprod_assoc).
  refine (iso_compose _ coprod_assoc).
  refine (iso_compose (iso_sym coprod_assoc) _).
  apply (coprod_respects_iso _ _ iso_id).
  refine (iso_compose (iso_sym coprod_assoc) _).
  refine (iso_compose (iso_sym coprod_assoc) _).
  apply (coprod_respects_iso _ _ iso_id).
  refine (iso_compose _ coprod_comm).
  refine (iso_compose _ coprod_assoc).
  apply (coprod_respects_iso _ _ iso_id).
  refine (iso_compose
            _ (coprod_respects_iso
                 _ _ (@prod_coprod_l _ _ _ _ z (x + y) (x × y))
                 _ _ (@iso_id _ (x × y)))).
  refine (iso_compose
            (iso_sym
               (coprod_respects_iso
                  _ _ (@iso_id _ (y × z))
                  _ _ (@prod_coprod_r _ _ _ _ x (y + z) (y × z)))) _).
  refine (iso_compose _ coprod_assoc).
  refine (iso_compose
            _ (coprod_respects_iso
                 _ _ (@prod_coprod_l _ _ _ _ z x y)
                 _ _ (@iso_id _ (x × y × z + x × y)))).
  refine (iso_compose _ coprod_assoc).
  refine (iso_compose _ coprod_comm).
  refine (iso_compose _ coprod_assoc).
  apply (coprod_respects_iso _ _ iso_id).
  refine (iso_compose _ coprod_assoc).
  refine (iso_compose _ coprod_comm).
  apply coprod_respects_iso.
    now apply (iso_sym prod_coprod_r).
  now apply prod_assoc.
Time Defined.
Next Obligation.
  unmerge.
  cat.
  rewrite !comp_assoc.
  rewrite <- !merge_comp.
  rewrite !comp_assoc.
  rewrite !inl_merge.
  rewrite !inr_merge.
  cat.
  f_equiv; auto.
Admitted.
Next Obligation.
  unmerge.
Qed.
Next Obligation.
  unmerge.
  cat.
  rewrite !comp_assoc.
  rewrite <- !merge_comp.
  rewrite !comp_assoc.
  rewrite !inl_merge.
  rewrite !inr_merge.
  cat.
  f_equiv; auto.
Admitted.
Next Obligation.
  unmerge.
Qed.
Next Obligation.
  unmerge.
Admitted.
Next Obligation.
  unmerge.
Admitted.
Next Obligation.
  unmerge.
Admitted.
Next Obligation.
  unmerge.
Admitted.
*)

End These.
