Require Import Category.Lib.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

(** * The unit of a semicartesian monoidal category is terminal *)

(* nLab: https://ncatlab.org/nlab/show/semicartesian+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   A semicartesian (affine) monoidal category is a monoidal category whose
   unit object I is terminal: every object x has the discard map eliminate :
   x ~> I, and any two maps x ~> I agree (unit_terminal). This file repackages
   exactly that data as a Terminal structure on I,

       terminal_obj := I,
       one          := eliminate    (the unique x ~> I),
       one_unique   := unit_terminal (any two x ~> I agree under ≈),

   matching nLab ("the unit for the tensor product is a terminal object") and
   Wikipedia ("in any cartesian monoidal category, the terminal object is the
   monoidal unit"; cartesian ⊆ semicartesian).

   The same definition, with the same name, is given at top level in
   Structure/Monoidal/Semicartesian.v; that copy is the one downstream files
   (e.g. Instance/Coq/Par.v) use. The version here is section-local, hence
   lives in the distinct module Category.Structure.Monoidal.Semicartesian.
   Terminal. *)

Section SemicartesianMonoidalTerminal.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

Program Definition SemicartesianMonoidal_Terminal : @Terminal C := {|
  terminal_obj := I;                     (* the terminal object is the unit I *)
  one := @eliminate _ _ _;               (* ! := eliminate, the discard x ~> I *)
  one_unique := @unit_terminal _ _ _     (* uniqueness of x ~> I, up to ≈ *)
|}.

End SemicartesianMonoidalTerminal.
