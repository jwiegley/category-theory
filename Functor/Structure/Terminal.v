Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(** Terminal-object-preserving functors. *)

(* nLab: https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   A terminal functor F : C ⟶ D between categories with terminal objects
   preserves the terminal object (the nullary, or empty, product). The
   terminal object is the limit of the empty diagram, so any limit-preserving
   functor carries it to a terminal object; a functor preserves it exactly
   when the canonical comparison between F 1 and 1 is an isomorphism.

   The comparison is recorded as the field [fobj_one_iso : 1 ≅ F 1], oriented
   in the lax direction so that its forward map [to fobj_one_iso : 1 ~> F 1]
   is the unit comparison η : I → F I of a (lax/strong) monoidal functor for
   the cartesian monoidal structure (tensor = ×, unit = the terminal object).
   The canonical map F 1 ~> 1 — the unique morphism into the terminal object
   1 of D — is then its inverse [from fobj_one_iso]; preservation means that
   unique map is invertible. This orientation matches [pure_iso : I ≅ F I] in
   Functor/Structure/Monoidal/Pure.v.

   This is the nullary-product half of a cartesian (strong monoidal) functor;
   the binary-product half F (x × y) ≅ F x × F y is the separate concern
   [CartesianFunctor] in the sibling file, and the two together give the full
   cartesian functor. The dual notion, a functor preserving the initial
   object, is named [InitialFunctor] below via the opposite functor F^op,
   following the library's built-in duality. *)

Section TerminalFunctor.

Context `{F : C ⟶ D}.
Context `{@Terminal C}.
Context `{@Terminal D}.

Class TerminalFunctor := {
  (* the comparison iso 1 ≅ F 1 witnessing terminal-object preservation *)
  fobj_one_iso : 1 ≅ F 1;

  (* F carries the unique map up to η: fmap ! ≈ η ∘ ! (with η = to fobj_one_iso) *)
  fmap_one {X : C} : fmap one ≈ to fobj_one_iso ∘ @one _ _ (F X)
}.

End TerminalFunctor.

(* An initial functor preserves the initial object. Rather than restate the
   dual class, it is defined by reusing [TerminalFunctor] on the opposite
   functor F^op (the initial object of C is the terminal object of C^op),
   exploiting the library's built-in duality. The first notation infers the
   categories; the second names them explicitly, requiring C, D and F at
   object level. *)
Notation "'InitialFunctor' F" := (@TerminalFunctor _ _ (F^op) _ _)
  (at level 9) : category_theory_scope.
Notation "@InitialFunctor C D F" := (@TerminalFunctor (C^op) (D^op) (F^op) _ _)
  (at level 9) : category_theory_scope.
