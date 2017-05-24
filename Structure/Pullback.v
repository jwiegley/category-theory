Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Limit.
Require Export Category.Structure.Span.

(* Given a cospan in C:

           A         B
            \       /
           f \     / g
              \   /
               v v
                C

  This can be thought of, set-theoretically, as the equation:

     ∀ a ∈ A, b ∈ B, f(b) = g(a)

  This is a strong statement, requiring that every element of A agree with
  an element of B through f and g. A pullback is a subset of the cartesian
  product of A and B, X ⊆ A × B, such that (a, b) ∈ X, where the following
  diagram commutes:

                X
              /   \
          pA /     \ pB
            /       \
           A         B
            \       /
           f \     / g
              \   /
               v v
                C

  An example of this is an INNER JOIN of two SQL tables, where f projects a
  primary key from A, and g a foreign key referencing A, so that X contains
  exactly those pairs of rows from A and B where id(A) = fkey(B).

  Wikipedia: "In fact, the pullback is the universal solution to finding a
  commutative square like this. In other words, given any commutative square
  [replacing in the above X with Y, and pA and pB with qA and qB] there is a
  unique function h : Y → X such that pA ∘ h ≈ qA and pB ∘ h ≈ qB."

  Pullbacks are defined first in terms of limits of cospans, and then arrow-
  wise with universal properties, followed by a proof of relation of the two
  representations. *)

Definition Pullback {C : Category} (F : Cospan C) := Limit F.
Arguments Pullback {_} F /.

Definition Pushout {C : Category} (F : Span C) := Colimit F.
Arguments Pushout {_} F /.
