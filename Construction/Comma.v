Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Comma.

Context `{A : Category}.
Context `{B : Category}.
Context `{C : Category}.

Context `{S : A ⟶ C}.
Context `{T : B ⟶ C}.

(* Wikipedia: "... a comma category (a special case being a slice category) is
   a construction in category theory. It provides another way of looking at
   morphisms: instead of simply relating objects of a category to one another,
   morphisms become objects in their own right. This notion was introduced in
   1963 by F. W. Lawvere (Lawvere, 1963 p. 36), although the technique did not
   become generally known until many years later. Several mathematical
   concepts can be treated as comma categories. Comma categories also
   guarantee the existence of some limits and colimits. The name comes from
   the notation originally used by Lawvere, which involved the comma
   punctuation mark." *)

Program Instance Comma : Category := {
  ob      := { p : A * B & S (fst p) ~> T (snd p) };
  hom     := fun x y => (fst (` x) ~> fst (` y)) * (snd (` x) ~> snd (` y));
  homset  := fun _ _ => {| equiv := fun f g => fst f ≈ fst g ∧ snd f ≈ snd g |} ;
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g)
}.

End Comma.

Notation "S ↓ T" := (@Comma _ _ _ S T) (at level 90).
