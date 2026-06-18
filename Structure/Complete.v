Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.

Generalizable All Variables.

(** * Complete and cocomplete categories *)

(* nLab:      https://ncatlab.org/nlab/show/complete+category
   Wikipedia: https://en.wikipedia.org/wiki/Complete_category

   Wikipedia: "a category C is complete if every diagram F : J → C (where J is
   small) has a limit in C." Dually, C is cocomplete if every such diagram has
   a colimit. nLab: a category "has all small limits" when "every small diagram
   F : D → C where D is a small category has a limit in C." In library notation
   the completeness condition reads:

       ∀ (D : Category) (F : D ⟶ C), Limit F,

   i.e. there is a [Limit] (a terminal/universal cone, see [Structure/Limit.v])
   for every diagram F of shape D in C. Cocompleteness is the exact dual,
   asking for a [Colimit] of every diagram; since [Colimit F := Limit (F^op)],
   C is cocomplete iff C^op is complete, matching the duality recorded by both
   sources.

   On the index class: both sources restrict J (here D) to be *small*. Wikipedia
   notes that demanding limits for *all* (proper-class-sized) diagrams "is too
   strong to be practically relevant" — such a C would be forced to be thin. The
   definitions below quantify over [∀ (D : Category)] without an explicit
   smallness hypothesis; the size discipline is instead carried implicitly by
   the library's universe polymorphism. When [Complete]/[Cocomplete] are
   instantiated, the universe levels of D become constrained relative to those
   of C, which is the universe-polymorphic stand-in for "D small relative to C".
   So these state "has a limit for every (suitably small) diagram" rather than
   the inconsistent all-diagrams reading. The morphism-level equality is the
   setoid [≈] of C, supplied inside [Limit]/[Cone]; it does not appear here. *)

(* C is complete: every diagram F : D ⟶ C has a limit (terminal cone) in C. *)
Definition Complete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Limit F.

(* C is cocomplete: every diagram F : D ⟶ C has a colimit in C — the dual of
   completeness, equivalently completeness of C^op. *)
Definition Cocomplete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Colimit F.
