(* Copyright (c) 2014, John Wiegley
 *
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(** %\chapter{Introduction}% *)

(** * Curried Category Theory

This book represents a formalization in Coq of Edwardk Kmett's [hask] library
for Haskell.  In it, Edward makes use of category theory to unify certain
concepts that before seemed merely related.  Much of this unification is
achieved by choosing the right category, equipped with a monoidal bifunctor of
some kind, and then currying that bifunctor to obtain a mapping from one
concept to another.  With it, many type classes which had to be implemented
separately before (e.g., [Functor], [Bifunctor], [Profunctor], [Applicative]),
can be derived from very few core definitions.

*)

(** * Further notes

[EDIT] Welcome to the Coq development of Edward Kmett's hask library, which
expresses many of the theories used by Haskell in the context of curried
monoidal bifunctors.

[EDIT] This is a specialized treatment of category theory, in that we
narrowing our focus to closed monoidal categories equipped with enriched
internal homs.  We do not attempt to formalize all of category theory, but
only those aspects touching on this specific sub-domain.  We do this because
it is directly applicable to the universe of Haskell types and functions, and
gives us useful results there.

[EDIT] Another deviation from convention is that we name categories after
their morphisms, rather than their objects.  Thus, operations always name
categories, which Coq coerces implicitly to the morphisms of that category.

[EDIT] For example, the notation [F ⟹ G] refers to natural transformations
from [F] to [G]; it also a name for the category [Nat] ([F ⟹ G] is just sugar
for [Nat F G]): the category of functors from some implied [C] to [D].  We can
normally let the particular cateries be inferred from context, or they can be
named using [@Nat C D F G].

[EDIT] Reference: _Categories for the Working Mathematician_
%\cite{Categories}%, by Saunders Mac Lane.

*)
