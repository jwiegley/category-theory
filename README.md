# Category Theory in Coq

This development encodes category theory in Coq, with the primary aim being to
allow representation and manipulation of categorical terms, as well
realization of those terms in various target categories.

Versions used: [Coq](https://github.com/coq/coq/) 8.10.2, 8.11.2, 8.12.2, 8.13.2.
Some parts depend on [Coq-Equations](https://github.com/mattam82/Coq-Equations) 1.2.4.

## Usage

It is recommended to include this library in your developments by adding the
following to your `_CoqProject` file:

    -R <path to this library> Category

Then include the primary elements of the library using:

    Require Import Category.Theory.

## Library structure

This library is broken up into several major areas:

  - Core `Theory`, covering topics such as categories, functors, natural
    transformations, adjunctions, kan extensions, etc.

  - Categorical `Structure`, which reveals internal structure of a category by
    way of morphisms related to some universal property.

  - Categorical `Construction`, which introduces external structure by
    building new categories out of existing ones.

  - Species of different kinds of `Functor`, `Natural.Transformation`,
    `Adjunction` and `Kan.Extension`; for example: categories with monoidal
    structure give rise to monoidal functors preserving this structure, which
    in turn leads to monoidal transformations that transform functors while
    preserving their monoidal mapping property.

  - The `Instance` directory defines various categories; some of these are
    fairly general, such as the category of preorders, applicable to any
    `PreOrder` relation, but in general these are either not defined in terms
    of other categories, or are sufficiently specific.

  - When a concept, such as limits, can be defined using more fundamental
    terms, that version of limits can be found in a subdirectory of the
    derived concept, for example there is `Category.Structure.Limit` and
    `Category.Limit.Kan.Extension`. This is done to demonstrate the
    relationship of ideas; for example:
    `Category.Construction.Comma.Natural.Transformation`. As a result, files
    with the same name occur often, with the parent directory establishing
    intent.

## Duality

The core theory is defined in such a way that "the dual of the dual" is
evident to Coq by mere simplification (that is, "C^op^op = C" follows by
reflexivity for the opposite of the opposite of categories, functors, natural
transformation, adjunctions, isomorphisms, etc.).

For this to be true, certain artificial constructions are necessary, such as
repeating the associativity law for categories in symmetric form, and likewise
the naturality condition of natural transformations. This repeats proof
obligations when constructing these objects, but pays off in the ability to
avoid repetition when stating the dual of whole structures.

As a result, the definition of comonads, for example, is reduced to one line:

    Definition Comonad `{M : C ⟶ C} := @Monad (C^op) (M^op).
    
Most dual constructions are similarly defined, with the exception of `Initial`
and `Cocartesian` structures. Although the core classes are indeed defined in
terms of their dual construction, an alternate surface syntax and set of
theorems is provided (for example, using `a + b` to indicate coproducts) to
make life is a little less confusing for the reader. For instance, it follows
from duality that `0 + X ≅ X` is just `1 × X ≅ X` in the opposite category,
but using separate notations makes it easier to see that these two
isomorphisms in the *same* category are not identical. This is especially
important because Coq hides implicit parameters that would usually let you
know duality is involved.

## Design decisions

Some features and choices made in this library:

  - Type classes are used throughout to present concepts. When a type class
    instance would be too general -- and thus overlap with other instances --
    it is presented as a definition that can later be added to instance
    resolution with `Existing Instance`.

  - All definitions are in Type, so that `Prop` is not used anywhere except
    specific category instances defined over `Prop`, such as the category
    `Rel` with heterogeneous relations as arrows.

  - No axioms are used anywhere in the core theory; they appear only at times
    when defining specific category instances, mostly for the `Coq` category.

  - Homsets are defined as computationally-relevant homsetoids (that is, using
    `crelation`). This is done using a variant of the `Setoid` type class
    defined for this library; likewise, the category of `Sets` is actually the
    category of such setoids. This increases the proof work necessary to
    establish definitions -- since preservation of the equivalence relation is
    required at all levels -- but allows categories to be flexible in what it
    means for two arrows to be equivalent.

## Notations

There are many notations used through the library, which are chosen in an
attempt to make complex constructions appear familiar to those reading modern
texts on category theory. Some of the key notations are:

 - `≈` is equivalence; equality is almost never used.
 - `≈[Cat]` is equivalence between arrows of some category, here `Cat`; this
   is only needed when type inference fails because it tries to find both the
   type of the arguments, and the type class instance for the equivalence
 - `≅` is isomorphism; apply it with `to` or `from`
 - `≊` is used specifically for isomorphisms between homsets in `Sets`
 - `iso⁻¹` also indicates the reverse direction of an isomorphism
 - `X ~> Y`: a squiggly arrow between objects is a morphism
 - `X ~{C}~> Y`: squiggly arrows may also specify the intended category
 - `id[C]`: many known morphisms allow specifying the intended category;
   sometimes this is even used in the printing format
 - `C ⟶ D`: a long right arrow between categories is a functor
 - `F ⟹ G`: a long right double arrow between functors is a natural
   transformation
 - `f ∘ g`: a small centered circle is composition of morphisms
 - `f ∘[Cat] g`: composition can specify the intended category, as an aid to
   type inference
 - `f ○ g`: a larger hollow circle is composition of functors
 - `f ⊙ g`: a larger circle with a dot is composition of isomorphisms
 - `f ∙ g`: a solid composition dot is composition of natural
   transformations
 - `f ⊚ g`: a larger circle with a smaller circle is composition of
   adjunctions
 - `f \o g`: a backslash-then-o is specifically composition in the `Coq`
   category; that is, regular functional composition
 - `([C, D])`: A pair of categories in square brackets is another way to give
   the type of a functor, being an object of the category `Fun(C, D)`
 - `F ~{[C, D]}~> G`: An arrow in a functor category is a natural
   transformation
 - `F ⊣ G`: the turnstile is used for adjunctions
 - Cartesian categories use `△` as the `fork` operation and `×` for products
 - Cocartesian categories use `▽` as the `merge` operation and `+` for
   coproducts
 - Closed categories use `^` for exponents and `≈>` for the internal hom
 - As objects, the numbers `0` and `1` refer to initial and terminal objects
 - As categories, the numbers `0` and `1` refer to the initial and terminal
   objects of `Cat`
 - Products of categories can be specified using `∏`, which does not require
   pulling in the cartesian definition of `Cat`
 - Coproducts of categories can be specified using `∐`, which does not require
   pulling in the cocartesian definition of `Cat`
 - Products of functors are given with `F ∏⟶ G`, combining product and functor
   notations; the same for `∐⟶`
 - Comma categories of two functors are given by `(F ↓ G)`
 - Likewise, the arrow category of `C⃗`
 - Slice categories use a unicode forward slash `C̸c`, since the normal forward
   slash is not considered an operator
 - Coslice categories use `c ̸co C`, to avoid ambiguity

## The Computational Solver

There are some equivalences in category-theory that are very easily expressed
and proven, but slow to establish in Coq using only symbolic term rewriting.
For example:

    (f ∘ g) △ (h ∘ i) ≈ split f h ∘ g △ i

This is solved by unfolding the definition of split, and then rewriting so
that the fork operation (here given by `△`) absorbs the terms to its left,
followed by observing the associativity of composition, and then simplify
based on the universal properties of products. This is repeated several times
until the prove is trivially completed.

Although this is easy to state, and even to write a tactic for, it can be
extremely slow, especially when the types of the terms involved becomes large.
A single rewrite can take several seconds to complete for some terms, in my
experience.

The goal of this solver is to reify the above equivalence in terms of its
fundamental operations, and then, using what we know about the laws of
category theory, to compute the equivalence down to an equation on indices
between the reduced terms. This is called *computational reflection*, and
encodes the fact that our solution only depends on the categorical structure
of the terms, and not their type.

That is, an incorrectly-built structure will simply fail to solve; but since
we're reflecting over well-typed expressions to build the structure we pass to
the solver, combined with a proof of soundness for that solver, we can know
that solvable, well-typed, terms always give correct solutions. In this way,
we transfer the problem to a domain without types, only indices, solve the
structural problem there, and then bring the solution back to the domain of
full types by way of the soundness proof.

## Future directions

### Compiling to categories

Work has started in `Tools/Abstraction` for compiling monomorphic Gallina
functions into "categorical terms" that can then be instantiated in any
supporting target category using Coq's type class instance resolution.

This is as a Coq implementation of an idea developed by Conal Elliott, which
he first implemented in and for Haskell. It is hoped that the medium of
categories may provide a sound means for transporting Gallina terms into other
syntactic domains, without relying on Coq's extraction mechanism.

## License

This library is made available under the MIT license, a copy of which is
included in the file `LICENSE`. Basically: you are free to use it for any
purpose, personal or commercial (including proprietary derivates), so long as
a copy of the license file is maintained in the derived work. Further, any
acknowledgement referring back to this repository, while not necessary, is
certainly appreciated.

John Wiegley
