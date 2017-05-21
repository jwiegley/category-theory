# Category Theory in Coq

This development encodes category theory in Coq, with the primary aim being to
allow representation and manipulation of categorical terms, as well
realization of those terms in various target categories.

## Usage

It is recommended to include this library in your developments by adding the
following to your `_CoqProject` file:

    -R <path to this library> Category

Then include the primary elements of the library using:

    Require Import Category.Theory.

## Library structure

This library is broken up into several major areas:

  - The core `Theory`, covering topics such as categories, functors, natural
    transformations, adjunctions, kan extensions, limits, etc.

  - Categorical `Structure`, that reveals some of the internal structure of a
    category by way of a set of morphisms related by some universal property.

  - Categorical `Construction`, that introduces external structure by building
    new categories out of existing ones.

  - Species of different kinds of `Functor` and `Natural.Transformation`; for
    example: categories with monoidal structure give rise to monoidal functors
    preserving this structure, which in turn leads to monoidal transformations
    that transform functors while preserving their monoidal mapping property.

  - The `Instance` directory defines various specific categories; some of
    these are fairly general, such as the category of preorders, applicable to
    any `PreOrder` relation, but it is not defined in terms of other
    categories.

  - When a concept, such as limits, can be defined using more fundamental
    terms, that version of limits can be found in a subdirectory of the
    derived concept, for example there is `Category.Theory.Limit` and
    `Category.Theory.Limit.Kan.Extension`. This is done to demonstrate the
    relationship of ideas; for example:
    `Category.Theory.Structure.Comma.Natural.Transformation`. As a result,
    files with the same name occur often, with the parent directory
    establishing the intent.

## Design decisions

Some of the features of this library are:

  - Type classes are used throughout to present concepts. When a type class
    instance would be too general -- and thus overlap with other instances --
    it is given as a definition that can later be added to instance resolution
    using `Existing Instance`.

  - All definitions are constructive, meaning that `Prop` is not used anywhere
    except for specific category instances that are defined over `Prop`, such
    as the category whose arrows are heterogeneous relations.

  - No axioms are used anywhere in the core theory; they only appear at times
    when defining specific category instances, such as the above mentioned
    category of heterogeneous relations, where proof irrelevance is needed to
    show equivalence between morphisms.

  - Homsets are defined as constructive homsetoids, using a variant of the
    `Setoid` type class defined within this library; likewise, the category of
    Sets is the category of setoids. This increases the amount of proof work
    necessary to establish new categories and functors, since preservation of
    the equivalence relation is required at all levels, but this allows
    categories to be flexible in what it means for two arrows to be
    equivalent.

## Notations

There are many notations used through the library, which are chosen in an
attempt to make complex constructions appear familiar to those reading modern
texts on category theory. Some of the key notations are:

 - `≈` is equivalence; equality is almost never used.
 - `≈[Cat]` is equivalence in the category `Cat`, or an isomorphism between
   categories; this is only needed if type inference fails because when type
   inference tries to find both the type of the arguments and the type class
   instance for the equivalence
 - `≅` is isomorphism; used as a morphism it coerces to the forward direction
   of the conversion
 - `iso⁻¹` or `from iso` indicates the reverse direction of the conversion
 - `≊` is used specifically for isomorphisms between homsets (in Sets)
 - `X ~> Y`: a squiggly arrow between objects is a morphism in a category
 - `X ~{C}~> Y`: squiggly arrows may also specify the intended category
 - `id[C]`: many known morphisms allow specifying the intended category;
   sometimes this is even used in the printing format
 - `C ⟶ D`: a long right arrow between categories indicates a functor
 - `F ⟹ G`: a long right double arrow between functors indicates a natural
   transformation
 - `f ∘ g`: a small centered circle is composition of morphisms
 - `f ∘[Cat] g`: composition can specify the intended category, as an aid to
   type inference
 - `f \o g`: a backslash-then-o is specifically composition in the `Coq`
   category; that is, regular functional composition
 - `f ○ g`: a larger hollow circle is composition of functors
 - `f ⊙ g`: a larger circle with a dot is composition of natural
   transformations
 - `([C, D])`: A pair of categories in square brackets is another way to give
   the type of a functor, being an object of the category `Fun(C, D)`.
 - `F ~{[C, D]}~> G`: An arrow in a functor category is a natural
   transformation.
 - `F ⊣ G`: the turnstile is used for adjunctions
 - Cartesian categories use `△` as the `fork` operation and `×` for products
 - Cocartesian categories use `▽` as the `merge` operation and `+` for
   coproducts
 - Closed categories use `^` for exponents
 - As objects, the numbers `0` and `1` refer to initial and terminal objects
 - As categories, the numbers `0` and `1` refer specifically to the initial
   and terminal objects of `Cat`
 - Products in `Cat` may also be specified using `∏`, which does not require
   pulling in the definition of `Cat`
 - Products of functors are given with `F ∏⟶ G`, combining the product and
   functor notations
 - Comma categories are the usual `(F ↓ G)`
 - Likewise, the arrow category of `C⃗`
 - Slice categories use a unicode forward slash `C̸c`, since the normal forward
   slash is not considered an operation
 - Coslice categories use `C ̸co c`, to avoid ambiguity

## More on structure

The library is structured according to the following sections:

### Theory

The essentials of category theory is found here, providing classes and
supporting theorems for the following core concepts:

#### Category

In this library, everything is rooted in categories, which support
the following notions:

The objects of a category are all of some `Type`.

Morphisms, or arrows, are also of type `Type`, but always in a universe above
objects. All of the library has `Universe Polymorphism` enabled, allowing
categories whose objects are categories, etc.

The morphisms identified by `A ~> B` form a hom-set, except that in this
library it is a hom-setoid, requiring the meaning of (constructive)
equivalence between morphisms to be given.
   
Identity, composition, and the related laws.

Defines the various properties and relationships of morphisms, as well as
specific types such as epis, monos, split epis, etc.

#### Isomorphism

Constructively defines what it means for two objects in a category to be
"isomorphic". This requires both witnesses to the isomoprhism, and proof their
compositions are equivalent to identity in both directions. Since this is a
constructive definition, having an isomorphism allows for conversion of
objects within definitions.

#### Functor

Functors map objects and morphisms between categories, where such mappings
preserve equivalences and basic categorical structure (identity and
composition). Note that there are many species of functor, one each for the
various categorical structures (included below), for example, the
`CartesianFunctor` that maps products to products and preserves all its
structural properties and laws.

#### Natural (Transformation)

If a functor may be transformed, one must show how to transform mapped objects
and that the mapping of morphisms is natural (i.e., transforming before or
after introduces no change in the effect of such mappings).

#### Adjunction

Adjunctions relate two functors that map between the same two categories
(though in opposite directions), in a manner that is weaker than isomorphism
or equivalence, but still quite informative. In general, one functor is
forgetful, and maps constructions from a more expressive domain into one that
captures only the essence of that structure; while the other is free, and maps
essential constructions into the fuller setting.

As an example: the category of ASTs may be mapped forgetfully to the category
of interpretated objects, which themselves map freely to some "canonical"
representation of each such object. So, "3", "1 + 2", and "2 + 1" all mean 3,
while 3 is canonically represented by the constant "3". The forgetful functor
is the evaluator, and the free functor a parser, giving rise to the following
isomorphism (in the category of Sets, whose objects may be hom-sets):

    AST a ~{category of ASTs}~> b
      ≅ a ~{category of interpretations}~> Denote b

#### Yoneda

Finally, there is the Yoneda lemma, which tells us that a natural
transformation, from the covariant or contravariant hom-functor on some object
in C, to some other functor from C to Sets, is isomorphic to mapping the
object by that functor directly from C to Sets.

Writing this statement in code, it becomes a bit clearer what it's telling us:
If the contravariant functor on `A` turns any `X` into the arrow `A ~> X`, and
if natural transformation is given by `∀ x, f x ~> g x` (assuming naturality),
the statement of the Yoneda lemma is:

    ∀ f x a, Functor f => (x ~{Sets}~> a) ~{Sets}~> f x ≅ f a
    
The Lemma states: Since the only thing knowable about a functor is its ability
to map objects and morphisms, any object `f x` through which we map a morphism
`x ~> a` to obtain an object `f a`, *must* be identical to `f a` obtained
directly, since the functor has no way of introducing additional meaning.

A benefit of the lemma is that we can displace any source object `a` (from an
arbitrary category `C`) into an object in the category of Sets -- i.e., the
hom-set whose domain or codomain is `a` -- allowing us to handle it using the
structure of sets. This has the benefit of making many proofs easier, which
become more difficult when restricted to the fully abstract nature of `C`.

### Structure

Categorical structures identify morphisms that reveal something about the
internal structure of certain categories: for example, products, coproducts
and exponentials (also called "internal homs").

####  Groupoid

A Groupoid is a category where all morphisms are isomorphisms.

####  Initial

An Initial category distinguishes an initial object, with arrows existing from
this object to every other object in the category. Further, any two arrows
from the initial object to the same object are unique up to unique
isomorphism.

####  Terminal

An Terminal category distinguishes a terminal object, with arrows existing
from every other object in the category to this object. Further, any two
arrows from the same object to the terminal object are unique up to unique
isomorphism.

Every terminal object is an initial object in its dual category, a vice versa
(see the Opposite construction, below).

####  Cartesian

####  Cocartesian

####  Bicartesian

####  Closed

####  BiCCC

Bicartesian closed category.

####  Constant

### Construction

A categorical construction builds a more complex category or functor, using
only what is already known about some other category or functor: that is, it
reveals no additional information about the category itself, in the way that
structures do.

#### Opposite

### Instances

These are instances of particular categories, some of which are essential
enough (such as Sets), that they are imported by the core theory modules.

## Future directions

### Compiling to categories

Work has started in `Tools/Abstraction` for compiling monomorphic Gallina
functions into categorical terms abstracted over any bicartesian closed
category, that can then be instantiated in any supporting target category
using Coq's type class instance resolution.

This is as a Coq implementation of an idea developed by Conal Elliott, which
he first implemented in and for Haskell. It is hoped that the medium of
categories may provide a sound means for transporting Gallina terms into other
syntactic domains, without relying on Coq's extraction mechanisms.

### TODO

See the file TODO.org for specific work waiting to be done.
