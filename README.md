# Category Theory in Coq

This development encodes category theory in Coq, with the primary aim being to
allow representation and manipulation of categorical terms, as well
realization of those terms in various target categories.

## Usage

It is recommended to include this library in your developments by adding the
following to your `_CoqProject` file:

    -R <path to this library> Category

And to include the primary elements of the library using:

    Require Import Category.Theory.

## Library structure

The library is structured according to the following sections:

### Theory

The essentials of category theory is found here, providing classes and
supporting theorems for the following core concepts:

#### Category

In this library, everything is rooted in categories, which support
the following notions:

##### Objects

The objects of a category are all of some `Type`.

##### Arrows

Morphisms, or arrows, are also of type `Type`, but always in a universe above
objects. All of the library has `Universe Polymorphism` enabled, allowing
categories whose objects are categories, etc.

The morphisms identified by `A ~> B` form a hom-set, except that in this
library it is a hom-setoid, requiring the meaning of (constructive)
equivalence between morphisms to be given.
   
##### Structure and laws

Identity, composition, and the related laws.

#### Morphisms

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
