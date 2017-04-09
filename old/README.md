Welcome to the Coq formalization of Edward Kmett's Hask library.

A PDF book documenting this development is here:

    http://ftp.newartisans.com/pub/hasq/Hasq.pdf

HTML documentation is here:

    http://ftp.newartisans.com/pub/hasq

* What are we trying to accomplish?

Proving that a view of Haskell based on curried bifunctors leads to a
unification of many concepts which are presently separate in the common
Haskell idiom.

* Future directions

- see how we can use univalence to avoid predicative extensionality
- start using -indices-matter (forces `eq` to be in `Type`)
- use `Set Primitive Projects`
- automatic dualization
- adjunctions
- limits
- trivial categories
  - product
  - sum
  - category Two
  - binary products (using limits), C^2
- category of spans
- equalizers
- pullbacks
- arbitrary products (indexing set does not have to be a number)
- copowersn
- dependent products (pi-types, exponentials)
- ends and co-ends
- dinatural transformations
- comma categories
- Grothendieck through commas
- setting up limits and colimits in terms of adjoints to the diagonal functor
- monoidal categories
- day convolution
- monoidal functors
- monads as monoids
- profunctor composition
- prearrows as monoids of profunctor composition
- a generalized tambara module that I use for lens
- free freyd categories and can freely adjoin
- 'profunctor strength' to any profunctor
- model monads and comonads on the category of profunctors
- since the Tambara construction is a comonad
- the left adjoint to the construction is a monad
- ... whose monad algebras are the strong profunctors
- once we have that we can start talking about the lens plumbing
