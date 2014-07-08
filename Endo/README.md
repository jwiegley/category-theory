The theories in these files have been simplified by restricting them to just
endofunctors on Coq, the category of Coq types and functions.  This is to
better mirror the way endofunctors are used in Haskell, at least until I can
make it easier to work with a more general formalization over any category.

Type classes yet to prove for Source in Conduit.v:

  - Semigroup
  - Monoid
  - Alternative
  - MonadPlus
  - MFunctor
  - MMonad
  - MonadFree
  - Foldable
