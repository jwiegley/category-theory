# Adjunctions

There are at least four ways to specify an adjunction F ⊣ G:

1. A bijective mapping between hom-sets `F a ~> b` and `a ~> U b`, natural in
   `a` and `b`. This is the definition given in `Category.Theory.Adjunction`.
   
2. A pair of `unit` and `counit` natural transformations, and that they
   compose to the identity functor in certain ways. This is given in
   `Category.Adjunction.Natural.Transformation`.

3. A pair of `unit` and `counit` morphisms, and their related equations. This
   spells out the details of (2) in terms of morphisms, equivalences in C and
   D, and the naturality conditions, rather than as natural transformations
   and equivalences in the functor categories [C, D] and [D, C]. This is not
   given, since it is not used.

4. An isomorphism between hom-set functors `Hom(F -, -)` and `Hom(-, U -)`.
   This the briefest statement, from which all the other formulations may be
   derived. This is given in `Category.Adjunction.Hom`.

See the Wikipedia page
on [Adjunctions](https://en.wikipedia.org/wiki/Adjoint_functors) for notes on
how these four formulations relate to each other.
