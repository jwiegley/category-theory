Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Parallel.

Generalizable All Variables.

(** * Equalizer of a parallel pair (a limit over the shape [Parallel]) *)

(* nLab:      https://ncatlab.org/nlab/show/equalizer
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   Given a parallel pair f, g : x ~> y in C, an equalizer is an object e
   together with an equalizing map i : e ~> x that equalizes the pair,

       f ∘ i ≈ g ∘ i,

   and is universal with this property: for every object n and every map
   m : n ~> x with f ∘ m ≈ g ∘ m there is a unique u : n ~> e with i ∘ u ≈ m
   (Wikipedia; nLab calls i the "equalizing map" and e the universal such
   object). Equivalently the equalizer is the limit of the parallel-pair
   diagram

       e ~> x ⇉ y,

   i.e. the limit over the two-object/two-arrow shape [Parallel] (see
   [Instance/Parallel.v]). That is exactly how it is defined here: an
   [Equalizer] is a [Limit] of a functor F : Parallel ⟶ C.

   This file does not restate the equalizing map or the universal property as
   fresh fields; they are inherited from [Limit] (see [Structure/Limit.v]).
   Under the shape [Parallel] the limit cone's two legs are the equalizing map
   i (the leg over [ParX], landing in x) and its composite with the pair (the
   leg over [ParY], landing in y); the leg-coherence law forces f ∘ i ≈ g ∘ i,
   and [ump_limits] supplies the unique mediating u for every competing cone.
   Use [APair f g : Parallel ⟶ C] from [Instance/Parallel.v] to obtain the
   diagram F from an actual parallel pair f, g. *)

(* Where equalizers come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/coequalizer
   nLab:  https://ncatlab.org/nlab/show/regular+category
   Paper: Eckmann, Hilton, "Group-like structures in general categories
          II. Equalizers, limits, lengths", Mathematische Annalen 151, 1963
   Blog:  Milewski, "Limits and Colimits", Category Theory for
          Programmers, 2015

   Equalizers entered category theory in the second installment of Eckmann
   and Hilton's "Group-like structures" series (Mathematische Annalen 151,
   1963), which defined them for arbitrary finite families of parallel
   morphisms under the name "left equalizers", with coequalizers as "right
   equalizers" (nLab).  The same paper already contains the basic fact of
   the subject: the equalizing map is always a monomorphism (their
   Prop. 1.3), since the mediating morphism of the universal property is
   unique.  The older algebraic name "difference kernel" records the
   additive case: where morphisms subtract, the equalizer of f and g is
   the kernel of f − g, and conversely the kernel of f is the equalizer of
   f with zero (Wikipedia).  Structure/Kernel.v performs exactly that
   specialization, defining [IsKernel] as [IsEqualizer] against [zero_mor]
   and deriving [kernel_monic] from [equalizer_monic].

   The equalizer is the categorical solution set of an equation.  In Set
   it is the subset {s | f s = g s} together with its inclusion (nLab),
   and the universal property says that morphisms into the equalizer are
   the same thing as morphisms into x satisfying the equation: the
   equalizer represents solutions.  It follows from monicity that
   equalizers are a canonical source of subobjects — those carved out by
   an equation — and monomorphisms arising this way are called regular
   (Wikipedia).  In type theory the same object is the dependent sum over
   the identity type, Σ (a : A), f a = g a (nLab), which is the subset
   type {a : A | f a = g a} of Coq itself.  Milewski's programming
   account works over precisely this file's two-object shape: the cone
   condition collapses to a single equation, and "an equalizer can thus
   be used to solve equations of the type f x = g x" (Milewski, "Limits
   and Colimits", 2015).

   Two structural theorems give this one limit shape its weight.  First,
   completeness reduces to it: a category has all (finite) limits as soon
   as it has (finite) products and equalizers, every limit arising as an
   equalizer of two maps between products (Mac Lane, Categories for the
   Working Mathematician, 2nd ed. 1998, §V.2, "Limits by Products and
   Equalizers"), and a functor preserves all limits as soon as it
   preserves both primitives (nLab, "limit").  Second, the shape carries
   Freyd's adjoint functor theorem (Freyd, Abelian Categories, 1964; Mac
   Lane §V.6): a weakly initial family becomes an initial object by
   taking the product and then the joint equalizer of all its
   endomorphisms, monicity of the equalizer supplying the uniqueness half
   (nLab, "adjoint functor theorem").  Both arguments run in this
   library: [initial_from_weakly_initial] in Theory/WeaklyInitial.v
   consumes [HasEqualizers], and Adjunction/GAFT.v extracts that supply
   from completeness as [Complete_HasEqualizers].

   Dually, [Coequalizer] is the categorical quotient.  In Set the
   coequalizer of f and g is the quotient of y by the equivalence relation
   generated by f x ∼ g x, and epimorphisms arising as coequalizers are
   the regular ones (nLab).  The interplay between coequalizers and kernel
   pairs — a regular epimorphism with a kernel pair is the coequalizer of
   that kernel pair — is what a regular category axiomatizes (Barr,
   Grillet, van Osdol, Exact Categories and Categories of Sheaves,
   Springer LNM 236, 1971), yielding the (regular epi, mono) image
   factorization; see Structure/Regular.v and the packaged [Regular_OFS]
   in Structure/Regular/Factorization.v.  The sheaf condition is likewise
   an equalizer diagram — local data glue exactly when they agree on
   overlaps (nLab, "sheaf") — and Beck's monadicity theorem runs on the
   split and reflexive coequalizers of Structure/Coequalizer/Split.v and
   Structure/Coequalizer/Reflexive.v, consumed throughout
   Monad/Monadicity/.

   This file supplies only the limit-form definitions [Equalizer] and
   [Coequalizer].  The elementary fork presentation [IsEqualizer], with
   [equalizer_monic], [equalizer_unique], the supply class
   [HasEqualizers], and round trips to the bundled form here, lives in
   Structure/Equalizer/Fork.v; the dual cofork API is
   Structure/Coequalizer.v. *)

(* The equalizer of the parallel-pair diagram F: a terminal cone over the
   shape [Parallel], whose limit-cone leg over [ParX] is the equalizing map
   and whose universal property is the equalizer's unique factorization. *)
Definition Equalizer {C : Category} (F : Parallel ⟶ C) := Limit F.

(* The coequalizer is the dual notion (nLab, Wikipedia: "obtained by reversing
   the arrows"): a colimit over the same shape [Parallel], i.e. a limit of the
   opposite diagram. Dually it is an object q with a coequalizing map
   q : y ~> q satisfying q ∘ f ≈ q ∘ g, universal among such maps. *)
Definition Coequalizer {C : Category} (F : Parallel ⟶ C) := Colimit F.
