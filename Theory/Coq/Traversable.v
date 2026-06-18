Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.

Generalizable All Variables.

(** The Traversable type class (sequence/traverse), with its categorical reading *)

(* nLab: https://ncatlab.org/nlab/show/distributive+law
   nLab: https://ncatlab.org/nlab/show/applicative+functor

   No dedicated nLab or Wikipedia page exists for "traversable functor": the
   nLab pages above are the closest (a traversable functor is precisely a
   functor carrying a distributive law over every applicative functor), and
   the Haskell-level account lives on the HaskellWiki / Wikibooks rather than
   in the Wikipedia main namespace
   (https://wiki.haskell.org/Foldable_and_Traversable).

   FP reading.  A traversable functor (in the Haskell sense) is a type
   constructor [T : Type → Type] that can be walked left-to-right while
   running an effect on each element, commuting [T] past any applicative
   functor [F].  The defining operation is
     [traverse : (x → F y) → T x → F (T y)],
   and the equivalent "no-op visitor" form recorded here is
     [sequence : T (F x) → F (T x)]   (Haskell's [sequenceA]).
   The two are interdefinable: [traverse f = sequence ∘ fmap f] and
   [sequence = traverse id].  Lawful instances satisfy three laws (with [η] the
   applicative-transformation / natural-transformation operations):
     naturality    [η ∘ traverse f ≈ traverse (η ∘ f)] for [η] an applicative
                   transformation;
     identity      [traverse Identity ≈ Identity] (the identity applicative);
     composition   [traverse (Compose ∘ fmap g ∘ f)
                      ≈ Compose ∘ fmap (traverse g) ∘ traverse f].
   A lawful [Traversable] is automatically a [Functor] ([fmap] = traverse with
   the identity applicative) and [Foldable] ([foldMap] = traverse with a
   constant applicative).

   Categorical reading.  Following McBride–Paterson, a traversable functor is a
   functor [T : C → C] equipped with a distributive law
     [δ_F : T ◯ F ⟹ F ◯ T]
   natural in the applicative functor [F] (a lax monoidal endofunctor with
   tensorial strength on the category of Coq types); equivalently a coalgebra
   for a parameterised comonad.  The three laws above are the coherence axioms
   making [δ] respect applicative transformations, the identity applicative,
   and applicative composition, so that [Traversable] functors form a monoidal
   category under composition.  By the Representation Theorem (Bird–Gibbons;
   Jaskelioff–O'Connor 2012) the lawful traversable functors on Set are
   exactly the finitary containers (sums of finite products), and that single
   theorem is equivalent to the conjunction of the three laws.

   As is usual for these Coq/Haskell-style classes, the laws are NOT recorded
   as fields here; [Traversable] carries only the [sequence] operation, and
   lawfulness is an obligation discharged for each concrete instance.  The
   fully categorical, law-bearing counterpart lives in
   [Category.Functor.Traversable]. *)

Class Traversable@{d c} {T : Type@{d} → Type@{c}} :=
  (* the distributive law T ◯ F ⟹ F ◯ T for any applicative F (Haskell's [sequenceA]) *)
  sequence : ∀ `{Applicative@{d c} F} {x : Type@{d}}, T (F x) → F (T x).

Arguments Traversable : clear implicits.

(* [Tupersable] is a project-specific specialization of [Traversable] to a
   pairing (writer-style) shape [x * -]: it sequences [T] past the tuple
   functor without requiring the carrier [x] to be [Applicative], by simply
   threading the seed value [a : x] through.  There is no standard name for
   this class; it is the traversal whose "applicative" is the (non-applicative)
   writer-shaped functor [λ y, x * y].  Like the other classes here it is
   lawless, recording only the [sequenceT] operation. *)

Class Tupersable@{d c} {x : Type@{d}} {T : Type@{d} → Type@{c}} := {
  (* sequence T past the writer-shaped tuple functor, seeded by [a : x] *)
  sequenceT {y : Type@{d}} (a : x) : T (x * y)%type → x * T y
}.

Arguments Tupersable : clear implicits.
