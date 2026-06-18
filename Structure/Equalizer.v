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

(* The equalizer of the parallel-pair diagram F: a terminal cone over the
   shape [Parallel], whose limit-cone leg over [ParX] is the equalizing map
   and whose universal property is the equalizer's unique factorization. *)
Definition Equalizer {C : Category} (F : Parallel ⟶ C) := Limit F.

(* The coequalizer is the dual notion (nLab, Wikipedia: "obtained by reversing
   the arrows"): a colimit over the same shape [Parallel], i.e. a limit of the
   opposite diagram. Dually it is an object q with a coequalizing map
   q : y ~> q satisfying q ∘ f ≈ q ∘ g, universal among such maps. *)
Definition Coequalizer {C : Category} (F : Parallel ⟶ C) := Colimit F.
