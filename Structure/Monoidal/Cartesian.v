Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Internal.Product.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/cartesian+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   The forward relationship between products and tensors: every cartesian
   category -- a category with binary products ([Cartesian]) and a terminal
   object ([Terminal]) -- is monoidal, with the tensor given by the
   categorical product and the unit by the terminal object,

       x ⨂ y := x × y,        I := 1.

   This is the direction most users want, because it lets every theorem about
   general monoidal categories specialize to cartesian products for free.

   The construction itself, together with all of its coherence proofs (the
   associator and unitors built from [prod_assoc]/[prod_one_l]/[prod_one_r],
   the triangle and pentagon identities, and the symmetric / relevant /
   semicartesian tower stacked on top), lives in
   [Category.Structure.Monoidal.Internal.Product] as [CC_Monoidal] and the
   [CC_*] family.  That file is re-exported here so that the forward direction
   has a name where readers naturally look for it; [Cartesian_Monoidal] below
   is the headline result.  A concrete use is [Instance/Coq.v], where
   [Coq_Monoidal := @CC_Monoidal Coq Coq_Cartesian Coq_Terminal].

   The *reverse* direction -- that a relevant and semicartesian monoidal
   category is itself cartesian (Fox 1976 / Heunen-Vicary) -- is the
   [CartesianMonoidal] typeclass in
   [Category.Structure.Monoidal.Heunen_Vicary]. *)

Section CartesianIsMonoidal.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(* The cartesian monoidal structure: tensor := ×, unit := 1.  This is a plain
   [Definition] rather than an [Instance] (mirroring [CC_Monoidal]): making it
   an instance would let typeclass resolution silently pick the product as
   *the* monoidal structure on every cartesian category, conflicting with
   hand-rolled monoidal structures elsewhere.  Callers select it explicitly. *)
Definition Cartesian_Monoidal : @Monoidal C := CC_Monoidal.

End CartesianIsMonoidal.
