Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * Indexed coproducts, as indexed products in the opposite category *)

(* nLab:      https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   An [A]-indexed coproduct of a family [f : A → C] is an object [p] together
   with a family of injections [inj a : f a ~> p] that is universal: every
   competing family [iota a : f a ~> c] factors through the injections by a
   unique mediating map [u : p ~> c] with [u ∘ inj a ≈ iota a] for every [a].
   That is precisely the [A]-indexed product of [f] read in [C^op], and this
   file takes it as the definition.  Two files in the tree already dualize
   this way, by two different mechanisms.  Structure/Cocartesian.v:23 states
   the idea -- "To be cocartesian is just to be cartesian in the opposite
   category" -- and realizes it with a NOTATION pair, [Notation "'Cocartesian'
   C" := (@Cartesian (C^op))] at :115 and :117.  [Comonad] instead uses a
   [Definition], [Comonad := @Monad (C^op) (M^op)] at Theory/Monad.v:144,
   with [Existing Class Comonad] declared separately in the API module at
   Comonad/Core.v:124.  This file follows the second, splitting [Definition]
   from [Existing Class] in exactly that way; see below for why.

   WHAT IS NEW HERE AND WHAT IS NOT.  No constant below carries a proof
   obligation.  Each is a definitional re-reading, at [C^op], of a constant of
   Structure/Limit/Product.v:

     [IsIndexedCoproduct f p inj]    is  [@IsIndexedProduct (C^op) A f p inj]
     [icoprod f L]                   is  [@iprod (C^op) A f L]
     [icoprod_inj f L]               is  [@iprod_proj (C^op) A f L]
     [icoprod_ump f L]               is  [@iprod_ump (C^op) A f L]
     [colimit_is_indexed_coproduct]  is  [@limit_is_indexed_product (C^op)]
     [HasIndexedCoproducts C]        is  [@HasIndexedProducts (C^op)]

   What the file adds is the covariant reading.  [icoprod_desc] and the three
   [indexed_coproduct*] accessors state the universal property with arrows in
   [C] rather than [C^op]; [Build_IsIndexedCoproduct] and
   [Build_HasIndexedCoproducts] let a caller supply the data in that same
   covariant form.  Each is its product counterpart applied at [C^op] with no
   step beyond [C^op]'s definitional unfolding of [hom], [compose] and
   [homset] (Construction/Opposite.v).

   [HasIndexedCoproducts] is a [Definition] with [Existing Class] declared
   immediately after, rather than a [Class] of its own.  Typeclass resolution
   keys on the head constant of a goal and does not look through the
   unfolding, so without the declaration a coproduct witness in scope would
   not be found for the implicit argument of the accessors below.  That is
   the reasoning recorded at Comonad/Core.v:110-124 for [Comonad], the
   [Definition]-plus-[Existing Class] precedent this file follows.  (One
   difference: [Comonad]'s two halves are deliberately kept in separate files,
   the definition in Theory/Monad.v and the class declaration in the API
   module, so that library-wide class resolution is not imposed on the bare
   definition.  Here there is only one file, so both sit together.)

   COLIMIT PRESENTATION.  [icoprod] and its companions read a [Limit] of the
   discrete diagram taken IN [C^op], namely
   [Limit (@DiscreteCat_Functor A (C^op) f)] -- not a [Colimit] in the sense
   of Structure/Limit.v:158, which sets [Colimit F := Limit (F^op)] and so
   indexes over [(DiscreteCat A)^op].  The hom from [x] to [y] is [x = y] in
   [DiscreteCat A] (Instance/Discrete.v:39) and [y = x] in its opposite
   (Construction/Opposite.v), and Coq does not identify the two categories:
   [eq_refl : (DiscreteCat A)^op = DiscreteCat A] is rejected, "cannot unify".
   (Checked outside the tree, so that the [make todo] scan stays clean.)  A
   translation between the two shapes is not given here, and no consumer in
   this development calls for one.

   STATUS: axiom-free, and free of new proof: the first inhabitant is
   [Sets_HasIndexedCoproducts] in Instance/Sets/Products.v, audited by the
   Makefile's [print-assumptions] target.  No finiteness is assumed -- [A] is
   an arbitrary [Type] -- but the ambient category may constrain the universe
   [A] lives at; see the header of Instance/Sets/Products.v for exactly what
   that constraint comes to at [Sets]. *)

Definition IsIndexedCoproduct {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) : Type :=
  @IsIndexedProduct (C^op) A f p inj.

Definition icoprod_desc {C : Category} {A : Type} {f : A → C} {p : C}
  {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj)
  {c : C} (iota : ∀ a : A, f a ~> c) :
  ∃! u : p ~> c, ∀ a : A, u ∘ inj a ≈ iota a :=
  @iprod_desc (C^op) A f p inj H c iota.

Definition Build_IsIndexedCoproduct {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p)
  (desc : ∀ (c : C) (iota : ∀ a : A, f a ~> c),
            ∃! u : p ~> c, ∀ a : A, u ∘ inj a ≈ iota a) :
  IsIndexedCoproduct f p inj :=
  @Build_IsIndexedProduct (C^op) A f p inj desc.

Definition icoprod {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) : C :=
  @iprod (C^op) A f L.

Definition icoprod_inj {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) (a : A) : f a ~> icoprod f L :=
  @iprod_proj (C^op) A f L a.

Definition icoprod_ump {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f))
  (c : C) (iota : ∀ a : A, f a ~> c) :
  ∃! u : icoprod f L ~> c, ∀ a : A, u ∘ icoprod_inj f L a ≈ iota a :=
  @iprod_ump (C^op) A f L c iota.

Definition colimit_is_indexed_coproduct {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) :
  IsIndexedCoproduct f (icoprod f L) (icoprod_inj f L) :=
  @limit_is_indexed_product (C^op) A f L.

Definition HasIndexedCoproducts (C : Category) : Type :=
  @HasIndexedProducts (C^op).

Existing Class HasIndexedCoproducts.

Definition Build_HasIndexedCoproducts {C : Category}
  (cobj : ∀ A : Type, (A → C) → C)
  (cinj : ∀ (A : Type) (f : A → C) (a : A), f a ~> cobj A f)
  (cump : ∀ (A : Type) (f : A → C),
            IsIndexedCoproduct f (cobj A f) (cinj A f)) :
  HasIndexedCoproducts C :=
  @Build_HasIndexedProducts (C^op) cobj cinj cump.

Section IndexedCoproductAPI.

Context {C : Category}.
Context {H : HasIndexedCoproducts C}.

Definition indexed_coproduct {A : Type} (f : A → C) : C :=
  @indexed_product (C^op) H A f.

Definition indexed_coproduct_inj {A : Type} (f : A → C) (a : A) :
  f a ~> indexed_coproduct f :=
  @indexed_product_proj (C^op) H A f a.

Definition indexed_coproduct_ump {A : Type} (f : A → C) :
  IsIndexedCoproduct f (indexed_coproduct f) (indexed_coproduct_inj f) :=
  @indexed_product_ump (C^op) H A f.

End IndexedCoproductAPI.
