Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Structure.Thin.

Generalizable All Variables.

(** * Monads and comonads in a thin category *)

(* nLab: https://ncatlab.org/nlab/show/closure+operator
   nLab: https://ncatlab.org/nlab/show/idempotent+monad
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, SS VI.1, printed p. 139
   Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
         SS 10.2, Example 10.4, printed p. 270
   Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
         SS 1.4.4, Example 1.122, printed p. 34
   Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,
         Example 5.1.7, printed p. 186

   Mac Lane asks on p. 139 "What is a monad in a preorder P?", and answers
   that the unit and multiplication exist "precisely when x ≤ Tx,
   T(Tx) ≤ Tx" (his display (3)), "the diagrams (2) then necessarily
   commute because in a preorder there is at most one arrow from here to
   yonder".  The argument uses nothing about a preorder beyond that last
   clause, so this file states it for ANY thin category in the sense of
   Structure/Thin.v's [Thin]: [thin_monad] builds a monad from an
   endofunctor and the two arrow families alone, and each of the five
   monad laws is one appeal to thinness.

   Mac Lane goes on: "The first equation of (3) gives Tx ≤ T(Tx)", the
   unit at Tx, and in a partial order he concludes T(Tx) = Tx.  Awodey's
   Example 10.4 (p. 270) makes the same step for a poset: "A monad on P is
   a monotone function T : P → P with x ≤ Tx and T²x ≤ Tx.  But then
   T² = T, i.e. T is idempotent."  Without antisymmetry the conclusion is
   an isomorphism, and that is [thin_join_IsIso]: the inverse of join at
   x is ret at M x, and both inverse laws are thinness.  Packaged,
   [thin_IdempotentMonad] says that EVERY monad on a thin category is an
   [IdempotentMonad] in the sense of Construction/Reflective/Idempotent.v.
   That file takes the class as a hypothesis; here it is derived, and the
   derivation is one of the two pieces of #463 with no earlier in-tree
   counterpart (the other is Construction/Reflective/Idempotent/Induced.v,
   the monad induced by the idempotent reflection being the original
   one).  [thin_talgebra_iff] is Mac Lane's reading of the algebras
   on p. 141, "a T-algebra is then an x ∈ P with Tx ≤ x": an algebra in a
   thin category is exactly an arrow T x ~> x.

   THE DUALS, BY DUALITY.  Riehl's Example 5.1.7 (p. 186) adds: "Dually,
   a comonad on a poset category (P, ≤) defines a kernel operator: an
   order-preserving function K so that Kp ≤ p and Kp = K²p."  Nothing on
   the comonad side is proved again.  Theory/Monad.v defines [Comonad] as
   [@Monad (C^op) (W^op)] and Construction/Opposite.v sets hom[C^op] x y
   to hom[C] y x, so each dual below is the monad-side constant at C^op,
   fed Structure/Thin.v's [Thin_Opposite]:
     - [thin_comonad] is [thin_monad] at C^op, typed by conversion;
     - [thin_IdempotentComonad] is [thin_IdempotentMonad] at C^op, and
       lands in Construction/Reflective/FixedPoints.v's
       [IdempotentComonad];
     - [thin_wcoalgebra_iff] is [thin_talgebra_iff] at C^op, read through
       Comonad/Coalgebra.v's bridges [WCoalgebra_to_TAlgebra] and
       [TAlgebra_to_WCoalgebra];
     - [thin_coreflective] is FixedPoints.v's [Idempotent_Coreflective] at
       the thin witness: the coreflection onto the objects where the
       counit is invertible, the dual of Seven Sketches Example 1.122's
       adjunction between a closure operator and the inclusion of its
       fixed points.
   The order-theoretic consumers are Instance/Proset/Monad.v, where a
   monad on a preorder is shown to be a closure operator,
   Instance/Props/Modal.v, the modal operator B ⇒ − on propositions, and,
   for the duals, Instance/Proset/Monad/Interior.v, where a comonad on a
   preorder is shown to be an interior operator, with its instance at the
   subsets of a space in Instance/Top/Interior.v.

   STRENGTHS.  [thin_monad]'s ret and join are the given families by
   [eq_refl] ([thin_monad_ret], [thin_monad_join]), and so are the
   extract and duplicate of [thin_comonad] ([thin_comonad_extract],
   [thin_comonad_duplicate]): the comonad is the monad at C^op on the
   nose, with no transport.  The algebra and coalgebra structure maps
   round-trip by [eq_refl] ([thin_talgebra_round],
   [thin_wcoalgebra_round]).  What is NOT on the nose is the comparison
   of [thin_monad] with a monad [MM] that has the same ret and join:
   [thin_monad TC T ret join = MM] is refused by conversion, because the
   law fields of a variable monad are stuck projections while those of
   [thin_monad] are appeals to [TC].  Any two such monads agree
   componentwise, at the hom-setoid's ≈, which in a thin category is the
   only comparison there is.

   UNIVERSES, read off [About].  Every constant binds [@{t o h}] with
   [C : Category@{o h h}]; hom and proof are identified because
   Structure/Thin.v's [Thin@{t o h}] accepts only [Category@{o h h}], and
   the block [o <= t, h <= t] is [Thin]'s own.  [thin_coreflective] adds
   two levels [s f] with the strict bound [h < s].  [Coreflective] reaches
   two donors that introduce such a bound in their own blocks, and neither
   file requires the other: Construction/Subcategory.v's [Sub], the
   codomain of [Reflective]'s reflector, and Instance/Sets.v's [Sets]
   ([o < so]), where the hom-setoid isomorphism of [Adjunction] lives.
   The two are unified into [s].  The same two donors bring the stdlib
   caps [h <= compose.u0, compose.u1, compose.u2, ID.u0] (first carried
   by [Sets], whose own block has them at its level o) and
   [o <= Projections.u0, h <= Projections.u0, h <= Projections.u1]
   (from [Sub] and [Incl]).  The level [f] is [Coreflective]'s own u3,
   which occurs in neither the type nor the constraint block of
   Construction/Reflective.v's [Coreflective] (measured by [About]); it
   is named here so that it is not a level of the body alone.
   [thin_wcoalgebra_iff] destructures
   the pair of [thin_talgebra_iff] with [let] instead of applying [fst]
   and [snd]: the projections add the stdlib caps
   [h <= projections.u0, h <= projections.u1] (measured), and
   destructuring adds nothing.  No constant carries [Set].  [Thin] is
   declared twice in the tree (here in Structure/Thin.v, and again in
   Instance/Proset/Galois.v); this file imports only the first.

   NOT DELIVERED.  No thin-category statement for a category whose hom
   and proof universes differ, since [Thin] cannot express one.  No
   monad-side [thin_reflective]: it would be [Idempotent_Reflective] at
   [thin_IdempotentMonad], and the one consumer, Instance/Proset/Monad.v,
   uses the reflection adjunction [idem_reflective_adj] directly.  No
   lemma that a monad on a thin category is determined by its functor,
   although it is true at ≈ by the argument above. *)

(** ** Monads in a thin category *)

(* Mac Lane's display (3) in any thin category: an endofunctor with a
   unit family and a multiplication family IS a monad.  Each law is an
   equation between parallel arrows, hence one appeal to [TC]. *)
Definition thin_monad@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x) :
  @Monad C T :=
  @Build_Monad C T u m
    (fun _ _ _ => TC _ _ _ _) (fun _ => TC _ _ _ _) (fun _ => TC _ _ _ _)
    (fun _ => TC _ _ _ _) (fun _ _ _ => TC _ _ _ _).

(* The unit and multiplication are the given families, on the nose. *)
Example thin_monad_ret@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x)
  (x : C) : @ret C T (thin_monad TC T u m) x = u x := eq_refl.

Example thin_monad_join@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x)
  (x : C) : @join C T (thin_monad TC T u m) x = m x := eq_refl.

(* Mac Lane p. 141: an algebra is exactly its structure map T x ~> x;
   both algebra laws are thinness. *)
Definition thin_talgebra_iff@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {T : C ⟶ C} {MM : @Monad C T} (x : C) :
  @TAlgebra C T MM x ↔ (T x ~> x) :=
  (fun a => @t_alg C T MM x a,
   fun h => @Build_TAlgebra C T MM x h (TC _ _ _ _) (TC _ _ _ _)).

Example thin_talgebra_round@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {T : C ⟶ C} {MM : @Monad C T} (x : C)
  (h : T x ~> x) :
  match thin_talgebra_iff TC (MM := MM) x with
  | (to_arrow, of_arrow) => to_arrow (of_arrow h)
  end = h := eq_refl.

(* Idempotency from thinness.  The inverse of join at x is ret at M x
   (Mac Lane's "Tx ≤ T(Tx)"), and both composites are endomorphisms,
   hence identities. *)
Definition thin_join_IsIso@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {M : C ⟶ C} {MM : @Monad C M} (x : C) :
  IsIsomorphism (@join C M MM x) :=
  {| two_sided_inverse := @ret C M MM (M x)
   ; is_right_inverse  := TC _ _ _ _
   ; is_left_inverse   := TC _ _ _ _ |}.

Definition thin_IdempotentMonad@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {M : C ⟶ C} {MM : @Monad C M} :
  @IdempotentMonad C M MM :=
  {| idem_join_iso := thin_join_IsIso TC |}.

(** ** The duals, as the monad constants at C^op *)

(* The interior data: a counit W x ~> x and a comultiplication
   W x ~> W (W x).  At C^op these ARE the unit and multiplication
   families, by conversion. *)
Definition thin_comonad@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (W : C ⟶ C) (e : ∀ x : C, W x ~> x) (d : ∀ x : C, W x ~> W (W x)) :
  @Comonad C W :=
  thin_monad (Thin_Opposite TC) (W^op) e d.

(* The comonad is the monad at C^op on the nose. *)
Example thin_comonad_extract@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) (W : C ⟶ C) (e : ∀ x : C, W x ~> x)
  (d : ∀ x : C, W x ~> W (W x)) (x : C) :
  @extract C W (thin_comonad TC W e d) x = e x := eq_refl.

Example thin_comonad_duplicate@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) (W : C ⟶ C) (e : ∀ x : C, W x ~> x)
  (d : ∀ x : C, W x ~> W (W x)) (x : C) :
  @duplicate C W (thin_comonad TC W e d) x = d x := eq_refl.

(* Every comonad on a thin category is idempotent: the monad-side
   constant at C^op. *)
Definition thin_IdempotentComonad@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} :
  IdempotentComonad W H :=
  @thin_IdempotentMonad (C^op) (Thin_Opposite TC) (W^op) H.

(* A coalgebra is exactly an arrow x ~> W x: [thin_talgebra_iff] at C^op,
   read through the bridges of Comonad/Coalgebra.v. *)
Definition thin_wcoalgebra_iff@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} (x : C) :
  @WCoalgebra C W H x ↔ (x ~> W x) :=
  let (to_arrow, of_arrow) :=
    thin_talgebra_iff (Thin_Opposite TC) (MM := H) x in
  (fun c => to_arrow (WCoalgebra_to_TAlgebra c),
   fun h => TAlgebra_to_WCoalgebra (of_arrow h)).

Example thin_wcoalgebra_round@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} (x : C)
  (h : x ~> W x) :
  match thin_wcoalgebra_iff TC (H := H) x with
  | (to_arrow, of_arrow) => to_arrow (of_arrow h)
  end = h := eq_refl.

(* The inclusion of the counit-fixed objects is coreflective: the dual
   of the reflection onto the closed elements. *)
Definition thin_coreflective@{t o h s f | h < s +} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} :
  Coreflective@{t t s t f h o h} (WLocal_Subcategory H) :=
  Idempotent_Coreflective H (thin_IdempotentComonad TC).
