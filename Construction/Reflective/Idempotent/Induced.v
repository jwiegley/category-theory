Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Construction.Reflective.FixedPoints.

Generalizable All Variables.

(** * The reflection of an idempotent monad induces that monad *)

(* nLab: https://ncatlab.org/nlab/show/idempotent+monad
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, SS VI.2, Theorem 1, printed pp. 140-141
   Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
         SS 10.2, printed p. 271

   Construction/Reflective/Idempotent.v proves that an idempotent monad M
   reflects C onto its M-local objects, those x at which ret x is
   invertible: [idem_reflective_adj] is the adjunction
   [idem_reflector ⊣ Incl C MLocal_Subcategory].  Its converse there,
   [Reflective_Monad] with [Reflective_IdempotentMonad], goes from a
   reflection to a monad.  What it does not state is that the two meet:
   that the monad induced by the reflection BUILT FROM M is M again.
   This file states it, as the triple the tree already uses for the other
   two resolutions of a monad, Monad/Eilenberg/Moore/Adjunction.v's
   [EM_unit_agrees], [EM_join_agrees], [EM_Monad_agrees] and
   Monad/Kleisli/Adjunction.v's [Kleisli_*_agrees]:
     - [idem_unit_agrees]: the induced unit is ret;
     - [idem_join_agrees]: the induced multiplication is join;
     - [idem_Monad_agrees]: the composite [Incl ◯ idem_reflector] is M,
       as functors, with identity components.
   The dual is the same three lemmas at C^op, the tree's duality
   discipline: the coreflection of an idempotent comonad, the adjunction
   of Construction/Reflective/FixedPoints.v's [Idempotent_Coreflective],
   induces that comonad ([idem_counit_agrees], [idem_comult_agrees],
   [idem_Comonad_agrees]), with no law proved again.
   The induced monad is Monad/Comparison.v's [Adjunction_Induced_Monad],
   whose ret and join are the adjunction's unit and the image of its
   counit, transparently.

   For the Eilenberg-Moore resolution Mac Lane states this as part of
   Theorem 1 (p. 140): "The monad defined in X by this adjunction is the
   given monad", checked on p. 141 as "The endofunctor G^T F^T is the
   original T, its unit η^T is the original unit, and its multiplication
   ... is the original multiplication of T."  For the fixed-point reflection
   of a monad on a poset Awodey builds the adjunction on p. 271 (with
   T = i ∘ t and t ⊣ i) without saying in words that it induces T; the
   order-theoretic instance of this file, where that is read back, is
   Instance/Proset/Monad/Awodey.v, and the instance at a preorder is
   Instance/Proset/Monad.v's [proset_fixed_adj].  This file is a
   satellite rather than an addition to Idempotent.v so that the donor,
   whose closure the index records, is not edited.

   STRENGTHS, measured.  On objects and on arrows the composite IS M by
   [eq_refl] ([idem_factorisation_obj], [idem_factorisation_fmap]).  The
   unit and multiplication agree at ≈
   and not by conversion: [cbn] and [cbv] both reduce the induced unit at
   x to [id ∘ ret x] and the induced multiplication at x to
   [join x ∘ fmap[M] id], with no opaque constant left in the normal
   form.  The identities are Theory/Adjunction.v's definitions of the
   unit and counit as transposes of identities ([unit := ⌊id⌋]), read
   through the bijection of [Adjunction_from_Transform]
   (Adjunction/Natural/Transformation/Universal.v), whose transpose of f
   is [fmap f ∘ unit].  So no [Qed] in the donors is what stands in the way;
   the gap is exactly the laws [id_left] and [fmap_id], which in an
   arbitrary C hold at ≈ only.  [eq_refl] for either component is
   refused by conversion ([cannot unify]), and so is the functor
   equation [Incl ◯ idem_reflector = M].  For the functor equation, fobj
   and fmap agree by eq_refl and the refusal is in the law fields alone,
   stuck projections of a variable M.  In a thin category every one
   of these ≈ is trivial, which is the situation of
   Instance/Proset/Monad.v.

   UNIVERSES, read off [About].  [idem_unit_agrees], [idem_join_agrees]
   and their duals [idem_counit_agrees], [idem_comult_agrees] bind
   [@{o h d s a}], the others [@{o h d s}], with [C : Category@{o h h}]
   as in every constant of Idempotent.v.
   [d] is the object level of the subcategory [Sub] ([o <= d],
   [h <= d]); [s] carries the one strict bound [h < s].  Its first
   carrier in dependency order is Theory/Functor.v's [Compose]
   ([u3 < u2]), through the composite [Incl ◯ idem_reflector] that every
   statement mentions; Construction/Subcategory.v's [Sub] introduces the
   same kind of bound in its own block (while [Setoid] and [Category]
   carry none), and for the unit and the multiplication so does
   Instance/Sets.v's [Sets] ([o < so]), where the hom-setoid isomorphism
   of [Adjunction] lives.  All are unified into [s].  [a] is a level of
   [idem_reflective_adj] that is free in that constant's block and
   occurs in the statement through its instance.  The stdlib caps
   [o <= Projections.u0, h <= Projections.u0, h <= Projections.u1] come
   from [Sub] and [Incl], and the unit and multiplication lemmas and
   their duals add [h <= compose.u0, compose.u1, compose.u2, ID.u0],
   first carried by [Sets] through [Adjunction] ([Sets@{o so}] has them
   at its level o).  In the duals the type level of FixedPoints.v's
   [IdempotentComonad] is unified with [d].  No constant carries [Set].

   NOT DELIVERED.  The three facts are not packaged as one isomorphism
   of monads; the tree has no record of monad morphisms to package them
   in.  The dual is stated only as the C^op instance of the three
   lemmas: [idem_Comonad_agrees] compares functors on C^op, as
   FixedPoints.v's [Coreflective_IdempotentMonad_op] does, and is not
   transported to C; and it is not stated through Comonad/Duality.v's
   [Adjunction_Comonad], which is built through the opaque
   [Adjunction_Monad], so that its extract does not reduce
   (Construction/Reflective/FixedPoints.v records the same obstacle). *)

(* The unit of the induced monad is ret.  It reduces to [id ∘ ret x]. *)
Lemma idem_unit_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  @ret C _ (Adjunction_Induced_Monad
              (@idem_reflective_adj@{o h d a h s} C M MM IM)) x
    ≈ @ret C M MM x.
Proof. cbn. apply id_left. Qed.

(* The multiplication of the induced monad is join.  It reduces to
   [join x ∘ fmap[M] id]. *)
Lemma idem_join_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  @join C _ (Adjunction_Induced_Monad
               (@idem_reflective_adj@{o h d a h s} C M MM IM)) x
    ≈ @join C M MM x.
Proof. cbn. rewrite fmap_id. apply id_right. Qed.

(* The composite of the reflection is M, with identity components. *)
Theorem idem_Monad_agrees@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} :
  Incl C (@MLocal_Subcategory C M MM)
    ◯ @idem_reflector@{o h d h h s} C M MM IM ≈ M.
Proof. exists (fun x => iso_id). intros x y f; cbn. cat. Qed.

(* ...and on objects it is M on the nose. *)
Example idem_factorisation_obj@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  fobj[Incl C (@MLocal_Subcategory C M MM)
         ◯ @idem_reflector@{o h d h h s} C M MM IM] x = M x := eq_refl.

(* ...and on arrows: the functor equation is refused in the law fields
   alone. *)
Example idem_factorisation_fmap@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} {x y : C}
  (f : x ~> y) :
  fmap[Incl C (@MLocal_Subcategory C M MM)
         ◯ @idem_reflector@{o h d h h s} C M MM IM] f = fmap[M] f := eq_refl.

(** ** The dual, as the three lemmas at C^op *)

(* The counit of the comonad induced by the coreflection is extract. *)
Definition idem_counit_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} (x : C) :
  @ret (C^op) _ (Adjunction_Induced_Monad
                   (@idem_reflective_adj@{o h d a h s} (C^op) (W^op) H IH)) x
    ≈ @extract C W H x :=
  @idem_unit_agrees@{o h d s a} (C^op) (W^op) H IH x.

(* Its comultiplication is duplicate. *)
Definition idem_comult_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} (x : C) :
  @join (C^op) _ (Adjunction_Induced_Monad
                    (@idem_reflective_adj@{o h d a h s} (C^op) (W^op) H IH)) x
    ≈ @duplicate C W H x :=
  @idem_join_agrees@{o h d s a} (C^op) (W^op) H IH x.

(* The composite of the coreflection is W^op, with identity components. *)
Definition idem_Comonad_agrees@{o h d s | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} :
  Incl (C^op) (@MLocal_Subcategory (C^op) (W^op) H)
    ◯ @idem_reflector@{o h d h h s} (C^op) (W^op) H IH ≈ W^op :=
  @idem_Monad_agrees@{o h d s} (C^op) (W^op) H IH.
