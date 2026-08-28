(** * Models are closed under product-preserving functors *)

(* nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   nLab:      https://ncatlab.org/nlab/show/product-preserving+functor
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   A model of a Lawvere theory [T] in a cartesian category [C] is a
   finite-product-preserving functor [law_cat T ⟶ C]
   (Theory/Lawvere/Model.v).  Composing one with a further
   finite-product-preserving functor [K : C ⟶ D] gives a model in [D],
   because preservation of finite products is closed under composition.
   That is the whole content of this file, stated once at the level of
   [Model] rather than per theory or per algebraic structure.

   PRIOR ART, MEASURED.  No such closure lemma exists anywhere in the
   tree.  Theory/Lawvere/Model.v has [Record Model], the category
   [Models], and the pack/unpack bridges, and nothing that composes a
   model with a product-preserving functor; and Functor/Structure/
   Cartesian.v and Functor/Structure/Terminal.v declare
   [CartesianFunctor] and [TerminalFunctor] with NO composition
   instance for either.  Read that narrowly: the tree DOES carry
   closure-under-composition results for a NEIGHBOURING notion --
   Structure/Limit/Preservation.v's [PreservesLimitCone_compose] and
   [continuous_compose] -- and they are cited here so the sentence above
   is not read as "nothing in the tree composes preservation".  They
   concern a different class and do not supply either lemma built below.
   A name search over the whole tree for a
   composition of [CartesianFunctor] returns nothing.  The two
   composition results are therefore built here as well, and they are
   the reusable half:

     [CartesianFunctor_Compose] : [CartesianFunctor (K ◯ F)]
     [TerminalFunctor_Compose]  : [TerminalFunctor (K ◯ F)]

   They are stated for arbitrary [F : B ⟶ C] and [K : C ⟶ D], mention
   no Lawvere theory, and would sit equally well beside their donor
   classes; they live here because this file is their first consumer and
   because the brief for this work scoped the edit to a new file.

   HOW THE COMPARISONS COMPOSE.  Both are [iso_compose] of the outer
   functor's comparison with the image of the inner one under
   [fobj_iso] (Theory/Functor.v:228, which is [Defined], so its [to]
   reduces to [fmap[K] (to _)]).  For products the composite comparison
   is thus

       φ_{K◯F} = φ_K ∘ fmap[K] φ_F : K (F (x × y)) ~> K (F x) × K (F y),

   and for the terminal object, in the lax orientation
   [TerminalFunctor] uses,

       η_{K◯F} = fmap[K] η_F ∘ η_K : 1 ~> K (F 1).

   Every remaining field is then one [fmap_comp] and one associativity
   step.

   STRENGTH.  [Model_Compose_fun] records by [eq_refl] that the
   underlying functor of the composed model IS [K ◯ model_fun M] -- the
   composition is not up to isomorphism.  [Models_Compose_obj] is the
   same passage read at objects of the category [Models] via the
   existing pack/unpack bridges.

   NOT DELIVERED.  The composition is given only on OBJECTS: no functor
   [Models T C ⟶ Models T D] is built, so nothing is said about the
   action on morphisms of models (which would be left whiskering by [K])
   and no functoriality in [K] is claimed.  Neither composition instance
   is registered with [#[export] Instance] -- both are plain
   [Program Definition]s, so typeclass resolution is unperturbed; a
   consumer applies them by name.  There is no converse: nothing here
   says that if [K ◯ F] preserves finite products and [K] reflects
   isomorphisms then [F] does.  And no concrete instance is exhibited --
   the file is a conditional, like its donors.

   UNIVERSES.  All three exported results IDENTIFY the hom-and-proof
   universes of the three categories involved:
   [CartesianFunctor_Compose], [TerminalFunctor_Compose] and
   [Model_Compose] each carry [u0 = u2], [u0 = u4] and [u2 = u4] in their
   constraint blocks, over binders [B : Category@{u u0 u0}],
   [C : Category@{u1 u2 u2}], [D : Category@{u3 u4 u4}].  So a model can
   only be transported between categories sitting at the SAME hom level
   -- a real bound on what this file calls the reusable half, and one a
   consumer should know before reaching for it.  The cause is the DONOR:
   [Compose] (Theory/Functor.v) is declared
   [forall {C : Category@{u0 u3 u3}} {D : Category@{u1 u3 u3}}
            {E : Category@{u u3 u3}}], one shared hom-and-proof level
   across all three.  Nothing here adds to the identification and it is
   NOT claimed unavoidable; no re-annotated [Compose] was attempted, so
   "inherited rather than inherent" is an attribution, not a proof.  No
   [Set] appears in any block of this file.

   AXIOMS.  9/9 constants of this file are closed under the global
   context, counted by [Print Module] (which lists the [Program]
   obligations a [.glob] sweep does not) and queried by fully-qualified
   name.  This file declares no [Record], so there is no unlisted
   [Build_*] constructor to add -- unlike its sibling
   Structure/Group/Representable.v, whose count does need that
   correction. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.

Generalizable All Variables.

Section FunctorClosure.

Context {B C D : Category}.
Context `{CB : @Cartesian B}.
Context `{TB : @Terminal B}.
Context `{CC : @Cartesian C}.
Context `{TC : @Terminal C}.
Context `{CD : @Cartesian D}.
Context `{TD : @Terminal D}.

Context (F : B ⟶ C) (K : C ⟶ D).
Context (FC : @CartesianFunctor B C F CB CC).
Context (KC : @CartesianFunctor C D K CC CD).

Program Definition CartesianFunctor_Compose :
  @CartesianFunctor B D (K ◯ F) CB CD := {|
  fobj_prod_iso := fun x y =>
    iso_compose (@fobj_prod_iso C D K CC CD KC (F x) (F y))
                (fobj_iso K _ _ (@fobj_prod_iso B C F CB CC FC x y))
|}.
Next Obligation.
  rewrite (@fmap_exl B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_exl C D K CC CD KC).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite (@fmap_exr B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_exr C D K CC CD KC).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite (@fmap_fork B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_fork C D K CC CD KC).
  now rewrite comp_assoc.
Qed.

Context (FT : @TerminalFunctor B C F TB TC).
Context (KT : @TerminalFunctor C D K TC TD).

Program Definition TerminalFunctor_Compose :
  @TerminalFunctor B D (K ◯ F) TB TD := {|
  fobj_one_iso :=
    iso_compose (fobj_iso K _ _ (@fobj_one_iso B C F TB TC FT))
                (@fobj_one_iso C D K TC TD KT)
|}.
Next Obligation.
  rewrite (@fmap_one B C F TB TC FT).
  rewrite fmap_comp.
  rewrite (@fmap_one C D K TC TD KT).
  now rewrite comp_assoc.
Qed.

End FunctorClosure.

Section ModelClosure.

Context (T : LawvereTheory).
Context {C D : Category}.
Context `{CC : @Cartesian C}.
Context `{TC : @Terminal C}.
Context `{CD : @Cartesian D}.
Context `{TD : @Terminal D}.
Context (K : C ⟶ D).
Context (KC : @CartesianFunctor C D K CC CD).
Context (KT : @TerminalFunctor C D K TC TD).

Definition Model_Compose (M : @Model T C CC TC) : @Model T D CD TD :=
  {| model_fun := K ◯ @model_fun T C CC TC M
   ; model_cartesian :=
       @CartesianFunctor_Compose (@law_cat T) C D (@law_cartesian T) CC CD
         (@model_fun T C CC TC M) K (@model_cartesian T C CC TC M) KC
   ; model_terminal :=
       @TerminalFunctor_Compose (@law_cat T) C D (@law_terminal T) TC TD
         (@model_fun T C CC TC M) K (@model_terminal T C CC TC M) KT |}.

Example Model_Compose_fun (M : @Model T C CC TC) :
  @model_fun T D CD TD (Model_Compose M) = K ◯ @model_fun T C CC TC M
  := eq_refl.

Definition Models_Compose_obj (x : @Models T C CC TC) : @Models T D CD TD :=
  @Model_pack T D CD TD (Model_Compose (@Model_unpack T C CC TC x)).

End ModelClosure.

