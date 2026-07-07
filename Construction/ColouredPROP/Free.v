Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * The free coloured-PROP category on a signature *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Free_category

   A coloured PROP over a set [Colour] of wire types is a strict
   symmetric monoidal category whose objects are the finite words
   [list Colour] and whose tensor on objects is concatenation.  The
   free coloured PROP on a signature [S] has as its [cs ~> ds] arrows
   the typed string-diagram terms [CTerm S cs ds] quotiented by the
   laws of a strict symmetric monoidal category; this is the standard
   "free = syntactic" construction, the many-sorted analogue of
   [Construction/PROP/Free.v], with [list Colour] replacing [nat] and
   [++] replacing [Nat.add] throughout.

   This file assembles the underlying [Category] layer of that
   quotient together with its tensor bifunctor:

     - obj        := list Colour                (objects: colour words)
     - hom cs ds  := CTerm S cs ds mod CTermEq  (typed diagrams / ≈)
     - id         := CT_id                      (identity wires)
     - compose    := CT_comp                    (sequential composition)
     - tensor     := CFreeCat_Tensor            (parallel composition)

   The hom-equivalence ≈ is [CTermEq S], so the [Category] laws
   (left/right unit, associativity) are exactly its [CTE_id_left] /
   [CTE_id_right] / [CTE_assoc] constructors, and [compose_respects]
   is its [CTE_comp_cong] congruence.  The [Monoidal],
   [SymmetricMonoidal], and strictness layers — which complete
   [CFreeCat S] to a free strict symmetric monoidal category and then
   to the first inhabitant of [Construction/ColouredPROP.v]'s class —
   live in the successor files ([Construction/ColouredPROP/Cast.v],
   [Monoidal.v], [Braided.v], [Instance.v]).

   Layout note: this file merges the one-sorted spine's donor pair
   [Construction/PROP/Free.v] + [Construction/PROP/Tensor.v].  The
   coloured tensor bifunctor needs nothing beyond the [CTE_tens_*]
   constructors already provided by the equational theory, so it
   lives here rather than in a file of its own.

   Following the coloured spine's proof-using discipline, the
   inductives ([CTerm], [CTermEq]) were declared in sections that
   closed in their home files; every statement below carries the
   signature [S] explicitly. *)

Section CFreeCategory.

Context {Colour : Type}.
Context (S : CSignature Colour).

(** The hom-setoid: terms are quotiented by [CTermEq]. *)
#[export] Program Instance CTerm_Setoid {cs ds : list Colour} :
  Setoid (CTerm S cs ds) := {|
  equiv := @CTermEq Colour S cs ds
|}.
Next Obligation.
  constructor.
  - intros t; apply CTE_refl.
  - intros s t; apply CTE_sym.
  - intros s t u; apply CTE_trans.
Defined.

(** Composition is the [CT_comp] constructor; it respects [CTermEq] by
    [CTE_comp_cong]. *)
#[export] Program Instance CT_comp_respects {cs ds es : list Colour} :
  Proper (equiv ==> equiv ==> equiv) (@CT_comp Colour S cs ds es).
Next Obligation.
  proper.
  apply CTE_comp_cong; assumption.
Qed.

(** Tensor (parallel composition) is also Proper for [CTermEq], by
    [CTE_tens_cong].  Allows [rewrite] under [CT_tens]. *)
#[export] Program Instance CT_tens_respects
  {cs1 ds1 cs2 ds2 : list Colour} :
  Proper (equiv ==> equiv ==> equiv) (@CT_tens Colour S cs1 ds1 cs2 ds2).
Next Obligation.
  proper.
  apply CTE_tens_cong; assumption.
Qed.

(** The free category on [S]. *)
Program Definition CFreeCat : Category := {|
  obj      := list Colour;
  hom      := @CTerm Colour S;
  homset   := @CTerm_Setoid;
  id       := CT_id;
  compose  := @CT_comp Colour S;
  compose_respects := @CT_comp_respects;
  id_left  := fun cs ds f => CTE_id_left f;
  id_right := fun cs ds f => CTE_id_right f;
  comp_assoc := fun cs ds es fs f g h => CTE_sym _ _ (CTE_assoc f g h);
  comp_assoc_sym := fun cs ds es fs f g h => CTE_assoc f g h
|}.

End CFreeCategory.

Arguments CFreeCat {Colour} S : assert.
Arguments CT_comp_respects {Colour S cs ds es}.
Arguments CT_tens_respects {Colour S cs1 ds1 cs2 ds2}.

(** * Parallel-composition bifunctor on CFreeCat *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   The monoidal product of a (strict, symmetric) monoidal category is
   a bifunctor [⊗ : C ∏ C ⟶ C].  For the free coloured PROP
   [CFreeCat S] this is the parallel composition of typed string
   diagrams, with boundaries given by concatenation:

     - on objects:    [(cs, ds) ↦ cs ++ ds]  (tensor on objects is [++])
     - on morphisms:  [(f, g) ↦ CT_tens f g], so [f : cs1 ~> ds1] and
                       [g : cs2 ~> ds2] yield
                       [f ⊗ g : cs1 ++ cs2 ~> ds1 ++ ds2]

   The bifunctor laws (a functor out of the product category
   [CFreeCat S ∏ CFreeCat S]) follow from the [CTE_tens_*]
   constructors of the [CTermEq] quotient relation:
     - respectfulness (fmap_respects):  [CTE_tens_cong]
     - identity preservation (fmap_id): [CTE_tens_id]
         [id_cs ⊗ id_ds ≈ id_(cs ++ ds)]
     - composition preservation (fmap_comp), i.e. the middle-four
       interchange [(f1 ⊙c f2) ⊗ (g1 ⊙c g2) ≈ (f1 ⊗ g1) ⊙c (f2 ⊗ g2)]:
       [CTE_interchange] (used via [CTE_sym], since the constructor
       states the reverse orientation). *)

Section CFreeTensor.

Context {Colour : Type}.
Context (S : CSignature Colour).

(** The tensor bifunctor on [CFreeCat S]. *)
Program Definition CFreeCat_Tensor :
  CFreeCat S ∏ CFreeCat S ⟶ CFreeCat S := {|
  fobj := fun p => (fst p ++ snd p)%list;
  fmap := fun p q m =>
    @CT_tens Colour S (fst p) (fst q) (snd p) (snd q) (fst m) (snd m)
|}.
Next Obligation.
  unfold Proper, respectful.
  intros [f1 f2] [g1 g2] [Hf Hg]; simpl in *.
  apply CTE_tens_cong; assumption.
Qed.
Next Obligation.
  apply CTE_tens_id.
Qed.
Next Obligation.
  apply CTE_sym, CTE_interchange.
Qed.

End CFreeTensor.

Arguments CFreeCat_Tensor {Colour} S : assert.
