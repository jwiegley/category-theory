Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Lawvere.

Generalizable All Variables.

(** * Models of a Lawvere theory *)

(* nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   A model (or algebra) of a Lawvere theory [T] in a cartesian category [C]
   is a finite-product-preserving functor [law_cat T ⟶ C].  In this library
   product preservation splits into two separate concerns, mirroring the
   nullary/binary split of finite products themselves:

     - [CartesianFunctor] (Functor/Structure/Cartesian.v): the binary
       comparison F (x × y) ≅ F x × F y is an isomorphism;
     - [TerminalFunctor] (Functor/Structure/Terminal.v): the nullary
       comparison 1 ≅ F 1 is an isomorphism.

   [Model] bundles a functor with both preservation witnesses.

   Morphisms of models are ALL natural transformations between the
   underlying functors — no compatibility condition is imposed, because
   product preservation is property-like structure on the objects, not on
   the morphisms.  Accordingly the category of models [Models T C] is the
   FULL subcategory of the functor category [law_cat T, C] on the
   product-preserving functors, built with Construction/Subcategory.v
   exactly as Construction/Localization.v builds the full subcategory of
   W-local objects: [sobj] selects the preservation witnesses and [shom]
   retains every morphism ([True]). *)

Section Model.

Context (T : LawvereTheory).
Context (C : Category).
Context `{@Cartesian C}.
Context `{@Terminal C}.

Record Model := {
  model_fun : @law_cat T ⟶ C;

  model_cartesian :
    @CartesianFunctor (@law_cat T) C model_fun (@law_cartesian T) _;

  model_terminal :
    @TerminalFunctor (@law_cat T) C model_fun (@law_terminal T) _
}.

(** ** The category of models

    The full subcategory of the functor category [law_cat T, C] whose
    objects carry both preservation witnesses.  [shom] retains every
    natural transformation ([True]), so closure under identity and
    composition is trivial ([I]) — the same shape as [C_W] in
    Construction/Localization.v. *)

Definition Models_sub : Subcategory (@Fun (@law_cat T) C) :=
  @Build_Subcategory (@Fun (@law_cat T) C)
    (fun F : @law_cat T ⟶ C =>
       (@CartesianFunctor (@law_cat T) C F (@law_cartesian T) _ *
        @TerminalFunctor (@law_cat T) C F (@law_terminal T) _)%type)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Models : Category := Sub (@Fun (@law_cat T) C) Models_sub.

(** ** Bridges between the record and subcategory presentations

    A [Model] packs into an object of [Models], and every object of
    [Models] unpacks to a [Model]; the two presentations carry exactly
    the same data. *)

Definition Model_pack (M : Model) : Models :=
  (model_fun M; (model_cartesian M, model_terminal M)).

Definition Model_unpack (x : Models) : Model :=
  {| model_fun       := `1 x
   ; model_cartesian := fst `2 x
   ; model_terminal  := snd `2 x |}.

(** The two presentations are mutually inverse on the nose: each round
    trip is an eta-expansion, discharged by case analysis.  (Propositional
    [=] on the packed OBJECT data — the sanctioned case; no morphism
    equality is asserted.) *)

Lemma Model_unpack_pack (M : Model) : Model_unpack (Model_pack M) = M.
Proof. destruct M; reflexivity. Qed.

Lemma Model_pack_unpack (x : Models) : Model_pack (Model_unpack x) = x.
Proof. destruct x as [F [HC HT]]; reflexivity. Qed.

(** ** Morphisms of models are all natural transformations

    [Models_sub] is a full subcategory: every natural transformation
    between the underlying functors of two models is a morphism of
    models (the [shom] witness is [I]). *)

Definition Models_Full :
  Construction.Subcategory.Full (@Fun (@law_cat T) C) Models_sub :=
  fun _ _ _ _ _ => I.

(** Concretely: any natural transformation between the underlying
    functors of two models lifts to a morphism in [Models], and it is
    sent back to itself by the (faithful) inclusion. *)

Definition Model_hom_of_transform (x y : Models) (f : `1 x ⟹ `1 y) :
  x ~{ Models }~> y := (f; I).

Lemma Model_hom_of_transform_incl (x y : Models) (f : `1 x ⟹ `1 y) :
  fmap[Incl _ Models_sub] (Model_hom_of_transform x y f)
    ≈ (f : `1 x ~{ @Fun (@law_cat T) C }~> `1 y).
Proof. simpl; intros; reflexivity. Qed.

End Model.
