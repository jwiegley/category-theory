Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Pseudofunctor.

Generalizable All Variables.

(** Lax and oplax transformations between pseudofunctors. *)

(* nLab: https://ncatlab.org/nlab/show/lax+natural+transformation
   nLab: https://ncatlab.org/nlab/show/pseudonatural+transformation
   Reference: Johnson–Yau, "2-Dimensional Categories", Definition 4.2.1.

   Given two pseudofunctors F, G : B ⟶ B' between bicategories, a *lax
   transformation* α : F ⟹ G consists of

     - a component 1-cell   α_x : F x ~~> G x            for each 0-cell x, and
     - a naturator 2-cell   α_f : G f ∘∘∘ α_x ⟹ α_y ∘∘∘ F f
                                                          for each 1-cell f : x ~~> y,

   subject to three coherence axioms: the naturator is natural in f (respects
   2-cells), and it is compatible with the identities and with horizontal
   composition (the unit and composition laws below).

   Orientation.  We take the standard nLab *lax* orientation, where the
   naturator points

       lt1 f : pf1[G] f ∘∘∘ lt0 x  ⟹  lt0 y ∘∘∘ pf1[F] f,

   i.e. across the naturality square with F f on top, G f on the bottom, the
   component 1-cells on the sides, the 2-cell goes from the left-then-bottom
   composite to the top-then-right composite.  The *oplax* variant reverses
   every naturator; it is written out in full as [OplaxTransformation] below
   (there is as yet no in-tree 2-cell-reversal `B^co` to read it off cleanly,
   so it is given directly rather than as a one-line op-definition).

   This mirrors the strong-monoidal-transformation coherence under the same
   dictionary used for [Pseudofunctor]: tensor ↔ hcompose, I ↔ bi1id,
   μ ↔ pf_comp, η ↔ pf_id, α ↔ hassoc, λ/ρ ↔ hunit_left/right.  The naturator
   family and its coherence are phrased through the Godement composite
   [hcomp2], the associator [hassoc] and the unitors of the two bicategories,
   exactly as in `Theory/Bicategory/Pseudofunctor.v`.

   Notation: `∘∘` is vertical 2-cell composition (vcompose), `∘∘∘` is
   horizontal 1-cell composition (hcompose), `hcomp2` the Godement horizontal
   composite of 2-cells; the two composition infixes and the `pf1[ ]` accessor
   are inherited from `Theory/Bicategory/Pseudofunctor.v`. *)

(* The lax transformation class, at full strength.  Its data are the component
   1-cells [lt0] and the naturator 2-cells [lt1]; its laws are naturality of
   the naturator in 2-cells [lt1_natural], the unit coherence [lt_unit], and
   the composition coherence [lt_comp]. *)
Class LaxTransformation {B B' : Bicategory} (F G : Pseudofunctor B B') := {
  (* component 1-cells α_x : F x ~~> G x *)
  lt0 (x : @bi0cell B) : @bicat B' (pf0 F x) (pf0 G x);

  (* naturator 2-cells, in the lax orientation *)
  lt1 {x y : @bi0cell B} (f : @bicat B x y) :
    pf1[G] f ∘∘∘ lt0 x
      ~{ @bicat B' (pf0 F x) (pf0 G y) }~> lt0 y ∘∘∘ pf1[F] f;

  (* the naturator is natural in f: for a 2-cell μ : f ⟹ f', the square built
     from lt1 f, lt1 f' and the whiskerings of G μ and F μ commutes. *)
  lt1_natural {x y : @bi0cell B} {f f' : @bicat B x y}
      (μ : f ~{ @bicat B x y }~> f') :
    lt1 f' ∘∘ hcomp2 (fmap[pf1[G]] μ) (bi2id (a:=lt0 x))
      ≈ hcomp2 (bi2id (a:=lt0 y)) (fmap[pf1[F]] μ) ∘∘ lt1 f;

  (* unit coherence: the naturator at the identity 1-cell, conjugated by the
     unit isos pf_id of F and G, agrees with the comparison of the two unitors
     on the component 1-cell. *)
  lt_unit (x : @bi0cell B) :
    hcomp2 (bi2id (a:=lt0 x)) (to (@pf_id _ _ F x))
      ∘∘ lt1 (@bi1id B x)
      ∘∘ hcomp2 (from (@pf_id _ _ G x)) (bi2id (a:=lt0 x))
    ≈ from (hunit_right (lt0 x)) ∘∘ to (hunit_left (lt0 x));

  (* composition coherence: the naturator at a composite g ∘∘∘ f, conjugated by
     the compositors pf_comp of F and G, agrees with the pasting of the two
     naturators lt1 g and lt1 f re-bracketed by the associator of B'. *)
  lt_comp {x y z : @bi0cell B} (g : @bicat B y z) (f : @bicat B x y) :
    hcomp2 (bi2id (a:=lt0 z)) (to (@pf_comp _ _ F x y z g f))
      ∘∘ lt1 (g ∘∘∘ f)
      ∘∘ hcomp2 (from (@pf_comp _ _ G x y z g f)) (bi2id (a:=lt0 x))
    ≈ to (hassoc (lt0 z) (pf1[F] g) (pf1[F] f))
      ∘∘ hcomp2 (lt1 g) (bi2id (a:=pf1[F] f))
      ∘∘ from (hassoc (pf1[G] g) (lt0 y) (pf1[F] f))
      ∘∘ hcomp2 (bi2id (a:=pf1[G] g)) (lt1 f)
      ∘∘ to (hassoc (pf1[G] g) (pf1[G] f) (lt0 x))
}.

Arguments lt0 {B B'} {F G} _ x.
Arguments lt1 {B B'} {F G} _ {x y} f.
Arguments lt1_natural {B B'} {F G} _ {x y f f'} μ.
Arguments lt_unit {B B'} {F G} _ x.
Arguments lt_comp {B B'} {F G} _ {x y z} g f.

(* The oplax transformation class: the dual of [LaxTransformation], with every
   naturator 2-cell reversed.  The naturator now points

       olt1 f : olt0 y ∘∘∘ pf1[F] f  ⟹  pf1[G] f ∘∘∘ olt0 x,

   and the three coherence axioms are the mirror images of the lax ones (the
   unit and composition laws with the associators inverted and the unitor
   comparison reversed). *)
Class OplaxTransformation {B B' : Bicategory} (F G : Pseudofunctor B B') := {
  (* component 1-cells α_x : F x ~~> G x *)
  olt0 (x : @bi0cell B) : @bicat B' (pf0 F x) (pf0 G x);

  (* naturator 2-cells, in the oplax (reversed) orientation *)
  olt1 {x y : @bi0cell B} (f : @bicat B x y) :
    olt0 y ∘∘∘ pf1[F] f
      ~{ @bicat B' (pf0 F x) (pf0 G y) }~> pf1[G] f ∘∘∘ olt0 x;

  olt1_natural {x y : @bi0cell B} {f f' : @bicat B x y}
      (μ : f ~{ @bicat B x y }~> f') :
    olt1 f' ∘∘ hcomp2 (bi2id (a:=olt0 y)) (fmap[pf1[F]] μ)
      ≈ hcomp2 (fmap[pf1[G]] μ) (bi2id (a:=olt0 x)) ∘∘ olt1 f;

  olt_unit (x : @bi0cell B) :
    hcomp2 (to (@pf_id _ _ G x)) (bi2id (a:=olt0 x))
      ∘∘ olt1 (@bi1id B x)
      ∘∘ hcomp2 (bi2id (a:=olt0 x)) (from (@pf_id _ _ F x))
    ≈ from (hunit_left (olt0 x)) ∘∘ to (hunit_right (olt0 x));

  olt_comp {x y z : @bi0cell B} (g : @bicat B y z) (f : @bicat B x y) :
    hcomp2 (to (@pf_comp _ _ G x y z g f)) (bi2id (a:=olt0 x))
      ∘∘ olt1 (g ∘∘∘ f)
      ∘∘ hcomp2 (bi2id (a:=olt0 z)) (from (@pf_comp _ _ F x y z g f))
    ≈ from (hassoc (pf1[G] g) (pf1[G] f) (olt0 x))
      ∘∘ hcomp2 (bi2id (a:=pf1[G] g)) (olt1 f)
      ∘∘ to (hassoc (pf1[G] g) (olt0 y) (pf1[F] f))
      ∘∘ hcomp2 (olt1 g) (bi2id (a:=pf1[F] f))
      ∘∘ from (hassoc (olt0 z) (pf1[F] g) (pf1[F] f))
}.

Arguments olt0 {B B'} {F G} _ x.
Arguments olt1 {B B'} {F G} _ {x y} f.
Arguments olt1_natural {B B'} {F G} _ {x y f f'} μ.
Arguments olt_unit {B B'} {F G} _ x.
Arguments olt_comp {B B'} {F G} _ {x y z} g f.

(* A lax transformation is *pseudonatural* when every naturator 2-cell is
   invertible.  This is a mixin over [LaxTransformation]: it exposes, for each
   1-cell f, a witness that [lt1 σ f] is an isomorphism in the hom-category of
   B', hence a two-sided inverse and its cancellation laws via [IsIsomorphism].
   (nLab: a pseudonatural transformation is a lax transformation whose
   naturators are invertible.) *)
Class Pseudonatural {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ : LaxTransformation F G) := {
  pn_iso {x y : @bi0cell B} (f : @bicat B x y) : IsIsomorphism (lt1 σ f)
}.

Arguments pn_iso {B B' F G σ} _ {x y} f.

(** Inhabitation witness. *)

(* To witness that the transformation classes are inhabited "closed under the
   global context", we exhibit them on the terminal bicategory: one 0-cell, one
   1-cell, one 2-cell, with the codiscrete 2-cell setoid in which every 2-cell
   equation holds.  This is a genuine (non-vacuous) bicategory — its unique
   0-cell, 1-cell and 2-cell are all inhabited — so the identity lax
   transformation on it exercises every coherence field of the classes above
   without appeal to the target bicategory's Kelly coherence (λ_{bi1id} =
   ρ_{bi1id}), which the identity lax transformation on an *arbitrary*
   pseudofunctor would require. *)

(* The codiscrete setoid on [unit]: any two elements are related. *)
Program Definition triv_setoid : Setoid unit := {| equiv := fun _ _ => True |}.

(* The terminal bicategory.  All data are the unique inhabitant [tt]; every law
   is an equation in the codiscrete hom-setoid, hence holds. *)
Definition Trivial_Bicategory : Bicategory.
Proof.
  unshelve refine (Build_Bicategory'
    unit                            (* bi0cell *)
    (fun _ _ => unit)               (* bi1cell *)
    (fun _ _ _ _ => unit)           (* bi2cell *)
    (fun _ => tt)                   (* bi1id *)
    (fun _ _ _ _ => triv_setoid)    (* bi2homset *)
    (fun _ _ _ => tt)               (* bi2id *)
    (fun _ _ _ _ _ _ _ => tt)       (* vcompose *)
    _ _ _ _                         (* vcompose_respects, bi2id_left/right, vcompose_assoc *)
    _                               (* hcompose *)
    _ _ _                           (* hunit_left, hunit_right, hassoc *)
    _ _ _                           (* hunit_left/right/hassoc naturality *)
    _ _).                           (* triangle, pentagon *)
  (* the codiscrete equations, the two whiskering naturalities and the two
     coherence laws all reduce to [True]; the associator/unitor isos and the
     horizontal-composition functor are the unique trivial ones. *)
  all: try (repeat intro; exact I).
  - (* hcompose : the horizontal-composition functor *)
    intros x y z.
    unshelve eapply Build_Functor.
    + exact (fun _ => tt).
    + exact (fun _ _ _ => tt).
    + repeat intro; exact I.
    + repeat intro; exact I.
    + repeat intro; exact I.
  - (* hunit_left *)
    intros x y f.
    unshelve eapply Build_Isomorphism; try exact tt; exact I.
  - (* hunit_right *)
    intros x y f.
    unshelve eapply Build_Isomorphism; try exact tt; exact I.
  - (* hassoc *)
    intros w x y z h g f.
    unshelve eapply Build_Isomorphism; try exact tt; exact I.
Defined.

(* The identity lax transformation on the terminal bicategory (via the identity
   pseudofunctor): all components and naturators are the unique [tt], and all
   three coherence laws hold in the codiscrete setoid. *)
Program Definition Trivial_LaxTransformation :
  LaxTransformation (Identity_Pseudofunctor Trivial_Bicategory)
                    (Identity_Pseudofunctor Trivial_Bicategory) := {|
  lt0 := fun _ => tt;
  lt1 := fun _ _ _ => tt
|}.

(* Its naturators are (trivially) invertible, so it is pseudonatural. *)
Program Definition Trivial_Pseudonatural :
  Pseudonatural Trivial_LaxTransformation := {|
  pn_iso := fun _ _ _ => {| two_sided_inverse := tt |}
|}.

(* The oplax dual is inhabited on the same terminal bicategory. *)
Program Definition Trivial_OplaxTransformation :
  OplaxTransformation (Identity_Pseudofunctor Trivial_Bicategory)
                      (Identity_Pseudofunctor Trivial_Bicategory) := {|
  olt0 := fun _ => tt;
  olt1 := fun _ _ _ => tt
|}.

