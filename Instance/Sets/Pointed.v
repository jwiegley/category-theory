Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.ZeroObject.

Generalizable All Variables.

(** * The category of pointed sets *)

(* nLab:      https://ncatlab.org/nlab/show/pointed+set
   nLab:      https://ncatlab.org/nlab/show/pointed+object
   Wikipedia: https://en.wikipedia.org/wiki/Pointed_set
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              Springer 1998, §I.7 (printed p. 26)
   Book:      Awodey, "Category Theory", 2nd ed., OUP 2010, §1.6 Example 1.8
              (printed p. 19)
   Book:      Awodey, "Category Theory", 1st ed., OUP 2006, §7.9 Example 7.26

   This is Set_*, Mac Lane's category of pointed sets, built over the setoids
   of Instance/Sets.v.  An object is a Bishop set with a distinguished element
   and an arrow is a map carrying the distinguished element to the
   distinguished element:

      objects: pointed setoids       (carrier + `≈` + a basepoint [pt])
       arrows: pointed setoid maps   (setoid maps with f (pt X) ≈ pt Y)
   hom-setoid: f ≈ g  :=  ∀ x, f x ≈ g x   (as in [Sets]: pointwise, up to `≈`)
     identity: the identity setoid map
  composition: composition of setoid maps — the basepoint travels through both

   Mac Lane introduces Set_* in §I.7 alongside the observation that makes it
   worth having: the one-point set is at once initial and terminal in it, so
   Set_* has a null object, whereas Set itself does not (Mac Lane 1998, §I.7).
   [PointedSets_Zero] is that remark, in the [ZeroObject] form of
   Structure/ZeroObject.v; the zero morphism it induces is the constant map at
   the basepoint, [pointed_const] here.  A zero object is exactly what the
   additive-structure vocabulary of Structure/Preadditive.v and
   Structure/Kernel.v presupposes — kernels and cokernels are stated relative
   to zero morphisms — and Set_* supplies one with no addition on the homsets
   whatsoever, in contrast with the commutative monoids of Instance/CMon.v.
   More generally a pointed object in a category with a terminal object is an
   object under 1 (nLab, "pointed object"), and Set_* is the case C = Set.
   Awodey uses the same category as a first example of a category of
   structured sets and structure-preserving maps (Awodey 2010, §1.6 Example
   1.8), and returns to it for the coslice reading recorded in
   Instance/Sets/Pointed/Coslice.v (Awodey 2006, §7.9 Example 7.26).

   Structurally, pointed sets sit at three crossings the library already
   touches.  They are the coslice of Set under the one-point set, the theorem
   of Instance/Sets/Pointed/Coslice.v turning the prose of
   Construction/Slice.v's header into a [≅[Cat]].  They are the algebras of
   the maybe monad: an algebra structure option A → A is forced to be the
   identity on [Some], so it amounts to nothing more than a choice of point,
   while Instance/Sets/Par.v's [Part] is the Kleisli category of the same
   monad.  Instance/Sets/Pointed/Part.v builds the comparison between the two
   directly and proves it an equivalence over a decidability hypothesis —
   whose content is that in the decidable case every algebra is free — which
   upgrades the claim made in the header of Instance/Coq/Par.v.  (The
   identification of that concrete functor with the Eilenberg–Moore comparison
   of Monad/Comparison.v is not formalized here.)  And, in the classical
   setting, pointed sets carry the smash product, making Set_* the prototype
   of a monoidal-but-not-cartesian category of "sets with a zero" (nLab,
   "pointed set"); the smash product is not developed here. *)

(* The constructive ledger of this development

   nLab:      https://ncatlab.org/nlab/show/axiom+of+choice
   nLab:      https://ncatlab.org/nlab/show/split+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Axiom_of_choice

   Mac Lane's §I.7 discussion of Set_* is not only about the null object; the
   accompanying proposition is the standard dictionary between the elementary
   and the arrow-theoretic descriptions of injections and surjections, and in
   Set it reads: monic ⟺ injective, epic ⟺ surjective, every monic with
   non-empty domain splits, every epic splits.  Formalizing it constructively
   separates the four claims sharply, and the separation is the mathematical
   content of this file rather than a formalization artefact.  What holds
   here, and at what price:

   - [pointed_monic_iff] : monic ⟺ injective.  UNCONDITIONAL.  The hard
     direction probes with the two-point pointed set [PointedTwo]; the
     singleton, which is Set's probe, is here the zero object and detects
     nothing, so the smallest useful probe has exactly one free point.

   - [pointed_epic_iff] : epic ⟺ surjective.  UNCONDITIONAL — no
     decidability, no choice.  The witness is the pointed cokernel pair
     [PointedCP]: two copies of the codomain glued along the image, with the
     gluing relation given in CLOSED FORM rather than as the transitive
     closure of a generating relation, so no quotient machinery is required.
     The two basepoints are identified because [preserves_pt] puts the
     basepoint in the image ([InImage_pt]), which is exactly what makes both
     legs pointed.  Since `≈` is [Type]-valued, the surjectivity extracted
     from an epimorphism carries preimages as DATA, which is what lets the
     inverse below be assembled without choice.

   - [pointed_monic_split] : monic ⟹ split monic, under the explicit
     hypothesis [ImageDecidable] that membership in the image is decidable.
     The retraction sends a point of the image to its preimage — unique, by
     injectivity — and everything else to the basepoint.  Note that Mac Lane's
     side condition "non-empty domain" is automatic in Set_*: every object has
     a basepoint.

   - [pointed_epic_split] : epic ⟹ split epi, under an enumeration of the
     domain together with decidable `≈` on the codomain.  This is the honest
     price.  In Set the unrestricted statement "every epimorphism splits" IS
     the axiom of choice (nLab, "axiom of choice"; Wikipedia, "Axiom of
     choice"), so no hypothesis-free proof can exist.  The obstruction is
     visible at exactly one point: a section must be RESPECTFUL, and when [f]
     is not injective two `≈`-related points of the codomain can have entirely
     unrelated preimages.  A first-preimage search over a fixed enumeration
     removes it, because the index it selects depends on the argument only
     through its `≈`-class — [pointed_search_respects] proves this up to
     Leibniz equality, not merely up to `≈`.  The basepoint is special-cased,
     without which the section need not be a morphism of Set_* at all.

   - [pointed_balanced] : invertible ⟺ monic ∧ epic.  UNCONDITIONAL in both
     directions, and the pleasant surprise of the file: although neither
     splitting result is available without hypotheses, their combination is.
     Injectivity from [pointed_monic_iff] makes the candidate inverse
     respectful and basepoint-preserving; surjectivity from
     [pointed_epic_iff], being data, supplies the function itself.  So Set_*
     is a balanced category constructively.

   Instance/Sets/Pointed/Finite.v discharges every hypothesis above at once
   for finite pointed sets with decidable equality, and exercises the results
   by computing a retraction and a section of concrete maps; it also exhibits
   a monic that is not epic and an epic that is not monic, so that
   [pointed_balanced] is not vacuous.  The satellite files are
   Instance/Sets/Pointed/Part.v (the equivalence with partial maps) and
   Instance/Sets/Pointed/Coslice.v (the coslice presentation). *)

(* A pointed setoid: a Bishop set together with a distinguished element. *)
Record PointedSetoid := {
  pointed_setoid :> SetoidObject;
  pt : carrier pointed_setoid
}.

(* A pointed map: a setoid map that carries the basepoint to the basepoint. *)
Record PointedMorphism (X Y : PointedSetoid) := {
  pointed_map :> SetoidMorphism (pointed_setoid X) (pointed_setoid Y);
  preserves_pt : pointed_map (pt X) ≈ pt Y
}.

Arguments pointed_map {X Y} _.
Arguments preserves_pt {X Y} _.

#[local] Obligation Tactic := idtac.

(* The hom-setoid: two pointed maps agree when their underlying setoid maps
   agree pointwise, exactly as in [Sets]. *)
#[export]
Program Instance PointedMorphism_Setoid {X Y : PointedSetoid} :
  Setoid (PointedMorphism X Y) := {|
  equiv := fun f g => ∀ x, pointed_map f x ≈ pointed_map g x
|}.
Next Obligation.
  intros X Y.
  constructor.
  - intros f x.
    reflexivity.
  - intros f g Hfg x.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh x.
    transitivity (pointed_map g x).
    + apply Hfg.
    + apply Hgh.
Qed.

(* The identity pointed map. *)
Program Definition pointed_id {X : PointedSetoid} : PointedMorphism X X := {|
  pointed_map := setoid_morphism_id
|}.
Next Obligation.
  intros X; simpl.
  reflexivity.
Qed.

(* Composition of pointed maps: the basepoint travels through both. *)
Program Definition pointed_compose {X Y Z : PointedSetoid}
        (f : PointedMorphism Y Z) (g : PointedMorphism X Y) :
  PointedMorphism X Z := {|
  pointed_map := setoid_morphism_compose (pointed_map f) (pointed_map g)
|}.
Next Obligation.
  intros X Y Z f g; simpl.
  unfold Basics.compose.
  rewrite (preserves_pt g).
  apply (preserves_pt f).
Qed.

Lemma pointed_compose_respects {X Y Z : PointedSetoid} :
  Proper (equiv ==> equiv ==> equiv) (@pointed_compose X Y Z).
Proof.
  intros f f' Hf g g' Hg x; simpl.
  unfold Basics.compose.
  rewrite (Hg x).
  apply Hf.
Qed.

(* The category of pointed sets, Mac Lane's Set_*.

       objects: pointed setoids            (a Bishop set with a basepoint)
        arrows: basepoint-preserving maps  (f (pt X) ≈ pt Y)
      identity: the identity setoid map
   composition: composition of setoid maps *)
Program Definition PointedSets : Category := {|
  obj     := PointedSetoid;
  hom     := PointedMorphism;
  homset  := @PointedMorphism_Setoid;
  id      := @pointed_id;
  compose := @pointed_compose;

  compose_respects := @pointed_compose_respects
|}.
Next Obligation. intros X Y f x; simpl; reflexivity. Qed.
Next Obligation. intros X Y f x; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z W f g h x; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z W f g h x; simpl; reflexivity. Qed.

(** ** The zero object: a single point, both initial and terminal *)

(* The one-point pointed set: [poly_unit] under `=`, pointed at its only
   element.  It plays both universal roles below. *)
Definition PointedOne : PointedSetoid := {|
  pointed_setoid := {| carrier := poly_unit |};
  pt := ttt
|}.

(* The constant map at the codomain's basepoint.  It is pointed for the most
   trivial of reasons, and it is the zero morphism of [PointedSets]: it is
   simultaneously the unique map into the one-point set and the unique map out
   of it, which is what makes that object a null object. *)
Program Definition const_pt_map (X Y : PointedSetoid) :
  SetoidMorphism (pointed_setoid X) (pointed_setoid Y) := {|
  morphism := fun _ => pt Y
|}.
Next Obligation. intros X Y; proper. Qed.

Definition pointed_const {X Y : PointedSetoid} : PointedMorphism X Y.
Proof.
  refine (Build_PointedMorphism X Y (const_pt_map X Y) _).
  simpl.
  reflexivity.
Defined.

(* Into the one-point set there is exactly one map: everything goes to the
   only element, which is that object's basepoint. *)
Definition pointed_one {X : PointedSetoid} : PointedMorphism X PointedOne :=
  @pointed_const X PointedOne.

Lemma pointed_one_unique {X : PointedSetoid}
  (f g : PointedMorphism X PointedOne) : f ≈ g.
Proof.
  intro x.
  (* [simpl] first: it keeps the goal's universes from being minimized to
     [Set] when the [poly_unit] elimination below is elaborated. *)
  simpl.
  destruct (pointed_map f x), (pointed_map g x).
  reflexivity.
Qed.

Definition PointedSets_Terminal : @Terminal PointedSets :=
  @Build_Terminal PointedSets PointedOne
    (fun X => @pointed_one X) (fun X => @pointed_one_unique X).

(* Out of the one-point set there is also exactly one map, and this is where
   pointedness bites: the single element IS the basepoint, so its image is
   forced to be the codomain's basepoint.  In [Sets] the singleton is only
   terminal; in [PointedSets] it is initial as well. *)
Definition pointed_zero {X : PointedSetoid} : PointedMorphism PointedOne X :=
  @pointed_const PointedOne X.

Lemma pointed_zero_unique {X : PointedSetoid}
  (f g : PointedMorphism PointedOne X) : f ≈ g.
Proof.
  intro u.
  simpl.
  destruct u.
  transitivity (pt X).
  - exact (preserves_pt f).
  - symmetry.
    exact (preserves_pt g).
Qed.

Definition PointedSets_Initial : @Initial PointedSets :=
  @Build_Terminal (PointedSets^op) PointedOne
    (fun X => @pointed_zero X) (fun X => @pointed_zero_unique X).

(* Mac Lane's null object (CWM §I.7): the same one-point set is initial and
   terminal, so the coincidence isomorphism is the identity.  Consequently
   every hom-setoid of [PointedSets] has a distinguished zero morphism, the
   constant map at the basepoint (Structure/ZeroObject.v's [zero_mor]). *)
#[export] Instance PointedSets_Zero : ZeroObject PointedSets :=
  @Build_ZeroObject PointedSets PointedSets_Terminal PointedSets_Initial iso_id.

(** ** Images, injections and surjections *)

(* [f] is injective when it separates points up to `≈`. *)
Definition PointedInjective {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ a b : carrier X, f a ≈ f b → a ≈ b.

(* Membership of [y] in the image of [f].  Because `≈` is [Type]-valued, this
   is a [sigT] and therefore carries the preimage as data: no choice principle
   is needed to extract it later. *)
Definition InImage {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (y : carrier Y) : Type :=
  ∃ x : carrier X, f x ≈ y.

(* [f] is surjective when every point of the codomain is in its image. *)
Definition PointedSurjective {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ b : carrier Y, InImage f b.

(* Image membership is a property of the `≈`-class, not of the representative:
   the same preimage witnesses membership of any equivalent point. *)
Lemma InImage_respects {X Y : PointedSetoid} (f : PointedMorphism X Y)
  {y y' : carrier Y} : y ≈ y' → InImage f y → InImage f y'.
Proof.
  intros Hyy [x Hx].
  exists x.
  now rewrite Hx.
Qed.

(* The basepoint is always in the image: [preserves_pt] IS a preimage
   witness.  This one line is what makes the cokernel-pair argument below
   respect basepoints, and what pins the retraction of a monic at the
   basepoint. *)
Lemma InImage_pt {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  InImage f (pt Y).
Proof.
  exists (pt X).
  apply preserves_pt.
Qed.

(** ** Monomorphisms are exactly the injections *)

(* The two-point pointed set: [option poly_unit] pointed at [None].  It is the
   probe object for monomorphisms — a map out of it is precisely a choice of
   one free point of the target, the basepoint being forced.  (In [Sets] the
   singleton suffices; here the singleton is the zero object, so it detects
   nothing, and the smallest useful probe has one point to spare.) *)
Definition PointedTwo : PointedSetoid := {|
  pointed_setoid := {| carrier := option poly_unit |};
  pt := Datatypes.None
|}.

Program Definition probe_map {X : PointedSetoid} (x : carrier X) :
  SetoidMorphism (pointed_setoid PointedTwo) (pointed_setoid X) := {|
  morphism := fun o => match o with
                       | Datatypes.Some _ => x
                       | Datatypes.None => pt X
                       end
|}.
Next Obligation.
  intros X x; simpl; intros a b Hab.
  destruct a, b; simpl in *; try contradiction; reflexivity.
Qed.

(* The probe at [x]: basepoint to basepoint, free point to [x]. *)
Definition pointed_probe {X : PointedSetoid} (x : carrier X) :
  PointedMorphism PointedTwo X.
Proof.
  refine (Build_PointedMorphism PointedTwo X (probe_map x) _).
  simpl.
  reflexivity.
Defined.

(* Mac Lane CWM §I.7: in Set_* the monomorphisms are exactly the injective
   maps.  Both directions are unconditional.  The hard direction feeds [f] the
   two probes at [a] and at [b]: they agree after [f], hence agree, hence
   a ≈ b at the free point. *)
Theorem pointed_monic_iff {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : PointedInjective f ↔ Monic f.
Proof.
  split.
  - intros Hinj.
    constructor; intros Z g1 g2 Hg z; simpl in *.
    apply Hinj.
    exact (Hg z).
  - intros [Hmonic] a b Hab.
    specialize (Hmonic PointedTwo (pointed_probe a) (pointed_probe b)).
    simpl in Hmonic.
    refine (Hmonic _ (Datatypes.Some ttt)).
    intros [u|]; simpl.
    + exact Hab.
    + reflexivity.
Qed.

(** ** Epimorphisms are exactly the surjections *)

(* The pointed cokernel pair of [f].  The carrier is two copies of Y; the
   relation is given in closed form rather than as the transitive closure of a
   generating relation, which is what keeps the development free of any
   quotient machinery:

       inl a ~ inl b   iff   a ≈ b
       inr a ~ inr b   iff   a ≈ b
       inl a ~ inr b   iff   a ≈ b  and  a lies in the image of f

   In words: the two copies are glued exactly along the image of [f].  The
   basepoint is [inl (pt Y)] — and the OTHER basepoint [inr (pt Y)] is
   equivalent to it, because [preserves_pt] puts [pt Y] in the image
   ([InImage_pt]); this is precisely why the right leg below is a pointed
   map. *)
Definition CP_rel {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (u v : carrier Y + carrier Y) : Type :=
  match u, v with
  | Datatypes.inl a, Datatypes.inl b => a ≈ b
  | Datatypes.inr a, Datatypes.inr b => a ≈ b
  | Datatypes.inl a, Datatypes.inr b => (a ≈ b) ∧ InImage f a
  | Datatypes.inr a, Datatypes.inl b => (a ≈ b) ∧ InImage f a
  end.

Program Definition CP_setoid {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Setoid (carrier Y + carrier Y) := {|
  equiv := CP_rel f
|}.
Next Obligation.
  intros X Y f.
  constructor.
  - intros [a|a]; simpl; reflexivity.
  - intros [a|a] [b|b]; simpl; intros H.
    + now symmetry.
    + destruct H as [Hab Him].
      split.
      * now symmetry.
      * exact (InImage_respects f Hab Him).
    + destruct H as [Hab Him].
      split.
      * now symmetry.
      * exact (InImage_respects f Hab Him).
    + now symmetry.
  - intros [a|a] [b|b] [c|c]; simpl; intros H1 H2.
    (* inl a ~ inl b ~ inl c *)
    + now transitivity b.
    (* inl a ~ inl b ~ inr c: the image membership travels back along H1 *)
    + destruct H2 as [Hbc Him].
      split.
      * now transitivity b.
      * exact (InImage_respects f (symmetry H1) Him).
    (* inl a ~ inr b ~ inl c *)
    + destruct H1 as [Hab _], H2 as [Hbc _].
      now transitivity b.
    (* inl a ~ inr b ~ inr c *)
    + destruct H1 as [Hab Him].
      split; [ now transitivity b | exact Him ].
    (* inr a ~ inl b ~ inl c *)
    + destruct H1 as [Hab Him].
      split; [ now transitivity b | exact Him ].
    (* inr a ~ inl b ~ inr c *)
    + destruct H1 as [Hab _], H2 as [Hbc _].
      now transitivity b.
    (* inr a ~ inr b ~ inl c *)
    + destruct H2 as [Hbc Him].
      split.
      * now transitivity b.
      * exact (InImage_respects f (symmetry H1) Him).
    (* inr a ~ inr b ~ inr c *)
    + now transitivity b.
Qed.

Definition PointedCP {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  PointedSetoid := {|
  pointed_setoid := {| carrier := carrier Y + carrier Y
                     ; is_setoid := CP_setoid f |};
  pt := Datatypes.inl (pt Y)
|}.

(* The two legs of the cokernel pair.  The left leg is pointed on the nose;
   the right leg is pointed because the two basepoints have been identified,
   which needs [InImage_pt]. *)
Program Definition CP_left_map {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid (PointedCP f)) := {|
  morphism := fun y => Datatypes.inl y
|}.
Next Obligation. intros X Y f; simpl; intros a b Hab; exact Hab. Qed.

Program Definition CP_right_map {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid (PointedCP f)) := {|
  morphism := fun y => Datatypes.inr y
|}.
Next Obligation. intros X Y f; simpl; intros a b Hab; exact Hab. Qed.

Definition CP_left {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Y ~{PointedSets}~> PointedCP f.
Proof.
  refine (Build_PointedMorphism Y (PointedCP f) (CP_left_map f) _).
  simpl.
  reflexivity.
Defined.

Definition CP_right {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Y ~{PointedSets}~> PointedCP f.
Proof.
  refine (Build_PointedMorphism Y (PointedCP f) (CP_right_map f) _).
  simpl.
  split.
  - reflexivity.
  - apply InImage_pt.
Defined.

(* The two legs agree after [f]: every point of the form [f x] is in the image
   by definition, which is exactly the gluing condition. *)
Lemma CP_coequalizes {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  CP_left f ∘ f ≈ CP_right f ∘ f.
Proof.
  intro x; simpl.
  split.
  - reflexivity.
  - exists x.
    reflexivity.
Qed.

(* An epimorphism of pointed sets is surjective.  Feed the cokernel pair to
   the cancellation property: the two legs become equal, and equality of the
   legs at [b] says precisely that [b] lies in the image.  No decidability and
   no choice enter — the image-membership witness is read straight off the
   relation. *)
Theorem pointed_epic_surjective {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Epic f → PointedSurjective f.
Proof.
  intros [Hepic] b.
  spose (Hepic (PointedCP f) (CP_left f) (CP_right f) (CP_coequalizes f) b)
    as Hb.
  exact (snd Hb).
Qed.

(* Mac Lane CWM §I.7: in Set_* the epimorphisms are exactly the surjective
   maps.  Both directions are unconditional. *)
Theorem pointed_epic_iff {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  PointedSurjective f ↔ Epic f.
Proof.
  split.
  - intros Hsurj.
    constructor; intros Z g1 g2 Hg b; simpl in *.
    destruct (Hsurj b) as [a Ha].
    rewrite <- Ha.
    exact (Hg a).
  - apply pointed_epic_surjective.
Qed.

(** ** Mac Lane's Proposition (CWM §I.7): splitting, and balance *)

(* The easy halves, valid in any category and proved here pointwise: a
   morphism with a left inverse is monic, one with a right inverse is epic. *)

Corollary pointed_split_monic_is_monic {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Section f → Monic f.
Proof.
  intros [r Hr].
  constructor; intros Z g1 g2 Hg z; simpl in *.
  transitivity (r (f (g1 z))).
  - symmetry.
    exact (Hr (g1 z)).
  - rewrite (Hg z).
    exact (Hr (g2 z)).
Qed.

Corollary pointed_split_epic_is_epic {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Retraction f → Epic f.
Proof.
  intros [s Hs].
  constructor; intros Z g1 g2 Hg b; simpl in *.
  transitivity (g1 (f (s b))).
  - now rewrite (Hs b).
  - rewrite (Hg (s b)).
    now rewrite (Hs b).
Qed.

(** *** Monic implies split monic, given decidable image membership *)

(* The hypothesis that makes the classical argument constructive: for each
   point of the codomain we may DECIDE whether it is hit.  Classically this is
   free; constructively it is exactly the missing content, and
   Instance/Sets/Pointed/Finite.v supplies it for every map out of a finitely
   enumerated pointed set into one with decidable `≈`. *)
Definition ImageDecidable {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ b : carrier Y, InImage f b + ¬ InImage f b.

(* The retraction: send a point of the image to its (unique, by injectivity)
   preimage, and everything else to the basepoint.  The basepoint of Y is
   never in the "everything else" branch — [InImage_pt] — so the retraction is
   automatically pointed. *)
Definition pointed_retract_fun {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (dec : ImageDecidable f) (b : carrier Y) :
  carrier X :=
  match dec b with
  | Datatypes.inl w => `1 w
  | Datatypes.inr _ => pt X
  end.

Program Definition pointed_retract_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (Hinj : PointedInjective f)
  (dec : ImageDecidable f) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := pointed_retract_fun f dec
|}.
Next Obligation.
  intros X Y f Hinj dec; simpl; intros b b' Hbb.
  unfold pointed_retract_fun.
  destruct (dec b) as [[a Ha]|n], (dec b') as [[a' Ha']|n']; simpl.
  - apply Hinj.
    rewrite Ha, Ha'.
    exact Hbb.
  - destruct (n' (InImage_respects f Hbb (a; Ha))).
  - destruct (n (InImage_respects f (symmetry Hbb) (a'; Ha'))).
  - reflexivity.
Qed.

Definition pointed_retract {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (Hinj : PointedInjective f) (dec : ImageDecidable f) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_retract_map f Hinj dec) _).
  simpl.
  unfold pointed_retract_fun.
  destruct (dec (pt Y)) as [[a Ha]|n]; simpl.
  - apply Hinj.
    rewrite Ha.
    symmetry.
    exact (preserves_pt f).
  - destruct (n (InImage_pt f)).
Defined.

(* Mac Lane's Proposition, first half: a monic pointed map splits, PROVIDED
   image membership is decidable.  The retraction is the one above; both of
   its laws are consequences of injectivity.  Ends in [Defined] because the
   retraction is DATA: Instance/Sets/Pointed/Finite.v evaluates it at concrete
   points by [reflexivity]. *)
Theorem pointed_monic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (dec : ImageDecidable f) : Monic f → Section f.
Proof.
  intros Hm.
  pose proof (snd (pointed_monic_iff f) Hm) as Hinj.
  refine (@Build_Section PointedSets X Y f (pointed_retract f Hinj dec) _).
  intro a; simpl.
  unfold pointed_retract_fun.
  destruct (dec (f a)) as [[a' Ha']|n]; simpl.
  - now apply Hinj.
  - refine (False_rect _ (n _)).
    exists a.
    reflexivity.
Defined.

(** *** Balance: invertible IS monic and epic, with no hypotheses at all *)

(* The inverse of a bimorphism.  Injectivity supplies respectfulness (the
   witness attached to [b] is pinned by its value) and pointedness; the
   surjectivity witness supplies the function itself. *)
Program Definition pointed_inverse_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (Hinj : PointedInjective f)
  (Hsurj : PointedSurjective f) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := fun b => `1 (Hsurj b)
|}.
Next Obligation.
  intros X Y f Hinj Hsurj; simpl; intros b b' Hbb.
  apply Hinj.
  rewrite (`2 (Hsurj b)), (`2 (Hsurj b')).
  exact Hbb.
Qed.

Definition pointed_inverse {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (Hinj : PointedInjective f) (Hsurj : PointedSurjective f) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_inverse_map f Hinj Hsurj) _).
  simpl.
  apply Hinj.
  rewrite (`2 (Hsurj (pt Y))).
  symmetry.
  exact (preserves_pt f).
Defined.

(* Mac Lane's Proposition, the balanced statement: in Set_* a map is
   invertible exactly when it is both monic and epic — and, in contrast with
   the two splitting results, this needs NO hypotheses.  The forward direction
   is formal; the converse assembles the inverse from the injectivity of a
   monic and the surjectivity of an epic, both established unconditionally
   above, the surjectivity witness being data rather than a mere existence
   claim. *)
Theorem pointed_balanced {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  IsIsomorphism f ↔ (Monic f ∧ Epic f).
Proof.
  split.
  - intros [g Hfg Hgf].
    split.
    + apply (pointed_split_monic_is_monic f).
      exact (@Build_Section PointedSets X Y f g Hgf).
    + apply (pointed_split_epic_is_epic f).
      exact (@Build_Retraction PointedSets X Y f g Hfg).
  - intros [Hm He].
    pose proof (snd (pointed_monic_iff f) Hm) as Hinj.
    pose proof (pointed_epic_surjective f He) as Hsurj.
    refine (@Build_IsIsomorphism PointedSets X Y f
              (pointed_inverse f Hinj Hsurj) _ _).
    + intro b; simpl.
      exact (`2 (Hsurj b)).
    + intro a; simpl.
      apply Hinj.
      exact (`2 (Hsurj (f a))).
Qed.

(** *** Epic implies split epic, given an enumeration and a decidable
        codomain *)

(* Decidability of `≈` on a pointed setoid. *)
Definition DecidableEquiv (Y : PointedSetoid) : Type :=
  ∀ y y' : carrier Y, (y ≈ y') + ¬ (y ≈ y').

(* Decidability of "is this the basepoint?", the weaker hypothesis needed by
   the essential-surjectivity argument of Instance/Sets/Pointed/Part.v. *)
Definition DecidablePt (Z : PointedSetoid) : Type :=
  ∀ z : carrier Z, (z ≈ pt Z) + ¬ (z ≈ pt Z).

(* Membership in a list up to `≈`, [Type]-valued so that the position of the
   witness may be inspected. *)
Fixpoint InSetoid {X : PointedSetoid}
  (x : carrier X) (l : list (carrier X)) : Type :=
  match l with
  | Datatypes.nil => False
  | Datatypes.cons a l' => (a ≈ x) + InSetoid x l'
  end.

(* An enumeration of a pointed setoid: a list meeting every `≈`-class.  This
   is the finiteness hypothesis; the [bool] witness of
   Instance/Sets/Pointed/Finite.v satisfies it. *)
Record PointedEnumeration (X : PointedSetoid) := {
  enum_list : list (carrier X);
  enum_covers : ∀ x : carrier X, InSetoid x enum_list
}.

Arguments enum_list {X} _.
Arguments enum_covers {X} _ _.

(* First-preimage search.  The KEY property is [pointed_search_respects]: the
   result depends on [b] only through its `≈`-class, and it does so up to
   Leibniz equality, not merely up to `≈`.  That is what makes the section
   below respectful — a bare choice of preimages need not be, since
   `≈`-related points can have wholly unrelated preimages when [f] is not
   injective, and this is precisely the obstruction that makes "every epi
   splits" a choice principle in general. *)
Fixpoint pointed_search {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y) :
  option (carrier X) :=
  match l with
  | Datatypes.nil => Datatypes.None
  | Datatypes.cons a l' =>
    match deq (f a) b with
    | Datatypes.inl _ => Datatypes.Some a
    | Datatypes.inr _ => pointed_search f deq l' b
    end
  end.

Lemma pointed_search_respects {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b b' : carrier Y) :
  b ≈ b' → pointed_search f deq l b = pointed_search f deq l b'.
Proof.
  intro Hbb.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - destruct (deq (f a) b) as [p|n], (deq (f a) b') as [p'|n'].
    + reflexivity.
    + destruct (n' (transitivity p Hbb)).
    + destruct (n (transitivity p' (symmetry Hbb))).
    + exact IH.
Qed.

Lemma pointed_search_correct {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y)
  (a : carrier X) :
  pointed_search f deq l b = Datatypes.Some a → f a ≈ b.
Proof.
  induction l as [|a0 l IH]; simpl.
  - intro H; discriminate.
  - destruct (deq (f a0) b) as [p|n].
    + intro H.
      injection H; intro Ha; subst.
      exact p.
    + exact IH.
Qed.

Lemma pointed_search_complete {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y)
  (a : carrier X) :
  InSetoid a l → f a ≈ b → pointed_search f deq l b <> Datatypes.None.
Proof.
  induction l as [|a0 l IH]; simpl.
  - intros [].
  - intros [Hh|Ht] Hfa; destruct (deq (f a0) b) as [p|n].
    + discriminate.
    + refine (False_rect _ (n _)).
      rewrite Hh.
      exact Hfa.
    + discriminate.
    + exact (IH Ht Hfa).
Qed.

(* The section: the basepoint goes to the basepoint (which IS a preimage, by
   [preserves_pt]) and every other point to the FIRST element of the
   enumeration mapping onto it.  Special-casing the basepoint is not a
   convenience — without it the section need not be a morphism of Set_* at
   all, since the first preimage of the basepoint may well be an ordinary
   point. *)
Definition pointed_section_fun {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) (b : carrier Y) :
  carrier X :=
  match deq b (pt Y) with
  | Datatypes.inl _ => pt X
  | Datatypes.inr _ =>
    match pointed_search f deq (enum_list E) b with
    | Datatypes.Some a => a
    | Datatypes.None => pt X
    end
  end.

Program Definition pointed_section_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (deq : DecidableEquiv Y)
  (E : PointedEnumeration X) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := pointed_section_fun f deq E
|}.
Next Obligation.
  intros X Y f deq E; simpl; intros b b' Hbb.
  unfold pointed_section_fun.
  destruct (deq b (pt Y)) as [p|n], (deq b' (pt Y)) as [p'|n'].
  - reflexivity.
  - destruct (n' (transitivity (symmetry Hbb) p)).
  - destruct (n (transitivity Hbb p')).
  - rewrite (pointed_search_respects f deq (enum_list E) b b' Hbb).
    reflexivity.
Qed.

Definition pointed_section {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_section_map f deq E) _).
  simpl.
  unfold pointed_section_fun.
  destruct (deq (pt Y) (pt Y)) as [p|n].
  - reflexivity.
  - refine (False_rect _ (n _)).
    reflexivity.
Defined.

(* Mac Lane's Proposition, second half: an epic pointed map splits, PROVIDED
   the domain is enumerated and `≈` on the codomain is decidable.  In Set the
   unrestricted statement "every epi splits" IS the axiom of choice, so the
   hypothesis pack is the honest constructive content of the proposition, not
   an artefact of the formalization: what a section must supply is a COHERENT
   choice of preimages, and an enumeration plus a decidable codomain is the
   smallest structure that produces one canonically.  As with
   [pointed_monic_split], this ends in [Defined] so that the section it builds
   computes. *)
Theorem pointed_epic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) :
  Epic f → Retraction f.
Proof.
  intros He.
  pose proof (pointed_epic_surjective f He) as Hsurj.
  refine (@Build_Retraction PointedSets X Y f (pointed_section f deq E) _).
  intro b; simpl.
  unfold pointed_section_fun.
  destruct (deq b (pt Y)) as [p|n].
  - rewrite (preserves_pt f).
    now symmetry.
  - destruct (pointed_search f deq (enum_list E) b) as [a|] eqn:Hs.
    + exact (pointed_search_correct f deq (enum_list E) b a Hs).
    + destruct (Hsurj b) as [a Ha].
      destruct (pointed_search_complete f deq (enum_list E) b a
                  (enum_covers E a) Ha Hs).
Defined.
