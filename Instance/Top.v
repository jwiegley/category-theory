Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * The category of topological spaces *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.7,
     printed p. 25
   nLab:      https://ncatlab.org/nlab/show/Top
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_topological_spaces
   Book:      Fong and Spivak, "Seven Sketches in Compositionality",
              §7.3.2, Definition 7.25 (open covers)
   Book:      Riehl, "Category Theory in Context", Examples 1.3.14(iv)
              and 1.4.4(v)

   This is the category [Top]. Mac Lane's roll-call of the standard large
   categories (CWM §I.7, printed p. 25) lists `Top`: objects the
   topological spaces, arrows the continuous maps. It is the ambient
   category of general topology, and the source of much categorical
   vocabulary — in the mathematics at large (none of it formalized here)
   the subspace and quotient topologies are limits and colimits, the
   product topology is the categorical product, and the initial and final
   topologies are those (co)limit constructions read as universal
   properties.

      objects: topological spaces  (a setoid of points + a family of opens)
       arrows: continuous maps     (preimages of opens are open)
   hom-setoid: f ≈ g  :=  ∀ x, f x ≈ g x   (pointwise, on the map part)
     identity: the identity map
  composition: composition of maps, preimages composing contravariantly

   The companion file Instance/Top/Closed.v carries the opens of a space as
   a thin category (Riehl, CTiC Example 1.3.14(iv)) and the complementation
   duality with its closed sets (Example 1.4.4(v)). *)

(* Design: what a topological space is, constructively

   nLab:      https://ncatlab.org/nlab/show/locale
   nLab:      https://ncatlab.org/nlab/show/constructive+mathematics
   Book:      Johnstone, "Stone Spaces", CUP 1982 (the locale/space
              adjunction and the pointfree tradition)
   Book:      Bishop, "Foundations of Constructive Analysis", McGraw-Hill
              1967 (the setoid discipline this file inherits)

   Four decisions govern the encoding below, and each is forced by the
   surrounding library rather than chosen for taste.

   1. POINTS ARE A SETOID.  Objects carry a [SetoidObject] of points, not
      a bare type: this is the same Bishop-set discipline that makes
      Instance/Sets.v the library's stand-in for Set.  A consequence is
      that an open set must be a predicate that respects `≈`; the field
      [open_proper] demands exactly that, so the topology cannot separate
      two points the carrier's own equality has already identified.

   2. OPENS ARE A PREDICATE ON PREDICATES, HENCE ONE UNIVERSE UP.  A
      topology is a subset of the powerset, so [IsOpen] has type
      `(carrier → Type) → Type`: it quantifies over predicates on the
      carrier and therefore lives strictly above the universe of points.
      This is the same placement Theory/Subobject/Functor.v gives its
      Sets-valued presheaf `Sub : C^op ⟶ Sets` — a subobject lattice is
      a powerset-sized object over a hom-sized base — and the same size
      phenomenon that keeps the truth-value object of Instance/Sets.v's
      [surjectivity_is_epic] out of Sets and confines the classifier
      theorems to Instance/Sets/Classifier.v.  Concretely, the record is
      declared [TopSpace@{o}]: points, their equalities, the values of an
      open predicate, the index type of a union and the openness witnesses
      all sit at `Type@{o}`, following the `SetoidObject@{o o}` discipline
      of Instance/Sets.v — so [TopSpace@{o}] itself lands at `Type@{o+2}`,
      the [IsOpen] field having quantified over the `Type@{o+1}` of
      predicates on the carrier.  The ascent shows up again one step later:
      [Continuous] quantifies over the opens of the codomain, so the
      hom-sets of [Top] live at `o+1`, which is the declared constraint
      `o < h` on [ContinuousMorphism_equiv] below.  Because all of this is
      universe-polymorphic, [Top] exists at every level rather than needing
      a chosen "universe of small sets".

   3. THE AXIOMS ARE STATED IN THEIR TYPE-VALUED FORM.  The union axiom
      quantifies over an arbitrary index TYPE and forms the dependent sum
      `{ i : I & U i x }` — the constructive reading of `⋃ᵢ Uᵢ`, where an
      element of the union carries the index witnessing membership.  The
      binary intersection is the product `U x ∧ V x`, and the whole space
      is the constant predicate [poly_unit].  Because `≈`-equality of
      predicates is pointwise `↔` (the library's [iffT]) rather than
      Rocq's `=`, closure under unions alone is not enough: [open_respects]
      records that being open is invariant under pointwise equivalence,
      which is what lets the union axiom be applied up to reindexing.

   4. THE EMPTY OPEN AND THE CONSTANTS ARE THEOREMS, NOT AXIOMS.  The
      union over the empty index type gives the empty open, and — the
      lemma that does the most work downstream — the union over the index
      type `P` of copies of the whole space gives [open_const]: EVERY
      constant predicate is open, in every space.  Its corollary
      [open_uniform] says every "uniform" predicate (one that holds at a
      point as soon as it holds anywhere) is open.  This is the
      constructive replacement for the classical remark that `∅` and `X`
      are open in every topology: constructively there are many more
      predicates that cannot be told apart from `∅` or `X`, and all of
      them must be open.  It is exactly what makes the one-point space
      terminal (§ [Top_Terminal]) and every map into an indiscrete space
      continuous (§ [into_indiscrete_continuous]).

   What is deliberately NOT attempted here: the pointfree turn.  A
   constructive analyst usually prefers locales (frames of opens with no
   points at all — Johnstone, "Stone Spaces"), precisely because the
   point-set axioms above behave badly without excluded middle.  This
   file stays point-set because the work order is Mac Lane's `Top`, and
   because the point-set encoding is what supports the mono/epi
   characterizations below. *)

(** ** Spaces *)

(* A topological space: a setoid of points together with a family of open
   predicates closed under the usual operations.  The three closure fields
   [open_union]/[open_whole]/[open_inter] are the classical axioms; the two
   [open_respects]/[open_proper] fields are the setoid bookkeeping described
   in the header.  The single universe [o] is spelled out rather than
   inferred, for the reason given in the header's point 2: pinning it to one
   variable is what keeps every space an object of one and the same [Top]. *)

Record TopSpace@{o} := {
  top_carrier :> SetoidObject@{o o};    (* the setoid of points *)

  (* the topology: which predicates on the points are open *)
  IsOpen : (top_carrier → Type@{o}) → Type@{o};

  (* being open is invariant under pointwise equivalence of predicates *)
  open_respects (U V : top_carrier → Type@{o}) :
    (∀ x, U x ↔ V x) → IsOpen U → IsOpen V;

  (* every open respects the carrier's own equality on points *)
  open_proper (U : top_carrier → Type@{o}) :
    IsOpen U → ∀ x y : top_carrier, x ≈ y → U x → U y;

  (* closure under arbitrary (type-indexed) unions *)
  open_union (I : Type@{o}) (U : I → (top_carrier → Type@{o})) :
    (∀ i, IsOpen (U i)) → IsOpen (fun x => { i : I & U i x });

  (* the whole space is open *)
  open_whole : IsOpen (fun _ => poly_unit@{o});

  (* closure under binary intersection *)
  open_inter (U V : top_carrier → Type@{o}) :
    IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
}.

(* Every constant predicate is open.  Proof: the union, indexed by the type
   [P] itself, of `P`-many copies of the whole space is pointwise equivalent
   to the constant predicate `P` — the witness of membership IS an element
   of `P`.  Classically this says no more than "∅ and X are open"; here it
   is the engine behind terminality of the point and the continuity of every
   map into an indiscrete space. *)
Lemma open_const (X : TopSpace) (P : Type) : IsOpen X (fun _ => P).
Proof.
  apply (open_respects X (fun _ => { _ : P & poly_unit }) (fun _ => P)).
  - intro x; split.
    + exact (fun w => projT1 w).
    + exact (fun p => (p; ttt)).
  - apply (open_union X P (fun _ _ => poly_unit)).
    intro i; exact (open_whole X).
Qed.

(* The empty predicate is open: the union over the empty index type, which
   is the [P := False] case of [open_const]. *)
Corollary open_empty (X : TopSpace) : IsOpen X (fun _ => False).
Proof. exact (open_const X False). Qed.

(* A predicate is "uniform" when it holds at every point as soon as it holds
   at some point.  Every uniform predicate is open, being pointwise
   equivalent to the constant predicate "this predicate is inhabited
   somewhere".  Classically the uniform predicates are just ∅ and X;
   constructively they are the whole of the coarsest topology, and this
   lemma says that topology is contained in every other one. *)
Lemma open_uniform (X : TopSpace) (U : X → Type) :
  (∀ x y : X, U x → U y) → IsOpen X U.
Proof.
  intro HU.
  apply (open_respects X (fun _ => { z : X & U z }) U).
  - intro x; split.
    + intro w; exact (HU (projT1 w) x (projT2 w)).
    + intro Ux; exact (x; Ux).
  - apply open_const.
Qed.

(** ** Continuous maps *)

(* Continuity, in its categorical form: the preimage of every open is open.
   The map itself is a [SetoidMorphism], so it already respects the two
   carriers' equalities; continuity is the extra topological condition. *)
Definition Continuous (X Y : TopSpace)
           (f : SetoidMorphism (top_carrier X) (top_carrier Y)) : Type :=
  ∀ U : Y → Type, IsOpen Y U → IsOpen X (fun x => U (f x)).

(* A morphism of [Top]: a setoid map on points that is moreover continuous.
   This wraps [SetoidMorphism] exactly as [SetoidMorphism] wraps a bare
   function in Instance/Sets.v. *)
Record ContinuousMorphism (X Y : TopSpace) := {
  continuous_map :> SetoidMorphism (top_carrier X) (top_carrier Y);
  continuity : Continuous X Y continuous_map
}.

Arguments continuous_map {X Y} _.
Arguments continuity {X Y} _ _ _.

(* The hom-setoid compares only the map part, pointwise up to the codomain's
   `≈`.  The continuity witness is not compared: two continuous maps that
   agree on points are the same arrow of [Top], whatever proofs of
   continuity they happen to carry.  This is the same extensional discipline
   as [SetoidMorphism_equiv], and it is what makes [Top] a category without
   any proof-irrelevance axiom. *)
(* The universes are declared: [o] is the space's own level, [h] the level
   of the hom (strictly above [o], because [Continuous] quantifies over the
   opens of the codomain — the hom-sets of [Top] genuinely live one step up
   from its points), and [p] the level at which morphism equality is
   recorded.  The `h ≤ p` constraint is the one [Category] itself imposes;
   left to inference the relation would be minimized down to [o] and no
   longer fit a hom-setoid. *)
Definition ContinuousMorphism_equiv@{o h p | o < h, h <= p}
  {X Y : TopSpace@{o}} : crelation@{h p} (ContinuousMorphism@{h o} X Y) :=
  fun f g => ∀ x : X, continuous_map f x ≈ continuous_map g x.

Arguments ContinuousMorphism_equiv {X Y} _ _ /.

#[export]
Program Instance ContinuousMorphism_Setoid@{o h p | o < h, h <= p}
  {X Y : TopSpace@{o}} : Setoid@{h p} (ContinuousMorphism@{h o} X Y) := {|
  equiv := ContinuousMorphism_equiv@{o h p}
|}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; exact (Hfg x).
  - intros f g h Hfg Hgh x; transitivity (continuous_map g x).
    + exact (Hfg x).
    + exact (Hgh x).
Qed.

(* The identity map is continuous: the preimage of U along the identity is
   U itself, up to eta. *)
Definition top_id {X : TopSpace} : ContinuousMorphism X X := {|
  continuous_map := setoid_morphism_id;
  continuity := fun _ H => H
|}.

(* Composition: preimages compose contravariantly, so the preimage along
   `g ∘ f` of an open is the preimage along `f` of the preimage along `g`. *)
Definition top_compose {X Y Z : TopSpace}
           (g : ContinuousMorphism Y Z) (f : ContinuousMorphism X Y) :
  ContinuousMorphism X Z := {|
  continuous_map := setoid_morphism_compose g f;
  continuity := fun U H => continuity f _ (continuity g U H)
|}.

Lemma top_compose_respects {X Y Z : TopSpace} :
  Proper (equiv ==> equiv ==> equiv) (@top_compose X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  rewrite (Hg (continuous_map f1 x)).
  apply proper_morphism, Hf.
Qed.

(* The category of topological spaces and continuous maps.  The category
   laws hold pointwise on the map parts, exactly as in [Sets]; the
   continuity witnesses play no part because the hom-setoid ignores them. *)
Program Definition Top : Category := {|
  obj     := TopSpace;
  hom     := ContinuousMorphism;
  homset  := @ContinuousMorphism_Setoid;
  id      := @top_id;
  compose := @top_compose;

  compose_respects := @top_compose_respects
|}.

(** ** Two extreme topologies *)

Section Discrete.

Context (A : SetoidObject).

(* The discrete topology: EVERY predicate that respects the carrier's `≈`
   is open.  Setoid bookkeeping is the only constraint left; this is the
   finest topology on A. *)
Definition discrete_open (U : A → Type) : Type :=
  ∀ x y : A, x ≈ y → U x → U y.

Lemma discrete_respects (U V : A → Type) :
  (∀ x, U x ↔ V x) → discrete_open U → discrete_open V.
Proof.
  intros HUV HU x y Hxy Vx.
  exact (fst (HUV y) (HU x y Hxy (snd (HUV x) Vx))).
Qed.

Lemma discrete_union (I : Type) (U : I → (A → Type)) :
  (∀ i, discrete_open (U i)) → discrete_open (fun x => { i : I & U i x }).
Proof.
  intros HU x y Hxy w.
  exact (projT1 w; HU (projT1 w) x y Hxy (projT2 w)).
Qed.

Lemma discrete_whole : discrete_open (fun _ => poly_unit).
Proof. intros x y Hxy w; exact w. Qed.

Lemma discrete_inter (U V : A → Type) :
  discrete_open U → discrete_open V → discrete_open (fun x => U x ∧ V x).
Proof.
  intros HU HV x y Hxy w.
  exact (HU x y Hxy (fst w), HV x y Hxy (snd w)).
Qed.

Definition Discrete_Top : TopSpace := {|
  top_carrier    := A;
  IsOpen         := discrete_open;
  open_respects  := discrete_respects;
  open_proper    := fun _ H => H;
  open_union     := discrete_union;
  open_whole     := discrete_whole;
  open_inter     := discrete_inter
|}.

End Discrete.

Section Indiscrete.

Context (A : SetoidObject).

(* The indiscrete (coarsest) topology.  The textbook presentation is
   `{∅, X}`, but that collection is NOT closed under arbitrary unions
   constructively: given a family of members, deciding whether some member
   is the whole space (so that the union is the whole space) rather than
   all of them being empty (so that the union is empty) is precisely an
   instance of excluded middle, and no such decision is available.
   The constructive rendering keeps the UNIFORM predicates: those that hold
   everywhere as soon as they hold somewhere.  Classically the uniform
   predicates are exactly ∅ and X, so this agrees with the textbook
   definition; constructively it is closed under everything required, and
   by [open_uniform] it is contained in every topology on A — which makes
   every setoid map into an indiscrete space continuous
   ([into_indiscrete_continuous] below). *)
Definition indiscrete_open (U : A → Type) : Type :=
  ∀ x y : A, U x → U y.

Lemma indiscrete_respects (U V : A → Type) :
  (∀ x, U x ↔ V x) → indiscrete_open U → indiscrete_open V.
Proof.
  intros HUV HU x y Vx.
  exact (fst (HUV y) (HU x y (snd (HUV x) Vx))).
Qed.

Lemma indiscrete_proper (U : A → Type) :
  indiscrete_open U → ∀ x y : A, x ≈ y → U x → U y.
Proof. intros HU x y _ Ux; exact (HU x y Ux). Qed.

Lemma indiscrete_union (I : Type) (U : I → (A → Type)) :
  (∀ i, indiscrete_open (U i)) → indiscrete_open (fun x => { i : I & U i x }).
Proof.
  intros HU x y w.
  exact (projT1 w; HU (projT1 w) x y (projT2 w)).
Qed.

Lemma indiscrete_whole : indiscrete_open (fun _ => poly_unit).
Proof. intros x y w; exact w. Qed.

Lemma indiscrete_inter (U V : A → Type) :
  indiscrete_open U → indiscrete_open V →
  indiscrete_open (fun x => U x ∧ V x).
Proof.
  intros HU HV x y w.
  exact (HU x y (fst w), HV x y (snd w)).
Qed.

Definition Indiscrete_Top : TopSpace := {|
  top_carrier    := A;
  IsOpen         := indiscrete_open;
  open_respects  := indiscrete_respects;
  open_proper    := indiscrete_proper;
  open_union     := indiscrete_union;
  open_whole     := indiscrete_whole;
  open_inter     := indiscrete_inter
|}.

End Indiscrete.

(* Every setoid map into an indiscrete space is continuous.  The preimage of
   a uniform predicate is uniform, and by [open_uniform] every uniform
   predicate is open in every space. *)
Lemma into_indiscrete_continuous (X : TopSpace) (A : SetoidObject)
      (f : SetoidMorphism (top_carrier X) A) :
  Continuous X (Indiscrete_Top A) f.
Proof.
  intros U HU.
  apply open_uniform.
  intros x y Ufx.
  exact (HU (f x) (f y) Ufx).
Qed.

(* Dually, every setoid map out of a discrete space is continuous: the
   preimage of any open respects `≈` because the map does. *)
Lemma out_of_discrete_continuous (A : SetoidObject) (Y : TopSpace)
      (f : SetoidMorphism A (top_carrier Y)) :
  Continuous (Discrete_Top A) Y f.
Proof.
  intros U HU x y Hxy Ufx.
  exact (open_proper Y U HU (f x) (f y) (proper_morphism f x y Hxy) Ufx).
Qed.

(* The constant setoid map, and its respectfulness certificate.  These are
   spelled out rather than left to [Program] because instance resolution
   solves the [Proper] goal with a lemma whose universes are pinned to
   [Set], which would in turn pin the carrier universe of every space
   receiving a constant map.  Supplying the field explicitly keeps the
   construction universe-polymorphic — the discipline the header's point 2
   describes. *)
Lemma const_proper (A B : SetoidObject) (b : B) :
  Proper (respectful equiv equiv) (fun _ : A => b).
Proof. intros u v Huv; reflexivity. Qed.

Definition const_morphism (A B : SetoidObject) (b : B) : SetoidMorphism A B := {|
  morphism        := fun _ => b;
  proper_morphism := const_proper A B b
|}.

(** ** Terminal and initial objects *)

(* The one-point space.  Its carrier is the singleton setoid used by
   [Sets_Terminal]; the topology is discrete (on a one-point carrier the
   discrete and indiscrete topologies agree). *)
Definition Point_Top : TopSpace := Discrete_Top unit_setoid_object.

(* Terminality.  The unique map sends everything to the point; its
   continuity is [open_const], since the preimage of any predicate on a
   single point is a CONSTANT predicate upstairs. *)
Definition top_one (X : TopSpace) : ContinuousMorphism X Point_Top := {|
  continuous_map := const_morphism (top_carrier X) (top_carrier Point_Top) ttt;
  continuity := fun U _ => open_const X (U ttt)
|}.

(* Any two maps into the point agree, since the codomain has exactly one
   element up to `≈`. *)
Lemma top_one_unique (X : TopSpace) (f g : X ~{Top}~> Point_Top) : f ≈ g.
Proof.
  intro x.
  destruct (continuous_map f x), (continuous_map g x); reflexivity.
Qed.

#[export]
Program Instance Top_Terminal : @Terminal Top := {
  terminal_obj := Point_Top;
  one := top_one;
  one_unique := top_one_unique
}.

(* The empty space: carrier [False], every predicate open (vacuously, since
   the discrete condition quantifies over points that do not exist). *)
Definition Empty_Top : TopSpace :=
  Discrete_Top {| carrier := False; is_setoid := False_Setoid |}.

Definition empty_map (X : TopSpace) :
  SetoidMorphism (top_carrier Empty_Top) (top_carrier X).
Proof.
  refine {| morphism := fun z : False => False_rect _ z |}.
  repeat intro; contradiction.
Defined.

Definition top_zero (X : TopSpace) : ContinuousMorphism Empty_Top X.
Proof.
  refine {| continuous_map := empty_map X |}.
  intros U HU; repeat intro; contradiction.
Defined.

(* Any two maps out of the empty space agree, there being no point at which
   they could differ. *)
Lemma top_zero_unique (X : TopSpace) (f g : Empty_Top ~{Top}~> X) : f ≈ g.
Proof. intro z; contradiction. Qed.

#[export]
Program Instance Top_Initial : @Initial Top := {
  terminal_obj := Empty_Top;
  one := top_zero;
  one_unique := top_zero_unique
}.

(* [Top] has NO zero object: the terminal object has one point and the
   initial object has none, so they are not isomorphic.  Nothing below
   claims otherwise. *)

(** ** Monomorphisms are the injections *)

(* Injectivity up to `≈` characterizes the monos of [Top].  The hard
   direction probes f with the two constant maps out of the one-point
   space, exactly as [injectivity_is_monic] does in Instance/Sets.v; the
   probes are continuous by [open_const]. *)
Definition top_point (X : TopSpace) (a : X) :
  ContinuousMorphism Point_Top X := {|
  continuous_map := const_morphism (top_carrier Point_Top) (top_carrier X) a;
  continuity := fun U _ => open_const Point_Top (U a)
|}.

Theorem top_monic_iff {X Y : TopSpace} (f : X ~{Top}~> Y) :
  (∀ a b : X, f a ≈ f b → a ≈ b) ↔ Monic f.
Proof.
  split.
  - intros Hinj.
    constructor; intros Z g1 g2 Hg z.
    exact (Hinj (continuous_map g1 z) (continuous_map g2 z) (Hg z)).
  - intros [Hmonic] a b Hab.
    exact (Hmonic Point_Top (top_point X a) (top_point X b)
                  (fun _ => Hab) ttt).
Qed.

(** ** Epimorphisms are the surjections *)

(* Membership in the image, as a Type-valued sigma: the same shape
   Instance/Sets.v uses in [surjectivity_is_epic] and Lib/Setoid.v's
   [surjective] class, namely a CHOSEN preimage rather than a
   propositional truncation.  In a setoid library this is the honest
   reading — the round trip in [bijective_is_iso] recovers an actual
   inverse function from it, with no appeal to choice. *)
Definition InImage {X Y : TopSpace} (f : X ~{Top}~> Y) (b : Y) : Type :=
  ∃ a : X, f a ≈ b.

(* The image predicate respects the codomain's equality. *)
Lemma InImage_respects {X Y : TopSpace} (f : X ~{Top}~> Y) (b b' : Y) :
  b ≈ b' → InImage f b → InImage f b'.
Proof.
  intros Hbb w.
  exact (projT1 w; transitivity (projT2 w) Hbb).
Qed.

(* *** The cokernel-pair space

   The unconditional constructive proof that epis in [Top] are surjective.
   Given f : X ~> Y, glue two copies of Y along the image of f: the carrier
   is `Y + Y`, and the two copies are identified EXACTLY over the image.
   No inductive closure of a generating relation is needed — the relation
   below is already transitive, because "lies in the image" transports
   along `≈` ([InImage_respects]).  A predicate is open when it respects
   the gluing and both of its restrictions along the two legs are open in
   Y.  The two legs then agree after f, so an epi f forces the legs to be
   equal, which says precisely that every point of Y lies in the image.

   This argument is fully constructive: no decidability hypothesis, no
   choice, and — unlike the classical two-point probe recalled below and
   unlike Instance/Sets.v's truth-value object — no jump to a higher
   universe, since `Y + Y` sits at the same level as Y. *)

Section CokernelPair.

Context {X Y : TopSpace}.
Context (f : X ~{Top}~> Y).

(* The glued carrier: two copies of the points of Y. *)
Definition CP_point : Type := Datatypes.sum (carrier (top_carrier Y))
                                            (carrier (top_carrier Y)).

(* The gluing relation.  Within a copy it is Y's own equality; across the
   copies it additionally demands membership in the image of f. *)
Definition CP_rel (u v : CP_point) : Type :=
  match u, v with
  | Datatypes.inl y, Datatypes.inl y' => y ≈ y'
  | Datatypes.inr y, Datatypes.inr y' => y ≈ y'
  | Datatypes.inl y, Datatypes.inr y' => (y ≈ y') ∧ InImage f y
  | Datatypes.inr y, Datatypes.inl y' => (y ≈ y') ∧ InImage f y
  end.

Lemma CP_rel_refl : Reflexive CP_rel.
Proof. intros [y|y]; simpl; reflexivity. Qed.

Lemma CP_rel_sym : Symmetric CP_rel.
Proof.
  intros [y|y] [y'|y'] H; simpl in *.
  - now symmetry.
  - exact (symmetry (fst H), InImage_respects f y y' (fst H) (snd H)).
  - exact (symmetry (fst H), InImage_respects f y y' (fst H) (snd H)).
  - now symmetry.
Qed.

Lemma CP_rel_trans : Transitive CP_rel.
Proof.
  intros [a|a] [b|b] [c|c] H1 H2; simpl in *.
  (* inl inl inl *) - now transitivity b.
  (* inl inl inr *) - exact (transitivity H1 (fst H2),
                             InImage_respects f b a (symmetry H1) (snd H2)).
  (* inl inr inl *) - exact (transitivity (fst H1) (fst H2)).
  (* inl inr inr *) - exact (transitivity (fst H1) H2, snd H1).
  (* inr inl inl *) - exact (transitivity (fst H1) H2, snd H1).
  (* inr inl inr *) - exact (transitivity (fst H1) (fst H2)).
  (* inr inr inl *) - exact (transitivity H1 (fst H2),
                             InImage_respects f b a (symmetry H1) (snd H2)).
  (* inr inr inr *) - now transitivity b.
Qed.

Definition CP_Setoid : Setoid CP_point := {|
  equiv := CP_rel;
  setoid_equiv := Build_Equivalence CP_rel CP_rel_refl CP_rel_sym CP_rel_trans
|}.

Definition CP_carrier : SetoidObject :=
  {| carrier := CP_point; is_setoid := CP_Setoid |}.

(* A glued predicate is open when it respects the gluing and restricts to
   an open along each of the two legs. *)
Definition CP_open (W : CP_carrier → Type) : Type :=
  ((∀ u v, CP_rel u v → W u → W v)
     ∧ IsOpen Y (fun y => W (Datatypes.inl y))
     ∧ IsOpen Y (fun y => W (Datatypes.inr y)))%type.

Lemma CP_respects (W W' : CP_carrier → Type) :
  (∀ u, W u ↔ W' u) → CP_open W → CP_open W'.
Proof.
  intros HW HO.
  refine (_, (_, _)).
  - intros u v Huv W'u.
    exact (fst (HW v) (fst HO u v Huv (snd (HW u) W'u))).
  - exact (open_respects Y _ _ (fun y => HW (Datatypes.inl y)) (fst (snd HO))).
  - exact (open_respects Y _ _ (fun y => HW (Datatypes.inr y)) (snd (snd HO))).
Qed.

Lemma CP_proper (W : CP_carrier → Type) :
  CP_open W → ∀ u v : CP_carrier, u ≈ v → W u → W v.
Proof. intros HO u v Huv; exact (fst HO u v Huv). Qed.

Lemma CP_union (I : Type) (W : I → (CP_carrier → Type)) :
  (∀ i, CP_open (W i)) → CP_open (fun u => { i : I & W i u }).
Proof.
  intro HW.
  refine (_, (_, _)).
  - intros u v Huv w.
    exact (projT1 w; fst (HW (projT1 w)) u v Huv (projT2 w)).
  - exact (open_union Y I (fun i y => W i (Datatypes.inl y))
                      (fun i => fst (snd (HW i)))).
  - exact (open_union Y I (fun i y => W i (Datatypes.inr y))
                      (fun i => snd (snd (HW i)))).
Qed.

Lemma CP_whole : CP_open (fun _ => poly_unit).
Proof. exact (fun _ _ _ w => w, (open_whole Y, open_whole Y)). Qed.

Lemma CP_inter (W W' : CP_carrier → Type) :
  CP_open W → CP_open W' → CP_open (fun u => W u ∧ W' u).
Proof.
  intros HO HO'.
  refine (_, (_, _)).
  - intros u v Huv w.
    exact (fst HO u v Huv (fst w), fst HO' u v Huv (snd w)).
  - exact (open_inter Y _ _ (fst (snd HO)) (fst (snd HO'))).
  - exact (open_inter Y _ _ (snd (snd HO)) (snd (snd HO'))).
Qed.

Definition CokernelPair : TopSpace := {|
  top_carrier   := CP_carrier;
  IsOpen        := CP_open;
  open_respects := CP_respects;
  open_proper   := CP_proper;
  open_union    := CP_union;
  open_whole    := CP_whole;
  open_inter    := CP_inter
|}.

(* The two legs.  Each is a setoid map by construction (within a copy the
   gluing relation IS Y's equality), and continuous because the two
   restriction conditions are literally the second and third components of
   [CP_open]. *)
Definition CP_inl : SetoidMorphism (top_carrier Y) CP_carrier.
Proof.
  refine {| morphism := Datatypes.inl |}.
  intros u v Huv; exact Huv.
Defined.

Definition CP_inr : SetoidMorphism (top_carrier Y) CP_carrier.
Proof.
  refine {| morphism := Datatypes.inr |}.
  intros u v Huv; exact Huv.
Defined.

Definition CP_leftLeg : ContinuousMorphism Y CokernelPair :=
  Build_ContinuousMorphism Y CokernelPair CP_inl (fun W HW => fst (snd HW)).

Definition CP_rightLeg : ContinuousMorphism Y CokernelPair :=
  Build_ContinuousMorphism Y CokernelPair CP_inr (fun W HW => snd (snd HW)).

(* The defining coequalizing property: the legs agree after f, because at a
   point of the image the gluing relation holds — witnessed by the very
   preimage that puts the point in the image. *)
Lemma CP_legs_agree :
  CP_leftLeg ∘[Top] f ≈ CP_rightLeg ∘[Top] f.
Proof.
  intro a; simpl.
  refine (_, _).
  - reflexivity.
  - refine (a; _); reflexivity.
Qed.

End CokernelPair.

(* Epimorphisms of [Top] are exactly the surjections, unconditionally.

   Forward: a surjection is right-cancellable pointwise.  Backward: apply
   the epi to the two legs of the cokernel-pair space, which agree after f
   by [CP_legs_agree]; the resulting equality of legs says that for every
   b the glued points `inl b` and `inr b` are related, and by construction
   that relation carries a preimage of b. *)
Theorem top_epic_iff {X Y : TopSpace} (f : X ~{Top}~> Y) :
  (∀ b : Y, ∃ a : X, f a ≈ b) ↔ Epic f.
Proof.
  split.
  - intros Hsurj.
    constructor; intros Z g1 g2 Hg b.
    destruct (Hsurj b) as [a Ha].
    rewrite <- Ha.
    exact (Hg a).
  - intros [Hepic] b.
    exact (snd (Hepic (CokernelPair f) (CP_leftLeg f) (CP_rightLeg f)
                      (CP_legs_agree f) b)).
Qed.

(* The same statement in cokernel-pair form, naming the construction that
   does the work. *)
Theorem top_epic_surjective_via_cokernel_pair
        {X Y : TopSpace} (f : X ~{Top}~> Y) :
  Epic f → ∀ b : Y, InImage f b.
Proof. intro He; exact (snd (top_epic_iff f) He). Qed.

(** ** The classical two-point probe, and its constructive status *)

(* The textbook proof that epis of Top are surjective probes f with two maps
   into the two-point INDISCRETE space — not the Sierpinski space, whose
   topology `{∅, {1}, Z}` characterizes DENSE images rather than surjective
   ones: the constant map at [true] and the characteristic map of the image.
   The
   two agree after f, so an epi makes them equal, and evaluating at b says b
   is in the image.

   Constructively the characteristic map is the obstruction: forming
   `fun b => if b ∈ im f then true else false` requires DECIDING image
   membership, which is exactly the hypothesis [dec] below.  So this route
   is hypothesis-scoped.  The unconditional theorem is
   [top_epic_surjective_via_cokernel_pair] above, which replaces the
   two-element codomain by the cokernel-pair space and needs no decision
   procedure at all; that contrast is the documented constructive status of
   the classical argument.  (The corresponding obstruction in
   Instance/Sets.v is different in kind: there the classical probe needs a
   truth-value object one universe up, so the reverse direction of
   [surjectivity_is_epic] is left out of the environment entirely and the
   cross-universe statements live in Instance/Sets/Classifier.v.) *)

Definition bool_setoid_object : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := @eq bool; setoid_equiv := eq_equivalence |}
|}.

(* The two-point indiscrete space used as the probe.  Every setoid map into
   it is continuous ([into_indiscrete_continuous]), which is the only
   property of it the argument uses. *)
Definition TwoPoint_Indiscrete : TopSpace := Indiscrete_Top bool_setoid_object.

Section IndiscreteProbe.

Context {X Y : TopSpace}.
Context (f : X ~{Top}~> Y).
Context (dec : ∀ b : Y, InImage f b ∨ ¬ (InImage f b)).

(* The characteristic function of the image, read off the decision. *)
Definition image_char (b : Y) : bool :=
  match dec b with
  | Datatypes.inl _ => true
  | Datatypes.inr _ => false
  end.

Definition image_char_setoid_map :
  SetoidMorphism (top_carrier Y) bool_setoid_object.
Proof using X Y dec f.
  refine {| morphism := image_char |}.
  intros b b' Hbb; unfold image_char.
  destruct (dec b) as [w|n], (dec b') as [w'|n'].
  - reflexivity.
  - destruct (n' (InImage_respects f b b' Hbb w)).
  - destruct (n (InImage_respects f b' b (symmetry Hbb) w')).
  - reflexivity.
Defined.

Definition image_char_map : ContinuousMorphism Y TwoPoint_Indiscrete :=
  Build_ContinuousMorphism Y TwoPoint_Indiscrete image_char_setoid_map
    (into_indiscrete_continuous Y bool_setoid_object image_char_setoid_map).

Definition always_true_setoid_map :
  SetoidMorphism (top_carrier Y) bool_setoid_object :=
  const_morphism (top_carrier Y) bool_setoid_object true.

Definition always_true_map : ContinuousMorphism Y TwoPoint_Indiscrete :=
  Build_ContinuousMorphism Y TwoPoint_Indiscrete always_true_setoid_map
    (into_indiscrete_continuous Y bool_setoid_object always_true_setoid_map).

(* The classical route, made honest: under [dec], an epi is surjective. *)
Theorem top_epic_surjective_via_indiscrete :
  Epic f → ∀ b : Y, InImage f b.
Proof using X Y dec f.
  intros [Hepic] b.
  assert (Hagree : always_true_map ∘[Top] f ≈ image_char_map ∘[Top] f).
  { intro a; simpl; unfold image_char.
    destruct (dec (continuous_map f a)) as [w|n].
    - reflexivity.
    - exfalso; apply n; refine (a; _); reflexivity. }
  pose proof (Hepic TwoPoint_Indiscrete always_true_map image_char_map Hagree b)
    as Heq.
  simpl in Heq; unfold image_char in Heq.
  destruct (dec b) as [w|n].
  - exact w.
  - discriminate Heq.
Qed.

End IndiscreteProbe.

(** ** Open covers *)

(* Fong and Spivak, "Seven Sketches in Compositionality", §7.3.2,
   Definition 7.25: a family of opens covers a set when the set is the union
   of the family.  Stated here at the level of predicates: the covered
   predicate is pointwise equivalent to the union of the family, and every
   member of the family is open. *)
Definition Covers {X : TopSpace} {I : Type}
           (U : I → (X → Type)) (V : X → Type) : Type :=
  ((∀ i, IsOpen X (U i)) ∧ (∀ x : X, V x ↔ ∃ i : I, U i x))%type.

(* The empty family covers the empty predicate — the nullary instance of the
   definition: with no members the union is empty, so what the family covers
   is exactly the empty predicate. *)
Definition covers_nothing (X : TopSpace) :
  Covers (X:=X) (I:=False) (fun _ _ => False) (fun _ => False).
Proof.
  split.
  - intro i; contradiction.
  - intro x; split.
    + contradiction.
    + intro w; exact (projT2 w).
Defined.

(* The one-member family consisting of the whole space covers the whole
   space. *)
Definition covers_whole (X : TopSpace) :
  Covers (X:=X) (I:=poly_unit) (fun _ _ => poly_unit) (fun _ => poly_unit).
Proof.
  split.
  - intro i; exact (open_whole X).
  - intro x; split.
    + intro w; exact (ttt; w).
    + intro w; exact (projT2 w).
Defined.

(** ** Separation and compactness *)

(* Hausdorff (T2): distinct points are separated by disjoint opens.  This is
   the literal classical separation axiom, with "distinct" rendered as
   `¬ (x ≈ y)` (apartness in the carrier's own equality) and the existential
   as a Σ-type carrying the two chosen opens.  A constructive topologist
   would usually prefer a positive apartness relation; that refinement is
   out of scope here, where the work order asks only for the definition. *)
Definition IsHausdorff (X : TopSpace) : Type :=
  ∀ x y : X, ¬ (x ≈ y) →
    ∃ U : X → Type, ∃ V : X → Type,
      ((IsOpen X U ∧ IsOpen X V)
         ∧ (U x ∧ V y)
         ∧ (∀ z : X, U z → V z → False))%type.

(* Compactness of the WHOLE space: every open cover of the whole space has a
   finite subcover, presented as a list of indices together with, for each
   point, a member of that list covering it.  The finiteness is the list;
   the choice of index for each point is data, as everywhere in this
   library. *)
Definition IsCompact (X : TopSpace) : Type :=
  ∀ (I : Type) (U : I → (X → Type)),
    Covers U (fun _ => poly_unit) →
    ∃ l : list I, ∀ x : X, ∃ i : I, (List.In i l ∧ U i x)%type.

(* Non-vacuity: the one-point space satisfies both predicates, so neither
   subcategory below is empty.  Compactness is witnessed by the singleton
   list containing the index that covers the point; the separation axiom is
   satisfied vacuously, there being no pair of distinct points to
   separate — exactly the classical situation. *)
Lemma Point_Compact : IsCompact Point_Top.
Proof.
  intros I U HU.
  destruct (fst (snd HU ttt) ttt) as [i Hi].
  refine (Datatypes.cons i Datatypes.nil; _).
  intro x; destruct x.
  refine (i; _); split.
  - left; reflexivity.
  - exact Hi.
Qed.

Lemma Point_Hausdorff : IsHausdorff Point_Top.
Proof.
  intros x y Hxy; destruct x, y.
  exfalso; apply Hxy; reflexivity.
Qed.

(* The full subcategory of Hausdorff spaces.  [shom] retains every
   continuous map, so closure under identity and composition is trivial —
   the same shape as [Sheaves_sub] in Theory/Sheaf/Category.v and
   [Models_sub] in Theory/Lawvere/Model.v. *)
Definition Hausdorff_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => IsHausdorff X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition HausdorffSpaces : Category := Sub Top Hausdorff_Subcategory.

Lemma Hausdorff_Full :
  Category.Construction.Subcategory.Full Top Hausdorff_Subcategory.
Proof. intros x y ox oy g; exact I. Qed.

(* The full subcategory of compact Hausdorff spaces.  Only the definition is
   provided: the deeper theory (that compact Hausdorff spaces are closed
   under continuous images, that a continuous bijection out of a compact
   space into a Hausdorff space is a homeomorphism, monadicity over Sets)
   is out of scope for this file. *)
Definition CompactHausdorff_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => (IsCompact X ∧ IsHausdorff X)%type)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition CompactHausdorffSpaces : Category :=
  Sub Top CompactHausdorff_Subcategory.

Lemma CompactHausdorff_Full :
  Category.Construction.Subcategory.Full Top CompactHausdorff_Subcategory.
Proof. intros x y ox oy g; exact I. Qed.
