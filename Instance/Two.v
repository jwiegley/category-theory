Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The interval category 2 (the "walking arrow"). *)

(* nLab:      https://ncatlab.org/nlab/show/interval+category
   nLab:      https://ncatlab.org/nlab/show/walking+structure (walking morphism)
   Wikipedia: https://en.wikipedia.org/wiki/Posetal_category

   2 is the ordinal {0 < 1} regarded as a (thin / posetal) category: two
   objects 0, 1, their identities, and a single non-identity arrow 0 → 1.
   There is NO arrow 1 → 0.  Here the objects are named TwoX (= 0) and
   TwoY (= 1), and the non-identity arrow is TwoXY : TwoX ~> TwoY.

   2 is the "walking arrow": a functor 2 ⟶ C is exactly a choice of one
   morphism of C (the image of TwoXY), so functors out of 2 classify the
   morphisms of C, and the functor category [2, C] is the arrow category of
   C (objects = arrows of C, morphisms = commutative squares).  Both halves
   of that sentence are theorems in Theory/Shapes.v: [Walk] and [arrow_of]
   with their round trips for the first, and [Two_Fun_Arrow] for the
   second, the latter an equivalence of categories in the sense of
   Instance/Cat.v rather than an isomorphism of categories. *)

(* The smallest non-trivial shape, and the smallest object of truth values

   nLab:      https://ncatlab.org/nlab/show/diagram
   nLab:      https://ncatlab.org/nlab/show/walking+morphism
   nLab:      https://ncatlab.org/nlab/show/walking+structure
   Paper:     Lawvere, "Metric spaces, generalized logic, and closed
              categories", Rendiconti del Seminario Matematico e Fisico
              di Milano XLIII, 1973
   Paper:     Foltz, Lair, Kelly, "Algebraic categories with few
              monoidal biclosed structures or none", J. Pure Appl.
              Algebra 17(2), 1980

   Two readings of [_2] run through the library, and the header above
   states the first of them.  In one it is a SHAPE, the diagram over which
   a construction is taken; in the other it is an object of TRUTH VALUES,
   the base over which enrichment produces preorders.  Both readings turn
   on the same property, that [_2] is thin.

   As a shape, [_2] is the smallest non-trivial one, and the arrow-category
   identification recorded above is the first entry in a longer list.  A
   diagram of shape J in a category C is a functor from J to C; the
   category J is its shape, index, or scheme, and a limit or colimit is a
   universal cone over such a functor, presented through the diagonal
   functor of Functor/Diagonal.v (nLab, "diagram"; Mac Lane, Categories
   for the Working Mathematician, 2nd ed., 1998).  The shape isolates the
   combinatorial pattern of a construction from the category in which it is
   instantiated, and the small shapes together account for the finite
   limits and colimits: the walking parallel pair [Parallel]
   (Instance/Parallel.v) for equalizers and coequalizers, the walking span
   [Roof] (Instance/Roof.v) for pushouts and pullbacks, the discrete pair
   [Two_Discrete] (Instance/Two/Discrete.v) for binary products and
   coproducts, and the empty shape [_0] (Instance/Zero.v) for terminal and
   initial objects, with the point [_1] (Instance/One.v) the trivial
   one-object shape.

   The name "walking arrow" belongs to a settled family of synonyms.  The
   nLab records walking, free-standing, and free-living for the one idea,
   attributes "walking" to James Dolan, and traces "free-living" to Foltz,
   Lair and Kelly (1980); the governing principle is that the walking X
   coclassifies X, so that functors OUT OF it are exactly the X-structures
   of the target.  The arrow-category reading above is that principle taken
   at a single morphism.

   The second reading regards [_2] as the two-element order {TwoX < TwoY}
   with meet for tensor and the top [TwoY] for unit.  Lawvere, dating the
   observation to a 1967 lecture of Richard Swan, drew the analogy between
   the composition of hom-objects and the triangle inequality and read off
   its consequences by varying the base: over [_2] enrichment produces
   preorders, over the interval [0, ∞] it produces metric spaces (Lawvere,
   1973).  The library carries the first case in full.
   Instance/Two/Monoidal.v places the cartesian monoidal structure
   [Two_Monoidal] on [_2] (tensor the meet [two_meet], unit the top
   [TwoY]), and Construction/Enriched/Two.v then proves categories enriched
   over it to be preorders and enriched functors to be monotone maps
   ([Enriched_Two_preorder], [EnrichedFunctor_Two_monotone]).  The move is
   from asking whether an arrow x ⟶ y exists to asking whether x ≤ y holds.

   [_2] carries two further identities.  It is the directed interval: the
   canonical interval object of Cat, the 1-simplex, the 1-globe, and the
   first oriental, so that a natural transformation between two functors
   from C to D is a functor from C ∏ [_2] to D, a directed homotopy (nLab,
   "walking morphism").  And it underlies a decategorified logic: thin
   categories are exactly those enriched over the Boolean algebra [_2] as a
   cartesian monoidal category, a Heyting algebra is a skeletal thin
   finitely-cocomplete cartesian-closed category, and a Boolean algebra a
   skeletal thin finitely-cocomplete star-autonomous one (Wikipedia,
   "Posetal category").  That [_2] itself is skeletal is [Two_Skeletal]
   (Theory/Skeleton/Separation.v).

   Computationally, thinness means the hom is proof-irrelevant, a mere
   proposition, so [_2] is a (0,1)-category.  Instance/Two/Monoidal.v makes
   this concrete: [Two_thin] below says any two parallel arrows coincide
   (Instance/Two/Monoidal.v's [two_thin] is now that lemma re-exported), which
   discharges every coherence obligation uniformly and is why the strict
   [Morphism_equality] setoid recorded above suffices.  Two consequences
   follow.  A functor out of [_2] materializes one morphism together with
   its endpoints, as [_2_as_Set] does by carrying [TwoXY] to the empty
   function from False to True.  And an enrichment over [_2] must compute a
   truth value, an object of [_2], for each pair of objects, which is why
   Construction/Enriched/Two.v carries a decidable, Type-valued order: the
   constructive reading of whether x ≤ y holds. *)

Inductive TwoObj : Set := TwoX | TwoY.

Inductive TwoHom : TwoObj → TwoObj → Set :=
  | TwoIdX : TwoHom TwoX TwoX
  | TwoIdY : TwoHom TwoY TwoY
  | TwoXY  : TwoHom TwoX TwoY.

Definition TwoHom_inv_t : ∀ x y, TwoHom x y → Prop.
Proof.
  intros [] [] f.
  - exact (f = TwoIdX).
  - exact (f = TwoXY).
  - exact False.          (* Unused, any Prop is ok here *)
  - exact (f = TwoIdY).
Defined.

Corollary TwoHom_inv x y f : TwoHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma TwoHom_Y_X_absurd : TwoHom TwoY TwoX → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoHom_Y_X_absurd : two_laws.

Local Set Warnings "-intuition-auto-with-star".

(* The category 2 has two objects TwoX, TwoY, their identity morphisms, and
   one non-identity morphism TwoXY : TwoX ~> TwoY from the first to the
   second.  The hom-sets carry strict (Leibniz) equality via
   Morphism_equality, since 2 is thin (at most one arrow between objects). *)

Program Definition _2 : Category := {|
  obj     := TwoObj;
  hom     := TwoHom;
  homset  := Morphism_equality;
  id      := fun x => match x with
    | TwoX => TwoIdX
    | TwoY => TwoIdY
    end;
  compose := fun x y z (f : TwoHom y z) (g : TwoHom x y) =>
    match x, y, z with
    | TwoX, TwoX, TwoX => TwoIdX
    | TwoY, TwoY, TwoY => TwoIdY
    | TwoX, TwoX, TwoY => TwoXY
    | TwoX, TwoY, TwoY => TwoXY
    | _,    _,    _    => _
    end
|}.
Next Obligation. destruct x, y, z; intuition; auto with *. Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition; auto with *. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition. Qed.

(* ------------------------------------------------------------------------ *)
(** ** A bimorphism that is not an isomorphism *)

(* Mac Lane, CWM 2nd ed., §I.5 Exercise 3: there are categories carrying an
   arrow that is both monic and epic yet has no inverse, so "bimorphic ⇒ iso"
   -- the property called BALANCEDness (nLab: balanced category) -- is not a
   theorem of category theory.  [Bimorphic] is defined in Theory/Morphisms.v
   and, before this, was never instantiated anywhere in the tree, so the
   library had no witness that the notion is even inhabited, let alone that it
   is strictly weaker than invertibility.

   The interval category 2 supplies the cheapest one.  [TwoXY] is monic and
   epic for the same degenerate reason -- 2 is thin, so any two parallel
   arrows are equal outright -- and it is not invertible because there is no
   arrow TwoY ~> TwoX at all ([TwoHom_Y_X_absurd]).

   Balancedness is a property of particular categories rather than of the
   notion of arrow, and 2 is a category where it does not hold.  For the
   contrast, [Sets] IS balanced in tree: [Sets_balanced]
   (Instance/Sets.v) assembles [Monic f -> Epic f -> IsIsomorphism f] from
   [injectivity_is_monic] and [epic_implies_surjective] via [bijective_is_iso].
   An earlier revision of this comment said the second half was unavailable --
   "the direction abandoned at Instance/Sets.v:476" -- and that was true when
   written; it was proved subsequently.  So the contrast is genuine and
   sharper than first stated: [2] is not balanced while [Sets] is. *)

Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.

(* Any two parallel arrows of 2 agree: the category is thin. *)
Lemma Two_thin {x y : TwoObj} (f g : x ~{_2}~> y) : f ≈ g.
Proof.
  destruct x, y.
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
  - contradiction (TwoHom_Y_X_absurd f).
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
Qed.

Definition TwoXY_monic : @Monic _2 TwoX TwoY TwoXY.
Proof. constructor; intros z g1 g2 _; apply Two_thin. Qed.

Definition TwoXY_epic : @Epic _2 TwoX TwoY TwoXY.
Proof. constructor; intros z g1 g2 _; apply Two_thin. Qed.

Definition TwoXY_bimorphic : @Bimorphic _2 TwoX TwoY TwoXY :=
  (TwoXY_epic, TwoXY_monic).

(* But it has no inverse: an inverse would be an arrow TwoY ~> TwoX. *)
Lemma TwoXY_not_iso : @IsIsomorphism _2 TwoX TwoY TwoXY → False.
Proof. intros [g _ _]; exact (TwoHom_Y_X_absurd g). Qed.

(* The exercise, packaged: 2 is not balanced. *)
Definition two_bimorphic_not_iso :
  @Bimorphic _2 TwoX TwoY TwoXY * (@IsIsomorphism _2 TwoX TwoY TwoXY → False) :=
  (TwoXY_bimorphic, TwoXY_not_iso).


(* Mac Lane, CWM 2nd ed., §I.5, printed p. 19.  CITED BY LOCATION; the printed
   text was not consulted.  The in-tree catalog entry for the item
   (doc/plan/books/maclane/inventory/I.json, id maclane:I.5:def5) records the
   aside that an arrow with a right inverse is epi, and that the converse
   holds in Set but not in Grp (paraphrased, not quoted).

   Mac Lane's own counterexample is out of reach in this tree, which has no
   category of groups.  Structure/Group.v defines group OBJECTS in a
   cartesian monoidal category, not Grp.  Instance/Comp.v comes closest and
   still misses: it has a TYPE of groups ([Group], :382, algebras for the
   group signature and its equations, :268) and a CATEGORY [Algs] (:151), but
   the objects of [Algs] are [OpAlgebra S] -- structures for a signature with
   the equations dropped -- so instantiating it at the group signature does
   not produce Grp.  Categories of algebras the tree does have, several of
   them: [Models T C] for a Lawvere theory (Theory/Lawvere/Model.v:77),
   [OperadAlgebras] for an operad (Theory/Multicategory/Algebra.v:417),
   [FAlg F] for an endofunctor (Construction/FAlg.v:114), [Algs] again, and
   the commutative monoids of Instance/CMon.v, which is the one carried far
   enough to serve as the tree's semiadditive witness.  None of them is Grp,
   and none is instantiated at the group signature anywhere in the tree:
   [GroupOp] (Instance/Comp.v:298) is used to build the TYPE [Group] (:382)
   and the single algebra [BoolOp] (:395), never the category [Algs] and
   never a Lawvere theory.

   The interval category gives a blunter counterexample, for the same reason
   it refutes balancedness above: [TwoXY] is epic, and there is no arrow
   TwoY ~> TwoX at all, so nothing can serve as a right inverse.  The same
   observation rules out regularity in the sense of Theory/Morphisms.v, since
   a pseudoinverse for [TwoXY] would also have to be an arrow TwoY ~> TwoX.
   So [RegularMorphism] is a real condition on an arrow: it is not satisfied
   by every arrow of every category, and in particular not by every
   epimorphism.

   Both halves of the witness are degenerate, and both degeneracies are worth
   naming.  [TwoXY] is epic because 2 is THIN, so [TwoXY_epic] proves nothing
   about cancellation; and it is non-regular because the reverse hom-set is
   EMPTY, so [TwoXY_not_regular] proves nothing about pseudoinverses.  The
   tree's other refutation of regularity has the same shape --
   [finset_empty_to_one_not_regular] (Instance/FinSet/Regular.v) again has an
   empty reverse hom-set -- and that is not a coincidence to be corrected by
   looking harder.  Over [Sets] the empty hom-set is what makes such a
   refutation available at all: [sets_coarsen_not_regular_absurd]
   (Instance/Sets/Regular.v) exhibits an arrow with INHABITED domain and
   INHABITED reverse hom-set whose non-regularity is refutable outright, its
   regularity being exactly the decidability of an arbitrary proposition
   ([sets_coarsen_regular_iff_dec]).  Where that proposition is undecided,
   neither answer can be proved, so the degeneracy above is a fact about the
   setting rather than a shortcut taken here. *)

Lemma TwoXY_not_regular : @RegularMorphism _2 TwoX TwoY TwoXY → False.
Proof. intros [g _]; exact (TwoHom_Y_X_absurd g). Qed.

(* Both one-sided splittings are ruled out through regularity, rather than by
   repeating the argument: a section or a retraction is regular. *)
Lemma TwoXY_not_retraction : @Retraction _2 TwoX TwoY TwoXY → False.
Proof. intro R; exact (TwoXY_not_regular (regular_of_retraction _ R)). Qed.

Lemma TwoXY_not_section : @Section _2 TwoX TwoY TwoXY → False.
Proof. intro S; exact (TwoXY_not_regular (regular_of_section _ S)). Qed.

(* Packaged: an arrow that is epic, does not split, and is not regular. *)
Definition two_epic_not_regular :
  @Epic _2 TwoX TwoY TwoXY
  * (@Retraction _2 TwoX TwoY TwoXY → False)
  * (@RegularMorphism _2 TwoX TwoY TwoXY → False) :=
  (TwoXY_epic, TwoXY_not_retraction, TwoXY_not_regular).


Require Import Category.Instance.Sets.

(* A functor 2 ⟶ Sets is precisely a morphism of Sets; this one picks out the
   unique map (the empty function) from False to True, sending TwoXY there. *)

Program Definition _2_as_Set : _2 ⟶ Sets := {|
  fobj := fun x =>
    match x with
    | TwoX => {| carrier := False |}
    | TwoY => {| carrier := True |}
    end;
  fmap := fun x y f =>
    match x, y with
    | TwoY, TwoY => _
    | _, _       => _
    end
|}.
Next Obligation.
  construct.
  - repeat intro.
    contradiction.
  - equivalence.
Defined.
Next Obligation.
  construct.
  - repeat intro.
    exact True.
  - equivalence.
Defined.
Next Obligation.
  construct; auto.
Defined.
Next Obligation.
  construct; auto.
  - destruct x, y; simpl in *; auto with two_laws.
  - proper.
    destruct x, y; simpl in *; auto with two_laws.
Qed.
Next Obligation.
  destruct x; simpl in *; auto with two_laws.
  contradiction.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; auto with two_laws.
  contradiction.
Qed.
