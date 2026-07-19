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
   C (objects = arrows of C, morphisms = commutative squares). *)

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
   "Posetal category").

   Computationally, thinness means the hom is proof-irrelevant, a mere
   proposition, so [_2] is a (0,1)-category.  Instance/Two/Monoidal.v makes
   this concrete: [two_thin] says any two parallel arrows coincide, which
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
