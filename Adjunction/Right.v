(** * Adjoint on the right: pairs of contravariant functors *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.

(* NOTATION GUARD, and it is REQUIRED rather than defensive -- measured:
   deleting the line below makes this file FAIL to compile.  Three
   scopes declare [_ ^op] (category, functor and adjunction), and
   Category.Functor.Opposite together with Category.Adjunction.Opposite
   open theirs, so a bare [C^op] can parse as the wrong one.  Delete the
   [Open Scope] and the result-type ascription of
   [Adjunction_of_AdjointOnTheRight] is rejected with [The term "A" has
   type "Category" while it is expected to have type "?F ⊣ ?U"]:
   [adjunction_scope]'s [_^op] wins there.  So an argument position is
   NOT rescued by [Bind Scope category_scope with Category] -- a sibling
   file reports the opposite for its own contents, and that reading does
   not transfer here.  The other
   half of the hazard is NOT defensive and is obeyed throughout: [T^op]
   for a FUNCTOR is written [Opposite_Functor T] by name, since under
   these imports the bare spelling is fragile.  Same family as the guards
   in Theory/Universal/Arrow/Dual.v and Structure/Limit/Constant.v. *)
Open Scope category_scope.

Generalizable All Variables.

(* Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          §IV.2 Definition 2, printed p. 89 (maclane:IV.2:def2), where the
          notion is attributed to Freyd
   Book:  Riehl, "Category Theory in Context", §4.4
   nLab:  https://ncatlab.org/nlab/show/mutually+left+adjoint+functors
   nLab:  https://ncatlab.org/nlab/show/adjoint+functor
   nLab:  https://ncatlab.org/nlab/show/opposite+category

   Mac Lane's §IV.2 Definition 2 says that a pair of CONTRAVARIANT
   functors S : A ⟶ X and T : X ⟶ A is ADJOINT ON THE RIGHT when there
   is a bijection

       A(a, T x)  ≅  X(x, S a)

   natural in both variables.  Everything sits on the right of the two
   hom-sets -- hence the name -- and the pair is symmetric in S and T:
   reading the bijection backwards exhibits T and S adjoint on the right
   in the other order.  The dual notion, with both objects on the LEFT
   (X(S a, x) ≅ A(T x, a)), is "adjoint on the left"; Riehl §4.4 calls the
   two "mutually right adjoint" and "mutually left adjoint".  The
   contravariant power set is the canonical example, and it is built
   below: a map a → P(x) and a map x → P(a) are both just a relation
   between a and x, so the bijection is the flip of a relation.

   PRIOR ART, MEASURED.  The notion was genuinely absent.  Tree-wide,
   [rg] for `adjoint on the right`, `AdjointOnTheRight`, and
   `mutually (right|left) adjoint` returned ZERO hits before this file,
   and Adjunction/Right.v did not exist.  The catalogue issue's citation
   of the ordinary class as Theory/Adjunction.v:130 is off by three --
   :129 and :130 are the two [Reserved Notation] lines for ⌊-⌋ and ⌈-⌉,
   and [Class Adjunction] begins at :133.  The drift is minor and the
   class is real; it is recorded here only so that a later reader
   checking the citation is not misled into thinking the class moved.

   WHAT THE DEFINITION IS, AND WHY IT IS NOT AN ABBREVIATION.  Because a
   contravariant functor A ⟶ X is here a functor A^op ⟶ X, and because
   hom-reversal is DEFINITIONAL in this library -- [a ~{A}~> T x] IS
   [T^op x ~{A^op}~> a] on the nose -- the bijection above can be READ as
   an ordinary adjunction T^op ⊣ S between A^op and X.  That reading is
   proved below, both ways and in both orientations.  It is NOT, however,
   how the class is stated: [AdjointOnTheRight] is its own record,
   carrying the family of hom-set isomorphisms together with FOUR
   separate naturality laws written in the vocabulary of A and X, with no
   opposite category and no [Opposite_Functor] WRITTEN in any field type.
   A consumer writes [fmap[S] g] and [fmap[T] k] and never meets an op.
   Read that at exactly its strength: [Print] does DISPLAY the second
   binder of [aor] as [x : obj[X^op]], because [T]'s domain is [X^op] --
   but [obj_op_is_obj] pins [obj[X^op] = obj[X]] at [eq_refl], so the
   displayed op is a rendering artifact and not content.

   That the two are DIFFERENT TYPES is guarded, not merely asserted:
   three TYPING negatives are pinned below, each stripped and read in
   full, each a plain type mismatch with no [cannot unify] and no
   universe clause.  The FIRST TWO are the ones about the ordinary
   adjunction, reporting ("The term H has type T^op ⊣ S while it is
   expected to have type AdjointOnTheRight S T") and its converse; the
   THIRD is a different claim -- that the right-hand and left-hand
   classes are not definitionally equal to each other -- and reports
   [AdjointOnTheRight S T] against [AdjointOnTheLeft S T].

   The reduction is nevertheless cheap, and that is the file's main
   structural finding: all SIX passages between the two contravariant
   classes and the ordinary [Adjunction] -- four unprimed, two primed --
   are supplied by [:=] with NO TACTIC, as are the two two-sided
   exchange passages besides.  For the four UNPRIMED passages each field
   of one record is a field of the other at permuted arguments; the two
   PRIMED ones additionally insert [iso_sym], since they present the
   inverse bijection.  All eight remain tactic-free; and all six
   round trips hold at [eq_refl]
   on the WHOLE RECORD, both records having primitive projections with
   eta.  Note the ORIENTATION, which is easy to get
   backwards: for Mac Lane's A(a, T x) ≅ X(x, S a) the matching ordinary
   adjunction is T^op ⊣ S, not S^op ⊣ T; the latter is the same data read
   through the inverse bijection, and is delivered as the primed second
   orientation, which [aor_second_orientation_is_opposite] identifies
   with [Opposite_Adjunction] of the first, at [eq_refl].

   MAC LANE'S WARNING IS DISCHARGED AS A THEOREM, NOT A HEADER NOTE.
   Adjointness on the right does not imply adjointness on the left.
   [right_does_not_imply_left] and [right_does_not_imply_left_in_Sets]
   refute the implication outright, each by exhibiting ONE pair that has
   the right-hand bijection and provably has no left-hand one.  Two
   independent witnesses are shipped, and the choice is explained rather
   than left to taste.  (i) An antitone Galois connection on a
   three-element chain: cheap (its half of the closure is
   Instance/Proset.v), NON-DEGENERATE by proof -- [chain3_s_not_monotone]
   and [chain3_t_not_monotone] show that in a thin category, where a
   functor IS a monotone map, NEITHER object map is the object map of any
   COVARIANT functor, so contravariance is genuinely exercised -- and
   free of any [Set] in its constraint block.  (ii) Mac Lane's own
   example, the contravariant power set on [Sets], over
   Instance/Sets/Powerset/Universal.v's single-universe
   [Powerset_Prop_op]: here the bijection IS the flip of a relation, and
   [powerset_aor_is_flip] pins that at [eq_refl] --
   [to aor f e v = f v e] -- while all four naturality fields and both
   iso laws discharge by [reflexivity], the preimage description of
   [fmap] making the two sides the same term.  A third witness (a
   constant functor on the walking arrow) was built during scouting and
   is DELIBERATELY NOT SHIPPED: it is degenerate -- the same data is also
   a covariant functor, machine-checked out of tree -- and it would drag
   two literal [Set]s into the universe instance.

   BOTH CLASSES ARE INHABITED, and that matters for reading the warning
   correctly: an implication into an EMPTY class would be cheap to
   refute, so [Id_AdjointOnTheLeft] is shipped -- degenerate, both
   functors being identities -- purely to rule that out, alongside
   [Id_AdjointOnTheRight].  The two real right-hand witnesses are
   non-degenerate on the OTHER axis too: [chain3_S_neq_T] separates
   the two functors of the Galois pair, and [powerset_Omega_two_subsets]
   proves that P(Ω) has two ≉-distinct elements, so the hom-setoids the
   [Sets] bijection relates are not trivially singletons.

   RIEHL §4.4.  Both derived notions are delivered.  [AdjointOnTheLeft]
   is the left-hand class with the same four-law shape, its own two
   passages to the ordinary [Adjunction] (there the reduction is T ⊣ S^op
   over A and X^op), its own symmetry lemma and its own [eq_refl] round
   trips; and [MutuallyRightAdjoint] / [MutuallyLeftAdjoint] give the
   unit/counit presentations, the first with TWO UNITS and the second
   with TWO COUNITS, each subject to two triangle identities.  The
   structural reason the right-hand notion has two UNITS is worth a
   sentence, because it is what makes that half free: under the
   reduction, [runit] is literally the unit of T^op ⊣ S while [runit'] is
   its COUNIT -- and a counit in A^op is a unit in A -- so both
   presentations ride Adjunction/Natural/Transformation/Universal.v's
   existing round trip and no triangle is re-proved here.  The only new
   machinery is four [Transform] repackagings, all [:=] with no tactic,
   each swapping [naturality] with [naturality_sym].

   Riehl's accompanying remark -- that only the TWO-SIDED dualization
   collapses -- is stated in all three of its readings rather than left
   as prose.  (i) Two-sided on an ORDINARY adjunction returns an ordinary
   adjunction: [ordinary_two_sided_collapses], which is the in-tree
   [Opposite_Adjunction] applied.  (ii) ONE-sided dualization is exactly
   what produces the contravariant notions:
   [Adjunction_of_AdjointOnTheRight] exhibits a mutually-right pair AS an
   ordinary adjunction between A^op and X.  (iii) Two-sided on a
   CONTRAVARIANT pair does NOT collapse -- it EXCHANGES the two notions:
   [AdjointOnTheLeft_of_AdjointOnTheRight_op] and its inverse, with both
   round trips at [eq_refl].

   STRENGTHS, MEASURED STRICT-FIRST.  Twenty-five [eq_refl] statements,
   counted on the comment-stripped source and excluding the three that
   sit inside a [Fail].  They break down as: SIX round trips with the
   ordinary [Adjunction] (both handednesses and both directions, plus
   both directions of the primed orientation); TWO two-sided exchange
   round trips; TWO symmetry involutions; FOUR [Adjunction_Transform]
   round trips; TWO identifications ([sym_swaps_orientation] and
   [aor_second_orientation_is_opposite]); the power-set flip; FOUR
   unit/counit readbacks; the two identity-witness readbacks; and the two
   opposite-category facts the file opens with.  Every
   one is Leibniz equality of the WHOLE RECORD except the flip and the
   readbacks, which are equalities of values, and the two
   opposite-category facts the file opens with, which are equalities of
   TYPES.
   The unit/counit READBACKS are strict too: [runit] is the transpose of
   the identity, [runit'] the inverse transpose of the identity, the
   recovered bijection is [fmap[S] g ∘ runit x], and [lcounit] is the
   transpose of the identity on the left-hand side, all four by
   [eq_refl].  EXACTLY ONE family of statements was attempted strict and
   REJECTED: the hom-set ↔ unit/counit round trips, in both directions.
   Those are pinned as two CONVERSION negatives, and the cause is
   VALUE-LEVEL RECONSTRUCTION rather than opaque proof fields: the round
   trip does not return the bijection it was given, it rebuilds it
   through the unit.  This file's own [aor_of_MRA_computes] and
   [runit_is_transpose_of_id] exhibit exactly that -- going out and back
   sends [to aor g] to [fmap[S] g ∘ to aor (id)], a different VALUE --
   so no amount of donor transparency could make the two convertible.
   An earlier draft of this header blamed [Program]/[Qed] opacity in
   [Adjunction_from_Transform]; that attribution is withdrawn, the
   discriminating experiment having been run.

   UNIVERSES, measured off BOTH the binder AND the constraint block,
   because in this file the trap fires in BOTH directions.  The CLASSES
   are declared with explicit [Universes o1 h1 p1 o2 h2 p2] binders, in
   the style of Theory/Adjunction.v itself, so their binders DISPLAY free
   (Category@{o1 h1 p1} and Category@{o2 h2 p2}) and the identifications
   are visible in the block: h1 = p1, h1 = h2, h1 = p2, h2 = p2, plus
   h1 = o3 = sh = sp and h1 < so for the [Sets] levels.  That block is
   the same content [Adjunction] itself carries, so annotating buys
   PRESENTATION, not strength -- an unannotated variant was compiled out
   of tree and minimizes the very same identifications into the binder
   instead.  BOTH OBJECT UNIVERSES o1 AND o2 ARE FREE: no constraint
   mentions either, not even a bound.  The DERIVED constants go the other
   way and a reader must not stop at their blocks --
   [Adjunction_of_AdjointOnTheRight@{u u0 u1 u2 u3}] has a block of five
   BOUNDS with NO equation while its BINDER reads Category@{u1 u3 u3} and
   Category@{u2 u3 u3}; likewise [right_does_not_imply_left], whose block
   carries no equation at all.

   The identifications are the DONORS', and each is probed rather than
   attributed, with siblings tested first.  For hom = proof there are TWO
   INDEPENDENT donors: under a declared [Constraint uh < up], [x ~> y]
   and [id[x]] elaborate (controls) while [Opposite C] alone is rejected
   ("Cannot enforce up = uh because uh < up") and, separately, a bare
   hom-setoid ascribed to [obj[Sets]] -- with no functor and no opposite
   in the command -- is rejected with the same message.  For A's hom =
   X's hom there are likewise TWO: under [Constraint ah < xh] the
   contravariant PAIR itself suffices, [(A^op) ⟶ X] elaborating while
   [(X^op) ⟶ A] is rejected (two functors in opposite directions give
   mutual ≤, which Coq collapses), and independently an [Isomorphism] in
   [Sets] between an A-hom-setoid and an X-hom-setoid is rejected with
   no functor anywhere in the command.  All four are pinned below as
   FORMABILITY negatives against passing controls; each was stripped and
   its message read in full.  Nothing here adds to the identifications,
   and none is claimed unavoidable -- no lift was attempted.

   The witnesses are clean: [Chain3_AdjointOnTheRight] and
   [right_does_not_imply_left] carry NO [Set] anywhere, in binder or
   block, and [Powerset_AdjointOnTheRight@{o so}] has [Set] only as a
   strict LOWER bound (Set < o, from [Prop]), inherited from the donor,
   with no pin.

   AXIOMS: 134/134 constants report "Closed under the global context".
   The count is every DISTINCT name the module declares -- 127 from
   [Print Module] on its WHITESPACE-FLATTENED output (it wraps [Record]
   onto its own line, so a line-anchored sweep silently misses the four
   record heads), plus the four [Build_*] constructors and the three
   constructors of [Chain3], which [Print Module] lists after a [:=] and
   no keyword-anchored regex sees.  MIND THE DUPLICATES: flattening the
   output makes a keyword regex return 134 OCCURRENCES for those 127
   names (six names repeat -- [runit] three times, five others twice),
   so counting occurrences and then adding the seven constructors
   double-counts and yields 141.  [Print Assumptions] takes NAMES, and
   all 134 distinct ones were queried.  Thirty of the 134 are [Program]
   obligations -- eight each for the two warning witnesses, four each for
   the two identity inhabitants, three each for the two Galois functors;
   the file uses [Program] nowhere else.

   CLOSURE COST, measured: this file's transitive [Require] closure is 55
   modules, of which 32 are contributed by the [Sets] power-set witness
   alone; without that section it is 23.  The witness is kept because it
   is Mac Lane's own example and because it inhabits the class in a large
   concrete category rather than a three-element poset, but a consumer
   who wants only the class and the reduction should know the price.

   WHAT IS NOT DELIVERED.

     - No [iffT] PACKAGING.  The issue asks for
       [AdjointOnTheRight S T ↔ S^op ⊣ T] and [↔ T^op ⊣ S], and pins
       [Print Assumptions adjoint_on_the_right_iff_op] in its
       Verification block.  No constant of that name exists here and no
       [↔] is formed: both directions of both orientations are shipped
       as four separate named passages instead, which is what makes the
       [eq_refl] round trips statable.  The divergence in shape and in
       naming is recorded rather than papered over.

     - No NOTATION.  The donor's ⌊-⌋ / ⌈-⌉ are declared by a [where]
       clause inside [Class Adjunction]; two classes here would clash
       over one such pair, so both transposes are written [to aor] and
       [from aor] longhand, and no infix for the relation itself is
       introduced.
     - No SEPARATION in the other direction: no pair is exhibited that is
       adjoint on the LEFT but not on the right.  Not attempted; NOT
       claimed impossible, and the symmetry of the two definitions makes
       a mirror-image witness look routine.
     - No UNIQUENESS of the partner functor -- nothing says that a given
       S has at most one T adjoint to it on the right, up to isomorphism
       or otherwise -- and hence no analogue of [right_adjoint_iso].
     - No FUNCTORIALITY and no NATURALITY of any of the eight passages in
       S or T, and no category of such pairs.
     - No two-sided dualization at the UNIT/COUNIT level: the exchange
       [MutuallyRightAdjoint (A^op) (X^op) ↔ MutuallyLeftAdjoint A X] is
       not built (it compiled during scouting; it is omitted for length,
       not blocked), and neither is a symmetry lemma for either
       unit/counit class.
     - Nothing about MONADS: a mutually-right-adjoint pair induces a
       monad on neither A nor X in the ordinary way, and no such
       construction is attempted or ruled out here.
     - No self-adjoint-on-the-right PREDICATE, and no statement that the
       power set is the universal such example.
     - No connection to Adjunction/GAFT.v, to representability, or to
       [Functor/Hom/Yoneda.v]: nothing says when a contravariant functor
       has a partner.
     - No transport along equivalences, no composition of such pairs, and
       no preservation results (a mutually-right pair carries colimits of
       A to limits of X; that is not stated here).
     - No [Set]-free or universe-lifted variant of the [Sets] witness,
       and no attempt to lift any of the four probed donor
       identifications. *)

(* The two facts the whole file rests on, pinned rather than assumed:
   passing to the opposite category leaves the objects alone and reverses
   the homs DEFINITIONALLY.  Everything below -- the class's field types,
   all eight passages, and every [eq_refl] round trip -- is downstream of
   these two.  DISPLAY HAZARD, flagged because it costs a reader time:
   [Print AdjointOnTheRight] renders the second binder of [aor] as
   [x : obj[X^op]], since [T]'s domain is [X^op]; by the first Example
   that IS [obj[X]], and no field of either class is WRITTEN with an
   opposite category or an [Opposite_Functor] in it. *)

Example obj_op_is_obj (X : Category) : obj[X^op] = obj[X] := eq_refl.

Example hom_op_is_hom (A : Category) (a b : A) :
  (a ~{A}~> b) = (b ~{A^op}~> a) := eq_refl.

Section AdjointOnTheRight.

Universes o1 h1 p1 o2 h2 p2.
Context {A : Category@{o1 h1 p1}}.
Context {X : Category@{o2 h2 p2}}.
Context (S : (A^op) ⟶ X).
Context (T : (X^op) ⟶ A).

Class AdjointOnTheRight@{o3 so sh sp} := {
  aor {a x} :
    @Isomorphism@{so sh sp} Sets@{o3 so}
      {| carrier := @hom A a (T x); is_setoid := @homset A a (T x) |}
      {| carrier := @hom X x (S a); is_setoid := @homset X x (S a) |};

  to_aor_nat_a {a a' x} (f : a ~{A}~> T x) (g : a' ~{A}~> a) :
    to aor (f ∘ g) ≈ fmap[S] g ∘ to aor f;
  to_aor_nat_x {a x x'} (f : a ~{A}~> T x') (k : x ~{X}~> x') :
    to aor (fmap[T] k ∘ f) ≈ to aor f ∘ k;

  from_aor_nat_a {a a' x} (p : x ~{X}~> S a) (g : a' ~{A}~> a) :
    from aor (fmap[S] g ∘ p) ≈ from aor p ∘ g;
  from_aor_nat_x {a x x'} (p : x' ~{X}~> S a) (k : x ~{X}~> x') :
    from aor (p ∘ k) ≈ fmap[T] k ∘ from aor p
}.

Class AdjointOnTheLeft@{o3 so sh sp} := {
  aol {x a} :
    @Isomorphism@{so sh sp} Sets@{o3 so}
      {| carrier := @hom A (T x) a; is_setoid := @homset A (T x) a |}
      {| carrier := @hom X (S a) x; is_setoid := @homset X (S a) x |};

  to_aol_nat_a {x a a'} (f : T x ~{A}~> a) (g : a ~{A}~> a') :
    to aol (g ∘ f) ≈ to aol f ∘ fmap[S] g;
  to_aol_nat_x {x x' a} (f : T x ~{A}~> a) (k : x ~{X}~> x') :
    to aol (f ∘ fmap[T] k) ≈ k ∘ to aol f;

  from_aol_nat_a {x a a'} (p : S a ~{X}~> x) (g : a ~{A}~> a') :
    from aol (p ∘ fmap[S] g) ≈ g ∘ from aol p;
  from_aol_nat_x {x x' a} (p : S a ~{X}~> x) (k : x ~{X}~> x') :
    from aol (k ∘ p) ≈ from aol p ∘ fmap[T] k
}.

End AdjointOnTheRight.

Arguments AdjointOnTheRight {A X} S T.
Arguments AdjointOnTheLeft {A X} S T.

(* ---------------- reduction to ordinary adjunctions ---------------- *)

Definition Adjunction_of_AdjointOnTheRight
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  @Adjunction (A^op) X (Opposite_Functor T) S :=
  @Build_Adjunction (A^op) X (Opposite_Functor T) S
    (fun x a => @aor A X S T H a x)
    (fun x y z f g => @to_aor_nat_x   A X S T H z x y f g)
    (fun x y z f g => @to_aor_nat_a   A X S T H y z x g f)
    (fun x y z f g => @from_aor_nat_x A X S T H z x y f g)
    (fun x y z f g => @from_aor_nat_a A X S T H y z x g f).

Definition AdjointOnTheRight_of_Adjunction
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  AdjointOnTheRight S T :=
  @Build_AdjointOnTheRight A X S T
    (fun a x => @adj (A^op) X (Opposite_Functor T) S H x a)
    (fun a a2 x f g => @to_adj_nat_r   (A^op) X _ S H x a a2 g f)
    (fun a x x2 f k => @to_adj_nat_l   (A^op) X _ S H x x2 a f k)
    (fun a a2 x p g => @from_adj_nat_r (A^op) X _ S H x a a2 g p)
    (fun a x x2 p k => @from_adj_nat_l (A^op) X _ S H x x2 a p k).

Definition Adjunction_of_AdjointOnTheLeft
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheLeft S T) :
  @Adjunction A (X^op) T (Opposite_Functor S) :=
  @Build_Adjunction A (X^op) T (Opposite_Functor S)
    (fun x a => @aol A X S T H x a)
    (fun x y z f g => @to_aol_nat_x   A X S T H y x z f g)
    (fun x y z f g => @to_aol_nat_a   A X S T H x y z g f)
    (fun x y z f g => @from_aol_nat_x A X S T H y x z f g)
    (fun x y z f g => @from_aol_nat_a A X S T H x y z g f).

Definition AdjointOnTheLeft_of_Adjunction
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction A (X^op) T (Opposite_Functor S)) :
  AdjointOnTheLeft S T :=
  @Build_AdjointOnTheLeft A X S T
    (fun x a => @adj A (X^op) T (Opposite_Functor S) H x a)
    (fun x a a2 f g => @to_adj_nat_r   A (X^op) T _ H x a a2 g f)
    (fun x x2 a f k => @to_adj_nat_l   A (X^op) T _ H x2 x a f k)
    (fun x a a2 p g => @from_adj_nat_r A (X^op) T _ H x a a2 g p)
    (fun x x2 a p k => @from_adj_nat_l A (X^op) T _ H x2 x a p k).

(* ---------------- round trips: all four at eq_refl ---------------- *)

Example aor_adjunction_round
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_Adjunction (Adjunction_of_AdjointOnTheRight H) = H
  := eq_refl.

Example adjunction_aor_round
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  Adjunction_of_AdjointOnTheRight (AdjointOnTheRight_of_Adjunction H) = H
  := eq_refl.

Example aol_adjunction_round
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheLeft S T) :
  AdjointOnTheLeft_of_Adjunction (Adjunction_of_AdjointOnTheLeft H) = H
  := eq_refl.

Example adjunction_aol_round
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction A (X^op) T (Opposite_Functor S)) :
  Adjunction_of_AdjointOnTheLeft (AdjointOnTheLeft_of_Adjunction H) = H
  := eq_refl.

(* ---------------- symmetry ---------------- *)

Definition AdjointOnTheRight_sym
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) : @AdjointOnTheRight X A T S :=
  @Build_AdjointOnTheRight X A T S
    (fun x a => iso_sym (@aor A X S T H a x))
    (fun x x2 a p k => @from_aor_nat_x A X S T H a x2 x p k)
    (fun x a a2 p g => @from_aor_nat_a A X S T H a2 a x p g)
    (fun x x2 a f k => @to_aor_nat_x   A X S T H a x2 x f k)
    (fun x a a2 f g => @to_aor_nat_a   A X S T H a2 a x f g).

Definition AdjointOnTheLeft_sym
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheLeft S T) : @AdjointOnTheLeft X A T S :=
  @Build_AdjointOnTheLeft X A T S
    (fun x a => iso_sym (@aol A X S T H a x))
    (fun x a a' f g => @from_aol_nat_x A X S T H a a' x f g)
    (fun x x' a f k => @from_aol_nat_a A X S T H a x x' f k)
    (fun x a a' p g => @to_aol_nat_x   A X S T H a a' x p g)
    (fun x x' a p k => @to_aol_nat_a   A X S T H a x x' p k).

Example aor_sym_invol {A X : Category} {S : (A^op) ⟶ X}
  {T : (X^op) ⟶ A} (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_sym (AdjointOnTheRight_sym H) = H := eq_refl.

Example aol_sym_invol {A X : Category} {S : (A^op) ⟶ X}
  {T : (X^op) ⟶ A} (H : AdjointOnTheLeft S T) :
  AdjointOnTheLeft_sym (AdjointOnTheLeft_sym H) = H := eq_refl.

(* ---------------- the second orientation ---------------- *)

Definition Adjunction_of_AdjointOnTheRight'
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  @Adjunction (X^op) A (Opposite_Functor S) T :=
  @Build_Adjunction (X^op) A (Opposite_Functor S) T
    (fun a x => iso_sym (@aor A X S T H a x))
    (fun x y z f g => @from_aor_nat_a A X S T H y x z f g)
    (fun x y z f g => @from_aor_nat_x A X S T H x z y g f)
    (fun x y z f g => @to_aor_nat_a   A X S T H y x z f g)
    (fun x y z f g => @to_aor_nat_x   A X S T H x z y g f).

Definition AdjointOnTheRight_of_Adjunction'
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction (X^op) A (Opposite_Functor S) T) :
  AdjointOnTheRight S T :=
  @Build_AdjointOnTheRight A X S T
    (fun a x => iso_sym (@adj (X^op) A (Opposite_Functor S) T H a x))
    (fun a a2 x f g => @from_adj_nat_l (X^op) A _ T H a2 a x f g)
    (fun a x x2 f k => @from_adj_nat_r (X^op) A _ T H a x2 x k f)
    (fun a a2 x p g => @to_adj_nat_l   (X^op) A _ T H a2 a x p g)
    (fun a x x2 p k => @to_adj_nat_r   (X^op) A _ T H a x2 x k p).

Example aor_adjunction_round'
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_Adjunction' (Adjunction_of_AdjointOnTheRight' H) = H
  := eq_refl.

Example adjunction_aor_round'
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction (X^op) A (Opposite_Functor S) T) :
  Adjunction_of_AdjointOnTheRight' (AdjointOnTheRight_of_Adjunction' H) = H
  := eq_refl.

Example sym_swaps_orientation {A X : Category} {S : (A^op) ⟶ X}
  {T : (X^op) ⟶ A} (H : AdjointOnTheRight S T) :
  Adjunction_of_AdjointOnTheRight (AdjointOnTheRight_sym H)
    = Adjunction_of_AdjointOnTheRight' H := eq_refl.

Example aor_second_orientation_is_opposite
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  Adjunction_of_AdjointOnTheRight' H
    = Opposite_Adjunction _ _ (Adjunction_of_AdjointOnTheRight H) := eq_refl.

(* ---------------- two-sided dualization EXCHANGES ---------------- *)

Definition AdjointOnTheLeft_of_AdjointOnTheRight_op
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @AdjointOnTheRight (A^op) (X^op)
         (Opposite_Functor S) (Opposite_Functor T)) :
  @AdjointOnTheLeft A X S T :=
  @Build_AdjointOnTheLeft A X S T
    (fun x a => @aor _ _ _ _ H a x)
    (fun x a a' f g => @to_aor_nat_a   _ _ _ _ H _ _ _ f g)
    (fun x x' a f k => @to_aor_nat_x   _ _ _ _ H _ _ _ f k)
    (fun x a a' p g => @from_aor_nat_a _ _ _ _ H _ _ _ p g)
    (fun x x' a p k => @from_aor_nat_x _ _ _ _ H _ _ _ p k).

Definition AdjointOnTheRight_op_of_AdjointOnTheLeft
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @AdjointOnTheLeft A X S T) :
  @AdjointOnTheRight (A^op) (X^op)
    (Opposite_Functor S) (Opposite_Functor T) :=
  @Build_AdjointOnTheRight (A^op) (X^op)
    (Opposite_Functor S) (Opposite_Functor T)
    (fun a x => @aol _ _ _ _ H x a)
    (fun a a' x f g => @to_aol_nat_a   _ _ _ _ H _ _ _ f g)
    (fun a x x' f k => @to_aol_nat_x   _ _ _ _ H _ _ _ f k)
    (fun a a' x p g => @from_aol_nat_a _ _ _ _ H _ _ _ p g)
    (fun a x x' p k => @from_aol_nat_x _ _ _ _ H _ _ _ p k).

Example two_sided_round_left {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : @AdjointOnTheLeft A X S T) :
  AdjointOnTheLeft_of_AdjointOnTheRight_op S T
    (AdjointOnTheRight_op_of_AdjointOnTheLeft S T H) = H := eq_refl.

Example two_sided_round_right {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @AdjointOnTheRight (A^op) (X^op)
         (Opposite_Functor S) (Opposite_Functor T)) :
  AdjointOnTheRight_op_of_AdjointOnTheLeft S T
    (AdjointOnTheLeft_of_AdjointOnTheRight_op S T H) = H := eq_refl.

Example ordinary_two_sided_collapses {C D : Category}
  (F : D ⟶ C) (U : C ⟶ D) :
  F ⊣ U -> Opposite_Functor U ⊣ Opposite_Functor F :=
  Opposite_Adjunction F U.

(* ---------------- both classes are inhabited ---------------- *)

(* These two are DEGENERATE and are here for one reason: without an
   inhabitant of [AdjointOnTheLeft] the refutation below would be a much
   weaker statement than it looks, since an implication into an empty
   class is cheap to refute.  Both functors are identities, so neither
   witness exercises contravariance; the non-degenerate exercise is the
   Galois pair and the power set below. *)

Program Definition Id_AdjointOnTheRight (C : Category) :
  @AdjointOnTheRight C (C^op) (Id[C^op]) (Id[C]) :=
  {| aor := fun a x => iso_id |}.

Example id_aor_is_id (C : Category) (a x : C) (f : a ~{C}~> x) :
  to (@aor C (C^op) _ _ (Id_AdjointOnTheRight C) a x) f = f := eq_refl.

Program Definition Id_AdjointOnTheLeft (C : Category) :
  @AdjointOnTheLeft (C^op) C (Id[C]) (Id[C^op]) :=
  {| aol := fun x a => iso_id |}.

Example id_aol_is_id (C : Category) (x a : C) (f : a ~{C}~> x) :
  to (@aol (C^op) C _ _ (Id_AdjointOnTheLeft C) x a) f = f := eq_refl.

(* ---------------- Mac Lane's warning, witnessed ---------------- *)

Inductive Chain3 : Set := C3bot | C3mid | C3top.

Definition chain3_le (x y : Chain3) : Prop :=
  match x with
  | C3bot => True
  | C3mid => match y with C3bot => False | _ => True end
  | C3top => match y with C3top => True | _ => False end
  end.

Definition chain3_PreOrder : RelationClasses.PreOrder chain3_le.
Proof.
  constructor.
  - intro x; destruct x; exact I.
  - intros x y z Hxy Hyz; destruct x, y, z; simpl in *; tauto.
Defined.

Definition Chain3Cat : Category := Proset chain3_PreOrder.

Definition chain3_s (a : Chain3) : Chain3 :=
  match a with C3bot => C3top | C3mid => C3top | C3top => C3bot end.

Definition chain3_t (x : Chain3) : Chain3 :=
  match x with C3bot => C3top | C3mid => C3mid | C3top => C3mid end.

Lemma chain3_s_anti (x y : Chain3) :
  chain3_le y x -> chain3_le (chain3_s x) (chain3_s y).
Proof. destruct x, y; simpl; tauto. Qed.

Lemma chain3_t_anti (x y : Chain3) :
  chain3_le y x -> chain3_le (chain3_t x) (chain3_t y).
Proof. destruct x, y; simpl; tauto. Qed.

Lemma chain3_galois_to (a x : Chain3) :
  chain3_le a (chain3_t x) -> chain3_le x (chain3_s a).
Proof. destruct a, x; simpl; tauto. Qed.

Lemma chain3_galois_from (a x : Chain3) :
  chain3_le x (chain3_s a) -> chain3_le a (chain3_t x).
Proof. destruct a, x; simpl; tauto. Qed.

#[local] Obligation Tactic := simpl; repeat intro; exact I.

Program Definition chain3_S : Chain3Cat^op ⟶ Chain3Cat := {|
  fobj := chain3_s;
  fmap := fun x y f => chain3_s_anti x y f
|}.

Program Definition chain3_T : Chain3Cat^op ⟶ Chain3Cat := {|
  fobj := chain3_t;
  fmap := fun x y f => chain3_t_anti x y f
|}.

Program Definition Chain3_AdjointOnTheRight :
  AdjointOnTheRight chain3_S chain3_T := {|
  aor := fun a x =>
    {| to   := {| morphism := chain3_galois_to a x |}
     ; from := {| morphism := chain3_galois_from a x |} |}
|}.

Theorem Chain3_not_AdjointOnTheLeft :
  AdjointOnTheLeft chain3_S chain3_T -> False.
Proof.
  intro H.
  exact (@to Sets _ _ (@aol _ _ _ _ H C3mid C3mid) (@id Chain3Cat C3mid)).
Qed.

Theorem right_does_not_imply_left :
  (forall (A X : Category) (S : (A^op) ⟶ X) (T : (X^op) ⟶ A),
      AdjointOnTheRight S T -> AdjointOnTheLeft S T) -> False.
Proof.
  intro H.
  exact (Chain3_not_AdjointOnTheLeft
           (H Chain3Cat Chain3Cat chain3_S chain3_T
              Chain3_AdjointOnTheRight)).
Qed.

Example chain3_s_not_monotone :
  chain3_le C3mid C3top /\ (chain3_le (chain3_s C3mid) (chain3_s C3top)
                              -> False).
Proof. split; simpl; tauto. Qed.

Example chain3_t_not_monotone :
  chain3_le C3bot C3mid /\ (chain3_le (chain3_t C3bot) (chain3_t C3mid)
                              -> False).
Proof. split; simpl; tauto. Qed.

Example chain3_s_not_constant :
  chain3_s C3bot = C3top /\ chain3_s C3top = C3bot.
Proof. split; reflexivity. Qed.

Example chain3_t_not_constant :
  chain3_t C3bot = C3top /\ chain3_t C3top = C3mid.
Proof. split; reflexivity. Qed.

Example chain3_S_neq_T : chain3_s C3mid = C3top /\ chain3_t C3mid = C3mid.
Proof. split; reflexivity. Qed.

(* ---------------- Mac Lane's own example: the power set ------------ *)

Definition aor_pflip@{o} {a x : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} a (Powerset_Prop_obj@{o} x)) :
  SetoidMorphism@{o o o} x (Powerset_Prop_obj@{o} a).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier x) (is_setoid x)
       (carrier (Powerset_Prop_obj@{o} a))
       (is_setoid (Powerset_Prop_obj@{o} a))
       (fun e => @Build_SetoidMorphism@{o o o}
                   (carrier a) (is_setoid a) Prop
                   (is_setoid Powerset_Prop_truth@{o})
                   (fun v => f v e) _) _).
  - intros v v' Hv; exact (proper_morphism f v v' Hv e).
  - intros e e' He v; exact (proper_morphism (f v) e e' He).
Defined.

#[local] Obligation Tactic := idtac.

Program Definition Powerset_AdjointOnTheRight@{o so} :
  @AdjointOnTheRight Sets@{o so} Sets@{o so}
    Powerset_Prop_op@{o so} Powerset_Prop_op@{o so} := {|
  aor := fun a x =>
    {| to   := {| morphism := fun f => aor_pflip@{o} f |}
     ; from := {| morphism := fun f => aor_pflip@{o} f |} |}
|}.
Next Obligation. intros a x f g H e v; exact (H v e). Qed.
Next Obligation. intros a x f g H e v; exact (H v e). Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.

Example powerset_aor_is_flip@{o so} (a x : SetoidObject@{o o})
  (f : a ~{Sets@{o so}}~> Powerset_Prop_obj@{o} x)
  (e : carrier x) (v : carrier a) :
  @to Sets@{o so} _ _
     (@aor _ _ _ _ Powerset_AdjointOnTheRight@{o so} a x) f e v = f v e
  := eq_refl.

Definition aor_SetsEmpty@{o} : SetoidObject@{o o} :=
  {| carrier := False ; is_setoid := False_Setoid@{o} |}.

Definition aor_const_true@{o} (Z : SetoidObject@{o o}) :
  SetoidMorphism@{o o o} Z Powerset_Prop_truth@{o}.
Proof.
  unshelve refine (@Build_SetoidMorphism@{o o o} (carrier Z) (is_setoid Z)
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun _ => True) _).
  intros z z' _; split; intro; exact I.
Defined.

Definition aor_const_false@{o} (Z : SetoidObject@{o o}) :
  SetoidMorphism@{o o o} Z Powerset_Prop_truth@{o}.
Proof.
  unshelve refine (@Build_SetoidMorphism@{o o o} (carrier Z) (is_setoid Z)
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun _ => False) _).
  intros z z' _; split; intro K; destruct K.
Defined.

Theorem Powerset_not_AdjointOnTheLeft@{o so} :
  @AdjointOnTheLeft Sets@{o so} Sets@{o so}
     Powerset_Prop_op@{o so} Powerset_Prop_op@{o so} -> False.
Proof.
  intro H.
  exact (@to Sets@{o so} _ _
           (@aol _ _ _ _ H aor_SetsEmpty@{o} Powerset_Omega@{o})
           (aor_const_true@{o} (Powerset_Prop_obj@{o} aor_SetsEmpty@{o}))
           (@setoid_morphism_id@{o o o} Powerset_Omega@{o})).
Qed.

Theorem right_does_not_imply_left_in_Sets :
  (forall (A X : Category) (S : (A^op) ⟶ X) (T : (X^op) ⟶ A),
      AdjointOnTheRight S T -> AdjointOnTheLeft S T) -> False.
Proof.
  intro H.
  exact (Powerset_not_AdjointOnTheLeft
           (H Sets Sets Powerset_Prop_op Powerset_Prop_op
              Powerset_AdjointOnTheRight)).
Qed.

Example powerset_Omega_two_subsets@{o} :
  (@equiv _ (is_setoid (Powerset_Prop_obj@{o} Powerset_Omega@{o}))
     (aor_const_true@{o} Powerset_Omega@{o})
     (aor_const_false@{o} Powerset_Omega@{o})) -> False.
Proof. intro H; exact (proj1 (H True) I). Qed.

(* ---------------- Riehl §4.4: the unit/counit presentations -------- *)

Section MutualTransforms.
Context {A X : Category}.
Context {S : (A^op) ⟶ X}.
Context {T : (X^op) ⟶ A}.

Class MutuallyRightAdjoint := {
  runit  : Id[X] ⟹ S ◯ Opposite_Functor T;
  runit' : Id[A] ⟹ T ◯ Opposite_Functor S;

  right_triangle_S {a : A} :
    fmap[S] (transform[runit'] a) ∘ transform[runit] (S a) ≈ id;
  right_triangle_T {x : X} :
    fmap[T] (transform[runit] x) ∘ transform[runit'] (T x) ≈ id
}.

Class MutuallyLeftAdjoint := {
  lcounit  : S ◯ Opposite_Functor T ⟹ Id[X];
  lcounit' : T ◯ Opposite_Functor S ⟹ Id[A];

  left_triangle_S {a : A} :
    transform[lcounit] (S a) ∘ fmap[S] (transform[lcounit'] a) ≈ id;
  left_triangle_T {x : X} :
    transform[lcounit'] (T x) ∘ fmap[T] (transform[lcounit] x) ≈ id
}.

End MutualTransforms.

Arguments MutuallyRightAdjoint {A X} S T.
Arguments MutuallyLeftAdjoint {A X} S T.

Definition aor_transform_counit {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : Id[A] ⟹ T ◯ Opposite_Functor S) :
  (Opposite_Functor T ◯ S) ⟹ Id[A^op] :=
  @Build_Transform (A^op) (A^op) (Opposite_Functor T ◯ S) (Id[A^op])
    (fun a => transform[n] a)
    (fun a a' f => @naturality_sym _ _ _ _ n a' a f)
    (fun a a' f => @naturality     _ _ _ _ n a' a f).

Definition aor_counit_transform {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : (Opposite_Functor T ◯ S) ⟹ Id[A^op]) :
  Id[A] ⟹ T ◯ Opposite_Functor S :=
  @Build_Transform A A (Id[A]) (T ◯ Opposite_Functor S)
    (fun a => transform[n] a)
    (fun a a' f => @naturality_sym _ _ _ _ n a' a f)
    (fun a a' f => @naturality     _ _ _ _ n a' a f).

Example aor_transform_counit_round {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : Id[A] ⟹ T ◯ Opposite_Functor S) :
  aor_counit_transform S T (aor_transform_counit S T n) = n := eq_refl.

Definition Adjunction_Transform_of_MutuallyRightAdjoint
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : MutuallyRightAdjoint S T) :
  @Adjunction_Transform (A^op) X (Opposite_Functor T) S :=
  @Build_Adjunction_Transform (A^op) X (Opposite_Functor T) S
    (@runit _ _ _ _ H)
    (aor_transform_counit S T (@runit' _ _ _ _ H))
    (fun x => @right_triangle_T _ _ _ _ H x)
    (fun a => @right_triangle_S _ _ _ _ H a).

Definition MutuallyRightAdjoint_of_Adjunction_Transform
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @Adjunction_Transform (A^op) X (Opposite_Functor T) S) :
  MutuallyRightAdjoint S T :=
  @Build_MutuallyRightAdjoint A X S T
    (@unit _ _ _ _ H)
    (aor_counit_transform S T (@counit _ _ _ _ H))
    (fun a => @fmap_counit_unit _ _ _ _ H a)
    (fun x => @counit_fmap_unit _ _ _ _ H x).

Example MRA_transform_round {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : MutuallyRightAdjoint S T) :
  MutuallyRightAdjoint_of_Adjunction_Transform S T
    (Adjunction_Transform_of_MutuallyRightAdjoint S T H) = H := eq_refl.

Example transform_MRA_round {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @Adjunction_Transform (A^op) X (Opposite_Functor T) S) :
  Adjunction_Transform_of_MutuallyRightAdjoint S T
    (MutuallyRightAdjoint_of_Adjunction_Transform S T H) = H := eq_refl.

Definition AdjointOnTheRight_of_MutuallyRightAdjoint
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : MutuallyRightAdjoint S T) : AdjointOnTheRight S T :=
  AdjointOnTheRight_of_Adjunction
    (@Adjunction_from_Transform (A^op) X (Opposite_Functor T) S
       (Adjunction_Transform_of_MutuallyRightAdjoint S T H)).

Definition MutuallyRightAdjoint_of_AdjointOnTheRight
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : AdjointOnTheRight S T) : MutuallyRightAdjoint S T :=
  MutuallyRightAdjoint_of_Adjunction_Transform S T
    (@Adjunction_to_Transform (A^op) X (Opposite_Functor T) S
       (Adjunction_of_AdjointOnTheRight H)).

Definition aol_transform_unit {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : S ◯ Opposite_Functor T ⟹ Id[X]) :
  Id[X^op] ⟹ Opposite_Functor S ◯ T :=
  @Build_Transform (X^op) (X^op) (Id[X^op]) (Opposite_Functor S ◯ T)
    (fun x => transform[n] x)
    (fun x x' f => @naturality_sym _ _ _ _ n x' x f)
    (fun x x' f => @naturality     _ _ _ _ n x' x f).

Definition aol_unit_transform {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : Id[X^op] ⟹ Opposite_Functor S ◯ T) :
  S ◯ Opposite_Functor T ⟹ Id[X] :=
  @Build_Transform X X (S ◯ Opposite_Functor T) (Id[X])
    (fun x => transform[n] x)
    (fun x x' f => @naturality_sym _ _ _ _ n x' x f)
    (fun x x' f => @naturality     _ _ _ _ n x' x f).

Definition Adjunction_Transform_of_MutuallyLeftAdjoint
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : MutuallyLeftAdjoint S T) :
  @Adjunction_Transform A (X^op) T (Opposite_Functor S) :=
  @Build_Adjunction_Transform A (X^op) T (Opposite_Functor S)
    (aol_transform_unit S T (@lcounit _ _ _ _ H))
    (@lcounit' _ _ _ _ H)
    (fun x => @left_triangle_T _ _ _ _ H x)
    (fun a => @left_triangle_S _ _ _ _ H a).

Definition MutuallyLeftAdjoint_of_Adjunction_Transform
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @Adjunction_Transform A (X^op) T (Opposite_Functor S)) :
  MutuallyLeftAdjoint S T :=
  @Build_MutuallyLeftAdjoint A X S T
    (aol_unit_transform S T (@unit _ _ _ _ H))
    (@counit _ _ _ _ H)
    (fun a => @fmap_counit_unit _ _ _ _ H a)
    (fun x => @counit_fmap_unit _ _ _ _ H x).

Example MLA_transform_round {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : MutuallyLeftAdjoint S T) :
  MutuallyLeftAdjoint_of_Adjunction_Transform S T
    (Adjunction_Transform_of_MutuallyLeftAdjoint S T H) = H := eq_refl.

Definition AdjointOnTheLeft_of_MutuallyLeftAdjoint
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : MutuallyLeftAdjoint S T) : AdjointOnTheLeft S T :=
  AdjointOnTheLeft_of_Adjunction
    (@Adjunction_from_Transform A (X^op) T (Opposite_Functor S)
       (Adjunction_Transform_of_MutuallyLeftAdjoint S T H)).

Definition MutuallyLeftAdjoint_of_AdjointOnTheLeft
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : AdjointOnTheLeft S T) : MutuallyLeftAdjoint S T :=
  MutuallyLeftAdjoint_of_Adjunction_Transform S T
    (@Adjunction_to_Transform A (X^op) T (Opposite_Functor S)
       (Adjunction_of_AdjointOnTheLeft H)).

(* ---------------- strict-first readbacks ---------------- *)

Example runit_is_transpose_of_id {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : AdjointOnTheRight S T) (x : X) :
  transform[@runit _ _ _ _ (MutuallyRightAdjoint_of_AdjointOnTheRight S T H)] x
    = @to Sets _ _ (@aor _ _ _ _ H (T x) x) (id[T x]) := eq_refl.

Example runit'_is_transpose_of_id {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : AdjointOnTheRight S T) (a : A) :
  transform[@runit' _ _ _ _ (MutuallyRightAdjoint_of_AdjointOnTheRight S T H)] a
    = @from Sets _ _ (@aor _ _ _ _ H a (S a)) (id[S a]) := eq_refl.

Example aor_of_MRA_computes {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : MutuallyRightAdjoint S T)
  (a : A) (x : X) (g : a ~{A}~> T x) :
  @to Sets _ _
     (@aor _ _ _ _ (AdjointOnTheRight_of_MutuallyRightAdjoint S T H) a x) g
    = fmap[S] g ∘ transform[@runit _ _ _ _ H] x := eq_refl.

Example lcounit_is_transpose_of_id {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : AdjointOnTheLeft S T) (x : X) :
  transform[@lcounit _ _ _ _ (MutuallyLeftAdjoint_of_AdjointOnTheLeft S T H)] x
    = @to Sets _ _ (@aol _ _ _ _ H x (T x)) (id[T x]) := eq_refl.


(* ---------------- probes ---------------- *)

(* Negatives 1-3 are TYPING and negatives 4-5 are CONVERSION; the two
   kinds are kept lexically apart, and each was stripped once and its
   whole error message read.  Negatives 1-3 report a plain type mismatch
   with NO [cannot unify] and no universe clause -- that is the reviewer
   bar, that the class is not an abbreviation for the ordinary
   adjunction.  Negatives 4-5 report [cannot unify] on the two hom-set ↔
   unit/counit round trips.  Negatives 6-9 are FORMABILITY and live in
   their own sections below, where the levels must be declared apart. *)

Section Probes.
Context {A X : Category}.
Context {S : (A^op) ⟶ X}.
Context {T : (X^op) ⟶ A}.

(* Controls: every constant the negatives name is also named outside a
   [Fail], and APPLIED rather than left bare -- an unapplied polymorphic
   constant elaborates whatever its arity, so a signature change would
   leave the guard green while negatives 4-5 went vacuous.  Measured:
   with a spurious argument added to
   [MutuallyRightAdjoint_of_AdjointOnTheRight], the bare form still
   compiles and the applied form does not. *)
Check (AdjointOnTheRight S T).
Check (AdjointOnTheLeft S T).
Check (@Adjunction (A^op) X (Opposite_Functor T) S).
Check @AdjointOnTheRight_of_Adjunction.
Check @Adjunction_of_AdjointOnTheRight.
Check (MutuallyRightAdjoint S T).
Check (fun H : AdjointOnTheRight S T =>
         MutuallyRightAdjoint_of_AdjointOnTheRight S T H).
Check (fun H : MutuallyRightAdjoint S T =>
         AdjointOnTheRight_of_MutuallyRightAdjoint S T H).

Fail Definition probe_not_an_abbreviation
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  AdjointOnTheRight S T := H.

Fail Definition probe_not_an_abbreviation_rev
  (H : AdjointOnTheRight S T) :
  @Adjunction (A^op) X (Opposite_Functor T) S := H.

Fail Definition probe_right_is_not_left (H : AdjointOnTheRight S T) :
  AdjointOnTheLeft S T := H.

Fail Example probe_MRA_round_strict (H : MutuallyRightAdjoint S T) :
  MutuallyRightAdjoint_of_AdjointOnTheRight S T
    (AdjointOnTheRight_of_MutuallyRightAdjoint S T H) = H := eq_refl.

Fail Example probe_aor_MRA_round_strict (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_MutuallyRightAdjoint S T
    (MutuallyRightAdjoint_of_AdjointOnTheRight S T H) = H := eq_refl.

End Probes.

(* Instrument check: [Fail] is live in this build and does notice a
   conversion failure.  Scope-free deliberately, so that it cannot fail
   on a missing scope delimiter instead of on the proposition. *)
Fail Example probe_358_instrument : (true = false) := eq_refl.

(* Negatives 6-7: hom = proof has TWO INDEPENDENT donors.  Section-local
   [Universes]/[Constraint] declarations are measured not to leak (the
   Instance/Fun/Group.v precedent). *)
Section ProbeHomProof.
Universes uo uh up.
Constraint uh < up.
Context (C : Category@{uo uh up}).
Context (x y : C).

Check (x ~{C}~> y).
Check (id[x]).

Fail Check (Opposite C).

Fail Check ({| carrier := @hom C x y; is_setoid := @homset C x y |}
            : obj[Sets]).

End ProbeHomProof.

(* Negatives 8-9: A's hom = X's hom likewise has TWO INDEPENDENT donors
   -- the contravariant PAIR itself, and [Sets] with no functor in the
   command at all. *)
Section ProbeCrossHom.
Universes ao ah ap xo xh xp.
Constraint ah < xh.
Context (A2 : Category@{ao ah ap}).
Context (X2 : Category@{xo xh xp}).
Context (a2 b2 : A2).
Context (x2 y2 : X2).

Check ((A2^op) ⟶ X2).
Check (a2 ~{A2}~> b2).
Check (x2 ~{X2}~> y2).

Fail Check ((X2^op) ⟶ A2).

Fail Check (@Isomorphism Sets
   {| carrier := @hom A2 a2 b2; is_setoid := @homset A2 a2 b2 |}
   {| carrier := @hom X2 x2 y2; is_setoid := @homset X2 x2 y2 |}).

End ProbeCrossHom.
