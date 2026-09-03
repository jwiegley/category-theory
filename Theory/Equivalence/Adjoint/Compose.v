Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(** * Composition of adjoint equivalences *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+equivalence
   nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   Mac Lane, Categories for the Working Mathematician, SIV.4, printed
   p. 95, Exercise 2, quoted from the page (ASCII transliteration of the
   arrows):

     "2. (a) Prove: the composite of two equivalences D -> C, C -> A is
             an equivalence.
         (b) State and prove the corresponding fact for adjoint
             equivalences."

   Clause (a) is already in the tree: Theory/Equivalence/Bundled.v:94
   carries [EquivalenceOfCategories_Compose], with the two comparison
   cells at :72 and :83 and the bundled [Equivalence_trans] at :115.  It
   is consumed here, never rebuilt.  This module supplies clause (b):
   the composite of two adjoint equivalences, the identity adjoint
   equivalence, the comparison of the composite's unit and counit with
   those of its two constituents, and a measurement of the groupoid
   laws.  Exercises 3, 4 and 5 of the same page belong elsewhere and are
   cited rather than delivered here: Exercise 3 is
   Theory/Equivalence/Strict.v, Exercise 4 is Adjunction/LeftInverse.v,
   Exercise 5 is Adjunction/Diagonal/Connected.v.

   PLACEMENT.  The catalog entry suggests this be an addition to
   Theory/Equivalence/Adjoint.v.  That is an existing file, and this
   development is delivered as the new sibling module
   Theory/Equivalence/Adjoint/Compose.v instead, leaving the donor
   untouched.  The naming mirrors Adjunction/Compose.v, which stands to
   Theory/Adjunction.v in exactly the same relation.

   PRIOR ART, MEASURED -- AND THE COUNT MOVES WITH THE CRITERION, SO THE
   CRITERION IS STATED.  Searching for the BARE WORD
   [AdjointEquivalence] (word boundaries on both sides) returns FIVE
   files at the base commit, its declaring one included:
   Adjunction/FullFaithful.v:285 (prose only),
   Structure/Monoidal/Dual.v:581, Construction/Subcategory/Dense.v:388
   and Theory/Equivalence/Strict.v:571,:839 (inhabitants), and
   Theory/Equivalence/Adjoint.v itself.  Searching for the same string
   as a SUBSTRING returns EIGHT (again counting the declaring file), the
   three extras being
   Theory/Equivalence/Adjunction.v:36 (prose) and
   Theory/Equivalence/Creation.v:66 and Theory/Equivalence/Limit.v:387,
   which consume [AdjointEquivalence_swap_adjunction] without ever
   naming the class.  Under EITHER criterion the conclusion is the same:
   NONE of them composes two adjoint equivalences and none exhibits an
   identity one -- the strings [AdjointEquivalence_Compose],
   [AdjointEquivalence_Id] and [AdjointEquivalence Id] each occur
   nowhere outside this module and its probe.  The INVERSE, by
   contrast, already exists: [AdjointEquivalence_swap]
   (Theory/Equivalence/Adjoint.v:407), with its underlying swapped
   adjunction [AdjointEquivalence_swap_adjunction] (:414).  It is cited
   below and NOT rebuilt.

   THE ROUTE, AND WHY IT IS NOT THE ONE THE CATALOG ENTRY PROPOSES.
   That entry proposes reading the composite off clause (a) by
   refinement:

     Equivalence_to_AdjointEquivalence
       (EquivalenceOfCategories_Compose
          (AdjointEquivalence_to_Equivalence A)
          (AdjointEquivalence_to_Equivalence B))

   That route is BUILT here, as
   [AdjointEquivalence_Compose_via_equivalence], and one of its premises
   is confirmed by measurement: the quasi-inverse of a composite
   equivalence IS the composite of the two quasi-inverses ON THE NOSE,
   because [quasi_inverse] of a [Build_EquivalenceOfCategories] is its
   second argument definitionally, so the constant elaborates at exactly
   the type [AdjointEquivalence (F' o F) (U o U')] with no transport and
   no coercion.  It is nevertheless not taken as the definition, because
   the composite it produces does not reduce, where the direct route's
   does.  A REASON, measured and not merely asserted: the two cells of
   [EquivalenceOfCategories_Compose] (Bundled.v:72,:83) are closed with
   [Qed], so the refined adjunction's transposes are behind an opaque
   constant.  Read that at its strength -- it is a reason and not an
   isolation.  An out-of-tree experiment rebuilding those two cells
   verbatim but [Defined] was run, and normalizing the refined unit
   still stops, one constructor further in, at the transposing
   isomorphism itself; so the [Qed] cells are NOT shown to be the sole
   blocker, and no experiment makes the two routes agree.  The DIRECT
   route -- take [Adjunction_Compose] of the two underlying adjunctions
   and supply the two invertibility clauses -- reduces, and that is what
   the strict readbacks below record.
   The two composites are DIFFERENT: their whole records, their
   underlying adjunctions and their unit components are each rejected at
   [eq_refl] (negatives 1-3 of Test/ProbeAdjointCompose379.v).  Nothing is
   claimed about whether the two agree up to [~], in either direction:
   an adjunction structure on a fixed adjoint pair need not be unique,
   and no proof and no counterexample is offered here.

   WHAT IS DELIVERED, WITH GRADES.

   (A) An invertibility calculus for [IsIsomorphism], four constants:
       [IsIso_id], [IsIso_along] (transport along [~]), [IsIso_comp]
       (composites) and [IsIso_fmap] (functor images).  [IsIso_fmap]
       DUPLICATES [fmap_IsIsomorphism], which already exists at
       Construction/Reflective/Idempotent.v:69 with the same statement
       up to the explicitness of [f] and the universe annotation (the
       donor takes [f] explicit and carries no universe binders) and
       essentially the same proof.  It is restated rather than
       required, on a measurement: that module's transitive in-project
       closure is 33, and requiring it would put the whole idempotent
       monad and reflective-subcategory development behind every
       consumer of this file.  The other three have no in-tree
       counterpart, measured by NAME over every .v file and by SHAPE:
       no declaration head outside this file states [IsIsomorphism]
       of an identity, of a composite, or transported along [~],
       the only [fmap]-shaped one being the acknowledged
       [fmap_IsIsomorphism].

   (B) [AdjointEquivalence_Compose A B :
          AdjointEquivalence (F' o F) (U o U')].
       Its underlying adjunction IS [Adjunction_Compose] of the two
       constituents at [eq_refl] ([AdjointEquivalence_Compose_adjunction]),
       and each of its two invertibility clauses is the named one at
       [eq_refl] ([..._unit_clause], [..._counit_clause]).

   (C) THE COMPARISON LEMMAS -- the point of clause (b), and the thing a
       bare existence statement would leave out.  Two grades are kept
       apart, because they differ:

       * [AdjointEquivalence_Compose_unit] and [_counit] state Mac
         Lane's whiskering formulas, unit ~ fmap[U] eta' o eta and
         counit ~ epsilon' o fmap[F'] epsilon.  These are [~] and NOT
         [eq_refl]: they are their donors [Adjunction_Compose_unit] and
         [Adjunction_Compose_counit] applied, both of which are [Qed]
         corollaries proved from [to_adj_unit] / [from_adj_counit], a
         genuine rewriting step and not a conversion.  Both are supplied
         by [:=] with no tactic, since the composite's adjunction is the
         donor's on the nose.

       * [AdjointEquivalence_Compose_unit_transpose] and
         [_counit_transpose] hold at [eq_refl]: the composite's unit IS
         the A-transpose of B's unit, and the composite's counit IS the
         B-inverse-transpose of A's counit.  This is the strict form the
         whiskered one is only [~]-equal to, and it is what makes the
         direct route worth taking.

       * [AdjointEquivalence_Compose_unit_inverse] and
         [_counit_inverse] read the two-sided inverses back at
         [eq_refl]: the inverse of the composite unit is
         eta^-1 o fmap[U] (eta'^-1), and of the composite counit
         fmap[F'] (epsilon^-1) o epsilon'^-1.

   (D) [AdjointEquivalence_Id C : AdjointEquivalence Id[C] Id[C]], over
       [Adjunction_Id] (which is Instance/Adjoints.v's [adj_id] reused,
       per Adjunction/Compose.v:65).  Its adjunction reads back at
       [eq_refl]; its unit and counit are [~] the identity, inherited
       from [Adjunction_Id_unit] / [_counit].

   (E) THE GROUPOID LAWS, MEASURED RATHER THAN ASSUMED, and the outcome
       is finer than "not statable".  At the level of the CLASS the
       associativity and identity equations are not even well typed:
       [Compose] of functors is not associative on the nose and [Id] is
       not a strict unit for it (the Adjunction/Pare.v measurement), so
       [AdjointEquivalence (F'' o (F' o F)) ((U o U') o U'')] and
       [AdjointEquivalence ((F'' o F') o F) (U o (U' o U''))] are
       distinct types.  Both shapes are pinned as TYPING negatives in
       the probe, and no transport is invented.  But the OBJECT actions
       of the two bracketings agree definitionally, so the units and
       counits inhabit convertible types, and there the laws hold ON THE
       NOSE: [AdjointEquivalence_Compose_assoc_unit],
       [_assoc_counit], [_id_left_unit], [_id_left_counit],
       [_id_right_unit] and [_id_right_counit] are all [eq_refl].  So
       the trio composition/identity/inverse is available together, and
       the laws relating them hold exactly as far as the type theory
       permits them to be stated.

   (F) NON-VACUITY, and it is not degenerate on the axis that matters.
       [indiscrete_square] composes [AdjointEquivalence_swap] of
       Theory/Equivalence/Strict.v's [indiscrete_adjoint_equivalence]
       with that equivalence itself, giving an adjoint equivalence of
       [Indiscrete bool] with itself whose two functors are both
       [IndT o Erase (Indiscrete bool)].  That composite functor MOVES
       an object: [indiscrete_square_moves] computes its value at
       [false] to [true] by [eq_refl], and [indiscrete_square_not_id]
       closes by [discriminate], so the composite is not an identity
       adjoint equivalence -- indeed it does not even have the type of
       one, pinned as a TYPING negative.  The unit at [false] therefore
       runs between two DIFFERENT objects.  DISCLOSED: [Indiscrete]'s
       hom family ignores its endpoints --
       Instance/Discrete/Reconstruct.v:418 declares
       [hom := fun _ _ => unit], the stdlib [unit : Set], which is also
       where the witness block's [Set] comes from -- so every hom-set
       there is a singleton, and the morphism-level statement "the unit
       at [false] IS the identity" is well typed and TRUE, at [eq_refl]
       and not merely at [~]; a morphism-level non-degeneracy statement
       is therefore unavailable.  This is the trap
       Theory/Equivalence/Strict.v records for its own counit; the
       honest non-degeneracy is the object-level one, and that is what
       is proved.

   WHAT IS NOT DELIVERED.  No direct construction of the inverse: the
   trio's third member is [AdjointEquivalence_swap], cited, and per the
   Theory/Equivalence/Strict.v measurement its unit does not reduce
   (it is built through [EquivalenceOfCategories_sym] and
   [Equivalence_to_AdjointEquivalence]); a hand-built swap whose
   transposes reduce is not attempted.  No comparison at [~] between the
   direct composite and the refinement route.  No uniqueness statement
   for the composite.  No category of categories and adjoint
   equivalences, so the groupoid laws are not packaged as a structure.
   No transport of an adjoint equivalence along a natural isomorphism of
   either adjoint.  No 2-categorical reading and no relation to
   Theory/Bicategory/Adjunction.v.  No witness at a pair of adjoint
   equivalences with three genuinely distinct categories.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK.  The four constants
   of the invertibility calculus are FREE: [IsIso_along@{o h p}] has an
   EMPTY-of-equations block carrying only [Category]'s own [h <= p], and
   [IsIso_fmap@{xo xh xp yo yh yp u}] keeps the two categories' six
   levels apart, with only [Functor]'s own bounds.  That is the explicit
   binders' doing and it is measured, not assumed: written unannotated
   the same bodies minimize so as to identify hom with proof, and are
   then rejected at a category whose two levels are declared apart,
   where the annotated forms are accepted (the probe checks all four as
   controls at exactly those levels).

   Everything downstream of the adjunction vocabulary does identify hom
   with proof -- [Category@{u u0 u0}] in the BINDER, with no such
   equation in any constraint block, the trap that reading a block alone
   gets wrong.  THREE donors are probed and the first is easy to miss:
   the IDENTITY FUNCTOR [Id] forces it ON ITS OWN, so a probe that
   writes [Id[Cu]] into an [Adjunction] is measuring [Id] and not
   [Adjunction] -- the discriminating control is an arbitrary
   endofunctor of the same category, which IS accepted, so [Functor] is
   not a donor.  Probed at two such endofunctors so that no [Id] occurs
   in the command, [Adjunction] is a donor independently; and
   [AdjointEquivalence] is a third that CANNOT be tested apart from
   [Adjunction], its first field being [F -| U], so those two are not
   independent.  [AdjointEquivalence_Id] has both [Id] and [Adjunction]
   in reach and its negative isolates neither.

   The composite additionally carries [u0 = u2], [u0 = u4], [u2 = u4] --
   the three categories' hom-and-proof universes collapsed to one, with
   all three OBJECT universes free -- and that is forced by the mere
   presence of functors in BOTH directions before any adjunction is
   formed, pinned as its own formability negative.  [AdjointEquivalence_Id]
   carries no equation at all in its block.  The witness block carries
   [Set], inherited through Theory/Equivalence/Strict.v from
   Instance/One.v and Instance/Discrete/Reconstruct.v; none of it is
   claimed unavoidable.

   CLOSURE, measured as transitive in-project .vo dependencies EXCLUDING
   this file.  39 modules; 26 with the witness section's three requires
   dropped, so the non-vacuity witness costs 13.  All 13 arrive with
   [Theory.Equivalence.Strict] (39 against 32 with its edge dropped);
   [Instance.One] and [Instance.Discrete.Reconstruct] cost nothing on
   top of it and are required only to bring the names [Erase] and
   [Indiscrete] into scope.  Of the general-theory requires, no single
   one costs anything by itself -- dropping any one of them individually
   leaves the closure at 39, each being inside the others' closures --
   against the donors' own figures of 22 (Theory/Equivalence/Adjoint.v),
   20 (Adjunction/Compose.v) and 20 (Theory/Equivalence/Bundled.v).  The
   probe's closure is 40.

   TRANSPARENCY.  The file has four [Defined.] lines, the two obligations
   each of [IsIso_comp] and [IsIso_fmap]; NONE of them is load-bearing,
   measured by flipping all four to [Qed] in a scratch copy, where the
   file still compiles with every [eq_refl] readback intact.  They are
   [Defined] by the house convention rather than by need -- each is a
   law field, and the data fields are supplied inline.  The one [Qed] in
   the file is [indiscrete_square_not_id], which produces no data.

   REGISTRATION.  Following Theory/Equivalence.v and
   Theory/Equivalence/Adjoint.v, nothing here is registered for instance
   resolution: an adjoint equivalence is a choice of data, always passed
   explicitly at use sites. *)

(** ** An invertibility calculus for [IsIsomorphism] *)

Section IsoCalculus.

(* The explicit universe binders are LOAD-BEARING: written unannotated,
   the same bodies minimize so as to identify X's hom and proof
   universes, and the four constants are then rejected at a category
   whose two levels are declared apart.  Annotated they carry only
   [Category]'s own [h <= p]. *)
Universes o h p.
Context {X : Category@{o h p}}.

(* The identity is invertible, in the predicate form. *)
Program Definition IsIso_id {x : X} : IsIsomorphism (id[x]) := {|
  two_sided_inverse := id
|}.

(* Invertibility transports along [~]: the inverse of the [~]-target
   inverts the source as well, both laws by rewriting with the given
   equation on the one side of the composite where it occurs. *)
Definition IsIso_along {x y : X} {f g : x ~> y}
  (H : f ≈ g) (Hg : IsIsomorphism g) : IsIsomorphism f :=
  {| two_sided_inverse := @two_sided_inverse X x y g Hg
   ; is_right_inverse :=
       transitivity (compose_respects _ _ H _ _ (reflexivity _))
                    (@is_right_inverse X x y g Hg)
   ; is_left_inverse :=
       transitivity (compose_respects _ _ (reflexivity _) _ _ H)
                    (@is_left_inverse X x y g Hg) |}.

(* A composite of invertible morphisms is invertible, with the inverses
   composed in the opposite order.  This is [iso_compose]
   (Theory/Isomorphism.v:172) read for the predicate rather than the
   bundled form. *)
Program Definition IsIso_comp {x y z : X} {f : y ~> z} {g : x ~> y}
  (Hf : IsIsomorphism f) (Hg : IsIsomorphism g) : IsIsomorphism (f ∘ g) := {|
  two_sided_inverse := @two_sided_inverse X x y g Hg
                         ∘ @two_sided_inverse X y z f Hf
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g).
  rewrite (@is_right_inverse X x y g Hg), id_left.
  apply is_right_inverse.
Defined.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (@two_sided_inverse X y z f Hf)).
  rewrite (@is_left_inverse X y z f Hf), id_left.
  apply is_left_inverse.
Defined.

End IsoCalculus.

(* A functor carries invertible morphisms to invertible morphisms.  This
   restates [fmap_IsIsomorphism] (Construction/Reflective/Idempotent.v:69);
   see the header for why it is restated rather than required. *)
Program Definition IsIso_fmap@{xo xh xp yo yh yp +}
  {X : Category@{xo xh xp}} {Y : Category@{yo yh yp}} (G : X ⟶ Y) {x y : X}
  {f : x ~> y} (Hf : IsIsomorphism f) : IsIsomorphism (fmap[G] f) := {|
  two_sided_inverse := fmap[G] (@two_sided_inverse X x y f Hf)
|}.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite (@is_right_inverse X x y f Hf).
  apply fmap_id.
Defined.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite (@is_left_inverse X x y f Hf).
  apply fmap_id.
Defined.

(** ** The composite of two adjoint equivalences *)

Section Compose.

Context {C D E : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context {F' : D ⟶ E} {U' : E ⟶ D}.
Context (A : AdjointEquivalence F U).
Context (B : AdjointEquivalence F' U').

(* The underlying adjunction of the composite: [Adjunction_Compose]
   (Adjunction/Compose.v:173) of the two underlying adjunctions. *)
Definition adjoint_equivalence_compose_adj : (F' ◯ F) ⊣ (U ◯ U') :=
  Adjunction_Compose (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B).

(* The composite's unit is invertible: transport along Mac Lane's
   whiskering formula, then compose the U-image of B's unit isomorphism
   with A's own. *)
Definition adjoint_equivalence_compose_unit_iso (x : C) :
  IsIsomorphism (@unit _ _ _ _ adjoint_equivalence_compose_adj x) :=
  IsIso_along
    (@Adjunction_Compose_unit _ _ _ _ _ _ _
       (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) x)
    (IsIso_comp (IsIso_fmap U (@adj_equiv_unit_iso _ _ _ _ B (F x)))
                (@adj_equiv_unit_iso _ _ _ _ A x)).

(* Dually for the counit. *)
Definition adjoint_equivalence_compose_counit_iso (y : E) :
  IsIsomorphism (@counit _ _ _ _ adjoint_equivalence_compose_adj y) :=
  IsIso_along
    (@Adjunction_Compose_counit _ _ _ _ _ _ _
       (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) y)
    (IsIso_comp (@adj_equiv_counit_iso _ _ _ _ B y)
                (IsIso_fmap F' (@adj_equiv_counit_iso _ _ _ _ A (U' y)))).

(* Mac Lane SIV.4 Exercise 2(b): adjoint equivalences compose. *)
Definition AdjointEquivalence_Compose :
  AdjointEquivalence (F' ◯ F) (U ◯ U') :=
  @Build_AdjointEquivalence C E (F' ◯ F) (U ◯ U')
    adjoint_equivalence_compose_adj
    adjoint_equivalence_compose_unit_iso
    adjoint_equivalence_compose_counit_iso.

(** *** Strict readbacks of the three fields *)

Example AdjointEquivalence_Compose_adjunction :
  @adj_equivalence _ _ _ _ AdjointEquivalence_Compose
    = Adjunction_Compose (@adj_equivalence _ _ _ _ A)
                         (@adj_equivalence _ _ _ _ B) := eq_refl.

Example AdjointEquivalence_Compose_unit_clause (x : C) :
  @adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Compose x
    = adjoint_equivalence_compose_unit_iso x := eq_refl.

Example AdjointEquivalence_Compose_counit_clause (y : E) :
  @adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Compose y
    = adjoint_equivalence_compose_counit_iso y := eq_refl.

(** *** The comparison with the two constituents *)

(* Mac Lane's whiskering formula for the unit, at [~].  Its donor is a
   [Qed] corollary proved from [to_adj_unit], so this grade is the
   donor's; the strict form is [AdjointEquivalence_Compose_unit_transpose]
   below. *)
Definition AdjointEquivalence_Compose_unit (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) x
    ≈ fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  @Adjunction_Compose_unit _ _ _ _ _ _ _
    (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) x.

Definition AdjointEquivalence_Compose_counit (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) y
    ≈ @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) :=
  @Adjunction_Compose_counit _ _ _ _ _ _ _
    (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) y.

(* The strict form: the composite's unit IS A's forward transpose of B's
   unit, and the composite's counit IS B's inverse transpose of A's
   counit.  Both by conversion. *)
Example AdjointEquivalence_Compose_unit_transpose (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) x
    = to (@adj _ _ _ _ (@adj_equivalence _ _ _ _ A) x (U' (F' (F x))))
         (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x)) := eq_refl.

Example AdjointEquivalence_Compose_counit_transpose (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) y
    = from (@adj _ _ _ _ (@adj_equivalence _ _ _ _ B) (F (U (U' y))) y)
           (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) := eq_refl.

(* The two-sided inverses, read back on the nose. *)
Example AdjointEquivalence_Compose_unit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Compose x)
    = @two_sided_inverse _ _ _ _ (@adj_equiv_unit_iso _ _ _ _ A x)
        ∘ fmap[U] (@two_sided_inverse _ _ _ _
                     (@adj_equiv_unit_iso _ _ _ _ B (F x))) := eq_refl.

Example AdjointEquivalence_Compose_counit_inverse (y : E) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Compose y)
    = fmap[F'] (@two_sided_inverse _ _ _ _
                  (@adj_equiv_counit_iso _ _ _ _ A (U' y)))
        ∘ @two_sided_inverse _ _ _ _
            (@adj_equiv_counit_iso _ _ _ _ B y) := eq_refl.

(** *** The refinement route, and how it compares *)

(* The route the catalog entry proposes: refine the composite of the two
   induced equivalences of categories.  Its premise checks out -- the
   type below is the same one [AdjointEquivalence_Compose] inhabits, with
   no transport -- but it is a different adjoint equivalence, rejected at
   [eq_refl] against the direct one on the whole record, on the
   underlying adjunction and on the unit components (negatives 1-3 of
   Test/ProbeAdjointCompose379.v). *)
Definition AdjointEquivalence_Compose_via_equivalence :
  AdjointEquivalence (F' ◯ F) (U ◯ U') :=
  Equivalence_to_AdjointEquivalence
    (EquivalenceOfCategories_Compose
       (AdjointEquivalence_to_Equivalence A)
       (AdjointEquivalence_to_Equivalence B)).

(* Its quasi-inverse is the composite of the two right adjoints on the
   nose, which is what makes the type above the right one. *)
Example AdjointEquivalence_Compose_via_quasi_inverse :
  @quasi_inverse C E (F' ◯ F)
    (EquivalenceOfCategories_Compose
       (AdjointEquivalence_to_Equivalence A)
       (AdjointEquivalence_to_Equivalence B)) = U ◯ U' := eq_refl.

End Compose.

(** ** The identity adjoint equivalence *)

Section Identity.

Context {C : Category}.

(* Id[C] is adjoint-equivalent to itself, over [Adjunction_Id]
   (Adjunction/Compose.v:65, itself Instance/Adjoints.v's [adj_id]
   reused).  Both invertibility clauses transport along the identity. *)
Definition AdjointEquivalence_Id : AdjointEquivalence Id[C] Id[C] :=
  @Build_AdjointEquivalence C C Id[C] Id[C] (@Adjunction_Id C)
    (fun x => IsIso_along (@Adjunction_Id_unit C x) IsIso_id)
    (fun x => IsIso_along (@Adjunction_Id_counit C x) IsIso_id).

Example AdjointEquivalence_Id_adjunction :
  @adj_equivalence _ _ _ _ AdjointEquivalence_Id = @Adjunction_Id C := eq_refl.

Definition AdjointEquivalence_Id_unit (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Id) x ≈ id[x] :=
  @Adjunction_Id_unit C x.

Definition AdjointEquivalence_Id_counit (x : C) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Id) x ≈ id[x] :=
  @Adjunction_Id_counit C x.

(* The two-sided inverses of the identity's clauses are the identity. *)
Example AdjointEquivalence_Id_unit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Id x) = id[x] := eq_refl.

Example AdjointEquivalence_Id_counit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Id x) = id[x] := eq_refl.

End Identity.

(** ** The inverse: cited, not rebuilt *)

Section Inverse.

Context {C D : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context (A : AdjointEquivalence F U).

(* Theory/Equivalence/Adjoint.v:407 already supplies the third member of
   the trio, [AdjointEquivalence_swap A : AdjointEquivalence U F], and
   :414 its underlying swapped adjunction.  The two agree on the nose,
   the latter being defined as the former's adjunction field.  Nothing
   is rebuilt here; the readback records that the trio
   composition/identity/inverse is available together.

   DISCLOSED: [AdjointEquivalence_swap] is built through
   [EquivalenceOfCategories_sym] and [Equivalence_to_AdjointEquivalence],
   so -- by the measurement Theory/Equivalence/Strict.v records for the
   same chain -- its unit does not reduce.  A direct swap whose
   transposes reduce is not attempted here. *)
Example AdjointEquivalence_swap_readback :
  @adj_equivalence _ _ _ _ (AdjointEquivalence_swap A)
    = AdjointEquivalence_swap_adjunction A := eq_refl.

End Inverse.

(** ** The groupoid laws, as far as they are statable *)

Section Laws.

Context {C1 C2 C3 C4 : Category}.
Context {F1 : C1 ⟶ C2} {U1 : C2 ⟶ C1}.
Context {F2 : C2 ⟶ C3} {U2 : C3 ⟶ C2}.
Context {F3 : C3 ⟶ C4} {U3 : C4 ⟶ C3}.
Context (A : AdjointEquivalence F1 U1).
Context (B : AdjointEquivalence F2 U2).
Context (G : AdjointEquivalence F3 U3).

(* The two bracketings of a triple composite have DIFFERENT types --
   [Compose] of functors is not associative on the nose -- so no equation
   between them is well formed, and none is invented; the shape is
   pinned as a typing negative in the probe.  What IS well formed is the
   comparison of their units and counits, because the two bracketings
   have definitionally equal object actions; and there the law holds by
   conversion. *)

Definition assoc_left :=
  AdjointEquivalence_Compose (AdjointEquivalence_Compose A B) G.

Definition assoc_right :=
  AdjointEquivalence_Compose A (AdjointEquivalence_Compose B G).

Example AdjointEquivalence_Compose_assoc_unit (x : C1) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_left) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_right) x := eq_refl.

Example AdjointEquivalence_Compose_assoc_counit (y : C4) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_left) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_right) y := eq_refl.

(* The identity laws, at the same two grades: not statable at the class
   (again pinned in the probe), on the nose at the unit and counit. *)

Example AdjointEquivalence_Compose_id_left_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example AdjointEquivalence_Compose_id_left_counit (y : C2) :
  @counit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ A) y := eq_refl.

Example AdjointEquivalence_Compose_id_right_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose A (@AdjointEquivalence_Id C2))) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example AdjointEquivalence_Compose_id_right_counit (y : C2) :
  @counit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose A (@AdjointEquivalence_Id C2))) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ A) y := eq_refl.

End Laws.

(** ** Non-vacuity *)

(* Theory/Equivalence/Strict.v:839 supplies a genuine adjoint
   equivalence between the terminal category and [Indiscrete bool], via
   Mac Lane SIV.4 Exercise 3.  Swapping it and composing gives an
   adjoint equivalence of [Indiscrete bool] with itself whose two
   functors are both [IndT o Erase (Indiscrete bool)]. *)

Definition indiscrete_swap :
  AdjointEquivalence (Erase (Indiscrete bool)) IndT :=
  AdjointEquivalence_swap indiscrete_adjoint_equivalence.

Definition indiscrete_square :
  AdjointEquivalence (IndT ◯ Erase (Indiscrete bool))
                     (IndT ◯ Erase (Indiscrete bool)) :=
  AdjointEquivalence_Compose indiscrete_swap indiscrete_adjoint_equivalence.

(* The composite is not an identity: its functor moves an object. *)
Example indiscrete_square_moves :
  (IndT ◯ Erase (Indiscrete bool)) false = true := eq_refl.

Theorem indiscrete_square_not_id :
  (IndT ◯ Erase (Indiscrete bool)) false = false → False.
Proof. discriminate. Qed.

(* Consequently the composite's unit at [false] connects two DIFFERENT
   objects: its codomain is [true].  Recorded on the objects, because
   [Indiscrete]'s hom family ignores its endpoints -- see the header. *)
Example indiscrete_square_unit_codomain :
  (IndT ◯ Erase (Indiscrete bool))
    ((IndT ◯ Erase (Indiscrete bool)) false) = true := eq_refl.

(* The underlying adjunction of the witness is the composite of the two
   constituents', on the nose. *)
Example indiscrete_square_adjunction :
  @adj_equivalence _ _ _ _ indiscrete_square
    = Adjunction_Compose
        (@adj_equivalence _ _ _ _ indiscrete_swap)
        (@adj_equivalence _ _ _ _ indiscrete_adjoint_equivalence) := eq_refl.
