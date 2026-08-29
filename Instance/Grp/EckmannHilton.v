Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.

Generalizable All Variables.

(* Every statement below mentions the group [G] and, in the first half,
   the group-object structure [GO]; but several of them -- [AbelianGrp G] in
   particular -- do not mention [GO] in their STATEMENT while consuming it
   in the PROOF.  Lib.v sets [Default Proof Using "Type"], which keeps only
   the section variables occurring in the statement, so the section
   hypotheses must be requested explicitly.  This is exactly the discipline
   Theory/EckmannHilton.v:110 adopts, and for the same reason. *)
Local Set Default Proof Using "All".

(** * Group objects in Grp are abelian groups *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, Section III.6 ("Groups in Categories"),
         Exercise 4, printed p. 76
   Paper: Eckmann, Hilton, "Structure maps in group theory", Fundamenta
          Mathematicae 50, 1961, Theorem 1.12
   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/group+object

   Mac Lane's Exercise 4 has two halves.

   (a) An abelian group's multiplication, unit and inversion are themselves
       group homomorphisms, so an abelian group assembles into a group
       object in Grp.

   (b) Conversely, every group object in Grp arises that way: the second
       multiplication agrees with the first, and the first is commutative.

   Half (b) is the Eckmann-Hilton argument.  This file CONSUMES
   Theory/EckmannHilton.v rather than re-deriving it -- it is that file's
   FOURTH consumer, after Structure/Semiadditive.v, Instance/Top/LoopSpace.v
   and Theory/Centre.v (measured by [Require], not by name: a grep for the
   token [EckmannHilton] returns EIGHT files -- Theory/EckmannHilton.v
   itself, the three consumers above, this file, and three that mention it
   in prose only (Instance/Grp/Quotient.v,
   Instance/Sets/Quotient/Partition.v and Structure/Bicartesian/Matrix.v);
   the looser token [Eckmann] returns TWENTY.  An earlier draft said seven
   and nineteen, silently dropping the donor from each; an audit corrected
   both, and the numbers quoted here are what the stated greps actually
   print). *)

(* A PROSE-TO-THEOREM CONVERSION, AND ITS THREE SITES

   The statement proved here is asserted in prose, unproved, in three
   places in the tree:

   - Structure/Group.v:71-80, the [GroupObject] background essay: "A group
     object in Grp itself is an abelian group: the two multiplications
     satisfy an interchange law, and the Eckmann-Hilton argument ... forces
     them to coincide and to commute".  (Theory/EckmannHilton.v:84 cites
     that passage as Structure/Group.v:73; the sentence's key line is
     :72, so that existing cross-reference is off by one.  It is left
     alone -- this file modifies nothing outside itself.  An audit caught
     an off-by-one in THIS sentence too: the citing token is on :84, not
     :85, which carries only the parenthetical gloss.)
   - Theory/EckmannHilton.v:51-57, in the list of facts the principle
     explains: "a group object in Grp is an abelian group.  The ambient
     multiplication and the internal one interchange because the internal
     one is a homomorphism for the ambient one."
   - Theory/EckmannHilton.v:85 again, in the roster of in-tree prose
     appeals to the principle.

   No formal statement of the exercise existed anywhere: a search for the
   phrases "group object in Grp" and "objects in Grp" over the tree's [.v]
   files returns exactly those three prose lines and nothing else. *)

(* A PRIOR-ART CORRECTION.  The issue's "Current state" section says that
   "no category Grp and no category of group objects exists".  BOTH halves
   are stale.  [Grp] is Instance/Grp.v:466 and [GrpCat], the category of
   group objects in a cartesian monoidal category, is
   Theory/Algebra/Group/Hom.v.  An object of [GrpCat GrpS] is precisely a
   [GrpS]-object together with a [@GroupObject GrpS GrpCM] structure on it,
   which is the datum quantified over below; but Theory/Algebra/Group/Hom.v
   is NOT required here (it would add nine modules to this file's
   dependency closure, measured, for no statement that is made), so
   nothing below is phrased in terms of [GrpCat].

   The sibling exercise is Instance/Fun/Group.v, which is Exercise 3 of the
   same section -- group objects in a FUNCTOR category are pointwise
   groups.  It is a different exercise and is neither used nor duplicated
   here; the two files share only the idiom of reading a diagrammatic
   [GroupObject] law at a point. *)

(* THE CRUX, AND WHY IT COSTS ONE LINE

   An object of [GrpCat GrpS] is a group [G] whose multiplication
   [mappend : G ⨂ G ~> G] is itself a MORPHISM OF Grp, i.e. a [GrpHom].
   Instance/Grp.v's [GrpHom] carries

     grp_map_mul : ∀ a b, f (grp_mul _ a b) ≈ grp_mul _ (f a) (f b)

   and the source of [mappend] is [Grp_product G G], whose multiplication
   is componentwise.  Writing [f x y := grp_map mappend (x, y)] and
   [g := grp_mul G], instantiating [grp_map_mul] at the two PAIRS [(a, c)]
   and [(b, d)] gives

     f (g a b) (g c d) ≈ g (f a c) (f b d)

   which is Theory/EckmannHilton.v's [interchange] verbatim.  The
   "middle-two swap" that the middle-four interchange law is usually
   described by is entirely absorbed into WHICH pairs are fed to
   [grp_map_mul]: the proof term of [gob_interchange] is literally
   [grp_map_mul mappend (a, c) (b, d)], with no tactic and no reassociation.
   Nothing else in half (b) has any content: the two unit laws are
   [mempty_left] and [mempty_right] read at the points [(ttt, a)] and
   [(a, ttt)], and respectfulness is [proper_morphism] of the underlying
   setoid map.

   The unit laws are usable because [CC_Monoidal]'s unitors are the
   TRANSPARENT cartesian isomorphisms [prod_one_l] and [prod_one_r]
   (an audit corrected the mechanism here: the record literal at
   Structure/Monoidal/Internal/Product.v:54-57 names ONLY [tensor] and [I],
   and the three isomorphism fields are filled by TYPECLASS RESOLUTION
   against Structure/Cartesian.v:451/:465/:485's [#[export] Program
   Instance]s [prod_one_l], [prod_one_r] and [prod_assoc] -- so exactly six
   naturality and two coherence fields become [Program] obligations, eight
   in all); had they been opaque
   obligations, [mempty_left] would have compared [mappend ∘ mempty ⨂ id]
   with a term that reduces to nothing and this route would have been
   closed.  This is worth recording because the same file's obligations ARE
   opaque and a reader scanning it will see them first. *)

(* WHAT IS PROVED, IN ORDER

   (1) [GrpS], [GrpCM], [GrpMon], [GrpTensor] -- the ambient data, with two
       [eq_refl] readings pinning that the tensor IS Instance/Grp.v's own
       [Grp_product] and the tensor unit IS [Grp_trivial].
   (2) [AbelianGrp] -- commutativity of a [GrpObject], named for the first
       time (see the naming note below).
   (3) Half (b): [gmul2], [gunit2], [ginv2] read a group-object structure
       elementwise; [gmul2_respects], [gmul2_unit_left],
       [gmul2_unit_right] and [gob_interchange] are the five inputs
       Theory/EckmannHilton.v asks for; then [gob_units_agree],
       [gob_mul_agrees], [gob_mul_comm] and the headline
       [group_object_abelian] are its outputs, and [gob_inv_agrees]
       finishes the identification by uniqueness of inverses.
   (4) [group_object_mul_unique], [group_object_unit_unique],
       [group_object_inverse_unique] -- the group-object structure on a
       group is unique when it exists, which is what "arises this way"
       means.
   (5) Half (a): [ab_mappend], [grp_ab_inverse], [ab_MonoidObject] and the
       headline [abelian_GroupObject].
   (6) [abelian_iff_group_object] and the packaged [maclane_III_6_ex4].
   (7) Strengths: three [eq_refl] round trips one way, three [≈] round
       trips the other, with the failures diagnosed.
   (8) Non-vacuity: Z/2 with computing operations, the trivial group as the
       degenerate case proved degenerate, and S3 -- a nonabelian group with
       PROVABLY NO group-object structure, so the theorem excludes
       something.
   (9) A probe section: SIX negatives of three kinds against five positive
       controls and an instrument check. *)

(* WHAT EACH HALF COSTS

   Half (b) costs nothing beyond the five inputs above; every conclusion is
   an [exact] of an [eh_*] applied to them.  Two of Eckmann-Hilton's four
   outputs are REDUNDANT in this instance and are deliberately not
   restated: [eh_assoc] and [eh_g_assoc] conclude associativity, which both
   operations already have by hypothesis ([mappend_assoc] for one,
   [grp_mul_assoc] for the other).  What this instance genuinely consumes
   is [eh_units], [eh_ops], [eh_comm] and [eh_g_comm] -- four, not three;
   an audit caught the omission of [eh_comm], which [gob_mul_comm] spends.
   That is the honest accounting:
   the argument is strictly more general than the use made of it here,
   because it assumes neither associativity nor commutativity of either
   operation, and this file supplies both associativities for free.

   Half (a) costs three homomorphism constructions, and commutativity is
   spent EXACTLY ONCE in each of two of them: in [ab_mappend]'s
   [grp_map_mul] obligation, which is the middle-four interchange
   [(a·c)·(b·d) ≈ (a·b)·(c·d)], and in [grp_ab_inverse]'s, where
   [grp_inv_mul] delivers [(a·b)⁻¹ ≈ b⁻¹·a⁻¹] and commutativity turns it
   into [a⁻¹·b⁻¹].  The third, [mempty], is not constructed at all:
   Instance/Grp.v's [Grp_zero_hom] already IS the constant-at-the-unit
   homomorphism out of the trivial group, and it is reused rather than
   rebuilt.  The five diagrammatic laws of [MonoidObject] and
   [GroupObject] are then pointwise readings of [grp_mul_unit_l],
   [grp_mul_unit_r], [grp_mul_assoc], [grp_mul_inv_l] and [grp_mul_inv_r];
   none of them spends commutativity. *)

(* STRENGTHS, MEASURED STRICT-FIRST

   Going from an abelian group to a group object and back, all three
   operations return AT LEIBNIZ EQUALITY, by [eq_refl]:
   [abelian_roundtrip_mul], [_unit], [_inv].  Nothing needed proving there;
   the group-object structure built in half (a) has [grp_mul G] literally
   inside it, and the pair projections reduce by iota.

   Going the other way -- from an arbitrary group object, through half (b),
   and back through half (a) -- reaches only [≈]:
   [group_object_roundtrip_mul], [_unit], [_inv].  The diagnosis is not
   "rebuilt law fields": it is that [gmul2 G GO] is a projection of a
   VARIABLE [GO], so there is nothing to reduce at all, and no amount of
   transparency downstream would change that.  The whole-record round trip
   [abelian_GroupObject G (group_object_abelian G GO) = GO] is refuted for
   the same reason and pinned as a probe.

   Also refuted, and pinned as [probe_other_roundtrip] -- an audit found
   this paragraph claiming "pinned" while NO negative in the file mentioned
   [HA] at all, so the guard is now real rather than asserted:
   [AbelianGrp G ↔ GroupObject G] is a biconditional
   and NOT an isomorphism of types.  The composite
   [group_object_abelian G (abelian_GroupObject G HA)] is a different proof
   term from [HA] -- it routes through [eh_g_comm] -- and there is no
   setoid on [AbelianGrp G] under which to state that they agree, [AbelianGrp G]
   being a family of [≈]-proofs and not a setoid carrier.  What replaces
   the missing type isomorphism is the uniqueness triple (4) above, which
   says the STRUCTURE is determined even though its PROOFS are not. *)

(* THE Set PIN, DISCLOSED

   [Grp_Terminal] (Instance/Grp.v:562) rides [Grp_trivial]
   (Instance/Grp.v:522), which is declared with a single universe binder
   where the record wants more, so [Grp_trivial@{u} : GrpObject@{u Set u}]
   and [Grp_Terminal@{u} : Terminal@{u Set}]: the HOM universe is pinned
   at [Set].  Since a [CartesianMonoidal] structure on Grp needs a terminal
   object, everything in this file is confined to groups whose hom-setoids
   live in [Set], which is what the local abbreviation

     Monomorphic Universe gu.  Definition GrpS := Grp@{gu Set}.

   makes explicit rather than leaving to elaboration.  The pin is
   MEASURED, not guessed: the probe section declares [Constraint Set < ph],
   accepts [Grp@{pu ph}] as a category AND [Grp_Cartesian] at those very
   levels, and rejects [Grp_Terminal] with "Cannot enforce Set = ph" -- so
   the cause is [Grp_Terminal] specifically, not [Grp] and not the
   cartesian structure.  The same rejection propagates to
   [CC_CartesianMonoidal], with the error still reported AT
   [Grp_Terminal].

   This is a DONOR defect.  It is not repaired here (Instance/Grp.v is not
   touched), and it is NOT claimed unavoidable -- [unit_setoid] is
   polymorphic and the pin looks like the universe-minimization family
   recorded elsewhere in this tree -- only located. *)

(* NOTATION AND SCOPE NOTES, MEASURED

   Three notation hazards were reported to this file's author as parse
   errors.  All three were re-measured here, and the report was WRONG
   about two of them.

   - [obj[Grp@{gu Set}]] PARSES AND ELABORATES FINE.  [Check] returns
     [obj[Grp] : Type].  There is no bracket-versus-[@{}] conflict.
   - [fobj[@tensor _ GrpCM]] PARSES AND ELABORATES FINE too, printing
     [fobj[(⨂)]].  The [fobj[ F ]] notation is closed on both sides, so its
     argument parses at level 200 and an [@]-applied head is fine.
   - What DOES bite, and what most likely produced the reports above, is
     something else: [fobj] lives in Category.Theory.Functor and its
     notation lives in [object_scope].  Requiring only
     Category.Instance.Grp loads that module without importing its names,
     so [fobj] is then "not found in the current environment" -- a NAME
     RESOLUTION error, not a parse error.  This file requires
     Category.Theory.Functor explicitly for exactly that reason.
   - The third hazard is REAL but is an elaboration error, not a parse
     error: bare [G ⨂[GrpCM] G] picks the MORPHISM notation
     (Structure/Monoidal.v:182) over the object one (:178), and reports
     that [G] "has type obj[GrpS] while it is expected to have type
     ?x ~{GrpS}~> ?w".  Either a [%object] delimiter or a result-type
     ascription selects the object reading.  Below, the object is written
     [@fobj _ _ GrpTensor (G, H)] so that no scope discipline is needed.

   Independently: [inverse] is effectively a keyword downstream of
   Structure/Group.v:131, whose notation quotes the token, so the
   group-object inversion is projected by its fully qualified name
   [@Category.Structure.Group.inverse]. *)

(* UNIVERSES, AND THE AXIOM COUNT

   Measured off BOTH the binder and the constraint block of every one of
   the file's 58 constants, with [Set Printing Universes]:

   - [GrpS@{} : Category@{gu Set Set}], constraint block [Set < gu].  So
     the object universe is free and the HOM and PROOF universes are BOTH
     [Set].  That identification is not this file's doing: [Grp]'s second
     universe binder fills both slots, and [Grp@{gu Set}] is the only
     instance a terminal object has (see THE Set PIN).
   - Every constant carries [Set < gu] except FIVE, each for a reason:
     [ctrl_probe_category] and [ctrl_probe_cartesian] live at
     [Grp@{pu ph}] and carry [Set < ph], [ph < pu] instead, which is
     exactly what makes them controls; [eh_probe_instrument] is over [bool];
     [Z2_GroupObject_nondegenerate] carries only
     [u <= Logic_lemmas.equality.u0]; and
     [trivial_GroupObject_degenerate] has an EMPTY constraint block.
     [ctrl_probe_terminal] carries BOTH [Set < gu] and [Set < ph], since
     it mentions both categories.
   - NO constraint block anywhere in the file contains a universe
     EQUATION.  Every constraint is a strict [<] or a bound [<=]; the [=]
     signs in the whole [About] dump are the TEN TERM equalities in the
     [eq_refl] Examples and readings ([grp_tensor_is_product],
     [grp_tensor_unit_is_trivial], the three [abelian_roundtrip_*], the four
     [Z2_gob_*] and [eh_probe_instrument]) -- an earlier draft of this
     paragraph said TWO, which an audit corrected.  So the [Set] pin is
     the ONLY identification, and it is INHERITED from [Grp_Terminal]
     rather than introduced here.
   - The predicate itself is free in its own universe:
     [AbelianGrp@{u} : obj -> Type@{u}], constraint block [Set < gu] only.

   58/58 constants are closed under the global context. *)

(* THE DEPENDENCY ON Instance/Grp/Epi.v

   That file is required for ONE thing: [GrpSym3], [sym3_s], [sym3_a] and
   [sym3_l0], which supply the nonabelian witness at the end.  It was
   chosen over Instance/Grp/TwoFunctors.v's [S3] by measurement: relative
   to the closure this file already needs, Epi.v adds exactly ONE module
   (itself), whereas TwoFunctors.v adds four (itself, Functor/Twist.v,
   Instance/Cat.v and Instance/StrictCat.v).  Neither S3 was rebuilt. *)

(* THE NAME [AbelianGrp]

   No predicate of this shape is named anywhere in the tree: searches for
   the token [AbelianGrp], for the shape
   [grp_mul _ a b ≈ grp_mul _ b a], and for a [Commutative]-style
   predicate over [GrpObject] all come back empty of a NAMED one.  The
   condition itself is written INLINE at four sites in three files -- as a
   hypothesis [comm] at Instance/Grp/TwoFunctors.v:196 and at
   Instance/Grp/Abelianization.v:165, and as a conclusion at
   Instance/Grp/Center.v:160 and :201 -- so this is a naming, not a
   discovery, and all four sites are left alone.  [AbelianGrp] here is a
   PREDICATE on Instance/Grp.v's [GrpObject]; it is NOT
   Structure/Abelian.v's [Class Abelian] (a property of a CATEGORY) and it
   is NOT Instance/Ab.v's [AbObject] (a record extending [CMonObject]).

   WHY THE SUFFIX.  A first draft of this file called the predicate plainly
   [Abelian], on the argument -- correct as far as it goes -- that the two
   notions are different and live in different files.  That argument misses
   the MECHANICAL hazard, which is what forced the rename: the
   [make print-assumptions] gate compiles every audited module into ONE
   scope, and Structure/Abelian.v IS required there, so a bare
   [Print Assumptions Abelian.] would resolve to whichever of the two was
   imported last and could silently audit the wrong constant.  The tree
   already carries one latent collision of exactly this shape
   ([BoolSet], Instance/Sets/Quotient.v and Instance/Sets/Pullback.v, both
   pulled into that same scope), and a second one on a name as central as
   [Abelian] is not worth the aesthetics.  [grp_ab_inverse] and
   [eh_probe_instrument] carry suffixes for a WEAKER reason, and an audit
   corrected an earlier draft that said "for the same reason": they collided
   with Instance/Ab/Character/Finite.v:1751 and Test/ProbePolynomial.v:85,
   but NEITHER of those files is required into the print-assumptions scope
   ([Locate ab_inverse] there returns nothing), so those two renames are
   tree-wide name hygiene and not a gate hazard.  All three collisions were
   found only by sweeping this file's OWN declared names against the tree with
   attribute prefixes allowed; a grep anchored at [Definition|Instance]
   misses [#[export] Program Instance] and would have reported none.
   No bridge to [AbObject] is built: that record is a different one, the
   only in-tree passage between the two hierarchies is
   Instance/Grp/Abelianization.v's [Ab_to_GrpOb] going the other way, and
   Instance/Ab.v is not in this file's dependency closure. *)

(* WHAT IS NOT DELIVERED

   - No statement about [GrpCat GrpS] as a CATEGORY: no forgetful functor,
     no comparison with [Ab], and in particular no claim that group
     objects in Grp form a category equivalent to abelian groups.  Only the
     OBJECTS are classified.
   - No bridge to Instance/Ab.v's [AbObject], for the reason above.
   - No morphism-level statement: nothing is proved about [GroupHom]s
     between two group objects in Grp, so "the identification is
     functorial" is neither stated nor proved.
   - No iterated collapse: the monoid analogue (a monoid object in the
     category of monoids is a commutative monoid) is not stated, and
     neither is the observation that the tower stops here.
   - No relation to Structure/Group/Representable.v's hom-group reading of
     a group object, and none to Instance/Fun/Group.v's Exercise 3.
   - The Set pin is disclosed and located, not repaired.
   - [AbelianGrp G ↔ GroupObject G] is a biconditional only; the two type
     isomorphism attempts are refuted rather than achieved (see STRENGTHS).
   - S3 is shown to carry NO group-object structure, but no CLASSIFICATION
     of which groups do is offered beyond the biconditional itself, and no
     nonabelian group other than S3 is exhibited. *)

(** ** The ambient category and its cartesian monoidal structure *)

(* The Set-pinned Grp.  See THE Set PIN above: [Grp_Terminal] forces the
   hom universe, and naming the instance here keeps every statement below
   at one fixed reading rather than letting elaboration pick per-constant
   instances. *)
Monomorphic Universe gu.

Definition GrpS : Category := Grp@{gu Set}.

Definition GrpCM : @CartesianMonoidal GrpS :=
  @CC_CartesianMonoidal GrpS Grp_Cartesian Grp_Terminal.

Definition GrpMon : @Monoidal GrpS := GrpCM.

Definition GrpTensor := @tensor GrpS GrpMon.

(* The tensor IS Instance/Grp.v's own direct product, and the tensor unit
   IS its own trivial group -- by [eq_refl], so no comparison morphism is
   needed anywhere below. *)
Example grp_tensor_is_product (G H : GrpS) :
  @fobj _ _ GrpTensor (G, H) = Grp_product G H := eq_refl.

Example grp_tensor_unit_is_trivial :
  @Category.Structure.Monoidal.I GrpS GrpMon = Grp_trivial := eq_refl.

(** ** Abelian groups *)

Definition AbelianGrp (G : GrpS) : Type :=
  ∀ a b : carrier G, grp_mul G a b ≈ grp_mul G b a.

(** ** Half (b): a group object in Grp is abelian *)

Section GroupObjectInGrp.

Context (G : GrpS).
Context (GO : @GroupObject GrpS GrpCM G).

Definition gob_monoid : @MonoidObject GrpS GrpMon G :=
  @groupobject_is_monoid GrpS GrpCM G GO.

(* The three structure morphisms, read elementwise.  [gmul2] is the SECOND
   multiplication -- the internal one -- as opposed to [grp_mul G], which
   is the group's own. *)
Definition gmul2 (a b : carrier G) : carrier G :=
  grp_map (@mappend GrpS GrpMon G gob_monoid) (a, b).

Definition gunit2 : carrier G :=
  grp_map (@mempty GrpS GrpMon G gob_monoid) ttt.

Definition ginv2 (a : carrier G) : carrier G :=
  grp_map (@Category.Structure.Group.inverse GrpS GrpCM G GO) a.

(* Input 1 of 5 to Eckmann-Hilton: [gmul2] respects [≈], because the
   underlying [SetoidMorphism] does and the product setoid's equivalence
   is componentwise.  Kept a plain [Lemma] rather than an [Instance]: it is
   passed explicitly to the [eh_*] lemmas, and registering a [Proper] for
   a projection of a variable would only slow resolution. *)
Lemma gmul2_respects : Proper (equiv ==> equiv ==> equiv) gmul2.
Proof.
  intros a a' Ha b b' Hb.
  unfold gmul2.
  apply proper_morphism.
  split; assumption.
Qed.

(* Inputs 2 and 3: the two unit laws.  These ARE [mempty_left] and
   [mempty_right] read at a point; the unitors of [CC_Monoidal] are the
   transparent cartesian projections, so nothing else is needed. *)
Lemma gmul2_unit_left (a : carrier G) : gmul2 gunit2 a ≈ a.
Proof. exact (@mempty_left GrpS GrpMon G gob_monoid (ttt, a)). Qed.

Lemma gmul2_unit_right (a : carrier G) : gmul2 a gunit2 ≈ a.
Proof. exact (@mempty_right GrpS GrpMon G gob_monoid (a, ttt)). Qed.

(* Input 4, THE CRUX.  [mappend] is a morphism of Grp, so it is a group
   homomorphism out of the direct product; its [grp_map_mul] clause,
   instantiated at the pairs [(a, c)] and [(b, d)], IS the interchange law
   in exactly the orientation Theory/EckmannHilton.v states it.  No
   tactic, no reassociation, no middle-two shuffling: the swap lives in
   the choice of pairs. *)
Lemma gob_interchange (a b c d : carrier G) :
  gmul2 (grp_mul G a b) (grp_mul G c d)
    ≈ grp_mul G (gmul2 a c) (gmul2 b d).
Proof.
  exact (grp_map_mul (@mappend GrpS GrpMon G gob_monoid) (a, c) (b, d)).
Qed.

(* Input 5 is [grp_mul G]'s own unit and respectfulness data, which
   Instance/Grp.v already supplies: [grp_mul_respects] is a field,
   [grp_mul_unit_l] is a field, and [grp_mul_unit_r] is derived there. *)

(* Eckmann-Hilton, output 1: the two units coincide. *)
Theorem gob_units_agree : gunit2 ≈ grp_unit G.
Proof.
  exact (eh_units gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange).
Qed.

(* Output 2: the two multiplications coincide. *)
Theorem gob_mul_agrees (a b : carrier G) : gmul2 a b ≈ grp_mul G a b.
Proof.
  exact (eh_ops gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange a b).
Qed.

(* Output 3, the internal reading of commutativity. *)
Theorem gob_mul_comm (a b : carrier G) : gmul2 a b ≈ gmul2 b a.
Proof.
  exact (eh_comm gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange a b).
Qed.

(* THE HEADLINE of half (b): the group's OWN multiplication is
   commutative.  This is [eh_g_comm], the [g]-side reading, which is what
   a consumer holding only [grp_mul G] wants. *)
Theorem group_object_abelian : AbelianGrp G.
Proof.
  exact (eh_g_comm gmul2 (grp_mul G) gunit2 (grp_unit G)
           gmul2_respects (grp_mul_respects G)
           gmul2_unit_left gmul2_unit_right
           (grp_mul_unit_l G) (grp_mul_unit_r G)
           gob_interchange).
Qed.

(* The two inverse laws of [GroupObject], read at a point.  [∆] copies and
   [eliminate] discards, so both sides reduce to elementwise statements
   about [gmul2], [ginv2] and [gunit2]. *)
Lemma gob_inv_left (a : carrier G) : gmul2 (ginv2 a) a ≈ gunit2.
Proof. exact (@left_inverse GrpS GrpCM G GO a). Qed.

Lemma gob_inv_right (a : carrier G) : gmul2 a (ginv2 a) ≈ gunit2.
Proof. exact (@right_inverse GrpS GrpCM G GO a). Qed.

(* Eckmann-Hilton says nothing about inversion, but once the two
   multiplications and the two units have been identified, the group
   object's inversion is a left inverse for the group's own
   multiplication, and Instance/Grp.v's [grp_inv_unique_l] finishes. *)
Theorem gob_inv_agrees (a : carrier G) : ginv2 a ≈ grp_inv G a.
Proof.
  apply grp_inv_unique_l.
  rewrite <- gob_mul_agrees.
  rewrite gob_inv_left.
  apply gob_units_agree.
Qed.

(* "Every group object in Grp arises this way", packaged: all three
   structure morphisms are the group's own. *)
Definition group_object_structure_forced :
  (∀ a b : carrier G, gmul2 a b ≈ grp_mul G a b)
    ∧ (gunit2 ≈ grp_unit G)
    ∧ (∀ a : carrier G, ginv2 a ≈ grp_inv G a) :=
  (gob_mul_agrees, (gob_units_agree, gob_inv_agrees)).

End GroupObjectInGrp.

(** ** Uniqueness of the group-object structure *)

(* Because every group-object structure on [G] is [G]'s own structure,
   any two of them agree.  This is the content of "arises this way" that a
   bare biconditional does not carry. *)

Theorem group_object_mul_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b ≈ gmul2 G GO' a b.
Proof.
  rewrite gob_mul_agrees.
  symmetry.
  apply gob_mul_agrees.
Qed.

Theorem group_object_unit_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) :
  gunit2 G GO ≈ gunit2 G GO'.
Proof.
  rewrite gob_units_agree.
  symmetry.
  apply gob_units_agree.
Qed.

Theorem group_object_inverse_unique (G : GrpS)
        (GO GO' : @GroupObject GrpS GrpCM G) (a : carrier G) :
  ginv2 G GO a ≈ ginv2 G GO' a.
Proof.
  rewrite gob_inv_agrees.
  symmetry.
  apply gob_inv_agrees.
Qed.

(** ** Half (a): an abelian group is a group object in Grp *)

Section AbelianIsGroupObject.

Context (G : GrpS).
Context (HA : AbelianGrp G).

(* The multiplication as a morphism of Grp.  The only obligation with
   content is [grp_map_mul], which is the middle-four interchange
   [(a·c)·(b·d) ≈ (a·b)·(c·d)]; commutativity is spent there exactly
   once, on the inner pair. *)
Definition ab_mappend : Grp_product G G ~{GrpS}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G G) G
       {| morphism := fun p => grp_mul G (fst p) (snd p) |} _ _).
  - intros p q Hpq.
    destruct Hpq as [H1 H2]; simpl in *.
    now rewrite H1, H2.
  - simpl.
    apply grp_mul_unit_l.
  - intros [a b] [c d]; simpl.
    rewrite !grp_mul_assoc.
    apply grp_mul_respects; [reflexivity |].
    rewrite <- !grp_mul_assoc.
    apply grp_mul_respects; [| reflexivity].
    apply HA.
Defined.

(* Inversion as a morphism of Grp.  Instance/Grp.v's [grp_inv_mul] gives
   the ANTIhomomorphism law [(a·b)⁻¹ ≈ b⁻¹·a⁻¹]; commutativity is spent
   exactly once, turning it into a homomorphism law.
   (Instance/Grp.v:886's [Grp_inv_to]
   already packages inversion as a morphism into the OPPOSITE group, which
   needs no hypothesis; that is a different arrow and is not reused.) *)
Definition grp_ab_inverse : G ~{GrpS}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G G {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - apply grp_inv_unit.
  - intros a b; simpl.
    rewrite grp_inv_mul.
    apply HA.
Defined.

(* The underlying monoid object.  The unit morphism is REUSED, not built:
   [Grp_zero_hom G] is already the constant-at-the-unit homomorphism out
   of the trivial group, and the trivial group is definitionally the
   tensor unit ([grp_tensor_unit_is_trivial] above).  All three laws are
   pointwise readings of Instance/Grp.v's own group laws; none of them
   spends commutativity. *)
Definition ab_MonoidObject : @MonoidObject GrpS GrpMon G.
Proof.
  unshelve notypeclasses refine
    (@Build_MonoidObject GrpS GrpMon G (Grp_zero_hom G) ab_mappend _ _ _).
  - intros [u a]; simpl.
    apply grp_mul_unit_l.
  - intros [a u]; simpl.
    apply grp_mul_unit_r.
  - intros [[a b] c]; simpl.
    apply grp_mul_assoc.
Defined.

(* THE HEADLINE of half (a).  Both inverse laws are [grp_mul_inv_l] and
   [grp_mul_inv_r] read at a point: [∆] copies, [eliminate] discards, and
   the right-hand side [mempty ∘ eliminate] is the constant-at-the-unit
   endomorphism. *)
Definition abelian_GroupObject : @GroupObject GrpS GrpCM G.
Proof.
  unshelve notypeclasses refine
    (@Build_GroupObject GrpS GrpCM G ab_MonoidObject grp_ab_inverse _ _).
  - intro a; simpl.
    apply grp_mul_inv_l.
  - intro a; simpl.
    apply grp_mul_inv_r.
Defined.

End AbelianIsGroupObject.

(** ** Mac Lane's Exercise 4 *)

(* [↔] is Lib's Type-valued [iffT] (Lib/Foundation.v:72), which is what
   the two sides need: [AbelianGrp G] is a family of [≈]-proofs and
   [GroupObject G] is data, so neither is a [Prop]. *)
Definition abelian_iff_group_object (G : GrpS) :
  AbelianGrp G ↔ @GroupObject GrpS GrpCM G :=
  (abelian_GroupObject G, group_object_abelian G).

(* The exercise, packaged: the biconditional together with the clause that
   makes the backward direction say "arises this way" rather than merely
   "exists". *)
Definition maclane_III_6_ex4 (G : GrpS) :
  (AbelianGrp G ↔ @GroupObject GrpS GrpCM G)
    ∧ (∀ GO : @GroupObject GrpS GrpCM G,
         (∀ a b : carrier G, gmul2 G GO a b ≈ grp_mul G a b)
           ∧ (gunit2 G GO ≈ grp_unit G)
           ∧ (∀ a : carrier G, ginv2 G GO a ≈ grp_inv G a)) :=
  (abelian_iff_group_object G, group_object_structure_forced G).

(** ** Strengths, measured strict-first *)

(* AbelianGrp group to group object and back: all three operations return at
   LEIBNIZ equality.  The structure built in half (a) has [grp_mul G],
   [grp_unit G] and [grp_inv G] literally inside it, and the pair
   projections reduce by iota, so these need no proof. *)

Example abelian_roundtrip_mul (G : GrpS) (HA : AbelianGrp G)
        (a b : carrier G) :
  gmul2 G (abelian_GroupObject G HA) a b = grp_mul G a b := eq_refl.

Example abelian_roundtrip_unit (G : GrpS) (HA : AbelianGrp G) :
  gunit2 G (abelian_GroupObject G HA) = grp_unit G := eq_refl.

Example abelian_roundtrip_inv (G : GrpS) (HA : AbelianGrp G)
        (a : carrier G) :
  ginv2 G (abelian_GroupObject G HA) a = grp_inv G a := eq_refl.

(* Group object to abelian group and back: only [≈].  The obstruction is
   NOT rebuilt law fields -- it is that [gmul2 G GO] projects a VARIABLE
   [GO], so no reduction is available on that side at all.  Probes 3 and 5
   pin the two strict failures. *)

Theorem group_object_roundtrip_mul (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G (abelian_GroupObject G (group_object_abelian G GO)) a b
    ≈ gmul2 G GO a b.
Proof.
  symmetry.
  apply gob_mul_agrees.
Qed.

Theorem group_object_roundtrip_unit (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) :
  gunit2 G (abelian_GroupObject G (group_object_abelian G GO))
    ≈ gunit2 G GO.
Proof.
  symmetry.
  apply gob_units_agree.
Qed.

Theorem group_object_roundtrip_inv (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a : carrier G) :
  ginv2 G (abelian_GroupObject G (group_object_abelian G GO)) a
    ≈ ginv2 G GO a.
Proof.
  symmetry.
  apply gob_inv_agrees.
Qed.

(** ** Non-vacuity *)

(* The degenerate case first, and proved degenerate: the trivial group is
   abelian, so it carries a group-object structure, but every pair of its
   elements is identified, so nothing about it separates anything. *)

Lemma trivial_abelian : AbelianGrp Grp_trivial.
Proof.
  intros a b.
  reflexivity.
Qed.

Definition trivial_GroupObject : @GroupObject GrpS GrpCM Grp_trivial :=
  abelian_GroupObject Grp_trivial trivial_abelian.

Lemma trivial_GroupObject_degenerate (a b : carrier Grp_trivial) : a ≈ b.
Proof.
  destruct a, b.
  reflexivity.
Qed.

(* Z/2, Instance/Grp.v:1087's own witness, reused rather than rebuilt. *)

Lemma Z2_abelian : AbelianGrp Z2.
Proof.
  intros a b; simpl.
  destruct a, b; reflexivity.
Qed.

Definition Z2_GroupObject : @GroupObject GrpS GrpCM Z2 :=
  abelian_GroupObject Z2 Z2_abelian.

(* The group-object structure on Z/2 COMPUTES. *)

Example Z2_gob_mul_tt : gmul2 Z2 Z2_GroupObject true true = false :=
  eq_refl.

Example Z2_gob_mul_tf : gmul2 Z2 Z2_GroupObject true false = true :=
  eq_refl.

Example Z2_gob_unit : gunit2 Z2 Z2_GroupObject = false := eq_refl.

Example Z2_gob_inv : ginv2 Z2 Z2_GroupObject true = true := eq_refl.

(* And it is not degenerate: the multiplication is not constant, and the
   carrier has two provably distinct elements ([Z2_nontrivial] is
   Instance/Grp.v's). *)

Lemma Z2_gob_not_constant :
  gmul2 Z2 Z2_GroupObject true true ≈ gmul2 Z2 Z2_GroupObject true false
    → False.
Proof.
  simpl.
  discriminate.
Qed.

Lemma Z2_GroupObject_nondegenerate :
  (∀ a b : carrier Z2, a ≈ b) → False.
Proof.
  intro Hall.
  exact (Z2_nontrivial (Hall true false)).
Qed.

(* THE EXCLUSION.  A theorem that classifies is worthless if it excludes
   nothing, so here is a group that provably carries NO group-object
   structure: the symmetric group on three letters, Instance/Grp/Epi.v's
   [GrpSym3], with [sym3_s] and [sym3_a] two transpositions.  The two
   composites differ already at the first letter, and [sym3_rel] at two
   distinct letters reduces to [False], so the refutation is a single
   application. *)

Definition Sym3 : GrpS := GrpSym3.

Lemma Sym3_not_abelian : AbelianGrp Sym3 → False.
Proof.
  intro H.
  exact (H sym3_s sym3_a sym3_l0).
Qed.

Theorem Sym3_no_group_object : @GroupObject GrpS GrpCM Sym3 → False.
Proof.
  intro GO.
  exact (Sym3_not_abelian (group_object_abelian Sym3 GO)).
Qed.

(** ** Probes *)

(* Five negatives of THREE kinds, each paired with a positive control that
   names every constant the negative names, plus an instrument check.
   Each [Fail] below was stripped once and its error read: the kinds are
   genuinely distinct, and the two universe negatives report their failure
   AT [Grp_Terminal] in both cases.

   A PARSE error cannot be captured by [Fail] -- the file aborts even
   inside it -- so the notation findings recorded in the header above are
   prose, not probes. *)

Section ProbeUniversePin.

Universe pu ph.
Constraint Set < ph.

(* Positive controls.  The first two say that at a hom universe strictly
   above [Set] the category Grp still elaborates and is still cartesian --
   so neither [Grp] nor [Grp_Cartesian] is the cause.  The third is the
   sharp contrast for the negative that follows: the SAME constant
   [Grp_Terminal] is accepted at [GrpS], where the hom universe IS [Set],
   and rejected one line later where it is not. *)
Definition ctrl_probe_category : Category := Grp@{pu ph}.

Definition ctrl_probe_cartesian : @Cartesian Grp@{pu ph} := Grp_Cartesian.

Definition ctrl_probe_terminal : @Terminal GrpS := Grp_Terminal.

(* FORMABILITY (universe), 1 of 2.  "The term Grp_Terminal has type
   Terminal@{_ Set} while it is expected to have type Terminal@{pu ph}
   (universe inconsistency: Cannot enforce Set = ph)." *)
Fail Definition probe_terminal_pinned : @Terminal Grp@{pu ph} :=
  Grp_Terminal.

(* FORMABILITY (universe), 2 of 2.  The same rejection propagates to the
   cartesian monoidal structure, and the error is still reported at
   [Grp_Terminal] -- which is what locates the pin. *)
Fail Definition probe_cm_pinned : @CartesianMonoidal Grp@{pu ph} :=
  @CC_CartesianMonoidal Grp@{pu ph} Grp_Cartesian Grp_Terminal.

End ProbeUniversePin.

(* TYPING.  [GroupObject] wants a [CartesianMonoidal]; [GrpMon] is only a
   [Monoidal].  "The term GrpMon has type Monoidal while it is expected to
   have type CartesianMonoidal." *)
Definition ctrl_probe_groupobject : Type := @GroupObject GrpS GrpCM Z2.

Fail Definition probe_needs_cartesian : Type :=
  @GroupObject GrpS GrpMon Z2.

(* CONVERSION, 1 of 2.  The two multiplications agree at [≈] and NOT on
   the nose: [gmul2 G GO] projects a variable [GO], so nothing reduces.
   "cannot unify gmul2 G GO a b and grp_mul G a b". *)
Example ctrl_probe_mul_agrees (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b ≈ grp_mul G a b := gob_mul_agrees G GO a b.

Fail Example probe_mul_strict (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) (a b : carrier G) :
  gmul2 G GO a b = grp_mul G a b := eq_refl.

(* CONVERSION, 2 of 2.  The whole-record round trip through both halves is
   refuted for the same reason: "cannot unify
   abelian_GroupObject G (group_object_abelian G GO) and GO".  What DOES
   hold is [group_object_roundtrip_mul] and its two siblings, at [≈].
   This is also why [abelian_iff_group_object] is a biconditional and not
   an isomorphism of types. *)
Fail Example probe_record_roundtrip (G : GrpS)
        (GO : @GroupObject GrpS GrpCM G) :
  abelian_GroupObject G (group_object_abelian G GO) = GO := eq_refl.

(* CONVERSION, 3 of 3.  The OTHER composite is refuted too, and this probe
   exists because an audit found the header claiming it was "pinned" when
   no negative mentioned [HA] at all: the round trip that starts from an
   [AbelianGrp] proof is likewise not the identity, so the biconditional is
   a biconditional in both directions and not an isomorphism of types.
   Every constant it names -- [AbelianGrp], [abelian_GroupObject],
   [group_object_abelian] -- is already named by a positive command above,
   so it needs no control of its own. *)
Fail Example probe_other_roundtrip (G : GrpS) (HA : AbelianGrp G) :
  group_object_abelian G (abelian_GroupObject G HA) = HA := eq_refl.

(* Instrument check: the [Fail] mechanism is live in this file, so the
   six negatives above are not passing vacuously.  Note that [1] parses
   as [terminal_obj] in [category_scope], which is why the check is
   written over [bool]. *)
Example eh_probe_instrument : true = true := eq_refl.

Fail Example probe_instrument_neg : true = false := eq_refl.
