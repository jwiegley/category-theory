Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Cartesian.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Group.Proofs.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Monoid.Product.

Generalizable All Variables.

(** * Group homomorphisms, the category of group objects, finite products *)

(* nLab:      https://ncatlab.org/nlab/show/group+object
   Wikipedia: https://en.wikipedia.org/wiki/Group_object

   Mac Lane, Categories for the Working Mathematician, 2nd ed., Section III.6
   ("Groups in Categories"), Exercises 1 and 2, as scoped by issue #343;
   Awodey, Category Theory, 2nd ed., Section 4.1 (the Group(C) construction).

   Given group objects (x, μ_X, η_X, ι_X) and (y, μ_Y, η_Y, ι_Y) in a
   cartesian monoidal category C (Structure/Group.v), a morphism f : x ~> y
   is a homomorphism of group objects when it commutes with the
   multiplications and the units,

     multiplication square   f ∘ μ_X ≈ μ_Y ∘ (f ⨂ f)
     unit triangle           f ∘ η_X ≈ η_Y

   and NOTHING ELSE IS DEMANDED.  Commutation with the inversions,
   f ∘ ι_X ≈ ι_Y ∘ f, is a THEOREM ([GroupHom_inverse]) rather than a field:
   this is Awodey's observation in Section 4.1, and it is why [GroupHom] is
   literally [MonoidHom] of the underlying monoid objects rather than a
   record extending it.  Group objects and these morphisms form a category
   [GrpCat], with faithful forgetful functors to C and to [Mon C]; when C has
   binary products and a terminal object, [GrpCat] has them too, carried
   componentwise, and the forgetful functor to C sends them to C's own ON THE
   NOSE.

   WHAT IS PROVED HERE, IN ORDER

   (1) [group_monoid] / [group_inverse] — reading a [GroupObject] as an
       internal [Monoid] in the mu/eta presentation that [Mon] is indexed by,
       and naming the inversion of a given group object.
   (2) [GroupHom] with [group_hom_mappend] / [group_hom_mempty], and
       [GroupHom_inverse], the theorem that replaces the missing field.
   (3) [GrpCat], [GrpCat_Forget] (faithful) and [GrpCat_Mon] (faithful) —
       Exercise 2 / Awodey's Group(C).
   (4) [GroupObject_Product] and [GrpCat_Cartesian] — binary products.
   (5) [GroupObject_Terminal] and [GrpCat_Terminal] — the terminal group
       object.
   (6) [GrpCat_Forget_*] — the forgetful functor sends both to C's own, at
       Leibniz equality.
   (7) [GrpCat_Cartesian_tensor] / [GrpCat_Terminal_unit] — the same two
       structures with NO hypothesis beyond the [CartesianMonoidal] that
       [GroupObject] already demands.
   (8) A probe section: three negatives of two kinds, four universe
       negatives, and their controls.

   HOW ISSUE #503 IS CONSUMED, AND AT WHICH GRADE

   The monoid half of Exercise 1 is Theory/Algebra/Monoid/Product.v
   ([Monoid_Product], [Mon_Cartesian], [Mon_Terminal]).  It is INSTANTIATED,
   not reproved, and the instantiation worked at three separate grades, each
   machine-checked rather than asserted:

     - DEFINITIONAL.  [grp_prod_monoid] shows by [eq_refl] that the
       underlying monoid of [GroupObject_Product] IS
       [Monoid_Product (group_monoid X) (group_monoid Y)] — the whole
       record, not a comparison map — and [grp_prod_mappend] /
       [grp_prod_mempty] read its two structure maps back as
       [mon_prod_mu] / [mon_prod_eta].  This rests on #503's own
       [monoid_round], the [Monoid]/[MonoidObject] round trip that closes by
       [eq_refl].
     - CONVERTIBLE.  [grp_exl_hom], [grp_exr_hom], [grp_fork_hom] and
       [grp_one_hom] are discharged by [exact] of #503's [mon_exl_hom],
       [mon_exr_hom], [mon_fork_hom] and [mon_one_hom] with no adapter: the
       [GroupHom] goal and the [MonoidHom] goal are the SAME TYPE up to
       conversion.  Not one new obligation about multiplication or unit
       occurs anywhere below.
     - REUSED PROOF SHAPE.  [Monoid_Product]'s three monoid laws are taken
       wholesale; only the inversion and the two inverse laws
       ([grp_prod_left_inverse], [grp_prod_right_inverse]) are new work, and
       their leg lemmas follow the shape of #503's [mon_prod_assoc_leg].

   WHAT COULD NOT BE INSTANTIATED, AND WHY — MEASURED

   #503 states its half over an ARBITRARY monoidal base M.  This file cannot:
   [GroupObject] is declared over [CartesianMonoidal], because its two
   inverse laws are written in copy/discard vocabulary (∆ and [eliminate])
   that a bare [Monoidal] does not supply.  That is pinned as negative 1
   below — a TYPING failure, "The term M has type Monoidal while it is
   expected to have type CartesianMonoidal" — against a control at
   [CartesianMonoidal].  So the scope difference between the two files is a
   fact about the DEFINITION of a group object, not a weakness of this
   development, and no route around it is offered.

   The consolation is real and is delivered: since a cartesian monoidal
   category IS cartesian (Fox's theorem, [CartesianMonoidal_Cartesian],
   Structure/Monoidal/Heunen_Vicary/Cartesian.v) and its unit IS terminal
   ([SemicartesianMonoidal_Terminal]), the finite products of [GrpCat] cost
   NO hypothesis at all: [GrpCat_Cartesian_tensor] and
   [GrpCat_Terminal_unit] instantiate the general theorems at those two, and
   [grpcat_tensor_product] / [grpcat_unit_terminal] record by [eq_refl] that
   the product is then carried by the tensor and the terminal object by I.
   The general forms are kept, and are strictly more general: they take a
   [Cartesian C] and a [Terminal C] with NO assumed compatibility with ⨂,
   exactly as #503 does.

   THE INVERSE-PRESERVATION THEOREM, AND WHAT IT COST

   [GroupHom_inverse] is ten tactic lines.  Its content is the elementwise
   argument "f(a⁻¹) is a left inverse of f(a), and left inverses are unique",
   run diagrammatically: reshape (f ∘ ι_x) ⨂ f as (f ⨂ f) ∘ (ι_x ⨂ id) by
   [bimap_comp], push f out through the multiplication square, collapse what
   remains by the SOURCE object's [left_inverse], and finish with the unit
   triangle.  Uniqueness of left inverses in the TARGET is
   Structure/Group/Proofs.v's [left_inverse_unique], which is where the
   diagonal's naturality and the terminality of I are spent — that list is
   NOT exhaustive, and the omission matters: an audit found that donor's
   proof also does [rewrite <- right_inverse] (Structure/Group/Proofs.v:111)
   and spends [mappend_assoc_sym] and both [mempty_*_diagonal] helpers.  So
   correct a claim an earlier draft of this header made: [right_inverse] does
   not occur in [GroupHom_inverse]'s OWN tactic script, but the theorem DOES
   depend on [right_inverse] of the target through [left_inverse_unique].
   What is asymmetric is the script, not the dependency, and calling it "an
   asymmetry worth recording" was wrong.  No hypothesis beyond [MonoidHom] is
   needed.  Two right-associated readings of the inverse laws
   ([left_inverse_r], [right_inverse_r]) exist only to meet [rewrite]'s
   bracketing and carry no content.

   THE NAME.  The category is [GrpCat], not [Grp], and the reason is
   measured rather than aesthetic: Instance/Grp.v:466 already declares
   [Grp : Category] — the concrete category of groups over [Sets] — together
   with [Grp_Cartesian] (:677), [Grp_Terminal] (:562), [Grp_Forget] (:493)
   and [Grp_Forget_Faithful] (:512), FIVE collisions found with [rg] over the
   whole tree.  An earlier draft said four; an audit found the fifth.  The
   cause is worth recording because the obvious explanation is WRONG: it is
   not the [#[export] Program Instance] shape, since [Grp_Cartesian] has
   exactly that shape and WAS found.  The list was built from four GUESSED
   names instead of being derived from this file's own declared names under
   the rename — [GrpCat_Forget_Faithful] maps to [Grp_Forget_Faithful], and
   that name was simply never searched for.  This file requires none of those
   modules, so nothing is ambiguous within it; the rename exists so that a
   consumer may import both without qualifying.

   TWO ENGINEERING FINDINGS, both about NAMES rather than mathematics.

   - [inverse] IS A KEYWORD downstream of Structure/Group.v.  Its notation
     (:131) quotes the token, [Notation "'inverse' [ G ]"], which makes
     [inverse] a terminal symbol: [@inverse _ _ _ G] is then a PARSE error
     ("Syntax error: [global] or [pattern_ident] expected after '@'"), and
     the record-literal field name is rejected too — in the realistic
     multi-field shape [{| groupobject_is_monoid := _ ; inverse := _ |}],
     with "Syntax error: ['|}'] expected after [record_declaration]".  The
     shape matters and an earlier draft of this header got it wrong by
     quoting that message against a SINGLE-field literal: with [inverse]
     first the message is instead "Syntax error: [record_declaration]
     expected after '{|'".  Both are parse errors, so no kind claim changes.
     NEITHER can be pinned as a probe: [Fail] catches elaboration failures,
     and a parse error aborts the file even inside [Fail] — which is why
     these two findings are recorded in prose rather than guarded.  The
     notation itself takes the OBJECT and leaves the instance to resolution,
     which is fine in Structure/Group/Proofs.v but not here, where several
     group objects on different objects are in scope at once.  Both are
     worked around: [group_inverse] names the instance via the qualified
     [@Category.Structure.Group.inverse] (a qualified path DOES parse after
     [@]), and [GroupObject_Product] / [GroupObject_Terminal] are built with
     [Build_GroupObject] rather than record-literal syntax.
     [group_inverse_is] records by [eq_refl] that the accessor and the
     notation agree.
   - [fork] AND [fork_respects] ARE SHADOWED.  Structure/Monoidal/Relevance.v
     declares its own [fork] (the diagonal-built pairing) and its own
     [fork_respects] instance, and [Heunen_Vicary.v] re-exports Relevance, so
     merely naming [CartesianMonoidal] brings both into scope.  Consequently
     [GrpCat_Cartesian] must write [Cartesian.fork] for its field — the same
     workaround Heunen_Vicary/Cartesian.v:51 uses — and its respectfulness
     obligation must name [Cartesian.fork_respects].  The [△] NOTATION is
     unaffected: Structure/Cartesian.v:504 declares it against the resolved
     constant, so it keeps meaning the product's pairing.

   STRENGTHS, MEASURED STRICT FIRST.  Twenty Examples close by [eq_refl].
   Ten are identifications: the two structure maps of [group_monoid], the
   inversion accessor, the four readings of [GroupObject_Product], the
   terminal monoid, and the two [GrpCat_Mon]/[GrpCat_Forget] agreements.
   Six record that [GrpCat_Forget] carries the product, the terminal object,
   both projections, the pairing and the unique map to C's own; two that
   [GrpCat_Mon] does the same into [Mon C]; and two that the hypothesis-free
   instances of (7) put the product at the tensor and the terminal object
   at I.  The four
   homomorphism lemmas are stronger still, being CONVERSIONS rather than
   equalities of terms.  ONE fallback, and it is a refutation rather than a
   weakening: [Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget] is REJECTED at
   [eq_refl] (negative 3), diagnosed to [Compose] rebuilding its
   [fmap_respects], [fmap_id] and [fmap_comp] fields as fresh proof terms
   while BOTH data fields agree on the nose — the two controls
   [grpcat_mon_forget_obj] and [grpcat_mon_forget_map] are exactly that
   agreement.  An earlier draft of this header justified delivering no [≈]
   form by saying that stating it "needs a hom-setoid on functors" which
   "would pull a functor category into the closure of a [Theory/Algebra]
   file".  THAT WAS FALSE and an audit refuted it: [Functor_Setoid] and
   [Functor_StrictEq_Setoid] are Theory/Functor.v:149 and :606, which this
   file already requires at line 4, and no functor category is involved.  The
   equation is therefore DELIVERED, and at the STRICTER of the two available
   strengths: [forget_compose_strict] proves it in
   [Functor_StrictEq_Setoid] with every object component literally [eq_refl].
   So negative 3 says exactly what it says and no more — the composite is not
   the SAME RECORD, while the two functors are strictly equal as functors.

   UNIVERSES.  Measured in the constraint blocks AND read off the binders,
   and the two disagree in the way that matters.

   - THE BINDER carries the only identification in the file.  Every constant
     that binds a [C] is over [C : Category@{u u0 u0}] — C's hom and proof
     universes IDENTIFIED — and there are 110 such occurrences over the 55
     named constants (140 over all 70).  There IS exactly one other
     [Category@{...}] instance, and an earlier draft of this header wrongly
     said there was none: [GrpCat]'s own RESULT type [Category@{u2 u0 u0}],
     quoted in the [Mon]-comparison bullet below.  It identifies hom with
     proof too, so the point
     survives — every one of the 141 occurrences has 2nd level = 3rd.  Note
     the measurement trap that produced the error: [Print] WRAPS a universe
     instance across lines, so a line-based [grep -o] silently misses a split
     one; flatten whitespace before counting.  The CONSTRAINT
     BLOCKS, by contrast, contain no [=] at all: every entry is a [<=] or a
     [<].  Reading the blocks alone would report this file as carrying no
     identification whatever, which is false.
   - ATTRIBUTION IS PROBED, NOT GUESSED, and there is no single culprit.  In
     [Section UniverseDonors] below, over [C : Category@{uo uh up}] with
     [Constraint uh < up], each of [@Monoidal C], [@Cartesian C],
     [@Terminal C] and [@CartesianMonoidal C] is REJECTED with "Cannot
     enforce up = uh because uh < up", while [x ~> y] and [id[x]] are
     ACCEPTED at those very levels.  Four donors, each sufficient on its
     own — but NOT four INDEPENDENT ones, and an audit corrected that word:
     [CartesianMonoidal] contains [RelevanceMonoidal] (Heunen_Vicary.v:47),
     which contains [SymmetricMonoidal] (Relevance.v:47) and so ultimately
     [Monoidal], so its rejection is INHERITED and at most THREE are
     independent.  Nothing in this file adds to it, and it is not claimed
     unavoidable — all four are declared over unannotated
     [Context {C : Category}], the minimization family this tree records
     elsewhere.  The donor
     [GroupObject] inherits it visibly, printing as
     [GroupObject@{u u0 u1} (C : Category@{u u0 u0})].
   - THE COST OVER [Mon] IS EXACTLY ONE LEVEL, and that is measured by
     printing both AND COMPARING THE BLOCKS ENTRY FOR ENTRY — the two
     blocks below are quoted WHOLE, not sampled.  [Mon@{u u0 u1 u2}] has
     type [Category@{u u0 u0} → Monoidal@{u u0} → Category@{u1 u0 u0}] and
     a block of TEN entries: the strict [u0 < u2]; [u <= u1] and
     [u0 <= u1]; and SEVEN bounds on the universes of the sigma that
     carries the objects — [u <= Projections.u0], [u <= projections.u0],
     [u <= projections.u1], [u0 <= Projections.u0], [u0 <= Projections.u1],
     [u0 <= projections.u0] and [u0 <= projections.u1].  Those seven come
     from [sigT] — more precisely from its PROJECTIONS, [projT1]'s own
     monomorphic [Projections.u0]/[Projections.u1] and a lowercase pair,
     which an isolating probe separates from merely FORMING the pair (a bare
     [{x : obj[C] & x ~> x}] acquires no [Projections.*] entry at all).  An
     earlier draft glossed them as "both of C's levels sit below the pair's";
     that is wrong — the pair's own level is a [max] and never appears.
     [GrpCat@{u u0 u1 u2 u3}] has type
     [Category@{u u0 u0} → CartesianMonoidal@{u u0 u1} → Category@{u2 u0 u0}]
     and a block of TWELVE entries: that same ten with [u2] renamed [u3]
     and [u1] renamed [u2], PLUS EXACTLY TWO more, [u <= u1] and
     [u0 <= u1], for the extra level [CartesianMonoidal] itself carries —
     bounded by both of C's levels, identified with neither.  That
     two-entry difference is the whole cost.  Likewise [Mon_Terminal] has
     type [Terminal@{u u0} → Terminal@{u2 u0}] against [GrpCat_Terminal]'s
     [Terminal@{u u0} → Terminal@{u3 u0}], and [Mon_Cartesian] concludes
     [Cartesian@{u2 u0}] against [GrpCat_Cartesian]'s [Cartesian@{u3 u0}]:
     in each pair a NEW level carries the objects of the constructed
     category, bounded below by both of C's levels and identified with
     neither, so a consumer loses nothing.
   - The strict [u0 < ·] entry is present in [Mon], [Mon_Cartesian] and
     [Mon_Terminal] already, at the same place in the same shape, so it is
     inherited rather than introduced; #503's header isolates it to setoid
     [rewrite] inside a [Program] obligation and does not name the supplying
     constant, and no better attribution is offered here.
   - NO [Set] ANYWHERE.  No universe instance printed for any of the 70
     constants contains [Set].

   NEGATIVES.  Three in the [Probes] section, of TWO KINDS kept lexically
   apart, plus four in [Section UniverseDonors]; each was stripped of its
   [Fail] and its failure kind read off the message.

   - TYPING.  (1) [@GroupObject C M x] for [M : @Monoidal C] — "The term M
     has type Monoidal while it is expected to have type
     CartesianMonoidal".  (2) [MonoidHom] applied to the raw
     [groupobject_is_monoid] fields — "The term groupobject_is_monoid has
     type MonoidObject x", where a [Monoid x] is wanted, so #503's class
     passage is genuinely load-bearing and not a convenience.
   - CONVERSION.  (3) [Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget] — "The term
     eq_refl has type Mon_Forget ◯ GrpCat_Mon = Mon_Forget ◯ GrpCat_Mon
     while it is expected to have type Mon_Forget ◯ GrpCat_Mon =
     GrpCat_Forget".
   - FORMABILITY (universe).  The four donor rejections described above.

   Controls: every constant named in a negative is also named by a positive
   command in this file, so a rename upstream breaks the build rather than
   turning a negative vacuously green.  (An earlier draft said "a SUCCEEDING
   command", which is wrong for one of them: [groupobject_is_monoid]'s guard
   is [group_monoid]'s own body, which PRECEDES negative 2.  A
   control naming it after the negative has been added as well.)  Guarded:
   [GroupObject],
   [MonoidHom], [groupobject_is_monoid], [group_monoid], [GroupHom],
   [Mon_Forget], [GrpCat_Mon], [GrpCat_Forget], [Monoidal],
   [CartesianMonoidal], [Cartesian] and [Terminal] all appear in positive
   commands, the last four as bare [Check @Name] guards in the universe
   section so that a rename cannot make those four rejections succeed on a
   reference-not-found error.  Section-local [Universes]/[Constraint] do not
   leak: they relate only three freshly declared levels to each other.

   AXIOMS.  Every constant of this file reports "Closed under the global
   context" — the named ones (from the [.glob]) plus the [Program]
   obligations, which are invisible to a [.glob] sweep and must be queried by
   fully qualified name.  READ THE GRADE: that is a ONE-TIME measurement of
   the whole file.  The [make print-assumptions] gate carries a SELECTED 25
   of them permanently, so the ungated remainder — the leg lemmas, most
   Examples, and every obligation — is verified but not guarded against
   regression.

   NOT DELIVERED, with reasons.

   - No [Cocartesian GrpCat].  The coproduct of groups is not carried by the
     coproduct of the underlying objects (it is a free product), so nothing
     here dualises; #503 records the same for monoids, quoting Mac Lane 1950
     on the asymmetry.
   - No abelian/commutative group objects, and nothing about exponentials.
     Read the second half narrowly: an audit corrected an earlier draft that
     called the [Hom_Monoid] analogue a library gap.  It is not built HERE,
     but it EXISTS — Structure/Group/Representable.v:996's [exp_GroupObject]
     is a group structure on the hom-object, in a file this one does not
     require.
   - No infinite or indexed products: this matches [Cartesian], which is
     binary.
   - No monoidal structure on [GrpCat], so it is NOT claimed to be cartesian
     MONOIDAL, and the Eckmann-Hilton consequence (a group object in
     [GrpCat] is abelian) is neither stated nor proved.
   - [GrpCat_Mon] is proved FULL as well as faithful ([GrpCat_Mon_Full]),
     superseding an earlier draft of this header that said fullness was
     "neither proved nor refuted": an audit observed that the two hom types
     are convertible, so the identity section discharges it in three lines.
     Nothing is claimed either way about whether it reflects or creates
     limits.
   - No concrete instantiation: [Sets], [Coq], [Instance/Grp.v] and the rest
     are untouched, and in particular the [Grp_GroupObject] /
     [GroupObject_GrpObject] reconciliation of Instance/Grp.v is neither
     used nor related to [GrpCat].  A previous attempt to route this file
     through that reconciliation was rejected because it fixes C := [Sets]
     and would build a group object per point.
   - No [Isomorphism] or uniqueness statement for the product group object
     beyond what [Cartesian] itself supplies through [ump_products].
   - [prod_ext] is a general [Cartesian] fact and is NOT new: the identical
     statement at the identical generality is Theory/Lawvere/Sets.v:61's
     [prod_separates] (its dual is Construction/Cospan/Bridging.v:106).  It
     is redeclared here only because Theory/Lawvere/Sets.v is not in this
     file's closure; an earlier draft implied no analogue existed, which an
     audit refuted.  It is likewise not moved into Structure/Cartesian.v. *)

Section GroupHomomorphism.

Context {C : Category}.
Context `{CM : @CartesianMonoidal C}.

(** ** Reading a group object as an internal monoid *)

(* The underlying monoid of a group object, in the [mu]/[eta] presentation
   that [Mon] is indexed by.  [groupobject_is_monoid] lands in
   Structure/Monoid.v's [MonoidObject]; [Monoid_of_MonoidObject]
   (Theory/Algebra/Monoid/Product.v) renames its fields.  Both steps are at
   the SAME monoidal base, so no tensor changes hands. *)
Definition group_monoid {x : C} (G : GroupObject x) : Monoid x :=
  Monoid_of_MonoidObject (@groupobject_is_monoid _ _ _ G).

(* The inversion morphism of a NAMED group object.  Declared because
   Structure/Group.v:131's [inverse[G]] notation quotes the token [inverse],
   which makes it a keyword: [@inverse _ _ _ G] is then a parse error, and
   [inverse[x]] leaves the instance to resolution.  This accessor names the
   instance explicitly; the two agree by [eq_refl] ([group_inverse_is]). *)
Definition group_inverse {x : C} (G : GroupObject x) : x ~> x :=
  @Category.Structure.Group.inverse _ _ _ G.

Example group_inverse_is {x : C} (G : GroupObject x) :
  group_inverse G = inverse[x] := eq_refl.

(* The passage costs nothing: the multiplication and unit of [group_monoid G]
   ARE [G]'s own, at Leibniz equality. *)
Example group_monoid_mu {x : C} (G : GroupObject x) :
  mu[group_monoid G] = mappend[G] := eq_refl.

Example group_monoid_eta {x : C} (G : GroupObject x) :
  eta[group_monoid G] = mempty[G] := eq_refl.

(** ** Group homomorphisms *)

(* A homomorphism of group objects IS a homomorphism of the underlying monoid
   objects.  There is no inverse-preservation field; that it holds anyway is
   [GroupHom_inverse] below.  A plain [Definition] rather than a [Class]: the
   equality with [MonoidHom] is then definitional, so every lemma of
   Theory/Algebra/Monoid/Hom.v and Theory/Algebra/Monoid/Product.v about
   monoid homomorphisms applies to group homomorphisms with no adapter. *)
Definition GroupHom {x y : C} (Gx : GroupObject x) (Gy : GroupObject y)
           (f : x ~> y) : Type :=
  MonoidHom (group_monoid Gx) (group_monoid Gy) f.

Lemma group_hom_mappend {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ mappend[Gx] ≈ mappend[Gy] ∘ f ⨂ f.
Proof. exact (@hom_mu _ _ _ _ _ _ _ F). Qed.

Lemma group_hom_mempty {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ mempty[Gx] ≈ mempty[Gy].
Proof. exact (@hom_eta _ _ _ _ _ _ _ F). Qed.

(** ** Preservation of the inverse is a THEOREM *)

(* Right-associated readings of the two inverse laws, in the bracketing that
   [rewrite] leaves after [rewrite <- !comp_assoc]. *)
Lemma left_inverse_r {x : C} {G : GroupObject x} :
  mappend[G] ∘ (group_inverse G ⨂ id[x] ∘ ∆x) ≈ mempty[G] ∘ eliminate.
Proof. rewrite comp_assoc; apply left_inverse. Qed.

Lemma right_inverse_r {x : C} {G : GroupObject x} :
  mappend[G] ∘ (id[x] ⨂ group_inverse G ∘ ∆x) ≈ mempty[G] ∘ eliminate.
Proof. rewrite comp_assoc; apply right_inverse. Qed.

(* Awodey, Category Theory 2nd ed., Section 4.1: a morphism of the underlying
   monoid objects automatically commutes with the inversions, so the
   internal-group hom class needs no inverse-preservation axiom.

   The elementwise argument is "f(a⁻¹) is a left inverse of f(a), and left
   inverses are unique".  Diagrammatically: reshape (f ∘ ι_x) ⨂ f as
   (f ⨂ f) ∘ (ι_x ⨂ id) with [bimap_comp], push f out through the
   multiplication square [group_hom_mappend], collapse the remainder by the
   SOURCE object's [left_inverse], and finish with the unit triangle
   [group_hom_mempty].  Uniqueness of left inverses in the TARGET is
   Structure/Group/Proofs.v's [left_inverse_unique], which is where the
   diagonal's naturality and the terminality of I are spent.

   Note what is NOT used: [right_inverse] of either object appears nowhere in
   this proof. *)
Theorem GroupHom_inverse {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
        {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ group_inverse Gx ≈ group_inverse Gy ∘ f.
Proof.
  apply left_inverse_unique.
  assert (HB : (f ∘ group_inverse Gx) ⨂ f
                 ≈ f ⨂ f ∘ group_inverse Gx ⨂ id[x]).
  { rewrite <- bimap_comp; now rewrite id_right. }
  rewrite HB; clear HB.
  rewrite comp_assoc.
  rewrite <- (group_hom_mappend F).
  rewrite <- !comp_assoc.
  rewrite left_inverse_r.
  rewrite comp_assoc.
  now rewrite (group_hom_mempty F).
Qed.

(** ** The category of group objects *)

Lemma GroupHom_id {x : C} (G : GroupObject x) : GroupHom G G id.
Proof. exact (MonoidHom_id (group_monoid G)). Qed.

Lemma GroupHom_comp {x y z : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {Gz : GroupObject z} {f : y ~> z} {g : x ~> y} :
  GroupHom Gy Gz f → GroupHom Gx Gy g → GroupHom Gx Gz (f ∘ g).
Proof. exact MonoidHom_comp. Qed.

Lemma GroupHom_equiv {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f g : x ~> y} : f ≈ g → GroupHom Gx Gy f → GroupHom Gx Gy g.
Proof. exact MonoidHom_equiv. Qed.

(* Mac Lane, CWM 2nd ed., Section III.6, Exercise 2 (as scoped by issue #343);
   Awodey Section 4.1's Group(C).  Objects are objects of C equipped with a
   group-object structure, morphisms are C-morphisms equipped with a proof of
   homomorphy, and equivalence is equivalence of the underlying morphisms —
   the same sigma packaging as [Mon] (Theory/Algebra/Monoid/Hom.v:83) and as
   [Sub] (Construction/Subcategory.v).

   Named [GrpCat] and not [Grp]: Instance/Grp.v:466 already declares
   [Grp : Category], the concrete category of groups over [Sets], along with
   [Grp_Cartesian], [Grp_Terminal], [Grp_Forget] and
   [Grp_Forget_Faithful] (:512) — five collisions,
   measured with [rg] rather than guessed.  This file requires none of those
   modules, so nothing is ambiguous here; the rename exists so that a
   consumer may import both. *)
Program Definition GrpCat : Category := {|
  obj     := { x : C & GroupObject x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & GroupHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; GroupHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; GroupHom_comp `2 f `2 g)
|}.

(* The forgetful functor to C, faithful by construction: morphism equivalence
   in [GrpCat] IS equivalence of the underlying C-morphisms. *)
Program Definition GrpCat_Forget : GrpCat ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

#[export] Instance GrpCat_Forget_Faithful : Faithful GrpCat_Forget.
Proof. constructor; intros X Y f g E; exact E. Qed.

(* The forgetful functor to internal monoids.  Its arrow action is the
   IDENTITY on the underlying data — that is exactly the content of
   [GroupHom] being [MonoidHom] rather than a record extending it. *)
Program Definition GrpCat_Mon : GrpCat ⟶ Mon C := {|
  fobj := fun X => (`1 X; group_monoid `2 X);
  fmap := fun _ _ f => (`1 f; `2 f)
|}.

#[export] Instance GrpCat_Mon_Faithful : Faithful GrpCat_Mon.
Proof. constructor; intros X Y f g E; exact E. Qed.

(* And FULL, which costs three lines because the two hom types are
   CONVERTIBLE: [fobj[GrpCat_Mon] X ~{Mon C}~> fobj[GrpCat_Mon] Y] is
   [{f & MonoidHom (group_monoid `2 X) (group_monoid `2 Y) f}], and that IS
   [X ~{GrpCat}~> Y] by [GroupHom]'s definition.  So the section is the
   identity and its coherence is [reflexivity]. *)
#[export] Instance GrpCat_Mon_Full : Full GrpCat_Mon.
Proof.
  unshelve econstructor.
  - intros X Y g; exact g.
  - intros X Y g; simpl; reflexivity.
Qed.

(* [Mon_Forget ◯ GrpCat_Mon] and [GrpCat_Forget] agree on objects and on
   morphisms, at Leibniz equality.  The whole functor RECORDS are not
   compared; see the probe section at the end of the file. *)
Example grpcat_mon_forget_obj (X : GrpCat) :
  fobj[Mon_Forget] (fobj[GrpCat_Mon] X) = fobj[GrpCat_Forget] X := eq_refl.

Example grpcat_mon_forget_map (X Y : GrpCat) (f : X ~> Y) :
  fmap[Mon_Forget] (fmap[GrpCat_Mon] f) = fmap[GrpCat_Forget] f := eq_refl.

(* The two functors are moreover EQUAL in [Functor_StrictEq_Setoid], with
   every object component literally [eq_refl].  What negative 3 at the end of
   the file refutes is the strictly stronger claim that the composite is the
   SAME RECORD as [GrpCat_Forget]; [Compose] rebuilds the three law fields,
   so that fails while this succeeds.  No functor category is needed —
   [Functor_StrictEq_Setoid] is Theory/Functor.v:606, already required. *)
Example forget_compose_strict :
  @equiv _ (@Functor_StrictEq_Setoid GrpCat C)
    (Mon_Forget ◯ GrpCat_Mon) GrpCat_Forget.
Proof. exists (fun _ => eq_refl); intros; cat. Qed.

(** ** Binary products *)

Section GrpProduct.

Context `{CA : @Cartesian C}.

(* Two morphisms into a product agree when their components do.  A general
   [Cartesian] fact, declared here for want of a second consumer. *)
Lemma prod_ext {x y z : C} (f g : z ~> x × y) :
  exl ∘ f ≈ exl ∘ g → exr ∘ f ≈ exr ∘ g → f ≈ g.
Proof.
  intros Hl Hr.
  rewrite <- (prod_fork_eta f), <- (prod_fork_eta g).
  apply fork_inv; split; assumption.
Qed.

Section GrpProductData.

Context {x y : C} (X : GroupObject x) (Y : GroupObject y).

(* The componentwise inversion. *)
Definition grp_prod_inverse : x × y ~> x × y :=
  split (group_inverse X) (group_inverse Y).

Notation MU := (mon_prod_mu (group_monoid X) (group_monoid Y)).
Notation ETA := (mon_prod_eta (group_monoid X) (group_monoid Y)).

(* One component of the left inverse law.  [p] is a projection: [Hmu] says it
   commutes with the two multiplications, [Hinv] with the two inversions.
   The diagonal's naturality is what carries [p] past ∆, and the terminality
   of I ([eliminate_comp]) is what absorbs it on the other side. *)
Lemma grp_prod_left_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Hmu : p ∘ MU ≈ mappend[Z] ∘ bimap p p)
      (Hinv : p ∘ grp_prod_inverse ≈ group_inverse Z ∘ p) :
  p ∘ (MU ∘ grp_prod_inverse ⨂ id[x × y] ∘ ∆(x × y))
    ≈ mempty[Z] ∘ eliminate.
Proof.
  rewrite !comp_assoc, Hmu.
  rewrite <- (comp_assoc mappend[Z] (bimap p p) _).
  rewrite <- bimap_comp, Hinv, id_right.
  assert (E : (group_inverse Z ∘ p) ⨂ p
                ≈ group_inverse Z ⨂ id[z] ∘ bimap p p)
    by (rewrite <- bimap_comp; now rewrite id_left).
  rewrite E; clear E.
  rewrite <- !comp_assoc.
  rewrite (diagonal_natural _ _ p); simpl.
  rewrite (comp_assoc (group_inverse Z ⨂ id[z]) ∆z p), comp_assoc.
  rewrite left_inverse_r.
  rewrite <- comp_assoc.
  now rewrite eliminate_comp.
Qed.

Lemma grp_prod_right_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Hmu : p ∘ MU ≈ mappend[Z] ∘ bimap p p)
      (Hinv : p ∘ grp_prod_inverse ≈ group_inverse Z ∘ p) :
  p ∘ (MU ∘ id[x × y] ⨂ grp_prod_inverse ∘ ∆(x × y))
    ≈ mempty[Z] ∘ eliminate.
Proof.
  rewrite !comp_assoc, Hmu.
  rewrite <- (comp_assoc mappend[Z] (bimap p p) _).
  rewrite <- bimap_comp, Hinv, id_right.
  assert (E : p ⨂ (group_inverse Z ∘ p)
                ≈ id[z] ⨂ group_inverse Z ∘ bimap p p)
    by (rewrite <- bimap_comp; now rewrite id_left).
  rewrite E; clear E.
  rewrite <- !comp_assoc.
  rewrite (diagonal_natural _ _ p); simpl.
  rewrite (comp_assoc (id[z] ⨂ group_inverse Z) ∆z p), comp_assoc.
  rewrite right_inverse_r.
  rewrite <- comp_assoc.
  now rewrite eliminate_comp.
Qed.

Lemma grp_prod_eta_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Heta : p ∘ ETA ≈ mempty[Z]) :
  p ∘ (ETA ∘ @eliminate _ _ _ (x × y))
    ≈ mempty[Z] ∘ @eliminate _ _ _ (x × y).
Proof. now rewrite comp_assoc, Heta. Qed.

Lemma grp_prod_left_inverse :
  MU ∘ grp_prod_inverse ⨂ id[x × y] ∘ ∆(x × y) ≈ ETA ∘ eliminate.
Proof.
  apply prod_ext.
  - rewrite (grp_prod_left_leg X exl (mon_prod_mu_exl _ _) (exl_split _ _)).
    now rewrite (grp_prod_eta_leg X exl (mon_prod_eta_exl _ _)).
  - rewrite (grp_prod_left_leg Y exr (mon_prod_mu_exr _ _) (exr_split _ _)).
    now rewrite (grp_prod_eta_leg Y exr (mon_prod_eta_exr _ _)).
Qed.

Lemma grp_prod_right_inverse :
  MU ∘ id[x × y] ⨂ grp_prod_inverse ∘ ∆(x × y) ≈ ETA ∘ eliminate.
Proof.
  apply prod_ext.
  - rewrite (grp_prod_right_leg X exl (mon_prod_mu_exl _ _) (exl_split _ _)).
    now rewrite (grp_prod_eta_leg X exl (mon_prod_eta_exl _ _)).
  - rewrite (grp_prod_right_leg Y exr (mon_prod_mu_exr _ _) (exr_split _ _)).
    now rewrite (grp_prod_eta_leg Y exr (mon_prod_eta_exr _ _)).
Qed.

(* The product group object.  Its monoid half is #503's [Monoid_Product]
   CONSUMED, not reproved; only the inversion and the two inverse laws are
   new.  Built with [Build_GroupObject] rather than record-literal syntax,
   because the field name [inverse] is a keyword (see [group_inverse]). *)
Definition GroupObject_Product : GroupObject (x × y) :=
  Build_GroupObject (x × y)
    (MonoidObject_of_Monoid
       (Monoid_Product (group_monoid X) (group_monoid Y)))
    grp_prod_inverse grp_prod_left_inverse grp_prod_right_inverse.

(* The underlying monoid of the product group IS #503's product monoid, at
   Leibniz equality: the [Monoid]/[MonoidObject] round trip is definitional
   ([monoid_round], Theory/Algebra/Monoid/Product.v). *)
Example grp_prod_monoid :
  group_monoid GroupObject_Product
    = Monoid_Product (group_monoid X) (group_monoid Y) := eq_refl.

Example grp_prod_inverse_is :
  group_inverse GroupObject_Product = grp_prod_inverse := eq_refl.

Example grp_prod_mappend :
  mappend[GroupObject_Product]
    = mon_prod_mu (group_monoid X) (group_monoid Y) := eq_refl.

Example grp_prod_mempty :
  mempty[GroupObject_Product]
    = mon_prod_eta (group_monoid X) (group_monoid Y) := eq_refl.

(* The projections and the pairing are group homomorphisms — and each is
   #503's monoid statement applied verbatim, the two [GroupHom] goals being
   CONVERTIBLE with the corresponding [MonoidHom] ones. *)
Lemma grp_exl_hom : GroupHom GroupObject_Product X exl.
Proof. exact (mon_exl_hom (group_monoid X) (group_monoid Y)). Qed.

Lemma grp_exr_hom : GroupHom GroupObject_Product Y exr.
Proof. exact (mon_exr_hom (group_monoid X) (group_monoid Y)). Qed.

Lemma grp_fork_hom {z : C} {Z : GroupObject z} {f : z ~> x} {g : z ~> y} :
  GroupHom Z X f → GroupHom Z Y g → GroupHom Z GroupObject_Product (f △ g).
Proof. exact (@mon_fork_hom _ _ _ _ _ _ _ _ _ _ _). Qed.

End GrpProductData.

(* Binary products in GrpCat, carried by binary products of C.  No terminal
   object of C is used, and no compatibility between × and ⨂. *)
#[export] Program Instance GrpCat_Cartesian : @Cartesian GrpCat := {|
  product_obj := fun X Y => (`1 X × `1 Y; GroupObject_Product `2 X `2 Y);
  Cartesian.fork :=
    fun _ _ _ f g => (`1 f △ `1 g; grp_fork_hom _ _ `2 f `2 g);
  exl := fun X Y => (exl; grp_exl_hom `2 X `2 Y);
  exr := fun X Y => (exr; grp_exr_hom `2 X `2 Y)
|}.
Next Obligation. proper; now apply Cartesian.fork_respects. Qed.
Next Obligation. apply ump_products. Qed.

End GrpProduct.

(** ** The terminal group object *)

Section GrpTerminal.

Context `{TE : @Terminal C}.

(* The terminal object of C carries a unique group-object structure: every
   structure map lands in 1, so [one_unique] discharges both inverse laws
   just as it discharges the three monoid laws in [Terminal_Monoid]. *)
Definition GroupObject_Terminal : GroupObject (1 : C) :=
  Build_GroupObject (1 : C) (MonoidObject_of_Monoid Terminal_Monoid)
    one (one_unique _ _) (one_unique _ _).

Example grp_terminal_monoid :
  group_monoid GroupObject_Terminal = Terminal_Monoid := eq_refl.

(* Every morphism into 1 is a group homomorphism. *)
Lemma grp_one_hom {x : C} (G : GroupObject x) :
  GroupHom G GroupObject_Terminal one.
Proof. exact (mon_one_hom (group_monoid G)). Qed.

#[export] Program Instance GrpCat_Terminal : @Terminal GrpCat := {|
  terminal_obj := ((1 : C); GroupObject_Terminal);
  one := fun X => (one; grp_one_hom `2 X)
|}.
Next Obligation. apply one_unique. Qed.

End GrpTerminal.

(** ** The forgetful functor sends the finite products to C's own *)

Section GrpForget.

Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

Example GrpCat_Forget_product (X Y : GrpCat) :
  fobj[GrpCat_Forget] (X × Y)
    = fobj[GrpCat_Forget] X × fobj[GrpCat_Forget] Y := eq_refl.

Example GrpCat_Forget_terminal :
  fobj[GrpCat_Forget] (@terminal_obj GrpCat GrpCat_Terminal) = (1 : C)
  := eq_refl.

Example GrpCat_Forget_exl (X Y : GrpCat) :
  fmap[GrpCat_Forget] (@exl GrpCat GrpCat_Cartesian X Y) = exl := eq_refl.

Example GrpCat_Forget_exr (X Y : GrpCat) :
  fmap[GrpCat_Forget] (@exr GrpCat GrpCat_Cartesian X Y) = exr := eq_refl.

Example GrpCat_Forget_fork (X Y Z : GrpCat) (f : X ~> Y) (g : X ~> Z) :
  fmap[GrpCat_Forget] (@Cartesian.fork GrpCat GrpCat_Cartesian _ _ _ f g)
    = fmap[GrpCat_Forget] f △ fmap[GrpCat_Forget] g := eq_refl.

Example GrpCat_Forget_one (X : GrpCat) :
  fmap[GrpCat_Forget] (@one GrpCat GrpCat_Terminal X) = one := eq_refl.

(* GrpCat_Mon likewise preserves them on the nose. *)
Example GrpCat_Mon_product (X Y : GrpCat) :
  fobj[GrpCat_Mon] (X × Y) = fobj[GrpCat_Mon] X × fobj[GrpCat_Mon] Y
  := eq_refl.

Example GrpCat_Mon_terminal :
  fobj[GrpCat_Mon] (@terminal_obj GrpCat GrpCat_Terminal)
    = @terminal_obj (Mon C) Mon_Terminal := eq_refl.

End GrpForget.

End GroupHomomorphism.

Arguments GrpCat C {CM}.

Section GrpCatIntrinsic.

Context {C : Category}.
Context `{CM : @CartesianMonoidal C}.

Definition GrpCat_Cartesian_tensor : @Cartesian (GrpCat C) :=
  @GrpCat_Cartesian C CM CartesianMonoidal_Cartesian.

Definition GrpCat_Terminal_unit : @Terminal (GrpCat C) :=
  @GrpCat_Terminal C CM (@SemicartesianMonoidal_Terminal C _ _).

Example grpcat_tensor_product (X Y : GrpCat C) :
  fobj[GrpCat_Forget] (@product_obj _ GrpCat_Cartesian_tensor X Y)
    = (fobj[GrpCat_Forget] X ⨂ fobj[GrpCat_Forget] Y)%object := eq_refl.

Example grpcat_unit_terminal :
  fobj[GrpCat_Forget] (@terminal_obj _ GrpCat_Terminal_unit) = @I C _
  := eq_refl.

End GrpCatIntrinsic.

(** ** Probes *)

(* Each [Fail] below was stripped once and its failure kind read off the
   message; the kinds are kept lexically apart, TYPING first and CONVERSION
   last.  Every constant a negative names is also named by a succeeding
   command, so a rename breaks the build instead of silencing a probe. *)

Section Probes.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{CM : @CartesianMonoidal C}.
Context {x y : C} (Gx : @GroupObject C CM x) (Gy : @GroupObject C CM y).
Context (f : x ~> y).

(* NEGATIVE 1, TYPING.  A group object cannot be stated over a bare monoidal
   base: the inverse laws need the diagonal and the discard.  This is the
   whole of the scope difference from Theory/Algebra/Monoid/Product.v, which
   quantifies over an arbitrary [M : @Monoidal C].
     "The term "M" has type "Monoidal" while it is expected to have type
      "CartesianMonoidal"." *)
Fail Check (fun z : obj[C] => @GroupObject C M z).

(* CONTROL for negative 1. *)
Check (fun z : obj[C] => @GroupObject C CM z).

(* NEGATIVE 2, TYPING.  [MonoidHom] is indexed by Theory/Algebra/Monoid.v's
   [Monoid], not by Structure/Monoid.v's [MonoidObject], so the raw field of
   a group object does not fit and #503's class passage
   ([Monoid_of_MonoidObject], used by [group_monoid]) is load-bearing.
     "The term "groupobject_is_monoid" has type "MonoidObject x"" *)
Fail Check (MonoidHom (@groupobject_is_monoid _ _ _ Gx)
                      (@groupobject_is_monoid _ _ _ Gy) f).

(* CONTROLS for negative 2, naming every constant it mentions — including
   [groupobject_is_monoid] itself, whose only other positive occurrence is
   inside [group_monoid]'s body, which PRECEDES the negative. *)
Check (@groupobject_is_monoid C CM x Gx).
Check (MonoidHom (group_monoid Gx) (group_monoid Gy) f).
Check (GroupHom Gx Gy f).
Check (eq_refl : GroupHom Gx Gy f
                   = MonoidHom (group_monoid Gx) (group_monoid Gy) f).

(* NEGATIVE 3, CONVERSION.  The two forgetful functors agree on objects and
   on morphisms at [eq_refl] (the controls below), but the composite FUNCTOR
   RECORD is not [GrpCat_Forget]: [Compose] rebuilds [fmap_respects],
   [fmap_id] and [fmap_comp] as fresh proof terms.
     "The term "eq_refl" has type
      "Mon_Forget ◯ GrpCat_Mon = Mon_Forget ◯ GrpCat_Mon" while it is
      expected to have type "Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget"." *)
Fail Check (eq_refl : Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget).

(* CONTROLS for negative 3. *)
Check (fun (X : GrpCat C) => (eq_refl :
  fobj[Mon_Forget] (fobj[GrpCat_Mon] X) = fobj[GrpCat_Forget] X)).
Check (fun (X Y : GrpCat C) (g : X ~> Y) => (eq_refl :
  fmap[Mon_Forget] (fmap[GrpCat_Mon] g) = fmap[GrpCat_Forget] g)).

End Probes.

(** ** Where the hom/proof identification comes from *)

(* Four FORMABILITY negatives.  Over a category whose hom and proof levels
   are declared strictly apart, each of the four donors this file names is
   rejected, while a hom and an identity at those very levels are accepted —
   so the identification visible in every binder above is inherited from
   four sources, each sufficient on its own, and is not introduced here.
   They are NOT independent: [CartesianMonoidal] contains [Monoidal], so at
   most three are.  See the UNIVERSES section of the header. *)

Section UniverseDonors.

Universes uo uh up.
Constraint uh < up.

(* CONTROLS: the levels themselves are fine. *)
Check (fun (C : Category@{uo uh up}) (a b : C) => a ~> b).
Check (fun (C : Category@{uo uh up}) (a : C) => id[a]).

(* CONTROLS that the four donor names resolve, so that a rename cannot make
   the rejections below succeed on a reference-not-found error. *)
Check @Monoidal.
Check @Cartesian.
Check @Terminal.
Check @CartesianMonoidal.
Check @GroupObject.

(* Each reports: "Cannot enforce up = uh because uh < up". *)
Fail Check (fun C : Category@{uo uh up} => @Monoidal C).
Fail Check (fun C : Category@{uo uh up} => @Cartesian C).
Fail Check (fun C : Category@{uo uh up} => @Terminal C).
Fail Check (fun C : Category@{uo uh up} => @CartesianMonoidal C).

End UniverseDonors.
