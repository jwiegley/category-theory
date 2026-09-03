Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.

Generalizable All Variables.

(** * Adjoints of the slice and coslice projections *)

(* Reference: Saunders Mac Lane, "Categories for the Working
              Mathematician", 2nd ed., §IV.2, book p. 90, Exercise 11
              [maclane:IV.2:ex11]: if C has finite coproducts, the
              projection out of the coslice under an object a has a LEFT
              adjoint, sending c to the coproduct injection a ~> a + c,
              with the copairing as the transposition and the right
              injection as the unit.
   Reference: Steve Awodey, "Category Theory", 2nd ed., §9.9, Exercise 6
              (starred), printed p. 262 [awodey:9:ex6]: the slice-side
              dual.  The domain functor out of C/a has a RIGHT adjoint,
              sending y to the projection y × a ~> a; the starred half
              asks when it also has a LEFT one.
   nLab:      https://ncatlab.org/nlab/show/under+category
   nLab:      https://ncatlab.org/nlab/show/over+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   Both exercises are one construction seen twice.  A morphism out of a
   coproduct is a pair of clauses, one per summand
   (Structure/Cocartesian.v's header says exactly this of [merge]); a
   morphism into a product is a pair of components.  An object of the
   coslice under a is an object x with a chosen arrow a ~> x, and the
   free way to produce one from a bare c is to adjoin a: take a + c with
   its left injection.  A coslice arrow out of that object is then a
   clause on a -- pinned by the coslice condition to be the target's own
   structure map -- plus a FREE clause on c, which is exactly an
   unconstrained arrow c ~> x.  That is the bijection, and every line
   below is bookkeeping around it.  Dually a slice arrow into y × a with
   the second projection as structure map is a free first component plus
   a second component pinned to the source's structure map.

   ** File placement: a departure from the issue's suggestion

   The issue suggests [Construction/Slice/Coslice.v] "(or an extension of
   Construction/Slice.v)".  This file is [Construction/Slice/Adjunction.v]
   instead, because it carries BOTH the coslice adjunction (Block A) and
   its slice dual (Block B) -- built directly, not transported -- plus the
   two settle results of Block C and the [Sets] witnesses of Block D.
   "Coslice.v" would misname more than half its content.  Extending
   Construction/Slice.v in place was also declined: that file is required
   by Construction/Comma/Special.v, Construction/Slice/Pullback.v,
   Construction/Slice/Terminal.v, Instance/Cat/Pullback.v and others, and
   the material below drags in Structure/Cartesian.v,
   Structure/Cocartesian.v, Structure/Terminal.v, Structure/Initial.v,
   Theory/Adjunction.v and three Instance/Sets modules, which would land
   on every one of them.  The module closure here is 31 (measured with
   coqdep).

   ** What is delivered, and at what strength

   Block A, over [{C} {CC : @Cocartesian C} (a : C)]:

     - [Coslice_Proj a : Coslice C a ⟶ C], the projection, as a
       three-line record whose object and arrow actions are the literal
       first projections and hence reduce.
     - [Coslice_Coprod a : C ⟶ Coslice C a], sending c to
       [(a + c; inl)] and f to [right f].  READ THE OBJECT PRECISELY: the
       coslice structure map of the value is [inl : a ~> a + c] -- the
       injection Mac Lane's own sentence names -- while the UNIT below is
       [inr : c ~> a + c], the right injection.  The exercise's arrow
       reading "id + f" is [cover id f], and [coslice_fmap_is_cover]
       records that the delivered [right f] is that morphism with the
       redundant [∘ id] removed.
     - **[Coslice_Projection_Adjunction a : Coslice_Coprod a ⊣
       Coslice_Proj a]**, the issue's pinned name, built through
       [Build_Adjunction'] (Theory/Adjunction.v:159) out of the hom-setoid
       isomorphism [coslice_adj] plus the two forward naturality clauses.
       The transposition is
       [Hom_{a/C}((a + c; inl), (x; g)) ≊ Hom_C(c, x)]: forward
       [(h; _) ↦ h ∘ inr], backward [k ↦ (g ▽ k; _)].  The [to ∘ from]
       round trip is the equation [inr_merge] states and is discharged by
       the default obligation tactic; the [from ∘ to] one is [merge_comp],
       [merge_inl_inr] and [id_right] after rewriting with the condition.
     - [coslice_projection_unit a c : c ~> a + c := inr] and
       [coslice_projection_counit a x := (`2 x ▽ id; _)], with their
       grades against the class-produced [unit]/[counit] measured
       strict-first (see the next section).

   Block B, over [{C} {CA : @Cartesian C} (a : C)], and COVARIANT:

     - [Slice_Proj a : Slice C a ⟶ C], the domain functor.
     - [Slice_Prod a : C ⟶ Slice C a], sending x to [(x × a; exr)] and f
       to [first f]; [slice_fmap_is_split] is the "f × id" reading.
     - **[Slice_Projection_Adjunction a : Slice_Proj a ⊣ Slice_Prod a]**,
       transposition [Hom_C(x, y) ≊ Hom_{C/a}((x; g), (y × a; exr))],
       forward [k ↦ (k △ g; _)], backward [(h; _) ↦ exl ∘ h].
     - [slice_projection_unit a x := (id △ `2 x; _)] and
       [slice_projection_counit a y := exl].

   Block C settles the starred question, in both handednesses and with NO
   (co)product hypothesis anywhere -- the section binds only [{C} (a : C)]:

     - **[slice_proj_left_adjoint_iff_terminal a :
       { L : C ⟶ Slice C a & L ⊣ Slice_Proj a } ↔ IsTerminalObj a]**
     - **[coslice_proj_right_adjoint_iff_initial a :
       { R : C ⟶ Coslice C a & Coslice_Proj a ⊣ R } ↔ IsInitialObj a]**

     Each direction is a separately named lemma, so a consumer projects
     by conversion rather than through the packaged [iffT]:
     [slice_left_adjoint_terminal] / [slice_terminal_left_adjoint] with
     [slice_terminal_left_adjoint_adj], and the initial mirrors.  The
     enabling facts are [slice_id_IsTerminalObj] -- [(a; id)] is terminal
     in [Slice C a] -- and [coslice_id_IsInitialObj], its dual; each has
     one hand-discharged obligation, the UNIQUENESS clause, a unit law
     after rewriting with the competitor's condition, while the sigma's
     own hole closes by the default obligation tactic.  Necessity reads
     the singleton across the adjunction's [Sets]-isomorphism, and
     sufficiency builds the adjoint whose transposition is the identity
     on underlying arrows, so all four naturality clauses close by
     [reflexivity].

     Construction/Slice/Terminal.v:140's [Slice_Terminal :
     Slice C 1 ≅[Cat] C] is the SPECIAL CASE at a bundled [Terminal].  It
     is cited, not consumed: the object-level [IsTerminalObj] statement is
     what the exercise asks to settle, and routing through the bundled
     class would have required unbundling it again, where the direct
     argument is about fifteen lines.

   Block D exercises all of it over [Sets].

   ** The unit is literally the coproduct injection, and the residue is
      exhibited rather than described

   The issue's reviewer check is that the unit be the coproduct injection.
   [coslice_projection_unit a c] is [inr] with no wrapper at all -- a
   [Definition] whose body is the constant.  What the CLASS produces is
   [⌊id⌋], and the forward transpose post-composes with [inr] while the
   identity of the coslice is carried by [id] of C, so the class value is
   [id ∘ inr].  Both grades are recorded:

     - [coslice_unit_strict], an [Example] closing at [eq_refl]:
       [unit = id ∘ coslice_projection_unit a c].  The residue is stated
       literally, so a later change that removed it would break this line
       rather than pass unnoticed.
     - [coslice_unit_is_inr], the [≈] form, one [id_left] away.

   The strict identity [unit = inr] does NOT hold, and it is pinned as
   CONVERSION negative 7 in Test/ProbeSliceAdjunction365.v.

   The four grades are NOT uniform across the two blocks, and the pattern
   is worth carrying because it is mirror-image:

     - coslice UNIT: residue [id ∘ -], on the LEFT.
     - coslice COUNIT: STRICT on the underlying morphism --
       [coslice_counit_strict] gives [`1 (counit x) = `2 x ▽ id] at
       [eq_refl] -- and [≈] as a coslice arrow by [reflexivity], the
       coslice hom-setoid comparing first projections only.  The WHOLE
       records are not equal, since [coslice_projection_counit] carries
       its own obligation proof.
     - slice UNIT: STRICT on the underlying morphism,
       [`1 (unit x) = id △ `2 x].
     - slice COUNIT: residue [- ∘ id], on the RIGHT
       ([slice_counit_strict]), with [slice_counit_is_exl] the [≈] form,
       one [id_right] away.  Pinned as CONVERSION negative 8.

   The cause of the asymmetry is structural rather than incidental: [⌊id⌋]
   feeds the identity into the FORWARD transpose and [⌈id⌉] into the
   BACKWARD one, and in each block exactly one of the two transposes
   touches its argument by composition.

   ** The slice side is built directly, and the "one Opposite transport
      away" claim is measured

   The issue's work item 4 says the slice statement "is one [Opposite]
   transport away".  That is true up to isomorphism and NOT on the nose,
   and the reviewer check -- no residual [^op] in any delivered type -- is
   what makes the distinction bite.  Unfolding, the opposite of the slice
   over C^op has homs [∃ f, f ∘ `2 x ≈ `2 y] where Construction/Slice.v's
   [Coslice] has [∃ f, `2 y ≈ f ∘ `2 x]: the same equation in the other
   ORIENTATION, hence a different type.  Construction/Slice/Terminal.v
   already records exactly this at :177-198, as its reason for proving
   [Coslice_Initial] directly rather than transporting [Slice_Terminal].
   Here it is pinned as CONVERSION negative 9, against a control showing
   that the OBJECT types DO agree definitionally, so the obstruction is
   located at the hom equations and not at the encoding at large.

   Accordingly Block B is a direct construction.  The word [Opposite] and
   the token [^op] occur nowhere below, and [Structure/Cocartesian.v]'s
   own [Cocartesian C] notation -- which IS [Cartesian (C^op)] -- is the
   only place duality enters, in Block A, where it is the tree's own
   spelling for having coproducts.

   ** Prior art: three claims in the issue are stale, and one is its own

   (1) The issue's Awodey section says of the slice domain functor that
   "the functor itself does not exist".  It does, twice over.
   Instance/Cat/Pullback.v:668 [Slice_proj] and :847 [Coslice_proj] are
   this very three-line record, with the same signature [{C} (c)];
   Construction/Slice/Terminal.v:99 [Slice_Forget] and :206
   [Coslice_Forget] are its specialisations to a terminal and an initial
   base.  The agreement is MEASURED, in the probe rather than here: both
   DATA fields of [Coslice_Proj]/[Coslice_proj] agree at [eq_refl] in
   both handednesses, while the WHOLE records do not, the three [Functor]
   law fields being each file's own opaque obligations (CONVERSION
   negative 10).  The record is rebuilt rather than imported because
   Instance/Cat/Pullback.v's module closure is 39 and requiring it would
   add 14 modules to this file's 31.

   (2) The same section says "The whole slice development is
   Construction/Slice.v's four definitions plus the two base-change
   functors in Construction/Slice/Pullback.v".  It omits
   Construction/Slice/Terminal.v, twelve declared results including the
   two forgetful functors just named.

   (3) The issue's Mac Lane section says "A search over slice, coslice and
   comma files for [⊣] finds only the commented-out slice base-change
   stub".  The stub was real when that was written; it has since been
   deleted and the theorem proved, as Construction/Slice/Pullback.v's
   [Base_Functor_Adjunction].  Even then,
   Construction/Comma/Adjunction.v carries live [⊣] results throughout,
   among them [Comma_Functor_F_Id_Id_G] at :835 and Lawvere's
   biconditional [Adjunction_Comma] at :904 -- as the issue's own
   preceding paragraph says.

   (4) What the issue gets exactly right, and what this file therefore
   does not dispute, is the central absence: no functor sending c to the
   injection [a ~> a + c], no adjunction for either projection, and no
   coproduct-injection unit existed anywhere.

   The issue's own suggested route -- transport [comma_proj2]
   (Construction/Comma.v:204) across [Comma_Coslice]
   (Construction/Slice.v:181) -- is a THIRD way, and it is measured
   instead of dismissed.  The composite typechecks and is built in the
   probe as [p365_via_comma].  But [Comma_Coslice] is a [Program Instance]
   whose [to] is written [{| fobj := _; fmap := _ |}], so BOTH data fields
   of the comparison functor are obligations: not even the OBJECT action
   of the transport returns [`1 x] on the nose (CONVERSION negative 12),
   where the direct record has it definitionally.  Its [≅[Cat]] strength
   is a second cost, [Cat]'s hom-setoid being natural isomorphism.

   ** Universes: the identification is in the BINDER, not the block

   Every headline constant here -- the four functors, the two adjunctions,
   the two biconditionals -- is over [C : Category@{u u0 u0}], hom
   IDENTIFIED with proof by reuse of one level variable in the BINDER,
   while its constraint block contains NO equation at all: only [<] and
   [<=].  Reading the block alone reports "no identification" and is
   wrong; both must be read.  Measured, flattening whitespace first,
   since [Print] wraps universe instances:

     [Coslice_Proj@{u u0 u1 u2}], and identically [Coslice_Coprod],
     [Slice_Proj], [Slice_Prod]: [u0 < u1] plus five bounds.
     [Coslice_Projection_Adjunction@{u u0 u1 u2 u3}] and
     [Slice_Projection_Adjunction]: [u0 < u2] plus seventeen bounds
     ([Basics.compose], [Logic_lemmas.equality], [Projections],
     [prod_rect], [projections], [ID]).
     [slice_proj_left_adjoint_iff_terminal@{u u0 u1 u2 u3 u4 u5}] and
     [coslice_proj_right_adjoint_iff_initial]: [u0 < u1] plus twenty
     bounds.

   What stays FREE is the OBJECT universe: [u] occurs in no equation, only
   in bounds, in every one of the eight.  And no [Set] occurs in any
   binder or block, in the general results OR in the [Sets] witnesses --
   which is why Block D builds its two-element object as the coproduct
   [1 + 1] in [Sets] rather than at [bool].

   The hom-is-proof identification is INHERITED, and FIVE donors each
   force it ALONE.  Under a section declaring [Constraint uh < up], with
   the category, its hom-sets and its identities all accepted as controls,
   each of [Slice], [Coslice], [Cartesian] (hence [Cocartesian], which is
   that class at the opposite category), [IsTerminalObj] and
   [IsInitialObj] is rejected, every one with "Cannot enforce up = uh
   because uh < up"; so is this file's own [Coslice_Proj], which inherits
   it from [Coslice] and adds nothing.  All six are FORMABILITY negatives
   1-6 in the probe.  Nothing here introduces the identification and none
   of the five donors is claimed unavoidable.

   ** Witnesses over Sets

   [Sets_Coslice_Projection_Adjunction] and
   [Sets_Slice_Projection_Adjunction] instantiate both adjunctions at an
   ARBITRARY object of [Sets].  The transposition COMPUTES:
   [sets_coslice_transpose_computes] evaluates the copairing at a
   right-summand element and gets the given map's value back, at
   [eq_refl]; [sets_slice_transpose_is_fork] and
   [sets_slice_transpose_computes] do the slice mirror through the first
   component of the pair.

   Non-degeneracy is proved rather than gestured at.
   [sets_coslice_unit_not_iso] shows the unit [inr : c ~> a + c] is not an
   isomorphism as soon as [a] is inhabited: a two-sided inverse would send
   [inl x] into the right summand, and the coproduct setoid identifies
   nothing across summands.  So the adjunction is not an equivalence.

   Non-vacuity of Block C runs in BOTH directions and at both ends.
   [sets_bipoint] is [1 + 1], with [sets_bipoint_distinct] proving its two
   points inequivalent; [sets_bipoint_not_terminal] and
   [sets_bipoint_not_initial] then give
   [sets_slice_proj_no_left_adjoint] and
   [sets_coslice_proj_no_right_adjoint] -- OUTRIGHT refutations, obtained
   by running the biconditionals forwards.  At the other end
   [sets_slice_proj_left_adjoint_at_terminal] and
   [sets_coslice_proj_right_adjoint_at_initial] exhibit the positive case
   at [Sets_Terminal]'s and [Sets_Initial]'s own objects, by running them
   backwards.  So both biconditionals are exercised in both directions
   over one concrete category.

   ** Negatives

   Twelve, of THREE KINDS kept lexically apart, all in
   Test/ProbeSliceAdjunction365.v rather than here -- an in-file
   negative command is renamed in lockstep with the constant it guards
   and so cannot detect a rename, and keeping them out of the library
   file leaves this one with zero [make todo] hits.  Six are
   FORMABILITY (the five donors plus this file's inherited
   [Coslice_Proj]), five are CONVERSION (the
   two unit/counit residues, the orientation refutation, the whole-record
   comparison with [Coslice_proj], and the transport route), one is
   TYPING (the reversed handedness).  Each was stripped one at a time and
   its whole error read.  The probe also carries a scope-free instrument
   check and a control for every constant its negatives name.

   ** What is NOT delivered

   No comparison of either adjunction with the [Comma_Coslice]/
   [Comma_Slice] readings beyond the object-action measurement above; no
   monad or comonad from either adjunction, and in particular no
   identification of the coslice one with the "writer"/coreader pair that
   Construction/Slice.v's header points at; no naturality of anything in
   [a], hence no statement that [C/(-)] or [(-)/C] is functorial here
   (Construction/Slice/Pullback.v's [Bang_Functor] is the relevant
   neighbour and is untouched); no uniqueness of the adjoints, so the two
   biconditionals assert EXISTENCE of an adjoint and not that it is the
   one named; no relation to [Slice_Terminal]/[Coslice_Initial] as an
   equivalence, only the pointwise object-level settle results; no
   composite [Σ_f ⊣ f* ⊣ Π_f] and nothing about base change; no infinite
   or indexed variants; no [Sets]-side computation of either adjoint
   functor's action beyond the transposition; and no proof that the
   [Cocartesian] hypothesis of Block A is NECESSARY -- what is proved
   there is a construction from coproducts, not a converse.

   ** Engineering findings

   Three, all about elaboration rather than mathematics.

   [(a; id)] does not elaborate to the intended sigma from context alone:
   with [id : a ~> a] the pair fits both [∃ x, x ~> a] and [∃ y, a ~> y],
   and Coq picks the coslice shape even where a slice object is expected,
   reporting "has type ∃ y, a ~> y while it is expected to have type
   obj[C ̸ a]".  [slice_id_obj] and [coslice_id_obj] therefore give the
   predicate explicitly with [existT], which is also what lets every use
   site below read as a name.

   A [Program Definition] whose body is a sigma with a hole -- the shape
   [{| morphism := fun k => (t k; _) |}] -- routes the [Proper] obligation
   through a goal whose [rewrite] is rejected with "build_signature: no
   constraint can apply on a dependent argument".  Elaborating the sigma
   as its own named [Program Definition] first ([coslice_transpose],
   [slice_transpose]) removes the dependency and leaves an ordinary
   two-argument respectfulness goal.  Note also which obligation the
   default tactic closes: [iso_to_from] of [coslice_adj], [iso_from_to] of
   [slice_adj], and the sigma hole of the two terminal/initial witnesses,
   leaving the other to [Next Obligation]; the order is the field order.

   Third, and the reason the [Sets] block is [Set]-free: a constant
   [Sets]-morphism written as a [Program Definition] leaves its
   [proper_morphism] certificate to instance resolution, which supplies
   [CMorphisms.reflexive_proper@{Set Set}] and thereby pins the carrier
   universe.  Measured here: written that way, [sets_point] came out at
   [@{u |= Set < u}].  Supplying the pointwise term
   [fun _ _ _ => reflexivity b] by hand -- as an ordinary [Definition],
   no [Program] -- removes it.  The tree records the same hazard at
   Theory/Universal/Element.v, with the same repair; this is a second
   sighting rather than a new finding. *)


(** ** Block A: the coslice projection and its left adjoint *)

Section CosliceAdjunction.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context (a : C).

Program Definition Coslice_Proj : @Coslice C a ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Definition Coslice_Coprod : C ⟶ @Coslice C a := {|
  fobj := fun c => (a + c; inl);
  fmap := fun _ _ f => (right f; _)
|}.
Next Obligation. symmetry; apply inl_right. Qed.
Next Obligation. proper; now rewrite X. Qed.
Next Obligation. apply right_id. Qed.
Next Obligation. apply right_comp. Qed.

Program Definition coslice_adj_to (c : C) (y : @Coslice C a) :
  {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
   ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |}
    ~{Sets}~>
  {| carrier   := c ~{C}~> Coslice_Proj y
   ; is_setoid := @homset C c (Coslice_Proj y) |} := {|
  morphism := fun h => `1 h ∘ inr
|}.

(* The exercise words the arrow action as "id + f"; the tree spells that
   [cover id f], and [right f] is the same morphism with the redundant
   [∘ id] removed. *)
Lemma coslice_fmap_is_cover (x y : C) (f : x ~> y) :
  `1 (fmap[Coslice_Coprod] f) ≈ cover id f.
Proof.
  simpl; unfold right, cover.
  apply merge_respects; [ now rewrite id_right | reflexivity ].
Qed.

Program Definition coslice_transpose (c : C) (y : @Coslice C a)
  (k : c ~> `1 y) : Coslice_Coprod c ~{@Coslice C a}~> y := (`2 y ▽ k; _).

Program Definition coslice_adj_from (c : C) (y : @Coslice C a) :
  {| carrier   := c ~{C}~> Coslice_Proj y
   ; is_setoid := @homset C c (Coslice_Proj y) |}
    ~{Sets}~>
  {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
   ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |} := {|
  morphism := coslice_transpose c y
|}.
Next Obligation. intros k1 k2 Hk; simpl; now rewrite Hk. Qed.

Program Definition coslice_adj (c : C) (y : @Coslice C a) :
  @Isomorphism Sets
    {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
     ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |}
    {| carrier   := c ~{C}~> Coslice_Proj y
     ; is_setoid := @homset C c (Coslice_Proj y) |} := {|
  to   := coslice_adj_to c y;
  from := coslice_adj_from c y
|}.
Next Obligation.
  rewrite X, merge_comp, merge_inl_inr.
  apply id_right.
Qed.

Definition Coslice_Projection_Adjunction : Coslice_Coprod ⊣ Coslice_Proj.
Proof.
  unshelve eapply (@Build_Adjunction' (@Coslice C a) C
                     Coslice_Coprod Coslice_Proj coslice_adj).
  - intros x y z f g; simpl.
    rewrite <- !comp_assoc.
    now rewrite inr_right.
  - intros x y z f g; simpl.
    now rewrite <- !comp_assoc.
Defined.

Definition coslice_projection_unit (c : C) : c ~> a + c := inr.

Program Definition coslice_projection_counit (x : @Coslice C a) :
  Coslice_Coprod (Coslice_Proj x) ~{@Coslice C a}~> x := (`2 x ▽ id; _).

Example coslice_unit_strict (c : C) :
  @unit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction c = id ∘ coslice_projection_unit c
  := eq_refl.

Lemma coslice_unit_is_inr (c : C) :
  @unit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction c ≈ coslice_projection_unit c.
Proof. apply id_left. Qed.

Example coslice_counit_strict (x : @Coslice C a) :
  `1 (@counit (@Coslice C a) C Coslice_Coprod Coslice_Proj
        Coslice_Projection_Adjunction x) = `2 x ▽ id := eq_refl.

Lemma coslice_counit_is_merge (x : @Coslice C a) :
  @counit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction x ≈ coslice_projection_counit x.
Proof. simpl; reflexivity. Qed.

End CosliceAdjunction.

(** ** Block B: the slice projection and its right adjoint *)

Section SliceAdjunction.

Context {C : Category}.
Context {CA : @Cartesian C}.
Context (a : C).

Program Definition Slice_Proj : @Slice C a ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Definition Slice_Prod : C ⟶ @Slice C a := {|
  fobj := fun x => (x × a; exr);
  fmap := fun _ _ f => (first f; _)
|}.
Next Obligation. apply exr_first. Qed.
Next Obligation. proper; now rewrite X. Qed.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(* Dually, the slice arrow action is "f × id", spelled [split f id]; the
   [id ∘] on the second component is what [first f] omits. *)
Lemma slice_fmap_is_split (x y : C) (f : x ~> y) :
  `1 (fmap[Slice_Prod] f) ≈ split f id.
Proof.
  simpl; unfold first, split.
  apply fork_respects; [ reflexivity | now rewrite id_left ].
Qed.

Program Definition slice_transpose (x : @Slice C a) (y : C)
  (k : `1 x ~> y) : x ~{@Slice C a}~> Slice_Prod y := (k △ `2 x; _).

Program Definition slice_adj_to (x : @Slice C a) (y : C) :
  {| carrier   := Slice_Proj x ~{C}~> y
   ; is_setoid := @homset C (Slice_Proj x) y |}
    ~{Sets}~>
  {| carrier   := x ~{@Slice C a}~> Slice_Prod y
   ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |} := {|
  morphism := slice_transpose x y
|}.
Next Obligation. intros k1 k2 Hk; simpl; now rewrite Hk. Qed.

Program Definition slice_adj_from (x : @Slice C a) (y : C) :
  {| carrier   := x ~{@Slice C a}~> Slice_Prod y
   ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |}
    ~{Sets}~>
  {| carrier   := Slice_Proj x ~{C}~> y
   ; is_setoid := @homset C (Slice_Proj x) y |} := {|
  morphism := fun h => exl ∘ `1 h
|}.

Program Definition slice_adj (x : @Slice C a) (y : C) :
  @Isomorphism Sets
    {| carrier   := Slice_Proj x ~{C}~> y
     ; is_setoid := @homset C (Slice_Proj x) y |}
    {| carrier   := x ~{@Slice C a}~> Slice_Prod y
     ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |} := {|
  to   := slice_adj_to x y;
  from := slice_adj_from x y
|}.
Next Obligation.
  rewrite <- X, fork_comp, fork_exl_exr.
  apply id_left.
Qed.

Definition Slice_Projection_Adjunction : Slice_Proj ⊣ Slice_Prod.
Proof.
  unshelve eapply (@Build_Adjunction' C (@Slice C a)
                     Slice_Proj Slice_Prod slice_adj).
  - intros x y z f g; simpl.
    rewrite <- fork_comp.
    now rewrite (`2 g).
  - intros x y z f g; simpl.
    now rewrite first_fork.
Defined.

Program Definition slice_projection_unit (x : @Slice C a) :
  x ~{@Slice C a}~> Slice_Prod (Slice_Proj x) := (id △ `2 x; _).

Definition slice_projection_counit (y : C) :
  Slice_Proj (Slice_Prod y) ~> y := exl.

Example slice_unit_strict (x : @Slice C a) :
  `1 (@unit C (@Slice C a) Slice_Proj Slice_Prod
        Slice_Projection_Adjunction x) = id △ `2 x := eq_refl.

Lemma slice_unit_is_fork (x : @Slice C a) :
  @unit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction x ≈ slice_projection_unit x.
Proof. simpl; reflexivity. Qed.

Example slice_counit_strict (y : C) :
  @counit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction y = slice_projection_counit y ∘ id
  := eq_refl.

Lemma slice_counit_is_exl (y : C) :
  @counit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction y ≈ slice_projection_counit y.
Proof. apply id_right. Qed.

End SliceAdjunction.

(** ** Block C: when do the projections have adjoints on the other side? *)

Section SliceSettle.

Context {C : Category}.
Context (a : C).

Definition slice_id_obj : @Slice C a :=
  existT (fun x : C => x ~> a) a id.
Definition coslice_id_obj : @Coslice C a :=
  existT (fun x : C => a ~> x) a id.

Program Definition slice_id_IsTerminalObj :
  @IsTerminalObj (@Slice C a) slice_id_obj := fun x => {|
  unique_obj := (`2 x; _);
  unique_property := I
|}.
Next Obligation. rewrite <- X; apply id_left. Qed.

Program Definition coslice_id_IsInitialObj :
  @IsInitialObj (@Coslice C a) coslice_id_obj := fun x => {|
  unique_obj := (`2 x; _);
  unique_property := I
|}.
Next Obligation. rewrite X; apply id_right. Qed.

Lemma slice_left_adjoint_terminal (L : C ⟶ @Slice C a)
  (A : L ⊣ Slice_Proj a) : IsTerminalObj a.
Proof.
  intro c.
  unshelve econstructor.
  - exact (to (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj)
             (unique_obj (slice_id_IsTerminalObj (L c)))).
  - exact I.
  - intros v _.
    transitivity
      (to (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj)
         (from (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj) v)).
    + apply proper_morphism.
      apply (uniqueness (slice_id_IsTerminalObj (L c)) _ I).
    + apply (iso_to_from
               (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj) v).
Qed.

Program Definition slice_terminal_left_adjoint (H : IsTerminalObj a) :
  C ⟶ @Slice C a := {|
  fobj := fun x => (x; is_terminal_one H);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply (is_terminal_unique H). Qed.

Program Definition slice_terminal_adj (H : IsTerminalObj a)
  (x : C) (y : @Slice C a) :
  @Isomorphism Sets
    {| carrier   := slice_terminal_left_adjoint H x ~{@Slice C a}~> y
     ; is_setoid :=
         @homset (@Slice C a) (slice_terminal_left_adjoint H x) y |}
    {| carrier   := x ~{C}~> Slice_Proj a y
     ; is_setoid := @homset C x (Slice_Proj a y) |} := {|
  to   := {| morphism := fun h => `1 h |};
  from := {| morphism := fun k => (k; _) |}
|}.
Next Obligation. apply (is_terminal_unique H). Qed.

Definition slice_terminal_left_adjoint_adj (H : IsTerminalObj a) :
  slice_terminal_left_adjoint H ⊣ Slice_Proj a.
Proof.
  unshelve eapply (@Build_Adjunction' (@Slice C a) C
                     (slice_terminal_left_adjoint H) (Slice_Proj a)
                     (slice_terminal_adj H)).
  - intros x y z f g; simpl; reflexivity.
  - intros x y z f g; simpl; reflexivity.
Defined.

Theorem slice_proj_left_adjoint_iff_terminal :
  { L : C ⟶ @Slice C a & L ⊣ Slice_Proj a } ↔ IsTerminalObj a.
Proof.
  split.
  - intros [L A]; exact (slice_left_adjoint_terminal L A).
  - intro H.
    exists (slice_terminal_left_adjoint H).
    exact (slice_terminal_left_adjoint_adj H).
Defined.

Lemma coslice_right_adjoint_initial (R : C ⟶ @Coslice C a)
  (A : Coslice_Proj a ⊣ R) : IsInitialObj a.
Proof.
  intro c.
  unshelve econstructor.
  - exact (from (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c)
             (unique_obj (coslice_id_IsInitialObj (R c)))).
  - exact I.
  - intros v _.
    transitivity
      (from (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c)
         (to (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c) v)).
    + apply proper_morphism.
      apply (uniqueness (coslice_id_IsInitialObj (R c)) _ I).
    + apply (iso_from_to
               (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c) v).
Qed.

Program Definition coslice_initial_right_adjoint (H : IsInitialObj a) :
  C ⟶ @Coslice C a := {|
  fobj := fun x => (x; is_initial_zero H);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply (is_initial_unique H). Qed.

Program Definition coslice_initial_adj (H : IsInitialObj a)
  (x : @Coslice C a) (y : C) :
  @Isomorphism Sets
    {| carrier   := Coslice_Proj a x ~{C}~> y
     ; is_setoid := @homset C (Coslice_Proj a x) y |}
    {| carrier   := x ~{@Coslice C a}~> coslice_initial_right_adjoint H y
     ; is_setoid :=
         @homset (@Coslice C a) x
           (coslice_initial_right_adjoint H y) |} := {|
  to   := {| morphism := fun k => (k; _) |};
  from := {| morphism := fun h => `1 h |}
|}.
Next Obligation. apply (is_initial_unique H). Qed.

Definition coslice_initial_right_adjoint_adj (H : IsInitialObj a) :
  Coslice_Proj a ⊣ coslice_initial_right_adjoint H.
Proof.
  unshelve eapply (@Build_Adjunction' C (@Coslice C a)
                     (Coslice_Proj a) (coslice_initial_right_adjoint H)
                     (coslice_initial_adj H)).
  - intros x y z f g; simpl; reflexivity.
  - intros x y z f g; simpl; reflexivity.
Defined.

Theorem coslice_proj_right_adjoint_iff_initial :
  { R : C ⟶ @Coslice C a & Coslice_Proj a ⊣ R } ↔ IsInitialObj a.
Proof.
  split.
  - intros [R A]; exact (coslice_right_adjoint_initial R A).
  - intro H.
    exists (coslice_initial_right_adjoint H).
    exact (coslice_initial_right_adjoint_adj H).
Defined.

End SliceSettle.

(** ** Block D: witnesses over [Sets] *)

Definition Sets_Coslice_Projection_Adjunction (a : Sets) :
  Coslice_Coprod a ⊣ Coslice_Proj a := Coslice_Projection_Adjunction a.

Definition Sets_Slice_Projection_Adjunction (a : Sets) :
  Slice_Proj a ⊣ Slice_Prod a := Slice_Projection_Adjunction a.

Definition sets_bipoint : Sets :=
  @Coprod Sets Sets_Cocartesian
    (@terminal_obj Sets Sets_Terminal)
    (@terminal_obj Sets Sets_Terminal).

Definition sets_bipoint_l : carrier sets_bipoint := Datatypes.inl ttt.
Definition sets_bipoint_r : carrier sets_bipoint := Datatypes.inr ttt.

Lemma sets_bipoint_distinct : sets_bipoint_l ≈ sets_bipoint_r → False.
Proof. intro H; exact H. Qed.

(* The [proper_morphism] certificate is written out as a POINTWISE TERM
   rather than left to instance resolution.  Resolution finds
   [CMorphisms.reflexive_proper@{Set Set}] here and thereby pins the
   carrier universe of [Sets] to [Set]; the tree records the same hazard
   at Theory/Universal/Element.v.  With the term supplied by hand both
   constants stay polymorphic. *)
Definition sets_point (b : carrier sets_bipoint) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> sets_bipoint :=
  {| morphism        := fun _ => b
   ; proper_morphism := fun _ _ _ => reflexivity b |}.

Definition sets_bipoint_const (b : carrier sets_bipoint) :
  sets_bipoint ~{Sets}~> sets_bipoint :=
  {| morphism        := fun _ => b
   ; proper_morphism := fun _ _ _ => reflexivity b |}.

Lemma sets_bipoint_not_terminal : IsTerminalObj sets_bipoint → False.
Proof.
  intro H.
  exact (is_terminal_unique H (sets_point sets_bipoint_l)
           (sets_point sets_bipoint_r) ttt).
Qed.

Lemma sets_bipoint_not_initial : IsInitialObj sets_bipoint → False.
Proof.
  intro H.
  exact (is_initial_unique H id (sets_bipoint_const sets_bipoint_l)
           sets_bipoint_r).
Qed.

Theorem sets_slice_proj_no_left_adjoint :
  { L : Sets ⟶ @Slice Sets sets_bipoint & L ⊣ Slice_Proj sets_bipoint } → False.
Proof.
  intro X.
  exact (sets_bipoint_not_terminal
           (fst (slice_proj_left_adjoint_iff_terminal sets_bipoint) X)).
Qed.

Theorem sets_coslice_proj_no_right_adjoint :
  { R : Sets ⟶ @Coslice Sets sets_bipoint & Coslice_Proj sets_bipoint ⊣ R }
    → False.
Proof.
  intro X.
  exact (sets_bipoint_not_initial
           (fst (coslice_proj_right_adjoint_iff_initial sets_bipoint) X)).
Qed.

Definition sets_slice_proj_left_adjoint_at_terminal :
  { L : Sets ⟶ @Slice Sets (@terminal_obj Sets Sets_Terminal)
      & L ⊣ Slice_Proj (@terminal_obj Sets Sets_Terminal) } :=
  snd (slice_proj_left_adjoint_iff_terminal
         (@terminal_obj Sets Sets_Terminal))
    (IsTerminalObj_from_Terminal Sets_Terminal).

Definition sets_coslice_proj_right_adjoint_at_initial :
  { R : Sets ⟶ @Coslice Sets (@initial_obj Sets Sets_Initial)
      & Coslice_Proj (@initial_obj Sets Sets_Initial) ⊣ R } :=
  snd (coslice_proj_right_adjoint_iff_initial
         (@initial_obj Sets Sets_Initial))
    (IsInitialObj_from_Initial Sets_Initial).

Example sets_coslice_transpose_computes (a c : Sets)
  (y : @Coslice Sets a) (k : c ~{Sets}~> Coslice_Proj a y)
  (z : carrier c) :
  `1 (coslice_transpose a c y k) (Datatypes.inr z) = k z := eq_refl.

Example sets_slice_transpose_is_fork (a : Sets) (x : @Slice Sets a)
  (y : Sets) (k : `1 x ~{Sets}~> y) :
  `1 (slice_transpose a x y k) = k △ `2 x := eq_refl.

Example sets_slice_transpose_computes (a : Sets) (x : @Slice Sets a)
  (y : Sets) (k : `1 x ~{Sets}~> y) (z : carrier (`1 x)) :
  Datatypes.fst ((k △ `2 x) z) = k z := eq_refl.

Lemma sets_coslice_unit_not_iso (a c : Sets) (x : carrier a) :
  IsIsomorphism (@coslice_projection_unit Sets Sets_Cocartesian a c)
    → False.
Proof.
  intros [g Hr Hl].
  exact (Hr (Datatypes.inl x)).
Qed.
