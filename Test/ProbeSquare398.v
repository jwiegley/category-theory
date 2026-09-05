Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Square.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Map.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Cat.Bicategory.Square.
Require Import Category.Instance.Cat.Bicategory.Adjunction.

Generalizable All Variables.

(** * Probe for Adjunction/Square.v and Instance/Cat/Bicategory/Square.v *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7,
   book p. 103, Exercise 4 (Kelly, adjoint squares) and Exercise 5
   (Palmquist); Riehl, "Category Theory in Context", 2nd ed., §4.3,
   Exercise 4.3.v.  The two exercises are quoted verbatim in the header of
   Adjunction/Square.v; they are not repeated here.

   This file guards the strict claims of those two headers.  Every
   statement below that is asserted to be refuted has been STRIPPED into
   its own scratch file carrying this file's whole Require prefix, compiled
   ALONE, and its complete error read; under this repo's coqc a passing
   [Fail] prints nothing, so a whole-file rc=0 alone would establish only
   THAT each command does not typecheck and never WHY.  Each negative is
   classified by the error TEXT, not by expectation:

     CONVERSION  — "cannot unify A and B" between two inhabitants of one
                   type; no universe clause.
     TYPING      — a plain "The term T has type X while it is expected to
                   have type Y"; NO "cannot unify", no universe clause.
     FORMABILITY — "(universe inconsistency: Cannot enforce ...)", naming
                   the levels the enclosing section declares.

   ** TALLY

   25 [Fail] commands = 1 instrument check + 24 negatives, in three kinds:
   TWELVE conversion (N1-N9, N11, N12, N20), THREE typing (N10, N13, N21)
   and NINE formability (N14-N19, N22-N24).  Numbering N1-N19 is the Core
   builder report's §10; N20-N24 are added here.  The Core stripped only
   two of its nineteen (N14 and N16), so the kinds of the other seventeen
   were its expectation; all twenty-four are measured here.

   ONE MEASUREMENT CORRECTS AN ATTRIBUTION.  Adjunction/Square.v's header
   says of the hom = proof identification that "the donor is
   [Adjunction]", listing five commands accepted under [ch < cp] of which
   only [Fu ⊣ Uu] is refused.  That sentence is true of those five, but it
   is not discriminating: N24 refutes [Uq ◯ Fq] at the same levels with NO
   adjunction anywhere in the command, so [Compose] is a SECOND donor,
   sufficient on its own.  N24 was written as a sixth CONTROL and became a
   negative when it was compiled.  The two [⟹] commands that replace it
   are accepted, so [Transform] remains a non-donor.

   ONE KIND DIVERGES FROM THAT EXPECTATION.  The Core's §10 lists N10 —
   [square_bijection] at K = L = Id against [conjugate_bijection] — as
   CONVERSION.  Stripped, it is TYPING: the two isomorphisms do not share
   a type at all (their [SetoidObject] endpoints differ), so elaboration
   stops before any unification of inhabitants, and the error carries no
   "cannot unify" clause.  N9, the [sq_dom]/[conj_dom] comparison one
   level down, IS conversion, because both sides are [SetoidObject]s.

   ** THE VERBATIM ERROR TAILS

   N1  CONVERSION
     (cannot unify "palm_via_mate A A' K L al x" and
      "palm_to A A' K L al x").
   N2  CONVERSION
     (cannot unify "palm_to A A' K L al x" and
      "palm_two_factor A A' K L al x").
   N3  CONVERSION
     The term "eq_refl" has type "unit = unit" while it is expected to
     have type "unit = fmap[U] unit o unit"
     (cannot unify "unit" and "fmap[U] unit o unit").
     [the display suppresses every implicit, so the two sides read alike;
      the composite adjunction's unit is the left one]
   N4  CONVERSION
     (cannot unify "F' o L o U ==> K" and "F' o (L o U) ==> K").
   N5  CONVERSION
     (cannot unify "L ==> U' o K o F" and "L ==> U' o (K o F)").
   N6  CONVERSION
     (cannot unify "F' o L o U" and "F' o (L o U)").
   N7  CONVERSION
     (cannot unify "F2 o Id[D] ==> Id[C] o F" and "F2 ==> F").
   N8  CONVERSION
     (cannot unify "F2 o Id[D]" and "F2").
   N9  CONVERSION
     The term "eq_refl" has type "sq_dom Id[C] Id[D] = sq_dom Id[C] Id[D]"
     while it is expected to have type "sq_dom Id[C] Id[D] = conj_dom"
     (cannot unify "sq_dom Id[C] Id[D]" and "conj_dom").
   N10 TYPING
     The term "conjugate_bijection A A2" has type "conj_dom ~= conj_cod"
     while it is expected to have type
     "sq_dom Id[C] Id[D] ~= sq_cod Id[C] Id[D]".
   N11 CONVERSION
     The term "eq_refl" has type "fun_comp_assoc x = fun_comp_assoc x"
     while it is expected to have type "fun_comp_assoc x = id{D'}"
     (cannot unify "fun_comp_assoc x" and "id{D'}").
   N12 CONVERSION
     (cannot unify "SqMate A A' K L sg a" and
      "mate (SqBA A) (SqBA' A') sg a").
   N13 TYPING
     The term "sigma x" has type
     "fobj[F'] (fobj[L] x) ~{ C' }~> fobj[K] (fobj[F] x)"
     while it is expected to have type
     "fobj[K] (fobj[F] x) ~= fobj[F'] (fobj[L] x)".
   N14 FORMABILITY
     The term "Fq" has type "@Functor@{co ch cp co ch cp} Du Cu"
     while it is expected to have type "@Functor@{...} ?D ?C"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N15 FORMABILITY
     The term "Aq" has type "Category@{ao ah ah}"
     while it is expected to have type "Category@{...}"
     (universe inconsistency: Cannot enforce ah = ... because ah < bh
      <= ...).
   N16 FORMABILITY
     The term "Lu" has type "@Functor@{co cho cho c2o ch2 ch2} Du D2u"
     while it is expected to have type "@Functor@{... ch2 ch2 c2o ch2
     ch2} ?C D2u"
     (universe inconsistency: Cannot enforce cho = ch2 because cho < ch2).
   N17 FORMABILITY
     (universe inconsistency: Cannot enforce ch2 = cho because cho < ch2).
   N18 FORMABILITY
     (universe inconsistency: Cannot enforce ch2 = cho because cho < ch2).
   N19 FORMABILITY
     (universe inconsistency: Cannot enforce cho = ch2 because cho < ch2).
   N20 CONVERSION
     (cannot unify "sq_mate_inv A A' K L (sq_mate A A' K L sigma) x" and
      "sigma x").
   N21 TYPING
     The term "ta" has type "L o U ==> U' o K" while it is expected to
     have type "F' o L ==> K o F".
   N22 FORMABILITY
     The term "C2u" has type "Category@{c2o ch2 ch2}" while it is
     expected to have type "Category@{... cho cho}"
     (universe inconsistency: Cannot enforce ch2 = cho because cho < ch2).
   N23 FORMABILITY
     The term "C2u" has type "Category@{c2o ch2 ch2}" while it is
     expected to have type "Category@{... cho cho}"
     (universe inconsistency: Cannot enforce ch2 = cho because cho < ch2).
   N24 FORMABILITY
     The term "Uq" has type "@Functor@{co ch cp co ch cp} Cu Du"
     while it is expected to have type "@Functor@{...} ?D ?E"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).

   (The tails above transcribe the unicode of the real messages as ASCII —
   [o] for the composition circle, [==>] for the transformation arrow and
   [~=] for the isomorphism sign — so that this comment stays free of the
   glyphs the sources use; the shape of every message is otherwise
   character for character what coqc printed.)

   ** WHAT EACH NEGATIVE PAIRS WITH

   Every negative sits beside a positive control that DOES hold, so that the
   guard measures a boundary rather than an absence.  N1/N2/N3/N12/N20 each
   pair with the library's own [≈] statement ([palm_to_via_mate],
   [palm_two_factor_agrees], [AB_unit_upto], [sq_mate_is_mate],
   [sq_mate_inv_mate]); N4/N5/N6 pair with [bracket_fobj_left] and
   [bracket_fmap_left], which locate the difference in the three LAW fields
   of [Compose] rather than in either data field; N7-N10 pair with three of
   the five [eq_refl] identifications with Adjunction/Conjugate.v
   ([ctrl_id_a], [ctrl_id_b], [ctrl_id_c]); N11 pairs with
   [fun_comp_assoc_component] ([= fmap[U'] id], strict) and
   [fun_comp_assoc_is_id] ([≈ id]); N13 pairs with [square_is_map_adj_hom],
   the same statement at an ISOMORPHISM family; N14 and N24 with seven
   commands accepted at the very levels that refuse them; N15 with the
   opposite functor direction; N16-N19 and N22/N23 with TEN commands
   accepted at levels declared strictly apart — the two bare component
   families, [AdjointSquare], [AdjointSquareUnit], [AdjointSquareCounit],
   both mate operators and [adjoint_square_iff_mate] — which is what
   attributes the collapse to [Compose] rather than to the condition.

   ** RENAME SIMULATION

   FOURTEEN target constants are named inside a negative:
   [palm_via_mate], [palm_to], [palm_two_factor], [AB], [sq_dom],
   [sq_cod], [square_bijection], [SqMate], [sq_mate], [sq_mate_inv],
   [SqSigma], [AdjointSquareT], [SqBA] and [SqBA'].  Each was renamed ONE
   AT A TIME in a SCRATCH COPY of its library file (never in place),
   together with a scratch copy of the sibling bridge file requiring it,
   both compiled under [-Q ... Scratch398]; a copy of this file requiring
   the two scratch modules instead of the two library ones was then
   compiled.  ALL FOURTEEN broke it, every one at a [Check] line of the
   guard block and NONE inside a [Fail]:

     palm_via_mate    line 295   Check @palm_via_mate.
     palm_to          line 294   Check @palm_to.
     palm_two_factor  line 296   Check @palm_two_factor.
     AB               line 297   Check @AB.
     sq_dom           line 291   Check @sq_dom.
     sq_cod           line 292   Check @sq_cod.
     square_bijection line 293   Check @square_bijection.
     SqMate           line 289   Check @SqMate.
     sq_mate          line 287   Check @sq_mate.
     sq_mate_inv      line 288   Check @sq_mate_inv.
     SqSigma          line 283   Check @SqSigma.
     AdjointSquareT   line 282   Check @AdjointSquareT.
     SqBA             line 298   Check @SqBA.
     SqBA'            line 299   Check @SqBA'.

   So 14/14, with zero vacuous guards.  (Renaming [palm_to], [SqMate] or
   [square_bijection] must also rename their [Program] obligations, whose
   names are that constant's name with [_obligation_n] appended; the
   simulation does so.)

   ** GUARD COVERAGE, measured mechanically

   Comments stripped, the file split into commands at a period followed by
   whitespace: 25 commands begin with [Fail]; they mention 95 distinct
   identifiers, of which 80 also occur in a command that is NOT a [Fail].
   The fifteen that do not are, exhaustively: the keyword [Fail] itself;
   [p398_no_such_constant_anywhere], the instrument's deliberately absent
   name; and the thirteen names of the [Fail Example]s themselves (n1-n12,
   n20), which never enter the environment because the commands that would
   have declared them do not typecheck.  No CONSTANT that a negative names
   is unguarded.

   ** make todo

   The repo's [todo] target greps every [.v] file, case-insensitively and
   with no word boundary, for its five alternatives: Fail, abort,
   undefined, jww and, between them, the hole-closing tactic name, which
   this comment does not spell because the aborted-sketch gate would
   count it.  This file contributes 40 such lines: the 25 [Fail] commands
   and 15 lines of the prose above.  The two library files contribute
   ZERO, which is the reason every refutation lives here rather than
   there.

   ** WHAT THIS FILE DOES NOT DO

   It proves nothing new.  It contains no proof hole of any kind, no
   hole-closing tactic, no [Axiom], no [Parameter] and no [Abort]; every
   positive control is a term, never a tactic script, so nothing here can
   drift by a change in the automation.  It does not measure universes beyond
   the three donor sections, does not count constants, and takes no position
   on the two headers' prose. *)

(* ---------------------------------------------------------------------- *)
(* INSTRUMENT.  A passing [Fail] prints nothing under this repo's coqc, so *)
(* this command establishes that [Fail] is doing anything at all.          *)
(* ---------------------------------------------------------------------- *)

Fail Check p398_no_such_constant_anywhere.

(* ---------------------------------------------------------------------- *)
(* GUARD BLOCK.  Every constant that any negative below names, target and  *)
(* donor alike, is named here OUTSIDE every [Fail], so that renaming any   *)
(* one of them breaks this file at a [Check] line rather than turning a    *)
(* negative vacuously green.                                              *)
(* ---------------------------------------------------------------------- *)

Check @Category.
Check @Functor.
Check @Transform.
Check @Adjunction.
Check @Compose.
Check @Id.
Check @Isomorphism.
Check @Sets.
Check @SetoidObject.
Check @carrier.
Check @id.
Check @fobj.
Check @fmap.
Check @transform.
Check @Category.Theory.Adjunction.unit.
Check @eq.

Check @AdjointSquare.
Check @AdjointSquareUnit.
Check @AdjointSquareCounit.
Check @AdjointSquareT.
Check @SqSigma.
Check @SqTau.
Check @SigmaNat.
Check @TauNat.
Check @sq_mate.
Check @sq_mate_inv.
Check @SqMate.
Check @SqMateInv.
Check @sq_dom.
Check @sq_cod.
Check @square_bijection.
Check @palm_to.
Check @palm_via_mate.
Check @palm_two_factor.
Check @AB.
Check @SqBA.
Check @SqBA'.

Check @conj_dom.
Check @conj_cod.
Check @conjugate_bijection.
Check @conj_mate.
Check @conj_mate_inv.
Check @Conjugate.
Check @MapAdjHom.
Check @fun_comp_assoc.
Check @mate.
Check @mate_inv.

Check @palm_to_via_mate.
Check @palm_two_factor_agrees.
Check @AB_unit_upto.
Check @AB_to_strict.
Check @sq_mate_is_mate.
Check @sq_mate_inv_is_mate_inv.
Check @sq_mate_inv_mate.
Check @sq_mate_mate_inv.
Check @square_is_map_adj_hom.
Check @square_is_conjugate.
Check @sq_mate_is_conj_mate.
Check @sq_mate_inv_is_conj_mate_inv.
Check @fun_comp_assoc_component.
Check @fun_comp_assoc_is_id.
Check @bracket_fobj_left.
Check @bracket_fmap_left.
Check @adjoint_square_T_is_bare.
Check @adjoint_square_iff_mate.
Check @sq_mate_is_post_of_pre.
Check @sq_dom_setoid.
Check @sq_cod_setoid.
Check @adjoint_square_iff_Cat_mate.

(* ====================================================================== *)
(* (1) N1-N6, N11-N13, N20, N21 over the four-category context.           *)
(* ====================================================================== *)

Section P398Main.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

(* -- N1.  CONTROL: the mate route agrees with [palm_to] up to [≈]. -- *)

Example ctrl_n1 (al : F' ◯ L ◯ U ⟹ K) :
  @palm_via_mate C D F U A C' D' F' U' A' K L al
    ≈ @palm_to C D F U A C' D' F' U' A' K L al
  := @palm_to_via_mate C D F U A C' D' F' U' A' K L al.

Fail Example n1 (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  @eq (fobj[L] x ~{D'}~> fobj[U'] (fobj[K] (fobj[F] x)))
      (@palm_via_mate C D F U A C' D' F' U' A' K L al x)
      (@palm_to C D F U A C' D' F' U' A' K L al x) := eq_refl.

(* -- N2.  CONTROL: the two-factor route agrees componentwise up to [≈]. -- *)

Example ctrl_n2 (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  @palm_to C D F U A C' D' F' U' A' K L al x
    ≈ @palm_two_factor C D F U A C' D' F' U' A' K L al x
  := @palm_two_factor_agrees C D F U A C' D' F' U' A' K L al x.

Fail Example n2 (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  @eq (fobj[L] x ~{D'}~> fobj[U'] (fobj[K] (fobj[F] x)))
      (@palm_to C D F U A C' D' F' U' A' K L al x)
      (@palm_two_factor C D F U A C' D' F' U' A' K L al x) := eq_refl.

(* -- N4/N5/N6.  CONTROL: the two bracketings agree on objects and on   -- *)
(* -- arrows, so what the three negatives locate is the LAW fields.     -- *)

Example ctrl_n456a (a : C) :
  @eq (obj[C']) (fobj[F' ◯ L ◯ U] a) (fobj[F' ◯ (L ◯ U)] a)
  := @bracket_fobj_left C D U C' D' F' L a.

Example ctrl_n456b (a b : C) (f : a ~> b) :
  fmap[F' ◯ L ◯ U] f = fmap[F' ◯ (L ◯ U)] f
  := @bracket_fmap_left C D U C' D' F' L a b f.

Fail Example n4 :
  @eq Type (@Transform C C' (F' ◯ L ◯ U) K)
           (@Transform C C' (F' ◯ (L ◯ U)) K) := eq_refl.

Fail Example n5 :
  @eq Type (@Transform D D' L (U' ◯ K ◯ F))
           (@Transform D D' L (U' ◯ (K ◯ F))) := eq_refl.

Fail Example n6 :
  @eq (C ⟶ C') (F' ◯ L ◯ U) (F' ◯ (L ◯ U)) := eq_refl.

(* -- N11.  CONTROL: the associator's component IS [fmap[U'] id], and   -- *)
(* -- it is [≈ id] but not [= id].                                      -- *)

Example ctrl_n11a (x : D) :
  transform[@fun_comp_assoc D C C' D' U' K F] x
    = fmap[U'] (@id C' (fobj[K] (fobj[F] x)))
  := @fun_comp_assoc_component C D F C' D' U' K x.

Example ctrl_n11b (x : D) :
  transform[@fun_comp_assoc D C C' D' U' K F] x
    ≈ @id D' (fobj[U'] (fobj[K] (fobj[F] x)))
  := @fun_comp_assoc_is_id C D F C' D' U' K x.

Fail Example n11 (x : D) :
  @eq (fobj[U'] (fobj[K] (fobj[F] x)) ~{D'}~> fobj[U'] (fobj[K] (fobj[F] x)))
      (transform[@fun_comp_assoc D C C' D' U' K F] x)
      (@id D' (fobj[U'] (fobj[K] (fobj[F] x)))) := eq_refl.

(* -- N12.  CONTROL: the Cat bridge holds at [≈].                       -- *)

Example ctrl_n12 (sg : F' ◯ L ⟹ K ◯ F) :
  @SqMate C D F U A C' D' F' U' A' K L sg
    ≈ mate (@SqBA C D F U A) (@SqBA' C' D' F' U' A') sg
  := @sq_mate_is_mate C D F U A C' D' F' U' A' K L sg.

Fail Example n12 (sg : F' ◯ L ⟹ K ◯ F) (a : C) :
  @eq (fobj[L] (fobj[U] a) ~{D'}~> fobj[U'] (fobj[K] a))
      (@SqMate C D F U A C' D' F' U' A' K L sg a)
      (mate (@SqBA C D F U A) (@SqBA' C' D' F' U' A') sg a) := eq_refl.

(* -- N20 (round trip).  CONTROL: the round trip holds at [≈] under     -- *)
(* -- [SigmaNat]; the strict form is refuted at an arbitrary family.    -- *)

Example ctrl_n20 (sigma : SqSigma K L) (Hs : SigmaNat K L sigma) (x : D) :
  @sq_mate_inv C D F U A C' D' F' U' A' K L
    (@sq_mate C D F U A C' D' F' U' A' K L sigma) x ≈ sigma x
  := @sq_mate_inv_mate C D F U A C' D' F' U' A' K L sigma Hs x.

Fail Example n20 (sigma : SqSigma K L) (x : D) :
  @eq (fobj[F'] (fobj[L] x) ~{C'}~> fobj[K] (fobj[F] x))
      (@sq_mate_inv C D F U A C' D' F' U' A' K L
         (@sq_mate C D F U A C' D' F' U' A' K L sigma) x)
      (sigma x) := eq_refl.

(* -- N13 (TYPING).  CONTROL: with an ISOMORPHISM family the same       -- *)
(* -- statement is [MapAdjHom] on the nose.                             -- *)

Example ctrl_n13
  (al : ∀ x : D, fobj[K] (fobj[F] x) ≅ fobj[F'] (fobj[L] x))
  (be : ∀ a : C, fobj[L] (fobj[U] a) ≅ fobj[U'] (fobj[K] a)) :
  @AdjointSquare C D F U A C' D' F' U' A' K L
      (fun x => from (al x)) (fun a => to (be a))
    = @MapAdjHom C D F U A C' D' F' U' A' K L al be
  := @square_is_map_adj_hom C D F U A C' D' F' U' A' K L al be.

Context (sigma : SqSigma K L) (tau : SqTau K L).

Fail Check (@MapAdjHom C D F U A C' D' F' U' A' K L
              (fun x => sigma x) (fun a => tau a)).

(* -- N21 (TYPING).  CONTROL: [SqMate] accepts a sigma-shaped Transform. -- *)

Example ctrl_n21 (sg : F' ◯ L ⟹ K ◯ F) : L ◯ U ⟹ U' ◯ K
  := @SqMate C D F U A C' D' F' U' A' K L sg.

Fail Check (fun ta : L ◯ U ⟹ U' ◯ K =>
              @SqMate C D F U A C' D' F' U' A' K L ta).

End P398Main.

(* ====================================================================== *)
(* (2) N7-N10: the Id-padding negatives, K = L = Id, against the          *)
(*     identity-bounding-functor development Adjunction/Conjugate.v.      *)
(* ====================================================================== *)

Section P398Id.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {F2 : D ⟶ C} {U2 : C ⟶ D} (A2 : F2 ⊣ U2).

(* CONTROL: at COMPONENT level the identification with Conjugate is    *)
(* [eq_refl] in all three of the shapes the negatives then refute at   *)
(* the level of types and of records.                                 *)

Example ctrl_id_a (s : F2 ⟹ F) (t : U ⟹ U2) :
  @AdjointSquare C D F U A C D F2 U2 A2 Id[C] Id[D]
      (transform[s]) (transform[t])
    = @Conjugate C D F U F2 U2 A A2 s t
  := @square_is_conjugate C D F U F2 U2 A A2 s t.

Example ctrl_id_b (s : F2 ⟹ F) (a : C) :
  @sq_mate C D F U A C D F2 U2 A2 Id[C] Id[D] (transform[s]) a
    = @conj_mate C D F U F2 U2 A A2 s a
  := @sq_mate_is_conj_mate C D F U F2 U2 A A2 s a.

Example ctrl_id_c (t : U ⟹ U2) (x : D) :
  @sq_mate_inv C D F U A C D F2 U2 A2 Id[C] Id[D] (transform[t]) x
    = @conj_mate_inv C D F U F2 U2 A A2 t x
  := @sq_mate_inv_is_conj_mate_inv C D F U F2 U2 A A2 t x.

Example ctrl_id_d :
  @eq Type (carrier (@conj_dom C D F F2)) (@Transform D C F2 F) := eq_refl.

Example ctrl_id_e :
  @eq Type (carrier (@sq_dom C D F C D F2 Id[C] Id[D]))
           (@Transform D C (F2 ◯ Id[D]) (Id[C] ◯ F)) := eq_refl.

Fail Example n7 :
  @eq Type (@Transform D C (F2 ◯ Id[D]) (Id[C] ◯ F))
           (@Transform D C F2 F) := eq_refl.

Fail Example n8 : @eq (D ⟶ C) (F2 ◯ Id[D]) F2 := eq_refl.

Fail Example n9 :
  @eq SetoidObject (@sq_dom C D F C D F2 Id[C] Id[D]) (@conj_dom C D F F2)
  := eq_refl.

Fail Example n10 :
  @eq (@Isomorphism Sets (@sq_dom C D F C D F2 Id[C] Id[D])
                         (@sq_cod C D U C D U2 Id[C] Id[D]))
      (@square_bijection C D F U A C D F2 U2 A2 Id[C] Id[D])
      (@conjugate_bijection C D F U F2 U2 A A2) := eq_refl.

End P398Id.

(* ====================================================================== *)
(* (3) N3: the composite adjunction's unit.                               *)
(* ====================================================================== *)

Section P398Vert.

Context {D C E : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {G : C ⟶ E} {V : E ⟶ C} (B : G ⊣ V).

(* CONTROL: the composite's TRANSPOSE is definitional, and its unit     *)
(* agrees with the whiskered formula up to [≈].                         *)

Example ctrl_n3a (x : D) (e : E) (k : fobj[G] (fobj[F] x) ~{E}~> e) :
  to (@adj E D (G ◯ F) (U ◯ V) (@AB D C E F U A G V B) x e) k
    = to (@adj C D F U A x (fobj[V] e))
        (to (@adj E C G V B (fobj[F] x) e) k)
  := @AB_to_strict D C E F U A G V B x e k.

Example ctrl_n3b (x : D) :
  @Category.Theory.Adjunction.unit E D (G ◯ F) (U ◯ V)
      (@AB D C E F U A G V B) x
    ≈ fmap[U] (@Category.Theory.Adjunction.unit E C G V B (fobj[F] x))
        ∘ @Category.Theory.Adjunction.unit C D F U A x
  := @AB_unit_upto D C E F U A G V B x.

Fail Example n3 (x : D) :
  @eq (x ~{D}~> fobj[U ◯ V] (fobj[G ◯ F] x))
      (@Category.Theory.Adjunction.unit E D (G ◯ F) (U ◯ V)
         (@AB D C E F U A G V B) x)
      (fmap[U] (@Category.Theory.Adjunction.unit E C G V B (fobj[F] x))
         ∘ @Category.Theory.Adjunction.unit C D F U A x) := eq_refl.

End P398Vert.

(* ====================================================================== *)
(* (4) N14 (FORMABILITY): [Adjunction] is the hom = proof donor.          *)
(* ====================================================================== *)

Section P398UnivAdj.

Universes co ch cp.
Constraint ch < cp.

Context (Cu Du : Category@{co ch cp}).

(* CONTROLS, all accepted at these very levels. *)

Check (Cu ⟶ Du).
Check (Du ⟶ Cu).
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => @id Cu x).
Check (fun Fq Gq : Cu ⟶ Du => Fq ⟹ Gq).

Check (fun Fq : Du ⟶ Cu => Fq ⟹ Fq).
Check (fun Uq : Cu ⟶ Du => Uq ⟹ Uq).

Fail Check (fun (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du) => Fq ⊣ Uq).

(* -- N24 (FORMABILITY).  [Compose] is a SECOND donor of hom = proof,  -- *)
(* -- independent of [Adjunction] and refused here with no adjunction  -- *)
(* -- anywhere in the command: Adjunction/Square.v's header attributes -- *)
(* -- the identification to [Adjunction] alone, which is true of the   -- *)
(* -- five controls it lists and is not discriminating.                -- *)

Fail Check (fun (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du) => Uq ◯ Fq).

End P398UnivAdj.

(* ====================================================================== *)
(* (5) N15 (FORMABILITY): functors in BOTH directions identify the two    *)
(*     hom levels, before any adjunction is formed.                       *)
(* ====================================================================== *)

Section P398UnivFun.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Aq : Category@{ao ah ah}).
Context (Bq : Category@{bo bh bh}).

Check (Aq ⟶ Bq).
Check (fun x y : Aq => x ~{Aq}~> y).
Check (fun x y : Bq => x ~{Bq}~> y).

Fail Check (Bq ⟶ Aq).

End P398UnivFun.

(* ====================================================================== *)
(* (6) N16-N19, N22, N23 (FORMABILITY): [Compose] is the donor of the     *)
(*     EXTRA collapse that every Transform-typed constant of              *)
(*     Adjunction/Square.v carries.  The whole bare-family engine is      *)
(*     formable at levels declared strictly apart; the four composites    *)
(*     and the two Transform-typed wrappers are not.                      *)
(* ====================================================================== *)

Section P398UnivComp.

Universes co cho c2o ch2.
Constraint cho < ch2.

Context (Cu Du : Category@{co cho cho}).
Context (C2u D2u : Category@{c2o ch2 ch2}).
Context (Fu : Du ⟶ Cu) (Uu : Cu ⟶ Du) (Au : Fu ⊣ Uu).
Context (F2u : D2u ⟶ C2u) (U2u : C2u ⟶ D2u) (A2u : F2u ⊣ U2u).
Context (Ku : Cu ⟶ C2u) (Lu : Du ⟶ D2u).
Context (sg : SqSigma Ku Lu) (ta : SqTau Ku Lu).

(* CONTROLS: the two component families, the condition, both mate      *)
(* operators, the characterisation and the two unit/counit forms are   *)
(* ALL accepted with the two hom levels declared strictly apart.       *)

Check (∀ x : Du, fobj[F2u] (fobj[Lu] x) ~{C2u}~> fobj[Ku] (fobj[Fu] x)).
Check (∀ a : Cu, fobj[Lu] (fobj[Uu] a) ~{D2u}~> fobj[U2u] (fobj[Ku] a)).
Check (@SqSigma Cu Du Fu C2u D2u F2u Ku Lu).
Check (@SqTau Cu Du Uu C2u D2u U2u Ku Lu).
Check (@AdjointSquare Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg ta).
Check (@AdjointSquareUnit Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg ta).
Check (@AdjointSquareCounit Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg ta).
Check (@sq_mate Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg).
Check (@sq_mate_inv Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu ta).
Check (@adjoint_square_iff_mate Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg ta).

Fail Check (F2u ◯ Lu).
Fail Check (Ku ◯ Fu).
Fail Check (Lu ◯ Uu).
Fail Check (U2u ◯ Ku).
Fail Check (@AdjointSquareT Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu).
Fail Check (@square_bijection Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu).

End P398UnivComp.
