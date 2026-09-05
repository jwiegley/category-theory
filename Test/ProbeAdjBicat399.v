Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Square.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Adj.Bicategory.

Generalizable All Variables.

(** * Probe for Instance/Adj/Bicategory.v *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.8,
   book p. 104 (PDF p. 113): Theorem 2, display (1), Exercise 1 and the
   closing remark; catalog ids maclane:IV.8:thm2, maclane:IV.8:ex1,
   maclane:IV.8:remark1.  Those passages are quoted verbatim in the header
   of Instance/Adj/Bicategory.v and are not repeated here.

   This file guards the strict claims of that header.  Every statement
   below that is asserted to be refuted has been STRIPPED into its own
   scratch copy carrying this file's whole prefix, compiled ALONE, and its
   complete error read; under this repo's coqc a passing [Fail] prints
   nothing, so a whole-file rc=0 alone would establish only THAT each
   command does not typecheck and never WHY.  Each negative is classified
   by the error TEXT, not by expectation:

     CONVERSION  - the message carries a "cannot unify A and B" clause and
                   no universe clause.
     TYPING      - a plain "The term T has type X while it is expected to
                   have type Y"; NO "cannot unify", no universe clause.
     FORMABILITY - "(universe inconsistency: Cannot enforce ...)", naming
                   the levels the enclosing section declares.

   ** TALLY

   27 [Fail] commands = 1 instrument check + 26 negatives, in three kinds:
   ELEVEN conversion (N4-N11, N13-N15), FOUR typing (N1-N3, N12) and ELEVEN
   formability (N16-N26).

   ** ONE KIND DIVERGES FROM THE BRIEF'S EXPECTATION

   N15 -- feeding [Build_Bicategory'] the arguments [Adj_Bicategory] feeds
   to the raw [Build_Bicategory] -- was expected to be a plain typing
   mismatch; the Core report (§M6g) assigns it no kind and quotes the
   message in a form that stops after the expected type.  Stripped and read
   WHOLE here it carries a trailing "(cannot unify ...)" clause past where
   that quotation ends, so it is CONVERSION, not TYPING.  Two scope notes.
   What cannot unify are two TYPES -- a functor type against the
   eta-expanded record spelling of the same two categories -- rather than
   two inhabitants of one type, so it sits at the boundary of the two
   kinds; and [Build_Bicategory'] takes TWENTY arguments where
   [Build_Bicategory] takes twenty-one, since it derives [comp_assoc_sym]
   by [symmetry], so the negative passes the twenty-one minus that one.
   Deriving it is exactly what breaks record eta and is what the negative
   exhibits.

   ** ONE NEGATIVE MEASURES ITS ARGUMENT AND NOT ITS SUBJECT

   N19 names [ConjPair], and the character offsets in its error put the
   refusal on the [Cu] of its [AdjObj Cu Du] binder, not on [ConjPair].
   [ConjPair]'s two object arguments are [AdjObj]s, so it CANNOT be tested
   apart from [AdjObj], which in turn contains an [Adjunction] and cannot
   be tested apart from that: whether [ConjPair] identifies anything of its
   own is UNKNOWN, not refuted.  This is the trap recorded for
   [MonoidObject] under issue #340, and it is stated here rather than
   glossed.  N17 and N18 are in the same position with respect to
   [Adjunction].

   ** THE VERBATIM ERROR TAILS

   (The tails transcribe the unicode of the real messages as ASCII -- [o]
   for the composition circle, [-|] for the adjunction sign, [==>] for the
   transformation arrow, [(X)] for the product of categories and [-->] for
   the functor arrow -- so that this comment stays free of the glyphs the
   sources use; the shape of every message is otherwise character for
   character what coqc printed.)

   N1  TYPING
     The term "Adjunction_Compose Aa (Adjunction_Compose Bb Cc)" has type
     "H o G o F -| U o (V o W)"
     while it is expected to have type "H o (G o F) -| U o V o W".
   N2  TYPING
     The term "Adjunction_Compose Aa Adjunction_Id" has type
     "Id[C] o F -| U o Id[C]"
     while it is expected to have type "F -| U".
   N3  TYPING
     The term "Adjunction_Compose Adjunction_Id Aa" has type
     "F o Id[D] -| Id[D] o U"
     while it is expected to have type "F -| U".
   N4  CONVERSION
     The term "eq_refl" has type "H o G o F = H o G o F"
     while it is expected to have type "H o G o F = H o (G o F)"
     (cannot unify "H o G o F" and "H o (G o F)").
   N5  CONVERSION
     (cannot unify "Id[C] o F" and "F").
   N6  CONVERSION
     (cannot unify "F o Id[D]" and "F").
   N7  CONVERSION
     (cannot unify "adjobj_hcompose (AdjIdObj y) a" and "a").
   N8  CONVERSION
     (cannot unify "adjobj_hcompose a (AdjIdObj x)" and "a").
   N9  CONVERSION
     (cannot unify "adjobj_hcompose (adjobj_hcompose c b) a" and
      "adjobj_hcompose c (adjobj_hcompose b a)").
   N10 CONVERSION
     (cannot unify "adjobj_left (adjobj_hcompose (AdjIdObj y) a)" and
      "adjobj_left a").
   N11 CONVERSION
     (cannot unify
      "paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e" and
      "nat_hcompose t tb e").
   N12 TYPING
     The term "paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb)"
     has type "G' o F' o Id[D] ==> Id[E] o (G o F)"
     while it is expected to have type "G' o F' ==> G o F".
   N13 CONVERSION
     The term "eq_refl" has type
     "adjunction (mA o mB) = adjunction (mA o mB)"
     while it is expected to have type
     "adjunction (mA o mB) =
      Adjunction_Compose (adjunction mA) (adjunction mB)"
     (cannot unify "adjunction (mA o mB)" and
      "Adjunction_Compose (adjunction mA) (adjunction mB)").
   N14 CONVERSION
     (cannot unify "adjobj_of_morphism (morphism_of_adjobj xo)" and "xo").
   N15 CONVERSION
     The term "@Adj_Hcompose" has type
     "forall x y z : Category, (Adj y z (X) Adj x y) --> Adj x z"
     while it is expected to have type
     "forall x y z : Category, ({| obj := obj[Adj y z]; ...;
      comp_assoc_sym := fun ... => symmetry (comp_assoc f g h) |}
      (X) {| ... |}) --> {| ... |}"
     (cannot unify "(Adj y z (X) Adj x y) --> Adj x z" and
      "({| ... |} (X) {| ... |}) --> {| ... |}").
     [the two record displays are the ten [Adj] projections plus the
      [symmetry]-derived [comp_assoc_sym], written out in full]
   N16 FORMABILITY
     The term "Fq" has type "@Functor@{co ch cp co ch cp} Du Cu"
     while it is expected to have type "@Functor@{...} ?D ?C"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N17 FORMABILITY
     The term "Cu" has type "Category@{co ch cp}"
     while it is expected to have type "Category@{... h h}"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N18 FORMABILITY  [same shape as N17, refusing at [Cu]]
   N19 FORMABILITY  [same shape as N17, refusing at the [Cu] of [AdjObj]]
   N20 FORMABILITY
     The term "Gq" has type "@Functor@{co ch cp co ch cp} Du Eu"
     while it is expected to have type "@Functor@{...} ?D ?E"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N21 FORMABILITY
     The term "aa" has type "@Transform@{co ch cp co ch cp} Du Eu J1 K1"
     while it is expected to have type "@Transform@{...} ?D ?E ?J ?K"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N22 FORMABILITY  [same shape as N17, refusing at [Cu]]
   N23 FORMABILITY  [same shape as N17, refusing at [Cu]]
   N24 FORMABILITY  [same shape as N17, refusing at [Cu]]
   N25 FORMABILITY
     The term "Aq" has type "Category@{ao ah ah}"
     while it is expected to have type "Category@{...}"
     (universe inconsistency: Cannot enforce ah = ... because ah < bh
      <= ...).
   N26 FORMABILITY
     The term "Bq" has type "Category@{bo bh bh}"
     while it is expected to have type "Category@{... ah ah}"
     (universe inconsistency: Cannot enforce bh = ah because ah < bh).

   ** WHAT EACH NEGATIVE PAIRS WITH

   Every negative sits beside a positive control that DOES hold, so that
   each guard measures a boundary rather than an absence.

   N1-N3 pair with two [Check]s each, of the very composites the equations
   would relate, so the refusal is of the EQUATION and not of either side.
   N4-N6 pair with [c399_n4a], [c399_n4b], [c399_n56a] and [c399_n56b]:
   [fobj] and [fmap] agree at [eq_refl] on the two bracketings, and [fobj]
   agrees on both unit paddings, so none of the three refusals is in
   [fobj].  That they are in [Compose]'s three LAW fields is the fact
   Adjunction/Pare.v and Instance/Cat/Bicategory.v already record -- it
   turns on [Functor] having primitive projections with eta and is NOT
   measured here.  N7-N10 pair with [c399_n7] to [c399_n10], the target's
   own four [eq_refl] readbacks ([hunit_left_obj_left] and its three
   siblings), which say exactly what the padded 1-cell's two adjoints ARE.
   N11 pairs with [c399_n11], the target's [routeb_tau], the same statement
   at [~=]; N12 pairs with [c399_n12], the target's [routeb_sigma], the
   same statement one level down at a COMPONENT and at [eq_refl] -- so the
   two together say that the sigma leg is the Godement product
   componentwise and the tau leg is not.  N13 pairs with two [Check]s, and
   its own error fires at [eq_refl] rather than at an argument, so both
   sides do elaborate at one and the same type; and with [c399_n13a],
   Adjunction/Compose.v's own [Adjunction_Compose_adj_comp_to], the
   positive half already in tree: the two constructions have definitionally
   equal transposes.  N14 pairs with [c399_n14], the target's
   [adjoints_round_record], the RECORD round trip at [eq_refl]; that what
   separates the two is stdlib [sigT]'s missing eta is the target header's
   attribution and is not measured here.  N15 pairs with
   [Check @Adj_Bicategory], the raw-constructor build that does typecheck.
   N16-N24 pair with five commands accepted at the very levels that refuse
   them -- a hom-set, an identity, a functor in each direction and a
   [Transform] between two functors.  N20 refutes [Compose] ALONE, with no
   adjunction and no transformation anywhere in the command, and that
   [Transform] control is accepted; so N21's refusal is ATTRIBUTED to the
   [Compose] in [nat_hcompose]'s result type, an attribution and not an
   isolation, since no [Compose]-free variant of it was compiled.  N25 and
   N26 pair with four commands accepted with the two hom levels declared
   strictly apart, so what N26 attributes to [AdjObj] is the presence of
   functors in BOTH directions and not the adjunction condition.

   ** RENAME SIMULATION

   FIFTEEN constants OF THE TARGET MODULE are named inside a negative:
   [AdjIdObj], [adjobj_hcompose], [conj_padL], [conj_padR],
   [adjobj_of_morphism], [morphism_of_adjobj], [Adj_Hcompose],
   [Adj_hunit_left], [Adj_hunit_right], [Adj_hassoc],
   [Adj_hunit_left_natural], [Adj_hunit_right_natural],
   [Adj_hassoc_natural], [Adj_triangle] and [Adj_pentagon].  (The other
   identifiers a negative names belong to donor modules, not to the target,
   and are guarded by [Check] all the same.)  Each was renamed ONE AT A
   TIME in a SCRATCH COPY of Instance/Adj/Bicategory.v -- never in place --
   compiled under [-Q ... Scratch]; a copy of this file requiring that
   scratch module instead of the library one was then compiled.  ALL
   FIFTEEN broke it, every one at a [Check] line of the guard block and
   NONE inside a [Fail]:

     AdjIdObj                  line 356   Check @AdjIdObj.
     adjobj_hcompose           line 357   Check @adjobj_hcompose.
     conj_padL                 line 349   Check @conj_padL.
     conj_padR                 line 350   Check @conj_padR.
     adjobj_of_morphism        line 382   Check @adjobj_of_morphism.
     morphism_of_adjobj        line 383   Check @morphism_of_adjobj.
     Adj_Hcompose              line 359   Check @Adj_Hcompose.
     Adj_hunit_left            line 367   Check @Adj_hunit_left.
     Adj_hunit_right           line 368   Check @Adj_hunit_right.
     Adj_hassoc                line 369   Check @Adj_hassoc.
     Adj_hunit_left_natural    line 375   Check @Adj_hunit_left_natural.
     Adj_hunit_right_natural   line 376   Check @Adj_hunit_right_natural.
     Adj_hassoc_natural        line 377   Check @Adj_hassoc_natural.
     Adj_triangle              line 378   Check @Adj_triangle.
     Adj_pentagon              line 379   Check @Adj_pentagon.

   So 15/15, with zero vacuous guards.  (Renaming a [Program Definition]
   must also rename its obligations, whose names are that constant's name
   with [_obligation_n] appended; a whole-file substitution does so.)

   ** GUARD COVERAGE, measured mechanically

   Comments stripped, the file split into commands at a period followed by
   whitespace: 183 commands, of which 27 begin with [Fail]; they mention
   118 distinct identifiers, of which 93 also occur in a command that is
   NOT a [Fail].  The twenty-five that do not are, exhaustively: the two
   keywords [Fail] and [Definition]; the seven variables bound inside the
   negatives themselves ([F1], [G1], [J1], [K1], [Uq], [aa] and [bb]); the
   fifteen names of the refuted declarations ([n1]-[n15]), which never
   enter the environment because the commands that would have declared them
   do not typecheck; and [p399_no_such_constant_anywhere], the instrument's
   deliberately absent name.  No CONSTANT that a negative names is
   unguarded.

   ** make todo

   The repo's [todo] target greps every [.v] file, case-insensitively and
   with no word boundary, for its five alternatives: [Fail], abort,
   undefined, jww and, between them, the hole-closing tactic name, which
   this comment does not spell because the aborted-sketch gate would count
   it.  This file contributes 41 such lines: the 27 [Fail] commands and 14
   lines of the prose above.  Instance/Adj/Bicategory.v contributes ZERO,
   which is the reason every refutation lives here rather than there.

   ** WHAT THIS FILE DOES NOT DO

   It proves nothing new.  It contains no proof hole of any kind, no
   hole-closing tactic, no [Axiom], no [Parameter] and no [Abort]; every
   positive control is a term, never a tactic script, so nothing here can
   drift by a change in the automation.  It does not measure universes
   beyond the two donor sections, does not count constants, does not
   compare the two Theorem-2 proof terms, and takes no position on the
   target header's prose. *)

(* ---------------------------------------------------------------------- *)
(* INSTRUMENT.  A passing [Fail] prints nothing under this repo's coqc, so *)
(* this command establishes that [Fail] is doing anything at all.          *)
(* ---------------------------------------------------------------------- *)

Fail Check p399_no_such_constant_anywhere.

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
Check @Bicategory.
Check @eq.
Check @obj.
Check @hom.
Check @homset.
Check @id.
Check @compose.
Check @compose_respects.
Check @id_left.
Check @id_right.
Check @comp_assoc.
Check @comp_assoc_sym.
Check @fobj.
Check @fmap.
Check @transform.
Check @nat_hcompose.

Check @Adjunction_Compose.
Check @Adjunction_Id.
Check @Adjunction_Compose_adj_comp_to.
Check @Adjunction_Compose_adj_comp_from.
Check @paste_v_sigma.
Check @paste_v_tau.
Check @Adjoints.
Check @adjunction.
Check @free_functor.
Check @forgetful_functor.
Check @Cat_Hcompose.
Check @Build_Bicategory.
Check @Build_Bicategory'.

Check @AdjObj.
Check @ConjPair.
Check @Adj.
Check @adjobj_left.
Check @adjobj_right.
Check @adjobj_adj.

Check @conjugate_hcompose.
Check @conj_padL.
Check @conj_padR.
Check @routeb_hyp.
Check @routeb_sigma.
Check @routeb_tau.
Check @conjugate_hcompose_via_square.
Check @nat_hcompose_interchange.
Check @AdjIdObj.
Check @adjobj_hcompose.
Check @conj_pair_hcompose.
Check @Adj_Hcompose.
Check @Adj_Hcompose_shape.
Check @hcomp_obj_adj.
Check @hcomp_obj_left.
Check @hcomp_obj_right.
Check @hcomp_left_is_nat_hcompose.
Check @hcomp_right_is_nat_hcompose.
Check @conj_interchange.
Check @Adj_hunit_left.
Check @Adj_hunit_right.
Check @Adj_hassoc.
Check @hunit_left_obj_left.
Check @hunit_left_obj_right.
Check @hunit_right_obj_left.
Check @hunit_right_obj_right.
Check @adj_hcomp2.
Check @Adj_hunit_left_natural.
Check @Adj_hunit_right_natural.
Check @Adj_hassoc_natural.
Check @Adj_triangle.
Check @Adj_pentagon.
Check @Adj_Bicategory.
Check @Adj_bicat_is_Adj.
Check @adjobj_of_morphism.
Check @morphism_of_adjobj.
Check @adjoints_round_record.

(* ====================================================================== *)
(* (1) N1-N6.  The 1-cell layer of [Adj] is WEAK: neither associativity   *)
(*     nor either unit law of [Adjunction_Compose] is even statable, and  *)
(*     one level down the functor equations are statable and refused at   *)
(*     conversion.                                                        *)
(* ====================================================================== *)

Section P399Assoc.

Context {D C E Z : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (Aa : F ⊣ U).
Context {G : C ⟶ E} {V : E ⟶ C} (Bb : G ⊣ V).
Context {H : E ⟶ Z} {W : Z ⟶ E} (Cc : H ⊣ W).

(* -- N1 (TYPING).  CONTROLS: both bracketings elaborate; what is        -- *)
(* -- refused is the EQUATION, whose two sides do not share a type.      -- *)

Check (@Adjunction_Compose E D Z (G ◯ F) (U ◯ V) H W
         (@Adjunction_Compose C D E F U G V Aa Bb) Cc).
Check (@Adjunction_Compose C D Z F U (H ◯ G) (V ◯ W) Aa
         (@Adjunction_Compose E C Z G V H W Bb Cc)).

Fail Example n1 :
  @eq (@Adjunction Z D (H ◯ (G ◯ F)) (U ◯ V ◯ W))
      (@Adjunction_Compose E D Z (G ◯ F) (U ◯ V) H W
         (@Adjunction_Compose C D E F U G V Aa Bb) Cc)
      (@Adjunction_Compose C D Z F U (H ◯ G) (V ◯ W) Aa
         (@Adjunction_Compose E C Z G V H W Bb Cc)) := eq_refl.

(* -- N2/N3 (TYPING).  CONTROLS: both padded composites elaborate.       -- *)

Check (@Adjunction_Compose C D C F U Id[C] Id[C] Aa (@Adjunction_Id C)).
Check (@Adjunction_Compose D D C Id[D] Id[D] F U (@Adjunction_Id D) Aa).

Fail Example n2 :
  @eq (@Adjunction C D F U) Aa
      (@Adjunction_Compose C D C F U Id[C] Id[C] Aa (@Adjunction_Id C))
  := eq_refl.

Fail Example n3 :
  @eq (@Adjunction C D F U) Aa
      (@Adjunction_Compose D D C Id[D] Id[D] F U (@Adjunction_Id D) Aa)
  := eq_refl.

(* -- N4-N6 (CONVERSION).  CONTROLS: [fobj] and [fmap] agree on the      -- *)
(* -- nose on both sides, so what the three negatives locate is the      -- *)
(* -- three LAW fields of [Compose] and neither data field.              -- *)

Example c399_n4a (o : D) :
  @eq (obj[Z]) (fobj[H ◯ G ◯ F] o) (fobj[H ◯ (G ◯ F)] o) := eq_refl.

Example c399_n4b (o1 o2 : D) (f : o1 ~> o2) :
  @eq (fobj[H ◯ G ◯ F] o1 ~{Z}~> fobj[H ◯ G ◯ F] o2)
      (fmap[H ◯ G ◯ F] f) (fmap[H ◯ (G ◯ F)] f) := eq_refl.

Fail Example n4 : @eq (D ⟶ Z) (H ◯ G ◯ F) (H ◯ (G ◯ F)) := eq_refl.

Example c399_n56a (o : D) :
  @eq (obj[C]) (fobj[Id[C] ◯ F] o) (fobj[F] o) := eq_refl.

Example c399_n56b (o : D) :
  @eq (obj[C]) (fobj[F ◯ Id[D]] o) (fobj[F] o) := eq_refl.

Fail Example n5 : @eq (D ⟶ C) (Id[C] ◯ F) F := eq_refl.

Fail Example n6 : @eq (D ⟶ C) (F ◯ Id[D]) F := eq_refl.

End P399Assoc.

(* ====================================================================== *)
(* (2) N7-N10.  The same three laws one level up, at [AdjObj]: both unit  *)
(*     laws, associativity, and the left-adjoint component of the first.  *)
(* ====================================================================== *)

Section P399AdjObj.

Context {x y z w : Category}.
Context (a : AdjObj x y) (b : AdjObj y z) (c : AdjObj z w).

(* -- CONTROLS: the target's own four [eq_refl] readbacks, which say     -- *)
(* -- what the padded 1-cell's two adjoints ARE.                         -- *)

Example c399_n7 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose (AdjIdObj y) a))
              (adjobj_left a ◯ Id[y])
  := @hunit_left_obj_left x y a.

Example c399_n8 :
  @eq (x ⟶ y) (adjobj_right (adjobj_hcompose (AdjIdObj y) a))
              (Id[y] ◯ adjobj_right a)
  := @hunit_left_obj_right x y a.

Example c399_n9 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose a (AdjIdObj x)))
              (Id[x] ◯ adjobj_left a)
  := @hunit_right_obj_left x y a.

Example c399_n10 :
  @eq (x ⟶ y) (adjobj_right (adjobj_hcompose a (AdjIdObj x)))
              (adjobj_right a ◯ Id[x])
  := @hunit_right_obj_right x y a.

Fail Example n7 :
  @eq (AdjObj x y) (adjobj_hcompose (AdjIdObj y) a) a := eq_refl.

Fail Example n8 :
  @eq (AdjObj x y) (adjobj_hcompose a (AdjIdObj x)) a := eq_refl.

Fail Example n9 :
  @eq (AdjObj x w) (adjobj_hcompose (adjobj_hcompose c b) a)
                   (adjobj_hcompose c (adjobj_hcompose b a)) := eq_refl.

Fail Example n10 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose (AdjIdObj y) a))
              (adjobj_left a) := eq_refl.

End P399AdjObj.

(* ====================================================================== *)
(* (3) N11, N12.  Route (b): the sigma leg of Adjunction/Square.v's       *)
(*     vertical paste IS the Godement product componentwise; the tau leg  *)
(*     is not, and as a WHOLE transformation neither leg has the type     *)
(*     [nat_hcompose] has.                                                *)
(* ====================================================================== *)

Section P399RouteB.

Context {C D E : Category}.
Context {F F' : D ⟶ C} {U U' : C ⟶ D}.
Context {G G' : C ⟶ E} {V V' : E ⟶ C}.

(* -- CONTROL for N11: the target's [routeb_tau], the same statement     -- *)
(* -- at [~=], one application of [naturality].                          -- *)

Example c399_n11 (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e
    ≈ nat_hcompose t tb e
  := @routeb_tau C D E U U' V V' t tb e.

(* -- CONTROL for N12: the target's [routeb_sigma], the sigma leg at a   -- *)
(* -- COMPONENT and at [eq_refl].                                        -- *)

Example c399_n12 (s : F' ⟹ F) (sb : G' ⟹ G) (o : D) :
  paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb) o
    = nat_hcompose sb s o
  := @routeb_sigma C D E F F' G G' s sb o.

Fail Example n11 (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  @eq (fobj[U] (fobj[V] e) ~{D}~> fobj[U'] (fobj[V'] e))
      (paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e)
      (nat_hcompose t tb e) := eq_refl.

Fail Example n12 (s : F' ⟹ F) (sb : G' ⟹ G) :
  @eq (@Transform D E (G' ◯ F') (G ◯ F))
      (paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb))
      (nat_hcompose sb s) := eq_refl.

End P399RouteB.

(* ====================================================================== *)
(* (4) N13, N14.  The bridge to Instance/Adjoints.v: that category        *)
(*     composes by [adj_comp], whose composite is NOT [Adjunction_Compose] *)
(*     at conversion though the two share a type; and the sigT round trip *)
(*     does not close where the record one does.                          *)
(* ====================================================================== *)

Section P399Adjoints.

Context {A1 B1 C1 : Category}.
Context (mA : B1 ~{Adjoints}~> C1) (mB : A1 ~{Adjoints}~> B1).
Context (xo : AdjObj A1 B1).

(* -- CONTROLS for N13: both sides elaborate, at one and the same type.  -- *)

Check (adjunction (mA ∘ mB)).
Check (@Adjunction_Compose B1 C1 A1
         (free_functor mA) (forgetful_functor mA)
         (free_functor mB) (forgetful_functor mB)
         (adjunction mA) (adjunction mB)).

(* -- CONTROL for N13, the positive half already in tree: the two        -- *)
(* -- constructions have definitionally equal transposes.                -- *)

Example c399_n13a (o : C1) (p : A1)
  (f : fobj[free_functor mB] (fobj[free_functor mA] o) ~{A1}~> p) :
  to (@adj _ _ _ _ (@Adjunction_Compose B1 C1 A1
        (free_functor mA) (forgetful_functor mA)
        (free_functor mB) (forgetful_functor mB)
        (adjunction mA) (adjunction mB)) o p) f
    ≈ to (@adj _ _ _ _ (adj_comp (free_functor mB) (forgetful_functor mB)
            (free_functor mA) (forgetful_functor mA)
            (adjunction mB) (adjunction mA)) o p) f
  := @Adjunction_Compose_adj_comp_to B1 C1 A1
       (free_functor mA) (forgetful_functor mA)
       (free_functor mB) (forgetful_functor mB)
       (adjunction mA) (adjunction mB) o p f.

(* -- CONTROL for N14: the RECORD round trip closes at [eq_refl].        -- *)

Example c399_n14 : morphism_of_adjobj (adjobj_of_morphism mA) = mA
  := @adjoints_round_record B1 C1 mA.

Fail Example n13 :
  @eq (@Adjunction A1 C1 (free_functor mB ◯ free_functor mA)
                   (forgetful_functor mA ◯ forgetful_functor mB))
      (adjunction (mA ∘ mB))
      (@Adjunction_Compose B1 C1 A1
         (free_functor mA) (forgetful_functor mA)
         (free_functor mB) (forgetful_functor mB)
         (adjunction mA) (adjunction mB)) := eq_refl.

Fail Example n14 :
  @eq (AdjObj A1 B1) (adjobj_of_morphism (morphism_of_adjobj xo)) xo
  := eq_refl.

End P399Adjoints.

(* ====================================================================== *)
(* (5) N15.  [Build_Bicategory'] churns: its [symmetry]-derived           *)
(*     [comp_assoc_sym] breaks record eta, [bicat x y] is then no longer  *)
(*     [Adj x y], and [Adj_Hcompose] no longer typechecks against         *)
(*     [hcompose].  The twenty arguments below are the twenty-one         *)
(*     [Adj_Bicategory] passes to the raw constructor, less the           *)
(*     [comp_assoc_sym] that this one derives.                            *)
(* ====================================================================== *)

(* -- CONTROL: the raw-constructor build, which does typecheck.          -- *)

Check @Adj_Bicategory.

Fail Definition n15 : Bicategory :=
  Build_Bicategory'
    Category
    (fun C D => @obj (Adj C D))
    (fun C D => @hom (Adj C D))
    (@AdjIdObj)
    (fun C D => @homset (Adj C D))
    (fun C D => @id (Adj C D))
    (fun C D => @compose (Adj C D))
    (fun C D => @compose_respects (Adj C D))
    (fun C D => @id_left (Adj C D))
    (fun C D => @id_right (Adj C D))
    (fun C D => @comp_assoc (Adj C D))
    (@Adj_Hcompose)
    (fun C D f => Adj_hunit_left f)
    (fun C D f => Adj_hunit_right f)
    (@Adj_hassoc)
    (@Adj_hunit_left_natural)
    (@Adj_hunit_right_natural)
    (@Adj_hassoc_natural)
    (@Adj_triangle)
    (@Adj_pentagon).

(* ====================================================================== *)
(* (6) N16-N24 (FORMABILITY): hom = proof.  The identification every      *)
(*     constant of the target carries in its BINDER is INHERITED, and     *)
(*     [Compose] is a donor of it on its own -- N20 refuses [Gq (o) Fq]   *)
(*     with no adjunction and no transformation anywhere in the command,  *)
(*     while a [Transform] between two functors is accepted.              *)
(* ====================================================================== *)

Section P399UnivHomProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu Du Eu : Category@{co ch cp}).

(* CONTROLS, all accepted at these very levels. *)

Check (fun o1 o2 : Cu => o1 ~{Cu}~> o2).
Check (fun o : Cu => @id Cu o).
Check (Cu ⟶ Du).
Check (Du ⟶ Cu).
Check (fun Fq Gq : Cu ⟶ Du => Fq ⟹ Gq).

(* -- N16.  [Adjunction] is a donor.                                     -- *)

Fail Check (fun (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du) => Fq ⊣ Uq).

(* -- N17-N19.  [AdjObj], [Adj] and [ConjPair] inherit it.  NOTE that    -- *)
(* -- [AdjObj] contains an [Adjunction] and [ConjPair] two [AdjObj]s, so -- *)
(* -- neither can be tested apart from its donor: N17-N19 record that     -- *)
(* -- the identification reaches them, not that they add one.            -- *)

Fail Check (AdjObj Cu Du).

Fail Check (Adj Cu Du).

Fail Check (fun o1 o2 : AdjObj Cu Du => @ConjPair Cu Du o1 o2).

(* -- N20, N21.  [Compose] refuses on its own; [nat_hcompose] refuses    -- *)
(* -- because its result type mentions [Compose], the [Transform]        -- *)
(* -- control above having been accepted.                                -- *)

Fail Check (fun (Fq : Cu ⟶ Du) (Gq : Du ⟶ Eu) => Gq ◯ Fq).

Fail Check (fun (F1 G1 : Cu ⟶ Du) (J1 K1 : Du ⟶ Eu)
                (aa : J1 ⟹ K1) (bb : F1 ⟹ G1) => nat_hcompose aa bb).

(* -- N22-N24.  Cat's own horizontal composition and the target's two    -- *)
(* -- 1-cell and bifunctor constants, all inheriting.                    -- *)

Fail Check (@Cat_Hcompose Cu Du Eu).

Fail Check (@adjobj_hcompose Cu Du Eu).

Fail Check (@Adj_Hcompose Cu Du Eu).

End P399UnivHomProof.

(* ====================================================================== *)
(* (7) N25, N26 (FORMABILITY): the two categories' HOM LEVELS.  Functors  *)
(*     in BOTH directions identify them before any adjunction is formed,  *)
(*     and [AdjObj] carries functors in both directions.                  *)
(* ====================================================================== *)

Section P399UnivHomLevels.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Aq : Category@{ao ah ah}).
Context (Bq : Category@{bo bh bh}).

Check (Aq ⟶ Bq).
Check (fun o1 o2 : Aq => o1 ~{Aq}~> o2).
Check (fun o1 o2 : Bq => o1 ~{Bq}~> o2).
Check (fun o : Aq => @id Aq o).

Fail Check (Bq ⟶ Aq).

Fail Check (AdjObj Aq Bq).

End P399UnivHomLevels.
