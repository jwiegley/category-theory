Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Orthogonality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Regular.Factorization.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Instance.FinSet.Subobject.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * Probe for Theory/Subobject/Lattice.v, Instance/Sets/SubobjectLattice.v
      and Instance/FinSet/Subobject.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.7
    Definition 2, printed p. 126; Riehl, Category Theory in Context, 2nd ed.,
    Definition 4.7.9, printed p. 177; Fong and Spivak, Seven Sketches in
    Compositionality, §1.2.1, printed p. 8.  Issue #445.

    The import list above is the UNION of the three target files' own import
    lists, unabbreviated, plus Theory/Subobject/Functor.v for the one
    readback that needs [sub_reindex].  A short prefix is what makes a probe
    pass vacuously, so nothing is trimmed even where a require is redundant.

    This file guards the strength claims of those three files.  Every
    statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and its
    complete error read; a refutation that holds prints nothing under this
    repo's coqc, so a whole-file rc=0 would establish only THAT each command
    does not typecheck and never WHY.  Each negative is classified by the
    error TEXT, under THIS import list (the parenthetical of a conversion
    error is rendered with the short names in scope, so the same refusal can
    print differently elsewhere):

      TYPING      - "The term T has type X while it is expected to have
                    type Y", with NO trailing "cannot unify" clause and no
                    universe clause.
      CONVERSION  - the same, with a trailing "(cannot unify A and B)".
      FORMABILITY - the statement cannot even be elaborated: an unresolved
                    implicit, "Cannot infer this placeholder", with NO
                    "(no type class instance found)" parenthetical (N3).
      INSTANCE    - an implicit argument of class type that no instance in
                    scope resolves.  The DISCRIMINATOR is the parenthetical
                    "(no type class instance found)", which Rocq appends
                    to either opener -- "Cannot infer the implicit
                    parameter H of ..." (N1, N4) or "Cannot infer this
                    placeholder of type ..." (N7); the opener alone does
                    not separate INSTANCE from FORMABILITY.  NOTE that a
                    bare [Check] TOLERATES such an open evar and succeeds,
                    printing "where ?H : [...]"; every missing-instance
                    negative below is therefore a [Definition], measured to
                    be refused where the [Check] form is accepted.

    The instrument check comes first: a name that does not exist, refused
    for a reason unrelated to any boundary.  Every LIBRARY constant a
    negative names -- in its statement, its section context or its proof
    term -- appears in a positive control outside any refutation command
    (stdlib names such as [Empty_set] and [False] excepted), so that a
    rename cannot leave a negative refused for reference-not-found and
    therefore vacuously green.  An independent audit of the first draft
    found six such constants uncovered ([WidePullback], [IsPullback],
    [IsWidePullback], [ImageOf], [terminal_obj], [Sets_Terminal]); the
    controls below were extended to cover them. *)

(** ** Instrument check *)

Fail Check sub_lattice_no_such_constant.

(** ** Positive controls: every constant the negatives depend on *)

Check @sub_meet.
Check @sub_meet_comm.
Check @sub_meet_is_glb.
Check @sub_wide_intersection.
Check @sub_wide_intersection_IsIntersection.
Check @sub_join.
Check @sub_join_via.
Check @sub_join_via_bot.
Check @sub_join_bot.
Check @sub_bot.
Check @sub_top.
Check @sub_pair.
Check @sub_compose.
Check @sub_reindex.
Check @ImageOf.
Check @ImageOf_of_OFS.
Check @OFS.
Check @MorphismClass.
Check @MonoClass.
Check @EpiClass.
Check @WidePullback.
Check @IsWidePullback.
Check @IsPullback.
Check @binary_wide_pullback.
Check @two_legs.
Check @terminal_obj.
Check @Sets_Terminal.
Check @Sets_HasImages.
Check @Sets_HasWidePullbacks.
Check @Sets_wpull_obj.
Check @fs_union.
Check @fs_pos.
Check @pos_obj.
Check @fs_union_is_positives.
Check @fs_inter_is_empty.
Check @FinSet_HasImages.
Check @ex11_u.
Check @ex11_v.

(** ** Readbacks that HOLD, at the strength stated *)

Section Readbacks.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(* The header of Theory/Subobject/Lattice.v states, and this pins, that the
   binary meet IS the pushforward along u of the reindexing of v along
   sub_mono u -- the same record with the same three fields, at Leibniz
   equality and with no tactic.  Theory/Subobject/Lattice.v does not import
   Theory/Subobject/Functor.v, so the readback lives here. *)
Example p445_meet_is_compose_reindex (u v : SubObj x) :
  sub_meet u v = sub_compose u (sub_reindex (sub_mono u) v) := eq_refl.

End Readbacks.

(* The FinSet numbers, restated here as the controls the negatives N8 and N9
   are read against: 4 (merging) and 1 (the meet) compute by [eq_refl]. *)
Example p445_union_four : sub_dom (sub_join ex11_u ex11_v) = 4%nat := eq_refl.
Example p445_meet_one : sub_dom (sub_meet ex11_u ex11_v) = 1%nat := eq_refl.
Example p445_coproduct_five :
  @Coprod FinSet FinSet_Cocartesian 2%nat 3%nat = 5%nat := eq_refl.

(** ** Negatives *)

Section NoPullbacks.

Context {C : Category}.
Context {x : C}.

(* N1 -- INSTANCE.  [sub_meet] is conditional on chosen pullbacks; with no
   [HasPullbacks C] in scope the definition is refused with "Cannot infer
   the implicit parameter H of sub_meet whose type is HasPullbacks C (no
   type class instance found)".  Measured: the [Check] form of the same
   term is ACCEPTED, printing the open evar, which is why this is a
   [Definition]. *)
Fail Definition n1 (u v : SubObj x) : SubObj x := sub_meet u v.

(* N3 -- FORMABILITY.  Over an EMPTY index there is no j0 to present the
   intersection at, and the wide pullback is the terminal object rather
   than the top subobject (Structure/Pullback/Wide.v); the hole cannot
   be filled: "Cannot infer this placeholder of type Empty_set".  The
   intersection of the empty family is [sub_top] ([IsIntersection_empty]),
   not anything read off a wide pullback. *)
Fail Definition n3 (S : Empty_set → SubObj x)
  (W : WidePullback (fun j => sub_mono (S j))) : SubObj x :=
  sub_wide_intersection S _ W.

End NoPullbacks.

Section WithPullbacks.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(* N2 -- TYPING.  Commutativity of the meet holds at ≈ on [SubObj x] (an
   isomorphism of domains over x) and NOT at Leibniz equality: the two
   chosen pullbacks are different records.  "The term sub_meet_comm u v
   has type sub_meet u v ≈ sub_meet v u while it is expected to have type
   sub_meet u v = sub_meet v u", with no "cannot unify" clause.  The
   statement itself is well-formed; the refusal is at the proof. *)
Fail Definition n2 (u v : SubObj x) : sub_meet u v = sub_meet v u :=
  sub_meet_comm u v.

(* N5 -- CONVERSION.  Structure/Pullback/Wide.v's [binary_wide_pullback]
   is stated over [two_fam (sub_dom u) (sub_dom v)], and that family is
   convertible with [fun b => sub_dom (sub_pair u v b)] at the two literals
   but NOT as a function of a variable b: "cannot unify P ~{ C }~>
   two_fam (sub_dom u) (sub_dom v) b and P ~{ C }~> sub_dom (sub_pair u v
   b)" (verbatim, under this import list).  This is
   the measured reason [sub_meet_is_wide_intersection] is proved through
   [IsIntersection_unique] instead of through that lemma. *)
Fail Definition n5 (u v : SubObj x) (P : C)
  (q1 : P ~> sub_dom u) (q2 : P ~> sub_dom v)
  (HP : IsPullback (sub_mono u) (sub_mono v) P q1 q2) :
  IsWidePullback (fun b => sub_mono (sub_pair u v b)) P (two_legs q1 q2) :=
  binary_wide_pullback HP.

End WithPullbacks.

Section NoImages.

Context {C : Category}.
Context `{@Cocartesian C}.
Context {x : C}.

(* N4 -- INSTANCE.  The join is conditional on images: with a cocartesian
   structure but no [HasImages C], "Cannot infer the implicit parameter H0
   of sub_join whose type is HasImages C (no type class instance found)".
   The [Check] form is accepted, as for N1. *)
Fail Definition n4 (u v : SubObj x) : SubObj x := sub_join u v.

End NoImages.

Section WrongClass.

Context {C : Category}.
Context {E : MorphismClass C}.

(* N6 -- CONVERSION.  An image as a subobject needs the RIGHT class of the
   factorization system to be the monos, because [fact_m_in] is fed
   directly to the [sub_is_monic] field; an (E, Epi) system is refused:
   "cannot unify EpiClass and MonoClass". *)
Fail Definition n6 (O : OFS E (@EpiClass C)) {y z : C} (f : y ~> z) :
  ImageOf f := ImageOf_of_OFS O f.

End WrongClass.

Section NoStrictness.

Context {C : Category}.
Context `{I : @Initial C}.
Context {x : C}.

(* N7 -- INSTANCE.  The bottom subobject needs the arrow out of the initial
   object to be MONIC, which an initial object does not supply by itself:
   "Cannot infer this placeholder of type Monic zero[x] (no type class
   instance found)".  [I] is pinned explicitly because [@Initial C] is a
   notation for [@Terminal (C^op)] and resolution does not see through it,
   which would otherwise add a second, unrelated placeholder to the
   verdict. *)
Fail Definition n7 : SubObj x := @sub_bot C I x _.

End NoStrictness.

(* N8 -- CONVERSION.  Merging versus tagging: the union of {0,1} and
   {1,2,3} inside 4 has FOUR elements (p445_union_four), and the tagged
   count 5 is refused: "cannot unify sub_dom (sub_join ex11_u ex11_v) and
   5%nat". *)
Fail Example n8 : sub_dom (sub_join ex11_u ex11_v) = 5%nat := eq_refl.

(* N9 -- CONVERSION.  The meet of the same two has ONE element
   (p445_meet_one); 2, the size of the first factor, is refused: "cannot
   unify sub_dom (sub_meet ex11_u ex11_v) and 2%nat".  So the pullback
   genuinely intersected rather than returning a leg's domain. *)
Fail Example n9 : sub_dom (sub_meet ex11_u ex11_v) = 2%nat := eq_refl.

(* N10 -- CONVERSION.  In Sets the union of the increasing family is ≈ the
   positive naturals ([fs_union_is_positives], an isomorphism of domains
   over nat) and NOT equal to them on the nose: the image carrier is a
   point of nat with a chosen preimage, not the sig of a positivity proof.
   "cannot unify sub_dom fs_union and pos_obj". *)
Fail Example n10 : sub_dom fs_union = pos_obj := eq_refl.

(* N11 -- CONVERSION.  The empty-index wide pullback in Sets is terminal
   only up to ≅ (Structure/Pullback/Wide.v's [wide_pullback_empty_terminal])
   and is NOT convertible with the chosen terminal setoid: its carrier is
   the setoid of empty coherent families, not [poly_unit].  Refused with
   "cannot unify", the two sides being the wide-pullback object and 1. *)
Fail Example n11 :
  Sets_wpull_obj (I:=False) (A:=fun i => match i with end)
    (z:=@terminal_obj Sets Sets_Terminal) (fun i => match i with end)
  = @terminal_obj Sets Sets_Terminal := eq_refl.
