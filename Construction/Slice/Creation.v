Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Slice.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.

Set Universe Polymorphism.

Generalizable All Variables.

(** * The coslice projection creates limits *)

(* nLab: https://ncatlab.org/nlab/show/over+category#limits_and_colimits
   nLab: https://ncatlab.org/nlab/show/created+limit

   Mac Lane §V.1 Exercise 1 (book p. 112) asks for the coslice case of the
   comma lemma: the projection [c ̸co C ⟶ C] creates every limit [C] has.
   Riehl states the same as the limit half of §3.4 Proposition 8 (printed
   p. 106) and again as §4.7 Lemma 2 (printed p. 174), whose Exercise
   (printed p. 180) asks for the direct argument.

   The comma side of that is Construction/Comma/Creation.v, which needs no
   hypothesis here beyond one this library already supplies: [Id] is a right
   adjoint ([adj_id], Instance/Adjoints.v:70, re-exported as
   [Adjunction_Id], Adjunction/Compose.v:65), and
   [right_adjoint_PreservesImageLimit] (Construction/Comma/Limit.v:266)
   turns any adjunction into the preservation witness.  So
   [@PreservesImageLimit C C Id] is inhabited for EVERY category, with no
   premise at all, and every statement in this file is unconditional in that
   sense — the only hypothesis anywhere below is a [Complete C] where
   completeness is the conclusion's subject.

   What transports and what does not.  [Comma_Coslice] (Construction/Slice.v:182 —
   issue #438 and five in-tree sites cite :181, which is the [#[export]]
   attribute heading that same declaration)
   is an isomorphism [c ̸co C ≅ =(c) ↓ Id] in [Cat], hence an equivalence,
   hence a creator of all limits (Theory/Equivalence/Creation.v), so
   completeness and CreatesLimit both cross over.  STRICT creation does not:
   the only coslice projection reachable from here is the transported
   [comma_proj2 ◯ Coslice_to_Comma], whose object action does not reduce to
   the first projection — [Comma_Coslice] is a [Program Instance] whose
   [fobj] is an obligation — and there is no [StrictlyCreatesLimit_compose]
   to compose strictness through.  Test/ProbeCommaCreation438.v's negatives
   n3 and n4 pin both halves of that: the object action is refused against
   [`1 x], and the coslice is not the comma category on the nose.  A plain
   unconditioned projection [c ̸co C ⟶ C] would have to be built from
   scratch; the three in-tree coslice projections ([Coslice_Proj],
   Construction/Slice/Adjunction.v:392; [Coslice_proj],
   Instance/Cat/Pullback.v:847; [Coslice_Forget],
   Construction/Slice/Terminal.v:206) each carry an extra hypothesis on [C],
   so none of them serves. *)

(** ** The identity is its own right adjoint, so the comma side is free *)

Definition Id_PreservesImageLimit {C : Category} : @PreservesImageLimit C C Id
  := right_adjoint_PreservesImageLimit (@Adjunction_Id C).

Section CosliceComma.

Context {C : Category}.
Context (c : C).

(* Strict creation for the coslice READ AS A COMMA.  Here the projection is
   [comma_proj2] itself, so the strictness of Construction/Comma/Creation.v
   survives: apex by [eq_refl], legs by [reflexivity], at every limiting
   cone downstairs. *)

Definition coslice_comma_StrictlyCreatesLimit
  {J : Category} (K : J ⟶ (=(c) ↓ Id)) :
  StrictlyCreatesLimit K comma_proj2 :=
  comma_StrictlyCreatesLimit K
    (fun N HN => Id_PreservesImageLimit J (Gdiag K)
                   (@Build_Limit J C (Gdiag K) N HN)).

Definition coslice_comma_CreatesAllLimits :
  CreatesAllLimits (@comma_proj2 _ _ _ (=(c)) (Id[C])) :=
  fun J K => StrictlyCreatesLimit_CreatesLimit
               (coslice_comma_StrictlyCreatesLimit K).

(* Completeness of the coslice-as-comma, obtained THROUGH creation rather
   than through [Comma_Complete]. *)

Definition coslice_comma_Complete (HC : @Complete C) : @Complete (=(c) ↓ Id) :=
  creates_limits_Complete comma_proj2 HC coslice_comma_CreatesAllLimits.

(* The same completeness by the route the issue names, kept as a
   cross-check: [Comma_Complete_right_adjoint] at [Adjunction_Id] does
   type-check, exactly as the issue's "Also covered by" section claims.  It
   is a different term from the one above — that one goes through creation,
   this one through Construction/Comma/Limit.v's [Comma_Complete]. *)

Definition coslice_comma_Complete_via_adjoint (HC : @Complete C) :
  @Complete (=(c) ↓ Id) :=
  Comma_Complete_right_adjoint (@Adjunction_Id C) c HC.

(** ** Transporting along [Comma_Coslice] *)

Definition Coslice_to_Comma : (c ̸co C) ⟶ (=(c) ↓ Id) :=
  to (Comma_Coslice C c).

Definition Coslice_Comma_Equivalence :
  @EquivalenceOfCategories (c ̸co C) (=(c) ↓ Id) Coslice_to_Comma :=
  Cat_Iso_to_Equivalence (Comma_Coslice C c).

Definition Coslice_to_Comma_CreatesAllLimits :
  CreatesAllLimits Coslice_to_Comma :=
  equivalence_CreatesAllLimits Coslice_Comma_Equivalence.

Definition Coslice_Complete (HC : @Complete C) : @Complete (c ̸co C) :=
  creates_limits_Complete Coslice_to_Comma (coslice_comma_Complete HC)
    Coslice_to_Comma_CreatesAllLimits.

(* The coslice projection, as the transported comma projection. *)

Definition coslice_comma_proj : (c ̸co C) ⟶ C := comma_proj2 ◯ Coslice_to_Comma.

Definition coslice_comma_proj_CreatesLimit {J : Category} (K : J ⟶ (c ̸co C)) :
  CreatesLimit K coslice_comma_proj :=
  CreatesLimit_compose (Coslice_to_Comma_CreatesAllLimits J K)
    (coslice_comma_CreatesAllLimits J (Coslice_to_Comma ◯ K)).

Definition coslice_comma_proj_CreatesAllLimits :
  CreatesAllLimits coslice_comma_proj :=
  fun J K => coslice_comma_proj_CreatesLimit K.

End CosliceComma.
