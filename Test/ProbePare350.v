(** * Probe: boundaries of Paré's criterion

    Guards the strength claims of Adjunction/Pare.v from OUTSIDE that
    file — an in-file [Fail] renames in lockstep with the constant it
    guards and so cannot detect a rename.

    That file's header MEASURES a cluster of rejections and says plainly
    that they are "not guarded here, probes being out of scope for this
    file".  This file closes that gap.  The cluster is one phenomenon:
    [Compose] is not associative on the nose and [Id] is not a strict
    unit for it, so Mac Lane's own composites [Gε ∘ ρG] and [εK ∘ Kρ]
    are not formable as written — they would land at [Id[X] ◯ G ⟹ G ◯
    Id[A]] and [K ◯ Id[X] ⟹ Id[A] ◯ K] rather than at [G ⟹ G] and
    [K ⟹ K].

    The obstruction is LOCATED rather than asserted, and it is MEASURED
    rather than inferred.  [Functor] has primitive projections WITH ETA
    CONVERSION (Rocq reports this on [Print Functor]), so record equality
    IS field equality — which is exactly what makes the localization
    sharp, and neither this file nor the target said so before.  The
    [fobj]/[fmap] controls show two of the five fields agree; negatives
    5-7 show each of the remaining THREE fails individually, so the
    confinement is a measurement and not an inference from a head count.

    ALL NEGATIVES HERE ARE ONE KIND: CONVERSION.  An earlier revision of
    this file labelled negative 4 TYPING and claimed "two kinds", with
    the method "each stripped and its kind read off the error".  Applying
    that method refutes the claim: all of them report
    [The term "..." has type "..." while it is expected to have type
    "..." (cannot unify ...)] and negative 4 carries NO distinguishing
    marker — no [cannot satisfy constraint], no [Illegal application],
    which is how this tree's genuine TYPING negatives are told apart
    (Instance/Cat/Pullback.v and Theory/Morphisms/CokernelPair.v).  Only
    the POSITION of the mismatch differs.  The claim is withdrawn.

    The import list mirrors Adjunction/Pare.v's in full; a short prefix
    is what makes a probe pass vacuously, and a vacuity check cannot
    detect it. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Construction.Karoubi.Universal.
Require Import Category.Adjunction.Pare.

Generalizable All Variables.

Section ProbeAssoc.

Context {A X : Category}.
Context (G : A ⟶ X).
Context (K : X ⟶ A).

(* INSTRUMENT CHECK: scope-free, and it must fail. *)
Fail Definition instrument_check : True = False := eq_refl.

(* CONTROLS: the object and arrow actions DO agree on the nose, on both
   sides of associativity and of the left unitor.  These are what make
   the negatives below locate the failure in the LAW fields. *)
Example ctl_assoc_fobj :
  @fobj A X ((G ◯ K) ◯ G) = @fobj A X (G ◯ (K ◯ G)) := eq_refl.

Example ctl_assoc_fmap :
  @fmap A X ((G ◯ K) ◯ G) = @fmap A X (G ◯ (K ◯ G)) := eq_refl.

Example ctl_unitor_fobj :
  @fobj A X (Id[X] ◯ G) = @fobj A X G := eq_refl.

Example ctl_unitor_fmap :
  @fmap A X (Id[X] ◯ G) = @fmap A X G := eq_refl.

(* NEGATIVE 1 (CONVERSION): the whole functor records do NOT agree, even
   though both actions above do.  [Compose] is not associative on the
   nose. *)
Fail Definition neg_assoc_record :
  ((G ◯ K) ◯ G) = (G ◯ (K ◯ G)) := eq_refl.

(* NEGATIVE 2 (CONVERSION): nor is [Id] a strict unit for it. *)
Fail Definition neg_unitor_record : (Id[X] ◯ G) = G := eq_refl.

(* NEGATIVE 3 (CONVERSION): the right unitor fails as well, so repairing
   the middle would still leave the endpoints wrong. *)
Fail Definition neg_unitor_right : (G ◯ Id[A]) = G := eq_refl.

(* NEGATIVES 5-7 (CONVERSION): each of [Functor]'s three LAW fields fails
   individually across the associativity re-bracketing.  [Functor] has
   primitive projections WITH ETA, so record equality IS field equality;
   together with the [fobj]/[fmap] controls above, these MEASURE the
   confinement that the target's header infers from a field count. *)
Fail Definition neg_law_respects :
  @fmap_respects A X ((G ◯ K) ◯ G) = @fmap_respects A X (G ◯ (K ◯ G))
  := eq_refl.

Fail Definition neg_law_id :
  @fmap_id A X ((G ◯ K) ◯ G) = @fmap_id A X (G ◯ (K ◯ G)) := eq_refl.

Fail Definition neg_law_comp :
  @fmap_comp A X ((G ◯ K) ◯ G) = @fmap_comp A X (G ◯ (K ◯ G)) := eq_refl.

End ProbeAssoc.

Section ProbeTyping.

Context {A X : Category}.
Context (P : PareData A X).

(* CONTROL: the whiskered composites ARE formable at the types the file
   gives them. *)
Check (pare_Geps P).
Check (pare_rhoG P).
Check (pare_epsK P).
Check (pare_Krho P).

(* CONTROL: and the idempotent IS formable at [K ⟹ K]. *)
Check (pare_idem P : pare_K P ⟹ pare_K P).

(* NEGATIVE 4 (CONVERSION): Mac Lane's [εK ∘ Kρ] cannot be assembled at
   all — which is why the file builds its idempotent explicitly instead
   of as this composite.

   READ THE CAUSE OFF THE ERROR, NOT OFF THE INTENTION.  It fails at the
   MIDDLE object: [cannot unify "K ◯ (G ◯ K)" and "K ◯ G ◯ K"], i.e.
   ASSOCIATIVITY — negative 1's phenomenon.  The endpoints agree on both
   sides ([K ◯ Id[X]] appears in each), so the UNITORS are never reached.
   An earlier revision of this comment attributed the failure to
   negatives 2 and 3; that was wrong, and the endpoint half of the
   "three identifications are missing" finding is therefore guarded only
   INDIRECTLY here, by negatives 2 and 3 as bare facts about [G], never
   inside the composite.

   The ascription is written [_ ∙ _] with NO type annotation on purpose:
   annotating it [: pare_K P ⟹ pare_K P] is INERT — measured, the error
   is byte-identical with and without, to the character range — so an
   annotated form would suggest the endpoint is what fails when it is
   not. *)
Fail Check ((pare_epsK P) ∙ (pare_Krho P)).

End ProbeTyping.

Section ProbeRoundTrip.

Context {A X : Category}.
Context (P : PareData A X).
Context (F : X ⟶ A).
Context (r : pare_K P ⟹ F) (s : F ⟹ pare_K P).
Context (Hsr : ∀ x, transform[s] x ∘ transform[r] x
                      ≈ transform[pare_idem P] x).
Context (Hrs : ∀ x, transform[r] x ∘ transform[s] x ≈ id).

(* CONTROL: the adjunction built from the splitting exists. *)
Check (pare_Adjunction P F r s Hsr Hrs).

(* CONTROL: and so does the section recovered back out of it. *)
Check (pare_r P F (pare_Adjunction P F r s Hsr Hrs)).

(* NEGATIVE 8 (CONVERSION): but recovering the section from the
   adjunction built out of it does NOT return it.  The target's header
   discloses this as measured and delivers NO round trip in any form,
   [≈] included; an earlier revision of this probe pinned the OTHER
   disclosed cluster and left this one unguarded, so the commit message's
   plural was wrong.  Pinned here. *)
Fail Definition neg_round_trip :
  pare_r P F (pare_Adjunction P F r s Hsr Hrs) = r := eq_refl.

End ProbeRoundTrip.

(* Names the negatives depend on must also be named OUTSIDE a [Fail],
   or a rename would leave this file compiling and the guard green. *)
Check @pare_idem.
Check @pare_idem_Idempotent.
Check @pare_unit.
Check @pare_counit.
Check @pare_Adjunction.
Check @pare_SplitIdempotent.
Check @pare_left_adjoint_iff_splits.
Check @PareSplits.
Check @PareLeftAdjoint.
Check @pare_epsK.
Check @pare_Krho.
Check @PareData.
Check @nat_compose.
Check @pare_r.
Check @fmap_respects.
Check @fmap_id.
Check @fmap_comp.
