Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Sieve.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Fun.Classifier.
Require Import Category.Instance.Two.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.

Generalizable All Variables.

(** * Probe for issue #403 — the sieve classifier of a functor category *)

(* Every refutation command below was stripped ONE AT A TIME, compiled
   alone, and its WHOLE error read; the kind is read off the error TEXT.
   FORMABILITY = "universe inconsistency"/"Cannot enforce"; CONVERSION =
   "cannot unify" between two terms of ONE type; TYPING = a plain
   "has type ... while it is expected to have type ..." with neither a
   cannot-unify nor a universe clause, or "Illegal application";
   RESOLUTION = "Cannot infer this placeholder".

   1 instrument check + 16 negatives, classified by reading the whole
   error of each after stripping it alone:
     10 FORMABILITY  (lines with "universe inconsistency")
      2 RESOLUTION   ("Cannot infer this placeholder")
      3 TYPING       (a plain has-type clause, or "Illegal application")
      1 CONVERSION   ("cannot unify" between two terms of one type)
   The labels run 1-10 and 12-14 (with 4a/4b, 5a/5b and 6a/6b): there is
   no NEGATIVE 11 — the prediction it would have pinned was refuted and
   ships as the positive [probe403_med_strict] instead.

   The probe mirrors the UNION of the three library files' Require lines
   (a short prefix is what makes negatives pass for the wrong reason),
   plus Instance/Sets/Powerset/Universal.v for the squash control and
   Instance/FinSet/Classifier.v for [FinSet_Pullbacks].

   GUARD COVERAGE, measured mechanically over the comment-stripped file: 67
   identifiers occur inside a refutation command and 55 of them also occur
   outside every one.  The twelve exceptions are exhaustively the keyword
   itself, three bound variables (P, h, p), the seven [probe403_*] names
   DECLARED inside a refutation command (which therefore never enter the
   environment), and the instrument's deliberately absent name.

   RENAME SIMULATION, 11/11.  Eleven TARGET constants are named inside a
   refutation command — [Sieve], [total_sieve], [sieve_subpresheaf],
   [sieve_incl], [sieve_incl_Monic], [Fun_Classifier],
   [Fun_Classifier_cov], [Fun_Classifier_small], [PShSmall],
   [PShSmall_Terminal], [Fun_HasPullbacks].  Each was renamed in a SCRATCH
   COPY of the three library files (never in the worktree), compiled under
   a shadowing logical root, and this file recompiled against it: every one
   broke at a [Check] line of the guard block below and NONE inside a
   refutation command.  One vacuous guard was found that way and closed:
   [sieve_incl_Monic] was named only inside negative 5b, so renaming it
   left this file compiling; its [Check] was added, and so were [Check]s
   for the three [SubObj] field names the same negative uses.  The guard
   block was extended after the simulation ran, which can only add breaking
   lines; every one of the eleven has its [Check] in the file as shipped,
   verified mechanically. *)

(* ------------------------------------------------------------------ *)
(** ** Instrument check *)

(* A deliberately absent name: if this were to succeed, the refutation
   commands below would be measuring nothing. *)
Fail Check probe403_this_name_does_not_exist.

(* ------------------------------------------------------------------ *)
(** ** Guard controls — every constant a negative names, named outside *)

Check @Sieve.
Check @SieveObj.
Check @Sieve_Presheaf.
Check @total_sieve.
Check @sieve_mem.
Check @sieve_respects.
Check @sieve_closed.
Check @sieve_truth.
Check @char_nat.
Check @char_sieve.
Check @char_square.
Check @presheaf_char_unique.
Check @presheaf_char_pullback.
Check @sieve_subpresheaf.
Check @sieve_incl.
Check @sieve_subobject.
Check @sieve_incl_Monic.
Check @sieve_cone.
Check @Fun_Classifier.
Check @Fun_Classifier_IEM.
Check @Fun_Classifier_cov.
Check @Fun_Classifier_small.
Check @fun_classifier_classifies.
Check @fun_sub_classifier_natural.
Check @fun_Sub_Representable.
Check @PShSmall.
Check @PShSmall_Terminal.
Check @Fun_HasPullbacks.
Check @Fun_Pullback.
Check @Fun_IsPullback.
Check @Fun_Pullback_Functor.
Check @Fun_Pullback_fst.
Check @Fun_Pullback_snd.
Check @fpb_at.
Check @fun_pullback_med_at.
Check @fun_char_roundtrip.
Check @fun_pullback_roundtrip.
Check @MacOmega.
Check @macj.
Check @jmap.
Check @mac_dictionary.
Check @twoX_total.
Check @twoX_mid.
Check @twoX_empty.
Check @twoY_total.
Check @twoY_empty.
Check @twoX_code.
Check @twoY_code.
Check @twoX_three_sieves.
Check @twoY_two_sieves.
Check @classifier_classifies.
Check @Sub_classifier_natural.
Check @Untruncate.
Check @IEM.
Check @Powerset_squash.
Check @powerset_squash_prop_inert.
Check @Sets_HasPullbacks.
Check @FinSet_Pullbacks.
Check @Functor_Category_Terminal.
Check @Sets_Terminal.
Check @Fun.
Check @Opposite.
Check @Functor.
Check @HasPullbacks.
Check @SubobjectClassifier.
Check @Sets.
Check @FinSet.
Check @_2.
Check @Curried_CoHom.
Check @presheaf_monic_iff_injective.
Check @Monic.
Check @SubObj.
Check @Representable.
Check @Terminal.
Check @IsPullback.
Check @ump_pullbacks.
Check @pullback.
Check @Ω.
Check @truth.
Check @char.
Check @sub_reindex.
Check @Build_SubObj.
Check @sub_dom.
Check @sub_mono.
Check @sub_is_monic.

(* ------------------------------------------------------------------ *)
(** ** Positive controls the file's claims rest on *)

(* Mac Lane's Sets^2 is [_2, Sets], which is presheaves on [_2^op]:
   the double opposite is the identity here, ON THE NOSE. *)
Example probe403_op_op_two : (_2^op)^op = _2 := eq_refl.

(* The five computations of Mac Lane's j, restated from OUTSIDE the
   target so a rename in the target breaks this file. *)
Example probe403_j_total : jmap twoX_total ≈ twoY_total := j_total.
Example probe403_j_mid : jmap twoX_mid ≈ twoY_total := j_mid.
Example probe403_j_empty : jmap twoX_empty ≈ twoY_empty := j_empty.
Example probe403_j_identifies : jmap twoX_total ≈ jmap twoX_mid
  := j_identifies.
Example probe403_j_separates : jmap twoX_total ≈ jmap twoX_empty -> False
  := j_separates.

(* Mac Lane's explicit three-element object, computing. *)
Example probe403_macj_0 : macj Fin.F1 = Fin.F1 := eq_refl.
Example probe403_macj_1 : macj (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example probe403_macj_2 :
  macj (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.
Example probe403_macOmega_X : fobj[MacOmega] TwoX = 3%nat := eq_refl.
Example probe403_macOmega_Y : fobj[MacOmega] TwoY = 2%nat := eq_refl.
Example probe403_macOmega_fmap : fmap[MacOmega] TwoXY = macj := eq_refl.

(* The classifier's data, read back from outside. *)
Example probe403_omega {C : Category} (UT : Untruncate) :
  @Ω ([C^op, Sets]) _ (Fun_Classifier UT) = Sieve_Presheaf C := eq_refl.
Example probe403_truth {C : Category} (UT : Untruncate) :
  @truth ([C^op, Sets]) _ (Fun_Classifier UT) = sieve_truth C := eq_refl.

(* The pointwise pullback, read back from outside. *)
Example probe403_pb_obj {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (a : F ~{[C, D]}~> H) (b : G ~{[C, D]}~> H) (x : C) :
  fobj[Pull _ _ (Fun_Pullback HP a b)] x
    = Pull _ _ (pullback (transform[a] x) (transform[b] x)) := eq_refl.

(* ------------------------------------------------------------------ *)
(** ** (1)-(2) [classifier_classifies] at the presheaf category *)

Section CC.
Context {C : Category}.
Context (HPB : @HasPullbacks ([C^op, Sets])).
Context (HS : @SubobjectClassifier ([C^op, Sets])
                (Functor_Category_Terminal Sets_Terminal)).
Context (UT : Untruncate).

(* CONTROL: the theorem IS formable at an ABSTRACT classifier of a
   presheaf category — unlike at [Sets], where #402 records that it is
   not statable at all. *)
Check (@classifier_classifies ([C^op, Sets])
         (Functor_Category_Terminal Sets_Terminal) HPB HS).
Check (@Sub_classifier_natural ([C^op, Sets])
         (Functor_Category_Terminal Sets_Terminal) HPB HS).

(* NEGATIVE 1 (FORMABILITY).  It is NOT applicable to the built
   [Fun_Classifier], whose elaboration minimizes the presheaf category's
   hom universe below its object universe.  The stripped error ends
   "Cannot enforce ... because ... <= ... < ...". *)
Fail Check (@classifier_classifies ([C^op, Sets])
              (Functor_Category_Terminal Sets_Terminal)
              (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT)).

(* NEGATIVE 2 (FORMABILITY).  Nor is the naturality upgrade. *)
Fail Check (@Sub_classifier_natural ([C^op, Sets])
              (Functor_Category_Terminal Sets_Terminal)
              (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT)).
End CC.

(* CONTROL: at the SECOND reading of the presheaf category — objects at
   or below homs — both DO apply, which is what section (I) of the
   target ships.  This pair is the precise form of the sentence
   "classifier_classifies is not statable for presheaf categories",
   which is false as stated. *)
Section CCSmall.
Universes co o so OO HH.
Constraint Set < o.
Constraint o < so.
Constraint so <= OO.
Constraint OO <= HH.
Context (Cs : Category@{co o o}).
Context (UTs : Untruncate@{o}).
Check (@classifier_classifies (PShSmall Cs) (PShSmall_Terminal Cs)
         (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier_small Cs UTs)).
Check (fun_classifier_classifies Cs UTs).
Check (fun_sub_classifier_natural Cs UTs).
Check (fun_Sub_Representable Cs UTs).

(* NEGATIVE 3 (FORMABILITY).  The BUILT [Fun_Classifier] still cannot be
   re-typed at those levels — a re-annotated REDEFINITION is what
   escapes, not a re-ascription of the constant. *)
Fail Check (Fun_Classifier (C:=Cs) UTs
              : @SubobjectClassifier (PShSmall Cs) (PShSmall_Terminal Cs)).
End CCSmall.

(* ------------------------------------------------------------------ *)
(** ** (4) No [HasPullbacks] for a functor category by resolution *)

(* CONTROLS: the two base categories DO have registered instances, and
   the target's plain [Definition] supplies the functor-category ones. *)
Definition probe403_pb_sets : @HasPullbacks Sets := _.
Definition probe403_pb_finset : @HasPullbacks FinSet := _.
Check (Fun_HasPullbacks Sets_HasPullbacks : @HasPullbacks ([_2, Sets])).
Check (Fun_HasPullbacks FinSet_Pullbacks : @HasPullbacks ([_2, FinSet])).

(* NEGATIVE 4a, 4b (RESOLUTION).  [Fun_HasPullbacks] is deliberately a
   plain [Definition] and not an [Instance], so resolution still finds
   nothing; the stripped errors read "Cannot infer this placeholder ...
   (no type class instance found)".  Note [Fail Check (_ : T)] is NOT a
   valid negative here — Coq accepts it and prints the evar. *)
Fail Definition probe403_no_pb_sets : @HasPullbacks ([_2, Sets]) := _.
Fail Definition probe403_no_pb_finset : @HasPullbacks ([_2, FinSet]) := _.

(* ------------------------------------------------------------------ *)
(** ** (5) The class takes TWO arguments, and its literals want the
        category written out *)

Section Arity.
Context {C : Category}.

(* CONTROL: the two-argument form. *)
Check (@SubobjectClassifier ([C^op, Sets])
         (Functor_Category_Terminal Sets_Terminal)).

(* NEGATIVE 5a (TYPING).  Offering a [HasPullbacks] as a third argument
   is an "Illegal application (Non-functional construction)": the
   [HasPullbacks] of the class's declaring section is used by the
   theorems BELOW the class, not by the class. *)
Fail Check (@SubobjectClassifier ([C^op, Sets])
              (Functor_Category_Terminal Sets_Terminal)
              (Fun_HasPullbacks Sets_HasPullbacks)).

(* CONTROL: the subobject of the representable, with the category
   written out. *)
Check (fun (c : C) (S : Sieve c) => sieve_subobject c S).

(* NEGATIVE 5b (TYPING).  The same record literal WITHOUT the explicit
   category is refused: the [sub_dom] field elaborates against
   [obj[?C]], and the stripped error is a plain "has type ... while it
   is expected to have type "obj[?C]"" with no cannot-unify and no
   universe clause. *)
Fail Definition probe403_sub_literal (c : C) (S : Sieve c) :
  @SubObj ([C^op, Sets]) (Curried_CoHom C c) :=
  {| sub_dom := sieve_subpresheaf c S
   ; sub_mono := sieve_incl c S
   ; sub_is_monic := sieve_incl_Monic c S |}.
End Arity.

(* ------------------------------------------------------------------ *)
(** ** (6) The presheaf category's two universe identifications *)

Section DonorA.
Universes co ch cp o so.
Constraint ch < cp.
Constraint o < so.
Context (Cu : Category@{co ch cp}).

(* CONTROLS accepted at levels where hom and proof are DECLARED APART:
   the hom type, an identity, and functors in both directions.  So
   [Functor] is NOT a donor of [ch = cp]. *)
Check (fun (x y : Cu) => x ~{Cu}~> y).
Check (fun (x : Cu) => @id Cu x).
Check (@Functor Cu Cu).
Check (@Functor Cu Sets@{o so}).

(* NEGATIVE 6a (FORMABILITY).  [Opposite] forces [ch = cp] on its own. *)
Fail Check (Cu^op).

(* NEGATIVE 6b (FORMABILITY).  So does [Fun], with NO [^op] anywhere in
   the command — two INDEPENDENT donors. *)
Fail Check ([Cu, Sets@{o so}]).
End DonorA.

Section DonorB.
Universes co2 ch2 o2 so2.
Constraint ch2 < o2.
Constraint o2 < so2.
Context (Cv : Category@{co2 ch2 ch2}).

(* CONTROLS: the opposite and both functor types elaborate with C's hom
   universe DECLARED BELOW [Sets]' carrier universe.  So neither
   [Opposite] nor [Functor] is a donor of [ch = o]. *)
Check (Cv^op).
Check (@Functor (Cv^op) Sets@{o2 so2}).
Check (@Functor Cv Sets@{o2 so2}).
Check (Sets@{o2 so2}).

(* NEGATIVE 7 (FORMABILITY).  [Fun] identifies its source and target hom
   universes, so the presheaf category pins C's hom universe to [Sets]'
   carrier universe.  The covariant reading is refused identically; the
   file's [Fun_Classifier_cov] therefore inherits the same bound. *)
Fail Check ([Cv^op, Sets@{o2 so2}]).
End DonorB.

Section DonorC.
Universes co3 ch3 do3 dh3.
Constraint ch3 < dh3.
Context (Cw : Category@{co3 ch3 ch3}).
Context (Dw : Category@{do3 dh3 dh3}).

(* CONTROL: the bare functor type elaborates at hom levels declared
   apart, so [Functor] is not the donor of Instance/Fun/Pullback.v's
   block equation [u0 = u2]. *)
Check (@Functor Cw Dw).

(* NEGATIVE 8 (FORMABILITY).  [Fun] is: the functor CATEGORY is
   refused at the same levels. *)
Fail Check ([Cw, Dw]).
End DonorC.

(* ------------------------------------------------------------------ *)
(** ** (3) A [Type]-valued sieve is not an object of [Sets] *)

Section TypeSieve.
Universes co4 ch4 cp4 o4 so4.
Constraint Set < o4.
Constraint o4 < so4.
Context (Cx : Category@{co4 ch4 ch4}).
Context (cx : obj[Cx]).

(* The [Type]-valued analogue of the record. *)
Record TSieve@{} (c : obj[Cx]) : Type@{max(co4,ch4,o4+1)} := {
  tsieve_mem : ∀ (d : obj[Cx]), (d ~{Cx}~> c) → Type@{o4};
  tsieve_closed : ∀ (d e : obj[Cx]) (f : d ~{Cx}~> c) (g : e ~{Cx}~> d),
      tsieve_mem d f → tsieve_mem e (f ∘ g)
}.

(* CONTROL: the [Prop]-valued carrier IS a [Type@{o4}]. *)
Check (Sieve cx : Type@{o4}).

(* NEGATIVE 9 (FORMABILITY).  The [Type@{o4}]-valued one sits at
   [o4 + 1]; the stripped error is "Cannot enforce o4 < o4 because
   o4 = o4".  This is why membership is [Prop]-valued and the
   characteristic sieve must truncate. *)
Fail Check (TSieve cx : Type@{o4}).
End TypeSieve.

(* ------------------------------------------------------------------ *)
(** ** (10) The truncation is not eliminable without [Untruncate] *)

(* CONTROL: over a [Prop] the squash is inert. *)
Check @powerset_squash_prop_inert.

(* NEGATIVE 10 (FORMABILITY).  The naive elimination is refused with
   "Cannot enforce ... <= Prop" — #402's wall, at the same level, and
   what [Untruncate] buys. *)
Fail Definition probe403_naive_untruncate@{o} : Untruncate@{o} :=
  fun P h => h P (fun p => p).

(* ------------------------------------------------------------------ *)
(** ** (9) The pointwise mediator is [≈] and not [eq_refl] *)

Section Med.
Context {C D : Category}.
Context (HP : @HasPullbacks D).
Context {F G H : C ⟶ D}.
Context (a : F ~{[C, D]}~> H) (b : G ~{[C, D]}~> H).
Context {Q : C ⟶ D} (q1 : Q ~{[C, D]}~> F) (q2 : Q ~{[C, D]}~> G).
Context (Hq : a ∘ q1 ≈ b ∘ q2).

(* POSITIVE, and it REFUTES a prediction: the mediator's component IS
   D's mediator at [eq_refl], not merely at [≈].  The brief expected a
   CONVERSION refutation here on the ground that the bundled
   [Fun_Pullback] reaches its universal property through
   [is_pullback_pullback] of [Fun_IsPullback]; measurement says
   otherwise, because [is_pullback_pullback] is a field repackaging and
   [Build_Transform'] is transparent, so the whole chain reduces. *)
Example probe403_med_strict (x : C) :
  transform[unique_obj (ump_pullbacks _ _ (Fun_Pullback HP a b) Q q1 q2 Hq)] x
    = unique_obj (ump_pullbacks _ _ (fpb_at HP a b x) (Q x)
                    (transform[q1] x) (transform[q2] x) (Hq x))
  := eq_refl.

(* The [≈] form is then a weakening, kept in the target because it is
   the shape a consumer rewrites with. *)
Check (fun x : C => fun_pullback_med_at HP a b q1 q2 Hq x).
End Med.

(* ------------------------------------------------------------------ *)
(** ** (11) The two classifier readings are not the same constant *)

Section TwoReadings.
Universes co5 o5 so5 OO5 HH5.
Constraint Set < o5.
Constraint o5 < so5.
Constraint so5 <= OO5.
Constraint OO5 <= HH5.
Context (Cz : Category@{co5 o5 o5}).
Context (UTz : Untruncate@{o5}).

(* CONTROL: both readings have the same truth object at [eq_refl],
   each against [Sieve_Presheaf] in its own category. *)
Check (@eq_refl _ (Sieve_Presheaf Cz)
        : @Ω (PShSmall Cz) (PShSmall_Terminal Cz)
             (Fun_Classifier_small Cz UTz) = Sieve_Presheaf Cz).

(* NEGATIVE 12 (FORMABILITY, and the kind was a prediction measurement
   corrected).  The two readings are not comparable at all: the refusal
   is a universe inconsistency, "Cannot enforce o5 = ... because
   o5 < ... <= ... <= ...", not the "cannot unify" a conversion
   refutation would give.  So the two classifiers do not even share a
   type, and NO equation between the readings is claimed anywhere. *)
Fail Definition probe403_two_readings :
  Fun_Classifier_small Cz UTz = Fun_Classifier (C:=Cz) UTz := eq_refl.
End TwoReadings.

(* ------------------------------------------------------------------ *)
(** ** (12) [Fun_Classifier_cov] is a conversion, not a transport *)

(* CONTROL: the covariant reading IS [Fun_Classifier] at the opposite,
   supplied by [:=] with no tactic — [(D^op)^op = D] by [eq_refl]. *)
Example probe403_cov {D : Category} (UT : Untruncate) :
  @Fun_Classifier_cov D UT = @Fun_Classifier (D^op) UT := eq_refl.

(* NEGATIVE 13 (TYPING).  The two ARE at different categories all the
   same: [Fun_Classifier_cov] is at [[D, Sets]] and cannot be ascribed
   at the presheaf category of the same D.  The stripped error is a
   plain has-type clause with no cannot-unify and no universe clause. *)
Section Cov.
Context {D : Category}.
Context (UT : Untruncate).
Fail Definition probe403_cov_bad :
  @SubobjectClassifier ([D^op, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  @Fun_Classifier_cov D UT.
End Cov.

(* ------------------------------------------------------------------ *)
(** ** (13) The sieve subpresheaf of the total sieve is not the
        representable ON THE NOSE *)

Section TotalSub.
Context {C : Category}.
Context (c : C).

(* CONTROLS: both ARE objects of the same presheaf category, so the
   refusal below is about conversion and not about formability. *)
Check (sieve_subpresheaf c (total_sieve c)).
Check (fobj[Curried_CoHom C] c).

(* NEGATIVE 14 (CONVERSION) — the file's ONLY one.  The subpresheaf cut
   by the total sieve has carrier [{ g : k ~> c & True }] where the
   representable has [k ~> c]; the stripped error is "cannot unify"
   between two terms of one type.  An isomorphism between them is NOT
   built: the classifier never needs one, since the uniqueness clause
   feeds the pullback the subpresheaf directly. *)
Fail Definition probe403_total_sub :
  sieve_subpresheaf c (total_sieve c) = fobj[Curried_CoHom C] c := eq_refl.
End TotalSub.
