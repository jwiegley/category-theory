Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sieve.
Require Import Category.Theory.Subobject.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Structure.Topos.Colimits.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Pushout.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.Topos.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Fun.Classifier.
Require Import Category.Instance.Fun.Topos.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Adjunction.GAFT.Sets.

Open Scope category_scope.

(** * Probe for issue #404: Sets and presheaf categories as toposes

    Guards Instance/Fun/Topos.v and Instance/Sets/Topos.v.  Its Require
    list is the UNION of theirs plus Structure/Topos/{Power,Monadic,
    Colimits}.v, Monad/Comparison.v, Structure/SubobjectClassifier/
    Natural.v, Theory/Subobject.v, the four shape modules
    (One, Two, Ordinal, Parallel, Roof), the three further Sets colimit
    modules and Adjunction/GAFT/Sets.v.  Those extras live here, and not
    in the library files, because Structure/Topos/{Monadic,Colimits}.v
    alone take the presheaf file's closure from 108 to 133 and the
    setoid file's from 74 to 101.

    NINETEEN refutation commands: ONE instrument check plus EIGHTEEN
    negatives, of FOUR kinds, told apart by the error TEXT and not by
    label.

      FORMABILITY  the error ends in a universe clause
                   ("universe inconsistency: Cannot enforce ...").
      CONVERSION   "cannot unify" between two terms of one type.
      TYPING       a plain has-type mismatch, no "cannot unify" and no
                   universe clause.
      RESOLUTION   "Cannot infer this placeholder ... (no type class
                   instance found)".

    Count by kind: 11 FORMABILITY (negatives 1-7 and 10-13), 4 CONVERSION
    (14-17), 2 TYPING (9 and 18), 1 RESOLUTION (8).

    Every negative was stripped from its Fail ONE AT A TIME, compiled
    alone in a scratch file mirroring this Require list, and its WHOLE
    error read before being classified.  Every constant a negative names
    is also Checked outside every Fail, in the guard block at the end.
*)

(* ==================================================================== *)
(** ** Instrument: a Fail that passes because the name is absent *)

Fail Check p404_instrument_absent.

(* ==================================================================== *)
(** ** (A) Presheaf negatives *)

Section PshNegatives.

Context (C : Category) (UT : Untruncate).

(* NEGATIVE 1 (FORMABILITY).  The classification theorem is not statable
   at this topos: it carries objects <= homs, while the presheaf
   category's objects sit strictly above its homs.  Stripped:

     The term "topos_terminal" has type "Terminal@{n1.41 n1.23}"
     while it is expected to have type "Terminal@{n1.26 n1.27}"
     (universe inconsistency: Cannot enforce n1.23 = n1.27 because
      n1.23 < n1.31 <= n1.26 <= n1.27).                              *)
Fail Check (@classifier_classifies ([C^op, Sets])
              (@topos_terminal _ (Presheaf_Topos C UT))
              (@topos_pullbacks _ (Presheaf_Topos C UT))
              (@topos_classifier _ (Presheaf_Topos C UT))).

(* NEGATIVE 2 (FORMABILITY).  [relations_iso] is built as
   [iso_compose exp_iso (classifier_classifies (a × b))] and inherits
   the refusal.  Stripped:

     The term "Presheaf_Topos C UT" has type
      "ElementaryTopos@{n2.41 n2.41 n2.23} ([C^op, Sets@{n2.23 n2.41}])"
     while it is expected to have type
      "ElementaryTopos@{n2.26 n2.27 n2.27} ([C^op, Sets@{n2.23 n2.30}])"
     (universe inconsistency: Cannot enforce n2.23 = n2.27 because
      n2.23 < n2.30 <= n2.27).                                       *)
Fail Check (@relations_iso ([C^op, Sets]) (Presheaf_Topos C UT)).

(* NEGATIVE 3 (FORMABILITY).  The naturality upgrade likewise.
   Stripped:

     The term "topos_terminal" has type "Terminal@{n3.41 n3.23}"
     while it is expected to have type "Terminal@{n3.26 n3.27}"
     (universe inconsistency: Cannot enforce n3.23 = n3.27 because
      n3.23 < n3.31 <= n3.26 <= n3.27).                              *)
Fail Check (@Sub_classifier_natural ([C^op, Sets])
              (@topos_terminal _ (Presheaf_Topos C UT))
              (@topos_pullbacks _ (Presheaf_Topos C UT))
              (@topos_classifier _ (Presheaf_Topos C UT))).

(* NEGATIVE 9 (TYPING).  The restriction readback must ascribe its arrow
   into [C^op]; written through the [morphism] coercion instead, the
   coercion is left an evar [?s] and [eq_refl] does not close.  No
   "cannot unify", no universe clause.  The ACCEPTED spelling is the
   control immediately below.  Stripped:

     The term "eq_refl" has type
      "?s (fmap[Sieve_Presheaf C] h) S = ?s (fmap[Sieve_Presheaf C] h) S"
     while it is expected to have type
      "?s (fmap[Sieve_Presheaf C] h) S = sieve_restrict h S".         *)
Fail Example p404_restrict (c d : C) (h : d ~{C}~> c) (S : Sieve c) :
  morphism (fmap[Sieve_Presheaf C] h) S = sieve_restrict h S := eq_refl.

Example p404_restrict_ctrl (c d : C) (h : d ~{C}~> c) (S : Sieve c) :
  fmap[@Ω ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))]
      (h : c ~{C^op}~> d) S
  = sieve_restrict h S := eq_refl.

End PshNegatives.

(* NEGATIVE 5 (FORMABILITY).  [_2] is declared with hom AND proof at the
   literal [Set], and [Fun_Classifier] carries the strict lower bound
   [Set < u].  The DISCRIMINATING CONTROL is the line above it:
   [Functor_Category_Closed _2] IS accepted, so the exclusion is the
   CLASSIFIER's and not the exponential's.  Stripped:

     The term "_2" has type "Category@{n5.32 Set Set}"
     while it is expected to have type "Category@{n5.29 n5.30 n5.30}"
     (universe inconsistency: Cannot enforce Set = n5.30 because
      Set < n5.30).                                                  *)
Check (Functor_Category_Closed _2).
Fail Definition p404_two (UT : Untruncate) := Presheaf_Topos _2 UT.

(* NEGATIVE 8 (RESOLUTION).  The bundle does not resolve: [ElementaryTopos]
   has no registered instance and its constructor is not one.  Stripped:

     The following term contains unresolved implicit arguments:
       (fun (C : Category) (UT : Untruncate) => ?e)
     More precisely:
     - ?e: Cannot infer this placeholder of type
       "ElementaryTopos ([C^op, Sets])" (no type class instance found)
       in environment: C : Category, UT : Untruncate                 *)
Fail Definition p404_resolve (C : Category) (UT : Untruncate) :
  ElementaryTopos ([C^op, Sets]) := _.

(* -------------------------------------------------------------------- *)
(** ** (B) The two donors of the smallness bound [objects <= homs] *)

(* A section declaring C's OBJECTS STRICTLY ABOVE its homs.  The
   terminal, cartesian and pullback donors are all ACCEPTED there; the
   exponential and the classifier are each refused ALONE. *)

Section DonorClosed.
Universes co ch cso.
Constraint ch < co.
Constraint Set < ch.
Constraint ch < cso.
Context (Cq : Category@{co ch ch}) (UTq : Untruncate@{ch}).

Check (@Functor_Category_Terminal (Cq^op) Sets@{ch cso} Sets_Terminal).
Check (@Functor_Category_Cartesian (Cq^op) Sets@{ch cso} Sets_Cartesian).
Check (@Fun_HasPullbacks (Cq^op) Sets@{ch cso} Sets_HasPullbacks).

(* NEGATIVE 6 (FORMABILITY).  Stripped:

     The term "Cq" has type "Category@{co ch ch}"
     while it is expected to have type "Category@{n6.55 n6.56 n6.56}"
     (universe inconsistency: Cannot enforce ch = n6.56 because
      ch < co <= n6.56).                                             *)
Fail Check (Functor_Category_Closed Cq).

(* NEGATIVE 7 (FORMABILITY), with no exponential in the command at all,
   so the two donors are measured independently.  Stripped:

     The term "Cq" has type "Category@{co ch ch}"
     while it is expected to have type "Category@{n7.37 n7.35 n7.35}"
     (universe inconsistency: Cannot enforce ch = n7.35 because
      ch < co <= n7.35).                                             *)
Fail Check (@Fun_Classifier Cq UTq).

End DonorClosed.

(* -------------------------------------------------------------------- *)
(** ** (C) The small reading is blocked, and at the CLOSED field *)

Section SmallReading.
Universes co o so OO HH.
Constraint Set < o.
Constraint o < so.
Constraint so <= OO.
Constraint OO <= HH.
Context (Cs : Category@{co o o}) (UTs : Untruncate@{o}).

(* the four fields that DO fit the lifted reading *)
Check (PShSmall_Terminal Cs : @Terminal (PShSmall Cs)).
Check (@Functor_Category_Cartesian (Cs^op) Sets@{o so} Sets_Cartesian
       : @Cartesian (PShSmall Cs)).
Check (Fun_HasPullbacks Sets_HasPullbacks : @HasPullbacks (PShSmall Cs)).
Check (Fun_Classifier_small Cs UTs
       : @SubobjectClassifier (PShSmall Cs) (PShSmall_Terminal Cs)).

(* NEGATIVE 4 (FORMABILITY).  The fifth does not.  Stripped:

     The term "Functor_Category_Closed Cs" has type
      "@Closed ([Cs^op, Sets])
         (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)"
     while it is expected to have type
      "@Closed (PShSmall Cs)
         (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)"
     (universe inconsistency: Cannot enforce o = n4.97 because
      o < so <= n4.96 <= n4.97).                                     *)
Fail Check (Functor_Category_Closed Cs
            : @Closed (PShSmall Cs)
                (@Functor_Category_Cartesian (Cs^op) Sets@{o so}
                   Sets_Cartesian)).

End SmallReading.

(* ==================================================================== *)
(** ** (D) Setoid negatives *)

(* The [Set]-reach split.  In a section declaring [Set < su], the four
   unconditional donors and the DECIDABLE route all reach the [Sets]
   whose carrier universe is the literal [Set]; the truncation route
   does not. *)

Section SetReach.
Universe su.
Constraint Set < su.

Check Sets@{Set su}.
Check Sets_Terminal@{su Set}.
Check Sets_Cartesian@{su Set}.
Check Sets_HasPullbacks@{su Set}.
Check Sets_Closed@{su Set}.
Check Sets_Classifier_dec@{Set su}.
Check Sets_Topos_dec@{Set su}.

(* NEGATIVE 10 (FORMABILITY).  Stripped:

     Universe inconsistency. Cannot enforce Set < Set because Set = Set. *)
Fail Check Sets_Topos@{Set su}.

(* NEGATIVE 11 (FORMABILITY), the same refusal one layer in, at the
   classifier the bundle carries.  Stripped:

     Universe inconsistency. Cannot enforce Set < Set because Set = Set. *)
Fail Check Sets_Classifier@{Set su}.

End SetReach.

Section SetsNegatives.

Context (U : Untruncate) (a b : obj[Sets]).

(* [Pow] DOES reach this topos: the accepted control for negatives 12
   and 13. *)
Check (@Pow Sets (Sets_Topos U) b).

(* NEGATIVE 12 (FORMABILITY).  [classifier_classifies] carries
   objects <= homs and [Sets@{o so} : Category@{so o o}] has o < so.
   Stripped:

     The term "Sets" has type "Category@{n12.34 n12.33 n12.33}"
     while it is expected to have type "Category@{n12.30 n12.31 n12.31}"
     (universe inconsistency: Cannot enforce n12.34 = n12.30 because
      n12.30 <= n12.31 < n12.34).                                    *)
Fail Check (@classifier_classifies Sets Sets_Terminal Sets_HasPullbacks
              (Sets_Classifier U)).

(* NEGATIVE 13 (FORMABILITY).  So one of Structure/Topos.v's own two
   derived constants is not statable at this genuine topos.  Stripped:

     The term "Sets" has type "Category@{n13.43 n13.42 n13.42}"
     while it is expected to have type "Category@{n13.41 n13.41 n13.41}"
     (universe inconsistency: Cannot enforce n13.43 = n13.41 because
      n13.41 < n13.43).                                              *)
Fail Check (@relations_iso Sets (Sets_Topos U) a b).

End SetsNegatives.

(* The four strict forms of Mac Lane's App.1 clause (b), each refused.
   The apex is a SIGMA carrying the agreement witness, so it is not the
   product carrier and its first projection is not [exl]. *)

(* NEGATIVE 14 (CONVERSION).  Stripped:

     The term "eq_refl" has type "pbone a b = pbone a b"
     while it is expected to have type "pbone a b = a × b"
     (cannot unify "pbone a b" and "a × b").                          *)
Fail Example p404_pbone_prod (a b : obj[Sets]) : pbone a b = a × b := eq_refl.

(* NEGATIVE 15 (CONVERSION), one layer in, at the CARRIERS.  Stripped:

     The term "eq_refl" has type "pbone a b = pbone a b"
     while it is expected to have type "pbone a b = a × b"
     (cannot unify "carrier (pbone a b)" and "carrier (a × b)").      *)
Fail Example p404_pbone_carrier (a b : obj[Sets]) :
  carrier (pbone a b) = carrier (a × b) := eq_refl.

(* NEGATIVE 16 (CONVERSION).  The leg equations hold at the setoid
   relation and not on the nose.  Stripped:

     The term "eq_refl" has type
      "exl ∘ pbone_to_prod a b = exl ∘ pbone_to_prod a b"
     while it is expected to have type
      "exl ∘ pbone_to_prod a b = pbone_fst a b"
     (cannot unify "exl ∘ pbone_to_prod a b" and "pbone_fst a b").    *)
Fail Example p404_pbone_leg (a b : obj[Sets]) :
  exl ∘ pbone_to_prod a b = pbone_fst a b := eq_refl.

(* NEGATIVE 18 (TYPING).  The projection is not [exl]: the two morphisms
   do not share a source, so the mismatch is a plain has-type one, with
   no "cannot unify" and no universe clause.  Stripped:

     The term "exl" has type "a × b ~{ Sets }~> a"
     while it is expected to have type "pbone a b ~{ Sets }~> a".     *)
Fail Example p404_pbone_fst_exl (a b : obj[Sets]) :
  pbone_fst a b = @exl Sets Sets_Cartesian a b := eq_refl.

(* NEGATIVE 17 (CONVERSION).  On the DECIDABLE route the power object is
   the decidable power set, not the [Prop]-valued one.  Its carrier IS
   [SetoidMorphism b BoolSetoid], which is the accepted control in
   Instance/Sets/Topos.v's [app1_pow_dec_carrier].  Stripped:

     The term "eq_refl" has type "Pow b = Pow b"
     while it is expected to have type "Pow b = Powerset_Prop_obj b"
     (cannot unify "Pow b" and "Powerset_Prop_obj b").                *)
Fail Example p404_pow_dec (D : DecImage) (b : obj[Sets]) :
  @Pow Sets (Sets_Topos_dec D) b = Powerset_Prop_obj b := eq_refl.

(* ==================================================================== *)
(** ** (E) The #405 flagships, at BOTH toposes

    All four elaborate at each.  On the presheaf side the five colimit
    legs projected out of [topos_has_finite_colimits] would each be the
    FIRST inhabitant of its class at any functor category in this tree
    (criterion, three sweeps, in Instance/Fun/Topos.v's header); on the
    setoid side all five are SECOND inhabitants, and the existing ones
    are Checked beside them so the TYPES are seen to line up.  NO
    AGREEMENT PROOF IS BUILT and none is claimed. *)

Section PshFlagships.
Context (C : Category) (UT : Untruncate).

Definition psh_Pow (P : C^op ⟶ Sets) :=
  @Pow ([C^op, Sets]) (Presheaf_Topos C UT) P.
Definition psh_monadic :=
  @power_object_monadic ([C^op, Sets]) (Presheaf_Topos C UT).
Definition psh_fincomplete :=
  @topos_finitely_complete ([C^op, Sets]) (Presheaf_Topos C UT).
Definition psh_colimits :=
  @topos_has_finite_colimits ([C^op, Sets]) (Presheaf_Topos C UT).

Definition psh_eq : @HasEqualizers ([C^op, Sets]) :=
  @topos_HasEqualizers ([C^op, Sets]) (Presheaf_Topos C UT).
Definition psh_init : @Initial ([C^op, Sets]) :=
  fst (fst (fst psh_colimits)).
Definition psh_cocart : @Cocartesian ([C^op, Sets]) :=
  snd (fst (fst psh_colimits)).
Definition psh_coeq : @HasCoequalizers ([C^op, Sets]) :=
  snd (fst psh_colimits).
Definition psh_push : @HasPushouts ([C^op, Sets]) := snd psh_colimits.

End PshFlagships.

Section SetsFlagships.
Context (U : Untruncate).

Definition sets_Pow (b : obj[Sets]) := @Pow Sets (Sets_Topos U) b.
Definition sets_monadic := @power_object_monadic Sets (Sets_Topos U).
Definition sets_fincomplete := @topos_finitely_complete Sets (Sets_Topos U).
Definition sets_colimits := @topos_has_finite_colimits Sets (Sets_Topos U).

Definition sets_derived_eq : @HasEqualizers Sets :=
  @topos_HasEqualizers Sets (Sets_Topos U).
Definition sets_derived_init : @Initial Sets := fst (fst (fst sets_colimits)).
Definition sets_derived_cocart : @Cocartesian Sets :=
  snd (fst (fst sets_colimits)).
Definition sets_derived_coeq : @HasCoequalizers Sets :=
  snd (fst sets_colimits).
Definition sets_derived_push : @HasPushouts Sets := snd sets_colimits.

End SetsFlagships.

(* the five pre-existing Sets inhabitants, at the same types *)
Check (Sets_Initial : @Initial Sets).
Check (Sets_Cocartesian : @Cocartesian Sets).
Check (Sets_HasCoequalizers : @HasCoequalizers Sets).
Check (Sets_HasPushouts : @HasPushouts Sets).
Check (Sets_HasEqualizers : @HasEqualizers Sets).

(* ==================================================================== *)
(** ** (F) Non-vacuity

    The presheaf topos at four named shapes -- [_2] being excluded by
    negative 5 -- with three definitional readbacks over them.  NOTHING
    COMPUTES TO A NUMERAL here and none is claimed: sieve membership is
    [Prop]-valued and truncated, so there is no analogue of
    Instance/FinSet/Topos.v's [Pow 2 = 4]. *)

Definition PT_one (UT : Untruncate) := Presheaf_Topos _1 UT.
Definition PT_ord2 (UT : Untruncate) := Presheaf_Topos (Ordinal 2) UT.
Definition PT_par (UT : Untruncate) := Presheaf_Topos Parallel UT.
Definition PT_roof (UT : Untruncate) := Presheaf_Topos Roof UT.

Example PT_one_truth (UT : Untruncate) (c : _1)
  (u : carrier (fobj[@terminal_obj ([_1^op, Sets])
                       (@topos_terminal _ (PT_one UT))] c)) :
  transform[@truth ([_1^op, Sets]) _ (@topos_classifier _ (PT_one UT))] c u
  = @total_sieve _1 c := eq_refl.

Example PT_one_pow (UT : Untruncate) (P : _1^op ⟶ Sets) :
  @Pow ([_1^op, Sets]) (PT_one UT) P = PshExp P (Sieve_Presheaf _1) := eq_refl.

Example PT_par_omega (UT : Untruncate) :
  @Ω ([Parallel^op, Sets]) _ (@topos_classifier _ (PT_par UT))
  = Sieve_Presheaf Parallel := eq_refl.

(* ==================================================================== *)
(** ** (G) Guard block

    Every constant any refutation command above names, Checked OUTSIDE
    every Fail.  Without this a rename would leave the negatives
    vacuously green. *)

Check @classifier_classifies.
Check @relations_iso.
Check @Sub_classifier_natural.
Check @Presheaf_Topos.
Check @Presheaf_Topos_IEM.
Check @Copresheaf_Topos.
Check @Copresheaf_Topos_IEM.
Check @Sets_Topos.
Check @Sets_Topos_dec.
Check @Sets_Topos_IEM.
Check @ElementaryTopos.
Check @topos_terminal.
Check @topos_cartesian.
Check @topos_pullbacks.
Check @topos_closed.
Check @topos_classifier.
Check @Pow.
Check @PShSmall.
Check @PShSmall_Terminal.
Check @Fun_Classifier.
Check @Fun_Classifier_small.
Check @Fun_Classifier_cov.
Check @Functor_Category_Terminal.
Check @Functor_Category_Cartesian.
Check @Functor_Category_Closed.
Check @Functor_Category_Closed_cov.
Check @Fun_HasPullbacks.
Check @Fun_Pullback.
Check @PshExp.
Check @presheaf_terminal.
Check @Sets_Terminal.
Check @Sets_Cartesian.
Check @Sets_HasPullbacks.
Check @Sets_Closed.
Check @Sets_Classifier.
Check @Sets_Classifier_dec.
Check @Sets_Classifier_IEM.
Check @Sets.
Check _1.
Check _2.
Check @Ordinal.
Check @Parallel.
Check @Roof.
Check @OneLevel.Untruncate.
Check @OneLevel.DecImage.
Check @OneLevel.IEM.
Check @Ω.
Check @truth.
Check @char.
Check @Sieve.
Check @Sieve_Presheaf.
Check @sieve_truth.
Check @sieve_restrict.
Check @sieve_mem.
Check @total_sieve.
Check @morphism.
Check @carrier.
Check @fmap.
Check @exl.
Check @exr.
Check @PBONE.
Check @pbone.
Check @pbone_fst.
Check @pbone_snd.
Check @pbone_to_prod.
Check @pbone_from_prod.
Check @pullback_over_one_is_product.
Check @Powerset_Prop_obj.
Check @Powerset_Omega.
Check @Powerset_truth_point.
Check @Powerset_squash.
Check @BoolSetoid.
Check @poly_bool.
Check @SetoidMorphism.
Check @Terminal.
Check @Cartesian.
Check @Closed.
Check @HasPullbacks.
Check @SubobjectClassifier.
Check (@Initial Sets).
Check (@Cocartesian Sets).
Check @HasCoequalizers.
Check @HasPushouts.
Check @HasEqualizers.
Check @topos_HasEqualizers.
Check @topos_finitely_complete.
Check @topos_has_finite_colimits.
Check @power_object_monadic.
Check @app1_char_rule_U.
Check @app1_char_rule_dec.
Check @app1_classifying_square.
Check @app1_classifying_unique.
Check @app1_truth_monic.
Check @psh_op_invol.
