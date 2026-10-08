(** * Probe for quotients as coequalizers split under U (issue #479)

    Pins the measured boundaries of Instance/Grp/Coequalizer.v and
    Instance/Rng/Coequalizer.v (Mac Lane, §VI.6, book p. 150, PDF p. 159,
    items maclane:VI.6:remark2 and maclane:VI.6:ex1, read from the page
    image: "if we apply the standard forgetful functor U: Grp→Set, the
    resulting fork in Set is split") and of Instance/Mon/Presentation.v
    (Awodey, 2005 pre-print, §3.4 Proposition 3.22 and §3.5 Exercise 3,
    items awodey:3.4:prop22 and awodey:3:ex3).  Donors named by a
    refusal: Instance/Grp/TwoFunctors.v ([S3], R3) and Instance/Mon/
    Free.v (the free functor's action on arrows, R5); by a control:
    Instance/Sets/Propositional/Full.v ([choice_of_untr] and
    [untr_of_choice], C19 and C20).

    THE IMPORT LIST, checked by a script over the [Require] lines.
    Target by target in dependency order: the fifteen lines of
    Instance/Grp/Coequalizer.v and that target; the nine lines
    Instance/Rng/Coequalizer.v adds and that target; the thirteen lines
    Instance/Mon/Presentation.v adds and that target: forty lines.  A
    shorter list is what makes a probe pass for no reason.

    DISCIPLINE.  Every negative other than the instrument is an
    [Example] or a [Definition], never a [Check].  Each of the seven
    refutation lines (the instrument and R1 to R6) was stripped of its
    refutation keyword in a copy of this WHOLE file, one at a time, and
    each copy stops inside the stripped command (seven of seven, by
    loop-tools' swcheck.py, comparing the File line of the error with the
    command's extent); each of the twenty controls, wrapped in the
    keyword in a whole-file copy, stops at that command with the message
    Rocq prints for a refutation whose command succeeds (twenty of
    twenty, by the same script).  Quotations are Rocq 9.1.1's under
    this file's import list, the environment block left out and
    universe serials written u0, u1, ..., distinct serials distinctly.

    KINDS.  NAME-ABSENCE: the instrument.  CONVERSION, [eq_refl] refused
    with a "cannot unify" parenthetical, every statement well typed: R1,
    R4, R5.  UNIVERSE, "universe inconsistency" between levels this file
    declares: R2, R3, R6.  CAUSES, read from the terms.  R1 and R4 are
    law 4 of the splitting after U, ∂₁ (t x) against s (p x), equal at
    ≈ (C1, C8) by a group or ring law of a variable G or R.  R5 is the
    free functor's action on arrows at a variable word of words, equal
    at ≈ (C12) and read through universal arrows, where the counit
    computes (C11).  R2 and R6 are ∂₀ at a membership level m above the
    carrier level p: an element of G ×₀ N carries a membership witness,
    and the pair lives in [Grp@{_ p}] (resp. [Rng@{_ p}]), while G ×₀ N
    as a group and a transversal's untruncation are formable there (C14,
    C5; C16, C15).  Below the carrier the readbacks of the pair are
    accepted (C17, C18): their binders keep N's membership level apart
    from the carrier level, which bare binders, left to minimization,
    identified.  R3 is S₃'s own pin, Instance/Grp/TwoFunctors.v's
    [S3@{u} : GrpObject@{u Set Set}]: the S₃/A₃ splitting is refused in
    [Grp@{u p}] above [Set], where the Z/4 refutation is accepted (C6);
    at [Set] it is accepted (C7).  C19 and C20 put the untruncation
    principle at the membership level m, written out as Full.v writes
    Instance/Sets/Classifier/OneLevel.v's [Untruncate@{m}], against the
    untruncation of the coset relation of every N at that level: Full.v's
    [choice_of_untr] composed with [choice_untruncates] one way, and
    [NS_untruncates_chooses] composed with [untr_of_choice] the other.

    LABELS.  Each refutation and control carries its label in a comment
    on the line above it; the constants are [p479_cN_…] and [p479_rN_…].

    RESTATEMENTS.  C4 is [transversal_round_trip], C9 [rsdp_mul_snd],
    C10 [EvenIdeal_transversal_fun], C11 [Mon_flatten_fun] and C13
    [Mon_canonical_split_s]; C17 and C18 are [transversal_split_e] and
    [rtransversal_split_e] at a membership level below the carrier.  C2
    and C3 are two readbacks the files do not state: t's second
    component with p x reduced to x, and the descent's underlying map,
    h's own, both at [eq_refl].

    THE REFUSALS, with the message each stripped copy prints.
      The instrument: The reference p479_absent_name was not found in
        the current environment.
      R1: (cannot unify "semidirect_d1 N (scoeq_t (transversal_split N
        T) x)" and "transversal_map T x").
      R2: The term "N" has type "NormalSubgroup@{m p p p} G" while it is
        expected to have type "NormalSubgroup@{u0 u1 u1 u1} ?G"
        (universe inconsistency: Cannot enforce m = u0 because
        u0 <= u1 < m).
      R3: The term "semidirect_d0 A3" has type "SemidirectGrp@{…}
        A3@{u0 Set} ~{ Grp@{u1 Set} }~> S3@{Set}" while it is
        expected to have type "?x ~{ Grp@{u p} }~> ?y" (universe
        inconsistency: Cannot enforce Set = p).
      R4: (cannot unify "rsemidirect_d1 A (scoeq_t (rtransversal_split A
        T) r)" and "rtransversal_map T r").
      R5: (cannot unify "mon_fun (Mon_free_evaluate M) ww" and "wmap (λ w
        : mon_ob (fobj[FreeMonSets] (fobj[Mon_Forget] M)), mon_fun
        (Mon_evaluate M) w) ww").
      R6: The term "A" has type "Ideal@{m p p p} R" while it is expected
        to have type "Ideal@{u0 u1 u1 u1} ?R" (universe inconsistency:
        Cannot enforce m = u0 because u0 <= u1 < m).
    In R2 and R6 the two serials are distinct: the expected type is ∂₀'s
    binder, membership u0 at or below carrier u1, the bound the two
    refusals pin; written as one u it would read as an identification. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Coequalizer.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Instance.Rng.Coequalizer.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Mon.Word.
Require Import Category.Instance.Mon.Presentation.

Generalizable All Variables.

(* The instrument *)
Fail Definition p479_instrument : True := p479_absent_name.

(** ** Groups *)

Section GrpProbe.

Universe p.
Context {G : GrpObject@{p p p}} (N : NormalSubgroup G).
Context (T : Transversal N) (x : carrier G).

(* R1 *)
Fail Example p479_r1_law4 :
  grp_map (semidirect_d1 N) (scoeq_t (transversal_split N T) x)
    = transversal_map T x := eq_refl.

(* C1 *)
Example p479_c1_law4 :
  grp_map (semidirect_d1 N) (scoeq_t (transversal_split N T) x)
    ≈ transversal_map T x.
Proof. exact (scoeq_law4 (transversal_split N T) x). Qed.

(* C2 *)
Example p479_c2_t_snd :
  `1 (snd (scoeq_t (transversal_split N T) x))
    = grp_mul G (grp_inv G x) (transversal_map T x) := eq_refl.

(* C3 *)
Example p479_c3_desc {K : GrpObject@{p p p}} (h : G ~{Grp}~> K)
  (Hh : h ∘ semidirect_d0 N ≈ h ∘ semidirect_d1 N) (a : carrier G) :
  grp_map (unique_obj (coeq_desc (quot_proj_IsCoequalizer N) h Hh)) a
    = grp_map h a := eq_refl.

(* C4 *)
Example p479_c4_round_trip (a : carrier G) :
  transversal_map (split_transversal N (transversal_split N T)) a
    = transversal_map T a := eq_refl.

End GrpProbe.

(* Membership above the carrier: the pair is refused there; G ×₀ N is
   formable as a group, and a transversal still untruncates. *)
Section GrpMembershipAbove.

Universes p m.
Constraint p < m.
Context {G : GrpObject@{p p p}} (N : NormalSubgroup@{m p p p} G).

(* R2 *)
Fail Definition p479_r2_pair := semidirect_d0 N.

(* C5 *)
Definition p479_c5_transversal (T : Transversal N) : CosetUntruncates N :=
  transversal_untruncates N T.

(* C14 *)
Definition p479_c14_sdp : GrpObject := SemidirectGrp N.

End GrpMembershipAbove.

(* Carriers above Set: Z/4's refutation is accepted there, the S3/A3
   splitting is refused. *)
Section AboveSet.

Universes u p.
Constraint Set < p.
Constraint p < u.

(* C6 *)
Definition p479_c6_Z4 :
  @SplitCoequalizer Grp@{u p} _ _ (semidirect_d0 Z4_two)
    (semidirect_d1 Z4_two) → False := Z4_two_not_split_in_Grp.

(* R3 *)
Fail Definition p479_r3_S3 :
  @SplitCoequalizer Grp@{u p} _ _ (semidirect_d0 A3) (semidirect_d1 A3)
  := S3_A3_Grp_split.

End AboveSet.

(* C7 *)
Definition p479_c7_S3 :
  SplitCoequalizer (semidirect_d0 A3) (semidirect_d1 A3) := S3_A3_Grp_split.

(** ** Rings *)

Section RngProbe.

Universe p.
Context {R : RingObject@{p p p}} (A : Ideal R).
Context (T : RTransversal A) (r : carrier (rig_setoid R)).

(* R4 *)
Fail Example p479_r4_law4 :
  rig_map (rsemidirect_d1 A) (scoeq_t (rtransversal_split A T) r)
    = rtransversal_map T r := eq_refl.

(* C8 *)
Example p479_c8_law4 :
  rig_map (rsemidirect_d1 A) (scoeq_t (rtransversal_split A T) r)
    ≈ rtransversal_map T r.
Proof. exact (scoeq_law4 (rtransversal_split A T) r). Qed.

(* C9 *)
Example p479_c9_mul_snd (q q' : carrier (rig_setoid (SemidirectRing A))) :
  `1 (snd (rig_mul (SemidirectRing A) q q'))
    = rig_add R (rig_add R (rig_mul R (fst q) (`1 (snd q')))
                           (rig_mul R (`1 (snd q)) (fst q')))
                (rig_mul R (`1 (snd q)) (`1 (snd q'))) := eq_refl.

End RngProbe.

Section RngMembershipAbove.

Universes p m.
Constraint p < m.
Context {R : RingObject@{p p p}} (A : Ideal@{m p p p} R).

(* R6 *)
Fail Definition p479_r6_pair := rsemidirect_d0 A.

(* C15 *)
Definition p479_c15_transversal (T : RTransversal A) : RCosetUntruncates A :=
  rtransversal_untruncates A T.

(* C16 *)
Definition p479_c16_sdp : RingObject := SemidirectRing A.

End RngMembershipAbove.

(* C10 *)
Example p479_c10_even (a : Z) :
  rtransversal_map EvenIdeal_transversal a = Z.modulo a 2 := eq_refl.

(* Membership below the carrier: the readbacks of the pair are accepted
   there, and the untruncation principle at the membership level is
   OneLevel.v's [Untruncate] at that level, against every N. *)
Section MembershipBelow.

Universes p m.
Constraint m < p.

(* C17 *)
Definition p479_c17_readback {G : GrpObject@{p p p}}
  (N : NormalSubgroup@{m p p p} G) (T : Transversal N) :=
  transversal_split_e T.

(* C18 *)
Definition p479_c18_rreadback {R : RingObject@{p p p}}
  (A : Ideal@{m p p p} R) (T : RTransversal A) :=
  rtransversal_split_e T.

(* C19 *)
Definition p479_c19_untruncate {G : GrpObject@{p p p}}
  (N : NormalSubgroup@{m p p p} G)
  (U : ∀ P : Type@{m}, (∀ Q : Prop, (P → Q) → Q) → P) :
  CosetUntruncates N := choice_untruncates N (choice_of_untr U).

(* C20 *)
Definition p479_c20_untruncate
  (D : ∀ S : Type@{m}, CosetUntruncates (NS S)) :
  ∀ P : Type@{m}, (∀ Q : Prop, (P → Q) → Q) → P :=
  untr_of_choice (fun S => NS_untruncates_chooses S (D S)).

End MembershipBelow.

(** ** Monoids *)

Section MonProbe.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

Context (M : MonOS) (ww : list (list (mon_ob M))).

(* C11 *)
Example p479_c11_flatten :
  mon_fun (Mon_flatten M) ww = wconcat ww := eq_refl.

(* R5 *)
Fail Example p479_r5_evaluate :
  mon_fun (Mon_free_evaluate M) ww
    = wmap (fun w => mon_fun (Mon_evaluate M) w) ww := eq_refl.

(* C12 *)
Example p479_c12_evaluate :
  mon_fun (Mon_free_evaluate M) ww
    ≈ wmap (fun w => mon_fun (Mon_evaluate M) w) ww.
Proof.
  exact (free_mon_fmap_is_wmap (fmap[Mon_Forget] (Mon_evaluate M)) ww).
Qed.

(* C13 *)
Example p479_c13_s :
  scoeq_s (Mon_canonical_split M) = free_mon_insert (Mon_Forget M) := eq_refl.

End MonProbe.
