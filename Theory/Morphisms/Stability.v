Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(* Pullback pasting and stability under base change.

   nLab:      https://ncatlab.org/nlab/show/pasting+law+for+pullbacks
              https://ncatlab.org/nlab/show/pullback-stable+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   The bundled [Pullback] record of Structure/Pullback.v packages its apex
   existentially, so it cannot assert that a GIVEN commuting square is a
   pullback.  This file first introduces the apex-pinned predicate
   [IsPullback], with conversions in both directions, and on top of it
   proves:

   - the pasting (composition/cancellation) law for two adjacent squares
     ([pullback_paste] and [pullback_unpaste]): when the right-hand square
     is a pullback, the left-hand square is a pullback exactly when the
     outer rectangle is;

   - monomorphisms are stable under pullback ([monic_pullback_stable]);

   - isomorphisms are stable under pullback ([iso_pullback_stable]);

   - stability of the orthogonal left class under cobase change
     ([ortho_left_cobase_change], at the end of the file, where the
     pushout accessors are in scope);

   - a strengthening of [pullback_unique]: any two pullbacks of one cospan
     are related by an isomorphism of apexes whose triangles with the
     projections commute ([pullback_transport]).  [pullback_unique] is
     Qed-opaque, so the mediators are re-derived here from the universal
     property. *)

(* The apex-pinned pullback predicate: the square

        P ---p2---> y
        |           |
      p1|           |g
        v           v
        x ---f----> z

   commutes and enjoys the universal property of a pullback.  The ∃!-with-∧
   shape below is the Type-valued [Unique] record of Lib/Setoid.v together
   with the Type-valued conjunction, mirroring [ump_pullbacks] in
   Structure/Pullback.v. *)

Record IsPullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z)
       (P : C) (p1 : P ~> x) (p2 : P ~> y) := {
  is_pullback_commutes : f ∘ p1 ≈ g ∘ p2;
  is_pullback_ump : ∀ Q (q1 : Q ~> x) (q2 : Q ~> y), f ∘ q1 ≈ g ∘ q2
    → ∃! u : Q ~> P, p1 ∘ u ≈ q1 ∧ p2 ∘ u ≈ q2
}.

Arguments is_pullback_commutes {C x y z f g P p1 p2} _.
Arguments is_pullback_ump {C x y z f g P p1 p2} _ Q q1 q2 _.

(* Both conversions with the bundled record are field repackagings. *)

Definition pullback_is_pullback {C : Category} {x y z : C}
           (f : x ~> z) (g : y ~> z) (P : Pullback f g) :
  IsPullback f g (Pull f g P) (pullback_fst f g P) (pullback_snd f g P) :=
  {| is_pullback_commutes := pullback_commutes f g P
   ; is_pullback_ump      := ump_pullbacks f g P |}.

Definition is_pullback_pullback {C : Category} {x y z : C}
           {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
           (H : IsPullback f g P p1 p2) : Pullback f g :=
  {| Pull              := P
   ; pullback_fst      := p1
   ; pullback_snd      := p2
   ; pullback_commutes := is_pullback_commutes H
   ; ump_pullbacks     := is_pullback_ump H |}.

(* ------------------------------------------------------------------------ *)
(* The pasting law                                                           *)

(* Two adjacent squares over the composable bottom row a --k--> b --h--> c:

        P ---p2---> Q ---q2---> y
        |           |           |
      p1|         q1|           |m
        v           v           v
        a ----k---> b ----h---> c

   Note: an earlier planning draft transposed the two squares; the statements
   proved below are the standard pasting law, in which the hypothesis that
   the RIGHT-hand square (over the cospan h, m) is a pullback is required in
   BOTH directions. *)

Section Pasting.

Context {C : Category}.
Context {a b c y : C}.
Context {k : a ~> b} {h : b ~> c} {m : y ~> c}.
Context {Q : C} {q1 : Q ~> b} {q2 : Q ~> y}.
Context {P : C} {p1 : P ~> a} {p2 : P ~> Q}.

(* Pasting, outward: if the right-hand square is a pullback and the
   left-hand square is a pullback, then the outer rectangle is a pullback. *)
Lemma pullback_paste
      (HQ : IsPullback h m Q q1 q2)
      (HP : IsPullback k q1 P p1 p2) :
  IsPullback (h ∘ k) m P p1 (q2 ∘ p2).
Proof.
  constructor.
  - (* The outer rectangle commutes. *)
    rewrite <- comp_assoc.
    rewrite (is_pullback_commutes HP).
    rewrite comp_assoc.
    rewrite (is_pullback_commutes HQ).
    rewrite <- comp_assoc.
    reflexivity.
  - intros Q0 r1 r2 Hr.
    (* First mediate into the right-hand square with the cone (k∘r1, r2). *)
    assert (Hr' : h ∘ (k ∘ r1) ≈ m ∘ r2).
    { rewrite comp_assoc.
      exact Hr. }
    pose proof (is_pullback_ump HQ Q0 (k ∘ r1) r2 Hr') as W.
    destruct (unique_property W) as [Wq1 Wq2].
    (* Then mediate into the left-hand square with the cone (r1, w). *)
    assert (Hw : k ∘ r1 ≈ q1 ∘ unique_obj W).
    { symmetry.
      exact Wq1. }
    pose proof (is_pullback_ump HP Q0 r1 (unique_obj W) Hw) as U.
    destruct (unique_property U) as [Up1 Up2].
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * exact Up1.
      * rewrite <- comp_assoc.
        rewrite Up2.
        exact Wq2.
    + intros v [Hv1 Hv2].
      (* p2 ∘ v also mediates the right-hand square, hence agrees with w. *)
      assert (Hvw : unique_obj W ≈ p2 ∘ v).
      { apply (uniqueness W); split.
        - rewrite comp_assoc.
          rewrite <- (is_pullback_commutes HP).
          rewrite <- comp_assoc.
          rewrite Hv1.
          reflexivity.
        - rewrite comp_assoc.
          exact Hv2. }
      apply (uniqueness U); split.
      * exact Hv1.
      * symmetry.
        exact Hvw.
Qed.

(* Pasting, inward: if the right-hand square is a pullback, the left-hand
   square commutes, and the outer rectangle is a pullback, then the
   left-hand square is a pullback.  The left square's commutativity is data
   the outer rectangle cannot recover, so it enters as the hypothesis
   [Hcomm]. *)
Lemma pullback_unpaste
      (HQ : IsPullback h m Q q1 q2)
      (Hcomm : k ∘ p1 ≈ q1 ∘ p2)
      (HO : IsPullback (h ∘ k) m P p1 (q2 ∘ p2)) :
  IsPullback k q1 P p1 p2.
Proof.
  constructor.
  - exact Hcomm.
  - intros Q0 r1 r2 Hr.
    (* (r1, q2 ∘ r2) is a cone over the outer rectangle. *)
    assert (Hout : (h ∘ k) ∘ r1 ≈ m ∘ (q2 ∘ r2)).
    { rewrite <- comp_assoc.
      rewrite Hr.
      rewrite comp_assoc.
      rewrite (is_pullback_commutes HQ).
      rewrite <- comp_assoc.
      reflexivity. }
    pose proof (is_pullback_ump HO Q0 r1 (q2 ∘ r2) Hout) as U.
    destruct (unique_property U) as [Up1 Up2].
    (* Both p2 ∘ u and r2 mediate the right-hand square for the cone
       (k ∘ r1, q2 ∘ r2), so they agree by its uniqueness clause. *)
    assert (Hrq : h ∘ (k ∘ r1) ≈ m ∘ (q2 ∘ r2)).
    { rewrite comp_assoc.
      exact Hout. }
    pose proof (is_pullback_ump HQ Q0 (k ∘ r1) (q2 ∘ r2) Hrq) as W.
    assert (Hp2u : p2 ∘ unique_obj U ≈ r2).
    { transitivity (unique_obj W).
      - symmetry.
        apply (uniqueness W); split.
        + rewrite comp_assoc.
          rewrite <- Hcomm.
          rewrite <- comp_assoc.
          rewrite Up1.
          reflexivity.
        + rewrite comp_assoc.
          exact Up2.
      - apply (uniqueness W); split.
        + symmetry.
          exact Hr.
        + reflexivity. }
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * exact Up1.
      * exact Hp2u.
    + intros v [Hv1 Hv2].
      apply (uniqueness U); split.
      * exact Hv1.
      * rewrite <- comp_assoc.
        rewrite Hv2.
        reflexivity.
Qed.

End Pasting.

(* ------------------------------------------------------------------------ *)
(* Stability under base change                                               *)

(* Monomorphisms are stable under pullback: in the square

        P ---snd--> y
        |           |
     fst|           |m
        v           v
        x ----f---> z

   with m monic, the projection opposite m is monic as well. *)
Lemma monic_pullback_stable {C : Category} {x y z : C}
      (f : x ~> z) (m : y ~> z) (Hm : Monic m) (P : Pullback f m) :
  Monic (pullback_fst f m P).
Proof.
  destruct Hm as [mono].
  constructor.
  intros w g1 g2 Heq.
  (* m cancels on the other projection. *)
  assert (Hsnd : pullback_snd f m P ∘ g1 ≈ pullback_snd f m P ∘ g2).
  { apply mono.
    rewrite !comp_assoc.
    rewrite <- (pullback_commutes f m P).
    rewrite <- !comp_assoc.
    rewrite Heq.
    reflexivity. }
  (* Both g1 and g2 mediate the cone (fst ∘ g1, snd ∘ g1). *)
  assert (Hcone : f ∘ (pullback_fst f m P ∘ g1)
                    ≈ m ∘ (pullback_snd f m P ∘ g1)).
  { rewrite !comp_assoc.
    rewrite (pullback_commutes f m P).
    reflexivity. }
  pose proof (ump_pullbacks f m P w (pullback_fst f m P ∘ g1)
                            (pullback_snd f m P ∘ g1) Hcone) as U.
  transitivity (unique_obj U).
  - symmetry.
    apply (uniqueness U); split.
    + reflexivity.
    + reflexivity.
  - apply (uniqueness U); split.
    + symmetry.
      exact Heq.
    + symmetry.
      exact Hsnd.
Qed.

(* Isomorphisms are stable under pullback: pulling an isomorphism m back
   along f yields an isomorphism.  The inverse is the mediator of the cone
   (id, m⁻¹ ∘ f). *)
Lemma iso_pullback_stable {C : Category} {x y z : C}
      (f : x ~> z) (m : y ~> z) (Hm : IsIsomorphism m) (P : Pullback f m) :
  IsIsomorphism (pullback_fst f m P).
Proof.
  destruct Hm as [g Hmg Hgm].
  assert (Hcone : f ∘ id ≈ m ∘ (g ∘ f)).
  { rewrite id_right.
    rewrite comp_assoc.
    rewrite Hmg.
    rewrite id_left.
    reflexivity. }
  pose proof (ump_pullbacks f m P x id (g ∘ f) Hcone) as U.
  destruct (unique_property U) as [Ufst Usnd].
  (* u ∘ fst mediates the cone (fst, snd) into the pullback itself, and so
     does id; uniqueness identifies them. *)
  pose proof (ump_pullbacks f m P (Pull f m P)
                            (pullback_fst f m P) (pullback_snd f m P)
                            (pullback_commutes f m P)) as UU.
  assert (Hleft : unique_obj U ∘ pullback_fst f m P ≈ id).
  { transitivity (unique_obj UU).
    - symmetry.
      apply (uniqueness UU); split.
      + rewrite comp_assoc.
        rewrite Ufst.
        rewrite id_left.
        reflexivity.
      + rewrite comp_assoc.
        rewrite Usnd.
        rewrite <- comp_assoc.
        rewrite (pullback_commutes f m P).
        rewrite comp_assoc.
        rewrite Hgm.
        rewrite id_left.
        reflexivity.
    - apply (uniqueness UU); split.
      + apply id_right.
      + apply id_right. }
  exact {| two_sided_inverse := unique_obj U
         ; is_right_inverse  := Ufst
         ; is_left_inverse   := Hleft |}.
Qed.

(* ------------------------------------------------------------------------ *)
(* Transport between two pullbacks of one cospan                             *)

(* [pullback_unique] in Structure/Pullback.v produces an isomorphism of
   apexes but keeps its triangles hidden behind Qed; the record below
   carries them explicitly. *)

Record PullbackTransport {C : Category} {x y z : C} {f : x ~> z} {g : y ~> z}
       (P P' : Pullback f g) := {
  transport_iso : Pull f g P ≅ Pull f g P';
  transport_fst : pullback_fst f g P' ∘ to transport_iso
                    ≈ pullback_fst f g P;
  transport_snd : pullback_snd f g P' ∘ to transport_iso
                    ≈ pullback_snd f g P
}.

Arguments transport_iso {C x y z f g P P'} _.
Arguments transport_fst {C x y z f g P P'} _.
Arguments transport_snd {C x y z f g P P'} _.

(* Any two pullbacks of one cospan are isomorphic via mediators that commute
   with the projections; the round trips reduce to id by the uniqueness
   clause applied to each pullback's self-mediator. *)
Lemma pullback_transport {C : Category} {x y z : C} {f : x ~> z} {g : y ~> z}
      (P P' : Pullback f g) : PullbackTransport P P'.
Proof.
  pose proof (ump_pullbacks f g P' _ (pullback_fst f g P) (pullback_snd f g P)
                            (pullback_commutes f g P)) as HT.
  pose proof (ump_pullbacks f g P _ (pullback_fst f g P') (pullback_snd f g P')
                            (pullback_commutes f g P')) as HF.
  pose proof (ump_pullbacks f g P _ (pullback_fst f g P) (pullback_snd f g P)
                            (pullback_commutes f g P)) as HPP.
  pose proof (ump_pullbacks f g P' _ (pullback_fst f g P') (pullback_snd f g P')
                            (pullback_commutes f g P')) as HQQ.
  destruct (unique_property HT) as [HTfst HTsnd].
  destruct (unique_property HF) as [HFfst HFsnd].
  unshelve refine
    {| transport_iso := {| to := unique_obj HT; from := unique_obj HF |} |}.
  - (* to ∘ from ≈ id, against the self-mediator of P' *)
    transitivity (unique_obj HQQ).
    + symmetry.
      apply (uniqueness HQQ); split.
      * rewrite comp_assoc.
        rewrite HTfst.
        exact HFfst.
      * rewrite comp_assoc.
        rewrite HTsnd.
        exact HFsnd.
    + apply (uniqueness HQQ); split.
      * apply id_right.
      * apply id_right.
  - (* from ∘ to ≈ id, against the self-mediator of P *)
    transitivity (unique_obj HPP).
    + symmetry.
      apply (uniqueness HPP); split.
      * rewrite comp_assoc.
        rewrite HFfst.
        exact HTfst.
      * rewrite comp_assoc.
        rewrite HFsnd.
        exact HTsnd.
    + apply (uniqueness HPP); split.
      * apply id_right.
      * apply id_right.
  - exact HTfst.
  - exact HTsnd.
Qed.

(* Stability of the orthogonal left class under cobase change.

   nLab: https://ncatlab.org/nlab/show/orthogonal+factorization+system

   If e ⫫ m and e' is a pushout of e along any morphism g (the cobase
   change of e), then e' ⫫ m as well.  With the span [b <-e- a -g-> a'] and
   the pushout square

       a --g--> a'
       |        |
      e|        | pushout_in2
       v        v
       b -----> apex ,
          in1

   a lifting square (u, v) over [pushout_in2] transports to one over [e],
   whose unique filler [d] then combines with [u] into a cocone under the
   span; the pushout mediator is the required filler, and both mediator
   uniqueness principles combine to give its uniqueness.  This discharges
   the pointer at the end of Theory/Orthogonality.v's closure-property
   list. *)

Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Pushout.

Lemma ortho_left_cobase_change {C : Category}
      {a b a' x y : C} (e : a ~> b) (g : a ~> a')
      (P : IsPushout e g) (m : x ~> y) :
  e ⫫ m → pushout_in2 P ⫫ m.
Proof.
  intros He.
  constructor.
  intros u v comm.
  (* the transported lifting square over e *)
  assert (comm_e : m ∘ (u ∘ g) ≈ (v ∘ pushout_in1 P) ∘ e).
  { rewrite comp_assoc.
    rewrite comm.
    rewrite <- !comp_assoc.
    now rewrite (pushout_commutes P). }
  pose (D := @ortho_lift _ _ _ _ _ e m He (u ∘ g) (v ∘ pushout_in1 P) comm_e).
  destruct (unique_property D) as [T1 T2].
  unshelve refine {| unique_obj := pushout_med P T1 |}.
  - split.
    + apply pushout_med_in2.
    + (* m ∘ mediator ≈ v, on both pushout legs *)
      assert (Hvc : (v ∘ pushout_in1 P) ∘ e ≈ (v ∘ pushout_in2 P) ∘ g).
      { rewrite <- !comp_assoc.
        now rewrite (pushout_commutes P). }
      apply (pushout_med_eq P Hvc).
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in1 P T1).
        exact T2.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in2 P T1).
        exact comm.
      * reflexivity.
      * reflexivity.
  - (* uniqueness: any filler agrees with the mediator on both legs *)
    intros v0 Hv0.
    destruct Hv0 as [W1 W2].
    assert (F1 : (v0 ∘ pushout_in1 P) ∘ e ≈ u ∘ g).
    { rewrite <- comp_assoc.
      rewrite (pushout_commutes P).
      rewrite comp_assoc.
      now rewrite W1. }
    assert (F2 : m ∘ (v0 ∘ pushout_in1 P) ≈ v ∘ pushout_in1 P).
    { rewrite comp_assoc.
      now rewrite W2. }
    assert (Hd : unique_obj D ≈ v0 ∘ pushout_in1 P).
    { apply (uniqueness D).
      split.
      - exact F1.
      - exact F2. }
    apply (pushout_med_eq P T1).
    + apply (pushout_med_in1 P T1).
    + apply (pushout_med_in2 P T1).
    + symmetry.
      exact Hd.
    + exact W1.
Qed.
