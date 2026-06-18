Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(** * The span category *)

(* nLab:      https://ncatlab.org/nlab/show/span
   Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory)

   A span in [C] from [X] to [Y] is a diagram [X <-leg1- N -leg2-> Y], i.e. an
   apex [N] with two legs.  In library notation:

     Objects:          the objects of [C].
     Morphisms X ~> Y: spans [X <-leg1- N -leg2-> Y], with apex [N].
     Equivalence ≈:    two spans are equivalent (span_equiv) if their apexes
                       are connected by an isomorphism respecting both legs.
     Composition:      given [X <- N -> Y] and [Y <- M -> Z], the composite is
                       the PULLBACK span [X <- N ×_Y M -> Z]; this needs [C] to
                       have pullbacks ([HasPullbacks]).
     Identity:         the span [X <-id- X -id-> X].

   Bicategory vs. category.  With spans taken literally as morphisms, pullbacks
   are determined only up to canonical isomorphism, so associativity and the
   unit laws hold only UP TO ISOMORPHISM of apexes; Span(C) is therefore in
   general a bicategory, not a strict 1-category.  Here we obtain an honest
   1-category ([SpanCat]) by the standard device of quotienting by that
   isomorphism: the hom-setoid equality [≈] is [span_equiv] (isomorphism of
   apexes respecting the legs).  Relative to that [≈] the unit and associativity
   laws hold strictly, which is exactly the nLab/Wikipedia prescription of
   taking iso-classes of spans to recover a 1-category.

   Related: a span generalises a binary relation [X <- R -> Y], so Span(Set)
   subsumes Rel; if [C] has finite products then Span(C) carries a (symmetric,
   in fact dagger compact) monoidal structure — neither is developed here.

   This file is the primary construction.  The dual file
   [Construction.Cospan.Category] is an independent mirror using pushouts in [C]
   directly (rather than pullbacks in [C^op]); it does not wrap [SpanCat]. *)

Section SpanCategory.

Context {C : Category}.

(** A span from [X] to [Y]: an apex [N] together with two legs from the
    apex into [X] and [Y]. *)
Record SpanArrow (X Y : C) : Type := {
  apex : C;
  leg1 : apex ~> X;
  leg2 : apex ~> Y
}.

Arguments apex {X Y} _.
Arguments leg1 {X Y} _.
Arguments leg2 {X Y} _.

(** Two spans are equivalent if there is an isomorphism of apexes whose
    composite (in either direction) with the corresponding legs agrees.

    Convention: we require [leg1 g ∘ to phi ≈ leg1 f] (the iso intertwines
    the legs from the LHS apex to the RHS apex). *)
Definition span_equiv {X Y : C} (f g : SpanArrow X Y) : Type :=
  { phi : apex f ≅ apex g
    & ((leg1 g ∘ to phi ≈ leg1 f) * (leg2 g ∘ to phi ≈ leg2 f))%type }.

Lemma span_equiv_refl {X Y : C} (f : SpanArrow X Y) :
  span_equiv f f.
Proof.
  exists iso_id; simpl; split; cat.
Defined.

Lemma span_equiv_sym {X Y : C} (f g : SpanArrow X Y) :
  span_equiv f g -> span_equiv g f.
Proof.
  intros [phi [H1 H2]].
  exists (iso_sym phi); simpl; split.
  - rewrite <- H1.
    rewrite <- comp_assoc.
    rewrite iso_to_from; cat.
  - rewrite <- H2.
    rewrite <- comp_assoc.
    rewrite iso_to_from; cat.
Defined.

Lemma span_equiv_trans {X Y : C} (f g h : SpanArrow X Y) :
  span_equiv f g -> span_equiv g h -> span_equiv f h.
Proof.
  intros [phi [H1 H2]] [psi [K1 K2]].
  exists (iso_compose psi phi); simpl; split.
  - rewrite comp_assoc, K1; exact H1.
  - rewrite comp_assoc, K2; exact H2.
Defined.

#[export] Program Instance SpanArrow_Setoid {X Y : C} :
  Setoid (SpanArrow X Y) := {|
  equiv := fun f g => span_equiv f g
|}.
Next Obligation.
  constructor.
  - intros f; apply span_equiv_refl.
  - intros f g; apply span_equiv_sym.
  - intros f g h; apply span_equiv_trans.
Defined.

(** Identity span on [X]: apex is [X], both legs are identity. *)
Definition span_id (X : C) : SpanArrow X X :=
  {| apex := X; leg1 := id[X]; leg2 := id[X] |}.

Variable HP : HasPullbacks C.

(** Composition of spans via pullback.

    Given [f : X ~> Y] with apex [N] and legs [l1f : N ~> X], [l2f : N ~> Y],
    and [g : Y ~> Z] with apex [M] and legs [l1g : M ~> Y], [l2g : M ~> Z],
    the pullback of the cospan [N -l2f-> Y <-l1g- M] gives an apex [P]
    with [pi1 : P ~> N], [pi2 : P ~> M].  The composite span has apex [P],
    [leg1 := l1f ∘ pi1] and [leg2 := l2g ∘ pi2]. *)
Definition span_compose
           {X Y Z : C}
           (g : SpanArrow Y Z) (f : SpanArrow X Y)
  : SpanArrow X Z :=
  let P := pullback (leg2 f) (leg1 g) in
  {| apex := Pull _ _ P;
     leg1 := leg1 f ∘ pullback_fst _ _ P;
     leg2 := leg2 g ∘ pullback_snd _ _ P |}.

(** ** Pullback-pasting helpers *)

(** The mediating morphism into a pullback. *)
Definition pullback_med {x y z : C} {f : x ~> z} {g : y ~> z}
           (P : Pullback f g)
           {Q : C} {q1 : Q ~> x} {q2 : Q ~> y}
           (Hcomm : f ∘ q1 ≈ g ∘ q2)
  : Q ~> Pull _ _ P :=
  unique_obj (ump_pullbacks _ _ P Q q1 q2 Hcomm).

Lemma pullback_med_fst {x y z : C} {f : x ~> z} {g : y ~> z}
      (P : Pullback f g)
      {Q : C} {q1 : Q ~> x} {q2 : Q ~> y}
      (Hcomm : f ∘ q1 ≈ g ∘ q2) :
  pullback_fst _ _ P ∘ pullback_med P Hcomm ≈ q1.
Proof.
  unfold pullback_med.
  destruct (unique_property (ump_pullbacks _ _ P Q q1 q2 Hcomm)) as [H _].
  exact H.
Qed.

Lemma pullback_med_snd {x y z : C} {f : x ~> z} {g : y ~> z}
      (P : Pullback f g)
      {Q : C} {q1 : Q ~> x} {q2 : Q ~> y}
      (Hcomm : f ∘ q1 ≈ g ∘ q2) :
  pullback_snd _ _ P ∘ pullback_med P Hcomm ≈ q2.
Proof.
  unfold pullback_med.
  destruct (unique_property (ump_pullbacks _ _ P Q q1 q2 Hcomm)) as [_ H].
  exact H.
Qed.

Lemma pullback_med_unique {x y z : C} {f : x ~> z} {g : y ~> z}
      (P : Pullback f g)
      {Q : C} {q1 : Q ~> x} {q2 : Q ~> y}
      (Hcomm : f ∘ q1 ≈ g ∘ q2)
      (v : Q ~> Pull _ _ P) :
  pullback_fst _ _ P ∘ v ≈ q1 ->
  pullback_snd _ _ P ∘ v ≈ q2 ->
  pullback_med P Hcomm ≈ v.
Proof.
  intros H1 H2.
  unfold pullback_med.
  apply (uniqueness (ump_pullbacks _ _ P Q q1 q2 Hcomm)); split; assumption.
Qed.

Lemma pullback_med_eq {x y z : C} {f : x ~> z} {g : y ~> z}
      (P : Pullback f g) {Q : C} {q1 : Q ~> x} {q2 : Q ~> y}
      (Hcomm : f ∘ q1 ≈ g ∘ q2)
      (u v : Q ~> Pull _ _ P) :
  pullback_fst _ _ P ∘ u ≈ q1 ->
  pullback_snd _ _ P ∘ u ≈ q2 ->
  pullback_fst _ _ P ∘ v ≈ q1 ->
  pullback_snd _ _ P ∘ v ≈ q2 ->
  u ≈ v.
Proof.
  intros Hu1 Hu2 Hv1 Hv2.
  transitivity (pullback_med P Hcomm).
  - symmetry. apply pullback_med_unique; assumption.
  - apply pullback_med_unique; assumption.
Qed.

(** ** Proper instance for composition (the pullback-pasting lemma) *)

Lemma span_compose_respects_aux
      {X Y Z : C}
      (g g' : SpanArrow Y Z) (f f' : SpanArrow X Y)
      (Hf : span_equiv f f') (Hg : span_equiv g g') :
  span_equiv (span_compose g f) (span_compose g' f').
Proof.
  destruct Hf as [phi [Hf1 Hf2]].
  destruct Hg as [psi [Hg1 Hg2]].
  unfold span_compose; simpl.
  pose (P  := pullback (leg2 f)  (leg1 g)).
  pose (P' := pullback (leg2 f') (leg1 g')).
  (* Mediator P -> P'.  Build a cocone (in the pullback sense) into P' from
     P, using legs (to phi ∘ pullback_fst P) and (to psi ∘ pullback_snd P).
     They satisfy
        leg2 f' ∘ (to phi ∘ pullback_fst P)
       = (leg2 f' ∘ to phi) ∘ pullback_fst P
       = leg2 f ∘ pullback_fst P                 (from Hf2 inverted)
       = leg1 g ∘ pullback_snd P                 (pullback commutes)
       = (leg1 g' ∘ to psi)? — we need leg1 g' ∘ (to psi ∘ pullback_snd P).
       Since leg1 g' ∘ to psi ≈ leg1 g, the equality holds. *)
  assert (Hcomm : leg2 f' ∘ (to phi ∘ pullback_fst _ _ P)
                  ≈ leg1 g' ∘ (to psi ∘ pullback_snd _ _ P)).
  { rewrite !comp_assoc.
    rewrite Hf2, Hg1.
    apply (pullback_commutes _ _ P). }
  set (u := pullback_med P' Hcomm).
  assert (Hu1 : pullback_fst _ _ P' ∘ u ≈ to phi ∘ pullback_fst _ _ P)
    by (apply pullback_med_fst).
  assert (Hu2 : pullback_snd _ _ P' ∘ u ≈ to psi ∘ pullback_snd _ _ P)
    by (apply pullback_med_snd).
  (* Mediator P' -> P. *)
  assert (Hcomm' : leg2 f ∘ (from phi ∘ pullback_fst _ _ P')
                  ≈ leg1 g ∘ (from psi ∘ pullback_snd _ _ P')).
  { assert (Hf2' : leg2 f ∘ from phi ≈ leg2 f').
    { rewrite <- Hf2.
      rewrite <- comp_assoc, iso_to_from; cat. }
    assert (Hg1' : leg1 g ∘ from psi ≈ leg1 g').
    { rewrite <- Hg1.
      rewrite <- comp_assoc, iso_to_from; cat. }
    rewrite !comp_assoc.
    rewrite Hf2', Hg1'.
    apply (pullback_commutes _ _ P'). }
  set (v := pullback_med P Hcomm').
  assert (Hv1 : pullback_fst _ _ P ∘ v ≈ from phi ∘ pullback_fst _ _ P')
    by (apply pullback_med_fst).
  assert (Hv2 : pullback_snd _ _ P ∘ v ≈ from psi ∘ pullback_snd _ _ P')
    by (apply pullback_med_snd).
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := u; from := v |}.
    + (* u ∘ v ≈ id on apex P'.  *)
      apply (pullback_med_eq P' (pullback_commutes _ _ P')
              (u ∘ v) id).
      * rewrite comp_assoc, Hu1.
        rewrite <- comp_assoc, Hv1.
        rewrite comp_assoc, iso_to_from; cat.
      * rewrite comp_assoc, Hu2.
        rewrite <- comp_assoc, Hv2.
        rewrite comp_assoc, iso_to_from; cat.
      * cat.
      * cat.
    + (* v ∘ u ≈ id on apex P. *)
      apply (pullback_med_eq P (pullback_commutes _ _ P)
              (v ∘ u) id).
      * rewrite comp_assoc, Hv1.
        rewrite <- comp_assoc, Hu1.
        rewrite comp_assoc, iso_from_to; cat.
      * rewrite comp_assoc, Hv2.
        rewrite <- comp_assoc, Hu2.
        rewrite comp_assoc, iso_from_to; cat.
      * cat.
      * cat.
  - simpl; split.
    + (* leg1 f' ∘ (pullback_fst P' ∘ u) ≈ leg1 f ∘ pullback_fst P. *)
      change ((leg1 f' ∘ pullback_fst _ _ P') ∘ u ≈ leg1 f ∘ pullback_fst _ _ P).
      rewrite <- comp_assoc, Hu1.
      rewrite comp_assoc, Hf1.
      reflexivity.
    + change ((leg2 g' ∘ pullback_snd _ _ P') ∘ u ≈ leg2 g ∘ pullback_snd _ _ P).
      rewrite <- comp_assoc, Hu2.
      rewrite comp_assoc, Hg2.
      reflexivity.
Defined.

#[export] Program Instance span_compose_respects {X Y Z : C} :
  Proper (equiv ==> equiv ==> equiv) (@span_compose X Y Z).
Next Obligation.
  proper.
  now apply span_compose_respects_aux.
Qed.

(** ** Identity laws *)

Lemma span_id_left {X Y : C} (f : SpanArrow X Y) :
  span_equiv (span_compose (span_id Y) f) f.
Proof.
  unfold span_compose, span_id; simpl.
  pose (P := pullback (leg2 f) id[Y]).
  (* Mediator from apex f into the pullback, using the cocone
       (id : apex f ~> apex f, leg2 f : apex f ~> Y). *)
  assert (HC : leg2 f ∘ id ≈ id ∘ leg2 f) by cat.
  set (m := pullback_med P HC).
  assert (Hm1 : pullback_fst _ _ P ∘ m ≈ id) by (apply pullback_med_fst).
  assert (Hm2 : pullback_snd _ _ P ∘ m ≈ leg2 f) by (apply pullback_med_snd).
  (* Iso: Pull P ≅ apex f, via to := pullback_fst P, from := m. *)
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := pullback_fst _ _ P; from := m |}.
    + exact Hm1.
    + (* m ∘ pullback_fst P ≈ id at Pull P.  By UMP against identity. *)
      apply (pullback_med_eq P (pullback_commutes _ _ P)
              (m ∘ pullback_fst _ _ P) id).
      * rewrite comp_assoc, Hm1; cat.
      * rewrite comp_assoc, Hm2.
        rewrite <- (id_left (pullback_snd _ _ P)).
        apply (pullback_commutes _ _ P).
      * cat.
      * cat.
  - simpl; split.
    + reflexivity.
    + (* leg2 f ∘ pullback_fst P ≈ id ∘ pullback_snd P  via pullback commutes. *)
      apply (pullback_commutes _ _ P).
Defined.

Lemma span_id_right {X Y : C} (f : SpanArrow X Y) :
  span_equiv (span_compose f (span_id X)) f.
Proof.
  unfold span_compose, span_id; simpl.
  pose (P := pullback id[X] (leg1 f)).
  assert (HC : id ∘ leg1 f ≈ leg1 f ∘ id) by cat.
  set (m := pullback_med P HC).
  assert (Hm1 : pullback_fst _ _ P ∘ m ≈ leg1 f) by (apply pullback_med_fst).
  assert (Hm2 : pullback_snd _ _ P ∘ m ≈ id) by (apply pullback_med_snd).
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := pullback_snd _ _ P; from := m |}.
    + exact Hm2.
    + apply (pullback_med_eq P (pullback_commutes _ _ P)
              (m ∘ pullback_snd _ _ P) id).
      * rewrite comp_assoc, Hm1.
        rewrite <- (id_left (pullback_fst _ _ P)).
        symmetry; apply (pullback_commutes _ _ P).
      * rewrite comp_assoc, Hm2; cat.
      * cat.
      * cat.
  - simpl; split.
    + (* id ∘ pullback_fst P ≈ leg1 f ∘ pullback_snd P  via pullback commutes. *)
      symmetry; apply (pullback_commutes _ _ P).
    + reflexivity.
Defined.

(** ** Associativity via pullback-pasting *)

Lemma span_compose_assoc {X Y Z W : C}
      (h : SpanArrow Z W) (g : SpanArrow Y Z) (f : SpanArrow X Y) :
  span_equiv
    (span_compose h (span_compose g f))
    (span_compose (span_compose h g) f).
Proof.
  unfold span_compose; simpl.
  pose (Pgf := pullback (leg2 f) (leg1 g)).
  pose (Phg := pullback (leg2 g) (leg1 h)).
  pose (PL  := pullback (leg2 g ∘ pullback_snd _ _ Pgf) (leg1 h)).
  pose (PR  := pullback (leg2 f) (leg1 g ∘ pullback_fst _ _ Phg)).
  pose proof (pullback_commutes _ _ Pgf) as Pgfc.
  pose proof (pullback_commutes _ _ Phg) as Phgc.
  pose proof (pullback_commutes _ _ PL)  as PLc.
  pose proof (pullback_commutes _ _ PR)  as PRc.
  (* === Build mediator PL -> PR ===
     PL has projections [pullback_fst PL : PL -> Pull Pgf] and
                        [pullback_snd PL : PL -> apex h].
     We need a map PL -> PR.  PR has projections to apex f and to Pull Phg.
       - To apex f:  use [pullback_fst Pgf ∘ pullback_fst PL : PL -> apex f].
       - To Pull Phg: use the UMP of Phg with cocone
           (pullback_snd Pgf ∘ pullback_fst PL : PL -> apex g,
            pullback_snd PL : PL -> apex h).
         This cocone commutes because of PLc. *)
  assert (Hphg :
    leg2 g ∘ (pullback_snd _ _ Pgf ∘ pullback_fst _ _ PL)
    ≈ leg1 h ∘ pullback_snd _ _ PL).
  { rewrite comp_assoc. exact PLc. }
  set (m_phg := pullback_med Phg Hphg).
  assert (Hm_phg1 :
    pullback_fst _ _ Phg ∘ m_phg ≈ pullback_snd _ _ Pgf ∘ pullback_fst _ _ PL)
    by (apply pullback_med_fst).
  assert (Hm_phg2 : pullback_snd _ _ Phg ∘ m_phg ≈ pullback_snd _ _ PL)
    by (apply pullback_med_snd).
  (* Now use these to build the mediator PL -> PR. *)
  assert (HuLR :
    leg2 f ∘ (pullback_fst _ _ Pgf ∘ pullback_fst _ _ PL)
    ≈ (leg1 g ∘ pullback_fst _ _ Phg) ∘ m_phg).
  { rewrite (comp_assoc (leg2 f)).
    rewrite Pgfc.
    rewrite <- !comp_assoc.
    rewrite Hm_phg1.
    rewrite !comp_assoc.
    reflexivity. }
  set (uLR := pullback_med PR HuLR).
  assert (HuLR1 :
    pullback_fst _ _ PR ∘ uLR ≈ pullback_fst _ _ Pgf ∘ pullback_fst _ _ PL)
    by (apply pullback_med_fst).
  assert (HuLR2 : pullback_snd _ _ PR ∘ uLR ≈ m_phg)
    by (apply pullback_med_snd).
  (* === Build mediator PR -> PL === *)
  (* PR has projections [pullback_fst PR : PR -> apex f] and
                        [pullback_snd PR : PR -> Pull Phg].
     Build cocone for Pgf using (pullback_fst PR, pullback_fst Phg ∘ pullback_snd PR). *)
  assert (Hpgf :
    leg2 f ∘ pullback_fst _ _ PR
    ≈ leg1 g ∘ (pullback_fst _ _ Phg ∘ pullback_snd _ _ PR)).
  { rewrite comp_assoc. exact PRc. }
  set (m_pgf := pullback_med Pgf Hpgf).
  assert (Hm_pgf1 : pullback_fst _ _ Pgf ∘ m_pgf ≈ pullback_fst _ _ PR)
    by (apply pullback_med_fst).
  assert (Hm_pgf2 :
    pullback_snd _ _ Pgf ∘ m_pgf ≈ pullback_fst _ _ Phg ∘ pullback_snd _ _ PR)
    by (apply pullback_med_snd).
  (* Now the mediator PR -> PL. *)
  assert (HuRL :
    (leg2 g ∘ pullback_snd _ _ Pgf) ∘ m_pgf
    ≈ leg1 h ∘ (pullback_snd _ _ Phg ∘ pullback_snd _ _ PR)).
  { rewrite <- comp_assoc.
    rewrite Hm_pgf2.
    rewrite comp_assoc.
    rewrite Phgc.
    rewrite <- comp_assoc.
    reflexivity. }
  set (uRL := pullback_med PL HuRL).
  assert (HuRL1 : pullback_fst _ _ PL ∘ uRL ≈ m_pgf)
    by (apply pullback_med_fst).
  assert (HuRL2 :
    pullback_snd _ _ PL ∘ uRL ≈ pullback_snd _ _ Phg ∘ pullback_snd _ _ PR)
    by (apply pullback_med_snd).
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := uLR; from := uRL |}.
    + (* uLR ∘ uRL ≈ id on PR.  *)
      apply (pullback_med_eq PR PRc (uLR ∘ uRL) id).
      * rewrite comp_assoc, HuLR1.
        rewrite <- comp_assoc, HuRL1.
        exact Hm_pgf1.
      * (* pullback_snd PR ∘ (uLR ∘ uRL) ≈ pullback_snd PR.
           Factor pullback_snd PR through Phg's UMP. *)
        assert (Hcc :
          leg2 g ∘ (pullback_fst _ _ Phg ∘ pullback_snd _ _ PR)
          ≈ leg1 h ∘ (pullback_snd _ _ Phg ∘ pullback_snd _ _ PR)).
        { rewrite !comp_assoc.
          now rewrite Phgc. }
        apply (pullback_med_eq Phg Hcc
                (pullback_snd _ _ PR ∘ (uLR ∘ uRL))
                (pullback_snd _ _ PR)).
        -- rewrite !comp_assoc.
           rewrite <- (comp_assoc (pullback_fst _ _ Phg)).
           rewrite HuLR2.
           rewrite Hm_phg1.
           rewrite <- !comp_assoc.
           rewrite HuRL1.
           exact Hm_pgf2.
        -- rewrite !comp_assoc.
           rewrite <- (comp_assoc (pullback_snd _ _ Phg)).
           rewrite HuLR2.
           rewrite Hm_phg2.
           exact HuRL2.
        -- reflexivity.
        -- reflexivity.
      * cat.
      * cat.
    + (* uRL ∘ uLR ≈ id on PL. *)
      apply (pullback_med_eq PL PLc (uRL ∘ uLR) id).
      * (* pullback_fst PL ∘ (uRL ∘ uLR) ≈ pullback_fst PL.
           Factor pullback_fst PL through Pgf's UMP. *)
        assert (Hcc :
          leg2 f ∘ (pullback_fst _ _ Pgf ∘ pullback_fst _ _ PL)
          ≈ leg1 g ∘ (pullback_snd _ _ Pgf ∘ pullback_fst _ _ PL)).
        { rewrite !comp_assoc.
          now rewrite Pgfc. }
        apply (pullback_med_eq Pgf Hcc
                (pullback_fst _ _ PL ∘ (uRL ∘ uLR))
                (pullback_fst _ _ PL)).
        -- rewrite !comp_assoc.
           rewrite <- (comp_assoc (pullback_fst _ _ Pgf)).
           rewrite HuRL1.
           rewrite Hm_pgf1.
           exact HuLR1.
        -- rewrite !comp_assoc.
           rewrite <- (comp_assoc (pullback_snd _ _ Pgf)).
           rewrite HuRL1.
           rewrite Hm_pgf2.
           rewrite <- !comp_assoc.
           rewrite HuLR2.
           exact Hm_phg1.
        -- reflexivity.
        -- reflexivity.
      * rewrite comp_assoc, HuRL2.
        rewrite <- comp_assoc, HuLR2.
        exact Hm_phg2.
      * cat.
      * cat.
  - simpl; split.
    + change ((leg1 f ∘ pullback_fst _ _ PR) ∘ uLR
              ≈ (leg1 f ∘ pullback_fst _ _ Pgf) ∘ pullback_fst _ _ PL).
      rewrite <- !comp_assoc, HuLR1.
      rewrite !comp_assoc.
      reflexivity.
    + change (((leg2 h ∘ pullback_snd _ _ Phg) ∘ pullback_snd _ _ PR) ∘ uLR
              ≈ leg2 h ∘ pullback_snd _ _ PL).
      rewrite <- !comp_assoc.
      rewrite HuLR2.
      rewrite Hm_phg2.
      reflexivity.
Defined.

Lemma span_compose_assoc_sym {X Y Z W : C}
      (h : SpanArrow Z W) (g : SpanArrow Y Z) (f : SpanArrow X Y) :
  span_equiv
    (span_compose (span_compose h g) f)
    (span_compose h (span_compose g f)).
Proof.
  apply span_equiv_sym, span_compose_assoc.
Defined.

End SpanCategory.

Arguments SpanArrow {C} X Y.
Arguments apex {C X Y} _.
Arguments leg1 {C X Y} _.
Arguments leg2 {C X Y} _.

(** ** The span category as a [Category] record *)
Section SpanCatDef.
Context (C : Category).
Context (HP : HasPullbacks C).

Program Definition SpanCat : Category := {|
  obj      := @obj C;
  hom      := fun X Y => SpanArrow X Y;
  homset   := fun X Y => @SpanArrow_Setoid C X Y;
  id       := fun X => span_id X;
  compose  := fun X Y Z g f => span_compose HP g f;
  compose_respects := fun X Y Z => @span_compose_respects C HP X Y Z;
  id_left  := fun X Y f => span_id_left HP f;
  id_right := fun X Y f => span_id_right HP f;
  comp_assoc := fun X Y Z W f g h => span_compose_assoc HP f g h;
  comp_assoc_sym := fun X Y Z W f g h => span_compose_assoc_sym HP f g h
|}.

End SpanCatDef.

Arguments SpanCat C HP.

