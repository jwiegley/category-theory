Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.

Generalizable All Variables.

(** * The cospan category (direct construction)

    Objects: the objects of [C].
    Morphisms [X ~> Y]: cospans [X -in1-> N <-in2- Y], with apex [N].
    Equivalence: two cospans are equivalent if their apexes are connected
    by an isomorphism that respects both legs.
    Composition: given [X -> N <- Y] and [Y -> M <- Z], the composite is
    the pushout [X -> N ⊔_Y M <- Z].

    For this to be a category we need that [C] has pushouts ([HasPushouts]).

    This construction MIRRORS [Construction.Span.Category] in shape but uses
    pushouts in [C] directly, rather than going through pullbacks in [C^op].
    Downstream files can therefore phrase all cospan obligations as C-level
    equations without C^op type friction.  The duality is still present at
    the level of [HasPushouts ↔ HasPullbacks (C^op)] (via [Structure/Pushout]).

    User-facing API:

      - [CospanArrow X Y]   — the record of cospans from [X] to [Y]
      - [cospan_apex f]     — the apex
      - [cospan_in1 f]      — the leg [X ~> apex]
      - [cospan_in2 f]      — the leg [Y ~> apex]
      - [CospanCat C HP]    — the category of cospans *)

Section CospanCategory.

Context {C : Category}.

(** A cospan from [X] to [Y]: an apex [N] together with two legs from [X]
    and [Y] into the apex. *)
Record CospanArrow (X Y : C) : Type := {
  cospan_apex : C;
  cospan_in1  : X ~> cospan_apex;
  cospan_in2  : Y ~> cospan_apex
}.

Arguments cospan_apex {X Y} _.
Arguments cospan_in1  {X Y} _.
Arguments cospan_in2  {X Y} _.

(** Two cospans are equivalent if there is an isomorphism of apexes whose
    composite (in either direction) with the corresponding legs agrees.

    Convention: we require [to phi ∘ cospan_in1 f ≈ cospan_in1 g] (the iso
    intertwines the legs from the LHS apex to the RHS apex). *)
Definition cospan_equiv {X Y : C} (f g : CospanArrow X Y) : Type :=
  { phi : cospan_apex f ≅ cospan_apex g
    & ((to phi ∘ cospan_in1 f ≈ cospan_in1 g)
     * (to phi ∘ cospan_in2 f ≈ cospan_in2 g))%type }.

Lemma cospan_equiv_refl {X Y : C} (f : CospanArrow X Y) :
  cospan_equiv f f.
Proof.
  exists iso_id; simpl; split; cat.
Defined.

Lemma cospan_equiv_sym {X Y : C} (f g : CospanArrow X Y) :
  cospan_equiv f g -> cospan_equiv g f.
Proof.
  intros [phi [H1 H2]].
  exists (iso_sym phi); simpl; split.
  - rewrite <- H1.
    rewrite comp_assoc.
    rewrite iso_from_to; cat.
  - rewrite <- H2.
    rewrite comp_assoc.
    rewrite iso_from_to; cat.
Defined.

Lemma cospan_equiv_trans {X Y : C} (f g h : CospanArrow X Y) :
  cospan_equiv f g -> cospan_equiv g h -> cospan_equiv f h.
Proof.
  intros [phi [H1 H2]] [psi [K1 K2]].
  exists (iso_compose psi phi); simpl; split.
  - rewrite <- comp_assoc, H1; exact K1.
  - rewrite <- comp_assoc, H2; exact K2.
Defined.

#[export] Program Instance CospanArrow_Setoid {X Y : C} :
  Setoid (CospanArrow X Y) := {|
  equiv := fun f g => cospan_equiv f g
|}.
Next Obligation.
  constructor.
  - intros f; apply cospan_equiv_refl.
  - intros f g; apply cospan_equiv_sym.
  - intros f g h; apply cospan_equiv_trans.
Defined.

(** Identity cospan on [X]: apex is [X], both legs are identity. *)
Definition cospan_id (X : C) : CospanArrow X X :=
  {| cospan_apex := X; cospan_in1 := id[X]; cospan_in2 := id[X] |}.

Variable HP : HasPushouts C.

(** Composition of cospans via pushout.

    Given [f : X ~> Y] with apex [N] and legs [i1f : X ~> N], [i2f : Y ~> N],
    and [g : Y ~> Z] with apex [M] and legs [i1g : Y ~> M], [i2g : Z ~> M],
    the pushout of the span [N <-i2f- Y -i1g-> M] gives an apex [P] with
    [in1 : N ~> P], [in2 : M ~> P].  The composite cospan has apex [P],
    [cospan_in1 := in1 ∘ i1f] and [cospan_in2 := in2 ∘ i2g]. *)
Definition cospan_compose
           {X Y Z : C}
           (g : CospanArrow Y Z) (f : CospanArrow X Y)
  : CospanArrow X Z :=
  let P := pushout (cospan_in2 f) (cospan_in1 g) in
  {| cospan_apex := pushout_apex P;
     cospan_in1  := pushout_in1 P ∘ cospan_in1 f;
     cospan_in2  := pushout_in2 P ∘ cospan_in2 g |}.

(** ** Proper instance for composition (the pushout-pasting lemma) *)

Lemma cospan_compose_respects_aux
      {X Y Z : C}
      (g g' : CospanArrow Y Z) (f f' : CospanArrow X Y)
      (Hf : cospan_equiv f f') (Hg : cospan_equiv g g') :
  cospan_equiv (cospan_compose g f) (cospan_compose g' f').
Proof.
  destruct Hf as [phi [Hf1 Hf2]].
  destruct Hg as [psi [Hg1 Hg2]].
  unfold cospan_compose; simpl.
  pose (P  := pushout (cospan_in2 f)  (cospan_in1 g)).
  pose (P' := pushout (cospan_in2 f') (cospan_in1 g')).
  (* Mediator P -> P'.  Build a cocone over (cospan_in2 f, cospan_in1 g)
     into apex P' using legs (pushout_in1 P' ∘ to phi : apex f ~> apex P')
     and (pushout_in2 P' ∘ to psi : apex g ~> apex P').
     They satisfy
        (pushout_in1 P' ∘ to phi) ∘ cospan_in2 f
       = pushout_in1 P' ∘ (to phi ∘ cospan_in2 f)
       = pushout_in1 P' ∘ cospan_in2 f'   [by Hf2]
       = pushout_in2 P' ∘ cospan_in1 g'   [pushout_commutes P']
       = pushout_in2 P' ∘ (to psi ∘ cospan_in1 g)   [by Hg1, rev]
       = (pushout_in2 P' ∘ to psi) ∘ cospan_in1 g. *)
  assert (Hcomm : (pushout_in1 P' ∘ to phi) ∘ cospan_in2 f
                  ≈ (pushout_in2 P' ∘ to psi) ∘ cospan_in1 g).
  { rewrite <- !comp_assoc.
    rewrite Hf2.
    rewrite Hg1.
    apply (pushout_commutes P'). }
  set (u := pushout_med P Hcomm).
  assert (Hu1 : u ∘ pushout_in1 P ≈ pushout_in1 P' ∘ to phi)
    by (apply pushout_med_in1).
  assert (Hu2 : u ∘ pushout_in2 P ≈ pushout_in2 P' ∘ to psi)
    by (apply pushout_med_in2).
  (* Mediator P' -> P. *)
  (* We want: (from phi) ∘ cospan_in2 f' ≈ cospan_in2 f,
     which follows from Hf2 + iso_from_to. *)
  assert (Hf2' : from phi ∘ cospan_in2 f' ≈ cospan_in2 f).
  { rewrite <- Hf2.
    rewrite comp_assoc, iso_from_to, id_left.
    reflexivity. }
  assert (Hg1' : from psi ∘ cospan_in1 g' ≈ cospan_in1 g).
  { rewrite <- Hg1.
    rewrite comp_assoc, iso_from_to, id_left.
    reflexivity. }
  assert (Hcomm' : (pushout_in1 P ∘ from phi) ∘ cospan_in2 f'
                  ≈ (pushout_in2 P ∘ from psi) ∘ cospan_in1 g').
  { rewrite <- !comp_assoc.
    rewrite Hf2', Hg1'.
    apply (pushout_commutes P). }
  set (v := pushout_med P' Hcomm').
  assert (Hv1 : v ∘ pushout_in1 P' ≈ pushout_in1 P ∘ from phi)
    by (apply pushout_med_in1).
  assert (Hv2 : v ∘ pushout_in2 P' ≈ pushout_in2 P ∘ from psi)
    by (apply pushout_med_in2).
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := u; from := v |}.
    + (* u ∘ v ≈ id on apex P'. *)
      apply (pushout_med_eq P' (pushout_commutes P')
              (u ∘ v) id[pushout_apex P']).
      * rewrite <- comp_assoc, Hv1.
        rewrite comp_assoc, Hu1.
        rewrite <- comp_assoc, iso_to_from, id_right; reflexivity.
      * rewrite <- comp_assoc, Hv2.
        rewrite comp_assoc, Hu2.
        rewrite <- comp_assoc, iso_to_from, id_right; reflexivity.
      * cat.
      * cat.
    + (* v ∘ u ≈ id on apex P. *)
      apply (pushout_med_eq P (pushout_commutes P)
              (v ∘ u) id[pushout_apex P]).
      * rewrite <- comp_assoc, Hu1.
        rewrite comp_assoc, Hv1.
        rewrite <- comp_assoc, iso_from_to, id_right; reflexivity.
      * rewrite <- comp_assoc, Hu2.
        rewrite comp_assoc, Hv2.
        rewrite <- comp_assoc, iso_from_to, id_right; reflexivity.
      * cat.
      * cat.
  - simpl; split; cbn [to from]; fold P P'.
    + (* u ∘ (pushout_in1 P ∘ cospan_in1 f) ≈ pushout_in1 P' ∘ cospan_in1 f' *)
      rewrite comp_assoc.
      rewrite Hu1.
      rewrite <- comp_assoc.
      rewrite Hf1.
      reflexivity.
    + rewrite comp_assoc.
      rewrite Hu2.
      rewrite <- comp_assoc.
      rewrite Hg2.
      reflexivity.
Defined.

#[export] Program Instance cospan_compose_respects {X Y Z : C} :
  Proper (equiv ==> equiv ==> equiv) (@cospan_compose X Y Z).
Next Obligation.
  proper.
  now apply cospan_compose_respects_aux.
Qed.

(** ** Identity laws *)

Lemma cospan_id_left {X Y : C} (f : CospanArrow X Y) :
  cospan_equiv (cospan_compose (cospan_id Y) f) f.
Proof.
  unfold cospan_compose, cospan_id; simpl.
  pose (P := pushout (cospan_in2 f) (id[Y] : Y ~{C}~> Y)).
  (* Mediator from apex P to apex f, via cocone (id : apex f ~> apex f,
     cospan_in2 f : Y ~> apex f). *)
  assert (HC : id ∘ cospan_in2 f ≈ cospan_in2 f ∘ id) by cat.
  set (m := pushout_med P HC).
  assert (Hm1 : m ∘ pushout_in1 _ ≈ id) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 _ ≈ cospan_in2 f) by (apply pushout_med_in2).
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := m; from := pushout_in1 _ |}.
    + (* m ∘ pushout_in1 P ≈ id at apex f. *)
      exact Hm1.
    + (* pushout_in1 P ∘ m ≈ id at apex P.  By UMP against identity. *)
      apply (pushout_med_eq P (pushout_commutes P)
              (pushout_in1 P ∘ m) id).
      * rewrite <- comp_assoc, Hm1; cat.
      * rewrite <- comp_assoc, Hm2.
        rewrite <- (id_right (pushout_in2 P)).
        exact (pushout_commutes P).
      * cat.
      * cat.
  - simpl; split; cbn [to from]; fold P.
    + (* m ∘ (pushout_in1 P ∘ cospan_in1 f) ≈ cospan_in1 f *)
      rewrite comp_assoc, Hm1, id_left; reflexivity.
    + (* m ∘ (pushout_in2 P ∘ id) ≈ cospan_in2 f *)
      rewrite id_right.
      exact Hm2.
Defined.

Lemma cospan_id_right {X Y : C} (f : CospanArrow X Y) :
  cospan_equiv (cospan_compose f (cospan_id X)) f.
Proof.
  unfold cospan_compose, cospan_id; simpl.
  pose (P := pushout (id[X] : X ~{C}~> X) (cospan_in1 f)).
  assert (HC : cospan_in1 f ∘ id ≈ id ∘ cospan_in1 f) by cat.
  set (m := pushout_med P HC).
  assert (Hm1 : m ∘ pushout_in1 _ ≈ cospan_in1 f) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 _ ≈ id) by (apply pushout_med_in2).
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := m; from := pushout_in2 _ |}.
    + exact Hm2.
    + apply (pushout_med_eq P (pushout_commutes P)
              (pushout_in2 P ∘ m) id).
      * rewrite <- comp_assoc, Hm1.
        rewrite <- (id_right (pushout_in1 P)).
        symmetry. exact (pushout_commutes P).
      * rewrite <- comp_assoc, Hm2; cat.
      * cat.
      * cat.
  - simpl; split; cbn [to from]; fold P.
    + rewrite id_right.
      exact Hm1.
    + rewrite comp_assoc, Hm2, id_left; reflexivity.
Defined.

(** ** Associativity via pushout-pasting

    Mirrors [span_compose_assoc] in [Construction/Span/Category.v]
    with arrows reversed.

    ** Refactoring note (deferred)

    The proof below is 175 lines.  It builds both mediator maps
    [PR -> PL] and [PL -> PR] inline by the HP-style "construct cocone,
    apply UMP, prove round-trips by [pushout_med_eq]" technique.
    The two mediator constructions are structurally identical modulo
    a swap of inner / outer pushouts.

    Extracting the "mediator-by-pasting" sub-lemma — call it
    [pushout_pasting_med] — should shrink this proof to roughly
    50 lines, by replacing the two ad-hoc inline mediator
    constructions with a single shared lemma application.  The
    underlying mathematical fact is one application of pushout-pasting
    in two steps (Mac Lane CWM IX.3, or Riehl Ch.3 Prop 3.4.7).

    Deferred to a follow-up PR; the present proof is correct and
    self-contained. *)

Lemma cospan_compose_assoc {X Y Z W : C}
      (h : CospanArrow Z W) (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_equiv
    (cospan_compose h (cospan_compose g f))
    (cospan_compose (cospan_compose h g) f).
Proof.
  unfold cospan_compose; simpl.
  pose (Pgf := pushout (cospan_in2 f) (cospan_in1 g)).
  pose (Phg := pushout (cospan_in2 g) (cospan_in1 h)).
  pose (PL  := pushout (pushout_in2 Pgf ∘ cospan_in2 g) (cospan_in1 h)).
  pose (PR  := pushout (cospan_in2 f) (pushout_in1 Phg ∘ cospan_in1 g)).
  pose proof (pushout_commutes Pgf) as Pgfc.
  pose proof (pushout_commutes Phg) as Phgc.
  pose proof (pushout_commutes PL)  as PLc.
  pose proof (pushout_commutes PR)  as PRc.
  (* === Build mediator PR -> PL ===
     PR has injections [pushout_in1 PR : apex f ~> apex PR] and
                       [pushout_in2 PR : apex Phg ~> apex PR].
     We need a map PR -> PL.  PL has injections from apex Pgf and apex h.
       - From apex Pgf:  use UMP of Pgf with cocone
           (pushout_in1 PL ∘ pushout_in1 Pgf : apex f ~> apex PL,
            pushout_in1 PL ∘ pushout_in2 Pgf : apex g ~> apex PL).
         BUT — we need a cocone into a single object.  Actually we need a
         direct map [apex Pgf ~> apex PR]; use [pushout_in1 PR : apex f ~> apex PR]
         and route apex g via pushout_in2 PR ∘ pushout_in1 Phg.
         Same structure as the span case, dualised. *)
  (* PR has cocone giving a map apex Pgf -> apex PR:
     (pushout_in1 PR : apex f -> apex PR, pushout_in2 PR ∘ pushout_in1 Phg : apex g -> apex PR)
     Commutes because: (pushout_in1 PR) ∘ cospan_in2 f
                     = (pushout_in2 PR ∘ pushout_in1 Phg) ∘ cospan_in1 g  [by PRc] *)
  assert (Hpgf :
    pushout_in1 PR ∘ cospan_in2 f
    ≈ (pushout_in2 PR ∘ pushout_in1 Phg) ∘ cospan_in1 g).
  { rewrite <- comp_assoc. exact PRc. }
  set (m_pgf := pushout_med Pgf Hpgf).
  assert (Hm_pgf1 : m_pgf ∘ pushout_in1 _ ≈ pushout_in1 PR)
    by (apply pushout_med_in1).
  assert (Hm_pgf2 : m_pgf ∘ pushout_in2 _ ≈ pushout_in2 PR ∘ pushout_in1 Phg)
    by (apply pushout_med_in2).
  (* Now the mediator PL -> PR: cocone from PL into PR.
     PL is pushout of (pushout_in2 Pgf ∘ cospan_in2 g, cospan_in1 h).
     Legs: (m_pgf : apex Pgf ~> apex PR) and need
           (apex h ~> apex PR).  Use pushout_in2 PR ∘ pushout_in2 Phg.
     Commute: m_pgf ∘ (pushout_in2 Pgf ∘ cospan_in2 g)
              ≈ (pushout_in2 PR ∘ pushout_in2 Phg) ∘ cospan_in1 h. *)
  assert (HuLR :
    m_pgf ∘ (pushout_in2 Pgf ∘ cospan_in2 g)
    ≈ (pushout_in2 PR ∘ pushout_in2 Phg) ∘ cospan_in1 h).
  { rewrite comp_assoc.
    rewrite Hm_pgf2.
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    exact Phgc. }
  set (uLR := pushout_med PL HuLR).
  assert (HuLR1 : uLR ∘ pushout_in1 _ ≈ m_pgf)
    by (apply pushout_med_in1).
  assert (HuLR2 : uLR ∘ pushout_in2 _ ≈ pushout_in2 PR ∘ pushout_in2 Phg)
    by (apply pushout_med_in2).
  (* === Build mediator PR -> PL (reverse) === *)
  (* Phg cocone giving map apex Phg -> apex PL:
     (pushout_in1 PL ∘ pushout_in2 Pgf : apex g -> apex PL, pushout_in2 PL : apex h -> apex PL) *)
  assert (Hphg :
    (pushout_in1 PL ∘ pushout_in2 Pgf) ∘ cospan_in2 g
    ≈ pushout_in2 PL ∘ cospan_in1 h).
  { rewrite <- comp_assoc. exact PLc. }
  set (m_phg := pushout_med Phg Hphg).
  assert (Hm_phg1 : m_phg ∘ pushout_in1 _ ≈ pushout_in1 PL ∘ pushout_in2 Pgf)
    by (apply pushout_med_in1).
  assert (Hm_phg2 : m_phg ∘ pushout_in2 _ ≈ pushout_in2 PL)
    by (apply pushout_med_in2).
  (* Now the mediator PR -> PL. *)
  assert (HuRL :
    (pushout_in1 PL ∘ pushout_in1 Pgf) ∘ cospan_in2 f
    ≈ m_phg ∘ (pushout_in1 Phg ∘ cospan_in1 g)).
  { rewrite <- !comp_assoc.
    rewrite Pgfc.
    rewrite (comp_assoc m_phg).
    rewrite Hm_phg1.
    rewrite <- !comp_assoc.
    reflexivity. }
  set (uRL := pushout_med PR HuRL).
  assert (HuRL1 : uRL ∘ pushout_in1 _ ≈ pushout_in1 PL ∘ pushout_in1 Pgf)
    by (apply pushout_med_in1).
  assert (HuRL2 : uRL ∘ pushout_in2 _ ≈ m_phg)
    by (apply pushout_med_in2).
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := uLR; from := uRL |}.
    + (* uLR ∘ uRL ≈ id on apex PR. *)
      apply (pushout_med_eq PR PRc (uLR ∘ uRL) id).
      * rewrite <- comp_assoc, HuRL1.
        rewrite comp_assoc, HuLR1.
        exact Hm_pgf1.
      * (* (uLR ∘ uRL) ∘ pushout_in2 PR ≈ pushout_in2 PR.
           Factor pushout_in2 PR through Phg's UMP. *)
        assert (Hcc :
          (pushout_in2 PR ∘ pushout_in1 Phg) ∘ cospan_in2 g
          ≈ (pushout_in2 PR ∘ pushout_in2 Phg) ∘ cospan_in1 h).
        { rewrite <- !comp_assoc.
          now rewrite Phgc. }
        apply (pushout_med_eq Phg Hcc
                ((uLR ∘ uRL) ∘ pushout_in2 PR)
                (pushout_in2 PR)).
        -- (* (uLR ∘ uRL ∘ pushout_in2 PR) ∘ pushout_in1 Phg
              ≈ pushout_in2 PR ∘ pushout_in1 Phg *)
           rewrite <- (comp_assoc _ uRL (pushout_in2 PR)).
           rewrite HuRL2.
           rewrite <- (comp_assoc uLR m_phg).
           rewrite Hm_phg1.
           rewrite (comp_assoc uLR).
           rewrite HuLR1.
           exact Hm_pgf2.
        -- (* (uLR ∘ uRL ∘ pushout_in2 PR) ∘ pushout_in2 Phg
              ≈ pushout_in2 PR ∘ pushout_in2 Phg *)
           rewrite <- (comp_assoc _ uRL (pushout_in2 PR)).
           rewrite HuRL2.
           rewrite <- (comp_assoc uLR m_phg).
           rewrite Hm_phg2.
           exact HuLR2.
        -- reflexivity.
        -- reflexivity.
      * cat.
      * cat.
    + (* uRL ∘ uLR ≈ id on apex PL. *)
      apply (pushout_med_eq PL PLc (uRL ∘ uLR) id).
      * (* (uRL ∘ uLR) ∘ pushout_in1 PL ≈ pushout_in1 PL.
           Factor pushout_in1 PL through Pgf's UMP. *)
        assert (Hcc :
          (pushout_in1 PL ∘ pushout_in1 Pgf) ∘ cospan_in2 f
          ≈ (pushout_in1 PL ∘ pushout_in2 Pgf) ∘ cospan_in1 g).
        { rewrite <- !comp_assoc.
          now rewrite Pgfc. }
        apply (pushout_med_eq Pgf Hcc
                ((uRL ∘ uLR) ∘ pushout_in1 PL)
                (pushout_in1 PL)).
        -- (* (uRL ∘ uLR ∘ pushout_in1 PL) ∘ pushout_in1 Pgf
              ≈ pushout_in1 PL ∘ pushout_in1 Pgf *)
           rewrite <- (comp_assoc _ uLR (pushout_in1 PL)).
           rewrite HuLR1.
           rewrite <- (comp_assoc uRL m_pgf).
           rewrite Hm_pgf1.
           exact HuRL1.
        -- (* (uRL ∘ uLR ∘ pushout_in1 PL) ∘ pushout_in2 Pgf
              ≈ pushout_in1 PL ∘ pushout_in2 Pgf *)
           rewrite <- (comp_assoc _ uLR (pushout_in1 PL)).
           rewrite HuLR1.
           rewrite <- (comp_assoc uRL m_pgf).
           rewrite Hm_pgf2.
           rewrite (comp_assoc uRL).
           rewrite HuRL2.
           exact Hm_phg1.
        -- reflexivity.
        -- reflexivity.
      * (* (uRL ∘ uLR) ∘ pushout_in2 PL ≈ pushout_in2 PL *)
        rewrite <- (comp_assoc _ uLR (pushout_in2 PL)).
        rewrite HuLR2.
        rewrite (comp_assoc uRL).
        rewrite HuRL2.
        exact Hm_phg2.
      * cat.
      * cat.
  - simpl; split; cbn [to from]; fold Pgf Phg; fold PL PR.
    + (* uLR ∘ (pushout_in1 PL ∘ (pushout_in1 Pgf ∘ cospan_in1 f))
         ≈ pushout_in1 PR ∘ cospan_in1 f *)
      rewrite (comp_assoc uLR).
      rewrite (comp_assoc _ (pushout_in1 Pgf)).
      rewrite HuLR1.
      rewrite Hm_pgf1.
      reflexivity.
    + (* uLR ∘ (pushout_in2 PL ∘ cospan_in2 h)
         ≈ pushout_in2 PR ∘ (pushout_in2 Phg ∘ cospan_in2 h) *)
      rewrite (comp_assoc uLR).
      rewrite HuLR2.
      rewrite <- comp_assoc.
      reflexivity.
Defined.

Lemma cospan_compose_assoc_sym {X Y Z W : C}
      (h : CospanArrow Z W) (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_equiv
    (cospan_compose (cospan_compose h g) f)
    (cospan_compose h (cospan_compose g f)).
Proof.
  apply cospan_equiv_sym, cospan_compose_assoc.
Defined.

End CospanCategory.

Arguments CospanArrow {C} X Y.
Arguments cospan_apex {C X Y} _.
Arguments cospan_in1  {C X Y} _.
Arguments cospan_in2  {C X Y} _.
Arguments Build_CospanArrow {C X Y} _ _ _.

(** [Build_CospanArrow] is the auto-generated record constructor:
      [Build_CospanArrow : forall {C X Y} (N : C) (l1 : X ~> N) (l2 : Y ~> N),
                            CospanArrow X Y].
    Downstream uses match this signature directly. *)

(** ** Cospan composition accessors (reflexivity-level)

    These let downstream code unfold composition without having to
    [simpl] the [pushout] applicative machinery. *)

Section CospanCompositionAccessors.

Context {C : Category}.
Context (HP : HasPushouts C).

Lemma cospan_compose_apex {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_apex (cospan_compose HP g f)
  = pushout_apex (pushout (cospan_in2 f) (cospan_in1 g)).
Proof. reflexivity. Qed.

Lemma cospan_compose_in1 {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in1 (cospan_compose HP g f)
  ≈ pushout_in1 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in1 f.
Proof. reflexivity. Qed.

Lemma cospan_compose_in2 {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in2 (cospan_compose HP g f)
  ≈ pushout_in2 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in2 g.
Proof. reflexivity. Qed.

End CospanCompositionAccessors.

(** ** The cospan category as a [Category] record *)
Section CospanCatDef.
Context (C : Category).
Context (HP : HasPushouts C).

Program Definition CospanCat : Category := {|
  obj      := @obj C;
  hom      := fun X Y => CospanArrow X Y;
  homset   := fun X Y => @CospanArrow_Setoid C X Y;
  id       := fun X => cospan_id X;
  compose  := fun X Y Z g f => cospan_compose HP g f;
  compose_respects := fun X Y Z => @cospan_compose_respects C HP X Y Z;
  id_left  := fun X Y f => cospan_id_left HP f;
  id_right := fun X Y f => cospan_id_right HP f;
  comp_assoc := fun X Y Z W f g h => cospan_compose_assoc HP f g h;
  comp_assoc_sym := fun X Y Z W f g h => cospan_compose_assoc_sym HP f g h
|}.

End CospanCatDef.

Arguments CospanCat C HP : assert.
