Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Instance.Parallel.

Generalizable All Variables.

(** * Equalizers, elementarily: forks and descent *)

(* nLab:      https://ncatlab.org/nlab/show/equalizer
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   Given a parallel pair f, g : x ~> y in C, an equalizer is an object q
   together with an equalizing map e : q ~> x forming a "fork" under the
   pair,

       f ∘ e ≈ g ∘ e,

   that is universal with this property: every h : z ~> x with
   f ∘ h ≈ g ∘ h factors uniquely through e, i.e. there is a unique
   u : z ~> q with e ∘ u ≈ h (Wikipedia; nLab presents the same universal
   property as the limit of the parallel pair).

   [Structure/Equalizer.v] already presents the equalizer as a limit over
   the walking parallel pair ([Equalizer (APair f g) := Limit (APair f g)]).
   This file provides the elementary, fork-shaped presentation
   [IsEqualizer] together with conversions in both directions showing that
   the two presentations coincide:

     - [equalizer_is_equalizer] reads a limit of [APair f g] as an
       elementary equalizer at its apex, equalized by the limit leg over
       [ParX];
     - [is_equalizer_limit] rebuilds the bundled limit from the elementary
       data.

   Uniqueness of the equalizer object up to isomorphism
   ([equalizer_unique]) and the classical fact that equalizing maps are
   monomorphisms ([equalizer_monic]; Wikipedia: "every equaliser is a
   monomorphism") complete the API.  [HasEqualizers] packages a choice of
   elementary equalizer for every parallel pair.  This file is the
   limit-side sibling of [Structure/Coequalizer.v], with no opposite
   categories anywhere: everything is phrased directly in C. *)

(* The elementary universal property: e forks the pair f, g at q, and
   every forking map h into x factors uniquely across e. *)
Record IsEqualizer {C : Category} {x y : C} (f g : x ~> y)
  (q : C) (e : q ~> x) := {
  (* the equalizing map is absorbed by the parallel pair *)
  fork_eq : f ∘ e ≈ g ∘ e;

  (* universal property: every forking map h factors uniquely through e *)
  eq_desc {z} (h : z ~> x) (Hh : f ∘ h ≈ g ∘ h) :
    ∃! u : z ~> q, e ∘ u ≈ h
}.

Arguments fork_eq {_ _ _ _ _ _ _} _.
Arguments eq_desc {_ _ _ _ _ _ _} _ {_} _ _.

(* A category has all (binary) equalizers when every parallel pair
   carries an elementary equalizer.  This is the equalizer analogue of
   [HasCoequalizers] in [Structure/Coequalizer.v]. *)
Class HasEqualizers (C : Category) := {
  equalizer {x y : C} (f g : x ~> y) : ∃ (q : C) (e : q ~> x), IsEqualizer f g q e
}.

Section EqualizerLimit.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~> y).

(** ** Equalizing maps are monomorphisms *)

(* Wikipedia: "every equaliser is a monomorphism"; both factorizations of
   e ∘ g1 agree with the canonical one, so descent uniqueness cancels e on
   the left. *)
Lemma equalizer_monic {q : C} {e : q ~> x} (E : IsEqualizer f g q e) :
  Monic e.
Proof.
  constructor.
  intros z g1 g2 Hg.
  assert (Hfork : f ∘ (e ∘ g1) ≈ g ∘ (e ∘ g1)).
  { rewrite !comp_assoc.
    rewrite (fork_eq E).
    reflexivity. }
  transitivity (unique_obj (eq_desc E (e ∘ g1) Hfork)).
  - symmetry.
    apply (uniqueness (eq_desc E (e ∘ g1) Hfork)).
    reflexivity.
  - apply (uniqueness (eq_desc E (e ∘ g1) Hfork)).
    symmetry.
    exact Hg.
Qed.

(** ** Equalizers are unique up to isomorphism *)

(* Mirrors [coequalizer_unique] in [Structure/Coequalizer.v]: each
   equalizer factors the other's equalizing map, and both round-trips
   factor the identity, so descent uniqueness identifies them with id. *)
Lemma equalizer_unique {q1 q2 : C} {e1 : q1 ~> x} {e2 : q2 ~> x}
  (E1 : IsEqualizer f g q1 e1) (E2 : IsEqualizer f g q2 e2) :
  q1 ≅ q2.
Proof.
  pose proof (eq_desc E2 e1 (fork_eq E1)) as D12.
  pose proof (eq_desc E1 e2 (fork_eq E2)) as D21.
  pose proof (eq_desc E1 e1 (fork_eq E1)) as D11.
  pose proof (eq_desc E2 e2 (fork_eq E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - (* to ∘ from ≈ id[q2], by uniqueness of descent against D22 *)
    transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D22).
      apply id_right.
  - (* from ∘ to ≈ id[q1], by uniqueness of descent against D11 *)
    transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D11).
      apply id_right.
Qed.

(** ** From a forking map to a cone over the walking parallel pair *)

(* The legs of the cone induced by a forking map h: the leg over ParX is
   h itself, the leg over ParY is the common composite f ∘ h. *)
Definition fork_legs {z : C} (h : z ~> x) (p : ParObj) :
  z ~{C}~> APair f g p :=
  match p return (z ~{C}~> APair f g p) with
  | ParX => h
  | ParY => f ∘ h
  end.

(* Leg coherence: pushing the leg at the domain of any Parallel arrow
   along its image recovers the leg at the codomain.  This statement is
   definitionally the [cone_coherence] field of an [ACone] over
   APair f g. *)
Lemma fork_legs_coherence {z : C} (h : z ~> x) (Hh : f ∘ h ≈ g ∘ h) :
  ∀ (a b : ParObj) (k : a ~{Parallel}~> b),
    fmap[APair f g] k ∘ fork_legs h a ≈ fork_legs h b.
Proof.
  intros a b k.
  destruct a, b.
  - (* identity arrow on ParX *)
    simpl.
    apply id_left.
  - (* the two arrows ParX ~> ParY, sent to f and g *)
    destruct k as [bb hk].
    destruct bb.
    + (* (true; ParOne), sent to f *)
      reflexivity.
    + (* (false; ParTwo), sent to g *)
      symmetry.
      exact Hh.
  - (* an arrow ParY ~> ParX: refuted *)
    destruct k as [bb hk].
    destruct (ParHom_Y_X_absurd _ hk).
  - (* identity arrow on ParY *)
    simpl.
    apply id_left.
Qed.

(* The cone over APair f g induced by a forking map. *)
Definition fork_cone {z : C} (h : z ~> x) (Hh : f ∘ h ≈ g ∘ h) :
  Cone (APair f g) :=
  @Build_Cone Parallel C (APair f g) z
    (@Build_ACone Parallel C z (APair f g)
       (fork_legs h) (fork_legs_coherence h Hh)).

(** ** From the limit presentation to the elementary one *)

(* The limit leg over ParX forks the pair: both composites agree with the
   leg over ParY, by leg coherence at the two nonidentity arrows of the
   walking parallel pair. *)
Lemma limit_equalizes (L : Equalizer (APair f g)) :
  f ∘ limit_leg (limit_is_alimit L) ParX
    ≈ g ∘ limit_leg (limit_is_alimit L) ParX.
Proof.
  transitivity (limit_leg (limit_is_alimit L) ParY).
  - exact (limit_leg_coherence (limit_is_alimit L)
             ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - symmetry.
    exact (limit_leg_coherence (limit_is_alimit L)
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
Qed.

(* Descent through the limit apex: mediate into the limit from the cone
   induced by the forking map. *)
Lemma limit_equalizer_desc (L : Equalizer (APair f g))
  {z : C} (h : z ~> x) (Hh : f ∘ h ≈ g ∘ h) :
  ∃! u : z ~> L,
    limit_leg (limit_is_alimit L) ParX ∘ u ≈ h.
Proof.
  unshelve eapply Build_Unique.
  - exact (limit_med (limit_is_alimit L) (fork_cone h Hh)).
  - exact (limit_med_commutes
             (limit_is_alimit L) (fork_cone h Hh) ParX).
  - intros v Hv.
    refine (limit_med_unique
              (limit_is_alimit L) (fork_cone h Hh) v _).
    intros p.
    destruct p.
    + exact Hv.
    + (* the ParY leg follows from the ParX leg via coherence *)
      rewrite <- (limit_leg_coherence (limit_is_alimit L)
                    ((true; ParOne) : ParX ~{Parallel}~> ParY)).
      rewrite <- comp_assoc.
      rewrite Hv.
      reflexivity.
Qed.

(* A limit of APair f g is an elementary equalizer at its apex. *)
Definition equalizer_is_equalizer (L : Equalizer (APair f g)) :
  IsEqualizer f g L (limit_leg (limit_is_alimit L) ParX) :=
  {| fork_eq := limit_equalizes L
   ; eq_desc := fun z h Hh => limit_equalizer_desc L h Hh |}.

(** ** From the elementary presentation back to the limit *)

(* The limit cone of an elementary equalizer: legs e and f ∘ e over ParX
   and ParY. *)
Definition is_equalizer_cone {q : C} {e : q ~> x}
  (E : IsEqualizer f g q e) : Cone (APair f g) :=
  fork_cone e (fork_eq E).

(* The universal property of that cone; this statement is definitionally
   the [ump_limits] field of the limit ([Limit (APair f g)]) whose limit
   cone is [is_equalizer_cone]. *)
Lemma is_equalizer_cone_ump {q : C} {e : q ~> x}
  (E : IsEqualizer f g q e) (N : Cone (APair f g)) :
  ∃! u : vertex_obj[N] ~> q,
    ∀ p : ParObj, fork_legs e p ∘ u ≈ cone_leg N p.
Proof.
  assert (HX1 : f ∘ cone_leg N ParX ≈ cone_leg N ParY).
  { exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _
             ((true; ParOne) : ParX ~{Parallel}~> ParY)). }
  assert (HX2 : g ∘ cone_leg N ParX ≈ cone_leg N ParY).
  { exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)). }
  assert (Hfg : f ∘ cone_leg N ParX ≈ g ∘ cone_leg N ParX).
  { rewrite HX1.
    rewrite HX2.
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (eq_desc E (cone_leg N ParX) Hfg)).
  - intros p.
    destruct p.
    + exact (unique_property (eq_desc E (cone_leg N ParX) Hfg)).
    + (* leg over ParY: (f ∘ e) ∘ u ≈ nY via the ParX triangle *)
      simpl.
      rewrite <- comp_assoc.
      rewrite (unique_property (eq_desc E (cone_leg N ParX) Hfg)).
      exact HX1.
  - intros v Hv.
    apply (uniqueness (eq_desc E (cone_leg N ParX) Hfg)).
    exact (Hv ParX).
Qed.

(* An elementary equalizer yields the bundled limit over the walking
   parallel pair. *)
Definition is_equalizer_limit {q : C} {e : q ~> x}
  (E : IsEqualizer f g q e) : Equalizer (APair f g) :=
  {| limit_cone := is_equalizer_cone E
   ; ump_limits := fun N => is_equalizer_cone_ump E N |}.

End EqualizerLimit.
