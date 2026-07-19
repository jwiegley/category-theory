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
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Coequalizers, elementarily: coforks and descent *)

(* nLab:      https://ncatlab.org/nlab/show/coequalizer
   Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

   Given a parallel pair f, g : x ~> y in C, a coequalizer is an object q
   together with a coequalizing map e : y ~> q forming a "cofork" over the
   pair,

       e ∘ f ≈ e ∘ g,

   that is universal with this property: every h : y ~> z with
   h ∘ f ≈ h ∘ g descends uniquely through e, i.e. there is a unique
   u : q ~> z with u ∘ e ≈ h (Wikipedia; nLab presents the same universal
   property as the pushout-style colimit of the parallel pair).

   [Structure/Equalizer.v] already presents the coequalizer as a colimit
   over the walking parallel pair ([Coequalizer (APair f g) :=
   Colimit (APair f g)]).  This file provides the elementary, fork-shaped
   presentation [IsCoequalizer] together with conversions in both
   directions showing that the two presentations coincide:

     - [coequalizer_is_coequalizer] reads a colimit of [APair f g] as an
       elementary coequalizer at its apex, coequalized by the colimit
       injection over [ParY];
     - [is_coequalizer_colimit] rebuilds the bundled colimit from the
       elementary data.

   Uniqueness of the coequalizer object up to isomorphism
   ([coequalizer_unique]) and the classical fact that coequalizing maps
   are epimorphisms ([coequalizer_epic]; Wikipedia: "every coequalizer is
   an epimorphism") complete the API.  [HasCoequalizers] packages a choice
   of elementary coequalizer for every parallel pair. *)

(* The elementary universal property: e coforks the pair f, g at q, and
   every coforking map h out of y descends uniquely across e. *)
Record IsCoequalizer {C : Category} {x y : C} (f g : x ~> y)
  (q : C) (e : y ~> q) := {
  (* the coequalizing map absorbs the parallel pair *)
  cofork : e ∘ f ≈ e ∘ g;

  (* universal property: every coforking map h descends uniquely through e *)
  coeq_desc {z} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
    ∃! u : q ~> z, u ∘ e ≈ h
}.

Arguments cofork {_ _ _ _ _ _ _} _.
Arguments coeq_desc {_ _ _ _ _ _ _} _ {_} _ _.

(* A category has all (binary) coequalizers when every parallel pair
   carries an elementary coequalizer.  This is the coequalizer analogue of
   [HasPullbacks] in [Structure/Pullback.v]. *)
Class HasCoequalizers (C : Category) := {
  coeq {x y : C} (f g : x ~> y) : ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e
}.

Section CoequalizerColimit.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~> y).

(** ** Coequalizing maps are epimorphisms *)

(* Wikipedia: "every coequalizer is an epimorphism"; both descents of
   g1 ∘ e agree with the canonical one, so descent uniqueness cancels e on
   the right. *)
Lemma coequalizer_epic {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  Epic e.
Proof.
  constructor.
  intros z g1 g2 Hg.
  assert (Hfork : (g1 ∘ e) ∘ f ≈ (g1 ∘ e) ∘ g).
  { rewrite <- !comp_assoc.
    rewrite (cofork E).
    reflexivity. }
  transitivity (unique_obj (coeq_desc E (g1 ∘ e) Hfork)).
  - symmetry.
    apply (uniqueness (coeq_desc E (g1 ∘ e) Hfork)).
    reflexivity.
  - apply (uniqueness (coeq_desc E (g1 ∘ e) Hfork)).
    symmetry.
    exact Hg.
Qed.

(** ** Coequalizers are unique up to isomorphism *)

(* Mirrors [pullback_unique] in [Structure/Pullback.v]: each coequalizer
   descends the other's coequalizing map, and both round-trips descend the
   identity, so descent uniqueness identifies them with id. *)
Lemma coequalizer_unique {q1 q2 : C} {e1 : y ~> q1} {e2 : y ~> q2}
  (E1 : IsCoequalizer f g q1 e1) (E2 : IsCoequalizer f g q2 e2) :
  q1 ≅ q2.
Proof.
  pose proof (coeq_desc E1 e2 (cofork E2)) as D12.
  pose proof (coeq_desc E2 e1 (cofork E1)) as D21.
  pose proof (coeq_desc E1 e1 (cofork E1)) as D11.
  pose proof (coeq_desc E2 e2 (cofork E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - (* to ∘ from ≈ id[q2], by uniqueness of descent against D22 *)
    transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite <- comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D22).
      apply id_left.
  - (* from ∘ to ≈ id[q1], by uniqueness of descent against D11 *)
    transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite <- comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D11).
      apply id_left.
Qed.

(** ** From a coforking map to a cocone over the walking parallel pair *)

(* The legs of the cocone induced by a coforking map h: the leg over ParX
   is the common composite h ∘ f, the leg over ParY is h itself. *)
Definition cofork_legs {z : C} (h : y ~> z) (p : ParObj) :
  APair f g p ~{C}~> z :=
  match p return (APair f g p ~{C}~> z) with
  | ParX => h ∘ f
  | ParY => h
  end.

(* Leg coherence, phrased covariantly in C: precomposing the leg at the
   codomain of any Parallel arrow with its image recovers the leg at the
   domain.  This statement is definitionally the [cone_coherence] field of
   an [ACone] over (APair f g)^op, since composition and hom-equivalence
   in C^op are those of C, flipped. *)
Lemma cofork_legs_coherence {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∀ (a b : ParObj) (k : b ~{Parallel}~> a),
    cofork_legs h a ∘ fmap[APair f g] k ≈ cofork_legs h b.
Proof.
  intros a b k.
  destruct a, b.
  - (* identity arrow on ParX *)
    simpl.
    apply id_right.
  - (* an arrow ParY ~> ParX: refuted *)
    destruct k as [bb hk].
    destruct (ParHom_Y_X_absurd _ hk).
  - (* the two arrows ParX ~> ParY, sent to f and g *)
    destruct k as [bb hk].
    destruct bb.
    + (* (true; ParOne), sent to f *)
      reflexivity.
    + (* (false; ParTwo), sent to g *)
      symmetry.
      exact Hh.
  - (* identity arrow on ParY *)
    simpl.
    apply id_right.
Qed.

(* The cocone over APair f g induced by a coforking map. *)
Definition cofork_cocone {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  Cocone (APair f g) :=
  @Build_Cone (Parallel^op) (C^op) ((APair f g)^op) z
    (@Build_ACone (Parallel^op) (C^op) z ((APair f g)^op)
       (cofork_legs h) (cofork_legs_coherence h Hh)).

(** ** From the colimit presentation to the elementary one *)

(* The colimit injection over ParY coforks the pair: both composites agree
   with the injection over ParX, by leg coherence at the two nonidentity
   arrows of the walking parallel pair. *)
Lemma colimit_coequalizes (L : Coequalizer (APair f g)) :
  colimit_inj (colimit_is_acolimit L) ParY ∘ f
    ≈ colimit_inj (colimit_is_acolimit L) ParY ∘ g.
Proof.
  transitivity (colimit_inj (colimit_is_acolimit L) ParX).
  - exact (colimit_inj_coherence (colimit_is_acolimit L)
             ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - symmetry.
    exact (colimit_inj_coherence (colimit_is_acolimit L)
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
Qed.

(* Descent through the colimit apex: mediate out of the colimit into the
   cocone induced by the coforking map. *)
Lemma colimit_coequalizer_desc (L : Coequalizer (APair f g))
  {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : colimit_apex L ~> z,
    u ∘ colimit_inj (colimit_is_acolimit L) ParY ≈ h.
Proof.
  unshelve eapply Build_Unique.
  - exact (colimit_med (colimit_is_acolimit L) (cofork_cocone h Hh)).
  - exact (colimit_med_commutes
             (colimit_is_acolimit L) (cofork_cocone h Hh) ParY).
  - intros v Hv.
    refine (colimit_med_unique
              (colimit_is_acolimit L) (cofork_cocone h Hh) v _).
    intros p.
    destruct p.
    + (* the ParX leg follows from the ParY leg via coherence *)
      rewrite <- (colimit_inj_coherence (colimit_is_acolimit L)
                    ((true; ParOne) : ParX ~{Parallel}~> ParY)).
      rewrite comp_assoc.
      rewrite Hv.
      reflexivity.
    + exact Hv.
Qed.

(* A colimit of APair f g is an elementary coequalizer at its apex. *)
Definition coequalizer_is_coequalizer (L : Coequalizer (APair f g)) :
  IsCoequalizer f g (colimit_apex L)
    (colimit_inj (colimit_is_acolimit L) ParY) :=
  {| cofork    := colimit_coequalizes L
   ; coeq_desc := fun z h Hh => colimit_coequalizer_desc L h Hh |}.

(** ** From the elementary presentation back to the colimit *)

(* The colimit cocone of an elementary coequalizer: legs e ∘ f and e over
   ParX and ParY. *)
Definition is_coequalizer_cocone {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : Cocone (APair f g) :=
  cofork_cocone e (cofork E).

(* The universal property of that cocone, phrased covariantly in C; this
   statement is definitionally the [ump_limits] field of the colimit
   ([Limit ((APair f g)^op)]) whose limit cone is [is_coequalizer_cocone]. *)
Lemma is_coequalizer_cocone_ump {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) (N : Cocone (APair f g)) :
  ∃! u : q ~> vertex_obj[N],
    ∀ p : ParObj, u ∘ cofork_legs e p ≈ cocone_inj N p.
Proof.
  assert (HX1 : cocone_inj N ParY ∘ f ≈ cocone_inj N ParX).
  { exact (cocone_inj_coherence N
             ((true; ParOne) : ParX ~{Parallel}~> ParY)). }
  assert (HX2 : cocone_inj N ParY ∘ g ≈ cocone_inj N ParX).
  { exact (cocone_inj_coherence N
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)). }
  assert (Hfg : cocone_inj N ParY ∘ f ≈ cocone_inj N ParY ∘ g).
  { rewrite HX1.
    rewrite HX2.
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (coeq_desc E (cocone_inj N ParY) Hfg)).
  - intros p.
    destruct p.
    + (* leg over ParX: u ∘ (e ∘ f) ≈ nX via the ParY triangle *)
      simpl.
      rewrite comp_assoc.
      rewrite (unique_property (coeq_desc E (cocone_inj N ParY) Hfg)).
      exact HX1.
    + exact (unique_property (coeq_desc E (cocone_inj N ParY) Hfg)).
  - intros v Hv.
    apply (uniqueness (coeq_desc E (cocone_inj N ParY) Hfg)).
    exact (Hv ParY).
Qed.

(* An elementary coequalizer yields the bundled colimit over the walking
   parallel pair. *)
Definition is_coequalizer_colimit {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : Coequalizer (APair f g) :=
  {| limit_cone := is_coequalizer_cocone E
   ; ump_limits := fun N => is_coequalizer_cocone_ump E N |}.

End CoequalizerColimit.
