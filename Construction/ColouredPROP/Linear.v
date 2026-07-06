Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Hom.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Supply.

From Coq Require Import Lists.List.
From Coq Require Import PeanoNat.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

Generalizable All Variables.

(** * The linear discipline over coloured PROPs *)

(* nLab:      https://ncatlab.org/nlab/show/PROP
   nLab:      https://ncatlab.org/nlab/show/linear+logic
   Wikipedia: https://en.wikipedia.org/wiki/Linear_type_system

   A wire type in a typed string-diagram language is LINEAR when values
   of that type may be neither duplicated nor deleted: every linear
   wire entering a diagram must leave it exactly once.  This file
   formalises that discipline over the coloured-PROP spine, in both
   directions:

   - NEGATIVE HALF (the fan-out/discard restriction).  Copyability is
     a boolean predicate [copyable : Colour -> bool]; a colour is
     linear when [copyable c = false].  A signature is CONSERVATIVE at
     a colour [c] when every generator has as many [c]-wires entering
     as leaving ([c_conservative], counted by [count_occ]); the free
     structural operations (identities, braids, composition, tensor)
     are conservative at EVERY colour, so per-colour wire counts are
     an invariant of all free terms ([cterm_count_occ]).  It follows
     that at a conservative colour the hom-types [CTerm S [c] [c; c]]
     (fan-out) and [CTerm S [c] []] (discard) are EMPTY
     ([no_linear_fanout] / [no_linear_discard]).  This is emptiness of
     the raw TYPE of terms, not merely emptiness up to the [CTermEq]
     equivalence — no diagram of that boundary can even be written
     down — and since a presented coloured PROP has literally the same
     morphisms as the free one (only the equivalence coarsens, see
     [Construction/ColouredPROP/Presentation.v]), the emptiness
     descends to EVERY presented quotient
     ([no_linear_fanout_presented] / [no_linear_discard_presented]).
     This is the categorical content of the type-level fan-out check
     of linear dataflow languages: an ill-linear plugging is not
     rewritten away — it is unrepresentable.

   - PERMUTATION INVARIANT.  Over a generator-free signature the
     counting invariant sharpens: every term's output boundary is a
     permutation of its input boundary ([structural_permutation]).
     This is a one-directional, Prop-level necessary condition on
     boundaries — it assigns no permutation to a term and proves no
     converse realizability — a necessary-condition shadow of "the
     free coloured PROP on no generators is the coloured permutation
     groupoid" (cf. [Empty_CSig] in
     [Construction/ColouredPROP/Signature.v]), which is not itself
     formalized here.

   - POSITIVE HALF (fan-out at copyable colours).  Conversely, a
     copyable colour is one whose wire object CARRIES a commutative
     comonoid: the selective supply of
     [Construction/ColouredPROP/Supply.v], whose single per-colour
     primitive [supply_wire] equips [wire c] with its comonoid
     whenever [copyable c = true].  Its comultiplication IS a fan-out
     morphism [wire c ~> wire c ⨂ wire c] ([copyable_fanout]) and its
     counit a discard [wire c ~> I] ([copyable_discard]) — the
     converse of the emptiness theorems, and the reason [copyable] is
     the correct boundary of the linear discipline.  Relative to the
     boundary supplies [supply_list] that [Supply.v] DERIVES from that
     primitive (by tensoring wire comonoids through
     [Theory/Algebra/Comonoid/Tensor.v]; nothing boundary-level is
     postulated), a morphism between all-copyable boundaries is
     DETERMINISTIC when it is a comonoid homomorphism between them
     ([sel_deterministic]) — the two Cho–Jacobs copy/discard
     preservation squares

       scopy ds Hd ∘ f    ≈ (f ⨂ f) ∘ scopy cs Hc
       sdiscard ds Hd ∘ f ≈ sdiscard cs Hc

     ([sel_deterministic_scopy] / [sel_deterministic_sdiscard]),
     packaged by the [ComonoidHom] class of
     [Theory/Algebra/Comonoid/Hom.v], whose kit supplies the
     identity/composition/respectfulness laws
     ([sel_deterministic_id] / [sel_deterministic_comp] /
     [sel_deterministic_equiv]).  The determinism predicate is stated
     on the braided/symmetric monoidal path [MBc P], where the supply
     comonoids live (see the MP/MB mediation note in [Supply.v]).
     The linear/non-linear bridge built on this predicate lives in
     [Construction/ColouredPROP/LNL.v].

   References:
   - Cho & Jacobs, "Disintegration and Bayesian inversion via string
     diagrams", MSCS 29(7):938-971, 2019 (arXiv:1709.00322) —
     determinism as comonoid homomorphy.
   - Fong & Spivak, "Supplying bells and whistles in symmetric
     monoidal categories" (arXiv:1908.02633) — supplies of commutative
     comonoids.
   - Bonchi, Sobocinski & Zanasi, "A categorical semantics of signal
     flow graphs" — coloured PROPs as typed diagram languages. *)

(** ** The negative half: conservativity and hom-emptiness *)

Section LinearDiscipline.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).
Context (copyable : Colour -> bool).

(** A colour is linear when it is not copyable. *)
Definition LinearColour (c : Colour) : Prop := copyable c = false.

(** A signature is conservative at [c] when every generator carries as
    many [c]-coloured wires in as out.  [Type]-valued: downstream
    positive-half files may need to eliminate it into data. *)
Definition c_conservative (c : Colour) : Type :=
  forall (cs ds : list Colour) (g : S cs ds),
    count_occ Cdec cs c = count_occ Cdec ds c.

(** The linear discipline for a whole signature: conservativity at
    every linear colour.  Copyable colours are unconstrained — their
    generators (e.g. explicit duplicators) may change wire counts. *)
Definition LinearRespecting : Type :=
  forall c : Colour, LinearColour c -> c_conservative c.

(** *** The occurrence invariant

    Per-colour wire counts are invariant under all five term formers:
    identities and composites trivially, the block braid and the
    tensor because [count_occ] distributes over [++]
    ([count_occ_app]), and generators by conservativity.  This is the
    whole-diagram consequence of the local counting discipline. *)

Lemma cterm_count_occ (c : Colour) (Hgen : c_conservative c)
  {cs ds : list Colour} (t : CTerm S cs ds) :
  count_occ Cdec cs c = count_occ Cdec ds c.
Proof.
  induction t as [xs | xs ys | xs ys zs g IHg f IHf
                 | xs1 ys1 xs2 ys2 f IHf g IHg | xs ys g];
  simpl.
  - (* CT_id *) reflexivity.
  - (* CT_braid: both boundaries are the same two blocks, swapped *)
    rewrite !count_occ_app; apply Nat.add_comm.
  - (* CT_comp: paste the two invariants *)
    etransitivity; eauto.
  - (* CT_tens: counts add across [++] *)
    rewrite !count_occ_app; congruence.
  - (* CT_gen: conservativity of the signature *)
    exact (Hgen _ _ g).
Qed.

(** *** Hom-emptiness at conservative colours

    No term can fan a conservative wire out ([1 <> 2]) or discard it
    ([1 <> 0]).  These are statements about the TYPE of raw terms:
    the free hom-setoid at these boundaries is empty outright, which
    is strictly stronger than emptiness up to [CTermEq]. *)

Theorem no_linear_fanout (c : Colour) (Hgen : c_conservative c) :
  CTerm S [c] [c; c] -> False.
Proof.
  intro t.
  pose proof (cterm_count_occ c Hgen t) as H.
  simpl in H.
  destruct (Cdec c c) as [_ | n] in H.
  - discriminate H.
  - exact (n eq_refl).
Qed.

Theorem no_linear_discard (c : Colour) (Hgen : c_conservative c) :
  CTerm S [c] [] -> False.
Proof.
  intro t.
  pose proof (cterm_count_occ c Hgen t) as H.
  simpl in H.
  destruct (Cdec c c) as [_ | n] in H.
  - discriminate H.
  - exact (n eq_refl).
Qed.

(** The bundled forms: under the linear discipline, every LINEAR
    colour has empty fan-out and discard homs. *)

Corollary linear_no_fanout (HL : LinearRespecting)
  (c : Colour) (Hc : LinearColour c) :
  CTerm S [c] [c; c] -> False.
Proof. exact (no_linear_fanout c (HL c Hc)). Qed.

Corollary linear_no_discard (HL : LinearRespecting)
  (c : Colour) (Hc : LinearColour c) :
  CTerm S [c] [] -> False.
Proof. exact (no_linear_discard c (HL c Hc)). Qed.

(** *** The permutation invariant of the structural fragment

    Over a generator-free signature the invariant sharpens from
    per-colour counting to boundary relatedness: every term's output
    boundary is a permutation of its input boundary.  Identities are
    reflexivity, the block braid is [Permutation_app_comm], and
    composition/tensor are transitivity/congruence of
    [Permutation]. *)

Theorem structural_permutation
  (Hempty : forall cs ds : list Colour, S cs ds -> False)
  {cs ds : list Colour} (t : CTerm S cs ds) :
  Permutation cs ds.
Proof.
  induction t as [xs | xs ys | xs ys zs g IHg f IHf
                 | xs1 ys1 xs2 ys2 f IHf g IHg | xs ys g].
  - apply Permutation_refl.
  - apply Permutation_app_comm.
  - eapply Permutation_trans; eauto.
  - apply Permutation_app; auto.
  - destruct (Hempty _ _ g).
Qed.

End LinearDiscipline.

Arguments LinearColour {Colour} copyable c : assert.
Arguments c_conservative {Colour} Cdec S c : assert.
Arguments LinearRespecting {Colour} Cdec S copyable : assert.
Arguments cterm_count_occ {Colour} Cdec S c Hgen {cs ds} t : assert.
Arguments no_linear_fanout {Colour} Cdec S c Hgen _ : assert.
Arguments no_linear_discard {Colour} Cdec S c Hgen _ : assert.
Arguments linear_no_fanout {Colour} Cdec S copyable HL c Hc _ : assert.
Arguments linear_no_discard {Colour} Cdec S copyable HL c Hc _ : assert.
Arguments structural_permutation {Colour} S Hempty {cs ds} t : assert.

(** ** Presented transfer

    A presented coloured PROP ([Construction/ColouredPROP/
    Presentation.v]) has THE SAME morphisms as the free category —
    [CPresentedCat E] is a [Quotient], which keeps [hom] on the nose
    and only coarsens the equivalence — so hom-emptiness transfers
    verbatim: both corollaries are [exact] applications of the free
    theorems at [CTerm (csmt_sig E)].  No quotient can create a
    fan-out at a conservative colour, whatever its axioms. *)

Section LinearPresented.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (E : CSMT Colour).

Corollary no_linear_fanout_presented (c : Colour)
  (Hgen : c_conservative Cdec (csmt_sig E) c) :
  ([c] ~{CPresentedCat E}~> [c; c]) -> False.
Proof. exact (no_linear_fanout Cdec (csmt_sig E) c Hgen). Qed.

Corollary no_linear_discard_presented (c : Colour)
  (Hgen : c_conservative Cdec (csmt_sig E) c) :
  ([c] ~{CPresentedCat E}~> []) -> False.
Proof. exact (no_linear_discard Cdec (csmt_sig E) c Hgen). Qed.

End LinearPresented.

Arguments no_linear_fanout_presented {Colour} Cdec E c Hgen _ : assert.
Arguments no_linear_discard_presented {Colour} Cdec E c Hgen _ : assert.

(** ** Machine-checked sanity: the empty signature

    [Empty_CSig] is conservative at every colour (its generator type
    is [Empty_set]), so with all colours declared linear it respects
    the linear discipline, its fan-out homs are empty, and every one
    of its terms has output boundary a permutation of its input
    boundary. *)

Example Empty_CSig_conservative {Colour : Type}
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) (c : Colour) :
  c_conservative Cdec Empty_CSig c :=
  fun _ _ g => match g with end.

Example Empty_CSig_linear_respecting {Colour : Type}
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) :
  LinearRespecting Cdec Empty_CSig (fun _ : Colour => false) :=
  fun c _ => Empty_CSig_conservative Cdec c.

Example Empty_CSig_no_fanout {Colour : Type}
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) (c : Colour) :
  CTerm Empty_CSig [c] [c; c] -> False :=
  no_linear_fanout Cdec Empty_CSig c (Empty_CSig_conservative Cdec c).

Example Empty_CSig_structural_permutation {Colour : Type}
  {cs ds : list Colour} (t : CTerm (@Empty_CSig Colour) cs ds) :
  Permutation cs ds :=
  structural_permutation Empty_CSig (fun _ _ g => match g with end) t.

(** ** The positive half: fan-out at copyable colours

    At an arbitrary coloured PROP [P] with a selective supply
    ([Construction/ColouredPROP/Supply.v]), every copyable wire
    carries honest fan-out and discard morphisms, and determinism at
    all-copyable boundaries is comonoid homomorphy for the derived
    supplies.  Everything is stated on the braided/symmetric monoidal
    path [MBc P], where the supply comonoids live. *)

Section SelectiveFanOut.

Context {Colour : Type}.
Context {P : ColouredPROP Colour}.
Context {copyable : Colour -> bool}.
Context `{SS : @SelectiveSupply Colour P copyable}.

Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(** *** Fan-out and discard at a copyable wire

    The comultiplication and counit of the wire supply, read as
    morphisms of [P]: the positive converses of [no_linear_fanout]
    and [no_linear_discard]. *)

Definition copyable_fanout {c : Colour} (H : copyable c = true) :
  wire (P := P) c ~{P}~>
    ((wire (P := P) c ⨂[MBc P] wire (P := P) c)%object) :=
  @ccomon_delta P (@cprop_symmetric Colour P) (wire (P := P) c)
    (@supply_wire Colour P copyable SS c H).

Definition copyable_discard {c : Colour} (H : copyable c = true) :
  wire (P := P) c ~{P}~> @I P (MBc P) :=
  @ccomon_epsilon P (@cprop_symmetric Colour P) (wire (P := P) c)
    (@supply_wire Colour P copyable SS c H).

(** *** Determinism at all-copyable boundaries

    Relative to the derived boundary supplies [supply_list], a
    morphism is DETERMINISTIC when it is a comonoid homomorphism
    between them — the two Cho–Jacobs preservation squares, packaged
    by [ComonoidHom].  The [ComonoidHom] kit of
    [Theory/Algebra/Comonoid/Hom.v] instantiates to the expected laws:
    identities are deterministic, deterministic morphisms compose, and
    determinism respects [≈]. *)

Definition sel_deterministic {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) : Type :=
  @ComonoidHom P (MBc P) ⟦cs⟧c ⟦ds⟧c
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
       (@supply_list Colour P copyable SS cs Hc))
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦ds⟧c
       (@supply_list Colour P copyable SS ds Hd))
    f.

Lemma sel_deterministic_id {cs : list Colour}
  (Hc : all_copyable copyable cs) :
  sel_deterministic Hc Hc (@id P ⟦cs⟧c).
Proof.
  exact (@ComonoidHom_id P (MBc P) ⟦cs⟧c
           (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
              (@supply_list Colour P copyable SS cs Hc))).
Qed.

Lemma sel_deterministic_comp {cs ds es : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (He : all_copyable copyable es)
  (f : ⟦ds⟧c ~{P}~> ⟦es⟧c) (g : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  sel_deterministic Hd He f ->
  sel_deterministic Hc Hd g ->
  sel_deterministic Hc He (f ∘ g).
Proof.
  exact (@ComonoidHom_comp P (MBc P) ⟦cs⟧c ⟦ds⟧c ⟦es⟧c _ _ _ f g).
Qed.

Lemma sel_deterministic_equiv {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f g : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  f ≈ g -> sel_deterministic Hc Hd f -> sel_deterministic Hc Hd g.
Proof.
  exact (@ComonoidHom_equiv P (MBc P) ⟦cs⟧c ⟦ds⟧c _ _ f g).
Qed.

(** The two Cho–Jacobs squares, projected out in the copy/discard
    vocabulary of [Supply.v]: copying after [f] is running [f] twice
    on a copy, and discarding after [f] is discarding. *)

Lemma sel_deterministic_scopy {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  sel_deterministic Hc Hd f ->
  @scopy Colour P copyable SS ds Hd ∘ f
    ≈ (f ⨂[MBc P] f) ∘ @scopy Colour P copyable SS cs Hc.
Proof.
  intro D.
  exact (@hom_delta P (MBc P) ⟦cs⟧c ⟦ds⟧c _ _ f D).
Qed.

Lemma sel_deterministic_sdiscard {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  sel_deterministic Hc Hd f ->
  @sdiscard Colour P copyable SS ds Hd ∘ f
    ≈ @sdiscard Colour P copyable SS cs Hc.
Proof.
  intro D.
  exact (@hom_epsilon P (MBc P) ⟦cs⟧c ⟦ds⟧c _ _ f D).
Qed.

End SelectiveFanOut.

Arguments copyable_fanout {Colour P copyable SS c} H : assert.
Arguments copyable_discard {Colour P copyable SS c} H : assert.
Arguments sel_deterministic {Colour P copyable SS cs ds} Hc Hd f : assert.
Arguments sel_deterministic_id {Colour P copyable SS cs} Hc : assert.
