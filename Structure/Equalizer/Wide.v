Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Wide equalizers, elementarily: wide forks and descent *)

(* nLab:      https://ncatlab.org/nlab/show/equalizer
   nLab:      https://ncatlab.org/nlab/show/wide+pullback
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   Mac Lane presents the coequalizer as a universal arrow over the walking
   parallel pair and then remarks that coequalizers of an ARBITRARY SET of
   parallel maps a → b are defined in the same way (Categories for the
   Working Mathematician, 2nd ed., §III.3, pp. 64-65).  This file and its
   dual [Structure/Coequalizer/Wide.v] carry out "the same way" on the
   limit side.  Given a family f : I → (x ~> y), a wide equalizer is an
   object q with a map e : q ~> x on which all the f i agree,

       ∀ i j,  f i ∘ e ≈ f j ∘ e,

   universal with that property: every h : z ~> x on which they agree
   factors uniquely through e.  Eckmann and Hilton defined equalizers for
   arbitrary families from the start, under the name "left equalizers"
   (Mathematische Annalen 151, 1963); the binary case of
   [Structure/Equalizer/Fork.v] is I = 2.

   WHAT IS DELIVERED, AND AT WHAT STRENGTH.

     - [IsWideEqualizer], the elementary record, is the literal
       generalization of [IsEqualizer]: one equation-family field and one
       descent field, no extra data.
     - [wide_equalizer_monic] and [wide_equalizer_unique] are the wide forms
       of [equalizer_monic] and [equalizer_unique].  Neither consumes an
       inhabitant of I; both hold for EVERY index type, empty included.
     - [wide_limit_equalizes] reads the fork equations off a limit.  It also
       needs no inhabitant.
     - The two ROUND TRIPS, [wide_equalizer_is_equalizer] and
       [is_wide_equalizer_limit], DO take an explicit inhabitant [i0 : I].
       They live in a section that fixes one.  For [is_wide_equalizer_limit]
       — the ELEMENTARY-to-LIMIT direction — that hypothesis is PROVED
       NECESSARY rather than assumed (see below).  For
       [wide_equalizer_is_equalizer], the LIMIT-to-ELEMENTARY direction, it
       is ASSUMED: nothing here refutes an unpointed version of it, and none
       is claimed.  The same asymmetry holds on the coequalizer side.

   WHY THE ROUND TRIPS NEED A POINT OF THE INDEX, and why that is a fact
   about the mathematics rather than about this proof.  A cone over
   [AWide fs] with apex z is a PAIR of legs, one into x and one into y,
   subject to [∀ i, f i ∘ legX ≈ legY].  When I is inhabited the second leg
   is determined by the first, and the cone condition collapses to the fork
   equations — which is what makes the elementary record equivalent to the
   limit.  When I is EMPTY the second leg is unconstrained, so a cone is
   just a pair of maps and the limit over the shape is the binary PRODUCT
   of x and y (an orientation, not a theorem — that identification is NOT
   formalized), while the elementary record, whose fork condition is then
   vacuous, is satisfied by [e := id[x]] and so pins down x itself.  The
   two notions come apart exactly there, and THAT is what is proved.  The
   binary donor never meets this because its index is [bool], and its
   [fork_legs] silently uses the distinguished member f:
   [fork_legs h ParY := f ∘ h].

   The necessity is machine-checked in three steps, all at the end of this
   file.  [wide_empty_id_IsWideEqualizer] exhibits the identity as an
   elementary wide equalizer over an empty index;
   [wide_unpointed_round_trip_gives_hom] shows that an unpointed round trip
   would therefore manufacture an arrow x ~> y out of nothing; and
   [wide_round_trip_needs_point] instantiates that at the walking arrow
   [Instance/Two.v]'s [_2], whose hom-set [TwoY ~> TwoX] is empty, deriving
   False.  So no reformulation of the PROOF removes the hypothesis; only a
   different elementary record (one carrying the second leg as data) would,
   and that record is not built here.

   UNIVERSES, measured in the constraint blocks rather than read off the
   binders (reproduce with [Set Printing Universes. About
   wide_equalizer_is_equalizer. About is_wide_equalizer_limit.]).  Both
   round trips come out over [C : Category@{u u0 u0}] with [I : Type@{u1}]
   and [u0 = u1]: the ambient hom and proof universes are identified, as
   they already are in the binary donor ([equalizer_is_equalizer] is over
   the same [Category@{u u0 u0}]), and the INDEX universe is identified
   with them as well.  Where the second identification ENTERS is measured,
   and it is NOT inherited from [Structure/Cone.v]: with the index and hom
   universes declared SEPARATELY, forming [Cone (AWide fs)] and writing
   [cone_leg N ParX] both yield only the BOUND [u1 <= u0], as do this
   file's own cone-building constants [wfork_cone],
   [is_wide_equalizer_cone] and [is_wide_equalizer_cone_ump].  The
   identification first appears at [wide_limit_equalizer_desc] below and at
   the assembly of the [Limit] record, both local to this file.  (An
   earlier draft of this header offered the [cone_leg] probe as evidence of
   inheritance; that probe collapses the two universes only under
   minimization, and the claim was wrong.  Whether any rearrangement of
   these proofs avoids the identification is UNTESTED.)  It also
   costs a consumer nothing, since a type at level l can be typed at any
   level above l, so the identification is satisfiable exactly when the
   [<=] form would be.  [IsWideEqualizer] ITSELF has an EMPTY constraint
   block, with the index universe free.

   CONSUMER.  [Theory/WeaklyInitial/Wide.v] runs Freyd's initial-object
   construction over [HasWideEqualizers], equalizing all endomorphisms of a
   product at once; it uses [wfork_eq] and [wide_equalizer_monic] and needs
   neither round trip, so it never meets the [i0] hypothesis.  It is an
   ADDITIVE second theorem: [Theory/WeaklyInitial.v] is untouched.

   NOT DELIVERED.  No second, leg-carrying elementary record that would
   round-trip unconditionally.  No identification of the limit over an
   empty-index wide shape with a binary product — the sharpness argument
   goes through an empty hom-set instead and needs no such theorem.  No
   [HasWideEqualizers] instance for any concrete category (the class is
   declared, not inhabited; the tree's only [HasEqualizers] inhabitant is
   [Sets_HasEqualizers], derived from completeness in Adjunction/GAFT.v,
   and no wide analogue is derived — so [Theory/WeaklyInitial/Wide.v] is a
   conditional exactly as its donor is).  No wide analogue of
   [Structure/Limit/Unique.v]'s leg-carrying essential
   uniqueness — [wide_equalizer_unique] delivers a bare [≅], exactly as its
   binary donor does.  No preservation or creation statements.  No
   comparison between the wide equalizer at I := bool and the binary
   equalizer of [Structure/Equalizer/Fork.v]: the SHAPES are compared, in
   [Instance/Parallel/Wide.v]'s [WideParallel_bool_Parallel] and
   [AWide_bool_APair], but the two elementary records are not related by
   any passage here. *)

(* The wide equalizer of a diagram of shape [WideParallel I]: a terminal
   cone, exactly as [Structure/Equalizer.v]'s [Equalizer] is over the
   two-arrow shape. *)
Definition WideEqualizer {C : Category} {I : Type} (F : WideParallel I ⟶ C) :=
  Limit F.

(* The elementary universal property: [e] equalizes the whole family at q,
   and every map h into x that the family agrees on factors uniquely
   through e. *)
Record IsWideEqualizer {C : Category} {I : Type} {x y : C}
  (fs : I → x ~> y) (q : C) (e : q ~> x) := {
  (* every member of the family absorbs e in the same way *)
  wfork_eq : ∀ i j : I, fs i ∘ e ≈ fs j ∘ e;

  (* universal property: every jointly forking map h factors uniquely *)
  weq_desc {z} (h : z ~> x) (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
    ∃! u : z ~> q, e ∘ u ≈ h
}.

Arguments wfork_eq {_ _ _ _ _ _ _} _ _ _.
Arguments weq_desc {_ _ _ _ _ _ _} _ {_} _ _.

(* A category has all wide equalizers when every family of parallel arrows
   carries an elementary wide equalizer.  The index [Type] is a universe
   PARAMETER of the class, not a quantifier over every universe, exactly as
   for [Structure/Limit/Product.v]'s indexed products; a consumer whose
   index is a hom-type instantiates it there. *)
Class HasWideEqualizers (C : Category) := {
  wide_equalizer {I : Type} {x y : C} (fs : I → x ~> y) :
    ∃ (q : C) (e : q ~> x), IsWideEqualizer fs q e
}.

Section WideEqualizerLimit.

Context {C : Category}.
Context {I : Type}.
Context {x y : C}.
Context (fs : I → x ~> y).

(* Abbreviations for the diagram and its shape; these are notations, so the
   statements below are literally about [AWide fs] and [WideParallel I]. *)
Local Notation WFam := (AWide fs).
Local Notation WShape := (WideParallel I).

(** ** Wide equalizing maps are monomorphisms *)

(* The binary argument verbatim: both factorizations of e ∘ g1 agree with
   the canonical one, so descent uniqueness cancels e on the left.  No
   member of the family is ever named, so no inhabitant of I is needed. *)
Lemma wide_equalizer_monic {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : Monic e.
Proof.
  constructor.
  intros z g1 g2 Hg.
  assert (Hfork : ∀ i j : I, fs i ∘ (e ∘ g1) ≈ fs j ∘ (e ∘ g1)).
  { intros i j.
    rewrite !comp_assoc.
    rewrite (wfork_eq E i j).
    reflexivity. }
  transitivity (unique_obj (weq_desc E (e ∘ g1) Hfork)).
  - symmetry.
    apply (uniqueness (weq_desc E (e ∘ g1) Hfork)).
    reflexivity.
  - apply (uniqueness (weq_desc E (e ∘ g1) Hfork)).
    symmetry.
    exact Hg.
Qed.

(** ** Wide equalizers are unique up to isomorphism *)

Lemma wide_equalizer_unique {q1 q2 : C} {e1 : q1 ~> x} {e2 : q2 ~> x}
  (E1 : IsWideEqualizer fs q1 e1) (E2 : IsWideEqualizer fs q2 e2) :
  q1 ≅ q2.
Proof.
  pose proof (weq_desc E2 e1 (wfork_eq E1)) as D12.
  pose proof (weq_desc E1 e2 (wfork_eq E2)) as D21.
  pose proof (weq_desc E1 e1 (wfork_eq E1)) as D11.
  pose proof (weq_desc E2 e2 (wfork_eq E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D22).
      apply id_right.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D11).
      apply id_right.
Defined.

(** ** From the limit presentation to the fork equations *)

(* The limit leg over [ParX] is equalized by the whole family: every member
   pushes it to the leg over [ParY], by leg coherence at that member — the
   arrow [i] of the shape IS the index, and [fmap[AWide fs] i] IS [fs i].
   No inhabitant of I is needed: the statement quantifies over i and j. *)
Lemma wide_limit_equalizes (L : WideEqualizer WFam) :
  ∀ i j : I,
    fs i ∘ limit_leg (limit_is_alimit L) ParX
      ≈ fs j ∘ limit_leg (limit_is_alimit L) ParX.
Proof.
  intros i j.
  transitivity (limit_leg (limit_is_alimit L) ParY).
  - exact (limit_leg_coherence (limit_is_alimit L)
             (i : ParX ~{WShape}~> ParY)).
  - symmetry.
    exact (limit_leg_coherence (limit_is_alimit L)
             (j : ParX ~{WShape}~> ParY)).
Qed.

(** ** The round trips, over a chosen member of the family *)

Section Pointed.

(* A chosen index.  This is the hypothesis the two round trips need, and
   the section is exactly its scope: everything above holds without it, and
   the sharpness results below show nothing weaker will do. *)
Context (i0 : I).

(* The legs of the cone induced by a jointly forking map h: the leg over
   [ParX] is h itself, the leg over [ParY] the common composite through the
   chosen member. *)
Definition wfork_legs {z : C} (h : z ~> x) (p : ParObj) :
  z ~{C}~> WFam p :=
  match p return (z ~{C}~> WFam p) with
  | ParX => h
  | ParY => fs i0 ∘ h
  end.

(* Leg coherence.  This statement is definitionally the [cone_coherence]
   field of an [ACone] over [AWide fs]. *)
Lemma wfork_legs_coherence {z : C} (h : z ~> x)
  (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
  ∀ (a b : ParObj) (k : a ~{WShape}~> b),
    fmap[WFam] k ∘ wfork_legs h a ≈ wfork_legs h b.
Proof.
  intros a b k.
  destruct a, b; simpl in *.
  - (* the identity arrow on ParX *)
    apply id_left.
  - (* the arrow k : I, sent to fs k *)
    exact (Hh k i0).
  - (* an arrow ParY ~> ParX: refuted by the empty hom-set *)
    destruct k.
  - (* the identity arrow on ParY *)
    apply id_left.
Qed.

Definition wfork_cone {z : C} (h : z ~> x)
  (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) : Cone WFam :=
  @Build_Cone WShape C WFam z
    (@Build_ACone WShape C z WFam
       (wfork_legs h) (wfork_legs_coherence h Hh)).

(* Descent through the limit apex. *)
Lemma wide_limit_equalizer_desc (L : WideEqualizer WFam)
  {z : C} (h : z ~> x) (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
  ∃! u : z ~> L, limit_leg (limit_is_alimit L) ParX ∘ u ≈ h.
(* Lib.v sets [Default Proof Using "Type"], which keeps only the section
   variables occurring in the STATEMENT.  This is the ONE proof in the
   section that reaches for [i0] without its statement mentioning it — the
   others go through [wfork_legs], whose body carries the dependency. *)
Proof using All.
  unshelve eapply Build_Unique.
  - exact (limit_med (limit_is_alimit L) (wfork_cone h Hh)).
  - exact (limit_med_commutes
             (limit_is_alimit L) (wfork_cone h Hh) ParX).
  - intros v Hv.
    refine (limit_med_unique
              (limit_is_alimit L) (wfork_cone h Hh) v _).
    intros p.
    destruct p.
    + exact Hv.
    + (* the ParY leg follows from the ParX leg via coherence at i0 *)
      rewrite <- (limit_leg_coherence (limit_is_alimit L)
                    (i0 : ParX ~{WShape}~> ParY)).
      rewrite <- comp_assoc.
      rewrite Hv.
      reflexivity.
Qed.

(* A limit of [AWide fs] is an elementary wide equalizer at its apex. *)
Definition wide_equalizer_is_equalizer (L : WideEqualizer WFam) :
  IsWideEqualizer fs L (limit_leg (limit_is_alimit L) ParX) :=
  {| wfork_eq  := wide_limit_equalizes L
   ; weq_desc  := fun z h Hh => wide_limit_equalizer_desc L h Hh |}.

(** ** From the elementary presentation back to the limit *)

Definition is_wide_equalizer_cone {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : Cone WFam :=
  wfork_cone e (wfork_eq E).

(* The universal property of that cone; definitionally the [ump_limits]
   field of the limit whose limit cone is [is_wide_equalizer_cone]. *)
Lemma is_wide_equalizer_cone_ump {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) (N : Cone WFam) :
  ∃! u : vertex_obj[N] ~> q,
    ∀ p : ParObj, wfork_legs e p ∘ u ≈ cone_leg N p.
Proof.
  assert (HX : ∀ i : I, fs i ∘ cone_leg N ParX ≈ cone_leg N ParY).
  { intro i.
    exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _
             (i : ParX ~{WShape}~> ParY)). }
  assert (Hfs : ∀ i j : I, fs i ∘ cone_leg N ParX ≈ fs j ∘ cone_leg N ParX).
  { intros i j.
    rewrite (HX i).
    rewrite (HX j).
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (weq_desc E (cone_leg N ParX) Hfs)).
  - intros p.
    destruct p.
    + exact (unique_property (weq_desc E (cone_leg N ParX) Hfs)).
    + (* the leg over ParY: (fs i0 ∘ e) ∘ u ≈ nY via the ParX triangle *)
      simpl.
      rewrite <- comp_assoc.
      rewrite (unique_property (weq_desc E (cone_leg N ParX) Hfs)).
      exact (HX i0).
  - intros v Hv.
    apply (uniqueness (weq_desc E (cone_leg N ParX) Hfs)).
    exact (Hv ParX).
Qed.

(* An elementary wide equalizer yields the bundled limit over the wide
   shape. *)
Definition is_wide_equalizer_limit {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : WideEqualizer WFam :=
  {| limit_cone := is_wide_equalizer_cone E
   ; ump_limits := fun N => is_wide_equalizer_cone_ump E N |}.

End Pointed.

(** ** The inhabitant is necessary, not merely convenient *)

(* Over an empty index the fork condition is vacuous, so the identity of x
   satisfies the elementary record — descent is then just [id_left], and
   needs no emptiness at all. *)
Lemma wide_empty_id_IsWideEqualizer (Hempty : I → False) :
  IsWideEqualizer fs x id[x].
Proof.
  unshelve refine {| wfork_eq := _ |}.
  - intros i j; destruct (Hempty i).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact h.
    + apply id_left.
    + intros v Hv.
      rewrite <- Hv.
      apply id_left.
Defined.

End WideEqualizerLimit.

(* Consequently an UNPOINTED round trip — one turning any elementary wide
   equalizer into a limit of the same diagram AT THAT SAME APEX, with no
   member of the family in hand — would produce an arrow x ~> y out of
   nothing: apply it to the identity above and read off the limit leg over
   [ParY].  The apex is pinned by the hypothesis below ([IsALimit (AWide fs)
   q]), which makes the refuted principle strictly stronger than the literal
   unpointed form of what is delivered, [is_wide_equalizer_limit] returning a
   [WideEqualizer WFam] whose apex its type does not pin. *)
Definition wide_unpointed_round_trip_gives_hom
  {C : Category} {I : Type} {x y : C} (fs : I → x ~> y)
  (Hempty : I → False)
  (RT : ∀ (q : C) (e : q ~> x),
          IsWideEqualizer fs q e → IsALimit (AWide fs) q) :
  x ~{C}~> y :=
  limit_leg (RT x id[x] (wide_empty_id_IsWideEqualizer fs Hempty)) ParY.

(* And that is refutable.  The witness is the walking arrow: [_2] has no
   arrow from [TwoY] to [TwoX] at all, so an unpointed round trip over the
   empty family [TwoY ⇉ TwoX] would produce an inhabitant of an empty
   hom-set.  This is the sharpness statement for the [i0] hypothesis of the
   section above; the general shape of the refuted principle is
   [wide_unpointed_round_trip_gives_hom], and this is one instance of it. *)
Definition two_empty_family : Empty_set → (TwoY ~{_2}~> TwoX) :=
  fun i => match i with end.

Theorem wide_round_trip_needs_point :
  (∀ (q : _2) (e : q ~{_2}~> TwoY),
     IsWideEqualizer two_empty_family q e
     → IsALimit (AWide two_empty_family) q) → False.
Proof.
  intro RT.
  exact (TwoHom_Y_X_absurd
           (wide_unpointed_round_trip_gives_hom two_empty_family
              (fun i => match i with end) RT)).
Qed.
