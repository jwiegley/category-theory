Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The cokernel pair of [Sets] is a cokernel pair *)

(* nLab: https://ncatlab.org/nlab/show/cokernel+pair

   Mac Lane, CWM 2nd ed., §III.3 p. 66 and §III.4 Exercise 4 p. 72; Fong
   and Spivak, *Seven Sketches*, §7.2.1 Definition 7.5.

   Instance/Sets.v:448-505 already builds, for f : A ~> B in [Sets], the
   setoid [CKSetoid f] — two copies of B glued exactly along the image of
   f — with two inclusions [ck_left]/[ck_right] and the equation
   [ck_agree : ck_left ∘ f ≈ ck_right ∘ f].  It was built to probe an
   epimorphism, and it stops there: NO universal property of it is proved
   in that file, the word "pushout" occurs there only at :116 in an
   unrelated header line, and it is nowhere related to
   Instance/Sets/Pushout.v's [Sets_HasPushouts], which sits in a different
   file and glues by a five-constructor inductive closure instead.

   This file proves the universal property, so that the pre-existing
   construction is exhibited as a genuine cokernel pair —
   [sets_ck_IsCokernelPair] — and hence as a pushout square in the sense
   of Theory/Morphisms/CokernelPair.v.  Nothing in Instance/Sets.v is
   changed; the mediator is the copairing of the two competing maps, and
   the ONLY step with content is its respectfulness at the gluing case,
   where the image witness supplies the preimage that lets the coequalizing
   hypothesis be applied.  As everywhere in [Sets], `∃` is [sigT], so that
   preimage is DATA and no choice principle is used.

   ------------------------------------------------------------------
   ** What is proved, and at what strength

   - [sets_ck_ump], [sets_ck_IsCokernelPair]: the universal property, and
     the apex-pinned identification.  The two triangles hold POINTWISE ON
     THE NOSE — [sets_ck_med_left]/[sets_ck_med_right] are [reflexivity]
     at every point, the mediator being defined by case analysis on the
     sum — and this is recorded as two [eq_refl] Examples on the
     underlying FUNCTIONS ([sets_ck_med_inl], [sets_ck_med_inr]).  What
     does NOT hold strictly is the equality of MORPHISMS: the composite
     [u ∘ ck_left] rebuilds its [proper_morphism] certificate, so the
     triangles are [≈] and not [eq].  That negative is pinned in
     Test/ProbeCokernelPair.v.

   - Non-vacuity BOTH WAYS, on Instance/Sets.v's own two-element witness
     pair, so that neither side of the characterization is empty:

       * [collapse : bool ~> unit] is surjective, hence epic, and its
         cokernel-pair legs are proved to agree
         ([sets_collapse_ckp_trivial]), so the identity square on it IS a
         pushout ([sets_collapse_pushout_square]).

       * [pick_true : unit ~> bool] misses [false], and its cokernel-pair
         legs are proved DISTINCT by hand ([sets_pick_true_ckp_nontrivial])
         — at [false] the gluing relation would demand a preimage, i.e.
         [true = false].  Hence the identity square on it is NOT a pushout
         ([sets_pick_true_not_pushout_square]).

     The second witness is the load-bearing one: it is what shows the
     general biconditional is not vacuously true, and it CROSS-CHECKS the
     general theory — [sets_pick_true_not_epic_via_ckp] re-derives
     Instance/Sets.v's [pick_true_not_epic] from the distinctness of the
     legs through [epic_iff_cokernel_pair_trivial], by a route that shares
     no proof text with the original.

   ------------------------------------------------------------------
   ** Universes, measured in the constraint blocks

   [sets_ck_IsCokernelPair@{h p}] and [sets_ck_ump@{h p}] carry two
   universe parameters.  Beyond [Sets]'s own [p < h] ([Sets@{o so} :
   Category@{so o o}] with [o < so], the carriers at [o]) the block records
   only bounds INHERITED verbatim — [p <= compose.u0], [p <= compose.u1],
   [p <= compose.u2], [p <= ID.u0], each of which [Sets], [CKSetoid],
   [ck_left] and [ck_agree] display identically.  (An earlier draft called
   [p < h] "the single constraint"; there are five lines.  The substance is
   unaffected: nothing here narrows the shape, and the identification is
   polymorphic in the carrier universe [p].)

   The two-element WITNESSES do pin, and only they:
   [sets_pick_true_not_pushout_square@{u}] displays
   [bool_setoid_object@{Set Set}] with [Set < u], because
   Instance/Sets.v's [bool_setoid_object] has a [bool] carrier.  That is
   the ordinary concrete-witness price and it is confined to the
   non-vacuity section.

   ------------------------------------------------------------------
   ** NOT DELIVERED (scoped)

   - [CKSetoid f] is NOT identified with the chosen pushout of
     [Sets_HasPushouts] (Instance/Sets/Pushout.v).  The two are different
     objects — a closed-form relation against an inductive closure — and
     the comparison would need a general "any two pushouts of one span are
     uniquely isomorphic" statement, which Theory/Morphisms/CokernelPair.v
     deliberately does not provide.  No claim is made here about whether
     they are isomorphic; the question is simply not addressed.

   - The [Top] and pointed-sets cokernel pairs (Instance/Top.v:579-726,
     Instance/Sets/Pointed.v:401-523) are NOT given universal properties.
     Only the [Sets] one is treated here.

   - No [Sets]-specific statement about [Monic] and kernel pairs. *)

Section SetsCokernelPair.

Universes h p.
Context {A B : SetoidObject@{p p}}.
Context (f : A ~{Sets@{p h}}~> B).

(** ** The mediator *)

(* The copairing of two competing maps: on the left copy use q1, on the
   right copy use q2. *)
Definition sets_ck_fun {Q : SetoidObject@{p p}}
           (q1 q2 : B ~{Sets@{p h}}~> Q)
  : carrier (CKSetoid f) → carrier Q :=
  λ s, match s with
       | Datatypes.inl b => q1 b
       | Datatypes.inr b => q2 b
       end.

(* Respectfulness.  Three of the four cases are [proper_morphism] of q1 or
   q2; the two GLUING cases are the whole content, and they are where the
   coequalizing hypothesis is spent: the image witness names a preimage
   [a] with [f a ≈ x], at which [q1] and [q2] agree by hypothesis. *)
Lemma sets_ck_respects {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f)
      (s t : carrier (CKSetoid f)) :
  ckrel f s t → sets_ck_fun q1 q2 s ≈ sets_ck_fun q1 q2 t.
Proof.
  destruct s as [xs|xs], t as [xt|xt]; simpl.
  - intro E; now rewrite E.
  - intros [E [a Ha]].
    (* q1 xs ≈ q1 (f a) ≈ q2 (f a) ≈ q2 xs ≈ q2 xt *)
    transitivity (q1 (f a)); [ now rewrite Ha |].
    transitivity (q2 (f a)); [ exact (Hc a) |].
    rewrite Ha; now rewrite E.
  - intros [E [a Ha]].
    transitivity (q2 (f a)); [ now rewrite Ha |].
    transitivity (q1 (f a)); [ symmetry; exact (Hc a) |].
    rewrite Ha; now rewrite E.
  - intro E; now rewrite E.
Qed.

Program Definition sets_ck_med {Q : SetoidObject@{p p}}
        (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f)
  : CKSetoid f ~{Sets@{p h}}~> Q :=
  {| morphism := sets_ck_fun q1 q2 |}.
Next Obligation.
  repeat intro; now apply sets_ck_respects.
Qed.

(** ** The universal property *)

(* Both triangles are POINTWISE [reflexivity]: the mediator is defined by
   case analysis on the sum, and each leg lands in exactly one case. *)
Lemma sets_ck_med_left {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  sets_ck_med q1 q2 Hc ∘[Sets@{p h}] ck_left f ≈ q1.
Proof. intro b; reflexivity. Qed.

Lemma sets_ck_med_right {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  sets_ck_med q1 q2 Hc ∘[Sets@{p h}] ck_right f ≈ q2.
Proof. intro b; reflexivity. Qed.

Lemma sets_ck_ump (Q : SetoidObject@{p p})
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  ∃! u : CKSetoid f ~{Sets@{p h}}~> Q,
    u ∘[Sets@{p h}] ck_left f ≈ q1 ∧ u ∘[Sets@{p h}] ck_right f ≈ q2.
Proof.
  unshelve refine {| unique_obj := sets_ck_med q1 q2 Hc |}.
  - split; [ apply sets_ck_med_left | apply sets_ck_med_right ].
  - intros v [Hv1 Hv2] s.
    destruct s as [b|b]; simpl.
    + symmetry; exact (Hv1 b).
    + symmetry; exact (Hv2 b).
Qed.

(* Instance/Sets.v's construction IS a cokernel pair.  The commuting
   equation is that file's own [ck_agree], reused rather than reproved. *)
Definition sets_ck_IsCokernelPair
  : IsCokernelPair (C:=Sets@{p h}) f (CKSetoid f) (ck_left f) (ck_right f) :=
  @Build_IsPushoutSquare Sets@{p h} A B B f f
    (CKSetoid f) (ck_left f) (ck_right f) (ck_agree f) sets_ck_ump.

End SetsCokernelPair.

(** ** The two triangles hold on the nose on the underlying functions *)

(* The mediator's value at either injection is the corresponding competing
   map applied to the point — Leibniz, not merely [≈].  What is NOT strict
   is the equality of MORPHISMS (see Test/ProbeCokernelPair.v). *)
Example sets_ck_med_inl@{h p} {A B Q : SetoidObject@{p p}}
        (f : A ~{Sets@{p h}}~> B) (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) (b : carrier B) :
  sets_ck_med f q1 q2 Hc (Datatypes.inl b) = q1 b := eq_refl.

Example sets_ck_med_inr@{h p} {A B Q : SetoidObject@{p p}}
        (f : A ~{Sets@{p h}}~> B) (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) (b : carrier B) :
  sets_ck_med f q1 q2 Hc (Datatypes.inr b) = q2 b := eq_refl.

(** ** Non-vacuity, both ways *)

(* Instance/Sets.v's own witness pair between the singleton and the
   two-element setoid is used, so no new object is introduced. *)

(** *** The epic side: [collapse] is surjective, so its legs agree *)

Lemma sets_collapse_surjective :
  ∀ u : carrier unit_setoid_object, ∃ b, collapse b ≈ u.
Proof. intro u; exists true; destruct u; reflexivity. Qed.

Definition sets_collapse_epic : Epic collapse :=
  surjective_implies_epic collapse sets_collapse_surjective.

(* Its cokernel pair is trivial: the two legs of [CKSetoid collapse]
   coincide.  Obtained through the general theorem, not by computation. *)
Definition sets_collapse_ckp_trivial :
  ck_left collapse ≈ ck_right collapse :=
  fst (epic_iff_cokernel_pair_trivial (C:=Sets) collapse
         (is_pushout_square_pushout (sets_ck_IsCokernelPair collapse)))
      sets_collapse_epic.

(* And the identity square on it is a pushout. *)
Definition sets_collapse_pushout_square :
  IsPushoutSquare (C:=Sets) collapse collapse unit_setoid_object id id :=
  fst (epic_iff_pushout_square collapse) sets_collapse_epic.

(** *** The non-epic side: [pick_true] misses [false] *)

(* The two legs of [CKSetoid pick_true] are DISTINCT, proved by hand: at
   [false] the gluing relation would supply a preimage of [false] under
   [pick_true], i.e. a proof that [true = false]. *)
Lemma sets_pick_true_ckp_nontrivial :
  ck_left pick_true ≈ ck_right pick_true → False.
Proof.
  intro E.
  (* [E false] inhabits [ckrel pick_true (inl false) (inr false)], whose
     second component is the image witness. *)
  destruct (E false) as [_ [u Hu]].
  destruct u.
  exact (Bool.diff_true_false Hu).
Qed.

(* Hence the identity square on [pick_true] is NOT a pushout: were it one,
   [pick_true] would be epic and the legs would have to agree. *)
Lemma sets_pick_true_not_pushout_square :
  IsPushoutSquare (C:=Sets) pick_true pick_true bool_setoid_object id id
  → False.
Proof.
  intro H.
  apply sets_pick_true_ckp_nontrivial.
  exact (fst (epic_iff_cokernel_pair_trivial (C:=Sets) pick_true
                (is_pushout_square_pushout
                   (sets_ck_IsCokernelPair pick_true)))
             (snd (epic_iff_pushout_square pick_true) H)).
Qed.

(* Cross-check: Instance/Sets.v's [pick_true_not_epic] re-derived through
   the general characterization, by a route sharing no proof text with the
   original (that one probes with [id] against [pick_true ∘ collapse];
   this one goes through the cokernel pair). *)
Lemma sets_pick_true_not_epic_via_ckp : Epic pick_true → False.
Proof.
  intro E.
  apply sets_pick_true_ckp_nontrivial.
  exact (fst (epic_iff_cokernel_pair_trivial (C:=Sets) pick_true
                (is_pushout_square_pushout
                   (sets_ck_IsCokernelPair pick_true))) E).
Qed.
