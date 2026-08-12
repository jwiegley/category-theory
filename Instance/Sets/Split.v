Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * A section/retraction pair in Sets that is not an isomorphism *)

(* nLab:      https://ncatlab.org/nlab/show/split+monomorphism
   nLab:      https://ncatlab.org/nlab/show/split+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   Fong and Spivak, "Seven Sketches in Compositionality" (CUP, 2019), §3.2.5
   Example 3.34, printed p. 89.  CITED BY LOCATION; the printed text was not
   consulted and no sentence of it is reproduced here.  The library's book
   catalog describes the example as exhibiting a one-sided inverse pair in
   sets and observing that neither map is an isomorphism
   (doc/plan/books/ledger.tsv, id 7sketches:3.2.5:example3.34).

   Theory/Morphisms/Classes.v arranges the morphism classes in the inclusion
   diagram

       Iso ⊆ SplitMono ⊆ Mono
       Iso ⊆ SplitEpi  ⊆ Epi

   and proves all four inclusions ([split_mono_in_mono]:51,
   [split_epi_in_epi]:58, [iso_in_split_mono]:66, [iso_in_split_epi]:77).
   Nothing there says any inclusion is STRICT, and showing Iso ⊆ SplitMono
   proper needs an actual split mono with no inverse.  The tree did not have
   one for [Sets].  Construction/Karoubi.v:226 manufactures splittings
   generically ([karoubi_idem_splits]), but only from a GIVEN idempotent, and
   never exhibits one that is provably not an identity, so the
   non-invertibility conclusion is never drawn there.  The nearest concrete
   pair, [pick_true]/[collapse] at Instance/Sets.v:497,500, is built to refute
   the cancellation converses (Mac Lane §I.5 Exercise 1) and is not carried as
   far as invertibility.

   The pair below separates both classes at once: a two-element setoid
   included into a three-element one, and a retraction folding the extra
   point back.  One composite is the identity, the other provably is not, and
   non-invertibility is settled by evaluating at the extra point. *)

(* ------------------------------------------------------------------------ *)
(** ** The two objects *)

(* The two-element setoid is the one Instance/Sets.v:493 already carries;
   this is a notation for it, not a second copy. *)
Notation sets_two := bool_setoid_object.

(* The three-element setoid: [option bool] under Coq's `=`, via [eq_Setoid]
   (Lib/Setoid.v:65).  The carriers are chosen so that every case analysis
   below is a plain [destruct] and every refutation a plain [discriminate]. *)
Definition sets_three@{t u} : SetoidObject@{t u} :=
  {| carrier := option bool ; is_setoid := eq_Setoid@{t} (option bool) |}.

(* The carriers really do have two and three inhabitants, and both halves of
   that claim are proved: the enumerations are exhaustive, and the listed
   values are pairwise distinct.  Neither half implies the other -- an
   exhaustive list is only an upper bound on the count -- so the packages
   [sets_two_card] and [sets_three_card] below carry them together.

   Distinctness is stated with `=`, and that is the right relation rather
   than a lapse from the library's `≈` discipline: these are equations
   between ELEMENTS of a carrier, not between morphisms, and both objects are
   DISCRETE -- [sets_three] carries [eq_Setoid] (Lib/Setoid.v:65) and
   [bool_setoid_object] (Instance/Sets.v:493) carries that same record
   written out -- so `=` IS the equivalence of the object, and refuting it
   refutes equality in [Sets] and not merely equality of representatives. *)

Lemma sets_two_enum (b : bool) : (b = true) ∨ (b = false).
Proof. destruct b; [ now left | now right ]. Qed.

Lemma sets_two_distinct : (true = false) → False.
Proof. discriminate. Qed.

Lemma sets_three_enum (o : option bool) :
  (o = None) ∨ (o = Some true) ∨ (o = Some false).
Proof.
  destruct o as [[|] |].
  - right; now left.
  - right; right; reflexivity.
  - now left.
Qed.

Lemma sets_three_distinct :
  ((None = Some true) → False)
  * ((None = Some false) → False)
  * ((Some true = Some false) → False).
Proof. repeat split; discriminate. Qed.

(* The counts, packaged.  The refutations further down re-derive what they
   need by [discriminate] rather than projecting out of these, a
   [discriminate] being shorter than the projection that would replace it. *)

Definition sets_two_card :
  (∀ b : bool, (b = true) ∨ (b = false))
  * ((true = false) → False) :=
  (sets_two_enum, sets_two_distinct).

Definition sets_three_card :
  (∀ o : option bool, (o = None) ∨ (o = Some true) ∨ (o = Some false))
  * (((None = Some true) → False)
     * ((None = Some false) → False)
     * ((Some true = Some false) → False)) :=
  (sets_three_enum, sets_three_distinct).

(* ------------------------------------------------------------------------ *)
(** ** The two maps *)

(* The inclusion is [Some].  The only feature of it the proofs below use is
   that it misses [None]. *)
Program Definition sets_incl23 : sets_two ~{Sets}~> sets_three := {|
  morphism := @Some bool
|}.

(* The retraction undoes [Some] and folds the missed point [None] onto
   [true], so it identifies [None] with [Some true]. *)
Definition option_fold (o : option bool) : bool :=
  match o with
  | Some b => b
  | None   => true
  end.

Program Definition sets_retr32 : sets_three ~{Sets}~> sets_two := {|
  morphism := option_fold
|}.

(* ------------------------------------------------------------------------ *)
(** ** One composite is the identity *)

Lemma sets_retr_incl : sets_retr32 ∘[Sets] sets_incl23 ≈ id{Sets}.
Proof. intro b; now destruct b. Qed.

(* Hence the inclusion is a split mono and the retraction a split epi, both
   witnessed by the SAME equation -- this is the shape Theory/Morphisms.v
   names [Section] and [Retraction]. *)

Definition sets_incl23_Section : Section sets_incl23 :=
  Build_Section _ _ sets_incl23 sets_retr32 sets_retr_incl.

Definition sets_retr32_Retraction : Retraction sets_retr32 :=
  Build_Retraction _ _ sets_retr32 sets_incl23 sets_retr_incl.

(* ------------------------------------------------------------------------ *)
(** ** The other composite provably is not the identity *)

(* At [None] the round trip lands on [Some true]: the retraction folds [None]
   onto [true] and the inclusion cannot recover it. *)

Lemma sets_incl_retr_not_id :
  sets_incl23 ∘[Sets] sets_retr32 ≈ id{Sets} → False.
Proof. intro H; discriminate (H None). Qed.

(* So this splitting's idempotent is not an identity -- which is exactly what
   the generic Karoubi construction never exhibits. *)
Lemma sets_incl_retr_idempotent :
  Idempotent (sets_incl23 ∘[Sets] sets_retr32).
Proof.
  exact (split_pair_idempotent sets_retr32 sets_incl23 sets_retr_incl).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Neither map is an isomorphism *)

(* The inclusion misses [None], so no right inverse can reach it: whatever
   value a candidate inverse returns there, [Some] of it is not [None]. *)

Lemma sets_incl23_not_iso : IsIsomorphism sets_incl23 → False.
Proof. intros [t Hr _]; discriminate (Hr None). Qed.

(* The retraction identifies [None] with [Some true], so no left inverse can
   separate them again. *)

Lemma sets_retr32_not_iso : IsIsomorphism sets_retr32 → False.
Proof.
  intros [u _ Hl].
  pose proof (Hl None) as H1.
  pose proof (Hl (Some true)) as H2.
  simpl in H1, H2.
  rewrite H1 in H2.
  discriminate.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The class inclusions of Theory/Morphisms/Classes.v are strict *)

(* [iso_in_split_mono] and [iso_in_split_epi] send IsoClass into
   SplitMonoClass and SplitEpiClass.  Each package below exhibits a morphism
   in the larger class and refutes its membership in the smaller one, so both
   inclusions are strict. *)

Definition sets_split_mono_not_iso :
  @SplitMonoClass Sets sets_two sets_three sets_incl23
  * (@IsoClass Sets sets_two sets_three sets_incl23 → False) :=
  (sets_incl23_Section, sets_incl23_not_iso).

Definition sets_split_epi_not_iso :
  @SplitEpiClass Sets sets_three sets_two sets_retr32
  * (@IsoClass Sets sets_three sets_two sets_retr32 → False) :=
  (sets_retr32_Retraction, sets_retr32_not_iso).

(* The Seven Sketches example in full: a one-sided inverse pair whose other
   composite provably is not an identity, with neither map invertible. *)
Definition sets_split_pair_not_iso :
  (sets_retr32 ∘[Sets] sets_incl23 ≈ id{Sets})
  * ((sets_incl23 ∘[Sets] sets_retr32 ≈ id{Sets}) → False)
  * (IsIsomorphism sets_incl23 → False)
  * (IsIsomorphism sets_retr32 → False) :=
  (sets_retr_incl, sets_incl_retr_not_id,
   sets_incl23_not_iso, sets_retr32_not_iso).

(* ------------------------------------------------------------------------ *)
(** ** Both maps are regular *)

(* Tying the example back to Mac Lane §I.5 Exercise 7: a one-sided inverse is
   already a pseudoinverse, so each map of the pair is regular even though
   neither is invertible. *)

Definition sets_incl23_regular : RegularMorphism sets_incl23 :=
  regular_of_section _ sets_incl23_Section.

Definition sets_retr32_regular : RegularMorphism sets_retr32 :=
  regular_of_retraction _ sets_retr32_Retraction.
