Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Met.

Generalizable All Variables.

Open Scope R_scope.

(** * Extended metric spaces *)

(* nLab:      https://ncatlab.org/nlab/show/extended+metric+space
   nLab:      https://ncatlab.org/nlab/show/Lawvere+metric+space
   Wikipedia: https://en.wikipedia.org/wiki/Metric_space#Extended_metrics
   Book:      Fong & Spivak, "Seven Sketches in Compositionality",
              §2.3.3, the variant introduced immediately after
              Definition 2.51, printed pp. 59-60 (PDF pp. 71-72)
   Paper:     Lawvere, "Metric spaces, generalized logic, and closed
              categories", Rend. Sem. Mat. Fis. Milano 43, 1973

   ON THE CITATIONS.  No book was opened for this file; the description of
   what Seven Sketches says is a paraphrase, taken from issue #308's own
   summary of §2.3.3 and from doc/plan/books/seven-sketches/pagemap.md (which
   places §2.3.3, "Lawvere metric spaces", at printed p. 59).  A reader
   checking this file against the printed book should expect the wording to
   differ.

   Seven Sketches gives Definition 2.51 (Instance/Met.v's [MetricSpace]) and
   then, immediately after it, the variant in which the distance is allowed
   the value ∞.  The variant is not an aside for that book: its whole
   enrichment story runs through the quantale Cost = [0,∞], whose monoidal
   unit is 0 and whose top element ∞ is absorbing for the tensor (addition).
   A Cost-enriched category can therefore record "there is no way from a to
   b" as the hom-object ∞, and without that value the enriched reading has
   nothing to say about spaces that fall into separate pieces.  What is
   asserted here is only that ∞ is needed for the structure to exist; NO
   enriched-category statement is proved in this file, and the identification
   of Cost-categories with extended metric spaces is not formalized anywhere
   in this tree.

   This file supplies the structure and the comparison the book's remark
   needs: [ExtMetricSpace], and the identification of ordinary metric spaces
   among the extended ones as EXACTLY those whose distances are all finite,
   in both directions with the round trips measured.

   SCOPE.  What is NOT here, deliberately: the Lawvere/[Cost]-enriched
   presentation.  Instance/Met.v's header explains the decision at length —
   Lawvere metric spaces drop symmetry and separation, which both records in
   this development keep, so they are a genuinely different structure, and
   no comparison functor between this file's [ExtMetricSpace] and any
   [Enriched] instance is built or claimed.  What this file does is name the
   structure the book's remark is about; connecting it to enrichment is a
   separate piece of work.  Also not here: a category of extended metric
   spaces.  The arrows would be the distance-preserving maps again, and
   nothing in Mac Lane §III.1 or in the issue asks for it; [Met] is
   Instance/Met.v's and is the category the completion lives in.

   [∞] IS AN INDUCTIVE CONSTRUCTOR, not a real number, so [Rinf] below has
   decidable "is it infinite" by construction ([Rinf_finite_dec]) and the
   two presentations of finiteness — a distance that is not ∞, and a
   distance that IS some real — coincide constructively
   ([EFinite_iff_not_infinite]).  Nothing in this file needs the reals to be
   complete, so its constants carry at most the two standard-library real
   axioms and never [sig_not_dec]; contrast Instance/Met/Completion.v. *)

(** ** The value type [0, ∞] *)

(* The non-negativity of [0,∞] is not imposed on the carrier: exactly as in
   Instance/Met.v, the four axioms DERIVE it ([edist_nonneg] below).  So
   [Rinf] is the reals with a point at infinity adjoined, and the metric
   axioms cut it down. *)
Inductive Rinf : Type :=
  | RFin : R → Rinf
  | RInf : Rinf.

Definition Rinf_zero : Rinf := RFin 0.

Definition Rinf_plus (a b : Rinf) : Rinf :=
  match a, b with
  | RFin x, RFin y => RFin (x + y)
  | _, _ => RInf
  end.

Definition Rinf_le (a b : Rinf) : Prop :=
  match a, b with
  | RFin x, RFin y => x <= y
  | RFin _, RInf => True
  | RInf, RFin _ => False
  | RInf, RInf => True
  end.

Lemma RFin_inj (x y : R) : RFin x = RFin y → x = y.
Proof. intro H; now inversion H. Qed.

Lemma RFin_neq_RInf (x : R) : RFin x <> RInf.
Proof. discriminate. Qed.

(* Whether a value is infinite is decided by looking at the constructor. *)
Definition Rinf_finite_dec (a : Rinf) : ((∃ r : R, a = RFin r) + (a = RInf))%type :=
  match a as z return ((∃ r : R, z = RFin r) + (z = RInf))%type with
  | RFin r => inl (r; eq_refl)
  | RInf   => inr eq_refl
  end.

Lemma Rinf_le_refl (a : Rinf) : Rinf_le a a.
Proof. destruct a; simpl; [ apply Rle_refl | exact I ]. Qed.

Lemma Rinf_le_trans (a b c : Rinf) : Rinf_le a b → Rinf_le b c → Rinf_le a c.
Proof.
  destruct a, b, c; simpl; intros H1 H2;
    solve [ exact I | contradiction | lra ].
Qed.

(* [RInf] is the top and absorbs addition — the two facts the triangle
   inequality below is argued with.  The two absorption laws are NOT equally
   strict, and the asymmetry is the match order rather than anything
   mathematical: [Rinf_plus] scrutinises its first argument first, so the
   left law closes by [reflexivity] and the right one needs a case split. *)
Lemma Rinf_le_RInf (a : Rinf) : Rinf_le a RInf.
Proof. destruct a; exact I. Qed.

Lemma Rinf_plus_RInf_l (b : Rinf) : Rinf_plus RInf b = RInf.
Proof. reflexivity. Qed.

Lemma Rinf_plus_RInf_r (a : Rinf) : Rinf_plus a RInf = RInf.
Proof. now destruct a. Qed.

(** ** The four axioms, with distance in [0, ∞] *)

(* Fong & Spivak's Definition 2.51 verbatim, with [R] replaced by [Rinf] and
   [<=] by [Rinf_le].  The clause-for-clause correspondence with
   Instance/Met.v's [MetricSpace] is exact: the same four conditions, the
   same setoid bookkeeping field. *)
Record ExtMetricSpace := {
  emet_carrier :> SetoidObject;

  edist : emet_carrier → emet_carrier → Rinf;

  edist_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → edist x y = edist x' y';
  edist_refl : ∀ x, edist x x = Rinf_zero;
  edist_separates : ∀ x y, edist x y = Rinf_zero → x ≈ y;
  edist_sym : ∀ x y, edist x y = edist y x;
  edist_triangle : ∀ x y z, Rinf_le (edist x z) (Rinf_plus (edist x y) (edist y z))
}.

Arguments edist {X} _ _ : rename.
Arguments edist_proper {X} _ _ _ _ _ _ : rename.
Arguments edist_refl {X} _ : rename.
Arguments edist_separates {X} _ _ _ : rename.
Arguments edist_sym {X} _ _ : rename.
Arguments edist_triangle {X} _ _ _ : rename.

(* Non-negativity is derived, as in the ordinary case, and it has an extra
   clause here: an infinite distance is vacuously non-negative. *)
Lemma edist_nonneg {E : ExtMetricSpace} (x y : E) (r : R) :
  edist x y = RFin r → 0 <= r.
Proof.
  intro Hr.
  pose proof (edist_triangle x y x) as H.
  rewrite (edist_refl x), (edist_sym y x) in H.
  rewrite Hr in H; simpl in H.
  unfold Rinf_zero in H; simpl in H.
  lra.
Qed.

(** ** Finiteness, and the identification with ordinary metric spaces *)

(* "All distances are finite".  Stated as data (this library's `∃` is
   [sigT]) so the real value may be read off without a choice principle;
   [EFinite_iff_not_infinite] shows the Prop-shaped alternative is
   equivalent, the case analysis on the constructor doing all the work. *)
Definition EFinite (E : ExtMetricSpace) : Type :=
  ∀ x y : E, ∃ r : R, edist x y = RFin r.

Lemma EFinite_iff_not_infinite (E : ExtMetricSpace) :
  EFinite E ↔ (∀ x y : E, edist x y = RInf → False).
Proof.
  split.
  - intros Hfin x y Hinf.
    destruct (Hfin x y) as [r Hr].
    rewrite Hinf in Hr; discriminate.
  - intros Hnot x y.
    destruct (Rinf_finite_dec (edist x y)) as [[r Hr] | Hinf].
    + exact (r; Hr).
    + now destruct (Hnot x y Hinf).
Qed.

(** *** Every metric space is an extended metric space *)

Section OfMetric.

Local Set Default Proof Using "All".

Context (X : MetricSpace).

Definition emet_of_dist (x y : X) : Rinf := RFin (dist x y).

Lemma emet_of_proper : ∀ x x' y y', x ≈ x' → y ≈ y' →
  emet_of_dist x y = emet_of_dist x' y'.
Proof.
  intros a b c d Hab Hcd; unfold emet_of_dist.
  now rewrite (dist_proper a b c d Hab Hcd).
Qed.

Lemma emet_of_refl : ∀ x, emet_of_dist x x = Rinf_zero.
Proof. intro a; unfold emet_of_dist, Rinf_zero; now rewrite dist_refl. Qed.

Lemma emet_of_separates : ∀ x y, emet_of_dist x y = Rinf_zero → x ≈ y.
Proof.
  intros a b H; unfold emet_of_dist, Rinf_zero in H.
  now apply dist_separates, RFin_inj.
Qed.

Lemma emet_of_sym : ∀ x y, emet_of_dist x y = emet_of_dist y x.
Proof. intros a b; unfold emet_of_dist; now rewrite dist_sym. Qed.

Lemma emet_of_triangle : ∀ x y z,
  Rinf_le (emet_of_dist x z) (Rinf_plus (emet_of_dist x y) (emet_of_dist y z)).
Proof. intros a b c; simpl; apply dist_triangle. Qed.

Definition ExtMetric_of_Metric : ExtMetricSpace :=
  {| emet_carrier    := met_carrier X;
     edist           := emet_of_dist;
     edist_proper    := emet_of_proper;
     edist_refl      := emet_of_refl;
     edist_separates := emet_of_separates;
     edist_sym       := emet_of_sym;
     edist_triangle  := emet_of_triangle |}.

(* ... and it is finite, with the real value read off on the nose. *)
Definition ExtMetric_of_Metric_EFinite : EFinite ExtMetric_of_Metric :=
  fun x y => (dist x y; eq_refl).

End OfMetric.

Arguments ExtMetric_of_Metric X : clear implicits.
Arguments ExtMetric_of_Metric_EFinite X : clear implicits.

(** *** Every finite extended metric space is a metric space *)

Section OfExtended.

Local Set Default Proof Using "All".

Context (E : ExtMetricSpace).
Context (Hfin : EFinite E).

Definition efin (x y : E) : R := `1 (Hfin x y).

Lemma efin_spec (x y : E) : edist x y = RFin (efin x y).
Proof. exact (`2 (Hfin x y)). Qed.

(* Every clause transfers by pushing [efin_spec] through the constructor and
   using its injectivity; no new mathematics happens here. *)
Lemma efin_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → efin x y = efin x' y'.
Proof.
  intros a b c d Hab Hcd.
  apply RFin_inj.
  rewrite <- 2 efin_spec.
  now apply edist_proper.
Qed.

Lemma efin_refl : ∀ x, efin x x = 0.
Proof.
  intro a; apply RFin_inj.
  rewrite <- efin_spec.
  exact (edist_refl a).
Qed.

Lemma efin_separates : ∀ x y, efin x y = 0 → x ≈ y.
Proof.
  intros a b H.
  apply edist_separates.
  rewrite efin_spec, H; reflexivity.
Qed.

Lemma efin_sym : ∀ x y, efin x y = efin y x.
Proof.
  intros a b; apply RFin_inj.
  rewrite <- 2 efin_spec.
  apply edist_sym.
Qed.

Lemma efin_triangle : ∀ x y z, efin x z <= efin x y + efin y z.
Proof.
  intros a b c.
  pose proof (edist_triangle a b c) as H.
  rewrite (efin_spec a c), (efin_spec a b), (efin_spec b c) in H.
  exact H.
Qed.

Definition Metric_of_EFinite : MetricSpace :=
  {| met_carrier    := emet_carrier E;
     dist           := efin;
     dist_proper    := efin_proper;
     dist_refl      := efin_refl;
     dist_separates := efin_separates;
     dist_sym       := efin_sym;
     dist_triangle  := efin_triangle |}.

End OfExtended.

Arguments Metric_of_EFinite E Hfin : clear implicits.

(** ** The two passages are mutually inverse *)

(* THE STRICT DIRECTION.  Starting from a metric space, going up to the
   extended world and back down along the canonical finiteness witness
   returns the distance ON THE NOSE — [eq_refl], not merely `≈` — because
   [ExtMetric_of_Metric_EFinite] hands back [dist x y] itself and [efin] is
   its first projection.  The carrier is likewise unchanged definitionally.
   These are convertibility statements, the exception this library allows
   itself; they say nothing about `≈`. *)
Example Metric_EFinite_roundtrip_carrier (X : MetricSpace) :
  met_carrier (Metric_of_EFinite (ExtMetric_of_Metric X)
                                 (ExtMetric_of_Metric_EFinite X))
    = met_carrier X := eq_refl.

Example Metric_EFinite_roundtrip_dist (X : MetricSpace) (x y : X) :
  dist (X := Metric_of_EFinite (ExtMetric_of_Metric X)
                               (ExtMetric_of_Metric_EFinite X)) x y
    = dist x y := eq_refl.

(* THE OTHER DIRECTION IS NOT STRICT, and the reason is worth being precise
   about: [Hfin] is an arbitrary witness, so [RFin (efin x y)] is
   [RFin (`1 (Hfin x y))] and reducing it to [edist x y] needs [`2 (Hfin x
   y)], a proof, not a conversion.  It holds up to [=] and is proved here;
   the corresponding [eq_refl] is pinned as a rejection probe in
   Test/ProbeMet.v, which is where this development's rejection vernacular
   is confined. *)
Lemma ExtMetric_of_Metric_roundtrip (E : ExtMetricSpace) (Hfin : EFinite E)
      (x y : E) :
  edist (X := ExtMetric_of_Metric (Metric_of_EFinite E Hfin)) x y = edist x y.
Proof. symmetry; exact (efin_spec E Hfin x y). Qed.

(* THE IDENTIFICATION Fong & Spivak's remark asks for.

   The comparison is between structures ON ONE CARRIER, which is how the
   book states it and is what makes it content-bearing: an extended metric
   space carries an ordinary metric structure on its own points exactly when
   none of its distances is ∞.  The carrier is deliberately NOT
   existentially quantified — comparing two records with different carriers
   would require transporting along an equality of setoids, which carries no
   mathematical content here and would obscure the statement.

   Note also where the constructive strength sits.  [EFinite] is POINTWISE
   ("for each pair there is a real") while [MetricPresentation] is GLOBAL
   ("there is a distance function"), and passing from the first to the
   second is exactly a choice step — free here only because this library's
   `∃` is [sigT], so the witness was data all along.  Over a Prop-valued
   existential this direction would be the axiom of choice. *)
Definition MetricPresentation (E : ExtMetricSpace) : Type :=
  ∃ d : E → E → R, ∀ x y : E, edist x y = RFin (d x y).

Theorem metric_iff_finite_extended (E : ExtMetricSpace) :
  EFinite E ↔ MetricPresentation E.
Proof.
  split.
  - intro Hfin.
    exact (efin E Hfin; efin_spec E Hfin).
  - intros [d Hd] x y.
    exact (d x y; Hd x y).
Qed.

(* A presentation is a metric space on the same carrier — the upgrade from
   the bare distance function to a [MetricSpace] record. *)
Definition Metric_of_presentation (E : ExtMetricSpace)
           (P : MetricPresentation E) : MetricSpace :=
  Metric_of_EFinite E (snd (metric_iff_finite_extended E) P).

(* Read the other way: the extended metric spaces arising from ordinary ones
   are exactly the finite ones. *)
Definition EFinite_of_Metric (X : MetricSpace) :
  EFinite (ExtMetric_of_Metric X) := ExtMetric_of_Metric_EFinite X.

(** ** Non-vacuity: an extended metric space that is not a metric space *)

(* Two points at infinite distance.  This is the smallest space the ordinary
   definition cannot express, and it is exactly the situation Seven Sketches
   wants ∞ for: a space in two pieces.  Every clause is a two-way case
   analysis on booleans. *)

Definition bool_setoid_object : SetoidObject :=
  {| carrier := bool; is_setoid := {| equiv := @eq bool |} |}.

Definition two_far_dist (x y : bool) : Rinf :=
  if Bool.eqb x y then RFin 0 else RInf.

Lemma two_far_proper : ∀ x x' y y' : bool_setoid_object,
  x ≈ x' → y ≈ y' → two_far_dist x y = two_far_dist x' y'.
Proof. intros a b c d Hab Hcd; simpl in *; now subst. Qed.

Lemma two_far_refl : ∀ x : bool_setoid_object, two_far_dist x x = Rinf_zero.
Proof. intro a; now destruct a. Qed.

Lemma two_far_separates : ∀ x y : bool_setoid_object,
  two_far_dist x y = Rinf_zero → x ≈ y.
Proof.
  intros a b H; destruct a, b; simpl in *;
    solve [ reflexivity | discriminate ].
Qed.

Lemma two_far_sym : ∀ x y : bool_setoid_object,
  two_far_dist x y = two_far_dist y x.
Proof. intros a b; now destruct a, b. Qed.

Lemma two_far_triangle : ∀ x y z : bool_setoid_object,
  Rinf_le (two_far_dist x z) (Rinf_plus (two_far_dist x y) (two_far_dist y z)).
Proof.
  intros a b c; destruct a, b, c; simpl;
    solve [ exact I | apply Rle_refl | lra ].
Qed.

Definition TwoFar : ExtMetricSpace :=
  {| emet_carrier    := bool_setoid_object;
     edist           := two_far_dist;
     edist_proper    := two_far_proper;
     edist_refl      := two_far_refl;
     edist_separates := two_far_separates;
     edist_sym       := two_far_sym;
     edist_triangle  := two_far_triangle |}.

Example TwoFar_infinite : edist (X := TwoFar) true false = RInf := eq_refl.

(* So the inclusion of metric spaces into extended ones is PROPER: [TwoFar]
   is an extended metric space that no ordinary metric space presents. *)
Theorem TwoFar_not_EFinite : EFinite TwoFar → False.
Proof.
  intro Hfin.
  exact (fst (EFinite_iff_not_infinite TwoFar) Hfin true false eq_refl).
Qed.

Corollary TwoFar_not_a_metric_space : MetricPresentation TwoFar → False.
Proof.
  intro H.
  exact (TwoFar_not_EFinite (snd (metric_iff_finite_extended TwoFar) H)).
Qed.
