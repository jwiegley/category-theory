Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Instance.FinSet.Topos.


Generalizable All Variables.

(** * Subobjects of a skeletal finite set: images that compute, and Fong
      and Spivak's merging-versus-tagging exercise *)

(* nLab:      https://ncatlab.org/nlab/show/subobject
   nLab:      https://ncatlab.org/nlab/show/image
   Wikipedia: https://en.wikipedia.org/wiki/Image_(category_theory)
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.
              (GTM 5), §V.7 Definition 2, printed p. 126 (PDF p. 135)
   Book:      Fong and Spivak, "Seven Sketches in Compositionality",
              §1.2.1 including Exercise 1.11, printed p. 8 (PDF p. 20)

   Theory/Subobject/Lattice.v's [sub_meet] and [sub_join] are conditional
   constructions: the meet wants chosen pullbacks, the join wants a
   cocartesian structure and images.  [FinSet] already has the first two
   -- Instance/FinSet/Classifier.v's [FinSet_Pullbacks] and
   Instance/FinSet.v's [FinSet_Cocartesian] -- and this file adds the
   third.  What that buys is not merely inhabitation but COMPUTATION:
   objects of [FinSet] are literal natural numbers and every codec in
   play reduces on closed input, so the meet and the join of two named
   subobjects can be EVALUATED, and Fong and Spivak's exercise -- the
   union of two subsets of a four-element set has four elements where
   their disjoint union has five -- becomes a pair of [eq_refl]s rather
   than a pair of isomorphisms.

   ** THE IMAGE, AND WHY THE DECISION PROCEDURE MUST RETURN A WITNESS

   For f : m ~> n the image is cut out by the HIT PREDICATE [finset_hit],
   "some a of the domain is carried to k", decided by
   Instance/FinSet/Classifier.v's [fin_existsb].  The image object is
   [fin_countP] of it, the mono is [fin_select] of it with
   monicity read straight off [fin_select_inj], and the factoring
   arrow is [fin_rank] at the hit witness supplied by
   [fin_existsb_complete].  The whole shape is
   Instance/FinSet/Limit.v's [FinSet_IsEqualizer] one construction over:
   a decidable predicate, its count, its tabulation, its ranking.

   [im_least] is where the choice of decision procedure is forced.  Given
   a competing subobject w and a factorization g of f through it, the
   comparison arrow must send the q-th selected image point to g of SOME
   a with f a = that point.  A boolean test alone cannot produce that a.
   Classifier.v's [fin_existsb_sound] can, because it is written to
   return the least witness as DATA -- a sigT, and it ends in [Defined]
   for exactly this kind of consumer.  [finset_image_witness] is that
   projection and [finset_image_witness_eq] its defining equation, by
   [fin_eqb_eq].  No injectivity of [sub_mono w] is spent here, unlike in
   the [Sets] companion: [FinSet]'s hom-setoid is pointwise Leibniz
   equality, so the equation transports with no respectfulness side
   condition at all.

   ** EXERCISE 1.11, CONCRETE AND COMPUTING

   The ambient object is 4.  [ex11_u] is {0,1} and [ex11_v] is {1,2,3},
   each presented as the count-codec subobject of an explicit boolean
   predicate, so that monicity is [fin_select_inj] and the domain is a
   count that reduces.  Then, all by [eq_refl]:

     [ex11_u_size]          sub_dom ex11_u                = 2
     [ex11_v_size]          sub_dom ex11_v                = 3
     [ex11_union_four]      sub_dom (sub_join ex11_u ex11_v) = 4
     [ex11_coproduct_five]  Coprod 2 3                    = 5
     [ex11_meet_one]        sub_dom (sub_meet ex11_u ex11_v) = 1

   The third is the book's MERGING reading and the fourth its TAGGING
   reading, side by side on the same two subsets, which is the whole
   point of the exercise.  The union number is not put in by hand: it is
   [fin_countP] of the hit predicate of the copairing out of
   [Fin.t (2 + 3)], evaluated.  The meet number is the count of the
   agreement predicate over the encoded pairs in [Fin.t (2 * 3)],
   evaluated through [FinSet_Pullbacks].

   The arithmetic clauses of the same exercise, which the tree asserted
   nowhere at these instances, are [finset_pow_three] (Pow 3 = 8) and
   [finset_product_two_three] (2 × 3 = 6), in the style of
   Instance/FinSet/Topos.v's [FinSet_Pow_two]; the third, 2 + 3 = 5, is
   [ex11_coproduct_five] above and is not restated.  Seventeen [eq_refl]
   Examples in all -- [grep -c ':= eq_refl'] over this file.

   ** THE ELEMENTS OF Pow 2, AND A CORRECTION TO THE ISSUE'S PRIOR-ART CLAIM

   The catalog issue says the [fin_tabulate]/[fin_apply] codec elements
   "are never listed".  MEASURED, that is too strong.  Running
   [grep -c "^Example .*_at_"] over Instance/FinSet/Subsets.v and
   Instance/FinSet/Powerset.v and reading the [finpow_mem] ones out finds
   NINE membership bits already recorded: six in Subsets.v and three in Powerset.v.

   What is genuinely absent is narrower, and it is what the block below
   supplies.  First, every one of those nine names its code by
   [fin_tabulate] of a characteristic function ([empty1], [full1],
   [sub2_10], [sub2_01], [finpow_sub02] -- checked at their defining
   lines); NOT ONE names a code by its POSITION in [Fin.t (finpow n)].
   Second, at n = 2 the four codes are all defined (Subsets.v) but only two of them are read out, so four of the eight
   bits were listed and four were not.  [powcode2_0] through
   [powcode2_3] are the four positions and the eight [powcode2_i_at_j]
   Examples are the complete bit table, which is the enumeration the
   issue asks for.  [finpow_two_is_Pow] pins [finpow 2] to
   Structure/Topos.v's [Pow] at [FinSet_Topos] by [eq_refl], so the
   positions really are positions in the topos-internal power object and
   not merely in a same-sized set.

   ** BOUNDARIES, measured

   Both computed numbers are pinned by their neighbours being refused.
   [sub_dom (sub_join ex11_u ex11_v) = 5%nat] is refused with "cannot
   unify sub_dom (sub_join ex11_u ex11_v) and 5%nat", and [sub_dom
   (sub_meet ex11_u ex11_v) = 2%nat] likewise against 2 -- conversion
   refusals, not typing or universe ones, which is what makes the
   positive [eq_refl]s evidence that the codecs reduced rather than that
   the statement was vacuous.

   ** TRANSPARENCY, measured by flipping

   [finset_image_least] is the only [Defined] here, and it was flipped to
   [Qed] and the file recompiled clean, so the transparency is for
   uniformity with the [Sets] companion rather than forced: the [eq_refl]
   Examples read [finset_image_obj] and [finset_image_mono], never
   [im_least].  Those two, and [finset_image_sub], [FinSet_ImageOf] and
   [finset_image_witness], are plain [Definition]s and MUST stay
   transparent for the Examples to reduce.

   ** UNIVERSES

   [About FinSet_HasImages] prints
   [FinSet_HasImages@{u u0 u1 u2 u3} : HasImages@{u u0} FinSet@{u u0 u1 u2}]
   with the single-line block [Set < u1], inherited from [FinSet] itself
   (objects are [nat]).  Nothing here introduces a constraint of its own.

   ** WHAT IS NOT DELIVERED

   No [HasWidePullbacks FinSet] -- the wide case is delivered at [Sets]
   only, and the count codec does not obviously extend to an arbitrary
   index type.  No [IsMeet]/[IsJoin] witnesses: the greatest-lower-bound
   and least-upper-bound properties of the computed objects are
   Theory/Subobject/Lattice.v's business, and nothing below states them.
   No lattice or order instance on [SubObj n], for the [Type]-versus-[Prop]
   reason Instance/Powerset/Subobject.v's header gives.  No comparison
   between the count-codec subobjects here and
   Instance/FinSet/Subsets.v's [finpow_le] order on power-object codes,
   and no claim that [FinSet_HasImages] agrees with any orthogonal
   factorization system or with Structure/Regular.v's image.  Nothing
   below mentions Instance/FinSet/Regular.v, which builds regular
   MORPHISMS and their splittings rather than a factorization.  The union
   and the coproduct are compared only at the level of OBJECT SIZES; no
   comparison arrow between them is built. *)

(* ------------------------------------------------------------------------ *)
(** ** (a) The map out of the empty finite set is monic *)

Lemma FinSet_zero_monic (x : FinSet) : Monic (@zero FinSet FinSet_Initial x).
Proof.
  constructor; intros z g1 g2 _ i.
  exact (Fin.case0 (fun _ => g1 i = g2 i) (g1 i)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (b) Images by the counted-subset codec *)

Section FinSetImages.

Context {m n : nat}.
Context (f : Fin.t m → Fin.t n).

(* The hit predicate: k is in the image when some a of the domain is
   carried to it.  [fin_existsb] decides this, and its soundness lemma
   returns the least witness as DATA, which is what [im_least] consumes. *)
Definition finset_hit : Fin.t n → bool :=
  fun k => fin_existsb (fun a : Fin.t m => fin_eqb (f a) k).

Definition finset_image_obj : nat := fin_countP finset_hit.

Definition finset_image_mono : Fin.t finset_image_obj → Fin.t n :=
  fin_select finset_hit.

Lemma finset_image_monic : Monic (finset_image_mono : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj finset_hit (g1 i) (g2 i) (Hg i)).
Qed.

Definition finset_image_sub : @SubObj FinSet n :=
  @Build_SubObj FinSet n finset_image_obj finset_image_mono
    finset_image_monic.

Lemma finset_hit_value (a : Fin.t m) : finset_hit (f a) = true.
Proof.
  exact (fin_existsb_complete (fun b : Fin.t m => fin_eqb (f b) (f a)) a
           (fin_eqb_refl (f a))).
Qed.

Definition finset_image_factor : Fin.t m → Fin.t finset_image_obj :=
  fun a => fin_rank finset_hit (f a) (finset_hit_value a).

Lemma finset_image_commutes :
  (finset_image_mono : _ ~{FinSet}~> _) ∘ finset_image_factor ≈ f.
Proof. intro a; apply fin_select_rank. Qed.

(* The chosen preimage of the q-th selected element of the image. *)
Definition finset_image_witness (q : Fin.t finset_image_obj) : Fin.t m :=
  `1 (fin_existsb_sound
        (fun a : Fin.t m => fin_eqb (f a) (fin_select finset_hit q))
        (fin_select_sat finset_hit q)).

Lemma finset_image_witness_eq (q : Fin.t finset_image_obj) :
  f (finset_image_witness q) = fin_select finset_hit q.
Proof.
  apply fin_eqb_eq.
  exact (`2 (fin_existsb_sound
               (fun a : Fin.t m => fin_eqb (f a) (fin_select finset_hit q))
               (fin_select_sat finset_hit q))).
Qed.

Lemma finset_image_least (w : @SubObj FinSet n)
  (g : Fin.t m → Fin.t (sub_dom w)) (Hg : sub_mono w ∘ g ≈ f) :
  sub_le finset_image_sub w.
Proof.
  exists (fun q => g (finset_image_witness q)).
  intro q; simpl.
  transitivity (f (finset_image_witness q)).
  - exact (Hg (finset_image_witness q)).
  - exact (finset_image_witness_eq q).
Defined.

Definition FinSet_ImageOf : ImageOf (f : _ ~{FinSet}~> _) :=
  @Build_ImageOf FinSet m n f finset_image_sub finset_image_factor
    finset_image_commutes finset_image_least.

End FinSetImages.

#[export] Instance FinSet_HasImages : HasImages FinSet :=
  @Build_HasImages FinSet (@FinSet_ImageOf).

(* ------------------------------------------------------------------------ *)
(** ** (c) Seven Sketches Exercise 1.11: merging versus tagging *)

Definition fin4_0 : Fin.t 4 := Fin.F1.
Definition fin4_1 : Fin.t 4 := Fin.FS Fin.F1.
Definition fin4_2 : Fin.t 4 := Fin.FS (Fin.FS Fin.F1).
Definition fin4_3 : Fin.t 4 := Fin.FS (Fin.FS (Fin.FS Fin.F1)).

(* {0,1} and {1,2,3} inside the 4-element ambient object, cut out by
   decidable predicates so that [fin_select_inj] supplies monicity and the
   domains are counts that REDUCE. *)
Definition ex11_u_pred : Fin.t 4 → bool :=
  fun i => (fin_eqb i fin4_0 || fin_eqb i fin4_1)%bool.

Definition ex11_v_pred : Fin.t 4 → bool :=
  fun i => (fin_eqb i fin4_1 || fin_eqb i fin4_2 || fin_eqb i fin4_3)%bool.

Lemma ex11_u_monic : Monic (fin_select ex11_u_pred : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj ex11_u_pred (g1 i) (g2 i) (Hg i)).
Qed.

Lemma ex11_v_monic : Monic (fin_select ex11_v_pred : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj ex11_v_pred (g1 i) (g2 i) (Hg i)).
Qed.

Definition ex11_u : @SubObj FinSet 4%nat :=
  @Build_SubObj FinSet 4%nat (fin_countP ex11_u_pred)
    (fin_select ex11_u_pred) ex11_u_monic.

Definition ex11_v : @SubObj FinSet 4%nat :=
  @Build_SubObj FinSet 4%nat (fin_countP ex11_v_pred)
    (fin_select ex11_v_pred) ex11_v_monic.

Example ex11_u_size : sub_dom ex11_u = 2%nat := eq_refl.
Example ex11_v_size : sub_dom ex11_v = 3%nat := eq_refl.

(* MERGING: the union inside the ambient 4-element object has four
   elements. *)
Example ex11_union_four :
  sub_dom (sub_join ex11_u ex11_v) = 4%nat := eq_refl.

(* TAGGING: the coproduct of the two domains has five. *)
Example ex11_coproduct_five :
  @Coprod FinSet FinSet_Cocartesian 2%nat 3%nat = 5%nat := eq_refl.

(* The intersection has one element. *)
Example ex11_meet_one :
  sub_dom (sub_meet ex11_u ex11_v) = 1%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (d) The arithmetic of Exercise 1.11, and the elements of Pow 2 *)

Example finset_pow_three : @Pow FinSet FinSet_Topos 3%nat = 8%nat := eq_refl.

Example finset_product_two_three :
  @product_obj FinSet FinSet_Cartesian 2%nat 3%nat = 6%nat := eq_refl.

(* The third arithmetic clause, 2 + 3 = 5, is [ex11_coproduct_five] above
   and is not restated here. *)

(* The four codes of the power object of 2, named by their POSITIONS in
   [Fin.t (Pow 2)] rather than by [fin_tabulate] of a characteristic
   function, and each read out through [finpow_mem] at both elements of
   the base.  [finpow_two_is_Pow] pins the two readings of the index type
   together.  The bit table is the enumeration:

       position 0 -> {0,1}   position 1 -> {0}
       position 2 -> {1}     position 3 -> {} *)

Example finpow_two_is_Pow : finpow 2%nat = @Pow FinSet FinSet_Topos 2%nat
  := eq_refl.

Definition powcode2_0 : Fin.t (finpow 2) := Fin.F1.
Definition powcode2_1 : Fin.t (finpow 2) := Fin.FS Fin.F1.
Definition powcode2_2 : Fin.t (finpow 2) := Fin.FS (Fin.FS Fin.F1).
Definition powcode2_3 : Fin.t (finpow 2) := Fin.FS (Fin.FS (Fin.FS Fin.F1)).

Definition fin2_0 : Fin.t 2 := Fin.F1.
Definition fin2_1 : Fin.t 2 := Fin.FS Fin.F1.

Example powcode2_0_at_0 : finpow_mem powcode2_0 fin2_0 = true  := eq_refl.
Example powcode2_0_at_1 : finpow_mem powcode2_0 fin2_1 = true  := eq_refl.
Example powcode2_1_at_0 : finpow_mem powcode2_1 fin2_0 = true  := eq_refl.
Example powcode2_1_at_1 : finpow_mem powcode2_1 fin2_1 = false := eq_refl.
Example powcode2_2_at_0 : finpow_mem powcode2_2 fin2_0 = false := eq_refl.
Example powcode2_2_at_1 : finpow_mem powcode2_2 fin2_1 = true  := eq_refl.
Example powcode2_3_at_0 : finpow_mem powcode2_3 fin2_0 = false := eq_refl.
Example powcode2_3_at_1 : finpow_mem powcode2_3 fin2_1 = false := eq_refl.
