(* The poset category 3: four presentations, its freeness, and its
   composition table.

   SOURCES.  Awodey, *Category Theory* (1st ed., CMU pre-print, September
   2005), §4.5 Exercise 3 (printed p. 91) -- give four different
   presentations by generators and relations of the poset category 3, and
   say whether 3 is free.  Fong & Spivak, *Seven Sketches in
   Compositionality* (CUP, 2019), §3.2.1 Exercise 3.10 (printed p. 83) --
   write out the composition table of the category 3, whose six morphisms
   are three identities, two generating steps, and their composite.

   A CORRECTION TO THE CATALOGUE ENTRY.  Its current-state note says that
   the category 3 "is not presented by generators and relations, and its
   freeness is not addressed".  BOTH halves were already false at the
   commit this file was written against, and both are measured here rather
   than restated:

     - [Construction/Free/Quiver/Presented.v] lines 421-537 already carry
       one presentation of 3 in full -- [Ord3Node] (:421), [Ord3Edge]
       (:423, generators a : 0 -> 1, b : 1 -> 2, c : 0 -> 2),
       [Ord3Quiver] (:428), [ord3_path_c] (:431), [ord3_path_ab] (:434),
       [ord3_free_distinct] (:441), [Ord3_count] (:448), [Ord3_lhs]
       (:451), [Ord3_rhs] (:458), [Ord3Eqns] (:465), [Ord3Finite] (:520),
       [Ord3Presentation] (:524), [Ord3] (:531) and [ord3_relation_holds]
       (:535).  That is the commutative-triangle presentation, and it is
       CONSUMED here as presentation (i); not one of those constants is
       rebuilt.

     - [Construction/Free/Quiver/Examples.v]:495 already carries
       [ordinal_free m : FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m]
       (with [ordinal_free_S] :456, [ordinal_free_0] :479 beneath it, the
       weaker [ordinal_free_Cat] :504 beside it, and the m = 3 instance
       [chain_free] :546).  So "is 3 free?  yes, on the linear two-edge
       graph" is [ordinal_free 3], ALREADY PROVED.  It is CONSUMED here as
       [three_is_free]; no freeness statement is reproved.

     - [Theory/Shapes.v:536-538] already names all three non-identity
       arrows of [_3] -- [three_01], [three_12] and
       [three_02 := three_12 ∘ three_01].  This file's [three_a],
       [three_b] and [three_c] ARE those terms
       ([three_a_is_shapes]/[three_b_is_shapes]/[three_c_is_shapes], all
       [eq_refl]); they are respelled as raw [le_t] terms so that the
       composition table below is a COMPUTATION rather than the unfolding
       of [three_02]'s definition, and the identification is recorded
       rather than the prior art passed over.

   WHAT IS DELIVERED.  Four presentations of the category 3, each shown
   isomorphic to [Instance/Ordinal.v]'s [_3] in [StrictCat], whose
   hom-setoid demands Leibniz equality on objects where [Cat]'s identifies
   naturally isomorphic functors ([Instance/StrictCat.v]:40-47 records
   that contrast).  No implication between the two readings is proved
   here; [StrictCat] is simply what the comparisons below inhabit:

     (i)   [Ord3]    -- three generators a, b, c; one relation c = b ∘ a.
                        CONSUMED from Presented.v.  [Ord3_iso].
     (ii)  [Lin3]    -- two generators a, b; NO relations.  This is the
                        free presentation, and [Lin3_iso] is built by
                        CONSUMING [ordinal_free 3].
     (iii) [Ord3Rev] -- three generators a, b, c; one relation b ∘ a = c,
                        the SAME equation written the other way round.
                        [Ord3Rev_iso].
     (iv)  [Tri4]    -- four generators a, b, c, d; two relations
                        c = b ∘ a and d = b ∘ a.  [Tri4_iso].

   WHAT MAKES THE FOUR DISTINCT, machine-checked rather than asserted.
   Their generator counts are 3, 2, 3 and 4 ([ord3_gen_total_3],
   [lin3_gen_total_2], [tri4_gen_total_4]) and their relation counts 1, 0,
   1 and 2 ([ord3_rel_total_1], [lin3_rel_total_0], [ord3_rev_rel_total_1],
   [tri4_rel_total_2]), so (i), (ii) and (iv) differ pairwise already in
   that data ([three_presentation_counts_differ]); and (iii) shares (i)'s
   quiver ([ord3_rev_shares_ord3_quiver], [eq_refl]), so it differs from
   (ii) and (iv) by those same numbers.  (i) and (iii)
   agree on both counts and are told apart by their equations instead: the
   left-hand side of (i)'s single equation is [ord3_path_c] and of (iii)'s
   is [ord3_path_ab] ([ord3_lhs_is_c], [ord3_rev_lhs_is_ab], both
   [eq_refl]), and those two paths are NOT the same arrow of the free
   category -- that is Presented.v's own [ord3_free_distinct], consumed as
   [ord3_presentations_differ].  No single constant states "the four
   records are pairwise distinct"; what is shipped is those numbers and
   that separation, from which a reader reads it off.

   THE ENGINE for the comparisons is one general lemma, [pq_same_iso]:
   two relation families that generate the same congruence present
   isomorphic categories, by identity-on-everything functors.  It is what
   relates (i) and (iii) with no path analysis at all, and its hypotheses
   are exactly what a presentation obtained from another by adding a
   derivable equation supplies.
   Its degenerate case [pq_trivial_iso] -- a relation family every member
   of which is already an [≈] presents the base category itself -- is what
   turns (ii) into a statement about [FreeOnQuiver (LinQuiver 3)] and so
   lets [ordinal_free 3] be applied.

   For (i) and (iv) the comparison needs the paths of the free category
   classified.  That is [o3_classify] and [t4_classify], written in
   [Instance/Square.v]'s [wsq_spec]/[wsq_classify] idiom: put the endpoint
   analysis in the SPECIFICATION, then induct on the path.  The
   classifications are stated at LEIBNIZ equality, not [≈] -- a deliberate
   strengthening, following [Instance/Square.v]:219-220, and the reason
   the free arrow counts below mean what they say.  From them [ord3_thin]
   and [tri4_thin] follow, and thinness is what makes the two comparison
   functors mutually inverse.

   THE COMPOSITION TABLE (Seven Sketches Exercise 3.10) is stated at [_3]
   itself, since all four presentations are shown isomorphic to it.  Six
   morphisms ([three_arrow_total_6]), of which three are identities
   ([three_identity_total_3]) and three are not
   ([three_nonidentity_total_3]); the enumeration is duplicate-free
   ([three_pairs_nodup]), sound ([three_pairs_sound]) and complete
   ([three_pairs_complete]); the three descending hom-sets are EMPTY
   ([three_no_10], [three_no_20], [three_no_21]).  All ten composable
   pairs are computed, and every one holds at LEIBNIZ equality by
   [eq_refl] -- composition in [Ordinal n] is [le_t_trans], a [Fixpoint]
   that reduces on closed indices -- so
   [three_table_ba : three_b ∘ three_a = three_c] is an equation of terms
   and not merely of [≈]-classes.  READ WHAT THE TABLE CARRIES, though:
   [_3] is thin AND its hom-setoid is Leibniz equality, so EVERY equation
   between parallel arrows already follows from [Instance/Ordinal.v]'s
   [ord_thin] -- what the ten entries pin down is therefore the
   INHABITATION pattern, which endpoint pairs carry an arrow at all,
   rather than the composites; the claim made for them is only that they
   hold at Leibniz rather than at [≈], and the non-vacuity paragraph
   below is what supplies the content.  Equality of morphisms is DECIDED by
   [three_mor_eq_dec], on the bundled morphism type [OrdMor 3] of
   [Instance/Ordinal.v]:636, through that file's
   [ord_coords_inj] (:644): a morphism of 3 is determined by its pair of
   endpoint indices.  At the level of parallel arrows the decision is
   total and always answers yes, which is exactly what thinness says
   ([three_equiv_dec], [ord3_equiv_dec], [ord3_rev_equiv_dec],
   [tri4_equiv_dec], [lin3_equiv_dec]).

   WHY THE COUNT OF SIX IS NOT VACUOUS.  A collapsed category would count
   fewer.  The three objects are pairwise distinct
   ([three_objects_distinct]); the three descending hom-sets are empty, so
   3 is not a preorder in which everything is related; and the generating
   step a is not invertible ([three_a_not_iso]), so 3 is not a groupoid
   with three objects in disguise.  The quotients are not vacuous either,
   and that is measured as an arithmetic: the free category on (i)'s
   quiver has SEVEN arrows and the presented one six, so exactly one
   identification happened ([ord3_merge_arithmetic]); on (iv)'s quiver the
   free category has EIGHT, so exactly two did ([tri4_merge_arithmetic]).
   Read those two numbers at their strength: what is PROVED is that the
   count functions [ord3_free_homcount] and [tri4_free_homcount] fold to
   seven and to eight, and what makes them the right functions is the
   classifications above together with the distinctness of the competing
   0 -> 2 paths -- [ord3_free_distinct] for (i), and [t4_c_ne_d],
   [t4_c_ne_ab], [t4_d_ne_ab] for (iv).

   WHAT IS NOT DELIVERED.  No walking isomorphism, no cyclic group and no
   one-object presented category -- those are other modules of this issue
   ([Instance/Presented/Cyclic.v] is the one already in tree).  No
   presentation of 3 is exhibited that generates a DIFFERENT category, so
   nothing here says how much a presentation may be changed before the
   category moves.  No Tietze transformations relating the four
   presentations as data, and no notion of equivalence of presentations:
   the four are compared only through the categories they present.  The
   isomorphisms are not compared with each other, so nothing says that
   (i)'s and (iii)'s comparison functors agree.  No universal property is
   restated: Presented.v's [PresentedFunctor] is applied, and neither it
   nor [presented_universal] is re-derived.  Nothing is said about
   [Theory/Metacategory.v]'s unrelated [Three] (:432), whose header
   records at :31-32 that it has no objects at all -- and note that this
   module's own short name is [Three] too, so a file importing both has a
   module and a constant of that name in scope at once; nothing declared
   below is called [Three].  No decision procedure for equality of
   objects of the presented categories is packaged beyond the two
   [eq_dec]s used internally.  And no count is given for the free category
   on (ii)'s quiver as a fold: [three_arrow_total_6] counts the arrows of
   [_3] and [three_is_free] relates the two categories, but no transfer of
   a number along an isomorphism of categories is formalized anywhere in
   this file. *)

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Construction.Free.Quiver.Examples.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Theory.Shapes.
Require Import Category.Instance.StrictCat.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.

Generalizable All Variables.

#[local] Existing Instance edgeset.

#[local] Obligation Tactic := idtac.

(* ---------- (A) presentations that generate the same congruence ---------- *)

(* Leastness of the generated congruence, in the shape a comparison of two
   presentations wants: it is enough that every generating equation of [R]
   is DERIVABLE in [S], not that it is one of [S]'s own generators. *)
(* [Construction/Quotient.v:610]'s [cc_least] is exactly this, applied at
   the congruence [CongClosure S].  That file's own comment on the sibling
   [cc_kernel] (:623-625) says such a passage is "a one-line corollary of
   leastness ... not a second induction", so this is a term and not an
   induction. *)
Definition pq_cc_mono {C : Category} (R S : HomRelT C)
  (HRS : ∀ x y (f g : x ~> y), R x y f g → CongClosure S x y f g)
  {x y : C} {f g : x ~> y} :
  CongClosure R x y f g → CongClosure S x y f g :=
  @cc_least C R (CongClosure S) (CongClosure_Congruence S) HRS x y f g.

Section SameCong.

Context {C : Category} (R S : HomRelT C).
Context (HRS : ∀ x y (f g : x ~> y), R x y f g → CongClosure S x y f g).
Context (HSR : ∀ x y (f g : x ~> y), S x y f g → CongClosure R x y f g).

(* Both quotients have the same objects, the same hom TYPES, the same
   identities and the same composition -- only the hom-setoid differs -- so
   the comparison is the identity on everything, and all its content is the
   respectfulness obligation. *)
Program Definition pq_same_to : QuotientCong C R ⟶ QuotientCong C S := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.
Next Obligation. intros a b f g H; exact (pq_cc_mono R S HRS H). Qed.
Next Obligation. intros; apply cc_refl. Qed.
Next Obligation. intros; apply cc_refl. Qed.

Program Definition pq_same_from : QuotientCong C S ⟶ QuotientCong C R := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.
Next Obligation. intros a b f g H; exact (pq_cc_mono S R HSR H). Qed.
Next Obligation. intros; apply cc_refl. Qed.
Next Obligation. intros; apply cc_refl. Qed.

(* Two presentations over ONE quiver whose relations generate the same
   congruence present isomorphic categories -- and at [StrictCat], since
   the object components are [eq_refl]. *)
Program Definition pq_same_iso :
  QuotientCong C R ≅[StrictCat] QuotientCong C S := {|
  to := pq_same_to;
  from := pq_same_from
|}.
Next Obligation.
  exists (fun x => eq_refl); intros x y f; simpl; apply cc_refl.
Qed.
Next Obligation.
  exists (fun x => eq_refl); intros x y f; simpl; apply cc_refl.
Qed.

End SameCong.

Section Trivial.

Context {C : Category} (R : HomRelT C).
Context (HF : ∀ x y (f g : x ~> y), R x y f g → f ≈ g).

(* The degenerate case: relations that assert nothing new.  [Id] merges
   them, so the library's own lift is the collapsing functor. *)
Definition pq_collapse : QuotientCong C R ⟶ C :=
  QuotientCongLift R Id[C] HF.

Program Definition pq_trivial_iso : QuotientCong C R ≅[StrictCat] C := {|
  to := pq_collapse;
  from := QuotientCongProj R
|}.
Next Obligation.
  exists (fun x => eq_refl); intros x y f; simpl; reflexivity.
Qed.
Next Obligation.
  exists (fun x => eq_refl); intros x y f; simpl; apply cc_refl.
Qed.

End Trivial.

(* ---------- (B) the three objects of 3 ---------- *)

(* [Ord_obj 3] is a record over [nat] with a bound, not a three-constructor
   inductive, so case analysis on it has to be proved.  The fourth branch
   is where the bound is spent. *)
Lemma ord3_cases (x : Ord_obj 3) :
  ((x = ord3_0) + (x = ord3_1) + (x = ord3_2))%type.
Proof.
  destruct x as [i H]; destruct i as [| [| [| i]]].
  - left; left; apply ord_obj_eq; reflexivity.
  - left; right; apply ord_obj_eq; reflexivity.
  - right; apply ord_obj_eq; reflexivity.
  - exfalso.
    exact (le_t_zero_absurd
             (le_t_SS_inv (le_t_SS_inv (le_t_SS_inv H)))).
Qed.

Lemma three_obj_eq_dec (x y : Ord_obj 3) : {x = y} + {x <> y}.
Proof.
  destruct (Nat.eq_dec (ord_val x) (ord_val y)) as [E | E].
  - left; exact (ord_obj_eq E).
  - right; intro Hxy; apply E; now rewrite Hxy.
Defined.

Lemma three_objects_distinct :
  ((ord3_0 = ord3_1 → False) * (ord3_1 = ord3_2 → False) *
   (ord3_0 = ord3_2 → False))%type.
Proof.
  repeat split; intro H; apply (f_equal ord_val) in H; discriminate H.
Qed.

Definition three_nodes : list (Ord_obj 3) :=
  ord3_0 :: ord3_1 :: ord3_2 :: nil.

Lemma three_nodes_complete (x : Ord_obj 3) : In x three_nodes.
Proof.
  destruct (ord3_cases x) as [[E | E] | E]; subst; simpl; tauto.
Qed.

Lemma three_nodes_nodup : NoDup three_nodes.
Proof.
  pose proof three_objects_distinct as [[H01 H12] H02].
  repeat constructor; simpl; intuition congruence.
Qed.

Definition three_all_pairs : list (Ord_obj 3 * Ord_obj 3) :=
  list_prod three_nodes three_nodes.

Example three_all_pairs_9 : length three_all_pairs = 9%nat := eq_refl.

Lemma three_all_pairs_complete (x y : Ord_obj 3) :
  In (x, y) three_all_pairs.
Proof. apply in_prod; apply three_nodes_complete. Qed.

(* ---------- (C) the six morphisms of 3, and the composition table ------- *)

(* Seven Sketches Exercise 3.10.  The two generating steps and the one
   composite; the three identities are the category's own. *)
Definition three_a : ord3_0 ~{_3}~> ord3_1 := le_t_S le_t_n.
Definition three_b : ord3_1 ~{_3}~> ord3_2 := le_t_S le_t_n.
Definition three_c : ord3_0 ~{_3}~> ord3_2 := le_t_S (le_t_S le_t_n).

(* PRIOR ART, and the three are not merely analogous but the SAME TERMS:
   [Theory/Shapes.v:536-538] already names all three non-identity arrows
   of [_3].  They are spelled out again here rather than consumed for one
   reason, and it is a reason about STRENGTH: that file DEFINES its 0 -> 2
   arrow as the composite ([three_02 := three_12 ∘ three_01]), so with it
   [three_table_ba] below would hold by unfolding a definition, where
   written independently as a raw [le_t] term it holds because
   [le_t_trans] COMPUTES.  The identification is recorded instead. *)
Example three_a_is_shapes : three_a = three_01 := eq_refl.
Example three_b_is_shapes : three_b = three_12 := eq_refl.
Example three_c_is_shapes : three_c = three_02 := eq_refl.

Definition three_id0 : ord3_0 ~{_3}~> ord3_0 := id.
Definition three_id1 : ord3_1 ~{_3}~> ord3_1 := id.
Definition three_id2 : ord3_2 ~{_3}~> ord3_2 := id.

(* The three descending hom-sets are empty.  This is what keeps 3 from
   being a preorder in which everything is related, and it is used again
   below to prove the enumeration complete. *)
Theorem three_no_10 (p : ord3_1 ~{_3}~> ord3_0) : False.
Proof. exact (le_t_zero_absurd p). Qed.

Theorem three_no_20 (p : ord3_2 ~{_3}~> ord3_0) : False.
Proof. exact (le_t_zero_absurd p). Qed.

Theorem three_no_21 (p : ord3_2 ~{_3}~> ord3_1) : False.
Proof. exact (le_t_zero_absurd (le_t_SS_inv p)). Qed.

(* THE TABLE.  Ten composable pairs, every one an equation of TERMS:
   composition in [Ordinal n] is [le_t_trans], which recurses on its second
   argument and so reduces outright on these closed indices.  The [≈] of
   [Ordinal n] is [Morphism_equality], i.e. Leibniz equality, so stating
   these with [=] is the same claim read at its strongest, and no
   [ord_thin] appeal is needed anywhere in the table. *)
Example three_table_ba : three_b ∘ three_a = three_c := eq_refl.

Example three_table_a_id0 : three_a ∘ three_id0 = three_a := eq_refl.
Example three_table_id1_a : three_id1 ∘ three_a = three_a := eq_refl.
Example three_table_b_id1 : three_b ∘ three_id1 = three_b := eq_refl.
Example three_table_id2_b : three_id2 ∘ three_b = three_b := eq_refl.
Example three_table_c_id0 : three_c ∘ three_id0 = three_c := eq_refl.
Example three_table_id2_c : three_id2 ∘ three_c = three_c := eq_refl.

Example three_table_id0 : three_id0 ∘ three_id0 = three_id0 := eq_refl.
Example three_table_id1 : three_id1 ∘ three_id1 = three_id1 := eq_refl.
Example three_table_id2 : three_id2 ∘ three_id2 = three_id2 := eq_refl.

(* Every parallel pair agrees, so the table above is the whole of it: no
   further entry could name a different arrow. *)
Theorem three_thin (x y : Ord_obj 3) (p q : x ~{_3}~> y) : p = q.
Proof. exact (ord_thin p q). Qed.

(* The six inhabited endpoint pairs: three loops, the two steps, and the
   composite. *)
Definition three_pairs : list (Ord_obj 3 * Ord_obj 3) :=
  (ord3_0, ord3_0) :: (ord3_1, ord3_1) :: (ord3_2, ord3_2) ::
  (ord3_0, ord3_1) :: (ord3_1, ord3_2) :: (ord3_0, ord3_2) :: nil.

Lemma three_pairs_nodup : NoDup three_pairs.
Proof.
  pose proof three_objects_distinct as [[H01 H12] H02].
  repeat constructor; simpl; intuition congruence.
Qed.

Theorem three_pairs_sound (q : Ord_obj 3 * Ord_obj 3) :
  In q three_pairs → fst q ~{_3}~> snd q.
Proof.
  pose proof three_objects_distinct as [[H01 H12] H02].
  destruct q as [x y]; intro H.
  destruct (ord3_cases x) as [[Ex | Ex] | Ex];
    destruct (ord3_cases y) as [[Ey | Ey] | Ey]; subst; simpl in H;
    solve [ exact three_id0 | exact three_id1 | exact three_id2
          | exact three_a | exact three_b | exact three_c
          | exfalso; intuition congruence ].
Qed.

Theorem three_pairs_complete (x y : Ord_obj 3) :
  (x ~{_3}~> y) → In (x, y) three_pairs.
Proof.
  intro p.
  destruct (ord3_cases x) as [[Ex | Ex] | Ex];
    destruct (ord3_cases y) as [[Ey | Ey] | Ey]; subst;
    solve [ simpl; tauto
          | exfalso; solve [ exact (three_no_10 p)
                           | exact (three_no_20 p)
                           | exact (three_no_21 p) ] ].
Qed.

(* The count, as a number.  [three_homcount] gives the number of arrows
   between each ordered pair of objects; the two lemmas either side of it
   say that it is 1 exactly on the listed pairs, and the per-pair
   statements above say what those numbers mean. *)
Definition three_homcount (x y : Ord_obj 3) : nat :=
  if Nat.leb (ord_val x) (ord_val y) then 1%nat else 0%nat.

Lemma three_homcount_in (x y : Ord_obj 3) :
  three_homcount x y = 1%nat → In (x, y) three_pairs.
Proof.
  destruct (ord3_cases x) as [[Ex | Ex] | Ex];
    destruct (ord3_cases y) as [[Ey | Ey] | Ey]; subst;
    solve [ intros _; simpl; tauto | discriminate ].
Qed.

Lemma three_in_homcount (x y : Ord_obj 3) :
  In (x, y) three_pairs → three_homcount x y = 1%nat.
Proof.
  pose proof three_objects_distinct as [[H01 H12] H02].
  destruct (ord3_cases x) as [[Ex | Ex] | Ex];
    destruct (ord3_cases y) as [[Ey | Ey] | Ey]; subst;
    solve [ intros _; reflexivity | simpl; intuition congruence ].
Qed.

Definition three_arrow_total : nat :=
  fold_right (fun q n => three_homcount (fst q) (snd q) + n)%nat 0%nat
    three_all_pairs.

(* Seven Sketches Exercise 3.10: six morphisms. *)
Theorem three_arrow_total_6 : three_arrow_total = 6%nat.
Proof. reflexivity. Qed.

Definition three_identity_total : nat :=
  fold_right (fun x n => three_homcount x x + n)%nat 0%nat three_nodes.

(* ...three of them identities... *)
Theorem three_identity_total_3 : three_identity_total = 3%nat.
Proof. reflexivity. Qed.

Definition three_nonidentity_total : nat :=
  (three_arrow_total - three_identity_total)%nat.

(* ...and three of them not: the two generating steps and the composite. *)
Theorem three_nonidentity_total_3 : three_nonidentity_total = 3%nat.
Proof. reflexivity. Qed.

(* [Instance/Ordinal.v]:855's independent count of endpoint pairs, read at
   n = 3.  Its left side is TWICE the morphism count, and its proof there
   is one rewrite by [ord_pairs_length] and the closed form
   [ord_tri_closed], so the six above is confirmed by an argument that
   shares no text with the fold. *)
Corollary three_morphism_count : (2 * length (ord_pairs 3) = 3 * (3 + 1))%nat.
Proof. exact (ord_morphism_count 3). Qed.

Example three_ord_pairs_6 : length (ord_pairs 3) = 6%nat := ord_pairs_3.

(* ---------- deciding equality of morphisms ---------- *)

(* A morphism of 3, bundled with its endpoints, is determined by the pair
   of endpoint indices -- objects by [ord_obj_eq], the arrow between them
   by thinness.  Both halves are [Instance/Ordinal.v]'s, consumed. *)
Theorem three_mor_eq_coords (a b : OrdMor 3) :
  ord_coords a = ord_coords b → a = b.
Proof. exact (@ord_coords_inj 3 a b). Qed.

Theorem three_coords_eq_mor (a b : OrdMor 3) :
  a = b → ord_coords a = ord_coords b.
Proof. intro E; now rewrite E. Qed.

(* Hence equality of morphisms is decided, by comparing two natural
   numbers. *)
Definition three_mor_eq_dec (a b : OrdMor 3) : {a = b} + {a <> b}.
Proof.
  destruct (Nat.eq_dec (fst (ord_coords a)) (fst (ord_coords b))) as [E1 | E1].
  - destruct (Nat.eq_dec (snd (ord_coords a)) (snd (ord_coords b)))
      as [E2 | E2].
    + left; apply three_mor_eq_coords.
      destruct (ord_coords a), (ord_coords b); simpl in *; congruence.
    + right; intro E; apply E2; now rewrite E.
  - right; intro E; apply E1; now rewrite E.
Defined.

(* At the level of PARALLEL arrows the decision is total and always
   answers yes.  That is not a weakness of the procedure: it is exactly
   what thinness of 3 says, and all the content sits in the endpoint
   analysis above -- which pairs of objects carry an arrow at all. *)
Definition three_equiv_dec (x y : Ord_obj 3) (p q : x ~{_3}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (three_thin x y p q).

(* Non-vacuity of the count of six.  A category with fewer objects, or one
   in which the step a were invertible, would count differently. *)
Theorem three_a_not_iso : @IsIsomorphism _3 ord3_0 ord3_1 three_a → False.
Proof. intros [g _ _]; exact (three_no_10 g). Qed.

(* ---------- (D) presentation (i): the commutative triangle ---------- *)

(* Generators a : 0 -> 1, b : 1 -> 2, c : 0 -> 2; one relation c = b ∘ a.
   Every piece of the presentation is [Construction/Free/Quiver/
   Presented.v]'s, CONSUMED: [Ord3Quiver], [Ord3Eqns], [Ord3Finite],
   [Ord3Presentation], [Ord3], [ord3_path_c], [ord3_path_ab],
   [ord3_free_distinct] and [ord3_relation_holds].  What is added here is
   the classification of the free paths, thinness, and the comparison with
   [_3]. *)
Example three_pres_i_is_Ord3 : FinitelyPresented Ord3Presentation = Ord3 :=
  eq_refl.

Definition FreeOrd3 : Category := FreeOnQuiver Ord3Quiver.

Definition o3_a : Ord3_0 ~{FreeOrd3}~> Ord3_1 :=
  tlist_singleton (B:=@edges Ord3Quiver) Ord3_a.
Definition o3_b : Ord3_1 ~{FreeOrd3}~> Ord3_2 :=
  tlist_singleton (B:=@edges Ord3Quiver) Ord3_b.

(* The specification: for each ordered pair of nodes, exactly which paths
   join them.  [False] marks the three pairs joined by no path.  The
   equalities are LEIBNIZ, not [≈] -- the strengthening
   [Instance/Square.v]:218-220 documents, and what makes the free count
   below a count of arrows rather than of [≈]-classes. *)
Definition o3_spec (y : Ord3Node) :
  ∀ x : Ord3Node, (x ~{FreeOrd3}~> y) → Type :=
  match y as y0 return ∀ x : Ord3Node, (x ~{FreeOrd3}~> y0) → Type with
  | Ord3_0 =>
      fun x => match x as x0 return (x0 ~{FreeOrd3}~> Ord3_0) → Type with
      | Ord3_0 => fun p => p = tnil
      | Ord3_1 => fun _ => False
      | Ord3_2 => fun _ => False
      end
  | Ord3_1 =>
      fun x => match x as x0 return (x0 ~{FreeOrd3}~> Ord3_1) → Type with
      | Ord3_0 => fun p => p = o3_a
      | Ord3_1 => fun p => p = tnil
      | Ord3_2 => fun _ => False
      end
  | Ord3_2 =>
      fun x => match x as x0 return (x0 ~{FreeOrd3}~> Ord3_2) → Type with
      | Ord3_0 => fun p => ((p = ord3_path_c) + (p = ord3_path_ab))%type
      | Ord3_1 => fun p => p = o3_b
      | Ord3_2 => fun p => p = tnil
      end
  end.

(* One induction on the path: the empty path forces source and target to
   agree, and a step is one of the three edges, which pins the source and
   hands the rest to the induction hypothesis.  The 0 -> 2 branch is the
   only one entering the disjunction, once on each side. *)
Theorem o3_classify (y x : Ord3Node) (p : x ~{FreeOrd3}~> y) : o3_spec y x p.
Proof.
  induction p as [ | i j e p IH ].
  - destruct y; reflexivity.
  - destruct e; destruct y; simpl in *;
      try contradiction;
      try (rewrite IH; reflexivity).
    + right; rewrite IH; reflexivity.
    + left;  rewrite IH; reflexivity.
Qed.

Corollary free_ord3_no_10 (p : Ord3_1 ~{FreeOrd3}~> Ord3_0) : False.
Proof. exact (o3_classify _ _ p). Qed.

Corollary free_ord3_no_20 (p : Ord3_2 ~{FreeOrd3}~> Ord3_0) : False.
Proof. exact (o3_classify _ _ p). Qed.

Corollary free_ord3_no_21 (p : Ord3_2 ~{FreeOrd3}~> Ord3_1) : False.
Proof. exact (o3_classify _ _ p). Qed.

(* Any two parallel arrows of the PRESENTED triangle agree.  The only pair
   the classification leaves apart is [ord3_path_c] against
   [ord3_path_ab], and the imposed relation is exactly what closes it --
   [ord3_relation_holds], consumed. *)
Theorem ord3_thin (x y : Ord3Node) (p q : x ~{Ord3}~> y) : p ≈ q.
Proof.
  pose proof (o3_classify y x p) as Hp.
  pose proof (o3_classify y x q) as Hq.
  destruct x, y; simpl in Hp, Hq;
    try contradiction;
    try (subst; apply cc_refl).
  destruct Hp as [Hp | Hp]; destruct Hq as [Hq | Hq]; subst.
  - apply cc_refl.
  - exact ord3_relation_holds.
  - exact (cc_sym ord3_relation_holds).
  - apply cc_refl.
Qed.

Definition ord3_equiv_dec (x y : Ord3Node) (p q : x ~{Ord3}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (ord3_thin x y p q).

(* The comparison into 3.  [_3] is thin, so both the quiver
   homomorphism's respectfulness and the merging hypothesis the presented
   category's universal property asks for are [ord_thin]; the functor
   itself is [PresentedFunctor], consumed. *)
Definition o3_ord (n : Ord3Node) : Ord_obj 3 :=
  match n with
  | Ord3_0 => ord3_0
  | Ord3_1 => ord3_1
  | Ord3_2 => ord3_2
  end.

Definition o3_edge_arr (x y : Ord3Node) (e : Ord3Edge x y) :
  o3_ord x ~{_3}~> o3_ord y :=
  match e with
  | Ord3_a => le_t_S le_t_n
  | Ord3_b => le_t_S le_t_n
  | Ord3_c => le_t_S (le_t_S le_t_n)
  end.

Definition o3_qhom : QuiverHomomorphism Ord3Quiver (QuiverOfCat _3) :=
  Build_QuiverHomomorphism Ord3Quiver (QuiverOfCat _3) o3_ord o3_edge_arr
    (fun x y e e' _ => ord_thin _ _).

Definition Ord3_to : Ord3 ⟶ _3 :=
  @PresentedFunctor Ord3Quiver (fe_rel Ord3Eqns) _3 o3_qhom
    (fun x y f g _ => ord_thin _ _).

Example ord3_to_gen_a :
  fmap[Ord3_to] (@pgen Ord3Quiver (fe_rel Ord3Eqns) _ _ Ord3_a) ≈ three_a.
Proof. apply ord_thin. Qed.

Example ord3_to_gen_b :
  fmap[Ord3_to] (@pgen Ord3Quiver (fe_rel Ord3Eqns) _ _ Ord3_b) ≈ three_b.
Proof. apply ord_thin. Qed.

Example ord3_to_gen_c :
  fmap[Ord3_to] (@pgen Ord3Quiver (fe_rel Ord3Eqns) _ _ Ord3_c) ≈ three_c.
Proof. apply ord_thin. Qed.

Definition ord3_gen {x y : Ord3Node} (e : @edges Ord3Quiver x y) :
  x ~{Ord3}~> y :=
  @pgen Ord3Quiver (fe_rel Ord3Eqns) x y e.

Definition o3_node (k : nat) : Ord3Node :=
  match k with
  | O => Ord3_0
  | S O => Ord3_1
  | _ => Ord3_2
  end.

(* The comparison out of 3.  The three descending cases are refuted by the
   [le_t] argument, which is where the order of 3 is spent. *)
Definition o3_arr : ∀ i j : nat, le_t i j → (o3_node i ~{Ord3}~> o3_node j).
Proof.
  intros i j; destruct i as [| [| i]]; destruct j as [| [| j]]; intro H.
  - exact id.
  - exact (ord3_gen Ord3_a).
  - exact (ord3_gen Ord3_c).
  - exact (False_rect _ (le_t_zero_absurd H)).
  - exact id.
  - exact (ord3_gen Ord3_b).
  - exact (False_rect _ (le_t_zero_absurd H)).
  - exact (False_rect _ (le_t_zero_absurd (le_t_SS_inv H))).
  - exact id.
Defined.

Program Definition Ord3_from : _3 ⟶ Ord3 := {|
  fobj := fun x => o3_node (ord_val x);
  fmap := fun x y f => o3_arr (ord_val x) (ord_val y) f
|}.
Solve All Obligations with (repeat intro; apply ord3_thin).

Lemma o3_node_ord (n : Ord3Node) : o3_node (ord_val (o3_ord n)) = n.
Proof. now destruct n. Qed.

Lemma o3_ord_node (x : Ord_obj 3) : o3_ord (o3_node (ord_val x)) = x.
Proof. destruct (ord3_cases x) as [[E | E] | E]; subst; reflexivity. Qed.

(* Presentation (i) presents the category 3, at [StrictCat] strength: both
   object components are the equalities above, and both morphism
   components are discharged by thinness of the two sides. *)
Program Definition Ord3_iso : Ord3 ≅[StrictCat] _3 := {|
  to := Ord3_to;
  from := Ord3_from
|}.
Next Obligation.
  exists o3_ord_node; intros x y f; apply ord_thin.
Qed.
Next Obligation.
  exists o3_node_ord; intros x y f; apply ord3_thin.
Qed.

(* How much the relation does.  [o3_classify] bounds each free hom-set
   from above, and [ord3_free_distinct] (Presented.v:441, consumed) shows
   the 0 -> 2 one really does have two elements, so the free category on
   the triangle quiver has SEVEN arrows against 3's six: the presentation
   makes exactly one identification. *)
Definition ord3_nodes : list Ord3Node := Ord3_0 :: Ord3_1 :: Ord3_2 :: nil.

Definition ord3_all_pairs : list (Ord3Node * Ord3Node) :=
  list_prod ord3_nodes ord3_nodes.

Definition ord3_free_homcount (x y : Ord3Node) : nat :=
  match x, y with
  | Ord3_0, Ord3_0 => 1%nat
  | Ord3_1, Ord3_1 => 1%nat
  | Ord3_2, Ord3_2 => 1%nat
  | Ord3_0, Ord3_1 => 1%nat
  | Ord3_1, Ord3_2 => 1%nat
  | Ord3_0, Ord3_2 => 2%nat
  | _, _ => 0%nat
  end.

Definition ord3_free_arrow_total : nat :=
  fold_right (fun q n => ord3_free_homcount (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem ord3_free_arrow_total_7 : ord3_free_arrow_total = 7%nat.
Proof. reflexivity. Qed.

Theorem ord3_free_two_paths : ord3_path_c ≈ ord3_path_ab → False.
Proof. exact ord3_free_distinct. Qed.

Example ord3_merge_arithmetic :
  (ord3_free_arrow_total - three_arrow_total)%nat = 1%nat := eq_refl.

(* ---------- (E) presentation (ii): two generators, no relations -------- *)

(* THE FREENESS VERDICT.  Awodey's question "is 3 free?" is answered YES,
   by CONSUMING [Construction/Free/Quiver/Examples.v]:495's [ordinal_free]
   at m = 3.  The category 3 is the free category on the linear two-edge
   graph 0 -> 1 -> 2: the arrow 0 -> 2 is the two-edge PATH, forced by
   composition, and not a generator subject to a relation. *)
(* [Examples.v:546]'s [chain_free] IS this constant -- same type, same
   body -- so it is aliased rather than restated; the local name is kept
   so this section reads without a cross-file alias. *)
Definition three_is_free : FreeOnQuiver (LinQuiver 3) ≅[StrictCat] _3 :=
  chain_free.

(* The three witnesses of that reading, all from Examples.v: the two
   generating steps have path length one, and the arrow they compose to
   has path length two -- it is a composite, not a fourth edge. *)
Example three_gen_0_length : tlist_length chain_e0 = 1%nat := chain_e0_length.
Example three_gen_1_length : tlist_length chain_e1 = 1%nat := chain_e1_length.
Example three_composite_length : tlist_length chain_e10 = 2%nat :=
  chain_e10_length.

Example three_composite_is_composite : chain_e10 = chain_e1 ∘ chain_e0 :=
  eq_refl.

(* The same thing as a PRESENTATION: the linear quiver, made finite, with
   the empty family of equations. *)
Definition lin3_ecount (x y : LinQuiver 3) : nat :=
  if Nat.eq_dec (S (ord_val x)) (ord_val y) then 1%nat else 0%nat.

Definition lin3_edge (x y : LinQuiver 3) :
  Fin.t (lin3_ecount x y) → @edges (LinQuiver 3) x y.
Proof.
  unfold lin3_ecount.
  destruct (Nat.eq_dec (S (ord_val x)) (ord_val y)) as [E | E].
  - intros _; exact E.
  - intro i; exact (Fin.case0 _ i).
Defined.

Definition lin3_eindex (x y : LinQuiver 3)
  (e : @edges (LinQuiver 3) x y) : Fin.t (lin3_ecount x y).
Proof.
  unfold lin3_ecount.
  destruct (Nat.eq_dec (S (ord_val x)) (ord_val y)) as [E | E].
  - exact Fin.F1.
  - exact (False_rect _ (E e)).
Defined.

(* An edge of the linear quiver is a proof of a [nat] equation, so two
   edges with the same endpoints agree by UIP on [nat] -- Hedberg, no
   axiom.  That is Examples.v:394's [linear_edge_unique], consumed. *)
Lemma lin3_edge_rt (x y : LinQuiver 3) (e : @edges (LinQuiver 3) x y) :
  lin3_edge x y (lin3_eindex x y e) ≈ e.
Proof. apply linear_edge_unique. Qed.

Definition Lin3Finite : FiniteQuiver (LinQuiver 3) :=
  @Build_FiniteQuiver (LinQuiver 3) 3 (@ord_of_fin 3) (@fin_of_ord 3)
    (@ord_of_fin_of_ord 3) lin3_ecount lin3_edge lin3_eindex lin3_edge_rt.

Definition Lin3Eqns : FiniteEquations (LinQuiver 3).
Proof.
  unshelve refine {| fe_count := fun _ _ => 0%nat |};
    intros x y i; exact (Fin.case0 _ i).
Defined.

Definition Lin3Presentation : FinitePresentation := {|
  fp_quiver := LinQuiver 3;
  fp_finite := Lin3Finite;
  fp_eqns := Lin3Eqns
|}.

Definition Lin3 : Category := FinitelyPresented Lin3Presentation.

(* No relations, at every pair of endpoints. *)
Theorem lin3_no_equations (x y : LinQuiver 3) :
  @fe_count _ Lin3Eqns x y = 0%nat.
Proof. reflexivity. Qed.

Lemma lin3_rel_empty (x y : LinQuiver 3)
  (f g : x ~{FreeOnQuiver (LinQuiver 3)}~> y) :
  fe_rel Lin3Eqns x y f g → f ≈ g.
Proof. intros [i _]; exact (Fin.case0 _ i). Qed.

(* Quotienting by nothing changes nothing... *)
Definition Lin3_free_iso : Lin3 ≅[StrictCat] FreeOnQuiver (LinQuiver 3) :=
  pq_trivial_iso (fe_rel Lin3Eqns) lin3_rel_empty.

(* ...so presentation (ii) presents 3, by [ordinal_free 3]. *)
Definition Lin3_iso : Lin3 ≅[StrictCat] _3 :=
  iso_compose three_is_free Lin3_free_iso.

Theorem lin3_thin (x y : LinQuiver 3) (p q : x ~{Lin3}~> y) : p ≈ q.
Proof. exact (cc_equiv (linear_free_thin x y p q)). Qed.

Definition lin3_equiv_dec (x y : LinQuiver 3) (p q : x ~{Lin3}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (lin3_thin x y p q).

(* ---------- (F) presentation (iii): the equation written backwards ----- *)

(* The same three generators, and the same single equation with its two
   sides exchanged: [Ord3Eqns] imposes c = b ∘ a, [Ord3RevEqns] imposes
   b ∘ a = c.  As presentation DATA the two are different, and section (H)
   below says how they are told apart; as categories they coincide,
   because a congruence is symmetric. *)
Definition Ord3RevEqns : FiniteEquations Ord3Quiver := {|
  fe_count := Ord3_count;
  fe_lhs := Ord3_rhs;
  fe_rhs := Ord3_lhs
|}.

Definition Ord3RevPresentation : FinitePresentation := {|
  fp_quiver := Ord3Quiver;
  fp_finite := Ord3Finite;
  fp_eqns := Ord3RevEqns
|}.

Definition Ord3Rev : Category := FinitelyPresented Ord3RevPresentation.

Lemma ord3_rev_relation_holds :
  @equiv _ (@homset Ord3Rev Ord3_0 Ord3_2) ord3_path_ab ord3_path_c.
Proof. apply cc_gen. exists Fin.F1. split; reflexivity. Qed.

(* Each presentation's generating equation is DERIVABLE in the other -- one
   [cc_sym] apiece -- so [pq_same_iso] applies with no path analysis. *)
Lemma ord3_rev_into_ord3 (x y : Ord3Quiver)
  (f g : x ~{FreeOnQuiver Ord3Quiver}~> y) :
  fe_rel Ord3RevEqns x y f g → CongClosure (fe_rel Ord3Eqns) x y f g.
Proof.
  destruct x, y; intros [i [Hf Hg]];
    try (exact (Fin.case0 _ i)).
  exact (cc_trans (cc_equiv Hf)
           (cc_trans (cc_sym ord3_relation_holds)
                     (cc_equiv (symmetry Hg)))).
Qed.

Lemma ord3_into_ord3_rev (x y : Ord3Quiver)
  (f g : x ~{FreeOnQuiver Ord3Quiver}~> y) :
  fe_rel Ord3Eqns x y f g → CongClosure (fe_rel Ord3RevEqns) x y f g.
Proof.
  destruct x, y; intros [i [Hf Hg]];
    try (exact (Fin.case0 _ i)).
  exact (cc_trans (cc_equiv Hf)
           (cc_trans (cc_sym ord3_rev_relation_holds)
                     (cc_equiv (symmetry Hg)))).
Qed.

Definition Ord3Rev_Ord3_iso : Ord3Rev ≅[StrictCat] Ord3 :=
  pq_same_iso (fe_rel Ord3RevEqns) (fe_rel Ord3Eqns)
    ord3_rev_into_ord3 ord3_into_ord3_rev.

(* Presentation (iii) presents the category 3. *)
Definition Ord3Rev_iso : Ord3Rev ≅[StrictCat] _3 :=
  iso_compose Ord3_iso Ord3Rev_Ord3_iso.

Theorem ord3_rev_thin (x y : Ord3Node) (p q : x ~{Ord3Rev}~> y) : p ≈ q.
Proof.
  exact (pq_cc_mono (fe_rel Ord3Eqns) (fe_rel Ord3RevEqns)
           ord3_into_ord3_rev (ord3_thin x y p q)).
Qed.

Definition ord3_rev_equiv_dec (x y : Ord3Node) (p q : x ~{Ord3Rev}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (ord3_rev_thin x y p q).

(* ---------- (G) presentation (iv): four generators, two relations ------ *)

(* Generators a : 0 -> 1, b : 1 -> 2 and TWO parallel arrows c, d : 0 -> 2,
   with both of them equated to the composite: c = b ∘ a and d = b ∘ a.
   The nodes are [Ord3Node] again, so Presented.v's node enumeration
   ([Ord3_node], [Ord3_index], [Ord3_node_rt]) is reused; the edges are
   new. *)
Inductive Tri4Edge : Ord3Node → Ord3Node → Set :=
  | Tri4_a : Tri4Edge Ord3_0 Ord3_1
  | Tri4_b : Tri4Edge Ord3_1 Ord3_2
  | Tri4_c : Tri4Edge Ord3_0 Ord3_2
  | Tri4_d : Tri4Edge Ord3_0 Ord3_2.

Definition Tri4Quiver : Quiver :=
  Build_Quiver_Standard_Eq Ord3Node Tri4Edge.

Definition FreeTri4 : Category := FreeOnQuiver Tri4Quiver.

Definition t4_a : Ord3_0 ~{FreeTri4}~> Ord3_1 :=
  tlist_singleton (B:=@edges Tri4Quiver) Tri4_a.
Definition t4_b : Ord3_1 ~{FreeTri4}~> Ord3_2 :=
  tlist_singleton (B:=@edges Tri4Quiver) Tri4_b.
Definition t4_c : Ord3_0 ~{FreeTri4}~> Ord3_2 :=
  tlist_singleton (B:=@edges Tri4Quiver) Tri4_c.
Definition t4_d : Ord3_0 ~{FreeTri4}~> Ord3_2 :=
  tlist_singleton (B:=@edges Tri4Quiver) Tri4_d.
Definition t4_ab : Ord3_0 ~{FreeTri4}~> Ord3_2 :=
  tcons (B:=@edges Tri4Quiver) _ Tri4_a
    (tlist_singleton (B:=@edges Tri4Quiver) Tri4_b).

Definition t4_spec (y : Ord3Node) :
  ∀ x : Ord3Node, (x ~{FreeTri4}~> y) → Type :=
  match y as y0 return ∀ x : Ord3Node, (x ~{FreeTri4}~> y0) → Type with
  | Ord3_0 =>
      fun x => match x as x0 return (x0 ~{FreeTri4}~> Ord3_0) → Type with
      | Ord3_0 => fun p => p = tnil
      | Ord3_1 => fun _ => False
      | Ord3_2 => fun _ => False
      end
  | Ord3_1 =>
      fun x => match x as x0 return (x0 ~{FreeTri4}~> Ord3_1) → Type with
      | Ord3_0 => fun p => p = t4_a
      | Ord3_1 => fun p => p = tnil
      | Ord3_2 => fun _ => False
      end
  | Ord3_2 =>
      fun x => match x as x0 return (x0 ~{FreeTri4}~> Ord3_2) → Type with
      | Ord3_0 => fun p => ((p = t4_c) + (p = t4_d) + (p = t4_ab))%type
      | Ord3_1 => fun p => p = t4_b
      | Ord3_2 => fun p => p = tnil
      end
  end.

Theorem t4_classify (y x : Ord3Node) (p : x ~{FreeTri4}~> y) : t4_spec y x p.
Proof.
  induction p as [ | i j e p IH ].
  - destruct y; reflexivity.
  - destruct e; destruct y; simpl in *;
      try contradiction;
      try (rewrite IH; reflexivity).
    + right; rewrite IH; reflexivity.
    + left; left; rewrite IH; reflexivity.
    + left; right; rewrite IH; reflexivity.
Qed.

(* The three 0 -> 2 paths of the free category are pairwise distinct.  For
   c against ab and d against ab the intermediate node already separates
   them, as in Presented.v's [ord3_free_distinct]; c against d is the case
   that needs UIP on the nodes, which they have by decidable equality
   (Hedberg, through [UIP_dec] -- no axiom is assumed). *)
Definition ord3_node_eq_dec (x y : Ord3Node) : {x = y} + {x <> y}.
Proof.
  destruct x, y; solve [ left; reflexivity | right; discriminate ].
Defined.

Lemma t4_c_ne_d : t4_c ≈ t4_d → False.
Proof.
  unfold t4_c, t4_d, tlist_singleton; simpl.
  unfold tlist_quiver_equiv; simpl.
  intros [q He Ht].
  rewrite (UIP_dec ord3_node_eq_dec q eq_refl) in He.
  simpl in He; discriminate He.
Qed.

Lemma t4_c_ne_ab : t4_c ≈ t4_ab → False.
Proof.
  unfold t4_c, t4_ab, tlist_singleton; simpl.
  unfold tlist_quiver_equiv; simpl. intros [q He Ht]. discriminate q.
Qed.

Lemma t4_d_ne_ab : t4_d ≈ t4_ab → False.
Proof.
  unfold t4_d, t4_ab, tlist_singleton; simpl.
  unfold tlist_quiver_equiv; simpl. intros [q He Ht]. discriminate q.
Qed.

Definition Tri4_count (x y : Tri4Quiver) : nat :=
  match x, y with Ord3_0, Ord3_2 => 2%nat | _, _ => 0%nat end.

Definition t4_pick (i : Fin.t 2) : Ord3_0 ~{FreeTri4}~> Ord3_2 :=
  match i with
  | Fin.F1 => t4_c
  | Fin.FS _ => t4_d
  end.

Definition Tri4_lhs (x y : Tri4Quiver) :
  Fin.t (Tri4_count x y) → x ~{FreeTri4}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact (t4_pick i) ].
Defined.

Definition Tri4_rhs (x y : Tri4Quiver) :
  Fin.t (Tri4_count x y) → x ~{FreeTri4}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact t4_ab ].
Defined.

Definition Tri4Eqns : FiniteEquations Tri4Quiver := {|
  fe_count := Tri4_count;
  fe_lhs := Tri4_lhs;
  fe_rhs := Tri4_rhs
|}.

Definition Tri4_ecount (x y : Ord3Node) : nat :=
  match x, y with
  | Ord3_0, Ord3_1 => 1%nat
  | Ord3_1, Ord3_2 => 1%nat
  | Ord3_0, Ord3_2 => 2%nat
  | _, _ => 0%nat
  end.

Definition Tri4_edge (x y : Ord3Node) :
  Fin.t (Tri4_ecount x y) → Tri4Edge x y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i)
          | exact Tri4_a | exact Tri4_b
          | exact (match i with
                   | Fin.F1 => Tri4_c
                   | Fin.FS _ => Tri4_d
                   end) ].
Defined.

Definition Tri4_eindex (x y : Ord3Node) (e : Tri4Edge x y) :
  Fin.t (Tri4_ecount x y) :=
  match e in Tri4Edge a b return Fin.t (Tri4_ecount a b) with
  | Tri4_a => Fin.F1
  | Tri4_b => Fin.F1
  | Tri4_c => Fin.F1
  | Tri4_d => Fin.FS Fin.F1
  end.

Lemma Tri4_edge_rt (x y : Ord3Node) (e : Tri4Edge x y) :
  Tri4_edge x y (Tri4_eindex x y e) = e.
Proof. destruct e; reflexivity. Qed.

Definition Tri4Finite : FiniteQuiver Tri4Quiver :=
  @Build_FiniteQuiver Tri4Quiver 3 Ord3_node Ord3_index Ord3_node_rt
    Tri4_ecount Tri4_edge Tri4_eindex Tri4_edge_rt.

Definition Tri4Presentation : FinitePresentation := {|
  fp_quiver := Tri4Quiver;
  fp_finite := Tri4Finite;
  fp_eqns := Tri4Eqns
|}.

Definition Tri4 : Category := FinitelyPresented Tri4Presentation.

Lemma tri4_c_ab : @equiv _ (@homset Tri4 Ord3_0 Ord3_2) t4_c t4_ab.
Proof. apply cc_gen. exists Fin.F1. split; reflexivity. Qed.

Lemma tri4_d_ab : @equiv _ (@homset Tri4 Ord3_0 Ord3_2) t4_d t4_ab.
Proof. apply cc_gen. exists (Fin.FS Fin.F1). split; reflexivity. Qed.

(* The two relations collapse the three-element 0 -> 2 hom-set of the free
   category to one class; every other hom-set was already a singleton or
   empty, so the presented category is thin. *)
Theorem tri4_thin (x y : Ord3Node) (p q : x ~{Tri4}~> y) : p ≈ q.
Proof.
  pose proof (t4_classify y x p) as Hp.
  pose proof (t4_classify y x q) as Hq.
  destruct x, y; simpl in Hp, Hq;
    try contradiction;
    try (subst; apply cc_refl).
  destruct Hp as [[Hp | Hp] | Hp]; destruct Hq as [[Hq | Hq] | Hq]; subst.
  - apply cc_refl.
  - exact (cc_trans tri4_c_ab (cc_sym tri4_d_ab)).
  - exact tri4_c_ab.
  - exact (cc_trans tri4_d_ab (cc_sym tri4_c_ab)).
  - apply cc_refl.
  - exact tri4_d_ab.
  - exact (cc_sym tri4_c_ab).
  - exact (cc_sym tri4_d_ab).
  - apply cc_refl.
Qed.

Definition tri4_equiv_dec (x y : Ord3Node) (p q : x ~{Tri4}~> y) :
  ((p ≈ q) + (p ≈ q → False))%type := inl (tri4_thin x y p q).

Definition t4_edge_arr (x y : Ord3Node) (e : Tri4Edge x y) :
  o3_ord x ~{_3}~> o3_ord y :=
  match e with
  | Tri4_a => le_t_S le_t_n
  | Tri4_b => le_t_S le_t_n
  | Tri4_c => le_t_S (le_t_S le_t_n)
  | Tri4_d => le_t_S (le_t_S le_t_n)
  end.

Definition t4_qhom : QuiverHomomorphism Tri4Quiver (QuiverOfCat _3) :=
  Build_QuiverHomomorphism Tri4Quiver (QuiverOfCat _3) o3_ord t4_edge_arr
    (fun x y e e' _ => ord_thin _ _).

Definition Tri4_to : Tri4 ⟶ _3 :=
  @PresentedFunctor Tri4Quiver (fe_rel Tri4Eqns) _3 t4_qhom
    (fun x y f g _ => ord_thin _ _).

Definition tri4_gen {x y : Ord3Node} (e : @edges Tri4Quiver x y) :
  x ~{Tri4}~> y :=
  @pgen Tri4Quiver (fe_rel Tri4Eqns) x y e.

Definition t4_arr : ∀ i j : nat, le_t i j → (o3_node i ~{Tri4}~> o3_node j).
Proof.
  intros i j; destruct i as [| [| i]]; destruct j as [| [| j]]; intro H.
  - exact id.
  - exact (tri4_gen Tri4_a).
  - exact (tri4_gen Tri4_c).
  - exact (False_rect _ (le_t_zero_absurd H)).
  - exact id.
  - exact (tri4_gen Tri4_b).
  - exact (False_rect _ (le_t_zero_absurd H)).
  - exact (False_rect _ (le_t_zero_absurd (le_t_SS_inv H))).
  - exact id.
Defined.

Program Definition Tri4_from : _3 ⟶ Tri4 := {|
  fobj := fun x => o3_node (ord_val x);
  fmap := fun x y f => t4_arr (ord_val x) (ord_val y) f
|}.
Solve All Obligations with (repeat intro; apply tri4_thin).

(* Presentation (iv) presents the category 3. *)
Program Definition Tri4_iso : Tri4 ≅[StrictCat] _3 := {|
  to := Tri4_to;
  from := Tri4_from
|}.
Next Obligation.
  exists o3_ord_node; intros x y f; apply ord_thin.
Qed.
Next Obligation.
  exists o3_node_ord; intros x y f; apply tri4_thin.
Qed.

(* The four-generator quiver's free category has EIGHT arrows -- the three
   0 -> 2 paths are pairwise distinct by the three lemmas above -- so this
   presentation makes exactly two identifications. *)
Definition tri4_free_homcount (x y : Ord3Node) : nat :=
  match x, y with
  | Ord3_0, Ord3_0 => 1%nat
  | Ord3_1, Ord3_1 => 1%nat
  | Ord3_2, Ord3_2 => 1%nat
  | Ord3_0, Ord3_1 => 1%nat
  | Ord3_1, Ord3_2 => 1%nat
  | Ord3_0, Ord3_2 => 3%nat
  | _, _ => 0%nat
  end.

Definition tri4_free_arrow_total : nat :=
  fold_right (fun q n => tri4_free_homcount (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem tri4_free_arrow_total_8 : tri4_free_arrow_total = 8%nat.
Proof. reflexivity. Qed.

Example tri4_merge_arithmetic :
  (tri4_free_arrow_total - three_arrow_total)%nat = 2%nat := eq_refl.

(* ---------- (H) the four presentations, compared ---------- *)

(* Generator counts, folded over every ordered pair of nodes. *)
Definition lin3_gen_total : nat :=
  fold_right (fun q n => lin3_ecount (fst q) (snd q) + n)%nat 0%nat
    three_all_pairs.

Theorem lin3_gen_total_2 : lin3_gen_total = 2%nat.
Proof. reflexivity. Qed.

Definition ord3_gen_total : nat :=
  fold_right (fun q n => Ord3_ecount (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem ord3_gen_total_3 : ord3_gen_total = 3%nat.
Proof. reflexivity. Qed.

Definition tri4_gen_total : nat :=
  fold_right (fun q n => Tri4_ecount (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem tri4_gen_total_4 : tri4_gen_total = 4%nat.
Proof. reflexivity. Qed.

(* Relation counts, likewise.  Presentations (i) and (iii) share their
   quiver, hence their generator count and their relation count. *)
Definition lin3_rel_total : nat :=
  fold_right (fun q n => @fe_count _ Lin3Eqns (fst q) (snd q) + n)%nat 0%nat
    three_all_pairs.

Theorem lin3_rel_total_0 : lin3_rel_total = 0%nat.
Proof. reflexivity. Qed.

Definition ord3_rel_total : nat :=
  fold_right (fun q n => @fe_count _ Ord3Eqns (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem ord3_rel_total_1 : ord3_rel_total = 1%nat.
Proof. reflexivity. Qed.

Definition ord3_rev_rel_total : nat :=
  fold_right
    (fun q n => @fe_count _ Ord3RevEqns (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem ord3_rev_rel_total_1 : ord3_rev_rel_total = 1%nat.
Proof. reflexivity. Qed.

Definition tri4_rel_total : nat :=
  fold_right (fun q n => @fe_count _ Tri4Eqns (fst q) (snd q) + n)%nat 0%nat
    ord3_all_pairs.

Theorem tri4_rel_total_2 : tri4_rel_total = 2%nat.
Proof. reflexivity. Qed.

(* The three quivers have three different generator counts, so no two of
   (i), (ii), (iv) are the same presentation data; (iii) shares (i)'s
   quiver, hence its generator count, and so differs from (ii) and (iv) by
   the same numbers. *)
Theorem three_presentation_counts_differ :
  (((ord3_gen_total = lin3_gen_total → False) *
    (ord3_gen_total = tri4_gen_total → False)) *
   (lin3_gen_total = tri4_gen_total → False))%type.
Proof.
  repeat split; unfold ord3_gen_total, lin3_gen_total, tri4_gen_total;
    discriminate.
Qed.

Example ord3_rev_shares_ord3_quiver :
  fp_quiver Ord3RevPresentation = fp_quiver Ord3Presentation := eq_refl.

(* (i) and (iii) agree on both counts, so what tells them apart is the
   equation itself: the left-hand side of (i)'s is the generator c and of
   (iii)'s is the composite path b ∘ a... *)
Example ord3_lhs_is_c :
  @fe_lhs _ Ord3Eqns Ord3_0 Ord3_2 Fin.F1 = ord3_path_c := eq_refl.

Example ord3_rev_lhs_is_ab :
  @fe_lhs _ Ord3RevEqns Ord3_0 Ord3_2 Fin.F1 = ord3_path_ab := eq_refl.

(* ...and those two are not the same arrow of the free category.  This is
   Presented.v:441's [ord3_free_distinct], consumed; it is the reason the
   two presentation records are distinguishable even though the categories
   they present are isomorphic. *)
Theorem ord3_presentations_differ : ord3_path_c ≈ ord3_path_ab → False.
Proof. exact ord3_free_distinct. Qed.

(* AWODEY §4.5 EXERCISE 3.  Four presentations of the category 3.  Every
   one is isomorphic to [_3] in [StrictCat], hence to each of the others;
   and by the counts above the four presentation records are pairwise
   distinguishable. *)
Definition three_four_presentations :
  (((Ord3 ≅[StrictCat] _3) * (Lin3 ≅[StrictCat] _3)) *
   ((Ord3Rev ≅[StrictCat] _3) * (Tri4 ≅[StrictCat] _3)))%type :=
  ((Ord3_iso, Lin3_iso), (Ord3Rev_iso, Tri4_iso)).

(* The four in one place, as data rather than as prose. *)
Definition three_presentations : list FinitePresentation :=
  Ord3Presentation :: Lin3Presentation ::
  Ord3RevPresentation :: Tri4Presentation :: nil.

Example three_presentations_4 : length three_presentations = 4%nat := eq_refl.
