Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Construction.Free.Quiver.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(** * Concrete free categories, and the finite ordinals as free categories *)

(* nLab:      https://ncatlab.org/nlab/show/free+category
   nLab:      https://ncatlab.org/nlab/show/quiver
   nLab:      https://ncatlab.org/nlab/show/thin+category
   Book:      Mac Lane, Categories for the Working Mathematician, 2nd ed.,
              GTM 5, Springer 1998, §II.7, printed pp. 50-51

   CITED BY LOCATION; the printed text was not consulted.  The two items worked
   here are the in-tree catalog entries [maclane:II.7:remark3] (the examples of
   free categories) and [maclane:II.7:ex2] (finite ordinals are free), in
   doc/plan/books/maclane/inventory/II.json.  Everything attributed to Mac Lane
   below paraphrases the CATALOG'S summaries, which are themselves paraphrases
   and not the book's wording.

   Construction/Free/Quiver.v builds the free category on a quiver and proves
   its universal property ([FreeOnQuiver], [UniversalArrowQuiverCat],
   [FreeForgetfulAdjunction]).  What it does not do is say what any particular
   free category IS.  This file identifies three of them by name.

   THE FOUR EXAMPLES.  The catalog's [maclane:II.7:remark3] lists three, and
   the exercise [maclane:II.7:ex2] adds the fourth:

     (1) THE LOOP.  One node with a single endo-edge; the free category has
         arrows 1, f, f^2, ..., i.e. the free monoid on one generator read as a
         one-object category.  NOT BUILT HERE.  That identification belongs to
         issue #802 ("the free category on a single loop is the additive
         naturals"), which owns it together with the general fact that a free
         category has only identity isomorphisms.  Neither is in the tree yet:
         as of this file there is no Construction/Free/Quiver/Loop.v.  It is
         recapped here only so the reader knows which of Mac Lane's examples
         this file does and does not cover.

     (2) THE WALKING ARROW.  One edge with distinct endpoints; the free
         category is that arrow plus an identity at each end.  Delivered as
         [arrow_free : FreeOnQuiver ArrowQuiver ≅[StrictCat] _2].

     (3) THE COMPOSABLE PAIR.  Three nodes . -> . -> .; the free category is
         the commutative triangle -- three identities, the two generators, and
         one composite.  Delivered as
         [chain_free : FreeOnQuiver (LinQuiver 3) ≅[StrictCat] _3], an INSTANCE
         of (4) rather than a second development, together with an exhaustive
         hom-set description ([chain_hom_01] and its eight siblings) and
         [chain_e10_length = 2], which says the composite is literally the
         two-edge path and not a further generator.

     (4) THE FINITE ORDINALS.  Exercise 2.  Delivered as
         [ordinal_free m : FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m],
         for EVERY m -- the empty ordinal included, through the separate
         [ordinal_free_0], since the donor [Functor_of_Steps] is stated for
         [Ordinal (S n)].

   STRENGTHS, stated precisely.  All three DELIVERED identifications above --
   (2), (3) and (4); (1) is not built here -- are isomorphisms in [StrictCat], i.e. up to [Functor_StrictEq_Setoid]: equal
   object maps on the nose, with the morphism maps agreeing after transport.
   That is the STRONGER of the two readings the library supports.  The weaker
   [Cat] reading -- where an isomorphism is only an EQUIVALENCE of categories,
   [Cat]'s hom-setoid being [Functor_Setoid] -- is recorded alongside as
   [arrow_free_Cat] and [ordinal_free_Cat], each obtained from the strict form
   through [strict_equiv_implies_fun_equiv] (Instance/StrictCat/ToCat.v).  For
   the walking arrow the strict witnesses are literally [eq_refl], both
   comparison functors being the identity on objects; for the nonempty ordinals
   they are [ord_clamp_id], the backward functor's object map being [Ordinal m]'s
   own clamping, and for the empty one they are vacuous.

   Instance/Ordinal.v's header previously recorded the [StrictCat] form of (4)
   as "a further theorem that is NOT delivered in this file and remains open".
   It is [ordinal_free] here, and that note has been updated to say so.

   THE ENGINE is one lemma, [graded_free_thin]: if a quiver carries a rank
   function on nodes such that every edge raises the rank by exactly one, the
   rank is injective on nodes, and parallel edges are unique up to the edge
   setoid, then its free category is THIN -- at most one path between any two
   nodes.  Every identification below then costs almost nothing, because each
   round trip and each functor law is an equation between parallel arrows: in
   [_2] by [Two_thin], in [Ordinal m] by [le_t_irr], and in the free category
   by [graded_free_thin] itself.  The one place with genuine content is
   [graded_het], an induction over [tlist] paths in the HETEROGENEOUS form the
   library's path equivalence uses, because two parallel paths pass through
   intermediate nodes that are only PROPOSITIONALLY equal, and the equivalence
   [tlist'_quiver_equiv] carries exactly that equality as data.

   NO UIP IS ASSUMED.  The induction needs uniqueness of identity proofs on
   nodes, and gets it: rank-injectivity makes node equality decidable
   ([graded_node_eq_dec]), and Hedberg's theorem through
   [Eqdep_dec.UIP_dec] then supplies [graded_node_uip], axiom-free.  The
   uniqueness of the linear quiver's edges is the same step at [nat]
   ([linear_edge_unique]).  No axiom, no functional extensionality, and no
   classical reasoning is used anywhere in this file; every named constant and
   every Program obligation reports "Closed under the global context".

   UNIVERSES, measured and attributed.  Every identification below in whose
   statement a quiver appears is stated at [Category@{Set Set Set}], and this is
   FORCED rather than an artifact of minimization.  [Build_Quiver_Standard_Eq] (Construction/Free/Quiver.v:194),
   the tree's only smart constructor for a quiver with a strict edge setoid,
   has type [... -> Quiver@{u u0 Set}]: its PROOF universe is pinned to [Set].
   [FreeOnQuiver@{o h p}] carries the constraints [o <= h] and [h <= p] (they
   are printed in its own universe context), so [p = Set] forces [h <= Set], and
   [o <= h] then pulls the object universe down with it.  Attempting to state
   [ordinal_free] over universes declared by [Universes o h] is therefore
   rejected outright.  The reproducible evidence for the pin, rather than any
   particular error text (the message varies with the probe's shape, so no
   quotation of it is given here): [LinQuiver@{o h} m : Quiver@{o h h}] is
   REJECTED while [Quiver@{o h Set}] is accepted -- the pin already bites at
   the quiver -- and letting the universes be inferred typechecks only by
   silently forcing them, the resulting constant printing the constraints
   [Set = o] and [Set = h].

   The consequence is that these are identifications of SMALL categories at the
   [Set] level, and that a consumer wanting them at a larger level cannot get
   there by instantiation.  Lifting the restriction would mean changing
   [Build_Quiver_Standard_Eq], which is shared with FIVE files outside
   Construction/Free/Quiver.v itself -- Construction/Free/Quiver/Concrete.v,
   Construction/Free/Quiver/Presented.v, Construction/Free/TwoFunctors.v,
   Theory/Diagram.v and Test/Issue138.v -- and is out of scope here.  Two contrasts are worth recording.  The engine is NOT pinned:
   [graded_free_thin@{u u0 u1}] is stated over an arbitrary
   [Quiver@{u u0 u1}], so thinness of a graded quiver's free category is
   available at any level, and only the instances built through
   [Build_Quiver_Standard_Eq] are confined.  And [Ordinal_2_strict_iso], the
   one identification below in whose statement no quiver appears, leaves the
   OBJECT universe free -- [Ordinal@{u0 Set Set} 2] against [_2@{u0 u1}] --
   its hom and proof universes being pinned instead by [_2]'s own
   [TwoHom : TwoObj -> TwoObj -> Set].  [linear_hom_iff] escapes nothing: it
   carries no universe binders at all ([@{}]), i.e. it is monomorphic.  Those
   are the constants measured; no claim is made about any other.

   WHAT IS NOT HERE.  The loop example, per the delegation above.  A bijection
   between paths and ordinal arrows on the nose: what is proved is that the two
   categories are isomorphic in [StrictCat], and the hom-level content is
   [linear_hom_iff] -- inhabited exactly when the indices are ordered, and
   thin -- rather than an identification of the underlying types.  And the
   agreement between [arrow_free] and [linear_2_free]: they identify the free
   categories on two DIFFERENT quivers with [_2], one whose nodes are [TwoObj]
   and one whose nodes are the objects of [Ordinal 2], so neither subsumes the
   other and no comparison between them is stated. *)

#[local] Existing Instance edgeset.

(* Every obligation below is discharged explicitly; no proof depends on a
   Program-generated tactic.  (Construction/Free/Quiver/Concrete.v does the
   same, for the same reason.) *)
#[local] Obligation Tactic := idtac.

(* ---------- graded quivers have thin free categories ---------- *)

Section Graded.

Context (G : Quiver).
Context (rank : @nodes G → nat).

Hypothesis edge_rank : ∀ x y : G, edges x y → rank y = S (rank x).
Hypothesis rank_inj  : ∀ x y : G, rank x = rank y → x = y.
Hypothesis edge_unique : ∀ (x y : G) (e e' : edges x y), e ≈ e'.

Definition graded_node_eq_dec (x y : G) : {x = y} + {x ≠ y} :=
  match PeanoNat.Nat.eq_dec (rank x) (rank y) with
  | left e   => left (rank_inj x y e)
  | right ne => right (fun H => ne (f_equal rank H))
  end.

Lemma graded_node_uip (x y : G) (e e' : x = y) : e = e'.
Proof using G rank rank_inj. apply (UIP_dec graded_node_eq_dec). Qed.

(* Every edge raises the rank by one, so a path's length is the rank
   difference of its endpoints. *)
Lemma graded_len (j i : G) (p : tlist edges i j) :
  rank j = (tlist_length p + rank i)%nat.
Proof using G rank edge_rank.
  induction p as [| i0 i1 e t IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite (edge_rank _ _ e).
    lia.
Qed.

(* Hence no path returns to its source unless it is empty. *)
Lemma graded_loop_nil (k : G) : ∀ (i : G) (g : tlist edges i k) (e : k = i),
  Logic.transport_r (fun z => @tlist' _ edges k z) e g = tnil.
Proof using G rank edge_rank rank_inj.
  intros i g; induction g as [| i0 i1 e t IH]; intro q.
  - now rewrite (graded_node_uip _ _ q eq_refl).
  - exfalso.
    pose proof (graded_len _ _ t) as Ht.
    rewrite (edge_rank _ _ e) in Ht.
    pose proof (f_equal rank q) as Hq.
    lia.
Qed.

(* The heterogeneous form of uniqueness: two paths with a common target and
   propositionally equal sources are equivalent along that equality.  This is
   the form the induction needs, since the intermediate nodes of two parallel
   paths are only propositionally equal. *)
Lemma graded_het (k : G) : ∀ (i : G) (f : tlist edges i k)
                                  (j : G) (g : tlist edges j k) (e : i = j),
  tlist'_quiver_equiv G k i j f g e.
Proof using G rank edge_rank rank_inj edge_unique.
  intros i f; induction f as [| i0 i1 fhead ftail IH]; intros j g e.
  - simpl; symmetry; now apply graded_loop_nil.
  - destruct g as [| j0 j1 ghead gtail].
    + (* a nonempty path cannot be parallel to the empty one *)
      exfalso.
      pose proof (graded_len _ _ ftail) as Ht.
      rewrite (edge_rank _ _ fhead) in Ht.
      pose proof (f_equal rank e) as He.
      lia.
    + (* both nonempty: the intermediate nodes agree by rank *)
      destruct e.
      assert (q : i1 = j1).
      { apply rank_inj.
        rewrite (edge_rank _ _ fhead), (edge_rank _ _ ghead).
        reflexivity. }
      destruct q.
      exists eq_refl.
      * apply edge_unique.
      * apply IH.
Qed.

(* At most one path between any two nodes: the free category is thin. *)
Theorem graded_free_thin (x y : FreeOnQuiver G) (p q : x ~> y) : p ≈ q.
Proof using G rank edge_rank rank_inj edge_unique.
  exact (graded_het y x p x q eq_refl).
Qed.

(* No path runs downwards. *)
Theorem graded_no_path (x y : FreeOnQuiver G) (p : x ~> y) :
  (rank x <= rank y)%nat.
Proof using G rank edge_rank. pose proof (graded_len _ _ p); lia. Qed.

End Graded.

(* ---------- the walking arrow ---------- *)

(* Two nodes, one edge between them.  The nodes are [TwoObj] itself, so both
   comparison functors below are the identity on objects. *)
Definition arrow_edges (x y : TwoObj) : Type :=
  match x with
  | TwoX => match y with
            | TwoX => Empty_set
            | TwoY => poly_unit
            end
  | TwoY => Empty_set
  end.

Definition ArrowQuiver : Quiver := Build_Quiver_Standard_Eq TwoObj arrow_edges.

Definition arrow_rank (x : TwoObj) : nat :=
  match x with TwoX => 0%nat | TwoY => 1%nat end.

Lemma arrow_edge_rank (x y : TwoObj) :
  @edges ArrowQuiver x y → arrow_rank y = S (arrow_rank x).
Proof. destruct x, y; simpl; intro e; try (destruct e); reflexivity. Qed.

Lemma arrow_rank_inj (x y : TwoObj) : arrow_rank x = arrow_rank y → x = y.
Proof. destruct x, y; simpl; intro H; try reflexivity; discriminate. Qed.

Lemma arrow_edge_unique (x y : TwoObj) (e e' : @edges ArrowQuiver x y) : e ≈ e'.
Proof.
  destruct x, y; simpl in e, e';
    try destruct e; try destruct e'; reflexivity.
Qed.

(* At most one path between any two nodes of the walking-arrow quiver. *)
Theorem arrow_free_thin (x y : FreeOnQuiver ArrowQuiver) (p q : x ~> y) : p ≈ q.
Proof.
  exact (graded_free_thin ArrowQuiver arrow_rank
           arrow_edge_rank arrow_rank_inj arrow_edge_unique x y p q).
Qed.

(* The generating edge, as a path. *)
Definition arrow_gen : @edges ArrowQuiver TwoX TwoY := ttt.

Definition arrow_path : TwoX ~{FreeOnQuiver ArrowQuiver}~> TwoY :=
  tlist_singleton arrow_gen.

Definition arrow_map (x y : TwoObj) : @edges ArrowQuiver x y → TwoHom x y :=
  match x as x0 return @edges ArrowQuiver x0 y → TwoHom x0 y with
  | TwoX => match y as y0 return @edges ArrowQuiver TwoX y0 → TwoHom TwoX y0 with
            | TwoX => fun e => match e return TwoHom TwoX TwoX with end
            | TwoY => fun _ => TwoXY
            end
  | TwoY => fun e => match e return TwoHom TwoY y with end
  end.

Definition arrow_hom : QuiverHomomorphism ArrowQuiver (QuiverOfCat _2) :=
  Build_QuiverHomomorphism ArrowQuiver (QuiverOfCat _2)
    (fun x => x) arrow_map (fun x y e e' H => f_equal (arrow_map x y) H).

Definition Arrow_to : FreeOnQuiver ArrowQuiver ⟶ _2 :=
  InducedFunctor ArrowQuiver arrow_hom.

Definition arrow_unmap (x y : TwoObj) (f : TwoHom x y) :
  x ~{FreeOnQuiver ArrowQuiver}~> y :=
  match f in TwoHom x0 y0 return x0 ~{FreeOnQuiver ArrowQuiver}~> y0 with
  | TwoIdX => tnil
  | TwoIdY => tnil
  | TwoXY  => arrow_path
  end.

(* Every functor law is an equation between parallel paths, so [arrow_free_thin]
   discharges all three. *)
Definition Arrow_from : _2 ⟶ FreeOnQuiver ArrowQuiver :=
  Build_Functor _2 (FreeOnQuiver ArrowQuiver)
    (fun x => x)
    arrow_unmap
    (fun x y f g _ => arrow_free_thin x y _ _)
    (fun x => arrow_free_thin x x _ _)
    (fun x y z f g => arrow_free_thin x z _ _).

(* Mac Lane's second example: the free category on one arrow with distinct
   endpoints is that arrow together with an identity at each end -- which is
   exactly the walking arrow [_2].  Both functors are the IDENTITY on objects,
   so both strict-equality witnesses are [eq_refl]. *)
Program Definition arrow_free : FreeOnQuiver ArrowQuiver ≅[StrictCat] _2 := {|
  to   := Arrow_to;
  from := Arrow_from
|}.
Next Obligation.
  exists (fun _ => eq_refl); intros x y f; apply Two_thin.
Qed.
Next Obligation.
  exists (fun _ => eq_refl); intros x y f; apply arrow_free_thin.
Qed.

(* The same identification read in [Cat], where functors are compared only up
   to natural isomorphism.  This is strictly weaker than the above. *)
Definition arrow_free_Cat : FreeOnQuiver ArrowQuiver ≅[Cat] _2 :=
  @Build_Isomorphism Cat _ _ Arrow_to Arrow_from
    (strict_equiv_implies_fun_equiv _ _ (iso_to_from arrow_free))
    (strict_equiv_implies_fun_equiv _ _ (iso_from_to arrow_free)).

(* ---------- every finite ordinal is free on its linear quiver ---------- *)

(* Nodes are the objects of [Ordinal m] themselves, and an edge x -> y is a
   proof that y is the successor of x.  Edges are therefore unique by UIP on
   [nat] (Hedberg, through [Eqdep_dec.UIP_dec] -- no axiom is assumed), and the
   quiver has exactly the m-1 generating steps 0 -> 1 -> ... -> m-1.  The
   numbering counts NODES, matching [Ordinal m]'s own convention: [LinQuiver 0]
   is empty, [LinQuiver 2] is the walking arrow and [LinQuiver 3] the
   composable pair. *)
Definition linear_edges@{o h} {m : nat} (x y : Ord_obj@{o} m) : Type@{h} :=
  (S (ord_val x) = ord_val y)%nat.

Definition LinQuiver@{o h} (m : nat) : Quiver@{o h Set} :=
  Build_Quiver_Standard_Eq@{o h} (Ord_obj@{o} m) (@linear_edges@{o h} m).

Lemma linear_edge_rank {m} (x y : LinQuiver m) :
  @edges (LinQuiver m) x y → ord_val y = S (ord_val x).
Proof. intro e; exact (eq_sym e). Qed.

Lemma linear_rank_inj {m} (x y : LinQuiver m) : ord_val x = ord_val y → x = y.
Proof. apply ord_obj_eq. Qed.

Lemma linear_edge_unique {m} (x y : LinQuiver m)
  (e e' : @edges (LinQuiver m) x y) : e ≈ e'.
Proof. apply (UIP_dec PeanoNat.Nat.eq_dec). Qed.

(* At most one path between any two nodes of the linear quiver. *)
Theorem linear_free_thin {m} (x y : FreeOnQuiver (LinQuiver m)) (p q : x ~> y) :
  p ≈ q.
Proof.
  exact (graded_free_thin (LinQuiver m) (@ord_val m)
           (@linear_edge_rank m) (@linear_rank_inj m) (@linear_edge_unique m)
           x y p q).
Qed.

(* And a path exists only upwards. *)
Theorem linear_no_descent {m} (x y : FreeOnQuiver (LinQuiver m)) (p : x ~> y) :
  (ord_val x <= ord_val y)%nat.
Proof.
  exact (graded_no_path (LinQuiver m) (@ord_val m) (@linear_edge_rank m) x y p).
Qed.

(* The comparison into the ordinal: an edge is the generating step.  This half
   is uniform in m, the empty ordinal included. *)
Definition linear_arrow {m} {x y : LinQuiver m} (e : @edges (LinQuiver m) x y) :
  x ~{Ordinal m}~> y :=
  match e in _ = z return le_t (ord_val x) z with
  | eq_refl => le_t_S le_t_n
  end.

Definition linear_hom (m : nat) :
  QuiverHomomorphism (LinQuiver m) (QuiverOfCat (Ordinal m)) :=
  Build_QuiverHomomorphism (LinQuiver m) (QuiverOfCat (Ordinal m))
    (fun x => x) (fun x y e => linear_arrow e)
    (fun x y e e' H => f_equal (fun t => @linear_arrow m x y t) H).

Definition Linear_to (m : nat) : FreeOnQuiver (LinQuiver m) ⟶ Ordinal m :=
  InducedFunctor (LinQuiver m) (linear_hom m).

(* The comparison out of the ordinal is [Instance/Ordinal.v]'s [Functor_of_Steps]
   applied to the n generating edges, taken at the clamped indices.  That donor
   is stated for [Ordinal (S n)], so this half splits on whether the ordinal is
   empty. *)
Lemma linear_min_step (n k : nat) (H : le_t (S k) n) :
  (S (Nat.min k n) = Nat.min (S k) n)%nat.
Proof.
  rewrite (le_t_min_l k n (le_t_trans (le_t_S le_t_n) H)).
  now rewrite (le_t_min_l (S k) n H).
Qed.

Definition linear_step {n} (k : nat) (H : le_t (S k) n) :
  @linear_edges (S n) (@ord_clamp n k) (@ord_clamp n (S k)) := linear_min_step n k H.

Definition linear_steps (n : nat) :
  @OrdSteps (FreeOnQuiver (LinQuiver (S n))) n (fun k => @ord_clamp n k) :=
  fun k H => tlist_singleton (@linear_step n k H).

Definition Linear_from (n : nat) :
  Ordinal (S n) ⟶ FreeOnQuiver (LinQuiver (S n)) :=
  Functor_of_Steps (linear_steps n).

(* The nonempty case.  Both round trips are equations between parallel arrows
   -- of [Ordinal (S n)], which is thin by [le_t_irr], and of the free category,
   which is thin by [linear_free_thin] -- so the transports carry no content. *)
Program Definition ordinal_free_S (n : nat) :
  FreeOnQuiver (LinQuiver (S n)) ≅[StrictCat] Ordinal (S n) := {|
  to   := Linear_to (S n);
  from := Linear_from n
|}.
Next Obligation.
  intros n.
  exists (fun x => @ord_clamp_id n x); intros x y f; apply le_t_irr.
Qed.
Next Obligation.
  intros n.
  exists (fun x => @ord_clamp_id n x); intros x y f; apply linear_free_thin.
Qed.

(* The empty case, where both categories have no objects at all. *)
Definition Linear_from_0 : Ordinal 0 ⟶ FreeOnQuiver (LinQuiver 0) :=
  Build_Functor (Ordinal 0) (FreeOnQuiver (LinQuiver 0))
    (fun x => x)
    (fun x y f => False_rect _ (ord_0_empty x))
    (fun x y f g H => False_rect _ (ord_0_empty x))
    (fun x => False_rect _ (ord_0_empty x))
    (fun x y z f g => False_rect _ (ord_0_empty x)).

Program Definition ordinal_free_0 :
  FreeOnQuiver (LinQuiver 0) ≅[StrictCat] Ordinal 0 := {|
  to   := Linear_to 0;
  from := Linear_from_0
|}.
Next Obligation.
  exists (fun x => False_rect _ (ord_0_empty x));
    intros x y f; destruct (ord_0_empty x).
Qed.
Next Obligation.
  exists (fun x => False_rect _ (ord_0_empty x));
    intros x y f; destruct (ord_0_empty x).
Qed.

(* Mac Lane II.7 Exercise 2, as stated: EVERY finite ordinal is a free
   category -- free on the linear quiver with the same nodes. *)
Definition ordinal_free (m : nat) :
  FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m :=
  match m with
  | O   => ordinal_free_0
  | S n => ordinal_free_S n
  end.

(* The same reading in [Cat], where functors are compared only up to natural
   isomorphism.  This is strictly weaker than the above. *)
Definition ordinal_free_Cat (m : nat) :
  FreeOnQuiver (LinQuiver m) ≅[Cat] Ordinal m :=
  @Build_Isomorphism Cat _ _ (to (ordinal_free m)) (from (ordinal_free m))
    (strict_equiv_implies_fun_equiv _ _ (iso_to_from (ordinal_free m)))
    (strict_equiv_implies_fun_equiv _ _ (iso_from_to (ordinal_free m))).

(* ---------- existence of paths, and the exhaustive hom description ---------- *)

Definition free_mor_of_eq {G : Quiver} {x y : FreeOnQuiver G} (e : x = y) : x ~> y :=
  match e in _ = z return x ~{FreeOnQuiver G}~> z with
  | eq_refl => id
  end.

(* The converse of [linear_no_descent]: whenever the indices are ordered there
   IS a path, obtained by transporting the ordinal's own arrow back along
   [Linear_from]. *)
Definition linear_path_of_le {n} (x y : FreeOnQuiver (LinQuiver (S n)))
  (H : (ord_val x <= ord_val y)%nat) : x ~> y :=
  @free_mor_of_eq (LinQuiver (S n)) _ _ (@ord_clamp_id n y)
    ∘ fmap[Linear_from n] (le_t_of_le H)
    ∘ @free_mor_of_eq (LinQuiver (S n)) _ _ (eq_sym (@ord_clamp_id n x)).

(* Together with thinness this classifies every hom-set of the free category on
   a linear quiver: it is empty when the indices are out of order, and a
   singleton otherwise. *)
Theorem linear_hom_iff {n} (x y : FreeOnQuiver (LinQuiver (S n))) :
  ((x ~> y) → (ord_val x <= ord_val y)%nat) *
  ((ord_val x <= ord_val y)%nat → (x ~> y)) *
  (∀ p q : x ~> y, p ≈ q).
Proof.
  split; [split |].
  - exact (@linear_no_descent (S n) x y).
  - exact (@linear_path_of_le n x y).
  - exact (@linear_free_thin (S n) x y).
Qed.

(* ---------- the composable pair: the three-node instance ---------- *)

(* Mac Lane's third example: the free category on . -> . -> . is the
   commutative triangle -- three identities, the two generators, and one
   composite.  This is [ordinal_free] at three nodes, whose target [Ordinal 3]
   is Instance/Ordinal.v's [_3]; it is an instance, not a second development. *)
Definition chain_free : FreeOnQuiver (LinQuiver 3) ≅[StrictCat] _3 :=
  ordinal_free 3.

Definition chain_e0 : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_1 :=
  tlist_singleton (eq_refl : @linear_edges 3 ord3_0 ord3_1).

Definition chain_e1 : ord3_1 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2 :=
  tlist_singleton (eq_refl : @linear_edges 3 ord3_1 ord3_2).

Definition chain_e10 : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2 :=
  chain_e1 ∘ chain_e0.

(* The composite is literally the two-edge path, not a further generator. *)
Lemma chain_e0_length : tlist_length chain_e0 = 1%nat.
Proof. reflexivity. Qed.

Lemma chain_e1_length : tlist_length chain_e1 = 1%nat.
Proof. reflexivity. Qed.

Lemma chain_e10_length : tlist_length chain_e10 = 2%nat.
Proof. reflexivity. Qed.

(* The three ascending hom-sets are singletons ... *)
Theorem chain_hom_01 (p : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_1) :
  p ≈ chain_e0.
Proof. apply linear_free_thin. Qed.

Theorem chain_hom_12 (p : ord3_1 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2) :
  p ≈ chain_e1.
Proof. apply linear_free_thin. Qed.

Theorem chain_hom_02 (p : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2) :
  p ≈ chain_e10.
Proof. apply linear_free_thin. Qed.

(* ... the three diagonal ones contain only the identity ... *)
Theorem chain_hom_00 (p : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_0) :
  p ≈ id.
Proof. apply linear_free_thin. Qed.

Theorem chain_hom_11 (p : ord3_1 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_1) :
  p ≈ id.
Proof. apply linear_free_thin. Qed.

Theorem chain_hom_22 (p : ord3_2 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2) :
  p ≈ id.
Proof. apply linear_free_thin. Qed.

(* ... and the three descending ones are empty. *)
Theorem chain_no_10 (p : ord3_1 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_0) : False.
Proof. pose proof (linear_no_descent _ _ p) as H; simpl in H; lia. Qed.

Theorem chain_no_20 (p : ord3_2 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_0) : False.
Proof. pose proof (linear_no_descent _ _ p) as H; simpl in H; lia. Qed.

Theorem chain_no_21 (p : ord3_2 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_1) : False.
Proof. pose proof (linear_no_descent _ _ p) as H; simpl in H; lia. Qed.

(* Instance/Ordinal.v's duplicate-free count of endpoint pairs, re-exported at
   n = 3 for the reader's convenience.  NOTE what this is and is not: the
   statement mentions neither [FreeOnQuiver] nor [chain_free], and no transport
   along the isomorphism is formalized -- it is a fact about [Ordinal 3] alone,
   whose left side is TWICE the morphism count (six).  The free category's own
   six morphisms are delivered by the nine hom-set theorems above, directly. *)
Corollary chain_morphism_count : (2 * length (ord_pairs 3) = 3 * (3 + 1))%nat.
Proof. exact (ord_morphism_count 3). Qed.

(* ---------- the walking arrow, hom-set by hom-set ---------- *)

Lemma arrow_path_length : tlist_length arrow_path = 1%nat.
Proof. reflexivity. Qed.

Theorem arrow_hom_XY (p : TwoX ~{FreeOnQuiver ArrowQuiver}~> TwoY) : p ≈ arrow_path.
Proof. apply arrow_free_thin. Qed.

Theorem arrow_hom_XX (p : TwoX ~{FreeOnQuiver ArrowQuiver}~> TwoX) : p ≈ id.
Proof. apply arrow_free_thin. Qed.

Theorem arrow_hom_YY (p : TwoY ~{FreeOnQuiver ArrowQuiver}~> TwoY) : p ≈ id.
Proof. apply arrow_free_thin. Qed.

Theorem arrow_no_YX (p : TwoY ~{FreeOnQuiver ArrowQuiver}~> TwoX) : False.
Proof.
  pose proof (graded_no_path ArrowQuiver arrow_rank arrow_edge_rank _ _ p) as H.
  simpl in H; lia.
Qed.

(* Non-degeneracy.  The generating path cannot be compared with an identity
   directly -- they inhabit different hom-sets -- so the statement is that it is
   not invertible: an inverse would be a path TwoY to TwoX, and there is none.
   The free category on one arrow is therefore not a groupoid, matching
   [TwoXY_not_iso] (Instance/Two.v) across [arrow_free].  This is one instance;
   the general fact that a free category has only identity isomorphisms is
   issue #802's, and is not proved here. *)
Lemma arrow_path_not_iso :
  @IsIsomorphism (FreeOnQuiver ArrowQuiver) TwoX TwoY arrow_path → False.
Proof. intros [g _ _]; exact (arrow_no_YX g). Qed.

(* ---------- [Ordinal 2] and [_2] agree strictly ---------- *)

Lemma ord2_to_from_obj (a : TwoObj) : ord_two_of (ord_val (ord2_obj a)) = a.
Proof. now destruct a. Qed.

Lemma ord2_from_to_obj (x : Ord_obj 2) : ord2_obj (ord_two_of (ord_val x)) = x.
Proof. apply ord_obj_eq, ord_2_val. Qed.

(* Instance/Ordinal.v delivers [Ordinal_2_iso] only in [Cat].  Both categories
   are thin, so the strict form costs nothing beyond the two object equalities
   -- which are exactly the lemmas that file already proves. *)
Program Definition Ordinal_2_strict_iso : Ordinal 2 ≅[StrictCat] _2 := {|
  to   := Ordinal_2_to;
  from := Ordinal_2_from
|}.
Next Obligation.
  exists ord2_to_from_obj; intros a b f; apply ord_two_thin.
Qed.
Next Obligation.
  exists ord2_from_to_obj; intros x y f; apply le_t_irr.
Qed.

(* The walking arrow again, reached through the general theorem at two nodes.
   The free category is built on a DIFFERENT quiver -- [LinQuiver 2], whose
   nodes are the objects of [Ordinal 2] -- so this does not subsume
   [arrow_free], whose comparison functors are the identity on objects; the two
   are separate presentations of the same shape. *)
Definition linear_2_free : FreeOnQuiver (LinQuiver 2) ≅[StrictCat] _2 :=
  iso_compose Ordinal_2_strict_iso (ordinal_free 2).
