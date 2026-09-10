Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Free.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** * The free abelian group functor is not continuous *)

(* Mac Lane §V.4 Exercise 3 (book p. 118; maclane:V.4:ex3): the free
   abelian group functor Sets ⟶ Ab does not preserve limits — a left
   adjoint need not be continuous.
   nLab: https://ncatlab.org/nlab/show/continuous+functor
   Wikipedia: https://en.wikipedia.org/wiki/Free_abelian_group

   BACKGROUND.  The free abelian group functor is a left adjoint
   (Instance/Ab/Free.v's [free_ab_adjunction : FreeAb ⊣ Ab_Forget], #400),
   so it preserves colimits; Mac Lane's exercise asks for a limit it does
   not preserve, and hints at a countable product.  This file exhibits the
   discontinuity at three shapes — the empty shape, Mac Lane's countable
   product, and the binary product through the canonical comparison map —
   and packages it as the tree's first refutation of [ContinuousFunctor]
   and of [PreservesAllLimits] at a named functor.

   ONE FACT, STATED ONCE.  The free abelian group on a point has two
   distinct endomorphisms, the identity and the zero map, because its
   generator is not zero (Instance/Ab/Free.v's [free_ab_gen_not_zero], read
   at ℤ); so it is not the zero group ([free_ab_one_id_not_zero]).  Every
   refutation below is this fact plus bookkeeping: over the empty shape it
   is immediately non-terminality; over a DISCONNECTED shape
   whose diagram is constant at the point, the limit in Sets is the point
   again and every image leg is [≈ id], so the mediator would have to equal
   every leg of a competing cone at once, and a cone with legs [id] and the
   zero map has none; over the binary shape the same fact appears as
   [exl ≈ exr] after cancelling the comparison map, refuted by
   [exl ∘ (id △ 0) ≈ id] against [exr ∘ (id △ 0) ≈ 0].

   STALE PREMISES, RE-MEASURED.
     - "Neither the functor nor its target exists": FALSE.  Instance/Ab.v:201
       [Ab] and :217 [Ab_Forget]; Instance/Ab/Free.v:561 [FreeAb : Sets ⟶
       Ab], :564 [free_ab_adjunction], :494 [free_ab_universal] — the term
       algebra [FATerm] under the congruence [fa_eq], not finitely supported
       ℤ-valued functions.  Work bullet 1 (construct the functor with its
       universal property) was done by #400; nothing about the free abelian
       group is re-derived here.
     - The QA correction "consume #540's Construction/FreeAb.v … bridging
       to Instance/Ab.v's carrier": that file does not exist in the tree;
       the donor is Instance/Ab/Free.v, already over #256's [Ab], and no
       bridge is needed.
     - "no in-tree counterexample to continuity of any functor is
       recorded": PARTIAL.  Structure/Limit/Preservation/Separation.v:191's
       [sep_not_PreservesLimitCone] refutes cone-level preservation for a
       synthetic span functor, so "the library's first recorded
       discontinuity witness" is NOT claimed.  What is first, measured by a
       tree-wide search for the class names beside [False]: the first
       [ContinuousFunctor _ → False], the first [PreservesAllLimits _ →
       False], and the first non-preservation result at a named
       mathematical functor.
     - [Ab] has binary products, coproducts and biproducts
       (Instance/Ab/Coproduct.v:225/:229/:220), a zero and a terminal object
       (Instance/Ab.v:276/:244), and NO indexed products or completeness
       (Instance/Ab/Coproduct.v:106 and Instance/Rng/Free.v:79 record the
       absence).  The countable witness below needs none: the competing cone
       is supplied directly, which is why that statement is cone-level.

   WHAT IS DELIVERED (33 named constants plus 1 [Program] obligation, every
   one closed under the global context).
     (1) THE INGREDIENTS.  [SetsPoint] (the terminal object of Sets),
         [ab_zero_endo A : A ~> A] (the constant-zero homomorphism, built
         directly — see UNIVERSES for why not as [Ab_zero_hom A ∘ Ab_one A]),
         [ab_zero_endo_value] ([eq_refl] in the probe), and the separation
         [free_ab_one_id_not_zero : id ≈ ab_zero_endo (FreeAb SetsPoint) →
         False].
     (2) WITNESS 1, THE EMPTY LIMIT — the free group on a point is not
         terminal in Ab.  [empty_cone_at] (a cone over the empty diagram at
         any apex; the file's only [Program] obligation), [SetsEmptyDiagram
         := From_0 Sets], [SetsPoint_empty_IsLimitCone] and
         [SetsPoint_empty_Limit] (the point is the empty limit in Sets),
         [FreeAb_not_PreservesLimitCone_empty], and — the APEX-ONLY form,
         which the product witnesses cannot reach —
         [FreeAb_not_PreservesLimit_empty : PreservesLimit SetsEmptyDiagram
         FreeAb → False] with [FreeAb_not_PreservesAllLimits].
     (3) WITNESS 2, MAC LANE'S COUNTABLE PRODUCT.  [NatOnes] (the constant
         family at the point), [NatOneDiagram : DiscreteCat nat ⟶ Sets]
         (Structure/Limit/Comparison.v's annotated [DiscreteCat_Functor']),
         [NatOneProduct] (the point is its own countable power in Sets),
         [NatOneCone] / [NatOneCone_IsLimitCone] (through
         [discrete_IsLimitCone_of_IsIndexedProduct]), the competing cone
         [NatCompeting] with legs [nat_legs] ([id] at 0, the zero map
         above), [fmap_one_point], and
         [FreeAb_not_PreservesLimitCone_countable_product].  The MECHANISM
         is not Mac Lane's: his argument is that the comparison
         FreeAb(∏ Xₙ) → ∏ FreeAb(Xₙ) is not surjective because every
         element on the left has finite support, which needs a normal form
         or coefficient uniqueness for [FATerm] that the tree does not have
         (the Instance/Ab/Free.v INDEX bullet says so in terms); here the
         factors are the point, the product collapses to the point, and the
         legs coincide.  The SHAPE is his; the proof is not.
     (4) WITNESS 3, THE BINARY PRODUCT THROUGH THE COMPARISON MAP (the
         issue's second work bullet).  [BinOnes], [BinDiagram],
         [FreeAb_binary_cmp := binary_comparison FreeAb BinOnes] (the
         canonical FreeAb(1 × 1) → FreeAb 1 × FreeAb 1),
         [FreeAb_binary_comparison_not_iso],
         [FreeAb_not_PreservesLimitCone_binary_product] (through
         [comparison_iso_of_PreservesLimitCone]) and
         [FreeAb_not_CartesianFunctor] (through Structure/Limit/
         Comparison.v's [cartesian_functor_iff_comparison_iso]).
     (5) THE CONCLUSION.  [FreeAb_not_continuous : ContinuousFunctor FreeAb →
         False] — the issue's pinned statement, through witness 2 — and
         [FreeAb_not_continuous_via_empty] through witness 1; see UNIVERSES
         for why the countable route is the headline.
     (6) THE POSITIVE SIDE OF THE SAME ADJUNCTION.  [Ab_Forget_Continuous]
         (RAPL: Adjunction/Continuity.v's [right_adjoint_Continuous]) and
         [FreeAb_Cocontinuous] (LAPC: [left_adjoint_Cocontinuous]), one line
         each: continuity is exactly what the left adjoint lacks.
     (7) READBACKS.  [freeab_is_left_adjoint := free_ab_adjunction],
         [free_ab_one_carrier] (the carrier of the free group on a point IS
         [FATerm SetsPoint], [eq_refl]), [bin_diagram_objects] ([eq_refl]).

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 33
   constants).  No block carries an equation.  [Set] appears in exactly 12
   of the 33, from two donors, both attributed by [About] on the donor:
     - [_0@{u …} : Category@{u Set Set}] (Instance/Zero.v:28, declared
       bare, its hom at [Set]) pins the eight empty-shape constants:
       [empty_cone_at], [SetsEmptyDiagram], [SetsPoint_empty_IsLimitCone],
       [SetsPoint_empty_Limit], [FreeAb_not_PreservesLimitCone_empty],
       [FreeAb_not_PreservesLimit_empty], [FreeAb_not_PreservesAllLimits]
       and [FreeAb_not_continuous_via_empty] — [PreservesLimitCone]
       identifies the shape's hom with the ambient's, so through the empty
       shape the functor's hom level itself is [Set]:
       [FreeAb_not_continuous_via_empty] is stated for [FreeAb@{u10 Set …}],
       i.e. [Sets@{Set u} ⟶ Ab@{u Set}] only.  THAT is why the headline
       [FreeAb_not_continuous] goes through the countable product, whose
       shape [DiscreteCat nat] has free levels: it and
       [FreeAb_not_PreservesLimitCone_countable_product] carry no [Set] at
       all.  The apex-level refutation exists only at the empty shape, so
       [FreeAb_not_PreservesAllLimits] is stated at [Ab@{u Set}] and cannot
       be otherwise here.
     - [Ab_trivial@{} : AbObject@{Set Set Set}] (Instance/Ab.v:227,
       MONOMORPHIC) pins everything assembled from the trivial group —
       [Ab_one], [Ab_zero_hom], [Ab_Terminal], [Ab_Zero], [Ab_Cartesian]
       ([Set < u], [Ab@{u Set}]) — and through [Ab_Cartesian] the four
       binary-witness constants [FreeAb_binary_cmp],
       [FreeAb_binary_comparison_not_iso],
       [FreeAb_not_PreservesLimitCone_binary_product],
       [FreeAb_not_CartesianFunctor] (probe N6-N8: [Ab_trivial],
       [Ab_Terminal], [Ab_Cartesian] refused at a hom level strictly above
       [Set], [Ab] and [Ab_Forget] accepted there).  [ab_zero_endo] is built
       directly so that the core separation [free_ab_one_id_not_zero], the
       countable witness and the headline escape this pin; the composite
       [Ab_zero_hom A ∘ Ab_one A] would have carried it.  The pin is the
       donor's and is not repaired here.  ℤ itself pins nothing:
       [ab_int@{u u0 u1}] is fully polymorphic.
     - The remaining 21 constants name no [Set].

   COUNTS AND CONVENTIONS.
     - 33 [.glob] declaration heads (23 [def], 10 [prf]) plus 1 [Program]
       obligation ([empty_cone_at]), all "Closed under the global context",
       zero [Axioms:] lines; the gate carries the 33 heads, fully qualified,
       [FreeAb_not_continuous] among them ([FreeAb] itself is #400's and
       sits in Instance/Ab/Free.v's own gate entries).
     - Two [Defined] ([ab_zero_endo], [NatOneProduct]), each flipped to
       [Qed] alone in a copy of the file: [ab_zero_endo] is LOAD-BEARING
       ([ab_zero_endo_value]'s [simpl; reflexivity] and the probe's
       [eq_refl] readback need the map to reduce), [NatOneProduct] is not
       (library and probe compile unchanged) and stays transparent as data.
       Eleven [Qed] tokens (ten lemmas and theorems — every refutation
       proves a negation, so nothing downstream computes with it — and the
       obligation).
     - Closure 60 files excluding self: Structure/Limit/Comparison.v costs 4
       at the margin, Instance/Ab/Free.v 3, Instance/Ab/Coproduct.v 2,
       Instance/Sets/Cartesian.v 1, Instance/Zero.v 1, the other nineteen
       [Require]s 0; the binary/comparison witness accounts for 8 of the 60
       and is kept because it is the issue's "comparison map" bullet.
       [Coq.ZArith.ZArith] is required explicitly (for [1%Z]; the tree's 68
       other files spell it the same way).  Name collisions: none — each of
       the 33 names has 0 word occurrences elsewhere in the tree.
     - Test/ProbeFreeAbNotContinuous430.v mirrors the [Require] list and
       carries 9 refutation commands (1 instrument + N1-N3 CONVERSION +
       N4-N5 TYPING + N6-N8 UNIVERSE), each stripped one at a time in a copy
       of the whole file and each beside its accepted controls; three
       [eq_refl] readbacks; guard coverage 37 identifier tokens inside the
       refutations / 29 also named outside, comments stripped, with eight
       exhaustive exceptions (two keywords, the five refuted declarations'
       names, the absent name); rename-simulated 15/15 ([FreeAb],
       [SetsPoint], [NatOneCone], [BinDiagram], [Ab_trivial], [Ab_Terminal],
       [Ab_Cartesian], [Ab], [Ab_Forget], [FreeAb_not_continuous],
       [FreeAb_not_PreservesLimitCone_binary_product],
       [PreservesAllLimits], [PreservesLimit], [cone_leg], [FCone]; module
       paths excluded), every first break on a positive line.  [make todo]
       grows by those 9 lines only (2233 → 2242 over master 1de68608), so
       the issue's "adds no new hits" box is not met as written; disclosed.
     - "The free abelian group on a point" is never written as ℤ: no
       isomorphism [FreeAb 1 ≅ ℤ] exists in the tree (the inverse would need
       an integer scalar action on [FATerm]), and the file needs only that
       the group has a nonzero element.

   NOT DELIVERED.
     - Mac Lane's own finite-support argument (a normal form for [FATerm]
       is absent); the countable witness reaches his SHAPE by a different
       mechanism, disclosed in (3).
     - Apex-level refutations at the product shapes ([PreservesLimit
       BinDiagram FreeAb → False] would need ℤ ≇ ℤ × ℤ in Ab, the same
       normal form); probe N5 pins the boundary.
     - [FreeAb 1 ≅ ℤ]; countable products in Ab; a repair of [Ab_trivial]'s
       or [_0]'s [Set] pins.
     - "The library's first recorded discontinuity witness" (false; see
       STALE PREMISES).
     - No edit to Instance/Ab.v, Instance/Ab/Free.v, Instance/Zero.v,
       Structure/Limit/Comparison.v or Structure/Limit/Preservation.v. *)

(** ** The point of Sets, and the zero endomorphism of an abelian group *)

Definition SetsPoint : Sets := @terminal_obj Sets Sets_Terminal.

(* Built directly rather than as [Ab_zero_hom A ∘ Ab_one A]: the composite
   would route through [Ab_trivial], whose monomorphic [Set] universes would
   then pin this constant (see the header's UNIVERSES). *)
Definition ab_zero_endo (A : Ab) : A ~{Ab}~> A.
Proof.
  unshelve refine {| cmon_map := {| morphism := fun _ => cmon_zero A |} |}.
  - intros x y _; reflexivity.
  - reflexivity.
  - intros a b; simpl; symmetry; apply cmon_plus_zero_l.
Defined.

Lemma ab_zero_endo_value (A : Ab) (a : carrier (cmon_setoid A)) :
  cmon_map (ab_zero_endo A) a ≈ cmon_zero A.
Proof. simpl; reflexivity. Qed.

(** ** The one separation everything below is spent on *)

(* The free abelian group on a point has two distinct endomorphisms, the
   identity and the zero map, because its generator is not zero
   (Instance/Ab/Free.v's [free_ab_gen_not_zero], read at ℤ).  Every
   refutation in this file is this fact plus bookkeeping. *)
Lemma free_ab_one_id_not_zero :
  @id Ab (FreeAb SetsPoint) ≈ ab_zero_endo (FreeAb SetsPoint) → False.
Proof.
  intro H.
  pose proof (H (fa_gen (X:=SetsPoint) ttt)) as Hg; simpl in Hg.
  exact (free_ab_gen_not_zero (X:=SetsPoint) ab_int 1%Z ab_int_one_not_zero
           ttt Hg).
Qed.

(** ** Witness 1: the empty limit — the free group on a point is not
       terminal in Ab *)

Program Definition empty_cone_at {C : Category} (K : _0 ⟶ C) (c : C)
  : Cone K := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := fun x => match x return _ with end |}
|}.
Next Obligation. destruct x. Qed.

Definition SetsEmptyDiagram : _0 ⟶ Sets := From_0 Sets.

Lemma SetsPoint_empty_IsLimitCone :
  IsLimitCone (empty_cone_at SetsEmptyDiagram SetsPoint).
Proof.
  intro M.
  unshelve eexists.
  - exact (@one Sets Sets_Terminal _).
  - intro x; destruct x.
  - intros v _; apply (@one_unique Sets Sets_Terminal).
Qed.

Definition SetsPoint_empty_Limit : Limit SetsEmptyDiagram :=
  limitcone_limit _ SetsPoint_empty_IsLimitCone.

Theorem FreeAb_not_PreservesLimitCone_empty :
  PreservesLimitCone SetsEmptyDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (P _ SetsPoint_empty_IsLimitCone) as H.
  destruct (H (empty_cone_at _ (FreeAb SetsPoint))) as [u _ Hu].
  apply free_ab_one_id_not_zero.
  transitivity u.
  - symmetry; apply Hu; intro x; destruct x.
  - apply Hu; intro x; destruct x.
Qed.

(* The apex-only form, which the product witnesses below CANNOT reach. *)
Theorem FreeAb_not_PreservesLimit_empty :
  PreservesLimit SetsEmptyDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (@preserves_limit _ _ _ _ _ P SetsPoint_empty_Limit) as H.
  destruct (@ump_limit _ _ _ _ H (empty_cone_at _ (FreeAb SetsPoint)))
    as [u _ Hu].
  apply free_ab_one_id_not_zero.
  transitivity u.
  - symmetry; apply Hu; intro x; destruct x.
  - apply Hu; intro x; destruct x.
Qed.

Definition FreeAb_not_PreservesAllLimits : PreservesAllLimits FreeAb → False :=
  fun H => FreeAb_not_PreservesLimit_empty (H _ SetsEmptyDiagram).

(** ** Witness 2: Mac Lane's countable product *)

Definition NatOnes : nat → Sets := fun _ => SetsPoint.
Definition NatOneDiagram : DiscreteCat nat ⟶ Sets := DiscreteCat_Functor' NatOnes.

Definition NatOneProduct :
  IsIndexedProduct NatOnes SetsPoint (fun _ => @one Sets Sets_Terminal SetsPoint).
Proof.
  constructor; intros c pi.
  exists (@one Sets Sets_Terminal c).
  - intro a; apply (@one_unique Sets Sets_Terminal).
  - intros v _; apply (@one_unique Sets Sets_Terminal).
Defined.

Definition NatOneCone : Cone NatOneDiagram :=
  discrete_cone NatOneDiagram SetsPoint (fun _ => @one Sets Sets_Terminal SetsPoint).

Definition NatOneCone_IsLimitCone : IsLimitCone NatOneCone :=
  discrete_IsLimitCone_of_IsIndexedProduct NatOneDiagram NatOneCone NatOneProduct.

Definition nat_legs (n : nat) : FreeAb SetsPoint ~{Ab}~> FreeAb SetsPoint :=
  match n with
  | O   => id
  | S _ => ab_zero_endo (FreeAb SetsPoint)
  end.

Definition NatCompeting : Cone (FreeAb ◯ NatOneDiagram) :=
  discrete_cone (FreeAb ◯ NatOneDiagram) (FreeAb SetsPoint) nat_legs.

Lemma fmap_one_point :
  fmap[FreeAb] (@one Sets Sets_Terminal SetsPoint) ≈ @id Ab (FreeAb SetsPoint).
Proof.
  rewrite (@one_unique Sets Sets_Terminal SetsPoint _ (@id Sets SetsPoint)).
  exact (@fmap_id Sets Ab FreeAb SetsPoint).
Qed.

Theorem FreeAb_not_PreservesLimitCone_countable_product :
  PreservesLimitCone NatOneDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (P _ NatOneCone_IsLimitCone) as H.
  destruct (H NatCompeting) as [u Hu _].
  apply free_ab_one_id_not_zero.
  assert (Hone : ∀ n : nat, u ≈ nat_legs n).
  { intro n.
    rewrite <- (Hu n).
    change (cone_leg (FCone FreeAb NatOneCone) n)
      with (fmap[FreeAb] (cone_leg NatOneCone n)).
    rewrite fmap_one_point.
    now rewrite id_left. }
  rewrite <- (Hone 0%nat).
  exact (Hone 1%nat).
Qed.

(** ** Witness 3: the binary product, through the comparison map *)

Definition BinOnes : bool → Sets := binary_fam SetsPoint SetsPoint.
Definition BinDiagram : DiscreteCat bool ⟶ Sets := DiscreteCat_Functor' BinOnes.

Definition FreeAb_binary_cmp :
  FreeAb (BinOnes true × BinOnes false)
    ~{Ab}~> FreeAb (BinOnes true) × FreeAb (BinOnes false) :=
  binary_comparison FreeAb BinOnes.

Theorem FreeAb_binary_comparison_not_iso :
  IsIsomorphism FreeAb_binary_cmp → False.
Proof.
  intro Hiso.
  apply free_ab_one_id_not_zero.
  assert (Hsets : @exl Sets _ SetsPoint SetsPoint ≈ @exr Sets _ SetsPoint SetsPoint).
  { transitivity (@one Sets Sets_Terminal (SetsPoint × SetsPoint));
      [ | symmetry ]; apply (@one_unique Sets Sets_Terminal). }
  assert (Hcmp : @exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint) ∘ FreeAb_binary_cmp
                 ≈ @exr Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint) ∘ FreeAb_binary_cmp).
  { unfold FreeAb_binary_cmp.
    rewrite (binary_comparison_exl FreeAb BinOnes).
    rewrite (binary_comparison_exr FreeAb BinOnes).
    now rewrite Hsets. }
  assert (Hlr : @exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint)
                ≈ @exr Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint)).
  { destruct Hiso as [g Hgf Hfg].
    rewrite <- (id_right (@exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint))).
    rewrite <- Hgf, comp_assoc, Hcmp, <- comp_assoc, Hgf.
    now rewrite id_right. }
  rewrite <- (@exl_fork Ab _ _ _ _
                (@id Ab (FreeAb SetsPoint)) (ab_zero_endo (FreeAb SetsPoint))).
  rewrite Hlr.
  apply (@exr_fork Ab _ _ _ _
           (@id Ab (FreeAb SetsPoint)) (ab_zero_endo (FreeAb SetsPoint))).
Qed.

Theorem FreeAb_not_PreservesLimitCone_binary_product :
  PreservesLimitCone BinDiagram FreeAb → False.
Proof.
  intro P.
  apply FreeAb_binary_comparison_not_iso.
  exact (comparison_iso_of_PreservesLimitCone FreeAb P
           (binary_image_cone_IsLimitCone FreeAb BinOnes)
           (binary_cone BinOnes)
           (binary_cone_IsLimitCone BinOnes)).
Qed.

Theorem FreeAb_not_CartesianFunctor :
  @CartesianFunctor Sets Ab FreeAb _ _ → False.
Proof.
  intro HF.
  apply FreeAb_binary_comparison_not_iso.
  exact (fst (cartesian_functor_iff_comparison_iso FreeAb) HF SetsPoint SetsPoint).
Qed.

(** ** The conclusion of the exercise *)

(* The headline goes through Mac Lane's countable product, whose shape
   [DiscreteCat nat] carries free universes; the empty shape [_0] is
   declared at [Category@{u Set Set}] (Instance/Zero.v:28) and pins the
   functor's hom level to [Set] (see the header's UNIVERSES). *)
Definition FreeAb_not_continuous : ContinuousFunctor FreeAb → False :=
  fun H => FreeAb_not_PreservesLimitCone_countable_product (H _ NatOneDiagram).

Definition FreeAb_not_continuous_via_empty :
  ContinuousFunctor FreeAb → False :=
  fun H => FreeAb_not_PreservesLimitCone_empty (H _ SetsEmptyDiagram).

(** ** The positive side of the same adjunction *)

Definition Ab_Forget_Continuous : ContinuousFunctor Ab_Forget :=
  right_adjoint_Continuous free_ab_adjunction.

Definition FreeAb_Cocontinuous : CocontinuousFunctor FreeAb :=
  left_adjoint_Cocontinuous free_ab_adjunction.

(** ** Readbacks *)

Example freeab_is_left_adjoint : FreeAb ⊣ Ab_Forget := free_ab_adjunction.

Example free_ab_one_carrier :
  carrier (Ab_Forget (FreeAb SetsPoint)) = FATerm SetsPoint := eq_refl.

Example bin_diagram_objects : BinOnes true = SetsPoint := eq_refl.
