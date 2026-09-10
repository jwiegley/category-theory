Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.BiCCC.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Product.Fixed.
Require Import Category.Adjunction.Continuity.Finite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.

Generalizable All Variables.

(** * Non-existence of adjoints in Sets and Sets^op *)

(* Mac Lane §V.5 Exercises 1 and 4 (book p. 120; maclane:V.5:ex1,
   maclane:V.5:ex4); Awodey §9.6's remark that limit preservation is a
   test for the non-existence of adjoints (awodey:9.6:remark-adjoint-
   existence-tests).
   nLab: https://ncatlab.org/nlab/show/continuous+functor
         https://ncatlab.org/nlab/show/complete+category

   BACKGROUND.  Right adjoints preserve limits, so a functor that does not
   preserve some limit has no left adjoint; the two exercises are the two
   classical instances in Sets.  Exercise 1: [X × − : Sets ⟶ Sets] has a
   left adjoint only when [X] is a point, since a right adjoint preserves
   the terminal object and [X × 1 ≅ X].  Exercise 4: [Sets^op] is not
   cartesian closed, since in a cartesian closed category with an initial
   object [x × 0 ≅ 0], and read in Sets that says [x + 1 ≅ 1].

   STALE PREMISES, RE-MEASURED.
     - "The library records only positive adjunction constructions … no
       impossibility result … no idiom for stating that a given functor
       lacks an adjoint": FALSE.  Seven no-adjoint theorems in three
       spellings predate this file: Instance/Top/Image.v:232
       [nat_inf_no_left_adjoint], Instance/Monoid/Translation.v:694
       [nat_translation_no_right_adjoint] and Adjunction/Choice.v:818
       [two_const_Y_no_right_adjoint] (quantified over the candidate);
       Instance/Powerset/Quantifier.v:1422 [exists_not_right_adjoint] and
       :1471 [forall_not_left_adjoint] ([(∃ L, L ⊣ G) → False]);
       Adjunction/Diagonal/Connected.v:764 [eval_not_left_adjoint] (at a
       named pair); Instance/Top/Forgetful.v:541 [indiscrete_no_right_
       adjoint] (hypothesis-shaped).  The issue's own grep is off too:
       'no left adjoint|no right adjoint' has 15 hits, not one, and [⊣]
       786 hits in 177 files, not 261.
     - "'not cartesian closed' finds only prose": FALSE.  Instance/Fun/
       Closed.v:573 [fun_not_cartesian_closed (CC : @Cartesian ([Omega,
       FinSet])) : @Closed _ CC → False] is a theorem, in the strong form
       quantified over every cartesian structure; Exercise 4 below is the
       SECOND non-cartesian-closedness result and the first for [Sets^op],
       at that strength.  (Instance/Coq/Par.v:219 and ParE.v:177 are prose,
       as the issue says.)
     - "The general tool (Adjunction/Continuity.v:202, :223) is never used
       in the negative direction": TRUE, and the constants sit at :205
       ([right_adjoint_PreservesLimitCone]) and :233 ([left_adjoint_
       preserves_colimit]) — :202 and :223 are comment lines.  RAPL/LAPC
       have eleven consumers in the tree, every one positive; this file
       is the FIRST negative use of them.  (The Awodey clause's "no
       category of posets" is stale too: Instance/Pos.v.)
     - Structure/BiCCC.v's [prod_zero_r] is declared at :221 (statement
       :222) and needs [Cartesian], [Closed] and [Initial] only — not the
       [Cocartesian] its section also opens — so no dual cocartesian
       structure of [Sets^op] is needed.

   WHAT IS DELIVERED (15 named constants plus the 4 [Program] obligations
   of [fp_adj_iso], every one closed under the global context; the four
   reusable corollaries live in Adjunction/Continuity/Finite.v).
     (1) EXERCISE 1, IN ANY CARTESIAN CATEGORY WITH A TERMINAL OBJECT.
         Forward: [fixed_product_left_adjoint_terminal (X) (L) (A : L ⊣
         fixed_product_functor X) : X ≅ 1] — Adjunction/Continuity/Finite.v's
         [right_adjoint_preserves_terminal] gives [fobj_one_iso : 1 ≅ X ×
         1], and Structure/Cartesian.v:465's [prod_one_r] closes; a
         GENUINE consequence of limit preservation, as the reviewer asks.
         Converse: [Id_adj_fixed_product (X) (HX : X ≅ 1) : Id ⊣ fixed_
         product_functor X], built directly from the hom-set bijection
         [fp_adj_iso] (pair with the unique arrow [to_X] to [X]; project
         back) through [Build_Adjunction']; [to_X_unique] is its one
         lemma.  No adjunction is transported along [X × − ≈ Id]: the
         converse is a construction (probe N1 refuses [fixed_product_
         functor 1 = Id] at [eq_refl]).  Packaged as the exact
         characterisation [fixed_product_left_adjoint_iff_terminal] and,
         at Sets, the issue's [times_X_has_left_adjoint_iff_terminal] — both
         directions, [∃] being [sigT] so the converse hands over the
         adjoint.  The functor is Functor/Product/Fixed.v:200's
         [fixed_product_functor X] ([X × −], [second] on arrows);
         Structure/Cartesian/Closed/Adjunction.v:177's [Prod_Functor] is
         the same functor on the other side ([− × S], with its right
         adjoint [Curry_Adjunction] :225), and its consolidation with
         Fixed.v's [fixed_product_functor_right] is surfaced, not done.
     (2) EXERCISE 4, IN THE STRONG FORM.  [Sets_op_not_cartesian_closed
         (CC : @Cartesian (Sets^op)) (CL : @Closed (Sets^op) CC) : False] —
         quantified over EVERY cartesian structure on [Sets^op], the
         strength of Instance/Fun/Closed.v:573.  The scaffolding is
         conversion ([Sets_op_Initial := Sets_Terminal];
         [Sets_op_Cartesian_is_coproducts : @Cartesian (Sets^op) =
         @Cocartesian Sets] at [eq_refl], Structure/Cocartesian.v:115-118's
         notation); the argument: [prod_zero_r] at the point gives [1 ×[CC]
         0 ≅ 0] in [Sets^op], so the apex is subterminal in Sets and the
         two projections [exl], [exr] agree as morphisms; copairing the
         two injections [pt_inl], [pt_inr] of [OnePlusOne := 1 + 1] through
         it forces [pt_inl ≈ pt_inr], and across summands the coproduct's
         [≈] IS [False] ([pt_inl_inr_apart], [eq_refl];
         Instance/Sets/Cocartesian.v).  The two-point set is [1 + 1] and
         not the [bool]-carried [bool_setoid_object]: the latter pins the
         object level to [Set] and would state the theorem for small
         setoids only (measured on a discarded draft).
     (3) THE REUSABLE OBSTRUCTION LEMMAS (Awodey's checkbox), in
         Adjunction/Continuity/Finite.v: [right_adjoint_preserves_terminal],
         [right_adjoint_preserves_binary_products],
         [left_adjoint_preserves_initial],
         [left_adjoint_preserves_binary_coproducts] — two-line compositions
         of Adjunction/Continuity.v's RAPL with Structure/Limit/
         Comparison.v's bridges (:807, :715), the last two through
         [Opposite_Adjunction].  They live in a satellite of Continuity.v
         because Comparison.v already requires Continuity.v (placing them
         in Continuity.v would cycle) and because their statements are
         generic, not about Sets.

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 15
   constants and the four corollaries).  No constant of this file carries
   a universe equation, none names [Set]:
   [Sets_op_not_cartesian_closed@{u u0} : ∀ CC : Cartesian@{u u0},
   Closed@{u u0 u} → False] with [u0 < u] only, and
   [times_X_has_left_adjoint_iff_terminal@{u u0 u1 u2}] over [Sets@{u2 u1}]
   with [u2 < u1] only.  The four corollaries carry [u0 = u2], the hom
   levels of the two categories identified — [Adjunction]'s own block
   ([Build_Adjunction'] has [h1 = h2]; [right_adjoint_PreservesLimitCone]
   carries the same equation), not this development's; probe N4 pins the
   underlying constraint (a functor may not go down the hom levels,
   Theory/Functor.v's [h1 <= h2]).  Stdlib caps, each attributed by
   [About] on the donor: [DiscreteCat_Functor'] (Comparison.v:535) carries
   [EqdepFacts], [JMeq], [eq_ind], [eq_ind_r], [eq_rect_r] and
   [Logic_lemmas.equality], and hands them to the four corollaries and so
   to [fixed_product_left_adjoint_terminal] and both iffs;
   [Build_Adjunction'] carries [Logic_lemmas.equality] and [prod_rect],
   inherited by [Id_adj_fixed_product]; [Sets_Terminal] carries
   [Logic_lemmas.equality], [eq_ind], [eq_ind_r], inherited by [OnePt],
   [OnePlusOne], [pt_inl], [pt_inr], [Sets_op_Initial] and
   [pt_inl_inr_apart]; [prod_zero_r] carries [prod_rect], inherited by
   [Sets_op_not_cartesian_closed].  [fixed_product_functor], [prod_one_r],
   [fobj_one_iso], [nullary_fam], [Sets_Cartesian] and [Sets_Cocartesian]
   carry none.

   COUNTS AND CONVENTIONS.
     - 15 [.glob] declaration heads here (11 [def], 4 [prf]) plus the 4
       [Program] obligations of [fp_adj_iso] (two discharged by
       [cat_simpl], two by hand), and 4 heads in Finite.v — all "Closed
       under the global context", zero [Axioms:] lines; the gate carries
       the 19 heads, fully qualified, the issue's
       [times_X_has_left_adjoint_iff_terminal] and
       [Sets_op_not_cartesian_closed] among them.
     - One [Defined], [Id_adj_fixed_product], LOAD-BEARING: flipped to
       [Qed] in a copy of the file, the probe's readback of its transpose
       ([to (adj …) f = to_X x △ f] at [eq_refl]) stops.  Six [Qed] (two
       theorems, [to_X_unique], the two hand-written obligations, the
       iff).  Finite.v has neither: its four constants are [:=] terms.
     - Closure 68 files excluding self: Functor/Product/Fixed.v costs 23 at
       the margin (it requires Instance/Grp.v — the price of reusing the
       tree's [X × −] rather than redefining it), Adjunction/Continuity/
       Finite.v 17, Structure/BiCCC.v 2, Instance/Sets/Cocartesian.v 1,
       the other fourteen [Require]s 0; Finite.v's own closure is 39
       (Structure/Limit/Comparison.v 12 at the margin).  Name collisions:
       none — each of the 19 names has 0 word occurrences elsewhere in the
       tree ([TwoPt] was renamed to [OnePlusOne] away from
       Instance/Top/Wedge.v's).
     - Test/ProbeNoAdjoint432.v mirrors the [Require] list and carries 5
       refutation commands (1 instrument + N1 CONVERSION + N2-N3 TYPING +
       N4 UNIVERSE), each stripped one at a time in a copy of the whole
       file beside its accepted controls (N4's message: "Cannot enforce ch
       = _ because ch < dh <= _"); four [eq_refl] readbacks; guard
       coverage 20 identifier tokens inside the refutations / 17 also
       named outside, comments stripped, with three exhaustive exceptions
       (the keyword, the refuted declaration's name, the absent name);
       rename-simulated over the ten library names the refutations use
       ([fixed_product_functor], [Id_adj_fixed_product],
       [Sets_op_not_cartesian_closed], [Closed], [Cartesian], [Sets],
       [Category], [iso_id], [Id], [eq_refl]; section binders excluded),
       every first break on a positive line.  [make todo] grows by those 5
       lines only (2246 → 2251 over master b72e7182), so the issue's "adds
       no new hits" box is not met as written; disclosed.

   NOT DELIVERED.
     - Awodey's concrete instances (the forgetful functor from posets, the
       free monoid): not built here.
     - A right-hand adjunction transport ([G ≈ G' → F ⊣ G → F ⊣ G']): not
       needed, the converse being a construction.
     - Any positive closedness statement about [Sets^op]; the
       [bool]-carried form of Exercise 4 (pinned at [Set], discarded).
     - The consolidation of [Prod_Functor] with [fixed_product_functor_
       right] (surfaced above).
     - No edit to Adjunction/Continuity.v, Structure/Limit/Comparison.v,
       Functor/Product/Fixed.v, Structure/BiCCC.v or Instance/Sets/*.v. *)

(** ** Mac Lane V.5 Exercise 1, in any cartesian category with a terminal
       object *)

Section FixedProductAdjoint.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.

(* Forward: a left adjoint to [X × −] makes [X × −] a right adjoint, so it
   preserves the terminal object, [1 ≅ X × 1]; with [X × 1 ≅ X] this is
   [X ≅ 1]. *)
Theorem fixed_product_left_adjoint_terminal
  (X : C) (L : C ⟶ C) (A : L ⊣ fixed_product_functor X) : X ≅ 1.
Proof.
  pose proof (@right_adjoint_preserves_terminal C C L
                (fixed_product_functor X) A T T) as HT.
  pose proof (@fobj_one_iso C C (fixed_product_functor X) T T HT) as Hi.
  simpl in Hi.
  transitivity (X × 1); [ symmetry; exact (@prod_one_r C CC T X) |].
  symmetry; exact Hi.
Qed.

Section Converse.

Context (X : C).
Context (HX : X ≅ 1).

(* Every object has exactly one arrow into an [X ≅ 1]. *)
Definition to_X (x : C) : x ~> X := from HX ∘ one.

Lemma to_X_unique {x : C} (f : x ~> X) : f ≈ to_X x.
Proof.
  unfold to_X.
  rewrite <- (id_left f), <- (iso_from_to HX), <- comp_assoc.
  apply compose_respects; [reflexivity |]; apply one_unique.
Qed.

(* The hom-set bijection [C(x, y) ≅ C(x, X × y)]: pair with the unique
   arrow to [X], and project back. *)
Program Definition fp_adj_iso (x y : C) :
  @Isomorphism Sets
    {| carrier := @hom C (Id x) y; is_setoid := @homset C (Id x) y |}
    {| carrier := @hom C x (fixed_product_functor X y)
     ; is_setoid := @homset C x (fixed_product_functor X y) |} := {|
  to   := {| morphism := fun f => to_X x △ f |};
  from := {| morphism := fun g => exr ∘ g |}
|}.
Next Obligation. proper; now apply fork_respects. Qed.
Next Obligation.
  symmetry; apply (snd (ump_products _ _ _)); split;
    [ apply to_X_unique | reflexivity ].
Qed.

(* Converse: when [X ≅ 1], the identity is a left adjoint of [X × −].  Built
   directly (no adjunction is transported along [X × − ≈ Id]). *)
Definition Id_adj_fixed_product : Id ⊣ fixed_product_functor X.
Proof using C CC HX T X.
  unshelve eapply (@Build_Adjunction' C C Id (fixed_product_functor X)
                     fp_adj_iso).
  - intros x y z f g; simpl.
    rewrite <- fork_comp.
    apply fork_respects; [| reflexivity].
    symmetry; apply to_X_unique.
  - intros x y z f g; simpl.
    symmetry; apply second_fork.
Defined.

End Converse.

(* The exact characterisation: [X × −] has a left adjoint iff [X] is
   terminal ([∃] is [sigT], so the converse hands over the adjoint). *)
Theorem fixed_product_left_adjoint_iff_terminal (X : C) :
  (∀ L : C ⟶ C, L ⊣ fixed_product_functor X → X ≅ 1)
  ∧ (X ≅ 1 → ∃ L : C ⟶ C, L ⊣ fixed_product_functor X).
Proof.
  split.
  - intros L A; exact (fixed_product_left_adjoint_terminal X L A).
  - intro HX; exists Id; exact (Id_adj_fixed_product X HX).
Qed.

End FixedProductAdjoint.

(** The exercise as stated, at Sets. *)
Definition times_X_has_left_adjoint_iff_terminal (X : Sets) :
  (∀ L : Sets ⟶ Sets, L ⊣ fixed_product_functor X → X ≅ 1)
  ∧ (X ≅ 1 → ∃ L : Sets ⟶ Sets, L ⊣ fixed_product_functor X) :=
  fixed_product_left_adjoint_iff_terminal X.

(** ** Mac Lane V.5 Exercise 4: [Sets^op] is not cartesian closed *)

(* The duality scaffolding is conversion: [@Cocartesian Sets] IS
   [@Cartesian (Sets^op)] (Structure/Cocartesian.v:115-118), and the
   terminal object of Sets is the initial object of [Sets^op]. *)
Definition Sets_op_Initial : @Initial (Sets^op) := Sets_Terminal.

Example Sets_op_Cartesian_is_coproducts :
  @Cartesian (Sets^op) = @Cocartesian Sets := eq_refl.

(* The point, and the two-point set [1 + 1] with its injections — kept
   polymorphic (a [bool]-carried two-point set would pin the object level
   to [Set]). *)
Definition OnePt : Sets := @terminal_obj Sets Sets_Terminal.

Definition OnePlusOne : Sets :=
  @product_obj (Sets^op) Sets_Cocartesian OnePt OnePt.

Definition pt_inl : OnePt ~{Sets}~> OnePlusOne :=
  @exl (Sets^op) Sets_Cocartesian OnePt OnePt.

Definition pt_inr : OnePt ~{Sets}~> OnePlusOne :=
  @exr (Sets^op) Sets_Cocartesian OnePt OnePt.

(* The two injections differ: across summands the coproduct's [≈] IS
   [False] (Instance/Sets/Cocartesian.v). *)
Example pt_inl_inr_apart :
  (pt_inl ttt ≈ pt_inr ttt) = False := eq_refl.

(* If [Sets^op] were cartesian closed for ANY cartesian structure [CC],
   [prod_zero_r] would give [1 ×[CC] 0 ≅ 0] in [Sets^op] — in [Sets], a
   subterminal apex under both injections of [1 + 1] — forcing the two
   injections to agree. *)
Theorem Sets_op_not_cartesian_closed
  (CC : @Cartesian (Sets^op)) (CL : @Closed (Sets^op) CC) : False.
Proof.
  pose (Z := @initial_obj (Sets^op) Sets_op_Initial).
  pose proof (@prod_zero_r (Sets^op) CC CL Sets_op_Initial OnePt) as Hi.
  assert (Hsub : ∀ p q : carrier (@product_obj (Sets^op) CC OnePt Z), p ≈ q).
  { intros p q.
    pose proof (iso_from_to Hi p) as Hp.
    pose proof (iso_from_to Hi q) as Hq.
    assert (Hu : ∀ u v : carrier OnePt, to Hi u ≈ to Hi v)
      by (intros [] []; reflexivity).
    exact (transitivity (symmetry Hp) (transitivity (Hu _ _) Hq)). }
  assert (Hi12 : @exl (Sets^op) CC OnePt Z ≈ @exr (Sets^op) CC OnePt Z)
    by (intro u; apply Hsub).
  assert (Hbad : pt_inl ≈ pt_inr).
  { rewrite <- (@exl_fork (Sets^op) CC OnePlusOne OnePt Z pt_inl pt_inr) at 1.
    rewrite <- (@exr_fork (Sets^op) CC OnePlusOne OnePt Z pt_inl pt_inr) at 2.
    now rewrite Hi12. }
  exact (Hbad ttt).
Qed.
