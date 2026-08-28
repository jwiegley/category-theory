Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.

Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(** * The fibre product of categories, and pullbacks of categories *)

(* nLab:      https://ncatlab.org/nlab/show/pullback
   nLab:      https://ncatlab.org/nlab/show/comma+object
   nLab:      https://ncatlab.org/nlab/show/pseudopullback
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

   Catalogued as Mac Lane, "Categories for the Working Mathematician", 2nd
   ed., section III.5 exercise 3 (book p. 74).  The construction is the
   evident one: given F : A ⟶ C and G : B ⟶ C, take the pairs of objects
   that AGREE under F and G, and the pairs of arrows whose images agree.
   Everything interesting here is about the word "agree", and about which
   category of categories the resulting square is a pullback IN.

   ** Which ambient category

   This library carries two categories of categories, and they answer this
   question differently.  [Cat] (Instance/Cat.v:28-37) has [Functor_Setoid]
   as its hom-setoid, which identifies functors that are merely NATURALLY
   ISOMORPHIC; its own header says so in terms -- it is the homotopy
   category Ho(Cat), "NOT the strict 1-category of categories of the
   textbooks", and an isomorphism in it is an EQUIVALENCE of categories.
   [StrictCat] (Instance/StrictCat.v:56) has [Functor_StrictEq_Setoid],
   under which two functors are identified by a Leibniz equality of their
   object maps together with a transported agreement of their arrow maps.

   The fibre product below is built out of Leibniz equalities [F a = G b],
   so it is a construction about the strict ambient, and that is where its
   universal property is proved:

     [FibreProduct_IsPullback] : ObjUIP C
       → IsPullback (in StrictCat) F G (FibreProduct F G) FP_fst FP_snd

   In [Cat] it is NOT a pullback, and that is measured rather than asserted:
   [FibreProduct_not_Cat_pullback] refutes it at the cospan
   1 --true--> Indiscrete bool <--false-- 1, where a competing square exists
   (an isomorphism true ≅ false supplies the natural isomorphism [Cat]'s
   square condition asks for) while the fibre product has no objects at all
   ([IB_FibreProduct_empty]), so no mediator can exist.  Read that refutation
   narrowly: [point_cospan_Cat_IsPullback] shows the SAME cospan does have a
   pullback in [Cat], namely the terminal category, so what is refuted is
   this candidate apex and not the existence of pullbacks in [Cat].  Whether
   [HasPullbacks Cat] holds is NOT settled here -- it is neither proved nor
   refuted, and no second candidate (the iso-comma, or pseudopullback, which
   is the standard replacement, or any other) was attempted.

   ** What the hypothesis is, where it is spent, and that it is necessary

   The apex's objects are dependent pairs carrying a PROOF of [F a = G b].
   Two mediators into it may therefore differ in that proof alone while
   agreeing in both coordinates, and the uniqueness clause of the pullback
   is exactly the statement that they do not.  So [ObjUIP C] -- uniqueness of
   identity proofs on the objects of the BASE, the honest hypothesis of
   Theory/Category/Monoid.v:546, never an axiom here -- is taken, and it is
   spent by exactly one of the pullback's fields, the uniqueness clause
   [FP_med_unique] -- literally it is destructed inside the helper
   [FP_obj_eq], which has no other consumer, so the two readings agree.
   [FP_commutes_strict], [FP_med], [FP_med_fst] and [FP_med_snd] take no
   hypothesis at all.  It is spent only on C: the
   morphism half of that proof needs the equality's two coordinate
   projections, and [FP_obj_eq] returns them alongside the object equality,
   so no hypothesis on A or on B is required.  [ObjUIP] is free for every
   category with decidable object equality, by Hedberg
   ([ObjUIP_of_ObjDecEq], and [FibreProduct_IsPullback_dec]).

   That hypothesis is NECESSARY, and this is a theorem rather than a remark:
   [FP_uniqueness_forces_UIP] shows that deriving the uniqueness clause
   uniformly -- for every cospan, with no hypothesis on the base -- entails
   UIP for every type.  The countermodel is the cospan 1 --x--> Indiscrete X
   <--x-- 1, where the fibre product's objects ARE the loops at x and each
   loop names a mediator satisfying both triangles.  This is the shape of
   [arrow_mul_respects_forces_UIP] (Theory/Category/Monoid.v) and of
   [Discrete_DiscreteRigid_forces_UIP] (Instance/Discrete/Reconstruct.v).

   Consequently [HasPullbacks StrictCat], which quantifies over EVERY
   cospan, is delivered only from the blanket hypothesis
   [∀ C : Category, ObjUIP C] ([StrictCat_HasPullbacks]).  Read the
   necessity theorem precisely before concluding more: it is about the
   uniqueness clause OF THIS APEX, so it does not refute [HasPullbacks
   StrictCat] with some other apex, and no such refutation is offered.

   ** Comma categories as pullbacks of the arrow-category projections

   Construction/Comma.v:105-108 already records the framing -- comma objects
   are PIE-limits, constructible from pullbacks and the power C^2 -- and that
   framing is consumed rather than restated.  The two one-object instances
   are proved: the slice C/c is the pullback of [Arrow_cod : C^2 ⟶ C] along
   [Diagonal 1 c : 1 ⟶ C] ([Slice_IsPullback]) and the coslice c/C is the
   pullback of [Arrow_dom] along the same ([Coslice_IsPullback]), both in
   [StrictCat] and both under the same [ObjUIP C].  The hypothesis is spent
   for the same reason but NOT, as an earlier draft of this header said, at
   a single point: [slice_arrow_reflect] is where it does work nothing else
   could -- the codomain coordinate of a transported morphism equality is a
   loop at c and must be [eq_refl] (dually [coslice_arrow_reflect] for the
   domain) -- while [Slice_med_arrow] and [Slice_med_unique] spend it again
   through [fp_hom_cast_irr] -- THREE LEMMAS and FOUR USES per side, since
   [Slice_med_arrow] spends it twice (dually [Coslice_med_arrow]).  Contrast
   the fibre product, where the pullback's other three fields really are
   hypothesis-free and only [FP_med_unique] consumes it.
   The apexes here are the tree's OWN [Slice] and [Coslice]
   (Construction/Slice.v), not the fibre product, so these are genuine
   assemblies and not instances of the general theorem.

   PRIOR ART, disclosed rather than left for a reader to find: the tree
   ALREADY has a comma universal property over these same two
   arrow-category projections, and in a module this file Requires --
   [comma_diagram_ump] (Construction/Comma/Diagram.v:484), Mac Lane §II.6
   Exercise 5, whose own header at :38-42 calls it "what exhibits it as a
   'pullback'-style limit" and at :128-136 re-records the same PIE-limit
   framing cited above.  Nothing here is a restatement of it and nothing it
   proves is falsified: it mediates into the GENERAL comma [(S ↓ T)] over
   the [MediatesDiagram] competitor class with uniqueness at [≈[Cat]],
   whereas the two results below are about the two ONE-OBJECT cospans, use
   the pullback's own competitor class, and are stated at [≈[StrictCat]].
   The claim that nothing in the tree states an [IsPullback] or a
   [Pullback] in [Cat] or [StrictCat] is unaffected and stays true.

   ** Strengths, measured strict-first

   Measured to hold at [eq_refl]: the strict square's object component IS
   the equality each object carries and its morphism component IS the
   equation each morphism carries ([FP_commutes_strict] is a [:=] with no
   tactic); both triangles have [eq_refl] object components, and the arrow
   half is [reflexivity] ([FP_med_fst], [FP_med_snd]); the mediator's object
   action is [((q1 x, q2 x); `1 Hsq x)]; and [fobj[FP_fst ◯ FP_med]] and
   [fmap[FP_fst ◯ FP_med] f] are [fobj[q1]] and [fmap[q1] f] at LEIBNIZ
   equality.  On the comma side, [Slice_commutes] and [Coslice_commutes]
   likewise have [eq_refl] object components, and [fobj[Slice_Arrow] x] is
   [((`1 x, c); `2 x)] at Leibniz equality.

   Measured and REFUTED, both conversion failures: [FP_fst ◯ FP_med = q1] as
   a Leibniz equality of [Functor] RECORDS -- the object and arrow actions
   agree on the nose, as just recorded, but the three law fields are rebuilt
   proofs; and [Slice C c = FibreProduct Arrow_cod (Diagonal 1 c)], the two
   being different categories (the slice stores an arrow, the fibre product
   a pair with a proof).  What IS proved is that both are pullbacks of the
   same cospan; the isomorphism between them that follows from essential
   uniqueness is not built.  These are measured here; they are pinned in the
   companion probe.

   ** Universes, read off the constraint blocks

   [FibreProduct] itself is the freer constant: its block carries bounds
   only ([u <= u5], [u0 <= u4], [u2 <= u4] among others) and no identifica-
   tion between A's and B's object universes.  [FibreProduct_IsPullback]
   displays three separate category binders but its constraint block
   contains [u = u1], [u = u3], [u0 = u2] and [u0 = u4]: all three object
   universes are IDENTIFIED with one another, and so are all three
   hom-and-proof universes.  That is what stating an [IsPullback] in
   [StrictCat] costs -- the three corners of the cospan are objects of ONE
   [Category@{o h p}] instance -- and it is inherited rather than introduced
   here; it is not claimed unavoidable, and no rearrangement was attempted.
   [Slice_IsPullback] and [Coslice_IsPullback] are over
   [C : Category@{u u0 u0}] with no [Set] anywhere in their blocks.
   [FP_uniqueness_forces_UIP@{u u0 u1 u2}] has its hypothesis quantified
   over [Category@{u0 Set Set}] -- hom and proof pinned at [Set], which
   WEAKENS the hypothesis and so strengthens the theorem -- with the
   conclusion [∀ X : Type@{u}], [u <= u0]; the pin is the witnesses' doing
   ([Indiscrete] has [hom := unit], and [_1] is instantiated to match).
   [FibreProduct_not_Cat_pullback] carries [Set < u] and [Set < u3], the
   ordinary price of a concrete witness.  Every category binder above
   displays hom and proof at one level; that identification was not probed
   for its cause and no claim is made about it.

   ** Prior art, measured by shape

   Nothing in the tree states an [IsPullback] or a [Pullback] in [Cat] or in
   [StrictCat] (measured: [rg "IsPullback StrictCat|Pullback StrictCat"] and
   the [Cat] analogue return only this file), and no fibre product of
   categories is constructed anywhere -- the two "fibre/fiber product"
   occurrences elsewhere are prose, about schemes (Structure/Pullback.v:113)
   and about base change along a slice (Construction/Slice/Pullback.v:26).
   BEFORE this commit the concrete [HasPullbacks] inhabitants were
   [Sets_HasPullbacks] (Instance/Sets/Pullback.v:393) and [FinSet_Pullbacks]
   (Instance/FinSet/Classifier.v:264), with three generic conditionals
   besides; that roster, and the correction of the older "exactly one
   inhabitant" reading, are Instance/Sets/Pullback.v's own (its header,
   lines 37-46), cited here rather than re-derived.  This commit adds a
   FOURTH conditional, [StrictCat_HasPullbacks] -- not a generic one, being
   for one named category under a blanket hypothesis.

   ** What is NOT delivered

   No [HasPullbacks Cat] and no refutation of it; only this apex is refuted,
   and only at one cospan.  No iso-comma, pseudopullback, bilimit or
   2-categorical universal property, and no comparison between any of those
   and the fibre product.  No unconditional [HasPullbacks StrictCat].  No
   isomorphism between [Slice C c] and the fibre product of its cospan, and
   no essential-uniqueness statement for pullbacks in [StrictCat] at all.
   The GENERAL comma [(S ↓ T)] as the pullback of [⟨dom, cod⟩ : C^2 ⟶ C ∏ C]
   along [S ∏⟶ T] is not built -- only the two one-object cospans.  Nothing
   about pasting, stability, or the interaction with [Cat_Cartesian]; no
   equalizers, no other finite limits, and no completeness statement for
   either category of categories; no connection to the reductions of
   Structure/Pullback/Reduction.v; and nothing is claimed about the arrow
   category as the power [C^2] beyond its use as the source of the two legs.

   108/108 constants (37 transparent, 71 opaque; 46 of them [Program]
   obligations, which the [.glob] sweep does not record and which take the
   62 the glob does count up to the 108 [Print Module] lists) report
   "Closed under the global context". *)

(** ** A small transport kit *)

(* Functors commute with [hom_cast], the endpoints being relabelled by
   [f_equal] of the object map.  Both sides become [fmap[P] f] once the two
   equalities are eliminated. *)
Lemma fmap_hom_cast {X Y : Category} (P : X ⟶ Y) {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) :
  fmap[P] (hom_cast ea eb f)
    ≈ hom_cast (f_equal (fobj[P]) ea) (f_equal (fobj[P]) eb) (fmap[P] f).
Proof. destruct ea, eb; reflexivity. Qed.

(* Reading a [hom_cast] equation as a conjugation, in the orientation the
   natural-isomorphism coherence of [Functor_Setoid] wants. *)
Lemma hom_cast_shift {X : Category} {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) (g : a' ~> b') :
  hom_cast ea eb f ≈ g → f ≈ id_cast (eq_sym eb) ∘ g ∘ id_cast ea.
Proof. destruct ea, eb; simpl; intros Hg; rewrite <- Hg; cat. Qed.

(* Under uniqueness of identity proofs on objects a [hom_cast] does not
   depend on WHICH proofs of its two endpoint equations it is given. *)
Lemma fp_hom_cast_irr {X : Category} (uip : ObjUIP X) {a b a' b' : X}
      (e1 e1' : a = a') (e2 e2' : b = b') (f : a ~> b) :
  hom_cast e1 e2 f = hom_cast e1' e2' f.
Proof. now rewrite (uip _ _ e1 e1'), (uip _ _ e2 e2'). Qed.

(* One [hom_cast] equation, read as a commuting square of [id_cast]s. *)
Lemma cast_of_hom_cast {X : Category} {a a' b b' : X}
      (ea : a = a') (eb : b = b') (g : a ~> b) (h : a' ~> b') :
  hom_cast ea eb g ≈ h → id_cast eb ∘ g ≈ h ∘ id_cast ea.
Proof. destruct ea, eb; simpl; intros Hg; rewrite id_left, id_right; auto. Qed.

(* A [hom_cast] that relabels only the codomain is a postcomposition. *)
Lemma hom_cast_left_refl {X : Category} {a b b' : X} (eb : b = b')
      (g : a ~> b) : hom_cast eq_refl eb g ≈ id_cast eb ∘ g.
Proof. destruct eb; cat. Qed.

(* An equality of comma objects transports the morphism they carry. *)
Lemma comma_obj_eq_inv {A B D : Category} {S : A ⟶ D} {T : B ⟶ D}
      {x y : (S ↓ T)} (E : x = y) :
  hom_cast (f_equal (fun z => fobj[S] (fst ``z)) E)
           (f_equal (fun z => fobj[T] (snd ``z)) E) (`2 x) = `2 y.
Proof. destruct E; reflexivity. Qed.

(* An arrow whose codomain is [d] IS the slice object over [d] it determines;
   this is the object half of the first triangle below.  It is stated at top
   level rather than inside the slice section so that eliminating [eh] does
   not have to generalize the section's own hypotheses. *)
Lemma slice_arrow_eta {D : Category} (d : D) (h : @Arrow D)
      (eh : snd ``h = d) :
  ((fst ``h, d); hom_cast eq_refl eh (`2 h)) = h.
Proof. destruct h as [[a b] g]; simpl in *; destruct eh; reflexivity. Defined.

(* Dually, one that relabels only the domain is a precomposition. *)
Lemma hom_cast_right_refl {X : Category} {a a' b : X} (ea : a = a')
      (g : a ~> b) : hom_cast ea eq_refl g ≈ g ∘ id_cast (eq_sym ea).
Proof. destruct ea; cat. Qed.

(* An arrow whose domain is [d] IS the coslice object under [d] it
   determines. *)
Lemma coslice_arrow_eta {D : Category} (d : D) (h : @Arrow D)
      (eh : fst ``h = d) :
  ((d, snd ``h); hom_cast eh eq_refl (`2 h)) = h.
Proof. destruct h as [[a b] g]; simpl in *; destruct eh; reflexivity. Defined.

(* Turning a [hom_cast] equation around. *)
Lemma hom_cast_flip {X : Category} {a a' b b' : X}
      (ea : a = a') (eb : b = b') (g : a ~> b) (h : a' ~> b') :
  hom_cast ea eb g ≈ h → hom_cast (eq_sym ea) (eq_sym eb) h ≈ g.
Proof. destruct ea, eb; simpl; intros Hg; now symmetry. Qed.

Section FibreProduct.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition FibreProduct : Category := {|
  obj    := ∃ p : A ∏ B, F (fst p) = G (snd p);
  hom    := fun x y =>
    ∃ f : (fst ``x ~{A}~> fst ``y) * (snd ``x ~{B}~> snd ``y),
      hom_cast (`2 x) (`2 y) (fmap[F] (fst f)) ≈ fmap[G] (snd f);
  homset := fun _ _ =>
    {| equiv := fun f g => (fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g) |};
  id      := fun _ => ((id, id); _);
  compose := fun _ _ _ f g => ((fst `1 f ∘ fst `1 g, snd `1 f ∘ snd `1 g); _)
|}.
Next Obligation.
  intros [[]] [[]]; simpl in *; equivalence.
Qed.
Next Obligation.
  intros x; simpl.
  rewrite !fmap_id.
  apply hom_cast_id.
Qed.
Next Obligation.
  intros x y z f g; simpl.
  rewrite !fmap_comp.
  rewrite <- (hom_cast_comp (`2 x) (`2 y) (`2 z)).
  rewrite (`2 f), (`2 g).
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? [e0 e1] ? ? [e2 e3].
  split.
  - now simpl; rewrite e0, e2.
  - now simpl; rewrite e1, e3.
Qed.
Next Obligation. intros; simpl; split; now rewrite id_left. Qed.
Next Obligation. intros; simpl; split; now rewrite id_right. Qed.
Next Obligation. intros; simpl; split; apply comp_assoc. Qed.
Next Obligation. intros; simpl; split; apply comp_assoc_sym. Qed.

Program Instance FP_fst : FibreProduct ⟶ A := {|
  fobj := fun x => fst ``x;
  fmap := fun _ _ f => fst ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance FP_snd : FibreProduct ⟶ B := {|
  fobj := fun x => snd ``x;
  fmap := fun _ _ f => snd ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

(** ** Object equality in the fibre product *)

(* Two objects of the fibre product agreeing in both coordinates are equal --
   PROVIDED the equality proofs they carry can be identified, which is
   exactly [ObjUIP C].  The sigma also returns the two projection equations,
   so that a later [hom_cast] along this equality can be rewritten into the
   coordinate casts without a second appeal to uniqueness of proofs (in
   particular without any hypothesis on A or B). *)
Lemma FP_obj_eq (uip : ObjUIP C) (x y : FibreProduct)
      (e1 : fst ``x = fst ``y) (e2 : snd ``x = snd ``y) :
  { e : x = y & (f_equal (fobj[FP_fst]) e = e1)
              * (f_equal (fobj[FP_snd]) e = e2) }.
Proof.
  destruct x as [[a b] p], y as [[a' b'] p']; simpl in *.
  destruct e1, e2, (uip _ _ p p').
  exists eq_refl; split; reflexivity.
Defined.

(** ** The projection square commutes, in both ambient categories *)

(* Strictly: the object component IS the equality carried by the object, and
   the morphism component IS the equation carried by the morphism. *)
Definition FP_commutes_strict :
  F ∘[StrictCat] FP_fst ≈[StrictCat] G ∘[StrictCat] FP_snd :=
  @Build_strict_eq FibreProduct C (F ◯ FP_fst) (G ◯ FP_snd)
                   (fun x : FibreProduct => `2 x)
                   (fun (x y : FibreProduct) (f : x ~> y) => `2 f).

(* Weakly: the same data read as a natural isomorphism, each component the
   [id_cast] of the object's equality. *)
Program Definition FP_commutes_cat :
  F ∘[Cat] FP_fst ≈[Cat] G ∘[Cat] FP_snd :=
  (fun x => id_cast_iso (`2 x); _).
Next Obligation.
  intros x y f.
  pose proof (`2 f) as Hf; cbv beta in Hf.
  simpl.
  now apply hom_cast_shift.
Qed.

(** ** The mediator, its triangles, and its uniqueness *)

Section Mediator.

Context {Q : Category}.
Context (q1 : Q ⟶ A) (q2 : Q ⟶ B).
Context (Hsq : F ∘[StrictCat] q1 ≈[StrictCat] G ∘[StrictCat] q2).

Program Definition FP_med : Q ⟶ FibreProduct := {|
  fobj := fun x => ((q1 x, q2 x); `1 Hsq x);
  fmap := fun x y f => ((fmap[q1] f, fmap[q2] f); strict_fmap_cast Hsq f)
|}.
Next Obligation. intros x y f g Hfg; split; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

(* Both triangles hold with an [eq_refl] object component: the mediator's
   first coordinate IS [q1] and its second IS [q2], definitionally. *)
Definition FP_med_fst : FP_fst ∘[StrictCat] FP_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q A (FP_fst ◯ FP_med) q1 (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition FP_med_snd : FP_snd ∘[StrictCat] FP_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q B (FP_snd ◯ FP_med) q2 (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(* Uniqueness.  This is the ONLY place a hypothesis is spent, and it is spent
   only on C: the object part needs the two proofs of [F a = G b] carried by
   the competitor and by the mediator to agree, and [FP_obj_eq] hands back
   the projection equations that make the morphism part go through with no
   hypothesis on A or B. *)
Lemma FP_med_unique (uip : ObjUIP C) (v : Q ⟶ FibreProduct)
      (H1 : FP_fst ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : FP_snd ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] FP_med.
Proof.
  refine (@Build_strict_eq Q FibreProduct v FP_med
            (fun x => `1 (FP_obj_eq uip (v x) (FP_med x)
                                    (`1 H1 x) (`1 H2 x))) _).
  intros x y f.
  pose proof (`2 (FP_obj_eq uip (v x) (FP_med x) (`1 H1 x) (`1 H2 x)))
    as [P1x P2x].
  pose proof (`2 (FP_obj_eq uip (v y) (FP_med y) (`1 H1 y) (`1 H2 y)))
    as [P1y P2y].
  split.
  - etransitivity;
      [ exact (fmap_hom_cast FP_fst _ _ (fmap[v] f)) | ].
    rewrite P1x, P1y.
    exact (strict_fmap_cast H1 f).
  - etransitivity;
      [ exact (fmap_hom_cast FP_snd _ _ (fmap[v] f)) | ].
    rewrite P2x, P2y.
    exact (strict_fmap_cast H2 f).
Qed.

End Mediator.

(** ** The strict pullback *)

Definition FibreProduct_IsPullback (uip : ObjUIP C) :
  @IsPullback StrictCat A B C F G FibreProduct FP_fst FP_snd.
Proof.
  unshelve refine {| is_pullback_commutes := FP_commutes_strict |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := FP_med q1 q2 Hsq |}.
  - split; [ exact (FP_med_fst q1 q2 Hsq) | exact (FP_med_snd q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry.
    exact (FP_med_unique q1 q2 Hsq uip v Hv1 Hv2).
Defined.

Definition FibreProduct_Pullback (uip : ObjUIP C) :
  @Pullback StrictCat A B C F G :=
  is_pullback_pullback (FibreProduct_IsPullback uip).

End FibreProduct.

(** ** Packaging: all pullbacks in StrictCat, under a blanket hypothesis *)

(* [ObjUIP] is not an axiom anywhere in this library, and it is free for every
   category whose objects have decidable equality (Hedberg); [obj_uip] of
   Construction/Quotient.v is that argument. *)
Definition ObjUIP_of_ObjDecEq {C : Category} `{@ObjDecEq C} : ObjUIP C :=
  fun x y p q => @obj_uip C _ x y p q.

Definition FibreProduct_IsPullback_dec {A B C : Category}
           (F : A ⟶ C) (G : B ⟶ C) `{@ObjDecEq C} :
  @IsPullback StrictCat A B C F G (FibreProduct F G) (FP_fst F G) (FP_snd F G)
  := FibreProduct_IsPullback F G ObjUIP_of_ObjDecEq.

(* The class [HasPullbacks StrictCat] quantifies over EVERY cospan, so it can
   only be inhabited from a blanket hypothesis.  Nothing weaker will do: the
   converse below shows that the uniqueness clause, taken uniformly, is that
   hypothesis. *)
Definition StrictCat_HasPullbacks (uip : ∀ C : Category, ObjUIP C) :
  HasPullbacks StrictCat.
Proof.
  constructor; intros A B C F G.
  exact (FibreProduct_Pullback F G (uip C)).
Defined.

(** ** The weak ambient: what happens in Ho(Cat) *)

Section CatMeasurement.

(* Any two functors into the terminal category are naturally isomorphic; this
   is [one_unique] at [Cat_Terminal], and it is all the universal property of
   the cospans below needs. *)
Lemma one_functors_equiv {Q : Category} (u v : Q ⟶ _1) : u ≈[Cat] v.
Proof. now apply (@one_unique Cat Cat_Terminal). Qed.

(* A cospan of two points of C, with an isomorphism between them supplying
   the commuting square in Cat. *)
Program Definition point_cospan_square {C : Category} {x y : C} (i : x ≅ y) :
  Diagonal _1 x ∘[Cat] Id[_1] ≈[Cat] Diagonal _1 y ∘[Cat] Id[_1] :=
  (fun _ => i; _).
Next Obligation.
  rewrite id_right.
  symmetry; apply iso_from_to.
Qed.

(* Such a cospan DOES have a pullback in Cat, namely the terminal category:
   every competing square factors through [Erase], uniquely up to natural
   isomorphism, because [Cat(Q, 1)] is a singleton up to [≈]. *)
Definition point_cospan_Cat_IsPullback {C : Category} {x y : C} (i : x ≅ y) :
  @IsPullback Cat _1 _1 C (Diagonal _1 x) (Diagonal _1 y) _1 Id[_1] Id[_1].
Proof.
  unshelve refine {| is_pullback_commutes := point_cospan_square i |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Erase Q |}.
  - split; apply one_functors_equiv.
  - intros v _; apply one_functors_equiv.
Defined.

(* The witness: two objects of a category that are isomorphic without being
   equal.  [Indiscrete bool] has exactly one arrow between any two points, so
   [true ≅ false] there, while [true = false] is empty. *)
Definition IB : Category := Indiscrete bool.

Program Definition IB_iso : @Isomorphism IB true false := {| to := tt;
                                                             from := tt |}.

Definition IBtrue  : _1 ⟶ IB := @Diagonal IB _1 true.
Definition IBfalse : _1 ⟶ IB := @Diagonal IB _1 false.

(* The strict fibre product of that cospan has NO objects at all. *)
Lemma IB_FibreProduct_empty : obj[FibreProduct IBtrue IBfalse] → False.
Proof. intros x; pose proof (`2 x) as Hx; simpl in Hx; discriminate. Qed.

(* Hence the strict fibre product is not a pullback in Cat: the competing
   square built from [IB_iso] has no mediator at all, since a functor out of
   [_1] would name an object of an object-empty category.  Note what this
   does and does not say -- the SAME cospan does have a Cat-pullback, by
   [point_cospan_Cat_IsPullback]; what fails is this candidate apex. *)
Theorem FibreProduct_not_Cat_pullback :
  @IsPullback Cat _1 _1 IB IBtrue IBfalse
              (FibreProduct IBtrue IBfalse)
              (FP_fst IBtrue IBfalse) (FP_snd IBtrue IBfalse) → False.
Proof.
  intros HP.
  destruct (is_pullback_ump HP _1 Id[_1] Id[_1] (point_cospan_square IB_iso))
    as [u _ _].
  exact (IB_FibreProduct_empty (u ttt)).
Qed.

End CatMeasurement.

(** ** Necessity: uniform uniqueness IS the hypothesis *)

Section Necessity.

(* The indiscrete category on X has object type X, so a loop at a point of X
   is literally a loop at an object.  Its homs are [unit], which keeps every
   morphism obligation below trivial. *)
Definition IX (X : Type) : Category := Indiscrete X.

Lemma punit_eq (u : poly_unit) : ttt = u.
Proof. now destruct u. Defined.

Definition IXpt {X : Type} (x : X) : _1 ⟶ IX X := @Diagonal (IX X) _1 x.

(* Each loop [p : x = x] names a functor into the fibre product of the cospan
   1 --x--> IX X <--x-- 1, and every such functor satisfies both triangles. *)
Program Definition loop_functor {X : Type} {x : X} (p : x = x) :
  _1 ⟶ FibreProduct (IXpt x) (IXpt x) := {|
  fobj := fun _ => ((ttt, ttt); p);
  fmap := fun _ _ _ => ((id, id); _)
|}.
Next Obligation.
  intros; simpl.
  match goal with |- ?a = ?b => now destruct a, b end.
Qed.

Lemma loop_functor_fst {X : Type} {x : X} (p : x = x) :
  FP_fst (IXpt x) (IXpt x) ∘[StrictCat] loop_functor p ≈[StrictCat] Id[_1].
Proof.
  refine (@Build_strict_eq _1 _1
            (FP_fst (IXpt x) (IXpt x) ◯ loop_functor p) Id[_1]
            (fun o => punit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma loop_functor_snd {X : Type} {x : X} (p : x = x) :
  FP_snd (IXpt x) (IXpt x) ∘[StrictCat] loop_functor p ≈[StrictCat] Id[_1].
Proof.
  refine (@Build_strict_eq _1 _1
            (FP_snd (IXpt x) (IXpt x) ◯ loop_functor p) Id[_1]
            (fun o => punit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Definition punit_pair_dec (a b : poly_unit * poly_unit) : {a = b} + {a <> b}.
Proof. destruct a as [[] []], b as [[] []]; now left. Defined.

(* Deriving the uniqueness clause of the strict pullback UNIFORMLY -- for
   every cospan, with no hypothesis on the base -- entails UIP for every type.
   So [ObjUIP C] in [FibreProduct_IsPullback] is not an artifact of the proof
   given above; it is what the statement costs.  This is the shape of
   [arrow_mul_respects_forces_UIP] (Theory/Category/Monoid.v) and
   [Discrete_DiscreteRigid_forces_UIP] (Instance/Discrete/Reconstruct.v). *)
Theorem FP_uniqueness_forces_UIP
        (K : ∀ (A B C : Category) (F : A ⟶ C) (G : B ⟶ C),
               @IsPullback StrictCat A B C F G (FibreProduct F G)
                           (FP_fst F G) (FP_snd F G)) :
  ∀ (X : Type) (x y : X) (p q : x = y), p = q.
Proof.
  assert (loops : ∀ (X : Type) (x : X) (p : x = x), p = eq_refl).
  { intros X x p.
    pose proof (is_pullback_ump (K _1 _1 (IX X) (IXpt x) (IXpt x))
                  _1 Id[_1] Id[_1] (reflexivity _)) as U.
    pose proof (uniqueness U (loop_functor p)
                  (loop_functor_fst p, loop_functor_snd p)) as Up.
    pose proof (uniqueness U (loop_functor (@eq_refl _ x))
                  (loop_functor_fst eq_refl, loop_functor_snd eq_refl)) as Ur.
    assert (Hpq : loop_functor p ≈[StrictCat] loop_functor (@eq_refl _ x))
      by (rewrite <- Up; exact Ur).
    exact (inj_pair2_eq_dec _ punit_pair_dec _ _ _ _ (`1 Hpq ttt)). }
  intros X x y p q; destruct p; symmetry; apply loops.
Qed.

End Necessity.


(** ** Comma categories as pullbacks of the arrow-category projections *)

Section SliceAsPullback.

Context {C : Category}.
Context (c : C).
Context (uip : ObjUIP C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

(* [Default Proof Using "All"] reaches the section's [Qed]/[Defined] proofs,
   so those take [uip] positionally even where it does not appear in the
   statement (the Theory/Category/Monoid.v:919 idiom).  It does NOT reach a
   [Program Definition]: [Slice_proj], [Slice_Arrow] and [Slice_med] -- and
   their coslice twins -- are genuinely free of [ObjUIP], as [Check] shows,
   so a consumer reusing them drags in no hypothesis. *)
Local Set Default Proof Using "All".

(* The evident projection [C/c ⟶ C]; used only to read the hom-setoid of the
   slice as a hom-setoid of C, which is what [fmap_hom_cast] needs. *)
Program Definition Slice_proj : Slice C c ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.
Next Obligation. now repeat intro. Qed.
Next Obligation. now intros. Qed.
Next Obligation. now intros. Qed.

(* The first leg: an object of the slice IS an arrow with codomain c. *)
Program Definition Slice_Arrow : Slice C c ⟶ @Arrow C := {|
  fobj := fun x => ((`1 x, c); `2 x);
  fmap := fun _ _ f => ((`1 f, id); _)
|}.
Next Obligation. intros x y f; simpl; rewrite id_left; apply (`2 f). Qed.
Next Obligation. intros x y f g Hfg; split; [ exact Hfg | reflexivity ]. Qed.
Next Obligation. intros x; split; reflexivity. Qed.
Next Obligation.
  intros x y z f g; split; simpl; [ reflexivity | now rewrite id_left ].
Qed.

(* A strict functor equality into the slice is settled by its [Slice_proj]
   reading, the slice hom-setoid being that of C on the underlying arrow. *)
Lemma slice_strict_eq {Q : Category} (u v : Q ⟶ Slice C c)
      (eo : ∀ z, u z = v z)
      (em : ∀ z w (f : z ~> w),
              hom_cast (f_equal (fobj[Slice_proj]) (eo z))
                       (f_equal (fobj[Slice_proj]) (eo w))
                       (fmap[Slice_proj] (fmap[u] f))
                ≈ fmap[Slice_proj] (fmap[v] f)) :
  u ≈[StrictCat] v.
Proof.
  refine (@Build_strict_eq Q (Slice C c) u v eo _).
  intros z w f.
  change (fmap[Slice_proj] (hom_cast (eo z) (eo w) (fmap[u] f))
            ≈ fmap[Slice_proj] (fmap[v] f)).
  etransitivity;
    [ exact (fmap_hom_cast Slice_proj (eo z) (eo w) (fmap[u] f)) | ].
  exact (em z w f).
Qed.

(* [Slice_Arrow] is injective on objects.  This is where [ObjUIP C] does
   work that nothing else could do: the codomain coordinate of the
   transported morphism equality is a loop at c, and it must be [eq_refl].
   It is NOT the only place the hypothesis is consumed on the slice side --
   [Slice_med_arrow] and [Slice_med_unique] each spend it too, through
   [fp_hom_cast_irr] -- and the section's [Default Proof Using "All"] makes
   every [Qed]/[Defined] result here take it positionally in any case; the
   [Program Definition]s it does not reach are listed at the section head. *)
Lemma slice_arrow_reflect (x y : Slice C c)
      (E : Slice_Arrow x = Slice_Arrow y) : x = y.
Proof.
  pose proof (comma_obj_eq_inv E) as HE.
  set (e1 := f_equal (fun z => fobj[Id[C]] (fst ``z)) E) in HE.
  set (e2 := f_equal (fun z => fobj[Id[C]] (snd ``z)) E) in HE.
  clearbody e1 e2; clear E.
  destruct x as [a f], y as [a' g]; simpl in *.
  rewrite (uip _ _ e2 (@eq_refl _ c)) in HE.
  destruct e1, HE; reflexivity.
Qed.

Section SliceMediator.

Context {Q : Category}.
Context (q1 : Q ⟶ @Arrow C) (q2 : Q ⟶ _1).
Context (Hsq : Arrow_cod ∘[StrictCat] q1
                 ≈[StrictCat] Diagonal _1 c ∘[StrictCat] q2).

Program Definition Slice_med : Q ⟶ Slice C c := {|
  fobj := fun z => (fst ``(q1 z); hom_cast eq_refl (`1 Hsq z) (`2 (q1 z)));
  fmap := fun z w f => (fst ``(fmap[q1] f); _)
|}.
Next Obligation.
  intros z w f; simpl.
  rewrite !hom_cast_left_refl.
  rewrite <- comp_assoc.
  transitivity (id_cast (`1 Hsq w)
                  ∘ (fmap[Arrow_cod] (fmap[q1] f) ∘ `2 (q1 z))).
  { apply compose_respects;
      [ reflexivity | exact (Arrow_square _ _ (fmap[q1] f)) ]. }
  rewrite comp_assoc.
  apply compose_respects; [ | reflexivity ].
  etransitivity;
    [ exact (cast_of_hom_cast _ _ _ _ (strict_fmap_cast Hsq f)) | ].
  exact (id_left (id_cast (`1 Hsq z))).
Qed.
Next Obligation.
  intros z w f g Hfg.
  exact (fst (@fmap_respects _ _ q1 z w f g Hfg)).
Qed.
Next Obligation. intros z; exact (fst (@fmap_id _ _ q1 z)). Qed.
Next Obligation.
  intros z w u f g; exact (fst (@fmap_comp _ _ q1 z w u f g)).
Qed.

Lemma Slice_med_arrow :
  Slice_Arrow ∘[StrictCat] Slice_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q (@Arrow C) (Slice_Arrow ◯ Slice_med) q1
            (fun z => slice_arrow_eta c (q1 z) (`1 Hsq z)) _).
  intros z w f; split.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_dom _ _
                 (fmap[Slice_Arrow ◯ Slice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ eq_refl _ eq_refl).
    reflexivity.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_cod _ _
                 (fmap[Slice_Arrow ◯ Slice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ (eq_sym (`1 Hsq z))
                            _ (eq_sym (`1 Hsq w))).
    exact (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f)).
Qed.

Lemma Slice_med_erase :
  Erase (Slice C c) ∘[StrictCat] Slice_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q _1
            (Erase (Slice C c) ◯ Slice_med) q2
            (fun z => punit_eq (q2 z)) _).
  intros z w f; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma Slice_med_unique (v : Q ⟶ Slice C c)
      (H1 : Slice_Arrow ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : Erase (Slice C c) ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] Slice_med.
Proof.
  refine (slice_strict_eq v Slice_med
            (fun z => slice_arrow_reflect (v z) (Slice_med z)
                        (eq_trans (`1 H1 z) (eq_sym (`1 Slice_med_arrow z))))
            _).
  intros z w f.
  rewrite (fp_hom_cast_irr uip _ (f_equal (fobj[Arrow_dom]) (`1 H1 z))
                          _ (f_equal (fobj[Arrow_dom]) (`1 H1 w))).
  transitivity (fmap[Arrow_dom]
                  (hom_cast (`1 H1 z) (`1 H1 w) (fmap[Slice_Arrow ◯ v] f))).
  { symmetry;
      exact (fmap_hom_cast Arrow_dom _ _ (fmap[Slice_Arrow ◯ v] f)). }
  exact (fst (strict_fmap_cast H1 f)).
Qed.

End SliceMediator.

Definition Slice_commutes :
  Arrow_cod ∘[StrictCat] Slice_Arrow
    ≈[StrictCat] Diagonal _1 c ∘[StrictCat] Erase (Slice C c).
Proof.
  refine (@Build_strict_eq (Slice C c) C
            (Arrow_cod ◯ Slice_Arrow) (Diagonal _1 c ◯ Erase (Slice C c))
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition Slice_IsPullback :
  @IsPullback StrictCat (@Arrow C) _1 C Arrow_cod (Diagonal _1 c)
              (Slice C c) Slice_Arrow (Erase (Slice C c)).
Proof.
  unshelve refine {| is_pullback_commutes := Slice_commutes |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Slice_med q1 q2 Hsq |}.
  - split; [ exact (Slice_med_arrow q1 q2 Hsq)
           | exact (Slice_med_erase q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry; exact (Slice_med_unique q1 q2 Hsq v Hv1 Hv2).
Defined.

End SliceAsPullback.

Section CosliceAsPullback.

Context {C : Category}.
Context (c : C).
Context (uip : ObjUIP C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.
Local Set Default Proof Using "All".

Program Definition Coslice_proj : Coslice C c ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.
Next Obligation. now repeat intro. Qed.
Next Obligation. now intros. Qed.
Next Obligation. now intros. Qed.

(* The first leg: an object of the coslice IS an arrow with domain c. *)
Program Definition Coslice_Arrow : Coslice C c ⟶ @Arrow C := {|
  fobj := fun x => ((c, `1 x); `2 x);
  fmap := fun _ _ f => ((id, `1 f); _)
|}.
Next Obligation. intros x y f; simpl; rewrite id_right; apply (`2 f). Qed.
Next Obligation. intros x y f g Hfg; split; [ reflexivity | exact Hfg ]. Qed.
Next Obligation. intros x; split; reflexivity. Qed.
Next Obligation.
  intros x y z f g; split; simpl; [ now rewrite id_left | reflexivity ].
Qed.

Lemma coslice_strict_eq {Q : Category} (u v : Q ⟶ Coslice C c)
      (eo : ∀ z, u z = v z)
      (em : ∀ z w (f : z ~> w),
              hom_cast (f_equal (fobj[Coslice_proj]) (eo z))
                       (f_equal (fobj[Coslice_proj]) (eo w))
                       (fmap[Coslice_proj] (fmap[u] f))
                ≈ fmap[Coslice_proj] (fmap[v] f)) :
  u ≈[StrictCat] v.
Proof.
  refine (@Build_strict_eq Q (Coslice C c) u v eo _).
  intros z w f.
  change (fmap[Coslice_proj] (hom_cast (eo z) (eo w) (fmap[u] f))
            ≈ fmap[Coslice_proj] (fmap[v] f)).
  etransitivity;
    [ exact (fmap_hom_cast Coslice_proj (eo z) (eo w) (fmap[u] f)) | ].
  exact (em z w f).
Qed.

Lemma coslice_arrow_reflect (x y : Coslice C c)
      (E : Coslice_Arrow x = Coslice_Arrow y) : x = y.
Proof.
  pose proof (comma_obj_eq_inv E) as HE.
  set (e1 := f_equal (fun z => fobj[Id[C]] (fst ``z)) E) in HE.
  set (e2 := f_equal (fun z => fobj[Id[C]] (snd ``z)) E) in HE.
  clearbody e1 e2; clear E.
  destruct x as [a f], y as [a' g]; simpl in *.
  rewrite (uip _ _ e1 (@eq_refl _ c)) in HE.
  destruct e2, HE; reflexivity.
Qed.

Section CosliceMediator.

Context {Q : Category}.
Context (q1 : Q ⟶ @Arrow C) (q2 : Q ⟶ _1).
Context (Hsq : Arrow_dom ∘[StrictCat] q1
                 ≈[StrictCat] Diagonal _1 c ∘[StrictCat] q2).

Program Definition Coslice_med : Q ⟶ Coslice C c := {|
  fobj := fun z => (snd ``(q1 z); hom_cast (`1 Hsq z) eq_refl (`2 (q1 z)));
  fmap := fun z w f => (snd ``(fmap[q1] f); _)
|}.
Next Obligation.
  intros z w f; cbv beta.
  transitivity (`2 (q1 w) ∘ id_cast (eq_sym (`1 Hsq w))).
  { exact (hom_cast_right_refl _ _). }
  transitivity (snd ``(fmap[q1] f)
                  ∘ (`2 (q1 z) ∘ id_cast (eq_sym (`1 Hsq z)))).
  2: { apply compose_respects;
         [ reflexivity | symmetry; exact (hom_cast_right_refl _ _) ]. }
  rewrite comp_assoc.
  transitivity ((`2 (q1 w) ∘ fmap[Arrow_dom] (fmap[q1] f))
                  ∘ id_cast (eq_sym (`1 Hsq z))).
  2: { apply compose_respects;
         [ exact (Arrow_square _ _ (fmap[q1] f)) | reflexivity ]. }
  rewrite <- comp_assoc.
  apply compose_respects; [ reflexivity | ].
  etransitivity;
    [ symmetry; exact (id_right (id_cast (eq_sym (`1 Hsq w)))) | ].
  exact (cast_of_hom_cast _ _ _ _
           (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f))).
Qed.
Next Obligation.
  intros z w f g Hfg.
  exact (snd (@fmap_respects _ _ q1 z w f g Hfg)).
Qed.
Next Obligation. intros z; exact (snd (@fmap_id _ _ q1 z)). Qed.
Next Obligation.
  intros z w u f g; exact (snd (@fmap_comp _ _ q1 z w u f g)).
Qed.

Lemma Coslice_med_arrow :
  Coslice_Arrow ∘[StrictCat] Coslice_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q (@Arrow C) (Coslice_Arrow ◯ Coslice_med) q1
            (fun z => coslice_arrow_eta c (q1 z) (`1 Hsq z)) _).
  intros z w f; split.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_dom _ _
                 (fmap[Coslice_Arrow ◯ Coslice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ (eq_sym (`1 Hsq z))
                            _ (eq_sym (`1 Hsq w))).
    exact (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f)).
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_cod _ _
                 (fmap[Coslice_Arrow ◯ Coslice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ eq_refl _ eq_refl).
    reflexivity.
Qed.

Lemma Coslice_med_erase :
  Erase (Coslice C c) ∘[StrictCat] Coslice_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q _1
            (Erase (Coslice C c) ◯ Coslice_med) q2
            (fun z => punit_eq (q2 z)) _).
  intros z w f; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma Coslice_med_unique (v : Q ⟶ Coslice C c)
      (H1 : Coslice_Arrow ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : Erase (Coslice C c) ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] Coslice_med.
Proof.
  refine (coslice_strict_eq v Coslice_med
            (fun z => coslice_arrow_reflect (v z) (Coslice_med z)
                        (eq_trans (`1 H1 z)
                                  (eq_sym (`1 Coslice_med_arrow z)))) _).
  intros z w f.
  rewrite (fp_hom_cast_irr uip _ (f_equal (fobj[Arrow_cod]) (`1 H1 z))
                          _ (f_equal (fobj[Arrow_cod]) (`1 H1 w))).
  transitivity (fmap[Arrow_cod]
                  (hom_cast (`1 H1 z) (`1 H1 w) (fmap[Coslice_Arrow ◯ v] f))).
  { symmetry;
      exact (fmap_hom_cast Arrow_cod _ _ (fmap[Coslice_Arrow ◯ v] f)). }
  exact (snd (strict_fmap_cast H1 f)).
Qed.

End CosliceMediator.

Definition Coslice_commutes :
  Arrow_dom ∘[StrictCat] Coslice_Arrow
    ≈[StrictCat] Diagonal _1 c ∘[StrictCat] Erase (Coslice C c).
Proof.
  refine (@Build_strict_eq (Coslice C c) C
            (Arrow_dom ◯ Coslice_Arrow)
            (Diagonal _1 c ◯ Erase (Coslice C c))
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition Coslice_IsPullback :
  @IsPullback StrictCat (@Arrow C) _1 C Arrow_dom (Diagonal _1 c)
              (Coslice C c) Coslice_Arrow (Erase (Coslice C c)).
Proof.
  unshelve refine {| is_pullback_commutes := Coslice_commutes |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Coslice_med q1 q2 Hsq |}.
  - split; [ exact (Coslice_med_arrow q1 q2 Hsq)
           | exact (Coslice_med_erase q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry; exact (Coslice_med_unique q1 q2 Hsq v Hv1 Hv2).
Defined.

End CosliceAsPullback.
