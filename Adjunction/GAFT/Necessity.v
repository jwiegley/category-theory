Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Size.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Representability.Sets.

Generalizable All Variables.

(** * The solution set condition cannot be dropped *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, §V.6, book pp. 122-123 (the remarks after
         Theorems 2 and 3).  Catalog ids [maclane:V.6:remark-ord-
         counterexample], [maclane:V.6:remark-comp-bool].
   Book: Awodey, "Category Theory", 2nd ed., §9.8, Remark 9.30, printed
         pp. 253-254.  Catalog id [awodey:9.8:remark30].
   nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Complete_Boolean_algebra

   ** READ THIS BEFORE READING ANYTHING ELSE

   NO COUNTEREXAMPLE CATEGORY IS BUILT HERE.  Mac Lane's §V.6 witness is
   the ordered class of small ordinals; this file does not construct it,
   and it constructs no other category either.  The two sharpness
   theorems below are CONDITIONAL: each takes a category with no initial
   object as a hypothesis and is inert until someone supplies one.  What
   is unconditional is everything else -- the continuity of the constant
   functor, the representable/initial biconditional, and the measurement
   in item 8 below, which is the reason the issue's plan cannot be
   carried out as its text describes.

   ** THE ISSUE'S SURVEY, RE-MEASURED

   Issue #444's "Current state in the library" and its Awodey §9.8
   section are off in eight places, each re-measured on 2026-09-13
   against a green build of master 050345f0.  Where only the EVIDENCE is
   wrong and the substance survives, that is said too.

   1. "The library has no ordinals as a category (`rg -w 'Ord|OrdCat'` →
      a lone prose cross-reference in Instance/Proset.v)".  The grep
      is wrong: `grep -rnw --include='*.v' -E 'Ord|OrdCat' .` returns 73
      lines over 8 files.  [Ord] IS a category in tree -- Instance/Ord.v,
      the category of ALL PREORDERS (Mac Lane's Preord, landed by #372),
      with [Ord_Forget], [Pos_Sub] and the Instance/Ord/Poset.v
      reflection -- and Instance/Ordinal.v builds [Ordinal n], every
      finite ordinal AS a thin category, with [Ord_Incl] and [Ord_Omega]
      relating them to Instance/Omega.v's ω.  What survives is the
      claim the issue needed: no category whose OBJECTS are the small
      ordinals (`grep -rin --include='*.v' -E 'category of (all )?(small
      )?ordinals|ordinals as a category|class of small ordinals' .` → 0).

   2. "no smallness/largeness machinery": FALSE.  Theory/Size.v declares
      [LocallySmall] and [Small], with
      [locally_small_ambient], [small_locally_small] and
      the witness [One_Small].  Both predicates are USED below --
      [Small] indexes the shapes of [SmallShapeComplete], and
      [LocallySmall] is the free extra hypothesis the sharpness clause
      carries.

   3. "it records no example of a continuous functor without a left
      adjoint (`rg -i 'counterexample|no left adjoint'` → nothing of this
      kind)".  That grep returns 60 lines over 42 files.  The substance
      survives with one correction.  Sweeping for files that carry BOTH
      [ContinuousFunctor] and one of [no_left_adjoint|not_left_adjoint|
      _no_adjoint] returns exactly two: Instance/FdVect/NoRightAdjoint.v
      and this one.  That file pairs [dual_vct_Continuous] with
      [dual_functor_no_right_adjoint] -- continuity together with
      the absence of a RIGHT adjoint, which is the other side of the
      street and not a witness to §V.6.

   4. "Complete Boolean algebras and Solovay's theorem are entirely
      absent (`rg -i 'solovay|complete boolean|CABA'` → 0 hits)": the
      sweep returns exactly ONE line, Instance/FdVect/NoRightAdjoint.v:
      104, and it cites a DIFFERENT theorem of Solovay's -- the ZF + DC
      model in which every set of reals has the Baire property
      (Solovay; Shelah), used there to explain why [CoordSpanProper] is
      taken as a hypothesis.  Nothing in tree mentions complete Boolean
      algebras or the free-complete-Boolean-algebra theorem, so the
      substance survives.

   5. The Awodey clause's "the library has no smallness or local-
      smallness predicate at all, so the clause cannot currently be
      phrased, let alone shown necessary": FALSE, by item 2.  The clause
      is phrased below ([RepresentabilityWithoutSolutionSet],
      [GAFTWithoutSolutionSet], [no_initial_not_Small]).

   6. The Awodey clause's three prose citations, checked one by one.
      [Adjunction/GAFT.v] is RIGHT: the paragraph cited opens "The
      hypotheses repair a genuine size obstruction rather than decorate
      the statement".  [Structure/Complete.v] is
      RIGHT: the paragraph cited opens "The smallness discipline the
      header describes is not decoration".
      [Instance/Poset.v] is WRONG: the range cited is the Lawvere
      enrichment paragraph (Two, metric spaces).  The adjoint-functor-
      theorem size paragraph is the one after it, ending "must carry a
      [SolutionSet] hypothesis".

   7. "Show the constant one-point functor [Ord^op ⟶ Sets] is continuous
      but not representable" is written as if nothing of it existed.  The
      constant one-point functor is already in tree as [ConstOne]
      (Structure/UniversalProperty/Terminal.v), and so are BOTH halves
      of the representable/initial correspondence -- [initial_to_repr]
      and [repr_to_initial], in the un-bundled
      [IsInitialObj] form.  This file REUSES all three and defines no
      constant functor of its own.  What it adds is the continuity, the
      bundling against [Functor/Representable.v]'s [Representable] class,
      and the consequences.

   8. THE MEASUREMENT THAT REDIRECTS THE ISSUE, corrected.  An earlier
      revision of this item said the library's [Complete] carries "no
      smallness side condition", that [@Complete C] therefore ALREADY
      gives [@Initial C], and that the pair "complete with no initial
      object" is consequently EMPTY so that "the §V.6 counterexample
      cannot be stated over [@Complete]".  That overstates a real fact
      into a false one, and the audit of this file measured the
      difference.  What is true is sharper and is the point of the whole
      issue.

      [Complete_Initial] below is genuine, but it consumes [@Complete C]
      at the universe instance that COLLAPSES the diagram shape's object
      universe onto [C]'s -- that is, at LARGE-completeness, limits over
      shapes as big as [C] itself.  The library's [Complete] does carry a
      smallness side condition, and Instance/Sets/Complete.v states
      it in terms and prints it: [Sets_Complete : Complete@{u u u u0}]
      with [u < u0], the shape STRICTLY below the ambient.  So the
      library's real witnesses are small-complete, and every one of them
      is REFUSED by [Complete_Initial].  Measured, with this file's own
      import list plus the four instance files, applying
      [Complete_Initial] to each witness in turn:

        Sets_Complete       -- refused
        Grp_Complete        -- refused
        Ab_Complete         -- refused
        Subsets_Complete    -- ACCEPTED

      The one witness that satisfies it is the THIN one -- the powerset
      lattice of Instance/Powerset.v.  That is not an accident and it
      is not a defect: it is Freyd's collapse (Structure/Complete/Freyd.v)
      appearing as a universe constraint.  A category with limits over
      shapes as large as itself has an initial object, and by Freyd it is
      a preorder; the thin lattice is exactly such a thing, and [Sets],
      [Grp] and [Ab] are exactly not.

      So [Complete_Initial] and its three companions
      ([Complete_ConstOne_representable], [Complete_no_initial_absurd],
      [Complete_Initial_obj]) are INERT on every large category in the
      tree, and this file says so rather than leaving a reader to
      discover it.  They are not vacuous -- [Subsets_Complete] inhabits
      the hypothesis -- but they are statements about large-completeness,
      which is a strictly stronger notion than the one Mac Lane's §V.6
      hypothesis names.

      THE COUNTEREXAMPLE THEREFORE LIVES AT SMALL-COMPLETENESS, and that
      is precisely what Instance/Ordinal/Large.v supplies: its
      [SmallOrd_op_Complete : Complete@{u u Set u0}] with [u < u0] is
      inhabited, while the collapsed instance is REFUTED there too
      ([SmallOrd_op_not_large_complete]; applying [Complete_Initial] to
      [SmallOrd_op_Complete] is likewise refused, measured).
      That pair -- the same library class inhabited at one universe
      instance and refuted at another, over one and the same category --
      is what makes the ordinals a counterexample rather than a
      restatement, and it is why no large-complete category could have
      served.  [SmallShapeComplete] below is the same boundary written
      with Theory/Size.v's [Small] instead of with universe levels;
      [SmallShapeComplete_Initial_of_Small] records that a SMALL
      small-shape-complete category takes the identity diagram back and
      the initial object returns, which is the in-tree shadow of Freyd's
      collapse at the one place this file needs it.  Note that this
      theorem is likewise inert on [Complete_SmallShapeComplete
      Sets_Complete], for the same universe reason -- disclosed here, not
      claimed away.

   ** WHAT IS DELIVERED (29 named constants plus the one [Program]
      obligation of [ConstOne_pt]; every one "Closed under the global
      context", zero [Axioms:] lines)

   (A) CONTINUITY, WITH NO HYPOTHESIS AT ALL.  [ConstOne_continuous C :
       ContinuousFunctor (ConstOne C)] for EVERY category C -- no
       completeness, no local smallness, no limit assumed anywhere.  The
       whole proof is [ConstOne_hom_unique]: a cone over the image
       diagram maps into a singleton, so the mediator exists
       ([ConstOne_pt]) and is unique, and both clauses of [IsLimitCone]
       are that one lemma.  [ConstOne_PreservesImageLimit] is the same
       fact in the hypothesis shape [GAFT] and [representability_theorem]
       consume, through Construction/Comma/Creation.v.

   (B) THE BICONDITIONAL, which is the sharp form and the model is
       Instance/Sets/NoAdjoint.v.  [ConstOne_representable_iff_initial
       C : Representable (ConstOne C) ↔ @Initial C], [Defined], with both
       legs exported separately ([initial_of_ConstOne_representable],
       [ConstOne_representable_of_initial]) and the readback
       [ConstOne_repr_obj] pinning the representing object to
       [initial_obj] at [eq_refl].  Neither leg is a new argument: the
       forward one is [repr_to_initial] followed by
       [Initial_from_IsInitialObj], the converse [IsInitialObj_from_
       Initial] followed by [initial_to_repr].  What is new is that the
       correspondence is now stated against the [Representable] CLASS,
       which quantifies the representing object away, and that is what
       makes [ConstOne_not_representable] usable.

   (C) THE LIMIT OF THE IDENTITY FUNCTOR IS INITIAL.
       [Initial_of_limit_id : Limit (@Id C) → @Initial C], by way of
       [lim_id_leg_self] (the leg at the apex is [id], since it mediates
       the limit cone to itself and so does [id]) and [lim_id_hom_unique]
       (every arrow out of the apex IS the leg).  Nothing in tree stated
       this before: `grep -rin --include='*.v' -E 'limit of the identity|
       Limit \(@?Id|Limit Id' .`, this file excluded, returns 8 lines --
       six in Theory/Equivalence/Colimit.v naming [two_IsALimit Id[_2]],
       which is the walking arrow and says nothing about initiality, and
       two that are artifacts of the case-insensitive pattern matching
       "IsALimit identifies" (Test/ProbeLimitInitial334.v) and
       "colimit identification" (Instance/Ab/DirectedColimit.v).

   (D) THE SHARPNESS CLAUSE, Awodey's, using the smallness vocabulary
       that item 2 says exists.  [RepresentabilityWithoutSolutionSet] and
       [GAFTWithoutSolutionSet] are Mac Lane's §V.6 Theorem 3 and
       Theorem 2 with the solution set REMOVED and local smallness ADDED;
       [representability_without_solution_set_refuted] and
       [gaft_without_solution_set_refuted] refute both from a
       small-shape-complete C with no initial object.  Adding
       [LocallySmall] costs the refutation nothing, since
       [locally_small_ambient] discharges it for every category -- which
       is the honest form of "local smallness does not repair the gap" in
       a library where local smallness is built into [Class Category].
       [no_initial_not_Small] is the size half: any witness to the
       sharpness is necessarily NOT [Small].

   (E) THE COMPLETE-BOOLEAN-ALGEBRA HALF, CONDITIONAL, with the
       set-theoretic input as a visible premise.  The [Solovay] section
       takes a category [CBA], a functor [U : CBA ⟶ Sets], an object
       [Countable] and the hypothesis [solovay : UniversalArrow Countable
       U → False] -- "there is no free complete Boolean algebra on a
       countable set" -- and concludes [solovay_no_left_adjoint] and,
       with small-shape completeness and continuity of U added,
       [solovay_gaft_refuted].  NOTHING IS CONSTRUCTED: no complete
       Boolean algebra, no category of them, no forgetful functor, and
       Solovay's theorem is NOT proved.  It is taken as an explicit
       hypothesis, exactly as the issue's Definition of Done requires the
       header to disclose, and there is no [Axiom] or [Parameter] here or
       anywhere in the file.  The section is therefore UNINHABITED at its
       distinctive premise in the sense of docs/INHABITATION.md, and a
       reader must not cite it as evidence that complete Boolean algebras
       behave this way -- only that IF they do, the solution set cannot
       be dropped.

   ** WHAT IS NOT DELIVERED

   - The ordinals counterexample.  No [Ord] of small ordinals, no proof
     that its opposite is small-complete, no inhabitant of the no-initial
     -object hypothesis of (D).  The issue's Verification block names
     [Ord_op_complete] and [Ord_constant_continuous_not_representable];
     neither is here under that name or any other.  The obstruction is
     not the mathematics but the size predicate: the class of small
     ordinals is exactly the thing Theory/Size.v's [Small] is designed to
     exclude, and building it means choosing an ordinal notation and a
     universe level for it.  Item 8 above is the part of that problem
     this file does solve -- it says which completeness hypothesis the
     construction has to satisfy, and shows that the obvious one is
     unusable.
   - Complete Boolean algebras, and Solovay's theorem.  See (E).
   - No [Test/Probe*] file.  The universe measurement of item 8 and the
     [Set]-minimization trap recorded at [ConstOneContinuity] are pinned
     nowhere; both deserve refutation probes and neither has one.
   - No edit to Structure/UniversalProperty/Terminal.v, Structure/
     Complete.v, Theory/Size.v, Adjunction/GAFT.v or Adjunction/
     Representability/Sets.v.
   - No claim that [SmallShapeComplete] is the RIGHT smallness notion for
     the library, and no comparison with the universe-annotated
     alternative (a [Complete] whose shape universes are declared
     strictly below C's).  [SmallShapeComplete] was chosen because it
     reuses the predicate the tree already has.

   ** UNIVERSES (measured by [About] under [Set Printing Universes] on
      all 29 constants and the [Program] obligation)

   NO constant of this file names [Set]: `grep -nE '\bSet\b'` over the
   [About] output of all 30 is empty.

   AN EARLIER REVISION OF THIS PARAGRAPH CREDITED THAT TO THE DECLARED
   UNIVERSES, and was wrong.  It said the three sections' [Universes o h.]
   / [Context (C : Category@{o h h}).] blocks are what stop [Set] from
   being minimized into [ConstOne_hom_unique] and travelling onward.
   Measured by removing all three blocks and replacing each [Context] with
   a bare [Context (C : Category).]: the file still compiles, rc=0, and no
   [Set] appears in the [About] output.  The minimization the paragraph
   feared cannot happen here at all, because Lib.v sets
   [#[export] Unset Universe Minimization ToSet] project-wide and every
   file inherits it.

   The annotations are KEPT -- writing the binders out is the house habit
   and costs nothing -- but they are not load-bearing, and this file no
   longer claims they are.  Only TWO constants carry universe
   EQUATIONS, both in the [Solovay] section: [solovay_no_left_adjoint]
   carries [u0 = u3] and [u1 = u2], [solovay_gaft_refuted] those plus
   [u6 = u21].  Attributed by [About] on the donor, not guessed:
   [universal_arrow_of_adjunction] (Adjunction/GAFT.v) binds
   [{C : Category@{u7 u8 u8}} {D : Category@{u6 u8 u8}}], identifying the
   hom-and-proof levels of the two categories, and that is [Adjunction]'s
   own block.  The control rules out the obvious alternative: the bare
   type [{ F : Sets ⟶ CBA & F ⊣ U }] carries NO equation on its own.

   ** COUNTS AND CONVENTIONS

   - 29 [.glob] declaration heads (19 [def], 10 [prf]) plus
     [ConstOne_pt_obligation_1], which is reachable only under its fully
     qualified name; all 30 report "Closed under the global context".
   - Two [Defined] tokens ([ConstOne_continuous] and
     [ConstOne_representable_iff_initial]) and ten [Qed]; the other
     seventeen heads are [:=] terms.  The biconditional is [Defined] so
     that both projections compute, unlike Instance/Sets/NoAdjoint.v's,
     which is [Qed] and has to export its adjoint separately.
   - Name collisions: none.  Each of the 29 names has 0 word occurrences
     elsewhere in the tree (`grep -rnw --include='*.v'` over Theory
     Structure Construction Instance Adjunction Functor Monad Comonad
     Natural Lib Solver Tools Test, this file excluded; instrument-checked
     against [ConstOne] (8), [Representable] (217), [Complete] (479) and
     [Small] (36), which are all nonzero).
   - Transitive [Require] closure 102 files excluding self.
     Adjunction/Representability/Sets.v costs 46 of them at the margin
     and is imported for one constant, [representable_of_left_adjoint];
     it is kept because this file is the sharpness companion to that
     file's [representability_theorem] and the link should be a term and
     not a comment.  Theory/Size.v and Structure/UniversalProperty/
     Terminal.v cost 1 each; the other 23 [Require]s cost 0.
     (CORRECTION, #451: Adjunction/SAFT.v, which Adjunction/
     Representability/Sets.v requires, now requires Theory/Subobject.v,
     and nothing else here reaches that module.  Counted over
     .Makefile.coq.d, which reproduces 102 and 46 when that edge is left
     out, the closure is 103 and Adjunction/Representability/Sets.v costs
     47 at the margin; the other margins are unchanged.) *)

(** ** The constant functor at the singleton, and its continuity *)

Section ConstOneContinuity.

(* The universes are DECLARED, not inferred.  Left to inference the two
   lemmas below minimize [C]'s hom level onto the carrier level of [Sets]
   and then onto [Set], and every consumer downstream inherits the pin
   -- which is what stops the sharpness theorems from applying to a [C]
   carrying a [Small]-constrained hypothesis. *)
Universes o h.
Context (C : Category@{o h h}).

(* Any two maps into the singleton agree.  This is the whole of the
   continuity proof: both the mediator and its uniqueness clause are
   instances of it. *)
Lemma ConstOne_hom_unique {x : C} {X : Sets}
  (f g : X ~{Sets}~> ConstOne C x) : f ≈ g.
Proof. intro a; destruct (f a), (g a); reflexivity. Qed.

Program Definition ConstOne_pt (x : C) (X : Sets) :
  X ~{Sets}~> ConstOne C x := {| morphism := fun _ => ttt |}.

(* Continuity, with NO hypothesis on [C] whatever: not completeness, not
   local smallness, not the existence of any limit.  A cone over the
   image diagram has a singleton apex to map into, so the mediator exists
   and is unique. *)
Definition ConstOne_continuous : ContinuousFunctor (ConstOne C).
Proof.
  intros J K N HN M.
  unshelve refine
    {| unique_obj := ConstOne_pt (vertex_obj[N]) (vertex_obj[M]) |}.
  - intro y; apply (ConstOne_hom_unique (x := K y)).
  - intros v Hv; apply (ConstOne_hom_unique (x := vertex_obj[N])).
Defined.

(* The same fact in the hypothesis shape that [GAFT] and
   [representability_theorem] consume. *)
Definition ConstOne_PreservesImageLimit :
  @PreservesImageLimit C Sets (ConstOne C) :=
  Continuous_PreservesImageLimit ConstOne_continuous.

End ConstOneContinuity.

(** ** Representability of [ConstOne C] is exactly initiality of [C] *)

Section ConstOneRepresentable.

Universes o h.
Context (C : Category@{o h h}).

(* Forward.  A representation names an object whose every hom-setoid is a
   singleton; [repr_to_initial] is that step, already in tree. *)
Definition initial_of_ConstOne_representable
  (R : Representable (ConstOne C)) : @Initial C :=
  Initial_from_IsInitialObj
    (repr_to_initial C (@repr_obj C (ConstOne C) R)
                       (@represented C (ConstOne C) R)).

(* Converse. *)
Definition ConstOne_representable_of_initial (I : @Initial C) :
  Representable (ConstOne C) :=
  {| repr_obj := @initial_obj C I
   ; represented :=
       initial_to_repr C (@initial_obj C I) (IsInitialObj_from_Initial I) |}.

(* The sharp form. *)
Theorem ConstOne_representable_iff_initial :
  Representable (ConstOne C) ↔ @Initial C.
Proof.
  split.
  - exact initial_of_ConstOne_representable.
  - exact ConstOne_representable_of_initial.
Defined.

Definition ConstOne_not_representable (Hno : @Initial C → False)
  (R : Representable (ConstOne C)) : False :=
  Hno (initial_of_ConstOne_representable R).

(* The representing object is the initial object, on the nose. *)
Example ConstOne_repr_obj (I : @Initial C) :
  @repr_obj C (ConstOne C) (ConstOne_representable_of_initial I)
    = @initial_obj C I := eq_refl.

End ConstOneRepresentable.

(** ** The limit of the identity functor is an initial object *)

Section LimitId.

Universes o h.
Context {C : Category@{o h h}}.
Context (L : Limit (@Id C)).

Definition lim_id_obj : C := vertex_obj[@limit_cone _ _ _ L].

Definition lim_id_leg (x : C) : lim_id_obj ~> x :=
  cone_leg (@limit_cone _ _ _ L) x.

(* Cone coherence at the identity diagram: every arrow out of the apex
   commutes with the legs. *)
Lemma lim_id_coh {x y : C} (f : x ~> y) : f ∘ lim_id_leg x ≈ lim_id_leg y.
Proof.
  exact (@cone_coherence _ _ _ _
           (@coneFrom _ _ _ (@limit_cone _ _ _ L)) x y f).
Qed.

(* The leg at the apex is the identity: it mediates the limit cone to
   itself, and so does [id], and the mediator is unique. *)
Lemma lim_id_leg_self : lim_id_leg lim_id_obj ≈ id.
Proof.
  pose proof (@ump_limits _ _ _ L (@limit_cone _ _ _ L)) as U.
  transitivity (unique_obj U).
  - symmetry; apply (uniqueness U); intro x; apply lim_id_coh.
  - apply (uniqueness U); intro x; apply id_right.
Qed.

(* ...hence every arrow out of the apex IS the leg. *)
Lemma lim_id_hom_unique {x : C} (f : lim_id_obj ~> x) : f ≈ lim_id_leg x.
Proof.
  rewrite <- (lim_id_coh f), lim_id_leg_self.
  now rewrite id_right.
Qed.

Definition Initial_of_limit_id : @Initial C :=
  @Build_Terminal (C^op) lim_id_obj (fun x => lim_id_leg x)
    (fun x f g => transitivity (lim_id_hom_unique f)
                    (symmetry (lim_id_hom_unique g))).

End LimitId.

(** ** Consequence: the library's [Complete] already carries an initial
       object, so "complete with no initial object" is an EMPTY hypothesis *)

Definition Complete_Initial {C : Category} (comp : @Complete C) : @Initial C :=
  Initial_of_limit_id (comp C Id).

Definition Complete_ConstOne_representable {C : Category}
  (comp : @Complete C) : Representable (ConstOne C) :=
  ConstOne_representable_of_initial C (Complete_Initial comp).

Definition Complete_no_initial_absurd {C : Category}
  (comp : @Complete C) (Hno : @Initial C → False) : False :=
  Hno (Complete_Initial comp).

(* ...and the initial object it produces IS the limit of the identity
   functor, on the nose. *)
Example Complete_Initial_obj {C : Category} (comp : @Complete C) :
  @initial_obj C (Complete_Initial comp) = lim_id_obj (comp C Id) := eq_refl.

(** ** Completeness for SMALL shapes, which is Mac Lane's hypothesis *)

Definition SmallShapeComplete (C : Category) : Type :=
  ∀ (D : Category), Small D → ∀ F : D ⟶ C, Limit F.

Definition Complete_SmallShapeComplete {C : Category} (comp : @Complete C) :
  SmallShapeComplete C := fun D _ F => comp D F.

(* Freyd's size boundary in the shape this file needs it: if the category
   is ITSELF small, small-shape completeness takes back the identity
   diagram and the initial object comes back. *)
Definition SmallShapeComplete_Initial_of_Small {C : Category}
  (SC : Small C) (HC : SmallShapeComplete C) : @Initial C :=
  Initial_of_limit_id (HC C SC Id).

(** ** The sharpness clause *)

(* Mac Lane §V.6 Theorem 3 with the solution set DROPPED, and with local
   smallness ADDED -- the extra hypothesis costs the refutation nothing,
   since [locally_small_ambient] discharges it for every category. *)
Definition RepresentabilityWithoutSolutionSet : Type :=
  ∀ (C : Category) (K : C ⟶ Sets),
    SmallShapeComplete C → LocallySmall C → ContinuousFunctor K →
    Representable K.

Theorem representability_without_solution_set_refuted (C : Category)
  (HC : SmallShapeComplete C) (Hno : @Initial C → False) :
  RepresentabilityWithoutSolutionSet → False.
Proof.
  intro H.
  exact (ConstOne_not_representable C Hno
           (H C (ConstOne C) HC (locally_small_ambient C)
              (ConstOne_continuous C))).
Qed.

(* Mac Lane §V.6 Theorem 2 (GAFT) with the solution set dropped. *)
Definition GAFTWithoutSolutionSet : Type :=
  ∀ (C D : Category) (U : C ⟶ D),
    SmallShapeComplete C → LocallySmall C → ContinuousFunctor U →
    { F : D ⟶ C & F ⊣ U }.

Theorem gaft_without_solution_set_refuted (C : Category)
  (HC : SmallShapeComplete C) (Hno : @Initial C → False) :
  GAFTWithoutSolutionSet → False.
Proof.
  intro H.
  destruct (H C Sets (ConstOne C) HC (locally_small_ambient C)
              (ConstOne_continuous C)) as [F A].
  exact (ConstOne_not_representable C Hno
           (representable_of_left_adjoint (ConstOne C) A)).
Qed.

(* Awodey §9.8's size clause, in the only direction this file can prove:
   a witness to the sharpness above is necessarily NOT small. *)
Theorem no_initial_not_Small (C : Category)
  (HC : SmallShapeComplete C) (Hno : @Initial C → False) : Small C → False.
Proof. intro SC; exact (Hno (SmallShapeComplete_Initial_of_Small SC HC)). Qed.

(** ** The complete-Boolean-algebra half, conditional on Solovay's theorem *)

Section Solovay.

(* [CBA] stands for the category of complete Boolean algebras and [U] for
   its forgetful functor; NOTHING below constructs either, and nothing
   below is evidence that they exist.  [solovay] is the set-theoretic
   input, stated as a hypothesis and never as an [Axiom]. *)
Context (CBA : Category).
Context (U : CBA ⟶ Sets).
Context (Countable : Sets).
Context (solovay : UniversalArrow Countable U → False).

Theorem solovay_no_left_adjoint : { F : Sets ⟶ CBA & F ⊣ U } → False.
Proof using CBA Countable U solovay.
  intros [F A]; exact (solovay (universal_arrow_of_adjunction A Countable)).
Qed.

Context (HCBA : SmallShapeComplete CBA).
Context (HU : ContinuousFunctor U).

Theorem solovay_gaft_refuted : GAFTWithoutSolutionSet → False.
Proof using CBA Countable HCBA HU U solovay.
  intro H.
  exact (solovay_no_left_adjoint
           (H CBA Sets U HCBA (locally_small_ambient CBA) HU)).
Qed.

End Solovay.
