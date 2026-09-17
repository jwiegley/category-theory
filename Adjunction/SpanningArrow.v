Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.

Generalizable All Variables.

(* Spanning arrows, and solution sets from intersections of subobjects

   nLab:  https://ncatlab.org/nlab/show/subobject
   nLab:  https://ncatlab.org/nlab/show/solution+set+condition

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7 ("Subobjects and Generators"), book pp. 127-128 (PDF pp. 136-137),
   is the source of everything below: the unnumbered Definition of a
   SPANNING arrow (catalog id maclane:V.7:def6, book p. 127), the
   unnumbered Lemma that every arrow factors through one
   (maclane:V.7:lem2, book p. 127), and the Remark that applies the Lemma
   to a variety through generated subalgebras (maclane:V.7:remark1, book
   p. 128).  CITED BY LOCATION AND BY THE IN-TREE CATALOG: the printed
   text was not consulted and no sentence of it is reproduced here.  The
   catalog summaries this file works from are
   doc/plan/books/maclane/inventory/V.json, and they read:

     def6  -- "Given any functor G : A -> X, an arrow f : x -> Ga of X is
     said to span a when there is no proper monomorphism s -> a in A
     (proper meaning a subobject strictly below the identity subobject)
     such that f factors through the image Gs -> Ga."

     lem2  -- "Let A be a category in which every set of subobjects of an
     object a has a pullback (an intersection).  If G : A -> X preserves
     all these pullbacks, then every arrow h : x -> Ga of X factors
     through an arrow f : x -> Gb which spans b. ... Consequence recorded
     in the text: a solution set for x may be taken to be the set of all
     arrows out of x which span."

   WHAT IS DELIVERED, AND AT WHAT STRENGTH.  [SubFactorsThrough],
   [Spanning] (with [spanning_arrow], the issue's pinned name, as an
   alias), [PreservesWidePullbacks] and [SpanningArrowsOutOf] are the
   vocabulary; all four are DATA (Type-valued), so a factorization is a
   lift one can compute with and not a truncated existence claim.  Lemma
   2 is then landed in four steps, each a named constant rather than a
   step of one big proof: [spanning_sub] is Mac Lane's intersection b of
   all the subobjects h factors through, [spanning_factor] is his f,
   [spanning_factor_commutes] is his h = G(v) f at ≈, and
   [spanning_factor_spanning] is "f spans b".  [factors_through_spanning]
   packages the four, and [spanning_solution_set] is his consequence:
   a [SolutionSet] (Adjunction/GAFT.v:159) whose index is exactly
   [SpanningArrowsOutOf G x].  [GAFT_from_spanning] feeds it to
   Adjunction/GAFT.v:243.  Nothing below is stated up to an isomorphism
   that is not exhibited: every equation is ≈ between named arrows.
   Two elementary facts, [sub_le_top_iso] (a subobject above the top one
   has an invertible mono) and [spanning_forces_top] (a spanning arrow
   factors through no subobject but the top one, at ≈ on [SubObj]), were
   first proved in the variety half, Instance/Variety/Spanning.v, and
   lifted here at integration.

   WHY "PROPER SUBOBJECT" IS NEVER NAMED.  Mac Lane's def6 is a negated
   existence -- "there is no proper monomorphism through which f
   factors".  A proper subobject is one strictly below the identity
   subobject, so the negation says: every subobject f factors through is
   NOT strictly below the top one.  In a setoid library with no
   antisymmetry for [SubObj] and no decision procedure for ≈, "strictly
   below" would have to be [sub_le m sub_top * (sub_le sub_top m → False)],
   and the negated existence would unfold to a double negation that
   yields nothing.  [Spanning] therefore states the CONTRAPOSITIVE-FREE
   positive form directly: every subobject m that f factors through
   satisfies [sub_le sub_top m], i.e. the top subobject factors through
   m, i.e. m is the whole of a.  This is the same move
   Structure/Generator.v makes for Riehl's Definition 4.7.7 and the same
   one Adjunction/SAFT.v:99's [Cogenerator] makes for "distinct arrows".
   The positive form is strictly stronger constructively: it hands back
   the splitting [k] with [sub_mono m ∘ k ≈ id], which is what
   [spanning_factor_spanning]'s proof produces and what a consumer needs.
   "Proper" is consequently not a defined notion anywhere in this file,
   and no lemma below asserts that a proper subobject exists.

   WHAT "SPANNING" IS RELATIVE TO.  An arrow does not span in the
   abstract: [Spanning G f] for [f : x ~> G a] quantifies over
   [SubObj a] -- the subobjects of the CODOMAIN OBJECT [a] of the
   A-side, not of [G a] in X, and not of [x].  So "f spans" is always
   short for "f spans a", and a spanning [f : x ~> G a] need not remain
   spanning when [a] is replaced by an isomorphic object unless the
   isomorphism is transported across [SubObj] as well (see NOT DELIVERED).
   The G-image enters only through [fmap[G] (sub_mono m)]: no hypothesis
   is made that G reflects or preserves monos, and [sub_mono m] monic in
   A does not make [fmap[G] (sub_mono m)] monic in X.

   THE IN-TREE SITUATION, MEASURED.  Issue #448 recorded as its verified
   current state that [SolutionSet] "is manufactured only in
   Adjunction/SAFT.v:252, never from spanning arrows".  The second half
   holds; the first is STALE, and the correction is recorded here rather
   than silently.  With
   grep -rn 'SolutionSet' --include='*.v' . over this worktree (107 lines
   in 16 files with this file and its probes excluded; an earlier
   revision said 109 in 17, measured with the stub still on disk), the
   constants whose result
   type is [SolutionSet] are: Adjunction/GAFT.v:266 [sols_of_wif] and
   :287 [sols_of_comma_initial] (repackagings of a weakly initial family
   and of a comma initial object), :367 [solution_set_of_adjunction] and
   :428 [solution_set_of_adjunction_via_comma] (from an adjunction that
   already exists), Adjunction/SAFT.v:255 [SAFT_solution_set] (the
   cogenerator-plus-well-poweredness route), Adjunction/GAFT/Sets.v:140
   [Sets_Id_SolutionSet] (hand-built at the identity functor of Sets) and
   :220 its adjunction-built twin, Adjunction/Representability/Sets.v:248
   [sols_of_esols], Instance/Grp/FreeAFT.v:417 and Instance/Rng/AFT.v:787
   and :791, and Test/ProbeGrpFreeAFT442.v:239.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17), to the
   sentence that followed and to the parenthetical inside that list.  The
   parenthetical read "(all three [solution_set_of_adjunction] applied to
   an adjunction the file already has -- Instance/Grp/FreeAFT.v:50 and
   Instance/Rng/AFT.v:166 both say so in their own headers)", and the
   sentence read "So of the structural routes to a solution set -- routes
   that do not presuppose the adjoint -- the tree had exactly one, SAFT's,
   and this file adds the second."

   The three named constants ARE still [solution_set_of_adjunction] applied
   to an adjunction the file already has, and their headers still say so.
   What is false is the count.  The same PR added, in the same three files,
   solution sets built from the QUOTIENTS OF A TERM MODEL by [Prop]-valued
   congruences: Instance/Rng/AFT.v:729 and :759, the [Prop]-congruence
   family of Instance/Mod/TensorAFT.v's section 3A, and (the [Grp] layer
   has landed) Instance/Grp/FreeAFT.v:396.  Those presuppose no adjoint, so
   the structural routes are now THREE families -- SAFT's cogenerator
   route, this file's subobject-intersection route, and the congruence
   route -- and the two GAFT applications at [Rng] are no longer circular.
   SAFT reaches it through a cogenerator and a well-powering; Mac Lane's
   §V.7 route reaches it through intersections of subobjects; the
   congruence route reaches it through the sort of [Prop].  No two of the
   three share a hypothesis.

   The donors are the ones the two preceding §V.7 issues landed.
   [sub_le] is Theory/Subobject.v:60, [sub_top] Theory/Subobject/
   Lattice.v:250, [sub_compose] :430, [sub_wide_intersection] :621 with
   [sub_wide_intersection_IsIntersection] :634 and the [IsIntersection]
   record :262; [IsWidePullback] is Structure/Pullback/Wide.v:182,
   [WidePullback] :202, [HasWidePullbacks] :257.  Every lattice fact used
   below is TRANSPORTED from Lattice.v and none is re-proved: the two
   halves of Mac Lane's argument are [inter_le] (b is contained in every
   u_j) and nothing else -- [inter_greatest] is not needed, because the
   competing subobject in the spanning step is produced rather than
   assumed.  [wide_pullback_proj_monic] and the monicity of the
   intersection's mono likewise come from Lattice.v's record and are not
   re-established.

   WHY [PreservesWidePullbacks] IS BESPOKE.  Structure/Limit/
   Preservation.v:98's [PreservesLimit] is stated for a diagram functor
   [J ⟶ C] and its limit cone; Structure/Pullback/Wide.v presents a wide
   pullback ELEMENTARILY, as a family [∀ i, P ~> A i] with a pairwise
   commutation clause and a unique mediator, and never builds the
   wide-cospan shape category (Wide.v's own NOT DELIVERED paragraph says
   so).  There is therefore no diagram to feed [PreservesLimit], and the
   interface's [PreservesWidePullbacks] states preservation directly on
   the elementary record.  It quantifies over all index types but only
   over families of MONOS -- intersections of subobjects, which is
   exactly what Mac Lane's Lemma asks G to preserve -- and Lemma 2
   consumes it at exactly one family per arrow, the monos of
   [FactoringFamily].  A first draft quantified over arbitrary families,
   a hypothesis strictly stronger than Mac Lane's; an audit flagged it
   and the monicity clause was added at integration, the proof body
   unchanged but for passing the monicity witnesses.

   UNIVERSES, MEASURED BY About (Set Printing Universes).
   [Spanning@{u u0 u1 u2 u3} : ∀ {A : Category@{u u0 u0}}
   {X : Category@{u1 u2 u2}} ...] -- A's hom universe is identified with
   its proof universe.  That identification is NOT this file's: it is
   [SubObj@{u u0} : ∀ {C : Category@{u u0 u0}}] of Theory/Subobject.v:15,
   and it is also what a bare [{A X : Category}] minimizes to anyway (a
   control definition over a bare pair of categories and a functor
   between them reports [Category@{u u0 u0}] and [Category@{u1 u0 u0}]).
   What this file's constants add on top is visible at
   [spanning_solution_set@{...}], which carries [u0 = u2] -- A's hom
   universe identified with X's.  That comes from the donor record:
   [SolutionSet@{i dobj cobj h} : ∀ {C : Category@{cobj h h}}
   {D : Category@{dobj h h}}] at Adjunction/GAFT.v:179 shares one hom
   universe between source and target.  (An earlier revision quoted the
   same record with the inferred binder names [@{u u0 u1 u2}]; the binders
   were written out in the PR "algebraic carriers are sets", 2026-09-17,
   and the shape is unchanged.)  [spanning_sub], [spanning_factor],
   [spanning_factor_spanning] and [factors_through_spanning] do not carry
   it.  No constant in this file is pinned at [Set] except
   [GAFT_from_spanning] -- and that pin is now this file's OWN section
   annotation rather than a restriction inherited from [GAFT]; the
   correction is recorded at that section below.

   TRANSPARENCY, AND WHY IT IS NOT UNIFORM.  31 constants: 16 are [:=]
   terms, 10 end in [Defined] (the two lifted facts among them) and 5 in
   [Qed].  The split follows the
   donor's own discipline (Theory/Subobject/Lattice.v is [Defined]
   everywhere its result is data -- [sub_le], [IsIntersection] -- and
   [Qed] only for the genuinely propositional [wide_pullback_proj_monic],
   [sub_le_monic], [sub_le_unique]): everything below whose result type
   is [SubFactorsThrough], [Spanning] or [sub_le] is transparent, and only
   the ≈-equations and [GAFT_from_spanning] are opaque.  MEASURED, not
   assumed: flipping every [Qed] in the file to [Defined] leaves it
   compiling (rc=0), so opacity is nowhere forced; and flipping either
   [Defined] on [factors_through_top] or [spanning_solution_set] to [Qed]
   ALSO leaves the file compiling, but each then REFUSES an [eq_refl]
   readback that holds as it stands -- `1 (factors_through_top G f) = f
   and [sol_index (spanning_solution_set G GP x)
   = SpanningArrowsOutOf G x], with [sol_obj] and [sol_arr] beside it.
   Those two [Defined]s are therefore load-bearing and the rest are a
   choice.

   NOT DELIVERED, and the scope of each statement is this file rather
   than the tree.  (1) No smallness, and so no Remark 1.  Mac Lane's
   Lemma quantifies over a SET of subobjects and his Remark bounds the
   cardinal of the generated subalgebra by those of S and Ω; here
   [FactoringFamily] is a [Type] at whatever universe [SubObj a] lands
   in, [HasWidePullbacks] is instantiated at that universe, and the
   [sol_index] delivered is [SpanningArrowsOutOf G x] with no cardinality
   statement of any kind.  Nothing below shows that index is small.
   (2) No variety instance.  Mac Lane's Remark is about Alg_τ and its
   underlying-set functor; Instance/Variety/Free.v:291's [SVariety] has
   no pullbacks, no wide pullbacks and no subalgebra vocabulary in tree
   (grep -rn 'subalgebra' --include='*.v' . finds four lines, all prose:
   Theory/Lawvere.v:89, Instance/Lie.v:313, Instance/Variety/Free.v:22
   and :108), so neither [HasWidePullbacks] nor [PreservesWidePullbacks]
   is discharged there and the Remark is not attempted here.  His Remark
   also REDEFINES subobject for that application ("a morphism u : s -> a
   for which Gu is injective in Set"), which is a different notion from
   [SubObj] and is not introduced below.  (3) No inhabitation of either
   hypothesis.  No [HasWidePullbacks] instance and no
   [PreservesWidePullbacks] witness is built in this file; Lemma 2 is an
   axiom-free CONDITIONAL, in the sense docs/INHABITATION.md uses, and
   [GAFT_from_spanning] is a conditional over four hypotheses at once.
   The tree's only [HasWidePullbacks] instance,
   Instance/Sets/SubobjectLattice.v's [Sets_HasWidePullbacks], does NOT
   discharge the first hypothesis either: its index type lives at the
   hom universe of [Sets] while [FactoringFamily] lives at the universe
   of [SubObj a], one level up, and applying it is refused with
   "universe inconsistency: Cannot enforce <the instance's index
   universe> = <the universe of SubObj a>" (measured by two audits, whose
   scratch-local universe labels differ, so the shape is quoted and not
   the labels), so BOTH hypotheses are open in tree.
   (4) No converse.  Nothing shows that an arrow through which every
   factorization is spanning must be [spanning_factor] of itself, and
   nothing shows [spanning_sub] is unique up to ≈ as a SUBOBJECT beyond
   what Lattice.v's [IsIntersection_unique] already gives.  (5) No
   transport of [Spanning] along an isomorphism of the codomain object:
   that needs an action of [a ≅ b] on [SubObj a], and Theory/Subobject.v
   has none -- the only transport in tree is Theory/Subobject/Functor.v's
   [sub_reindex], which is a pullback and needs [HasPullbacks], a
   requirement this file does not take.  The iso transport that IS landed
   below is on the DOMAIN, [spanning_precompose_iso].  (6) No probe file
   is written here; the boundaries this file's claims rest on are
   reported to the issue rather than pinned in Test/. *)

Section SpanningArrow.

Context {A X : Category}.
Context (G : A ⟶ X).

(* f : x ~> G a FACTORS THROUGH the subobject m of a when it lifts along
   G (sub_mono m).  The lift is data, as everywhere in this library. *)
Definition SubFactorsThrough {x : X} {a : A} (f : x ~> G a) (m : SubObj a) :
  Type :=
  { k : x ~> G (sub_dom m) & fmap[G] (sub_mono m) ∘ k ≈ f }.

(* Mac Lane's definition, stated POSITIVELY as a cancellation law: f
   spans a when every subobject of a through which f factors is already
   the whole of a, i.e. lies above the top subobject [sub_top] (so its
   mono is an isomorphism).  "Proper subobject" -- one for which
   [sub_le sub_top m] does not hold -- never needs to be named, exactly
   as Adjunction/SAFT.v:99's [Cogenerator] avoids "distinct arrows". *)
Definition Spanning {x : X} {a : A} (f : x ~> G a) : Type :=
  ∀ m : SubObj a, SubFactorsThrough f m → sub_le sub_top m.

(* The issue's pinned name, an alias of [Spanning] -- the same Type, so
   that the verification block's [Print Assumptions spanning_arrow] has a
   referent.  Every statement below is about [Spanning]. *)
Definition spanning_arrow {x : X} {a : A} (f : x ~> G a) : Type :=
  Spanning f.

(* G preserves wide pullbacks OF MONOS -- intersections of subobjects,
   exactly what Mac Lane's Lemma asks G to preserve: the image under G
   of a wide pullback cone over a family of monos is again a wide
   pullback cone.  A first draft quantified over arbitrary families, a
   hypothesis strictly stronger than Mac Lane's; an audit flagged it and
   the monicity clause [Hm] was added at integration. *)
Definition PreservesWidePullbacks : Type :=
  ∀ (I : Type) (B : I → A) (z : A) (g : ∀ i, B i ~> z)
    (Hm : ∀ i, Monic (g i)) (P : A) (p : ∀ i, P ~> B i),
    IsWidePullback g P p →
    IsWidePullback (fun i => fmap[G] (g i)) (G P) (fun i => fmap[G] (p i)).

(* The index of the solution set the lemma delivers: the spanning arrows
   out of x, with their codomains. *)
Definition SpanningArrowsOutOf (x : X) : Type :=
  { a : A & { f : x ~> G a & Spanning f } }.

End SpanningArrow.

Arguments SubFactorsThrough {A X} G {x a} f m.
Arguments Spanning {A X} G {x a} f.
Arguments spanning_arrow {A X} G {x a} f.
Arguments PreservesWidePullbacks {A X} G.
Arguments SpanningArrowsOutOf {A X} G x.

(** ** Elementary closure properties, before any hypothesis on A or G *)

Section SpanningElementary.

Context {A X : Category}.
Context (G : A ⟶ X).

Lemma factors_through_top {x : X} {a : A} (f : x ~> G a) :
  SubFactorsThrough G f (sub_top (x:=a)).
Proof.
  exists f; simpl.
  rewrite fmap_id; cat.
Defined.

Lemma spanning_respects {x : X} {a : A} (f f' : x ~> G a) :
  f ≈ f' → Spanning G f → Spanning G f'.
Proof.
  intros Hf Hs m [k Hk].
  apply Hs.
  exists k.
  now rewrite Hk.
Defined.

Lemma spanning_precompose_split_epi {x x' : X} {a : A}
  (f : x ~> G a) (e : x' ~> x) (s : x ~> x') (Hes : e ∘ s ≈ id) :
  Spanning G f → Spanning G (f ∘ e).
Proof.
  intros Hs m [k Hk].
  apply Hs.
  exists (k ∘ s).
  rewrite comp_assoc, Hk, <- comp_assoc, Hes; cat.
Defined.

Corollary spanning_precompose_iso {x x' : X} {a : A}
  (f : x ~> G a) (i : x' ≅ x) : Spanning G f → Spanning G (f ∘ to i).
Proof.
  exact (spanning_precompose_split_epi f (to i) (from i) (iso_to_from i)).
Defined.

Lemma spanning_of_top_only {x : X} {a : A} (f : x ~> G a)
  (H : ∀ m : SubObj a, sub_le sub_top m) : Spanning G f.
Proof. intros m _; exact (H m). Defined.


(* The two facts below were first proved in Instance/Variety/Spanning.v,
   the parallel witness half of #448, under a "CANDIDATE FOR this file"
   note, and were lifted here at integration; the variety file consumes
   [spanning_forces_top], while [sub_le_top_iso] is stated for the
   reading it gives and is not yet consumed anywhere.  Neither re-proves
   a lattice fact: they TRANSPORT
   Theory/Subobject/Lattice.v:256's [sub_top_greatest] and :284's
   [sub_le_antisym]. *)

(* A subobject that the top subobject factors through has an invertible
   mono: the factor is its inverse, the other triangle by monicity.  This
   is the sense in which Mac Lane's "factors through no proper subobject"
   is recovered from the positive form of [Spanning]. *)
Lemma sub_le_top_iso {a : A} (m : SubObj a) (H : sub_le sub_top m) :
  IsIsomorphism (sub_mono m).
Proof.
  destruct H as [k Hk]; simpl in Hk.
  unshelve econstructor.
  - exact k.
  - exact Hk.
  - apply (monic (Monic:=sub_is_monic m)).
    rewrite comp_assoc, Hk.
    now rewrite id_left, id_right.
Defined.

(* Mac Lane's own words, read back: a spanning arrow factors through no
   subobject other than the top one, at ≈ on [SubObj]. *)
Lemma spanning_forces_top {x : X} {a : A} (f : x ~> G a) (Hf : Spanning G f)
  (m : SubObj a) (Hm : SubFactorsThrough G f m) : m ≈ sub_top.
Proof.
  apply sub_le_antisym.
  - exact (sub_top_greatest m).
  - exact (Hf m Hm).
Defined.

End SpanningElementary.

Arguments sub_le_top_iso {_ _} _ _.
Arguments spanning_forces_top {_ _} _ {_ _} _ _ _ _.

(** ** Mac Lane's Lemma 2: factoring through a spanning arrow *)

Section SpanningLemma.

Context {A X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).

Section AtAnArrow.

Context {x : X} {a : A}.
Context (f : x ~> G a).

Definition FactoringFamily : Type :=
  { m : SubObj a & SubFactorsThrough G f m }.

Definition factoring_sub (j : FactoringFamily) : SubObj a := `1 j.

Definition factoring_lift (j : FactoringFamily) :
  x ~> G (sub_dom (factoring_sub j)) := `1 (`2 j).

Lemma factoring_lift_commutes (j : FactoringFamily) :
  fmap[G] (sub_mono (factoring_sub j)) ∘ factoring_lift j ≈ f.
Proof. exact (`2 (`2 j)). Qed.

Definition factoring_top : FactoringFamily :=
  (sub_top; factors_through_top G f).

Definition factoring_wpull :
  WidePullback (fun j => sub_mono (factoring_sub j)) :=
  wide_pullback (fun j => sub_mono (factoring_sub j)).

Definition spanning_sub : SubObj a :=
  sub_wide_intersection factoring_sub factoring_top factoring_wpull.

Definition spanning_sub_IsIntersection :
  IsIntersection factoring_sub spanning_sub :=
  sub_wide_intersection_IsIntersection factoring_sub factoring_top
    factoring_wpull.

Definition spanning_wpull_preserved :
  IsWidePullback (fun j => fmap[G] (sub_mono (factoring_sub j)))
                 (G (WPull factoring_wpull))
                 (fun j => fmap[G] (wide_pullback_proj factoring_wpull j)) :=
  GP FactoringFamily (fun j => sub_dom (factoring_sub j)) a
     (fun j => sub_mono (factoring_sub j))
     (fun j => sub_is_monic (factoring_sub j))
     (WPull factoring_wpull) (wide_pullback_proj factoring_wpull)
     (wide_pullback_is_pullback factoring_wpull).

Lemma factoring_lifts_agree (i j : FactoringFamily) :
  fmap[G] (sub_mono (factoring_sub i)) ∘ factoring_lift i
    ≈ fmap[G] (sub_mono (factoring_sub j)) ∘ factoring_lift j.
Proof. now rewrite !factoring_lift_commutes. Qed.

Definition spanning_mediator :
  ∃! u : x ~> G (WPull factoring_wpull),
    ∀ j : FactoringFamily,
      fmap[G] (wide_pullback_proj factoring_wpull j) ∘ u ≈ factoring_lift j :=
  wpull_ump spanning_wpull_preserved factoring_lift factoring_lifts_agree.

Definition spanning_factor : x ~> G (sub_dom spanning_sub) :=
  unique_obj spanning_mediator.

Lemma spanning_factor_lifts (j : FactoringFamily) :
  fmap[G] (wide_pullback_proj factoring_wpull j) ∘ spanning_factor
    ≈ factoring_lift j.
Proof. exact (unique_property spanning_mediator j). Qed.

Theorem spanning_factor_commutes :
  fmap[G] (sub_mono spanning_sub) ∘ spanning_factor ≈ f.
Proof.
  change (sub_mono spanning_sub)
    with (sub_mono (factoring_sub factoring_top)
            ∘ wide_pullback_proj factoring_wpull factoring_top).
  rewrite fmap_comp, <- comp_assoc.
  rewrite spanning_factor_lifts.
  apply factoring_lift_commutes.
Qed.

Lemma spanning_sub_least (m : SubObj a) :
  SubFactorsThrough G f m → sub_le spanning_sub m.
Proof.
  intro Hm.
  exact (inter_le factoring_sub spanning_sub spanning_sub_IsIntersection
           (m; Hm)).
Defined.

Theorem spanning_factor_spanning : Spanning G spanning_factor.
Proof.
  intros n [l Hl].
  assert (Hm' : SubFactorsThrough G f (sub_compose spanning_sub n)).
  { exists l.
    change (sub_mono (sub_compose spanning_sub n))
      with (sub_mono spanning_sub ∘ sub_mono n).
    rewrite fmap_comp, <- comp_assoc, Hl.
    exact spanning_factor_commutes. }
  destruct (spanning_sub_least (sub_compose spanning_sub n) Hm') as [k Hk].
  exists k; simpl.
  apply (monic (Monic := sub_is_monic spanning_sub)).
  rewrite id_right, comp_assoc.
  exact Hk.
Defined.

End AtAnArrow.

Definition factors_through_spanning {x : X} {a : A} (f : x ~> G a) :
  { m : SubObj a & { f' : x ~> G (sub_dom m)
                   & Spanning G f' * (fmap[G] (sub_mono m) ∘ f' ≈ f) } } :=
  (spanning_sub f;
     (spanning_factor f;
        (spanning_factor_spanning f, spanning_factor_commutes f))).

(** ** The solution set the lemma delivers *)

Definition spanning_solution_set (x : X) : SolutionSet G x.
Proof using A G GP HWP X.
  unshelve refine
    {| sol_index := SpanningArrowsOutOf G x
     ; sol_obj := fun i => `1 i
     ; sol_arr := fun i => `1 (`2 i) |}.
  intros c h.
  destruct (factors_through_spanning h) as [m [f' [Hsp Hcom]]].
  exact ((sub_dom m; (f'; Hsp)); (sub_mono m; Hcom)).
Defined.

End SpanningLemma.

(** ** Mac Lane's use of the lemma: GAFT without a separate solution set *)

(* WHY THIS SECTION EXISTS -- AND A RECORDED CORRECTION: ITS REASON NO
   LONGER HOLDS, THOUGH THE SECTION IS STILL WHAT THE FILE SHIPS.

   An earlier revision of this comment read, in full:

     "MEASURED UNIVERSE PIN, and the reason this section exists.  With
      Set Printing Universes, [About GAFT] reports
        GAFT@{u u0 u1 u2 u3 u4} :
          ∀ {C : Category@{u1 Set Set}} {D : Category@{u2 Set Set}} ...
      -- Adjunction/GAFT.v:243 is pinned at hom = proof = Set in BOTH
      arguments.  The pin is ATTRIBUTED BY About, not guessed: of the
      five constants GAFT's proof consumes, [Comma_Complete],
      [wif_of_sols], [Complete_HasEqualizers] and [GAFT_from_initials]
      all report a free hom universe, and [initial_from_weakly_initial]
      (Theory/WeaklyInitial.v:102) reports
        initial_from_weakly_initial@{u u0 u1 u2} :
          ∀ {C : Category@{u2 Set Set}} ...
      so that is the carrier.  (Instance/One.v's [_1],
      Instance/Parallel.v's [Parallel] and Instance/Discrete.v's
      [DiscreteCat] are each free in h, measured the same way; an earlier
      draft of this comment named them and was wrong.)  Nothing above
      carries the pin: [spanning_solution_set] is polymorphic in the hom
      universe, as the header's About records.  Feeding it to [GAFT]
      inside Section SpanningLemma is therefore REFUSED, with
        universe inconsistency: Cannot enforce Set = <the hom universe of A>
      so the corollary is stated here instead, over categories annotated
      at Set."

   Every step of that attribution was correct, and it located the pin one
   link further back than [initial_from_weakly_initial]: at
   Instance/Discrete.v's then-unannotated [DiscreteCat_Functor], which
   [initial_from_weakly_initial] takes two limits over.  That donor was
   annotated in place at Instance/Discrete.v:81 in the PR "algebraic
   carriers are sets" (2026-09-17).  Measured after it:

     GAFT@{cobj dobj h u u0 u1} :
       ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} ...

   -- no [Set], both hom universes free -- and the refusal quoted above
   NO LONGER OCCURS.  Re-measured directly: the very [exact] below,
   restated in a section whose A and X are declared at free hom
   universes, is ACCEPTED, reporting
   [GAFT_from_spanning_free@{oA hA oX hX …}] with [Complete@{hA hA hA oA}]
   and no [Set] anywhere.

   The section below is nonetheless left AS IT STANDS, annotated at [Set],
   because that PR changed prose only; widening it is a change to the
   statement of a shipped theorem and belongs to its own commit.  What the
   [Set] annotation now is, therefore, is a RESTRICTION THIS FILE IMPOSES
   and no longer one it inherits -- and it was never a claim that spanning
   arrows need small hom-sets.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): the own
   commit anticipated in the paragraph above is this one, and the widening
   has been made.  The [Universes oA oX.] line and the two [@{oA Set Set}]
   / [@{oX Set Set}] annotations are GONE; [A] and [X] are now declared
   bare, and the elaborator arrives at free object and hom levels for both.
   Nothing else in the section changed -- the statement, the [Proof using]
   list and the one-line [exact] are untouched -- so no theorem was lost
   and none was weakened.  Measured, [About] under [Set Printing
   Universes]:

     BEFORE (8 universes)
       GAFT_from_spanning@{oA oX u u0 u1 u2 u3 u4} :
         ∀ {A : Category@{oA Set Set}} {X : Category@{oX Set Set}}
           (G : A ⟶ X),
         HasWidePullbacks@{u u oA Set} A →
         PreservesWidePullbacks@{oA Set oX Set u0 u1 u1 u1} G →
         Complete@{Set Set Set oA} →
         PreservesImageLimit@{oA Set oX Set u3 Set u4 Set} → ∃ F : X ⟶ A, F ⊣ G
       (* … Set = oA / u = u1 *)

     AFTER (13 universes)
       GAFT_from_spanning@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11} :
         ∀ {A : Category@{u u0 u0}} {X : Category@{u1 u2 u2}} (G : A ⟶ X),
         HasWidePullbacks@{u3 u4 u u0} A →
         PreservesWidePullbacks@{u u0 u1 u2 u5 u6 u7 u8} G →
         Complete@{u0 u0 u0 u} →
         PreservesImageLimit@{u u0 u1 u0 u10 u0 u11 u0} → ∃ F : X ⟶ A, F ⊣ G
       (* … u <= u0 / u0 <= u2 / u2 < u10 / u2 < u11 / u3 < u5 / u6 < u5 … *)

   No [Set] anywhere, and in particular the BEFORE block's [Set = oA] --
   which demanded a category whose OBJECTS as well as homs live in [Set] --
   is gone.  [spanning_solution_set] never carried the pin and its
   [About] is unchanged.

   WHAT THE WIDENING DOES NOT BUY.  It does not make the theorem reach
   [RMod R].  The AFTER block reads [u <= u0], objects at or below homs,
   and [RMod R] has homs strictly below objects; feeding it is still
   refused, now with "Cannot enforce u_hom = b because u_hom < u_obj <= b"
   rather than with the old [Set] message.  That refusal, and the
   independent fact that [HasWidePullbacks (RMod R)] is itself universe-
   refused, are recorded at Instance/Mod/Spanning.v:149-180 and pinned as
   NEGATIVE 2 of Test/ProbeModTensorAFT449.v.  The route that DOES reach
   [RMod R] is the congruence-indexed solution set of
   Instance/Mod/TensorAFT.v, which goes through [representability_theorem]
   and not through this section. *)

Section GAFTFromSpanning.

Context {A : Category}.
Context {X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).

Theorem GAFT_from_spanning (comp : @Complete A)
  (cont : @PreservesImageLimit A X G) : { F : X ⟶ A & F ⊣ G }.
Proof using A G GP HWP X.
  exact (GAFT G comp cont (spanning_solution_set G GP)).
Qed.

End GAFTFromSpanning.
