Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Disjoint.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Bicartesian.Matrix.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.Diagonal.Coproduct.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Grp.FreeAFT.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Colimit.

Generalizable All Variables.

(** * Colimits of groups, from the adjoint functor theorem *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab:      https://ncatlab.org/nlab/show/free+product
   nLab:      https://ncatlab.org/nlab/show/Grp
   Wikipedia: https://en.wikipedia.org/wiki/Free_product
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_groups

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7 Exercise 1 (book p. 128, PDF p. 137) asks that the free product of
   two groups be obtained from the adjoint functor theorem, and that its
   two injections be shown monic with images meeting in the trivial
   subgroup; §IX.1 Exercise 1 (book p. 214, PDF p. 221) asks that [Grp] be
   shown to have ALL small colimits by the same theorem.  The theorem is
   Freyd's general adjoint functor theorem, §V.6 Theorem 2, which the tree
   carries as Adjunction/GAFT.v's [GAFT]; Instance/Grp/FreeAFT.v applies
   it at the forgetful functor, as §V.6 does on book p. 123 (the page the
   in-repo catalog, doc/plan/books/maclane/inventory/V.json, gives for
   its entry maclane:V.6:construction-free-group).  Wikipedia's
   "Free product" gives the element-level picture this file never builds:
   reduced words alternating between the two factors.

   ** THE ISSUE'S SURVEY IS PARTLY STALE, MEASURED

   Issue #450 says the free product of groups is "prose only" and that
   there is "no [Grp]".  Neither held when this file was written.  [Grp]
   is Instance/Grp.v (#255), and Instance/Grp/Pushout.v already builds the
   free product by generators and relations -- [Grp_free_product], the
   exported [Grp_Cocartesian] and [Grp_free_product_injections_Monic] --
   as an amalgam along constant legs, with no adjoint functor theorem in
   sight.  What WAS absent, measured at the parent commit (e139ecfb) by
   [grep -rn --include='*.v'] over the whole tree: [GAFT] applied at a
   diagonal functor (pattern ['GAFT[A-Za-z_]* +\(?@?Diagonal'], no hit), a
   [HasCoequalizers Grp] (no hit), and a [Cocomplete] at any algebraic
   category (pattern ['@?Cocomplete *\(?(Grp|Rng|Ring|Ab|CMon|RMod|Rg)'],
   whose one hit is Instance/Ab/DirectedColimit.v's prose "No [Cocomplete
   Ab]").  Those are what this file adds, and
   [Grp_coproduct_agrees] below says the free product it obtains IS the one
   Instance/Grp/Pushout.v built.

   NAMES.  The issue suggests a module Instance/Grp/Coproduct.v, not
   used, and its verification block runs [Print Assumptions
   Grp_free_product].  That constant is Instance/Grp/Pushout.v's
   words-based free product, not a construction by the adjoint functor
   theorem; the latter is this file's [Grp_Cocartesian_via_GAFT], and
   [Grp_free_product_iso] and [Grp_coproduct_agrees] relate the two.

   ** THE ROUTE: ONE THEOREM, APPLIED AT THE DIAGONAL

   A J-shaped colimit functor is a left adjoint of the diagonal
   Δ[J] : Grp ⟶ [J, Grp], and Adjunction/Diagonal/Limit.v reads colimits
   off such an adjoint ([Diagonal_left_adjoint_HasColimits]).  So for each
   shape J the UNIVERSES section below allows (homs at the carrier
   universe, objects at or below it), [GAFT] is applied to Δ[J]
   ([Grp_colim_via_GAFT]), and the three hypotheses are:

     - completeness of the domain: Instance/Grp/Limit.v's [Grp_Complete];
     - continuity of Δ[J]: Adjunction/Diagonal/Limit.v's
       [Diagonal_continuous], bridged to [GAFT]'s preservation hypothesis
       by Construction/Comma/Creation.v's [Continuous_PreservesImageLimit]
       (the alternative, [right_adjoint_PreservesImageLimit], would be circular
       here, Δ[J] being a right adjoint exactly when the colimits exist);
     - a solution set at each diagram D : J ⟶ Grp:
       [Diagonal_Grp_solution_set], the one new ingredient.

   [Grp_Cocomplete_via_GAFT] assembles the shapes into a [Cocomplete].

   ** THE SOLUTION SET: CONE CONGRUENCES ON A FREE GROUP

   Following the one idea of Instance/Grp/FreeAFT.v, the index is a family
   of [Prop]-valued congruences on a term model, never a Σ over the
   objects of [Grp] (the size note in the header of Structure/Complete.v
   explains why the latter is one universe too high).  Here the term model
   is the free group [FGWord DGen] on the DISJOINT UNION of the carriers,
   [DGen] = Σ j, carrier (D j), taken with Leibniz equality.  A member of
   the index ([DCongIdx]) is a relation [Rq] with a proof of
   [IsCoconeCong Rq]: [Rq] is a group congruence ([IsGrpCongruence]), it
   identifies the letters of `≈`-equal elements ([cc_resp]), it makes each
   insertion multiplicative ([cc_mul]), and it identifies [a] with its
   image under every arrow of the diagram ([cc_nat]).  Those three extra
   clauses are exactly what makes the insertions into the quotient
   [DQ i] group homomorphisms ([dq_leg], through Instance/Grp.v's
   [Build_GrpHom'], which derives the unit law) and makes them a cocone
   ([dq_arr]).  Covering: a cocone h : D ⟹ Δ(c) flattens to a map of
   generators ([dflat]), extends to the free group
   ([free_grp_extend]), and its kernel ([fg_ker] of Instance/Grp/FreeAFT.v)
   is a cocone congruence ([dker_cocone]) whose quotient maps to c by
   [fg_ker_med].  The kernel is a [Prop] because the TARGET c carries
   [grp_prop]; that is the property the PR "algebraic carriers are sets"
   (2026-09-17) added to every [GrpObject], and without it the index would
   not fit at the carrier universe.

   [dker_cocone] ENDS IN [Defined], AND MUST.  [QGrp] depends on the proof
   of [IsGrpCongruence], so the quotient at the kernel index is the
   quotient [fg_ker_med] maps out of only when [cc_grp _ dker_cocone]
   reduces to [fg_ker_is_cong].  Measured by closing [dker_cocone] with
   [Qed] in a copy of this file: [Diagonal_Grp_solution_set] is then
   refused with "The term "fg_ker_med (dflat c h)" has type "GrpHom (QGrp
   (fg_ker (dflat c h)) (fg_ker_is_cong (dflat c h))) c" while it is
   expected to have type "DQ (dker_idx c h) ~{ Grp }~> c"" (universe
   instances elided).

   ** FINITE COLIMITS, THROUGH THE EXISTING BRIDGES

   The binary coproduct, the coequalizers and the initial object are NOT
   rebuilt: Structure/Limit/Finite.v's bridges are applied to
   [Cocomplete_FinitelyCocomplete Grp_Cocomplete_via_GAFT], read in
   [Grp^op] by [FinitelyCocomplete_FinitelyComplete_op].
   [Grp_Cocartesian_via_GAFT] is [FinitelyComplete_Cartesian] of it,
   [Grp_HasCoequalizers_via_GAFT] is Structure/Pullback/Reduction.v's
   [HasCoequalizers_of_HasEqualizers_op] after [FinitelyComplete_HasEqualizers],
   and [Grp_Initial_via_GAFT] is [FinitelyCocomplete_Initial].

   What that assembly IS, read off the bodies of those bridges in
   Structure/Limit/Finite.v: [FinitelyComplete_Cartesian] and
   [FinitelyComplete_HasEqualizers] are [Cartesian_of_HasPullbacks_Terminal]
   and [HasEqualizers_of_HasPullbacks_Terminal] at
   [FinitelyComplete_Terminal] and [FinitelyComplete_HasPullbacks], so,
   read back in [Grp], the binary coproduct is the AFT pushout over the
   AFT initial object, the coequalizer is assembled from AFT pushouts and
   the AFT initial object, and the initial object is the AFT colimit of
   the empty diagram.  Every one of those colimits is itself a [GAFT]
   colimit at a diagonal: [Grp_Cocomplete_via_GAFT] at the opposite of
   Finite.v's walking cospan [Roof^op] for a pushout, and at the
   opposite of its [EmptyShape] for the initial object.  The direct
   reading -- the coproduct as [GAFT]'s colimit over a discrete
   two-object shape, the coequalizer as its colimit over the walking
   parallel pair -- is NOT the one used; the same bridge assembly is
   used for all three categories of #450 (this file,
   Instance/Rng/Colimit.v and Instance/Variety/Colimit.v).

   Structure/Limit/Cartesian.v's [Cartesian_Limit] over
   Instance/Two/Discrete.v's [Two_Discrete] is deliberately NOT the route:
   [About] reads [Two_Discrete@{u u0} : Category@{u Set Set}] and
   [Cartesian_Limit@{u u0 u1 u2} : ∀ C : Category@{u2 Set Set}, …], and
   [Fun] identifies a shape's hom universe with the target's, so that route
   would pin the group carriers to [Set], below the [Set < carrier] side
   condition of [Grp_colim_via_GAFT] (UNIVERSES, below).

   ** INSTANCE DISCIPLINE

   This file imports Instance/Grp/Pushout.v, whose [Grp_Cocartesian] is
   [#[export]].  Every statement below that mentions a coproduct therefore
   passes its [Cocartesian] argument EXPLICITLY, so that no headline says
   "via the adjoint functor theorem" while resolving to the words-based
   instance.  Nothing in this file is registered as an [Instance].

   ** WHAT IS PROVED ABOUT WHAT WAS BUILT

   Agreement.  [Grp_coproduct_agrees] is Theory/Adjunction.v's
   [left_adjoint_iso] over Adjunction/Diagonal/Coproduct.v's
   [Diagonal_Coproduct_Adjunction] at the two [Cocartesian] structures: the
   two coproduct bifunctors [+(Grp)] agree up to natural isomorphism.  At
   one pair, [Grp_free_product_iso] is the comparison G +_AFT H ≅ G * H
   built from the two copairings, and [Grp_free_product_iso_inl] /
   [Grp_free_product_iso_inr] say it carries injections to injections --
   so the object the adjoint functor theorem produces is Instance/Grp/
   Pushout.v's free product, compatibly with the injections
   ([Grp_Cocartesian_obj_is_free_product] reads the right-hand object back
   as [Grp_free_product G H] by [eq_refl]).  [Grp_initial_agrees] compares
   the initial object with Instance/Grp.v's trivial group [Grp_Initial],
   and [Grp_coequalizer_agrees_normal_closure] compares the coequalizer of
   (f, 0) with Instance/Grp/Quotient/Colimit.v's quotient by the normal
   closure of the image of f (Riehl, "Category Theory in Context",
   Example 3.1.25).  The last two could not have been stated before #450,
   when Instance/Grp.v's zero object lived only at [Set] carriers; #450
   wrote out its universes in place (see the essay above [Grp_trivial]
   there).

   Exercise 1, second half.  [Grp_inl_via_GAFT_Monic] and
   [Grp_inr_via_GAFT_Monic] are Structure/Bicartesian/Matrix.v's
   [inl_Monic] / [inr_Monic] at [Grp_Zero] and the AFT coproduct: each
   injection is split by the copairing of the identity with the trivial
   map.  That is NOT the exercise's own method.  The in-repo catalog's
   statement summary of §V.7 Exercise 1
   (doc/plan/books/maclane/inventory/V.json, entry maclane:V.7:ex1, book
   page 128) opens this half with "Using the product G x H", which in
   this library is the comparison G + H → G × H, Structure/Semiadditive.v's
   [can_comparison]; the retraction needs no product at all, and
   Theory/Subobject/Disjoint.v's header records why that route is
   preferred there.  [Grp_free_product_meet_trivial] is
   Theory/Subobject/Disjoint.v's [coproduct_injections_meet_trivial] at
   the same structures: the intersection of the two injections, in the
   sense of #445's [sub_meet] (a pullback), is the bottom subobject, whose
   domain IS the trivial group by [eq_refl]
   ([Grp_free_product_meet_bottom_is_trivial]).  Its pullbacks are
   [Grp_HasPullbacks], chosen by measurement between two routes:
   [FinitelyComplete_HasPullbacks (Complete_FinitelyComplete Grp_Complete)]
   and Structure/Pullback/Reduction.v's
   [HasPullbacks_of_Cartesian_HasEqualizers] at [Grp_Cartesian].  Both
   carry the same strict bound, carrier < [eq_rect_r.u0]; the second
   reaches its equalizers through the first's pullbacks, and its
   constraint block has 23 constraints on stdlib globals against the
   first's 18 (the same strict one, plus four bounds [eq.u0],
   [eq_ind.u0], [eq_ind_r.u0], [Fin.case0.u0] on the carrier and one,
   [False_rect.u0], on the object universe), so the first is used.

   ** STRENGTHS, STRICTEST FIRST

   Nothing about a colimit object computes.  [GAFT] ends in [Qed] (so
   does [left_adjoint_iso]; [About] reports both opaque), and so the AFT
   coproduct of two groups is not convertible to [Grp_free_product]:
   measured in a scratch file, [Example conv (G H : Grp) : @Coprod Grp
   Grp_Cocartesian_via_GAFT G H = Grp_free_product G H := eq_refl] is
   refused with "cannot unify "G + H" and "Grp_free_product G H"".
   Every agreement is therefore an isomorphism, carried as data:
   [Grp_free_product_iso],
   [Grp_initial_agrees] and [Grp_coequalizer_agrees_normal_closure] are
   [≅], [Grp_coproduct_agrees] is `≈` of functors (a natural isomorphism),
   and the equations about them ([Grp_free_product_iso_inl] and
   [Grp_free_product_iso_inr]) are `≈`.  The meet is `≈` in the subobject
   setoid, which is again an isomorphism of domains.  The two [eq_refl]
   [Example]s are about the words-based instance and about the bottom
   subobject, not about anything the theorem built.

   ** UNIVERSES, MEASURED

   By [About] under [Set Printing Universes], dropping bounds on stdlib
   globals: [Diagonal_Grp_solution_set] takes J : Category@{u u0 u0} and
   D : J ⟶ Grp@{u1 u0} and returns [SolutionSet@{u2 u1 u1 u0}] with
   [u0 <= u2] and [Set < u2] on the index [u2] -- an index of
   [Prop]-valued relations sits strictly above [Set] -- and [Set < u1]
   (Grp's own), but no [Set] bound on the carrier [u0].  [GAFT] itself,
   [GAFT@{cobj dobj h u u0 u1}], takes [SolutionSet@{h dobj cobj h}]:
   the index AT the hom universe [h], which for [Grp] is the carrier.
   [Grp_colim_via_GAFT] takes
   J : Category@{u2 u3 u3} with [u2 <= u3]: J's objects stay free below
   the carrier, which is what [Diagonal_continuous]'s explicit binders buy.
   [Grp_Cocomplete_via_GAFT] is [Cocomplete@{u u0 u u1}] over [Grp@{u1 u}]
   with [Set < u], [u < u1] and [u0 <= u]: the one side condition is
   [Set < carrier], the same as Instance/Grp/FreeAFT.v's
   [free_group_via_GAFT].  It is [GAFT]'s, not the solution set's: the
   index must sit AT the carrier, and it sits above [Set].  Measured in a
   scratch file under [Monomorphic Constraint Set < gu]: at
   J : Category@{Set Set Set} and D : J ⟶ Grp@{gu Set},
   [@Diagonal_Grp_solution_set J D] is accepted, while
   [Grp_colim_via_GAFT@{gu _ _ Set Set _ _} J] is refused with "Universe
   inconsistency. Cannot enforce Set < Set because Set = Set."
   Test/ProbeAlgColimit450.v's N4 pins the refusal, with the solution set
   and [GAFT] applied to every argument but it both accepted at the same
   J as its controls.  The finite-colimit constants add, through
   [FinitelyComplete_HasPullbacks] (Structure/Limit/Finite.v, attributed
   by [About] on that constant), the strict stdlib bound carrier <
   [eq_rect_r.u0]; [Grp_Initial_via_GAFT] does not carry it.

   ** NON-VACUITY

   [Grp_free_product_via_GAFT_nontrivial]: the AFT coproduct of Z/2 with
   itself is not a subsingleton (¬ ∀ a b, a ≈ b), because [inl] is injective
   ([Grp_inl_via_GAFT_injective], from monicity by Instance/Grp.v's
   [Grp_injectivity_is_monic]).  It is stated at Instance/Grp.v's [Z2],
   which #450 also lifted off [Set] in place; before, [Z2] could not meet
   the [Set < carrier] side condition at all.  [Grp_initial_via_GAFT_trivial]
   shows the initial object is the one-element group.

   ** AXIOMS

   Every constant of this file reports "Closed under the global context".

   ** NOT DELIVERED

   No element-level description of any colimit built here: no reduced
   words, no normal form and no word problem, and none of the colimit
   objects computes.  No general coequalizer described as a quotient: the
   normal closure of the image of f · g⁻¹ is still not built, and only the
   pair (f, 0) is compared with an explicit quotient.  No filtered-colimit
   route (Mac Lane's primary argument in §IX.1).  No monadicity.  Riehl's
   presentation of the free product as a coequalizer of free groups
   (§5.6) is not in this file: it is Instance/Grp/Colimit/Presentation.v,
   whose [Grp_free_product_is_coequalizer] is stated at this file's
   coproduct and whose [Grp_free_product_coequalizer_agrees] compares it
   with this file's coequalizers.  Nothing at [Set]-level carriers, no
   [Cocartesian] agreement among it: the solution set itself elaborates
   there, but [GAFT] puts its index at the carrier universe and the index
   sits strictly above [Set] (UNIVERSES, above).  Nothing is registered
   as an [Instance]. *)

(** ** The solution set at a diagram *)

Section DiagonalSolutionSet.

Context {J : Category}.
Context (D : J ⟶ Grp).

(* The generators: the disjoint union of the carriers, with Leibniz
   equality.  Each factor's own `≈` enters through [cc_resp] below. *)
Definition DGen : SetoidObject :=
  {| carrier := { j : obj[J] & carrier (grp_setoid (D j)) };
     is_setoid := eq_Setoid _ |}.

Definition dins (j : J) (a : carrier (grp_setoid (D j))) : FGWord DGen :=
  fg_insert DGen (j; a).

(* A congruence on the free group that makes the insertions a cocone of
   group homomorphisms. *)
Record IsCoconeCong (Rq : FGWord DGen → FGWord DGen → Prop) : Prop := {
  cc_grp  : IsGrpCongruence Rq;
  cc_resp : ∀ j a b, a ≈ b → Rq (dins j a) (dins j b);
  cc_mul  : ∀ j a b, Rq (dins j (grp_mul (D j) a b))
                        (grp_mul (FreeGrpObject DGen) (dins j a) (dins j b));
  cc_nat  : ∀ j k (f : j ~{J}~> k) a,
              Rq (dins k (grp_map (fmap[D] f) a)) (dins j a)
}.

Definition DCongIdx : Type :=
  { Rq : FGWord DGen → FGWord DGen → Prop & IsCoconeCong Rq }.

Definition DQ (i : DCongIdx) : obj[Grp] := QGrp (`1 i) (cc_grp _ (`2 i)).

Definition dq_leg (i : DCongIdx) (j : J) : D j ~{Grp}~> DQ i.
Proof.
  unshelve refine (@Build_GrpHom' (D j) (DQ i)
                     {| morphism := dins j |} _).
  - intros a b Hab; exact (cc_resp _ (`2 i) j a b Hab).
  - intros a b; exact (cc_mul _ (`2 i) j a b).
Defined.

Definition dq_arr (i : DCongIdx) :
  D ~{[J, Grp]}~> fobj[@Diagonal Grp J] (DQ i).
Proof.
  unshelve refine (@Build_Transform' J Grp D (fobj[@Diagonal Grp J] (DQ i))
                     (fun j => dq_leg i j) _).
  intros j k f a; simpl.
  apply (gc_sym _ _ (cc_grp _ (`2 i))).
  exact (cc_nat _ (`2 i) j k f a).
Defined.

(* The covering: the kernel of a cocone's extension to the free group. *)
Section Cover.

Context (c : Grp) (h : D ~{[J, Grp]}~> fobj[@Diagonal Grp J] c).

Definition dflat : DGen ~{Sets}~> Grp_Forget c.
Proof using h.
  unshelve refine {| morphism := fun p => grp_map (transform[h] (`1 p)) (`2 p) |}.
  intros p q Hpq; simpl in Hpq; subst; reflexivity.
Defined.

Lemma dflat_gen (j : J) (a : carrier (grp_setoid (D j))) :
  fg_ev dflat (dins j a) ≈ grp_map (transform[h] j) a.
Proof using h. exact (free_grp_extend_generators DGen c dflat (j; a)). Qed.

(* Transparent on purpose: see the header. *)
Lemma dker_cocone : IsCoconeCong (fg_ker dflat).
Proof using h.
  constructor.
  - exact (fg_ker_is_cong dflat).
  - intros j a b Hab; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    rewrite !dflat_gen; now rewrite Hab.
  - intros j a b; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    unfold fg_ev; rewrite (grp_map_mul (free_grp_extend dflat)).
    fold (fg_ev dflat (dins j a)); fold (fg_ev dflat (dins j b)).
    fold (fg_ev dflat (dins j (grp_mul (D j) a b))).
    rewrite !dflat_gen.
    apply (grp_map_mul (transform[h] j)).
  - intros j k f a; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    rewrite !dflat_gen.
    pose proof (@naturality_sym _ _ _ _ h j k f a) as Hn; simpl in Hn.
    rewrite Hn; reflexivity.
Defined.

Definition dker_idx : DCongIdx := (fg_ker dflat; dker_cocone).

End Cover.

Definition Diagonal_Grp_solution_set : SolutionSet (@Diagonal Grp J) D.
Proof.
  unshelve refine (@Build_SolutionSet Grp ([J, Grp]) (@Diagonal Grp J) D
                     DCongIdx DQ dq_arr _).
  intros c h.
  exists (dker_idx c h).
  exists (fg_ker_med (dflat c h)).
  intros j a; simpl.
  exact (dflat_gen c h j a).
Defined.

End DiagonalSolutionSet.

(** ** Every colimit of groups within the shape discipline *)

Definition Grp_colim_via_GAFT (J : Category) :
  { K : [J, Grp] ⟶ Grp & K ⊣ @Diagonal Grp J } :=
  GAFT (@Diagonal Grp J) Grp_Complete
       (Continuous_PreservesImageLimit Diagonal_continuous)
       (@Diagonal_Grp_solution_set J).

Definition Grp_Cocomplete_via_GAFT : @Cocomplete Grp :=
  fun J F => Diagonal_left_adjoint_HasColimits (projT2 (Grp_colim_via_GAFT J)) F.

(** ** Coproducts, coequalizers and the initial object *)

Definition Grp_FinitelyCocomplete_via_GAFT : @FinitelyCocomplete Grp :=
  Cocomplete_FinitelyCocomplete Grp_Cocomplete_via_GAFT.

Definition Grp_Cocartesian_via_GAFT : @Cocartesian Grp :=
  FinitelyComplete_Cartesian
    (FinitelyCocomplete_FinitelyComplete_op Grp_FinitelyCocomplete_via_GAFT).

Definition Grp_HasCoequalizers_via_GAFT : HasCoequalizers Grp :=
  HasCoequalizers_of_HasEqualizers_op
    (FinitelyComplete_HasEqualizers
       (FinitelyCocomplete_FinitelyComplete_op Grp_FinitelyCocomplete_via_GAFT)).

Definition Grp_Initial_via_GAFT : @Initial Grp :=
  FinitelyCocomplete_Initial Grp_FinitelyCocomplete_via_GAFT.

(** ** Agreement with the constructions already in tree *)

(* The coproduct bifunctors agree up to natural isomorphism: both are left
   adjoint to the diagonal [Grp ⟶ Grp ∏ Grp]. *)
Definition Grp_coproduct_agrees :
  @InternalCoproductFunctor Grp Grp_Cocartesian_via_GAFT
    ≈ @InternalCoproductFunctor Grp Grp_Cocartesian :=
  left_adjoint_iso (Diagonal_Product Grp) _ _
    (@Diagonal_Coproduct_Adjunction Grp Grp_Cocartesian_via_GAFT)
    (@Diagonal_Coproduct_Adjunction Grp Grp_Cocartesian).

(* At one pair of groups: the comparison built from the two copairings,
   which carries injections to injections. *)
Definition Grp_free_product_iso@{u p +} (G H : Grp@{u p}) :
  @Coprod Grp@{u p} Grp_Cocartesian_via_GAFT G H
    ≅ @Coprod Grp@{u p} Grp_Cocartesian G H.
Proof.
  unshelve refine {|
    to   := @merge Grp Grp_Cocartesian_via_GAFT _ _ _
              (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H);
    from := @merge Grp Grp_Cocartesian _ _ _
              (@inl Grp Grp_Cocartesian_via_GAFT G H)
              (@inr Grp Grp_Cocartesian_via_GAFT G H) |}.
  - rewrite <- (@merge_comp Grp Grp_Cocartesian).
    rewrite (@inl_merge Grp Grp_Cocartesian_via_GAFT),
            (@inr_merge Grp Grp_Cocartesian_via_GAFT).
    exact (@merge_inl_inr Grp Grp_Cocartesian G H).
  - rewrite <- (@merge_comp Grp Grp_Cocartesian_via_GAFT).
    rewrite (@inl_merge Grp Grp_Cocartesian),
            (@inr_merge Grp Grp_Cocartesian).
    exact (@merge_inl_inr Grp Grp_Cocartesian_via_GAFT G H).
Defined.

Lemma Grp_free_product_iso_inl@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_iso G H) ∘ @inl Grp Grp_Cocartesian_via_GAFT G H
    ≈ @inl Grp Grp_Cocartesian G H.
Proof. exact (@inl_merge Grp Grp_Cocartesian_via_GAFT _ _ _ _ _). Qed.

Lemma Grp_free_product_iso_inr@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_iso G H) ∘ @inr Grp Grp_Cocartesian_via_GAFT G H
    ≈ @inr Grp Grp_Cocartesian G H.
Proof. exact (@inr_merge Grp Grp_Cocartesian_via_GAFT _ _ _ _ _). Qed.

(* The right-hand object above IS Instance/Grp/Pushout.v's free product. *)
Example Grp_Cocartesian_obj_is_free_product (G H : Grp) :
  @Coprod Grp Grp_Cocartesian G H = Grp_free_product G H := eq_refl.

(* The initial object is the trivial group. *)
Definition Grp_initial_agrees :
  @initial_obj Grp Grp_Initial_via_GAFT ≅ @initial_obj Grp Grp_Initial :=
  initial_unique Grp_Initial_via_GAFT Grp_Initial.

Lemma Grp_initial_via_GAFT_trivial
  (a b : carrier (grp_setoid (@initial_obj Grp Grp_Initial_via_GAFT))) :
  a ≈ b.
Proof.
  pose proof (iso_from_to Grp_initial_agrees a) as Ha.
  pose proof (iso_from_to Grp_initial_agrees b) as Hb.
  simpl in Ha, Hb.
  rewrite <- Ha, <- Hb.
  destruct (grp_map (to Grp_initial_agrees) a),
           (grp_map (to Grp_initial_agrees) b).
  reflexivity.
Qed.

(* The coequalizer of f with the trivial map is the quotient by the normal
   closure of the image of f (Riehl, Example 3.1.25). *)
Definition Grp_coequalizer_agrees_normal_closure {G H : Grp}
  (f : G ~{Grp}~> H) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _ f (@zero_mor Grp Grp_Zero G H))
    ≅ QuotientGrp (NormalClosure f) :=
  coequalizer_unique _ _
    (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _ f
                (@zero_mor Grp Grp_Zero G H))))
    (normal_closure_IsCoequalizer f).

(** ** Mac Lane §V.7 Exercise 1, second half *)

(* Both injections of the free product are monic, split by the copairing
   of the identity with the trivial map. *)
Definition Grp_inl_via_GAFT_Monic (G H : Grp) :
  Monic (@inl Grp Grp_Cocartesian_via_GAFT G H) :=
  @inl_Monic Grp Grp_Zero Grp_Cocartesian_via_GAFT G H.

Definition Grp_inr_via_GAFT_Monic (G H : Grp) :
  Monic (@inr Grp Grp_Cocartesian_via_GAFT G H) :=
  @inr_Monic Grp Grp_Zero Grp_Cocartesian_via_GAFT G H.

Lemma Grp_inl_via_GAFT_injective (G H : Grp) (a b : carrier (grp_setoid G)) :
  grp_map (@inl Grp Grp_Cocartesian_via_GAFT G H) a
    ≈ grp_map (@inl Grp Grp_Cocartesian_via_GAFT G H) b → a ≈ b.
Proof.
  exact (snd (Grp_injectivity_is_monic _) (Grp_inl_via_GAFT_Monic G H) a b).
Qed.

Lemma Grp_inr_via_GAFT_injective (G H : Grp) (a b : carrier (grp_setoid H)) :
  grp_map (@inr Grp Grp_Cocartesian_via_GAFT G H) a
    ≈ grp_map (@inr Grp Grp_Cocartesian_via_GAFT G H) b → a ≈ b.
Proof.
  exact (snd (Grp_injectivity_is_monic _) (Grp_inr_via_GAFT_Monic G H) a b).
Qed.

(* The pullbacks the subobject meet is taken in. *)
Definition Grp_HasPullbacks : HasPullbacks Grp :=
  FinitelyComplete_HasPullbacks (Complete_FinitelyComplete Grp_Complete).

(* The images of the two injections meet in the trivial subgroup. *)
Definition Grp_free_product_meet_trivial (G H : Grp) :
  @sub_meet Grp Grp_HasPullbacks _
     (@sub_inl Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
     (@sub_inr Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
    ≈ @coprod_bot Grp Grp_Zero Grp_Cocartesian_via_GAFT G H :=
  @coproduct_injections_meet_trivial Grp Grp_Zero Grp_Cocartesian_via_GAFT
     Grp_HasPullbacks G H.

Example Grp_free_product_meet_bottom_is_trivial (G H : Grp) :
  sub_dom (@coprod_bot Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
    = Grp_trivial := eq_refl.

(** ** Non-vacuity *)

Example Grp_free_product_via_GAFT_nontrivial :
  (∀ a b : carrier (grp_setoid (@Coprod Grp Grp_Cocartesian_via_GAFT Z2 Z2)),
     a ≈ b) → False.
Proof.
  intro Hall.
  apply Z2_nontrivial.
  apply (Grp_inl_via_GAFT_injective Z2 Z2).
  apply Hall.
Qed.
