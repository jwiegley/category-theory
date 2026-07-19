Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Discrete.

Set Universe Polymorphism.

Generalizable All Variables.

(** * Freyd's General Adjoint Functor Theorem *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   The General Adjoint Functor Theorem (GAFT, Freyd; Mac Lane CWM V.6) gives
   sufficient conditions for a functor [U : C ⟶ D] to have a left adjoint.  It
   has two ingredients, one universal-arrow-shaped and one solution-set-shaped:

     - if every object [d : D] has a *universal arrow* into [U] — packaged
       here as an initial object of the comma category [=(d) ↓ U] — then those
       arrows assemble into a left adjoint.  This is [GAFT_from_initials], and
       it is immediate from [Theory/Universal/Arrow.v]
       ([AdjunctionFromUniversalArrows]).

     - Freyd's theorem then *manufactures* those initial objects from a
       completeness hypothesis on [C], a limit-preservation hypothesis on [U],
       and a *solution set* at each [d].  A solution set is a small family of
       arrows [d ~> U (sol_obj i)] through which every [d ~> U c] factors; it
       is exactly a *weakly* initial family in [=(d) ↓ U].  Comma completeness
       ([Construction/Comma/Limit.v]) plus the passage from a weakly initial
       family to a genuine initial object ([Theory/WeaklyInitial.v]) then
       promote that weakly initial family to an initial object, feeding
       [GAFT_from_initials].

   VARIANCE.  [Theory/Universal/Arrow.v] states its universal-arrow adjunction
   for a functor [U0 : D0 ⟶ C0] and produces a left adjoint [C0 ⟶ D0].  We
   instantiate it with [C0 := D], [D0 := C], [U0 := U], so that [=(c) ↓ U0]
   with [c : C0 = D] is our [=(d) ↓ U] and the induced left adjoint is
   [D ⟶ C], exactly as required by the packaging [{ F : D ⟶ C & F ⊣ U }].

   HYPOTHESIS FORM (donor-signature deviation, recorded honestly).  The
   operative preservation hypothesis of [GAFT] is [PreservesImageLimit U] from
   [Construction/Comma/Limit.v], the cone-level statement that [U] carries a
   limit cone of any diagram to a limit cone (the image cone
   [(U L, fmap[U] π_•)] is universal).  This is the mathematically correct
   reading of "U preserves limits", and it is precisely what
   [Comma_Complete] consumes.  The apex-only class [PreservesAllLimits] of
   [Structure/Limit/Preservation.v] records only that the apex object [U L]
   carries *some* limit structure, whose legs need not be the image legs; as
   [Construction/Comma/Limit.v] documents in detail, two cone structures on the
   same apex can differ by a non-invertible endomorphism, so apex-only
   preservation does not by itself make the image cone universal.  Taking the
   cone-level [PreservesImageLimit] is therefore a strengthening to the correct
   notion of preservation — a leaner, honest hypothesis — and never a weakening
   of the conclusion, which remains a full left adjoint [F ⊣ U].  This mirrors
   the identical, documented choice made by [Comma_Complete] itself. *)

(* The converse of continuity: provenance, obstruction, and use

   nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Book:  Freyd, "Abelian Categories: An Introduction to the Theory of
          Functors", Harper & Row 1964 (TAC Reprints 3, 2003)
   Paper: Kan, "Adjoint Functors", Trans. AMS 87(2), 1958
   Paper: Porst, "The history of the General Adjoint Functor Theorem",
          arXiv:2310.19528, 2023
   Post:  Milewski, "Freyd's Adjoint Functor Theorem", 2020

   The theorem answers one question: which limit-preserving functors are
   right adjoints.  That a right adjoint preserves limits is elementary, and
   is proven in-tree as [rapl_is_alimit] of Adjunction/Continuity.v (RAPL);
   [GAFT] answers the converse: sufficient conditions under which a
   continuous [U] is a right adjoint, exhibited here as the left adjoint
   [F ⊣ U].

   Adjoint functors were a recent notion when the theorem was proved.  Kan
   introduced them (Kan, "Adjoint Functors", Trans. AMS 87(2), 1958), and
   Mac Lane records that Bourbaki had just missed the concept in a 1948
   draft appendix.  Both the general and the special adjoint functor
   theorems then first appeared in print in Freyd's 1964 book, where — as
   nLab records — they sit in the exercise section of chapter 3 rather than
   among the headline results.  Porst has argued that the substance of the
   result reaches back further still, into the universal-mapping-problem
   tradition of the late 1940s (Porst, arXiv 2023) — a claim about
   provenance, not settled consensus.  Freyd and Scedrov later renamed the
   solution-set condition pre-adjointness (1990).

   The hypotheses repair a genuine size obstruction rather than decorate the
   statement.  Building the adjoint pointwise as a limit over the comma
   category breaks down because that category is large, and a large category
   need not have large limits; indeed a small complete category is a
   preorder (Freyd), so completeness cannot be exploited naively at large
   size.  The [SolutionSet] record is the minimal patch — a small family
   [sol_arr] through which every [d ~> U c] factors, that is, a weakly
   initial family in the comma [=(d) ↓ U].  Freyd's repair runs in two
   stages, both carried out by [initial_from_weakly_initial] of
   Theory/WeaklyInitial.v: take the [iprod] of the family to a weakly
   initial object, then equalize all of its endomorphisms to sharpen weak
   initiality into genuine initiality.  In [GAFT] those products and
   equalizers come from [Comma_Complete], and [wif_of_sols] is the passage
   from a [SolutionSet] to the [WeaklyInitialFamily] consumed there.

   The special adjoint functor theorem trades the explicit solution set for
   structural smallness of the domain: Adjunction/SAFT.v manufactures a
   [SolutionSet] from well-poweredness ([SubobjectIndex]) and a cogenerating
   family ([Cogenerator]), so [SAFT] never asks the caller to supply one.
   Continuity by itself does not suffice, and the boundary is sharp: nLab
   records a counterexample that Joyal attributes to Mac Lane, a product
   of representables over the simple groups that is continuous yet not
   representable.  The modern sharpening (Adámek and Rosický) makes it a
   biconditional between locally presentable categories, where a functor
   has a left adjoint exactly when it is accessible and preserves small
   limits.

   The reach is broad.  When [U] forgets structure its left adjoint is the
   free construction, which Milewski glosses as freely ad-libbing the
   forgotten information.  A full subcategory is reflective exactly when its
   inclusion has a left adjoint, so the theorem is the standard tool for
   producing reflectors (Construction/Reflective.v,
   Construction/Localization.v).  Limits, colimits and Kan extensions are
   themselves adjoints, so it yields existence criteria for them; and in the
   order-theoretic degenerate case it is the adjoint functor theorem for
   preorders, the Galois-connection setting that Instance/Poset.v cites
   [SolutionSet] to explain.  Adjunction/GAFT/Examples.v runs
   [GAFT_from_initials] end to end to recover the diagonal adjoint Δ ⊣ (×),
   proving the produced functor naturally isomorphic to Δ
   ([diagonal_product_via_gaft_is_diagonal]).

   The computational reading is the generate-then-constrain recipe familiar
   from free-algebra constructions.  Milewski reads the solution set as a
   way to cut a large comma category down to a manageable size, and the
   construction holographically: gather all information about an object
   through the morphisms out of it, ship that record back through [U], and
   reconstruct the best preimage as a limit.  The product-then-equalizer
   shape tuples the small family and carves it by imposing every self-map;
   Milewski notes an unexpected connection to defunctionalization, the
   Reynolds program transformation that motivated the account. *)

(** ** Solution sets *)

(* A solution set at [d : D] for [U : C ⟶ D]: a small [Type] of indices, a
   family of objects [sol_obj i : C] with arrows [sol_arr i : d ~> U (sol_obj i)],
   such that every [h : d ~> U c] factors through some member,
   [fmap[U] t ∘ sol_arr i ≈ h].  No uniqueness of the factorization is asked —
   this is a *weakly* initial family in the comma category [=(d) ↓ U]. *)
Record SolutionSet {C D : Category} (U : C ⟶ D) (d : D) := {
  sol_index : Type;
  sol_obj : sol_index -> C;
  sol_arr : forall i, d ~> U (sol_obj i);
  sol_covers {c} (h : d ~> U c) :
    { i : sol_index & { t : sol_obj i ~> c & fmap[U] t ∘ sol_arr i ≈ h } }
}.

Arguments sol_index {C D U d} _.
Arguments sol_obj {C D U d} _ _.
Arguments sol_arr {C D U d} _ _.
Arguments sol_covers {C D U d} _ {c} _.

(** ** The universal-arrow half: initial objects give a left adjoint *)

(* If every [d : D] has an initial object in the comma category [=(d) ↓ U],
   then [U] has a left adjoint.  Immediate from [Theory/Universal/Arrow.v]:
   each such initial object is a [UniversalArrow d U], and a universal arrow at
   every object assembles into the left adjoint by
   [AdjunctionFromUniversalArrows], instantiated with the codomain [D] on the
   left (see the VARIANCE note above). *)
Theorem GAFT_from_initials {C D : Category} (U : C ⟶ D)
  (H : forall d : D, @Initial (=(d) ↓ U)) : { F : D ⟶ C & F ⊣ U }.
Proof.
  pose (Hu := fun d : D => {| arrow_initial := H d |} : @UniversalArrow D C d U).
  exists (@LeftAdjointFunctorFromUniversalArrows D C U Hu).
  exact (@AdjunctionFromUniversalArrows D C U Hu).
Qed.

(** ** Auxiliary bridges from completeness *)

(* Every complete category has all binary equalizers: take the limit of the
   walking parallel pair [APair f g] and read it, at its apex, as an elementary
   equalizer via [equalizer_is_equalizer] of [Structure/Equalizer/Fork.v]. *)
Definition Complete_HasEqualizers {A : Category} (HA : @Complete A) :
  HasEqualizers A.
Proof.
  constructor.
  intros x y f g.
  pose (L := HA Parallel (APair f g)).
  eexists.
  eexists.
  exact (equalizer_is_equalizer f g L).
Defined.

(* A solution set at [d] is a weakly initial family in the comma [=(d) ↓ U]:
   the family members are the comma objects [(sol_obj i, sol_arr i)], and the
   covering arrow for any comma object [(c, h)] is the [U]-factorization
   [(sol_obj i, t)] of [h] supplied by [sol_covers], upgraded to a comma
   morphism (its commuting triangle is exactly the factorization equation, the
   left leg [fmap[=(d)] _] collapsing to [id[d]]). *)
Definition wif_of_sols {C D : Category} (U : C ⟶ D) (d : D)
  (S : SolutionSet U d) : WeaklyInitialFamily (=(d) ↓ U).
Proof.
  destruct S as [idx obj arr cov].
  unshelve refine (@Build_WeaklyInitialFamily (=(d) ↓ U) idx
                     (fun i => ((ttt, obj i); arr i)) _).
  intro Y.
  destruct Y as [[oY cY] hY].
  destruct (cov cY hY) as [i [t e]].
  exists i.
  unshelve refine ((ttt, t); _).
  change (hY ∘ id[d] ≈ fmap[U] t ∘ arr i).
  rewrite id_right.
  symmetry; exact e.
Defined.

(** ** Freyd's General Adjoint Functor Theorem *)

(* Freyd's GAFT.  [C] complete, [U] preserving (image) limits, and a solution
   set at every [d], yield a left adjoint [F ⊣ U].  For each [d]:

     - comma completeness [Comma_Complete] makes [=(d) ↓ U] complete;
     - the solution set becomes a weakly initial family [wif_of_sols];
     - the two products (over the solution-set index, and over the
       endomorphisms of that product) and the equalizers demanded by
       [initial_from_weakly_initial] are drawn from that comma completeness;
     - [initial_from_weakly_initial] then yields an initial object of
       [=(d) ↓ U], fed to [GAFT_from_initials].

   See the header for why the preservation hypothesis is the cone-level
   [PreservesImageLimit] rather than the apex-only [PreservesAllLimits]. *)
Theorem GAFT {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (cont : @PreservesImageLimit C D U)
  (sols : forall d : D, SolutionSet U d) : { F : D ⟶ C & F ⊣ U }.
Proof.
  apply GAFT_from_initials.
  intro d.
  pose (HCat := @Comma_Complete C D U d cont comp).
  pose (W := wif_of_sols U d (sols d)).
  pose (P := HCat _ (DiscreteCat_Functor (wif_obj W))).
  refine (@initial_from_weakly_initial (=(d) ↓ U) W P
            (HCat _ (DiscreteCat_Functor
                       (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
                        => iprod (wif_obj W) P)))
            (Complete_HasEqualizers HCat)).
Qed.
