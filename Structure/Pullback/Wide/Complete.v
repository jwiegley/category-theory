Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * Wide pullbacks from completeness *)

(* nLab:      https://ncatlab.org/nlab/show/wide+pullback
   nLab:      https://ncatlab.org/nlab/show/complete+category
   nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.2
   (book p. 113, as Structure/Limit/FromProducts.v cites it) builds every
   small limit from products and equalizers, and the intersection of a
   small family of subobjects, which #451's reading of §V.8 (book p. 130)
   needs, is the limit of the family of monos: a wide pullback.  The
   tree had the wide-pullback vocabulary (Structure/Pullback/Wide.v's
   [WidePullback] and [HasWidePullbacks]) and completeness
   (Structure/Complete.v's [Complete]), but no constant passing from the
   second to the first.  This file supplies it: [complete_wide_pullback]
   builds a wide pullback of every family [f : ∀ j, A j ~> z] out of a
   completeness witness, and [Complete_HasWidePullbacks] packages it as the
   class.  mathlib defines [HasWidePullbacks] as [HasLimitsOfShape
   (WidePullbackShape J)] for every [J], so there completeness gives it at
   once; the tree has no wide-cospan shape category, and the construction
   below instead follows the §V.2 recipe, specialised to the wide cospan.

   ** The construction

   The wide pullback of [f] is the equalizer of two maps

       ∏_{j : J} A j  ⇉  ∏_{(i, j) : J × J} z

   whose [(i, j)] components are [f i ∘ π_i] and [f j ∘ π_j].  A map into
   the product equalizes the pair exactly when its components agree after
   [f], which is the commutativity field of [WidePullback], and the
   mediator is the equalizer's descent of the product's tuple.  Both
   products are Structure/Limit/Product.v's [iprod] read off
   [comp _ (DiscreteCat_Functor _)], and maps into them are compared by
   Structure/Limit/FromProducts.v's [pe_iprod_ext] through
   [limit_is_indexed_product]; the equalizer is
   Structure/Limit/Finite.v's [FinitelyComplete_HasEqualizers] applied to
   [Complete_FinitelyComplete comp], so the whole construction stays in the
   Structure layer.  (Adjunction/GAFT.v's [Complete_HasEqualizers] would
   serve too, with a smaller universe block, compared below; it is not
   used, so that nothing here depends on the adjoint-functor development.)

   No point of [J] is needed, and the empty index is handled correctly: at
   [J] empty both products are terminal, the equalizer of the unique pair
   is terminal, and the result agrees with Structure/Pullback/Wide.v's
   [wide_pullback_empty_terminal].

   ** Why not through the wide equalizer

   The shorter route would take the limit of a wide-cospan-shaped diagram,
   or the wide equalizer of Structure/Equalizer/Wide.v.  The tree has no
   wide-cospan shape category, and the wide-equalizer shape is
   Instance/Parallel/Wide.v's [WideParallel@{i p} : Type@{i} →
   Category@{Set i p}], whose object universe is a hand-written [Set].
   Because the category record is not cumulative, applying a [Complete] at
   that shape forces [Complete]'s shape-object universe to [Set]; at the
   regime the adjoint functor theorems use, [Complete@{h h h o}], this is
   refused as "Cannot enforce Set = h" (measured by the #451 scouts).  The
   route through products over [J] and [J × J] has no such pin, and needs
   no pointed section either.  Lifting the pin on [WideParallel] is a
   separate matter and is not attempted here.

   ** Universes, measured

   Read with [Set Printing Universes. About complete_wide_pullback.],
   stdlib bounds omitted:

     complete_wide_pullback@{u u0 u1 u2 u3 u4 u5 u6 u7} :
       ∀ {C : Category@{u u0 u0}}, Complete@{u1 u2 u0 u} →
       ∀ {J : Type@{u3}} {A : J → obj[C]} {z : obj[C]}
         (f : ∀ j : J, A j ~{ C }~> z), WidePullback@{u3 u4 u u0} f
     (* u0 < u5, u0 < u6, u2 < u6, u5 < u7, u <= u6, u0 <= u1, u0 <= u4,
        u1 <= u6, u2 <= u1, u3 <= u1, u3 <= u2, u3 <= u4 *)

   The omitted stdlib bounds are upper bounds by floating global
   universes, and they come from the equalizer bridge: [u1 <=
   Fin.case0.u0], [u1 <= VectorDef.nth.u0] and [u1 <= VectorDef.of_list.u0]
   (the finite presentation of the walking cospan in
   Structure/Limit/Finite.v), [u0 <= EqdepFacts.eq_sigT_sig_eq.u2], and
   [u0, u2 <= Logic_lemmas.equality.u0].  Adjunction/GAFT.v's
   [Complete_HasEqualizers] carries none of them (its block, stdlib
   bounds aside, is [u0 < u1, u0 <= u3, u2 <= u3]; its one stdlib bound
   is [u0 <= False_rect.u0]); they are the price of staying in the
   Structure layer, and they constrain nothing at the two regimes checked,
   [Complete@{h h h o}] with [h < o] and [Sets_Complete].

   The one bound that matters is [u3 <= u2]: the index of the family must
   lie at or below [Complete]'s shape-object universe, because the index
   IS the object type of the discrete shape the product is taken over.
   Nothing ties the index to the object or hom universe of [C].
   [Complete_HasWidePullbacks] instantiates the class's index slot at that
   shape-object universe itself:

     Complete_HasWidePullbacks@{u u0 u1 u2 u3 u4 u5} :
       ∀ {C : Category@{u1 u2 u2}}, Complete@{u0 u u2 u1} →
       HasWidePullbacks@{u u0 u1 u2} C
     (* u < u4, u2 < u3, u2 < u4, u3 < u5, u <= u0, u0 <= u4, u1 <= u4,
        u2 <= u0 *)

   At the adjoint-functor regime, [C : Category@{o h h}] with [h < o] and
   [comp : Complete@{h h h o}], the index therefore lies at [h], the size
   of the hom-sets: the book's small families.  That is exactly what
   Structure/WellPowered.v's intersection theorem needs, and why a
   well-powered category (subobjects indexed at [h]) has intersections of
   classes of subobjects while an arbitrary family indexed by the large
   type of subobjects is refused.

   ** Non-vacuity

   [complete_wide_pullback] is consumed by Structure/WellPowered.v's
   [complete_intersection], which that file instantiates unconditionally
   at an indiscrete category ([Indiscrete_types_has_intersections]).  Any
   concrete [Complete] instance of the tree feeds the class form: in
   scratch files, [Complete_HasWidePullbacks Sets_Complete] (a second
   source of wide pullbacks at [Sets], next to Instance/Sets/
   SubobjectLattice.v's direct [Sets_HasWidePullbacks], and at the same
   universes) and [Complete_HasWidePullbacks (SVariety_Complete E)] are
   accepted, the latter reported closed under the global context.

   ** Not delivered

   No limit presentation of the wide pullback over a wide-cospan shape, and
   no comparison between the construction here and the direct instances
   [Sets_HasWidePullbacks] and [RMod_HasWidePullbacks] beyond what
   [wide_pullback_unique] gives any two wide pullbacks of the same family.
   No wide pushouts from cocompleteness are stated separately: they are the
   construction read at [C^op] through Construction/Product/Limit.v's
   [Complete_op_of_Cocomplete], which is how Structure/WellPowered.v uses
   them. *)

Section CompleteWide.

Context {C : Category}.
Context (comp : @Complete C).

Section AtFamily.

Context {J : Type} {A : J → C} {z : C} (f : ∀ j, A j ~> z).

(* The product of the family, and its projections. *)
Definition cwp_P_lim := comp _ (DiscreteCat_Functor A).
Definition cwp_P : C := iprod A cwp_P_lim.
Definition cwp_pi (j : J) : cwp_P ~> A j := iprod_proj A cwp_P_lim j.

(* The [J × J]-fold power of the codomain. *)
Definition cwp_Z_lim := comp _ (DiscreteCat_Functor (fun _ : J * J => z)).
Definition cwp_Z : C := iprod (fun _ : J * J => z) cwp_Z_lim.
Definition cwp_rho (k : J * J) : cwp_Z ~> z :=
  iprod_proj (fun _ : J * J => z) cwp_Z_lim k.

(* The two maps whose equalizer is the wide pullback. *)
Definition cwp_l : cwp_P ~> cwp_Z :=
  unique_obj (iprod_ump (fun _ : J * J => z) cwp_Z_lim cwp_P
                (fun k => f (fst k) ∘ cwp_pi (fst k))).
Definition cwp_r : cwp_P ~> cwp_Z :=
  unique_obj (iprod_ump (fun _ : J * J => z) cwp_Z_lim cwp_P
                (fun k => f (snd k) ∘ cwp_pi (snd k))).

(* The equalizer, from the Structure layer's finite-limit bridge. *)
Definition cwp_E :=
  @equalizer C (FinitelyComplete_HasEqualizers (Complete_FinitelyComplete comp))
    _ _ cwp_l cwp_r.
Definition cwp_Eobj : C := `1 cwp_E.
Definition cwp_e : cwp_Eobj ~> cwp_P := `1 (`2 cwp_E).
Definition cwp_isE : IsEqualizer cwp_l cwp_r cwp_Eobj cwp_e := `2 (`2 cwp_E).

Lemma cwp_rho_l (k : J * J) : cwp_rho k ∘ cwp_l ≈ f (fst k) ∘ cwp_pi (fst k).
Proof. exact (unique_property (iprod_ump _ cwp_Z_lim cwp_P _) k). Qed.

Lemma cwp_rho_r (k : J * J) : cwp_rho k ∘ cwp_r ≈ f (snd k) ∘ cwp_pi (snd k).
Proof. exact (unique_property (iprod_ump _ cwp_Z_lim cwp_P _) k). Qed.

Definition complete_wide_pullback : WidePullback f.
Proof using comp.
  unshelve refine {| WPull := cwp_Eobj;
                     wide_pullback_proj := fun j => cwp_pi j ∘ cwp_e |}.
  - intros i j.
    rewrite !comp_assoc.
    rewrite <- (cwp_rho_l (i, j)), <- (cwp_rho_r (i, j)).
    simpl.
    rewrite <- !comp_assoc.
    now rewrite (fork_eq cwp_isE).
  - intros Q q Hq.
    pose (t := iprod_ump A cwp_P_lim Q q).
    assert (Ht : cwp_l ∘ unique_obj t ≈ cwp_r ∘ unique_obj t).
    { apply (pe_iprod_ext (limit_is_indexed_product _ _)); intro k.
      rewrite !comp_assoc.
      change (iprod_proj (fun _ : J * J => z) cwp_Z_lim k) with (cwp_rho k).
      rewrite cwp_rho_l, cwp_rho_r.
      rewrite <- !comp_assoc.
      change (iprod_proj A cwp_P_lim) with cwp_pi in (type of t).
      rewrite (unique_property t (fst k)), (unique_property t (snd k)).
      exact (Hq (fst k) (snd k)). }
    pose (u := eq_desc cwp_isE (unique_obj t) Ht).
    unshelve eapply Build_Unique.
    + exact (unique_obj u).
    + intro j. rewrite <- comp_assoc.
      rewrite (unique_property u).
      exact (unique_property t j).
    + intros v Hv.
      apply (uniqueness u).
      apply (pe_iprod_ext (limit_is_indexed_product _ _)); intro j.
      rewrite comp_assoc.
      change (iprod_proj A cwp_P_lim j) with (cwp_pi j).
      rewrite (Hv j).
      symmetry; exact (unique_property t j).
Defined.

End AtFamily.

End CompleteWide.

(* The class, with its index slot at [Complete]'s shape-object universe. *)
Definition Complete_HasWidePullbacks {C : Category} (comp : @Complete C) :
  HasWidePullbacks C :=
  {| wide_pullback := fun I A z f => complete_wide_pullback comp f |}.
