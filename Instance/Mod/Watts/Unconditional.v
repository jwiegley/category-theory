(** * Watt's theorem with no hypothesis: every additive T : (R-Mod)^op ⟶ Ab
      carrying colimits to limits is Hom(−, A) *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed. (GTM 5), §V.8, printed p. 131 (PDF p. 140; ledger item
              `maclane:V.8:thm-watt`, issue #454), read from the printed
              page: "any contravariant additive functor T on R-Mod to Ab
              which takes small colimits to limits is representable by a
              group isomorphism T ≅ hom_R(−, C) for some R-module C".  (The
              in-repo catalog, doc/plan/books/maclane/inventory/V.json,
              summarises it in its own words, "every contravariant
              additive functor T on R-Mod to Ab which carries small
              colimits to limits is representable: T is naturally
              isomorphic to hom_R(-, C) for some R-module C".)
   Book:      Mac Lane, ibid., §V.6 Theorem 3 and Definition 3 — the
              representability theorem with its element-wise solution set
              condition, Adjunction/Representability/Sets.v, which is the
              theorem actually applied here.
   nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab:      https://ncatlab.org/nlab/show/representable+functor

   A DEVIATION, STATED PLAINLY.  The issue asks for Watt's theorem
   "derived from SAFT", and its Reviewer line reads "the representability
   must be derived from SAFT plus additivity".  This file does NOT use the
   special adjoint functor theorem.  It applies the GENERAL one, in the
   form of Mac Lane's §V.6 Theorem 3 ([representability_theorem], whose
   proof is Adjunction/GAFT.v's comma-initial step), to an explicit
   element-wise solution set, and the covering step of that solution set
   is the Eilenberg–Watts construction read in solution-set form.  The
   reason is measured, not preferred: SAFT at (R-Mod)^op asks for the
   co-well-poweredness of R-Mod, which the tree has only under the
   hypothesis [Untruncate] (Instance/Mod/WellPowered.v's
   [RMod_CoWellPowered_untruncate]; that header quotes the refusals
   without it), and its cogenerator [RModop_Cogenerator] exists only at
   [RingObject@{c c c}].  The route here needs neither, so it delivers the
   book's contravariant statement with NO hypothesis beyond the book's
   own two.  "Plus additivity" is kept verbatim: the Ab-level conclusion
   is Functor/Representable/Additive.v's [watt_ab_iso].  #454's
   SAFT-derived conditional form is not replaced by this file.

   THE HEADLINE, AND THE SAFT ROUTE.  For the book's contravariant
   statement this file is #454's headline.  Instance/Mod/Watts.v keeps
   Mac Lane's own route, the one the Reviewer line names, as
   [watts_theorem]: SAFT at (RMod R)^op, under the hypothesis
   [Untruncate] and with the ring at [RingObject@{c c c}].  Its statement
   is a special case of [watts_theorem_unconditional]'s, and Watts.v,
   which imports this file, derives it from this theorem in its section
   6 ([watts_theorem_via_unconditional], with [Untruncate] carried and not
   consumed); the SAFT route is kept for its fidelity to the Reviewer
   line, not for its strength.  Of Watts.v's constants, this theorem
   subsumes three.  The first is [watts_theorem], in tree as just said.
   The second is [watts_theorem_coext]: its statement elaborates verbatim
   from [watts_theorem_unconditional] at [HomAbForget R A], closed and
   with no universe equation.  The third is [watts_theorem_sets], but
   only at the instance whose second [Representable] universe is RMod's
   object universe, since [RModop_continuous_representable] returns a
   [Representable@{u o s o c}]; the same elaboration reads back
   [o = rt].  (Both measured in a scratch file importing Watts.v, with
   each statement copied from Watts.v and [U] left unused.)
   [watts_theorem_coext_obj] and [watts_theorem_coext_obj_2a] have
   unconditional counterparts, Watts.v's [watts_unconditional_coext] and
   [watts_unconditional_coext_2a], which identify the module THIS theorem
   returns.  Not subsumed: [watts_theorem_adjoint], the book's left
   adjoint of T, which only SAFT builds here, and [watts_theorem_Fz], the
   comparison with it; the readbacks [watts_theorem_obj] and
   [watts_theorem_to_at], which are about the SAFT object; and the
   covariant Exercise 3 family ([watts_ex3], [watts_ex3_sets],
   [watts_ex3_QZ], [watts_ex3_QZ_cogenerator], [watts_ex3_forget],
   [watts_ex3_forget_obj]).  Watts.v's other constants
   ([RMod_Forget_Ab_additive], [RMod_Forget_equiv], [watt_at_forget],
   [HomAbForget], [HomAbForget_additive], [HomAbForget_continuous],
   [coext_representable], [Ab_Forget_Id_equiv], [ab_hom_Z_iso]) carry no
   hypothesis to remove.

   WHAT IS CONSUMED.  Adjunction/Representability/Sets.v's
   [representability_theorem] and [ElementSolutionSet];
   Instance/Mod/Colimit.v's [RMod_Cocomplete_via_GAFT], read in the
   opposite by Construction/Product/Limit.v's [Complete_op_of_Cocomplete];
   Instance/Mod/Free.v's [FreeModObject], [fv_gen] and [fv_extend];
   Instance/Mod/WellPowered.v's [PSubmodule], [psm_sub] and [pker];
   Instance/Mod/Quotient.v's [QuotientMod] and [mquot_med];
   Instance/Discrete.v's [DiscreteCat_Functor];
   Functor/Representable/Additive.v's [CoHomAb], [HomAb_additive],
   [HomAb_representable], [CoHomAb_continuous], [LocallyPropositional_op],
   [watt_ab_iso] and [wab_obj]; Adjunction/Additive.v's [AbEnriched_op];
   Instance/Ab/Limit.v's [Ab_Forget_creates_continuous];
   Structure/Limit/Preservation.v's [continuous_compose] and [FCone];
   Construction/Comma/Creation.v's [Continuous_PreservesImageLimit];
   Functor/Hom/Continuous.v's [hom_continuous_at].

   WHAT IS BUILT.

     - [MultiSpan X], a thin shape: nodes [ms_mod], [ms_free] and
       [ms_gen m] for m : X, with one arrow from each [ms_gen m] to each of
       the other two; [ms_diagram] draws it in any category.
     - [sets_limit_point]: a compatible family of elements over a limiting
       cone of setoids is the image of one element of the apex (the
       mediator out of the singleton cone, at its point).
     - [ew_Gen], the free module on one generator [ew_g0], and [ew_ev m],
       the homomorphism sending [ew_g0] to m ([ew_ev_g0] at [eq_refl]).
     - **[RModop_esols K contK : ElementSolutionSet K]** for every
       continuous K : (RMod R)^op ⟶ Sets, and
       **[RModop_continuous_representable K contK : Representable K]**.
     - **[watts_theorem_unconditional T AF contT]**: for T : (RMod R)^op ⟶
       Ab additive and continuous, a module A with [CoHomAb A ≅ T] in the
       functor category, i.e. T ≅ Hom_R(−, A) as Ab-valued functors.
     - The witnesses of NON-VACUITY below.  The continuity of the
       Ab-valued hom functors, [HomAb_continuous] and
       [CoHomAb_continuous], is not built here but consumed from
       Functor/Representable/Additive.v.

   THE ARGUMENT.  Fix a continuous K : (R-Mod)^op ⟶ Sets.  Let Cop be the
   coproduct of copies of [ew_Gen], one for each element i of K(ew_Gen),
   with injections inj_i ([ew_Cop], [ew_inj]); it is ONE module, fixed
   once K is.  K carries it to a product, so the tautological family
   i ↦ i is the image of one y0 in K(Cop) ([ew_y0_leg]).  Now take any
   module M and any x in K(M).  Put a_m := K(ev_m)(x) in K(ew_Gen) and let
   P be the colimit of the multi-span M ← ew_Gen → Cop, drawn once for
   each m, by ev_m and inj_{a_m}.  Its legs identify inj_{a_m}(g0) with m
   ([ew_key]).  K carries P to a limit, and (x, y0, (a_m)_m) is a
   compatible family over it (by the definition of a_m and by y0's), so
   it is the image of one e in K(P) ([ew_e_leg]).  The member of the
   solution set is Q := Cop / N, with N the [Prop] kernel of the leg
   Cop → P ([ew_N], a [PSubmodule] of the fixed Cop, and [ew_Q]).  The map
   t : M → Q is m ↦ [inj_{a_m}(g0)] ([ew_t_at] at [eq_refl]).  NO CHOICE is
   made anywhere: the generator of each copy is an explicit element, where
   the SAFT route must invert an epi.  The quotient maps into P by
   [mquot_med] ([ew_k], with k ∘ t ≈ the leg at M, [ew_k_t]), so
   K(t)(K(k)(e)) ≈ x ([ew_t_covers]).  The index, a [PSubmodule] of Cop
   paired with an element of K at the quotient ([ew_WIdx]), sits at the
   carrier universe, which is where [representability_theorem] pins it.
   The route is GAFT over a [Prop]-indexed family of quotients of one
   free module, with two choices made against the evident ones.  The
   free module on one generator stands in for the ring, which avoids
   [Ring_RMod]'s collapse of the ring's universes.  And one multi-span
   colimit replaces the pushout of the canonical free presentation
   F(U M) → M, so K is never evaluated at F(U M) and no joint
   monicity is needed.  Additivity is not used for [RModop_esols]; it
   enters only through [watt_ab_iso].

   STRENGTHS, strict first.  At [eq_refl]: [ew_ev_g0] (evaluation at the
   generator), [ew_t_at] (the covering map on the nose) and
   [watts_theorem_unconditional_obj] (the representing module IS the
   object [representability_theorem] produces for [Ab_Forget ◯ T]); the
   two components of the isomorphism ARE the representation's, by
   Functor/Representable/Additive.v's [watt_ab_iso_to_at] and
   [watt_ab_iso_from_at].  Up to ≈: the covering ([ew_t_covers]) and the
   natural isomorphism, componentwise in the functor category.  Up to ≅:
   the witnesses' identification of the module found with the expected
   one.  Flip census, each [Defined] turned to [Qed] one at a time in a
   copy of the whole file: 12 [Defined] (counted by token outside
   comments), of which six are LOAD-BEARING.  [ms_fmap] stops
   [ms_diagram]'s first obligation, [ew_efam] stops [ew_e_ex]'s coherence
   case, [ew_k] stops [ew_k_t], [ew_ev] stops [ew_ev_g0], [ew_t] stops
   [ew_t_at], and [watts_theorem_unconditional] stops
   [watts_theorem_unconditional_obj].  Six recompile as [Qed]: [ms_id],
   [ms_comp], [sets_limit_point], [ew_y0_ex], [ew_e_ex] and
   [RModop_esols].  They are kept [Defined] because they produce data.

   UNIVERSES, measured by [About] under [Set Printing Universes], stdlib
   bounds omitted.

     watts_theorem_unconditional@{a c p o x b s …} :
       ∀ {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c}),
       AdditiveFunctor@{o c b} T → ContinuousFunctor@{u u o c b c c b o s} T
       → { A & CoHomAb@{o c b} (RMod_AbEnriched@{x o a p c} R) A ≅ T }
       (* Set < c, Set < o, Set < b, c < o, c < x, c < b, c < s, c <= a,
          p <= a, a <= o, … — no equation *)

     RModop_continuous_representable@{a c p o x s …} :
       ∀ {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s}),
       ContinuousFunctor@{u u o c s c c s o s} K → Representable K
       (* Set < c, Set < o, c < o, c < x, c < s, … — no equation *)

   The ring keeps its three universes APART.  The SAFT route's
   [RModop_Cogenerator] is at [RingObject@{c c c}], and here nothing
   identifies them: [watts_unconditional_at_Z] instantiates the theorem
   at [Int_Ring@{c p a}] with the three distinct.  [Set < c] is GENUINE:
   deleted from [RModop_continuous_representable]'s binder in a copy of
   the whole file, it is re-inferred.  Deleted from the section's
   [Constraint], it is re-added per constant, first at [ew_CC] (the
   cocompleteness, Instance/Mod/Colimit.v's [Set < c]), and not at
   [ew_Idx] or [ew_CopD].  [PSubmodule]'s sort, [Type@{max(Set+1,m3)}] by
   its [About], would need it again for [ew_WIdx : Type@{c}].  So ℤ with
   its carrier at [Set] is excluded, and ℤ above [Set] is not.
   Test/ProbeWatts454.v pins this: its N24 refuses
   [watts_unconditional_at_Z] at a module of [RMod@{o x Set Set Set}
   Int_Ring@{Set Set Set}], and its N25 refuses the theorem itself at
   [RingObject@{Set Set Set}], beside the controls [p454_unc_Z_ccc] and
   [p454_unc_Z_apart] (ℤ above [Set], its universes collapsed and apart),
   [p454_rmod_at_set] (the category of ℤ-modules at a [Set] carrier is
   formed, so the refusals are the theorem's) and [p454_unc_apart] (a
   ring above [Set] with its three universes strictly apart); its
   [p454_unc_x_below_s] and [p454_unc_s_below_x] accept the theorem with
   x and s apart in both orders.  The only universe equations in
   the module ([About] on all of its 67 names)
   are c = u2 and c = u4 on the continuity hypothesis's own instance: its
   shape-object slot and a universe of its [IsLimitCone]s.  They are
   carried by [RModop_esols] and by the nine section constants that use
   the hypothesis, and they sit at the carrier because the hypothesis is
   used at [MultiSpan@{c}] and [DiscreteCat@{c c c}], the shape universe
   [representability_theorem] fixes.  The two headlines and the
   witnesses carry none.  Three auxiliary universes are pinned by name in
   the covering section: w for [DiscreteCat_Functor] and [ms_diagram],
   and w0, w1 for [RMod_Cocomplete_via_GAFT].  Without them, measured in
   copies of the whole file, [ew_P] carried universes of its own.  Its
   first was instantiated at the continuity hypothesis's last slot inside
   [ew_e] and at x inside [ew_k], and their meeting at [ew_eQ] identified
   RMod's second universe x with that slot, which
   [representability_theorem] identifies with the target's s.  No single
   pin removed the equation; the three together do.  The statement's
   [ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T] names that last slot for
   the same reason: left flexible, it was set to x, and [About] read back
   x = s until it was named.

   NON-VACUITY.  Functor/Representable/Additive.v's [CoHomAb_continuous]
   proves the contravariant Ab-valued hom functor continuous for every
   locally propositional Ab-enriched category.  So T := [CoHomAb A]
   meets both premises for EVERY ring and EVERY module A, and
   [watts_unconditional_CoHomAb_obj] shows that the module the theorem
   returns is isomorphic to A ([repr_unique_iso] against
   [HomAb_representable]).  [RModop_hom_representable_obj] is the same at
   the set-valued level, for the plain hom-functor.  At a concrete ring,
   [watts_unconditional_at_Z] instantiates all of it at ℤ.  These three
   feed the theorem a hom functor, whose representation is known in
   advance.  A witness that is not one is in Instance/Mod/Watts.v, which
   imports this file: its section 6 applies the theorem at
   [HomAbForget R A], M ↦ Hom_Ab(U M, A) for an abelian group A, whose
   continuity comes from the coextension adjunction rather than from a
   hom functor of RMod R.  [watts_unconditional_coext] identifies the
   module returned with [CoextObj R A] ([repr_unique_iso] against
   [coext_representable]), and [watts_unconditional_coext_2a] with
   Exercise 2(a)'s hom_ℤ(R, A).  Neither needs [Untruncate]; both are at
   [RingObject@{c c c}], which [CoextObj] imposes (Instance/Mod/
   Coextension.v).

   THE CONDITIONS, plainly.  T is additive; this is used only by the Ab
   upgrade.  T is continuous in the cone sense ([ContinuousFunctor]) at
   the shapes whose objects sit at the carrier universe.  The shape
   discipline is the one [Complete] and [representability_theorem]
   impose, so every colimit of modules over such a shape goes to a limit
   of groups; that is the book's "takes small colimits to limits".
   Finally, [Set < c].  No
   [Untruncate], no cogenerator, no co-well-poweredness, no choice and no
   axiom: every constant of this module is "Closed under the global
   context".

   SIZE.  374 non-blank lines of code once comments are stripped,
   including the 33 [Require]s.

   NOT DELIVERED.  Exercise 3 (the covariant form) is not delivered
   unconditionally: Instance/Mod/Watts.v delivers it only over
   [Untruncate] and a cogenerator of R-Mod, through the special adjoint
   functor theorem, whose solution set the cogenerator supplies.  No
   other route to it is attempted, and nothing in tree proves either
   hypothesis necessary.  What is proved classical is the book's ℚ/ℤ
   premise (Instance/Mod/Cogenerator.v's metatheorems), and [RMod R]
   well-powered at the pin without [Untruncate] is neither built nor
   refuted (Instance/Mod/WellPowered.v).  The representing module is not
   identified with T(R), or with T(ew_Gen), carrying the Eilenberg–Watts
   action.  It is the object the representability theorem produces, and
   only [repr_unique_iso] compares it with anything.  The module has no
   naturality in T and no functoriality of T ↦ A.  The additivity
   premise [AF] is redundant in principle and is not eliminated: a
   functor between additive categories that preserves finite products
   is additive, and a continuous T : (R-Mod)^op → Ab carries the zero
   module and binary direct sums, which are colimits of modules, to a
   terminal group and to products.  The statement keeps it because the
   book states it; that argument is not formalised here.  No [Instance]
   is registered.

   COQ 8.19 AND 8.20.  A dependency closure of 250 files, containing
   the seven development files #454 adds, this one among them, was
   built by [coq_makefile] with the nix-store Coq 8.19.2 and 8.20.1 and
   Equations 1.3: make rc=0 on each.  There [Print Assumptions] reports
   all 132 constants of Functor/Representable/Additive.v, this file and
   Watts.v closed, and the same ten constants carry the same two
   equations as on 9.1.  The copies were taken before a last round of
   comment-only edits; the code is the same modulo comments and
   whitespace, compared file by file.  The same two trees were then
   brought to the later sources, replacing the three files that differed
   from them (this one, Instance/Mod/Watts.v and
   Instance/Mod/Cogenerator.v, each in its header alone), and
   Test/ProbeWatts454.v, which pins this file's [Set] boundary as its N24
   and N25, was added: [coq_makefile] compiled those four files on each,
   make returned 0 on both, and the probe's stripped refutations are
   refused there as its header records.  Those closures are not the
   whole library; the Nix flake's builds of the committed revision are
   the authoritative gate, and docs/INDEX.md's bullet for this file
   records their result. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.AbCategory.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.WellPowered.
Require Import Category.Instance.Mod.Colimit.
Require Import Category.Functor.Representable.Additive.

Generalizable All Variables.

(** ** 1. The multi-span shape

    Objects: one node [ms_mod], one node [ms_free], and one node [ms_gen m]
    for every [m : X]; besides the identities, exactly one arrow from each
    [ms_gen m] to each of the other two nodes.  Every hom-set has at most
    one element up to the identification of equality proofs, so the
    hom-setoids are the total relation and every category law is [I]. *)

Inductive MSObj@{u} (X : Type@{u}) : Type@{u} :=
  | ms_mod
  | ms_free
  | ms_gen (m : X).

Arguments ms_mod {X}.
Arguments ms_free {X}.
Arguments ms_gen {X} m.

Definition MSHom@{u} {X : Type@{u}} (i j : MSObj@{u} X) : Type@{u} :=
  match i, j with
  | ms_mod, ms_mod => poly_unit@{u}
  | ms_free, ms_free => poly_unit@{u}
  | ms_gen m, ms_gen m' => m = m'
  | ms_gen _, ms_mod => poly_unit@{u}
  | ms_gen _, ms_free => poly_unit@{u}
  | _, _ => False
  end.

Definition ms_id@{u} {X : Type@{u}} (i : MSObj@{u} X) : MSHom i i.
Proof. destruct i; simpl; first [ exact ttt | reflexivity ]. Defined.

Definition ms_comp@{u} {X : Type@{u}} {i j k : MSObj@{u} X} :
  MSHom j k → MSHom i j → MSHom i k.
Proof.
  destruct i, j, k; simpl; intros g f;
    first [ exact ttt | contradiction | exact (eq_trans f g) ].
Defined.

#[local] Obligation Tactic := idtac.

Program Definition MultiSpan@{u} (X : Type@{u}) : Category@{u u u} := {|
  obj := MSObj@{u} X;
  hom := @MSHom@{u} X;
  homset := fun i j => {| equiv := fun _ _ => True |};
  id := @ms_id@{u} X;
  compose := fun i j k => @ms_comp@{u} X i j k
|}.
Solve All Obligations with
  (intros;
   first [ constructor; repeat intro; exact I | repeat intro; exact I ]).

(* A diagram of that shape: two arrows out of [G] for each [m : X]. *)
Section MSDiagram.

Universes o h.

Context {X : Type@{h}} {C : Category@{o h h}} (A B G : C)
        (u : X → G ~{C}~> A) (v : X → G ~{C}~> B).

Definition ms_fobj (i : MSObj@{h} X) : C :=
  match i with ms_mod => A | ms_free => B | ms_gen _ => G end.

Definition ms_fmap {i j : MSObj@{h} X} :
  MSHom i j → ms_fobj i ~{C}~> ms_fobj j.
Proof using u v.
  destruct i as [| | m], j as [| | m']; simpl; intro f;
    first [ exact id | contradiction | exact (u m) | exact (v m) ].
Defined.

Program Definition ms_diagram : MultiSpan@{h} X ⟶ C := {|
  fobj := ms_fobj;
  fmap := fun i j f => ms_fmap f
|}.
Next Obligation.
  intros i j f g _.
  destruct i as [| | m], j as [| | m']; simpl in *;
    first [ contradiction | reflexivity ].
Qed.
Next Obligation.
  intro i; destruct i; simpl; reflexivity.
Qed.
Next Obligation.
  intros i j k f g.
  destruct i as [| | m], j as [| | m'], k as [| | m'']; simpl in *;
    try contradiction; solve [ subst; cat ].
Qed.

End MSDiagram.

(** ** 2. A point of a limit of setoids

    A compatible family of elements over a limiting cone in [Sets] is the
    image of one element of the apex: the mediator out of the singleton
    cone, evaluated at its point. *)

Definition sets_limit_point@{j c s +}
  {J : Category@{j c c}} {F : J ⟶ Sets@{c s}} (N : Cone F) (HN : IsLimitCone N)
  (e : ∀ i : J, carrier (F i))
  (He : ∀ (i i' : J) (f : i ~{J}~> i'), fmap[F] f (e i) ≈ e i') :
  { v : carrier (vertex_obj[N]) & ∀ i : J, cone_leg N i v ≈ e i }.
Proof.
  unshelve epose (P := @Build_Cone J Sets F unit_setoid_object
           (@Build_ACone J Sets unit_setoid_object F
              (fun i => {| morphism := fun _ => e i |}) _)).
  - intros w w' _; reflexivity.
  - intros i i' f w; simpl; exact (He i i' f).
  - destruct (HN P) as [w Hw _].
    exists (w ttt).
    intro i; exact (Hw i ttt).
Defined.

(** ** 3. The free module on one generator, and evaluation at an element *)

Definition ew_Gen@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} : obj[RMod@{o x a p c} R] :=
  @FreeModObject R unit_setoid_object@{c c}.

Definition ew_g0@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} : carrier (cmon_setoid (@ew_Gen@{a c p o x} R)) :=
  @fv_gen R unit_setoid_object@{c c} ttt.

(* [m ↦ the homomorphism sending the generator to m]: the free module's own
   extension, so it needs no choice and computes. *)
Definition ew_ev@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]}
  (m : carrier (cmon_setoid M)) :
  @ew_Gen@{a c p o x} R ~{RMod@{o x a p c} R}~> M.
Proof.
  refine (@fv_extend R unit_setoid_object@{c c} M
            {| morphism := fun _ => m |}).
  intros ? ? ?; reflexivity.
Defined.

Example ew_ev_g0@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]}
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_ev@{a c p o x} m)) ew_g0 = m := eq_refl.

(** ** 4. The element-wise solution set at (R-Mod)^op *)

Section Covering.

(* The ring (a c p), [RMod] (o x), the target of [K] (s), and three
   auxiliary universes pinned by name (w for [DiscreteCat_Functor] and
   [ms_diagram], w0 w1 for [RMod_Cocomplete_via_GAFT]): left free, they
   gave [ew_P] universes of its own, instantiated differently inside
   [ew_e] and inside [ew_k], and [ew_eQ] identified the two (see the
   header, UNIVERSES). *)
Universes a c p o x s w w0 w1.
Constraint Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, c < w,
  o <= w1, x <= w1.

Context {R : RingObject@{a c p}}.
Context (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s}).
Context (contK : ContinuousFunctor K).

#[local] Notation Gen := (@ew_Gen@{a c p o x} R).
#[local] Notation g0 := (@ew_g0@{a c p o x} R).

(* The ONE fixed object: the coproduct of copies of [Gen], one per element
   of [K Gen], taken from [RMod_Cocomplete_via_GAFT]. *)
Definition ew_Idx : Type@{c} := carrier (K Gen).

Definition ew_CopD : DiscreteCat@{c c c} ew_Idx ⟶ RMod@{o x a p c} R :=
  DiscreteCat_Functor@{c c c o c c w} (fun _ => Gen).

Definition ew_CC : @Cocomplete@{c c c o} (RMod@{o x a p c} R) :=
  RMod_Cocomplete_via_GAFT@{a c p o x c w0 w1} R.

Definition ew_CopL : Colimit ew_CopD := ew_CC _ ew_CopD.

Definition ew_Cop : obj[RMod@{o x a p c} R] :=
  vertex_obj[@limit_cone _ _ _ ew_CopL].

Definition ew_inj (i : ew_Idx) : Gen ~{RMod@{o x a p c} R}~> ew_Cop :=
  cone_leg (@limit_cone _ _ _ ew_CopL) i.

(* [K] carries that coproduct to a product, so the tautological family
   [i ↦ i] is the image of one element [ew_y0] of [K ew_Cop]. *)
Definition ew_y0_ex :
  { w : carrier (K ew_Cop)
  & ∀ i : ew_Idx, @fmap _ _ K ew_Cop Gen (ew_inj i) w ≈ i }.
Proof using contK.
  destruct (sets_limit_point (FCone K (@limit_cone _ _ _ ew_CopL))
              (contK _ _ (@limit_cone _ _ _ ew_CopL) (limit_limitcone ew_CopL))
              (fun i : ew_Idx => i)) as [w Hw].
  - intros i i' f; destruct f; simpl.
    exact (@fmap_id _ _ K Gen _).
  - exists w; exact Hw.
Defined.

Definition ew_y0 : carrier (K ew_Cop) := projT1 ew_y0_ex.

Definition ew_y0_leg (i : ew_Idx) :
  @fmap _ _ K ew_Cop Gen (ew_inj i) ew_y0 ≈ i :=
  projT2 ew_y0_ex i.

Section AtElement.

Context (M : obj[RMod@{o x a p c} R]) (x0 : carrier (K M)).

(* For each m, the element [K(ev m)(x0)] of [K Gen] names a copy of [Gen]
   inside [ew_Cop]. *)
Definition ew_am (m : carrier (cmon_setoid M)) : ew_Idx :=
  @fmap _ _ K M Gen (ew_ev m) x0.

(* The diagram M ← Gen → ew_Cop, one span per element m of M, and its
   colimit P. *)
Definition ew_PD :
  MultiSpan@{c} (carrier (cmon_setoid M)) ⟶ RMod@{o x a p c} R :=
  ms_diagram@{o c w} M ew_Cop Gen
    (fun m => ew_ev m) (fun m => ew_inj (ew_am m)).

Definition ew_PL : Colimit ew_PD := ew_CC _ ew_PD.

Definition ew_P : obj[RMod@{o x a p c} R] :=
  vertex_obj[@limit_cone _ _ _ ew_PL].

Definition ew_pM : M ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) ms_mod.

Definition ew_pF : ew_Cop ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) ms_free.

Definition ew_pG (m : carrier (cmon_setoid M)) :
  Gen ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) (ms_gen m).

Lemma ew_pM_ev (m : carrier (cmon_setoid M)) : ew_pM ∘ ew_ev m ≈ ew_pG m.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ ew_PL))
           ms_mod (ms_gen m) ttt).
Qed.

Lemma ew_pF_inj (m : carrier (cmon_setoid M)) :
  ew_pF ∘ ew_inj (ew_am m) ≈ ew_pG m.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ ew_PL))
           ms_free (ms_gen m) ttt).
Qed.

(* The one equation the covering rests on: P identifies m with the
   generator of the copy of [Gen] that [ew_am m] names. *)
Lemma ew_key (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom ew_pF) (cmon_map (rm_hom (ew_inj (ew_am m))) g0)
    ≈ cmon_map (rm_hom ew_pM) m.
Proof.
  pose proof (ew_pF_inj m g0) as H1; pose proof (ew_pM_ev m g0) as H2.
  simpl in H1, H2.
  exact (Equivalence_Transitive _ _ _ H1 (Equivalence_Symmetric _ _ H2)).
Qed.

(* [K] carries the colimit P to a limit, so the compatible family
   (x0 at M, ew_y0 at ew_Cop, ew_am m at each copy of Gen) is the image of
   one element [ew_e] of [K P]. *)
Definition ew_efam (i : MultiSpan@{c} (carrier (cmon_setoid M))) :
  carrier ((K ◯ ew_PD^op) i).
Proof using contK.
  destruct i as [| | m]; [ exact x0 | exact ew_y0 | exact (ew_am m) ].
Defined.

Definition ew_e_ex :
  { w : carrier (K ew_P)
  & ∀ i, cone_leg (FCone K (@limit_cone _ _ _ ew_PL)) i w ≈ ew_efam i }.
Proof using contK.
  refine (sets_limit_point (FCone K (@limit_cone _ _ _ ew_PL))
            (contK _ _ (@limit_cone _ _ _ ew_PL) (limit_limitcone ew_PL))
            ew_efam _).
  intros i i' f.
  destruct i as [| | m], i' as [| | m']; simpl in f |- *;
    try contradiction;
    first [ exact (@fmap_id _ _ K _ _)
          | reflexivity
          | exact (ew_y0_leg _)
          | (subst; exact (@fmap_id _ _ K _ _)) ].
Defined.

Definition ew_e : carrier (K ew_P) := projT1 ew_e_ex.

Lemma ew_e_leg : @fmap _ _ K ew_P M ew_pM ew_e ≈ x0.
Proof using contK. exact (projT2 ew_e_ex ms_mod). Qed.

(* The member of the solution set: [ew_Cop] modulo the [Prop] kernel of
   [ew_pF], a [PSubmodule] of the ONE fixed module [ew_Cop]. *)
Definition ew_N : PSubmodule ew_Cop := pker ew_pF.

Definition ew_Q : obj[RMod@{o x a p c} R] := QuotientMod (psm_sub ew_N).

Definition ew_k : ew_Q ~{RMod@{o x a p c} R}~> ew_P.
Proof.
  refine (mquot_med (psm_sub ew_N) (existT _ ew_pF _)).
  intros z Hz; exact (pequiv_to _ _ Hz).
Defined.

Lemma ew_qrel_of (z z' : carrier (cmon_setoid ew_Cop)) :
  cmon_map (rm_hom ew_pF) z ≈ cmon_map (rm_hom ew_pF) z' →
  mquot_rel (psm_sub ew_N) z z'.
Proof.
  intro H; constructor; simpl.
  apply pequiv_from.
  rewrite (ab_map_sub (rm_hom ew_pF) z z').
  apply (snd (ab_sub_eq_zero_iff _ _ _)); exact H.
Qed.

(* The covering map, with NO choice: m ↦ the generator of the copy that
   [ew_am m] names, read in the quotient. *)
Definition ew_tfun (m : carrier (cmon_setoid M)) :
  carrier (cmon_setoid ew_Cop) :=
  cmon_map (rm_hom (ew_inj (ew_am m))) g0.

Definition ew_t : M ~{RMod@{o x a p c} R}~> ew_Q.
Proof.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact ew_tfun.
  - intros m m' Hm; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key m), (ew_key m'); now rewrite Hm.
  - apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (cmon_zero M)).
    rewrite (cmon_map_zero (rm_hom ew_pM)).
    symmetry; exact (cmon_map_zero (rm_hom ew_pF)).
  - intros m m'; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (cmon_plus M m m')).
    rewrite (cmon_map_plus (rm_hom ew_pF)).
    rewrite (ew_key m), (ew_key m').
    exact (cmon_map_plus (rm_hom ew_pM) m m').
  - intros r m; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (rm_smul M r m)).
    rewrite (rm_map_smul ew_pF).
    rewrite (ew_key m).
    exact (rm_map_smul ew_pM r m).
Defined.

Example ew_t_at (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom ew_t) m = cmon_map (rm_hom (ew_inj (ew_am m))) g0 := eq_refl.

Lemma ew_k_t : ew_k ∘ ew_t ≈ ew_pM.
Proof. intro m; simpl; exact (ew_key m). Qed.

Definition ew_eQ : carrier (K ew_Q) := @fmap _ _ K ew_P ew_Q ew_k ew_e.

Lemma ew_t_covers : @fmap _ _ K ew_Q M ew_t ew_eQ ≈ x0.
Proof using contK.
  unfold ew_eQ.
  pose proof (@fmap_comp _ _ K ew_P ew_Q M ew_t ew_k ew_e) as Hc; simpl in Hc.
  pose proof (@fmap_respects _ _ K ew_P M (ew_k ∘ ew_t) ew_pM ew_k_t ew_e)
    as Hr;
    simpl in Hr.
  rewrite <- ew_e_leg.
  exact (Equivalence_Transitive _ _ _ (Equivalence_Symmetric _ _ Hc) Hr).
Qed.

End AtElement.

(* The index: a [Prop] submodule of the fixed [ew_Cop] with an element of
   [K] at the quotient.  It sits at the carrier universe [c]. *)
Definition ew_WIdx : Type@{c} :=
  { N : PSubmodule ew_Cop & carrier (K (QuotientMod (psm_sub N))) }.

Definition RModop_esols : ElementSolutionSet K.
Proof using contK.
  refine (@Build_ElementSolutionSet ((RMod@{o x a p c} R)^op) K ew_WIdx
            (fun i => QuotientMod (psm_sub (projT1 i))) (fun i => projT2 i) _).
  intros M x.
  exists (existT (fun N : PSubmodule ew_Cop =>
                    carrier (K (QuotientMod (psm_sub N))))
            (ew_N M x) (ew_eQ M x)).
  exists (ew_t M x).
  exact (ew_t_covers M x).
Defined.

End Covering.

(** ** 5. Every continuous K : (R-Mod)^op ⟶ Sets is representable *)

Definition RModop_continuous_representable@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s})
  (contK : ContinuousFunctor K) : Representable K :=
  representability_theorem K
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit contK) (RModop_esols K contK).

(** ** 6. Watt's theorem, contravariant form, with no hypothesis *)

Definition watts_theorem_unconditional@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun ((RMod@{o x a p c} R)^op) Ab@{b c})
      (@CoHomAb _ (RMod_LocallyPropositional R) (RMod_AbEnriched R) A) T }.
Proof.
  pose (Rp := RModop_continuous_representable (Ab_Forget@{b s c} ◯ T)
                (continuous_compose contT Ab_Forget_creates_continuous)).
  exists (wab_obj Rp).
  exact (@watt_ab_iso _ (LocallyPropositional_op (RMod_LocallyPropositional R))
           (AbEnriched_op (RMod_AbEnriched R)) T AF Rp).
Defined.

(* The representing module IS the object the representability theorem
   produces for [Ab_Forget ◯ T]. *)
Example watts_theorem_unconditional_obj@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  projT1 (watts_theorem_unconditional T AF contT)
    = wab_obj (RModop_continuous_representable (Ab_Forget@{b s c} ◯ T)
                 (continuous_compose contT Ab_Forget_creates_continuous))
  := eq_refl.

(** ** 7. Non-vacuity *)

(* Every module A gives an instance of the theorem, through
   Functor/Representable/Additive.v's [CoHomAb_continuous], and the
   module the theorem returns is isomorphic to A. *)
Definition watts_unconditional_CoHomAb_obj@{a c p o x b +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, Set < b, c < b +}
  {R : RingObject@{a c p}} (A : RMod@{o x a p c} R) :
  projT1 (watts_theorem_unconditional
            (@CoHomAb _ (RMod_LocallyPropositional R) (RMod_AbEnriched R) A
             : _ ⟶ Ab@{b c})
            (@HomAb_additive _
               (LocallyPropositional_op (RMod_LocallyPropositional R))
               (AbEnriched_op (RMod_AbEnriched R)) A)
            (CoHomAb_continuous (RMod_AbEnriched R) A))
    ≅[(RMod@{o x a p c} R)^op] A :=
  repr_unique_iso
    (@HomAb_representable _
       (LocallyPropositional_op (RMod_LocallyPropositional R))
       (AbEnriched_op (RMod_AbEnriched R)) A)
    (RModop_continuous_representable _
       (continuous_compose (CoHomAb_continuous (RMod_AbEnriched R) A)
          Ab_Forget_creates_continuous)).

(* The set-valued form at the plain hom-functor. *)
Definition RModop_hom_representable_obj@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (A : RMod@{o x a p c} R) :
  @repr_obj _ _ (RModop_continuous_representable
                   (@HomFrom_at ((RMod@{o x a p c} R)^op) A : _ ⟶ Sets@{c s})
                   (@hom_continuous_at ((RMod@{o x a p c} R)^op) A))
    ≅[(RMod@{o x a p c} R)^op] A :=
  repr_unique_iso (@Hom_Representable ((RMod@{o x a p c} R)^op) A)
    (RModop_continuous_representable _
       (@hom_continuous_at ((RMod@{o x a p c} R)^op) A)).

(* At a concrete ring: ℤ, with its three universes apart. *)
Definition watts_unconditional_at_Z@{a c p o x b +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, Set < b, c < b +}
  (A : RMod@{o x a p c} Int_Ring@{c p a}) :
  projT1 (watts_theorem_unconditional
            (@CoHomAb _ (RMod_LocallyPropositional _) (RMod_AbEnriched _) A
             : _ ⟶ Ab@{b c})
            (@HomAb_additive _
               (LocallyPropositional_op (RMod_LocallyPropositional _))
               (AbEnriched_op (RMod_AbEnriched _)) A)
            (CoHomAb_continuous (RMod_AbEnriched _) A))
    ≅[(RMod@{o x a p c} Int_Ring@{c p a})^op] A :=
  watts_unconditional_CoHomAb_obj A.
