Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(** * The fork C² ⇉ C → 1 in Cat, split by a terminal object of C *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.6, the example of a fork in Cat,
         printed p. 150 (PDF p. 159) — maclane:VI.6:remark1; the
         definitions of fork and split fork open the section, printed
         p. 149 (PDF p. 158)
   nLab: https://ncatlab.org/nlab/show/split+coequalizer
   nLab: https://ncatlab.org/nlab/show/arrow+category
   nLab: https://ncatlab.org/nlab/show/terminal+category

   WHAT THE BOOK SAYS, read from the page images.  On p. 149: "By a fork
   in a category C we mean a diagram a ⇉ b → c (1) in C with e∂₀ = e∂₁",
   and "A split fork in C is a fork (1) with two more arrows a ← b ← c
   (2)", t and s, "which satisfy with the arrows (1) the conditions
   e∂₀ = e∂₁, es = 1, ∂₀t = 1, ∂₁t = se. (3)".  On p. 150: "Since a
   split fork is defined by equations involving only composites and
   identities, it remains a split fork under the application of any
   functor.  Hence, Corollary.  In every split fork, e is an absolute
   coequalizer of ∂₀ and ∂₁."  Then: "Here is an example of a fork in
   Cat, for C any category: C² ⇉ C → 1", the pair ∂₀, ∂₁ and the arrow
   e.  "C² is the category whose objects are the arrows of C; ∂₀ and ∂₁
   are the functors assigning to each arrow its domain and its codomain,
   respectively, while e is the functor which sends every object of C
   to the unique object of 1.  If C has a terminal object a₀, this fork
   is split by the functor s which sends the unique object of 1 to a₀,
   and the functor t which sends each c ∈ C to the unique arrow
   c → a₀."

   THE DATA: FOUR PIECES REUSED, ONE NEW.  C² is Construction/Arrow.v's
   [Arrow C], the comma (Id ↓ Id).  ∂₀ and ∂₁ are
   Construction/Comma/Diagram.v's [Arrow_dom] and [Arrow_cod], Mac Lane's
   ∂0 and ∂1 of §II.6, the comma projections at S = T = Id.  e is
   Instance/One.v's [Erase C], which is the terminal map of [Cat] and of
   [StrictCat] at [eq_refl] ([arrow_fork_e_one],
   [arrow_fork_e_one_strict]).  s is [Diagonal _1 a₀], the constant
   functor of Functor/Diagonal.v out of 1, i.e. the functor 1 ⟶ C picking
   out a₀, which is how Instance/One/Diagonal.v reads it and the term
   Instance/Cat/Pullback.v uses as a cospan leg; it sends the object of
   1 to a₀ at [eq_refl] ([arrow_fork_s_obj]).  The new functor is t,
   [arrow_fork_t]: Construction/Arrow/Functor.v's [Arrow_intro], Mac
   Lane's Exercise II.4.7 reading of a natural transformation as a
   functor into C², applied to the unique arrow from Id[C] to the
   terminal object of the functor category [C, C], the constant functor
   at a₀ (Instance/Fun/Terminal.v's [Functor_Category_Terminal], by that
   file's account Mac Lane's Exercise III.5.5 in the nullary case).  So
   t c is the unique arrow c → a₀ ([arrow_fork_t_obj]) and t f is the
   square (f, 1) ([arrow_fork_t_map]), both at [eq_refl].

   NAMES.  Construction/Arrow/Functor.v, required for [Arrow_intro], has
   an [Arrow_dom H] and an [Arrow_cod H] of its own, the boundaries of a
   functor H into C².  Construction/Comma/Diagram.v is required after it,
   so the short names below are Diagram.v's; the two pairs have
   different types, so a mix-up would be a type error and could not
   change a statement's meaning silently.

   THE FOUR LAWS.  The split fork is Structure/Coequalizer/Split.v's
   record [SplitCoequalizer] with f := ∂₀ and g := ∂₁, whose four laws
   are Mac Lane's (3) in his order.  They are proved in [StrictCat], the
   strict category of categories of the textbooks, which identifies two
   functors by equalities of their values at every object along which
   their arrow maps agree up to ≈ ([Functor_StrictEq_Setoid]): laws 1
   and 2 because any two functors into 1 are strictly equal
   (Instance/StrictCat/Terminal.v's [StrictCat_Terminal]), laws 3 and 4
   with the object component [fun _ => eq_refl] and reflexivity on
   arrows; their proofs end [Defined], and those components read back
   at [eq_refl] ([arrow_fork_law3_strict_component],
   [arrow_fork_law4_strict_component]).  Law 1 needs no terminal object,
   so C² ⇉ C → 1 is a fork for every C, as the book says
   ([arrow_fork_law1_strict]; in [Cat], [arrow_fork_law1], from
   Instance/One.v's [Cat_Terminal]).  The split fork in [StrictCat] is
   [arrow_fork_split_strict].  The one in [Cat], [arrow_fork_split], is
   that one pushed along Instance/StrictCat/ToCat.v's comparison functor
   [StrictCat_to_Cat] by Split.v's [functor_preserves_split]: the remark
   on p. 150 that a split fork, being defined by equations, remains one
   under any functor.  The comparison is the identity on objects and on
   arrows, so the split fork in [Cat] has Mac Lane's e, s and t at
   [eq_refl] ([arrow_fork_split_e], [arrow_fork_split_s],
   [arrow_fork_split_t]).
     A second split fork in [Cat], [arrow_fork_split_direct], is proved
   there directly: laws 2 to 4 hold in [Cat] with identity isomorphisms
   for components ([arrow_fork_law2_direct], [arrow_fork_law3_direct],
   [arrow_fork_law4_direct]), and law 1 is [arrow_fork_law1].  It has the
   same e, s and t ([arrow_fork_split_direct_e],
   [arrow_fork_split_direct_s], [arrow_fork_split_direct_t]), so the two
   differ only in their law fields, and that is where they differ in
   strength (STRENGTHS).  The pushed one is kept as the primary one,
   being the book's remark; the direct one is the one whose components
   compute.

   CONSEQUENCES, through Split.v and Absolute.v.  e is a coequalizer of
   ∂₀ and ∂₁ in [StrictCat] and in [Cat]
   ([arrow_fork_coequalizer_strict], [arrow_fork_coequalizer], by
   [split_coequalizer_is_coequalizer], the Lemma of p. 149).  The
   Corollary of p. 150 is stated at this fork through issue #477's
   predicate [AbsoluteCoequalizer] (Structure/Coequalizer/Absolute.v),
   which quantifies over the functors out of the category: e is an
   absolute coequalizer in [StrictCat] and in [Cat]
   ([arrow_fork_absolute_strict], [arrow_fork_absolute], by
   [split_coequalizer_absolute]).  Where Mac Lane's definition takes
   "any category X whatever", the targets here are the categories
   X : Category@{xo xh xh}, whose hom and proof levels coincide, as
   [IsCoequalizer] requires, with o <= xh (UNIVERSES).  At one target D
   and functor F, the Corollary says that F carries e to a coequalizer,
   which the file also states through Split.v's
   [split_coequalizer_preserved], for every functor out of either
   category into a D : Category@{do dh dh} with o <= dh
   ([arrow_fork_preserved_strict], [arrow_fork_preserved]); the two
   readings agree at [eq_refl] ([arrow_fork_preserved_absolute_strict],
   [arrow_fork_preserved_absolute]).  These are the first coequalizers
   stated in [Cat] or [StrictCat]: no other file states an
   [IsCoequalizer], a [SplitCoequalizer] or an [AbsoluteCoequalizer] at
   either (a grep of the tree), and Instance/Cat/Limit.v scopes
   coequalizers out.

   NOT EVERY SUCH FORK IS A COEQUALIZER.  This is not the book's; it
   shows that the hypothesis is not idle.  If C has no objects, e is not
   a coequalizer of ∂₀ and ∂₁ in [Cat] ([arrow_fork_not_coequalizer]):
   C² has no objects either, so the identity of C coforks the pair, and
   it would descend through e to a functor 1 ⟶ C, whose value is an
   object of C.  The empty category is such a C
   ([arrow_fork_not_coequalizer_0]).

   STRENGTHS, measured.  The two sides of laws 1, 3 and 4 agree at
   [eq_refl] on every object and every arrow ([arrow_fork_law1_obj],
   [arrow_fork_law1_map], [arrow_fork_law3_obj], [arrow_fork_law3_map],
   [arrow_fork_law4_obj], [arrow_fork_law4_map]), which by eta is to
   say that their object maps and their arrow maps are convertible as
   functions (six such equalities at [eq_refl], in a scratch compile).
   Those of law 2 agree at [eq_refl] at the object of 1 and at its
   identity arrow ([arrow_fork_law2_obj], [arrow_fork_law2_map]); at a
   variable object or arrow of 1 [eq_refl] is refused (R1 and R2 of
   Test/ProbeSplitFork478.v), and a case analysis is needed, [poly_unit]
   being an inductive type with no eta rule.  None of the four laws
   holds as a Leibniz equality of the two composite [Functor] records at
   [eq_refl] (R3 to R6): where their actions agree, their law fields are
   still different proof terms.  As equalities of functors, then, the
   laws are proved in the stricter of the tree's two setoids on
   functors, Theory/Functor.v's [Functor_StrictEq_Setoid], which is
   [StrictCat]'s ≈, against its [Functor_Setoid], natural isomorphism,
   which is [Cat]'s; the readbacks above say more, of the actions alone.
     In [Cat] it is the components of the isomorphisms that can
   compute, and in [arrow_fork_split] they do not: R8 refuses law 3's
   component as [id] at [eq_refl].  Its laws are the strict ones pushed
   along [StrictCat_to_Cat] by [functor_preserves_split], and [Eval cbv]
   of that component (in a scratch file) stops at opaque constants: the
   ones the setoid rewriting in [functor_preserves_split] goes through,
   the standard library's [CMorphisms] obligation
   [trans_co_eq_inv_arrow_morphism_obligation_1] and Theory/Functor.v's
   [Functor_Setoid_obligation_1], and the three obligations of
   [StrictCat_to_Cat], whose respects obligation calls
   Instance/StrictCat/ToCat.v's [strict_equiv_implies_fun_equiv].  That
   lemma does not occur in the normal form, so making it transparent
   would not make the components compute.  In [arrow_fork_split_direct]
   the components of laws 3 and 4 are [id] at [eq_refl] at every object
   ([arrow_fork_law3_direct_component],
   [arrow_fork_law4_direct_component]; C27 is R8's twin there), and law
   2's at the object of 1 (in a scratch compile); law 1's is not,
   [arrow_fork_law1] being closed with [Qed].  That lemma, the fork law
   in [Cat] for every C, is not read through [StrictCat] at all: it is
   [Cat_Terminal]'s [one_unique].
     Four proofs end [Qed]: [arrow_fork_law1], [arrow_fork_law1_strict],
   [arrow_fork_law2_strict] and [arrow_fork_not_coequalizer]; every
   other name is a transparent term.  The hypothesis of the splitting is
   met in the tree, by [Cat] itself among others (control C25 of the
   probe).

   UNIVERSES, read off [About] for all forty-five names, by script.
   Every name but [arrow_fork_not_coequalizer_0] binds o and h first,
   with C : Category@{o h h}: [Cat] and [StrictCat] take their objects
   at one hom and proof level (a scratch [Definition] of the coercion of
   a Category@{a b c} into [obj[Cat]] carries b = c).  Twenty-eight
   names carry h <= o: those with a binder C whose statements make C²
   and C objects of one [Cat] or [StrictCat] instance.  C² is then at
   the object level o, and its objects carry arrows of C, so o is at
   least h ([Arrow]'s own block bounds its object level below by its
   argument's hom level).  The other seventeen do not carry it; among
   them [arrow_fork_not_coequalizer_0], whose C is [_0], at hom level
   [Set], where the bound holds trivially.  R7 of the probe pins the
   bound: the fork cannot be stated at o < h.  The binders [@{o h +}]
   are load-bearing: with them removed, law 1 minimizes to
   C : Category@{u u u}, one level for objects, homs and proofs
   (measured in a scratch copy).  Only [arrow_fork_not_coequalizer_0]'s
   block mentions [Set], the hom level of Instance/Zero.v's [_0], which
   is a Category@{u Set Set}.  No block carries an equation.
   [arrow_fork_preserved] and [arrow_fork_preserved_strict] name the
   levels do and dh of the target D in their binders and carry o <= dh:
   Split.v's [split_coequalizer_preserved], whose binders #477 wrote
   out, lets the target's hom level sit above the source's, and the
   source here is [Cat] or [StrictCat], whose hom level is o.  Left
   unwritten, D's binders let minimization put D's hom level at o (D a
   Category@{u o o}, measured in a scratch compile).  Likewise
   [arrow_fork_absolute] and [arrow_fork_absolute_strict] name the
   target levels xo and xh and carry o <= xh, through the explicit
   universe instance [AbsoluteCoequalizer@{_ _ xo xh _}] in their
   statements, an instance of an existing constant and the only one the
   file writes outside its binders: left to Rocq, minimization sets the
   target's hom level to o ([AbsoluteCoequalizer@{u o u0 o u1}],
   measured in a scratch compile), as Absolute.v records for its
   [split_coequalizer_absolute].  No explicit universe instance of a new
   constant is written.

   STALE PREMISE.  Issue #478 (filed 2026-07-23) says that no
   construction assembles the pair dom, cod : C² ⇉ C, the fork to 1, or
   the splitting.  For the pair, that was accurate when filed and has
   been stale since PR #1134 (merged 2026-08-17), which named it
   [Arrow_dom] and [Arrow_cod] in Construction/Comma/Diagram.v; the pair
   is reused here.  The fork to 1 and its splitting were absent, as the
   issue says.

   CLOSURE.  The [Require]s load eighty-five [Category] modules
   ([Print Libraries]): thirty of them for Instance/Fun/Terminal.v,
   whose [Functor_Category_Terminal] supplies the transformation t
   classifies, and eleven for Structure/Coequalizer/Absolute.v, whose
   predicate states the Corollary, each figure being what dropping that
   one [Require] saves.  The cheapest variant not taken is a local
   transformation Id[C] ⟹ s ◯ e with components [one] and its two
   naturality squares by [one_unique], which compiles, every name
   closed, in a scratch copy without Instance/Fun/Terminal.v, at
   fifty-five modules.  CORRECTION (#480): eighty-six, thirty, twelve
   and fifty-six by the same counts, since Structure/Coequalizer/
   Absolute.v requires Structure/Coequalizer/Contractible.v.

   NOT DELIVERED.  Mac Lane's example in Grp and Exercise 1 are issue
   #479's.  Whether e is a coequalizer for some C that has objects but
   no terminal object is not examined; only categories without objects
   are shown to fall short.  A law 1 in [Cat] whose components compute:
   [arrow_fork_split_direct] reuses [arrow_fork_law1] rather than
   restate it. *)

(** ** The fork, for C any category *)

(* e, the unique functor C ⟶ 1, is the terminal map of [Cat] and of
   [StrictCat] alike. *)
Example arrow_fork_e_one@{o h +} (C : Category@{o h h}) :
  Erase C = @one Cat Cat_Terminal C := eq_refl.

Example arrow_fork_e_one_strict@{o h +} (C : Category@{o h h}) :
  Erase C = @one StrictCat StrictCat_Terminal C := eq_refl.

(* Law 1, e ∂₀ = e ∂₁: both sides are functors into 1, so they agree in
   either category of categories. *)
Lemma arrow_fork_law1@{o h +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod.
Proof. apply (@one_unique Cat Cat_Terminal). Qed.

Lemma arrow_fork_law1_strict@{o h +} (C : Category@{o h h}) :
  Erase C ∘[StrictCat] Arrow_dom ≈[StrictCat] Erase C ∘[StrictCat] Arrow_cod.
Proof. apply (@one_unique StrictCat StrictCat_Terminal). Qed.

(* ... and on the nose, on objects and on arrows. *)
Example arrow_fork_law1_obj@{o h +} (C : Category@{o h h}) (x : @Arrow C) :
  fobj[Erase C ◯ Arrow_dom] x = fobj[Erase C ◯ Arrow_cod] x := eq_refl.

Example arrow_fork_law1_map@{o h +} (C : Category@{o h h})
  {x y : @Arrow C} (f : x ~> y) :
  fmap[Erase C ◯ Arrow_dom] f = fmap[Erase C ◯ Arrow_cod] f := eq_refl.

(** ** The splitting, given a terminal object a₀ of C *)

(* s, the functor 1 ⟶ C sending the object of 1 to a₀. *)
Example arrow_fork_s_obj@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  (x : _1) :
  fobj[Diagonal _1 (@terminal_obj C T)] x = @terminal_obj C T := eq_refl.

(* t, the functor C ⟶ C² sending c to the unique arrow c → a₀: the
   classifying functor of the unique arrow from Id[C] to the terminal
   object of [C, C], the constant functor at a₀. *)
Definition arrow_fork_t@{o h +} {C : Category@{o h h}} `{T : @Terminal C} :
  C ⟶ @Arrow C :=
  Arrow_intro (Id[C]; (Constant_Terminal_Functor T;
                        @one _ (Functor_Category_Terminal T) Id[C])).

Example arrow_fork_t_obj@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  (c : C) :
  fobj[arrow_fork_t] c = ((c, @terminal_obj C T); @one C T c) := eq_refl.

Example arrow_fork_t_map@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  {c d : C} (f : c ~> d) :
  `1 (fmap[arrow_fork_t] f) = (f, @id C (@terminal_obj C T)) := eq_refl.

(* Law 2, e s = 1: two functors into 1 again. *)
Lemma arrow_fork_law2_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Erase C ∘[StrictCat] Diagonal _1 (@terminal_obj C T)
    ≈[StrictCat] @id StrictCat _1.
Proof. apply (@one_unique StrictCat StrictCat_Terminal). Qed.

(* Law 3, ∂₀ t = 1, with the object component [eq_refl]. *)
Lemma arrow_fork_law3_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_dom ∘[StrictCat] arrow_fork_t ≈[StrictCat] @id StrictCat C.
Proof. exists (fun _ => eq_refl). intros; simpl; reflexivity. Defined.

(* Law 4, ∂₁ t = s e, with the object component [eq_refl]. *)
Lemma arrow_fork_law4_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_cod ∘[StrictCat] arrow_fork_t
    ≈[StrictCat] Diagonal _1 (@terminal_obj C T) ∘[StrictCat] Erase C.
Proof. exists (fun _ => eq_refl). intros; simpl; reflexivity. Defined.

(* ... and those object components, read back. *)
Example arrow_fork_law3_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law3_strict C T) = fun _ => eq_refl := eq_refl.

Example arrow_fork_law4_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law4_strict C T) = fun _ => eq_refl := eq_refl.

(* Law 2 on the nose at the object of 1 and its arrow; for a variable
   object or arrow of 1 it needs a case analysis (see the header). *)
Example arrow_fork_law2_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] ttt = fobj[Id[_1]] ttt
  := eq_refl.

Example arrow_fork_law2_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] (@id _1 ttt)
    = fmap[Id[_1]] (@id _1 ttt) := eq_refl.

(* Laws 3 and 4 on the nose, on objects and on arrows. *)
Example arrow_fork_law3_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  fobj[Arrow_dom ◯ arrow_fork_t] c = fobj[Id[C]] c := eq_refl.

Example arrow_fork_law3_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} {c d : C} (f : c ~> d) :
  fmap[Arrow_dom ◯ arrow_fork_t] f = fmap[Id[C]] f := eq_refl.

Example arrow_fork_law4_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  fobj[Arrow_cod ◯ arrow_fork_t] c
    = fobj[Diagonal _1 (@terminal_obj C T) ◯ Erase C] c := eq_refl.

Example arrow_fork_law4_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} {c d : C} (f : c ~> d) :
  fmap[Arrow_cod ◯ arrow_fork_t] f
    = fmap[Diagonal _1 (@terminal_obj C T) ◯ Erase C] f := eq_refl.

(* The split fork in StrictCat: Split.v's record, f := ∂₀ and g := ∂₁. *)
Definition arrow_fork_split_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer StrictCat (@Arrow C) C Arrow_dom Arrow_cod :=
  @Build_SplitCoequalizer StrictCat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) (Diagonal _1 (@terminal_obj C T)) arrow_fork_t
    (arrow_fork_law1_strict C) arrow_fork_law2_strict
    arrow_fork_law3_strict arrow_fork_law4_strict.

(* The split fork in Cat: the one in StrictCat, pushed along the
   comparison functor StrictCat ⟶ Cat, which is the identity on objects
   and on arrows. *)
Definition arrow_fork_split@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod :=
  functor_preserves_split StrictCat_to_Cat _ _ arrow_fork_split_strict.

(* ... whose e, s and t are Mac Lane's. *)
Example arrow_fork_split_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e arrow_fork_split = Erase C := eq_refl.

Example arrow_fork_split_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s arrow_fork_split = Diagonal _1 (@terminal_obj C T) := eq_refl.

Example arrow_fork_split_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t arrow_fork_split = arrow_fork_t := eq_refl.

(** ** The split fork in Cat, directly *)

(* Laws 2 to 4 proved in Cat itself, each natural isomorphism having
   identities for components; law 1 is [arrow_fork_law1]. *)
Lemma arrow_fork_law2_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Erase C ∘[Cat] Diagonal _1 (@terminal_obj C T) ≈[Cat] @id Cat _1.
Proof.
  unshelve eexists.
  - intros []; exact iso_id.
  - intros [] [] []; simpl; reflexivity.
Defined.

Lemma arrow_fork_law3_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_dom ∘[Cat] arrow_fork_t ≈[Cat] @id Cat C.
Proof. exists (fun _ => iso_id). intros; simpl; cat. Defined.

Lemma arrow_fork_law4_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_cod ∘[Cat] arrow_fork_t
    ≈[Cat] Diagonal _1 (@terminal_obj C T) ∘[Cat] Erase C.
Proof. exists (fun _ => iso_id). intros; simpl; cat. Defined.

(* The components of laws 3 and 4 are identities on the nose. *)
Example arrow_fork_law3_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law3_direct C T) c) = id := eq_refl.

Example arrow_fork_law4_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law4_direct C T) c) = id := eq_refl.

(* The split fork they make, with the same e, s and t. *)
Definition arrow_fork_split_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod :=
  @Build_SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) (Diagonal _1 (@terminal_obj C T)) arrow_fork_t
    (arrow_fork_law1 C) arrow_fork_law2_direct
    arrow_fork_law3_direct arrow_fork_law4_direct.

Example arrow_fork_split_direct_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e arrow_fork_split_direct = Erase C := eq_refl.

Example arrow_fork_split_direct_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s arrow_fork_split_direct = Diagonal _1 (@terminal_obj C T)
  := eq_refl.

Example arrow_fork_split_direct_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t arrow_fork_split_direct = arrow_fork_t := eq_refl.

(** ** Consequences, through Structure/Coequalizer/Split.v and Absolute.v *)

(* e is a coequalizer of ∂₀ and ∂₁: the Lemma of §VI.6. *)
Definition arrow_fork_coequalizer_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @IsCoequalizer StrictCat _ _ Arrow_dom Arrow_cod _1 (Erase C) :=
  split_coequalizer_is_coequalizer _ _ arrow_fork_split_strict.

Definition arrow_fork_coequalizer@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase C) :=
  split_coequalizer_is_coequalizer _ _ arrow_fork_split.

(* ... and every functor out of StrictCat or out of Cat into a
   D : Category@{do dh dh} with o <= dh carries it to a coequalizer. *)
Definition arrow_fork_preserved_strict@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : StrictCat ⟶ D) :
  IsCoequalizer (fmap[F] Arrow_dom) (fmap[F] Arrow_cod)
    (F _1) (fmap[F] (Erase C)) :=
  split_coequalizer_preserved F _ _ arrow_fork_split_strict.

Definition arrow_fork_preserved@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : Cat ⟶ D) :
  IsCoequalizer (fmap[F] Arrow_dom) (fmap[F] Arrow_cod)
    (F _1) (fmap[F] (Erase C)) :=
  split_coequalizer_preserved F _ _ arrow_fork_split.

(* The Corollary of p. 150, "In every split fork, e is an absolute
   coequalizer of ∂₀ and ∂₁", at this fork: Absolute.v's predicate. *)
Definition arrow_fork_absolute_strict@{o h xo xh +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @AbsoluteCoequalizer@{_ _ xo xh _} StrictCat (@Arrow C) C Arrow_dom
    Arrow_cod _1 (Erase C) :=
  split_coequalizer_absolute arrow_fork_split_strict.

Definition arrow_fork_absolute@{o h xo xh +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @AbsoluteCoequalizer@{_ _ xo xh _} Cat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) :=
  split_coequalizer_absolute arrow_fork_split.

(* The two corollaries above are the Corollary, applied to D and F. *)
Example arrow_fork_preserved_absolute_strict@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : StrictCat ⟶ D) :
  @arrow_fork_preserved_strict C T D F = @arrow_fork_absolute_strict C T D F
  := eq_refl.

Example arrow_fork_preserved_absolute@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : Cat ⟶ D) :
  @arrow_fork_preserved C T D F = @arrow_fork_absolute C T D F := eq_refl.

(** ** Not every such fork is a coequalizer *)

(* If C has no objects, neither has C², so the identity of C coforks ∂₀
   and ∂₁; were e a coequalizer, it would descend through e to a functor
   1 ⟶ C, whose value is an object of C. *)
Lemma arrow_fork_not_coequalizer@{o h +} (C : Category@{o h h})
  (empty : C → False) :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase C) → False.
Proof.
  intros E.
  assert (H : @id Cat C ∘[Cat] Arrow_dom ≈[Cat] @id Cat C ∘[Cat] Arrow_cod).
  { unshelve eexists.
    - intros [[x y] f]. contradiction (empty x).
    - intros [[x y] f]. contradiction (empty x). }
  destruct (coeq_desc E (@id Cat C) H) as [u _ _].
  exact (empty (fobj[u] ttt)).
Qed.

(* The empty category is such a C. *)
Example arrow_fork_not_coequalizer_0 :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase _0) → False :=
  arrow_fork_not_coequalizer _0 (fun x => match x with end).
