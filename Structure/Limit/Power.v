Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * Powers and copowers of a single object *)

(* nLab:      https://ncatlab.org/nlab/show/power
   nLab:      https://ncatlab.org/nlab/show/copower
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   Sources, cited BY LOCATION; the one-line descriptions are transcribed from
   the catalog entries of issue #321 rather than from the printed books:

     - Mac Lane, "Categories for the Working Mathematician", 2nd ed.
       (Springer GTM 5), section III.3, printed p. 64 (PDF p. 73), item
       [maclane:III.3:def3], and section III.4, printed p. 70 (PDF p. 79),
       item [maclane:III.4:def4].  The POWER [b^J] is the product of the
       constant J-indexed family at [b], characterized by
       [C(c, b^J) ≅ C(c, b)^J]; dually the COPOWER [J · b] is the
       constant-family coproduct, characterized by [C(J · b, c) ≅ C(b, c)^J].
     - Riehl, "Category Theory in Context", 2nd ed., section 3.5, printed
       p. 110 (PDF p. 130), item [riehl:3.5:example4]: iterated products of a
       single object are POWERS (cotensors), written [A^I], with the
       representable universal property [C(X, A^I) ≅ C(X, A)^I] given by
       composing with the projections [ev_i].  Printed p. 111 (PDF p. 131),
       item [riehl:3.5:example8]: iterated coproducts of a single object are
       COPOWERS (tensors), written [I · A], with [C(∐_I A, X) ≅ C(A, X)^I].
     - Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
       September 2005), chapter 3, section 3.2, unnumbered remark, printed
       p. 61 (PDF p. 70), item [awodey:3.2:remark-finite-copower]: in Sets a
       finite set [A] is a coproduct of copies of the terminal object,
       [A ≅ 1 + 1 + ⋯ + 1] with [n = |A|].

   THIS FILE IS THE NAMING LAYER; THE ISOMORPHISMS ARE NEXT DOOR.

   Everything below is a constant-family reading of
   Structure/Limit/Product.v and Structure/Limit/Coproduct.v, with no proof
   obligation anywhere: every constant is supplied by [:=].  The two
   characterizing isomorphisms, the [Sets] identifications and the Awodey
   witness live in Structure/Limit/Power/Hom.v, which is separate for a
   DEPENDENCY reason and not a thematic one -- see that file's header, and
   the paragraph on Theory/WeaklyInitial.v below.

   WHY THESE NAMES

   [power] and [copower] are the words Mac Lane, Riehl and the nLab use, and
   both were free as top-level constants before this file.  Reproduce with

     rg -n -e '^\s*(Program\s+)?(Definition|Lemma|Theorem|Corollary|Fixpoint|Record|Class|Inductive|Instance|Example|Notation)\s+(power|copower)\b' \
        -g '*.v' -g '!Structure/Limit/Power*'

   -- excluding this file and its satellite, since they now declare exactly
   those names -- which returns nothing.  [Pow] was NOT free and is
   deliberately not used: two
   different in-tree notions already carry it, NEITHER of them Mac Lane's --
   Instance/Fun/Discrete.v:254's [Fixpoint Pow (B : Category) (n : nat) :
   Category], the n-fold product OF CATEGORIES, and Structure/Topos.v:130's
   [Definition Pow (a : C) := Ω ^ a], the topos power OBJECT.  A third
   near-name, [Sets_pow] (Instance/Sets/Products.v:400), IS the same notion at
   [Sets] and is not shadowed either: Structure/Limit/Power/Hom.v proves the
   two ISOMORPHIC rather than redefining it -- only that.  They are NOT
   convertible, and Test/ProbePower.v pins it: a power's carrier is the bare
   function type while the exponential's is setoid MORPHISMS out of the
   discrete setoid.

   Read "free" as scoped to top-level constant DECLARATIONS matching that
   pattern; the token "power" occurs widely in comments and inside longer
   names ([Powerset], [GrpCosetPower], [cogen_power], [law_pow], [mat_pow],
   [tpower]), none of which this file touches.

   NOTATION, AND WHY IT IS OPT-IN

   [J ⋔ b] for the power and [J · b] for the copower, in their own
   [power_scope] with key [%power], following the [addition_scope]
   precedent of Structure/Preadditive.v:77-81: a consumer opts in with
   [Open Scope power_scope] or the [%power] key, and nothing is imposed on a
   file that merely Requires this one.  [⋔] is the nLab's symbol for powering
   and was entirely free tree-wide:

     rg -c -e '⋔' -g '*.v' -g '!Structure/Limit/Power*' -g '!Test/ProbePower.v'

   returns no files.  [·] is Mac Lane's own symbol for the copower, and while
   it occurs in the tree it occurs in COMMENTS only -- no notation
   declaration mentions it, measured by

     rg -n -e '(Notation|Infix|Reserved)' -g '*.v' \
        -g '!Structure/Limit/Power*' | grep -c -e '·'

   which returns 0.  Both notations are declared at level 30, right
   associativity -- the level Structure/Cartesian/Closed.v:65 gives the
   exponential, these being operators of the same kind.

   Mac Lane's own [b^J] is not available at all: [y ^ x] is already the
   exponential of a cartesian closed category, declared twice in
   Structure/Cartesian/Closed.v -- at [object_scope] inside the [Closed]
   section (:65) and at [category_scope] at the end of the file (:433).
   [⊙], sometimes used for the copower, is also unavailable --
   Theory/Isomorphism.v:441 declares [f ⊙ g] for isomorphism composition with
   NO scope annotation, so it is global.

   WHAT IS DELIVERED HERE

   At the ELEMENTARY level, [IsPower b p ev] is [IsIndexedProduct] at the
   constant family and [IsCopower b p inj] is that read in [C^op]; both are
   [Definition]s unfolding to their donors, so every lemma about an indexed
   (co)product applies to a (co)power with no adapter, and
   [IsCopower_is_IsIndexedCoproduct] records the coproduct reading by
   [eq_refl].  [power_desc] and [copower_desc] state the universal property
   with arrows in [C] -- the copower one covariantly, no [^op] visible.

   At the CLASS level, [power J b] and [copower J b] are the chosen
   (co)products of the constant family drawn from [HasIndexedProducts] /
   [HasIndexedCoproducts], with [power_ev] (Riehl's [ev_i]),
   [copower_inj], and their universal properties.

   At the LIMIT level, [power_of_limit] and [copower_of_colimit] read a
   limit of the constant discrete diagram, with [power_ump_of_limit] and
   [copower_ump_of_colimit] the universal properties.  These are provided
   because that is the shape Theory/WeaklyInitial.v actually consumes.

   UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS

   Reproduce with [Set Printing Universes.] and [About]; reading the binder
   alone gets this wrong.

     [power@{u u0 u1 u2 u3 u4}] takes [C : Category@{u3 u4 u4}] and an index
     [Type@{u}] with [u <= u0] and nothing else touching [u]: the index
     universe is bounded above by the class's own index parameter and is
     otherwise free.  No [Set] and no equality.

     [copower] is likewise IN SUBSTANCE -- no [Set], no equality, index not
     pinned -- but NOT in binder layout, and the difference is worth printing
     rather than waving through.  [copower@{u u0 u1 u2 u3}] has FIVE binders,
     its index is [Type@{u0}], and that index carries TWO constraints
     ([u0 < u] and [u0 <= u1]) where [power]'s carries one.  Going through
     [C^op] is what reshuffles them.  The asymmetry is visible in the probe:
     the two smallness negatives print DIFFERENT messages for the two
     operators, and that is why, not an accident of phrasing.

     [power_of_limit@{u u0 u1}] and [copower_of_colimit@{u u0 u1}] take
     [C : Category@{u1 Set Set}] -- [C]'s hom AND proof universes pinned to
     [Set] -- with the INDEX [Type@{u}] left FREE.  That pin is
     Structure/Limit/Product.v's, not this file's: the hom-setoid of
     [DiscreteCat J] is strict equality.  The index staying free is what
     matters for the consumer, since Theory/WeaklyInitial.v's index is a
     hom-type.

   Nothing in this file mentions [Sets]; the universe situation of the two
   characterizing isomorphisms is Structure/Limit/Power/Hom.v's, and is
   measured there.

   THE GAFT SPINE: ONE OF THE TWO ANONYMOUS PRODUCTS IS A POWER AND THE
   OTHER IS NOT.

   Theory/WeaklyInitial.v:104-106 forms
   [Limit (DiscreteCat_Functor (fun _ : (P0 ~> P0) => P0))].  The family is
   CONSTANT, so that is a power -- the endomorphism-indexed power of [P0] --
   and Theory/WeaklyInitial.v now says so, through [power_of_limit] and
   [power_ev_of_limit], which is why this file is kept free of the
   Instance/Sets SATELLITES.

   State that precisely, because the obvious phrasing is false.  [Instance/Sets]
   ITSELF is already in this file's dependency closure, one hop away:
   Structure/Cone.v:6 Requires it, and this file Requires Structure/Cone at
   line 5.  It is likewise already in Adjunction/GAFT.v's closure, through
   Structure/Limit.  So "kept free of Instance/Sets" would be wrong, and a
   textual grep of GAFT.v for [Instance.Sets] -- which returns zero -- measures
   that file's own text, not what it Requires.

   What the split actually buys, measured by comparing the two closures: a
   combined file would add TEN modules to GAFT's, namely Functor/Hom.v, the
   four Instance/Sets satellites (Cartesian, Cartesian/Closed, Cocartesian,
   Products), the three Structure ones (Cartesian, Cartesian/Closed,
   Cocartesian), Structure/Limit/Indexed/Hom.v and Structure/Limit/Power/Hom.v.
   That is the cost avoided, and it is why the naming layer is separated from
   the hom-bijection satellite -- the same split #320 made between
   Structure/Limit/Product.v and Structure/Limit/Indexed/Hom.v, and which
   Structure/Limit/Weighted.v:6 shows is not obligatory for a
   Structure/Limit/ file.

   The change in Theory/WeaklyInitial.v is by conversion only: the statement
   of [initial_from_weakly_initial] is untouched.

   Adjunction/SAFT.v:188-190's [cogen_power] is NOT a power, despite the
   name, and this file makes no attempt to re-express it.  Its family is
   [cogen_power_fam G c p := cog_obj G (projT1 p)] over the Σ-index
   [{ j : cog_index G & c ~> cog_obj G j }] (Adjunction/SAFT.v:175-181),
   which varies with [projT1 p]; there is no single object [b] for which it
   is [fun _ => b].  It is a product of a genuinely indexed family, and the
   word "power" in that file names the classical phrase "the unit into the
   cogenerator power is monic" rather than the constant-family construction.

   WHAT IS NOT DELIVERED

   No (co)power of a family in the enriched sense -- [J] here is a bare
   [Type], not an object of a base of enrichment, so nothing below is a
   cotensor over a monoidal category; Structure/Limit/Weighted.v's
   [WeightedColimit] at a one-object shape is the enriched reading and is not
   connected to this file.  No functoriality of [power] or [copower] in
   either argument, in particular no [J ⋔ (-)] endofunctor and no action on
   maps of index types.  No comparison of [power] with a cartesian closed
   exponential in general -- only at [Sets], in Power/Hom.v.  No claim that a
   category has powers without having all indexed products.

   STATUS: axiom-free, no [Program], no tactic.  Every constant is a
   [Definition] supplied by [:=]; the two [Example]s close by [eq_refl].  All
   22 constants -- the whole of [Print Module Category.Structure.Limit.Power],
   which lists 22 [Definition]s and no opaque constants -- report "Closed
   under the global context"; the Makefile's [print-assumptions] target audits
   the headline ones. *)

(** ** The elementary universal properties, at a constant family *)

(* A power of [b] by the index [J]: an object [p] with a family [ev] of
   evaluation maps that is universal among such families.  Mac Lane's [b^J];
   Riehl's [A^I] with [ev_i] the projections. *)
Definition IsPower {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) : Type :=
  IsIndexedProduct (fun _ : J => b) p ev.

(* A copower of [b] by [J]: dually, an object with a universal family of
   injections.  Mac Lane's [J · b]; Riehl's [I · A]. *)
Definition IsCopower {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) : Type :=
  @IsPower (C^op) J b p inj.

Example IsPower_is_IsIndexedProduct {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  IsPower b p ev = IsIndexedProduct (fun _ : J => b) p ev := eq_refl.

Example IsCopower_is_IsIndexedCoproduct {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  IsCopower b p inj = IsIndexedCoproduct (fun _ : J => b) p inj := eq_refl.

(* The universal property, read with arrows in [C].  The copower form is
   covariant: no [^op] appears in its statement. *)
Definition power_desc {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev)
  {c : C} (pi : ∀ _ : J, c ~> b) :
  ∃! u : c ~> p, ∀ j : J, ev j ∘ u ≈ pi j :=
  @iprod_desc C J (fun _ : J => b) p ev H c pi.

Definition copower_desc {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj)
  {c : C} (iota : ∀ _ : J, b ~> c) :
  ∃! u : p ~> c, ∀ j : J, u ∘ inj j ≈ iota j :=
  @icoprod_desc C J (fun _ : J => b) p inj H c iota.

(* Smart constructors, taking the data in that same covariant form. *)
Definition Build_IsPower {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b)
  (desc : ∀ (c : C) (pi : ∀ _ : J, c ~> b),
            ∃! u : c ~> p, ∀ j : J, ev j ∘ u ≈ pi j) :
  IsPower b p ev :=
  @Build_IsIndexedProduct C J (fun _ : J => b) p ev desc.

Definition Build_IsCopower {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p)
  (desc : ∀ (c : C) (iota : ∀ _ : J, b ~> c),
            ∃! u : p ~> c, ∀ j : J, u ∘ inj j ≈ iota j) :
  IsCopower b p inj :=
  @Build_IsIndexedCoproduct C J (fun _ : J => b) p inj desc.

(** ** The chosen power and copower, from the classes *)

Definition power {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) : C :=
  indexed_product (fun _ : J => b).

Definition power_ev {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) (j : J) : power J b ~> b :=
  indexed_product_proj (fun _ : J => b) j.

Definition power_ump {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) : IsPower b (power J b) (power_ev J b) :=
  indexed_product_ump (fun _ : J => b).

Definition copower {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) : C :=
  @power (C^op) HC J b.

Definition copower_inj {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) (j : J) : b ~> copower J b :=
  @power_ev (C^op) HC J b j.

Definition copower_ump {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) : IsCopower b (copower J b) (copower_inj J b) :=
  @power_ump (C^op) HC J b.

(** ** The limit-shaped reading

    [power_of_limit] and [copower_of_colimit] carry the universe pin that
    Structure/Limit/Product.v's header describes: [DiscreteCat J]'s hom-setoid
    is strict equality, so forming the limit constrains [C]'s hom and proof
    universes (the index, measured in the header, stays free).  They are
    supplied because that is the shape Theory/WeaklyInitial.v consumes -- and
    only that file: Adjunction/SAFT.v's superficially similar [cogen_power] is
    not a power, per the header.  Note the second one reads a limit taken IN
    [C^op] -- the shape
    Structure/Limit/Coproduct.v's header records, NOT [Colimit] in the sense
    of Structure/Limit.v; no translation between the two is offered here
    either. *)

Definition power_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) : C :=
  iprod (fun _ : J => b) L.

Definition power_ev_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) (j : J) :
  power_of_limit b L ~> b :=
  iprod_proj (fun _ : J => b) L j.

Definition power_ump_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b)))
  (c : C) (pi : ∀ _ : J, c ~> b) :
  ∃! u : c ~> power_of_limit b L, ∀ j : J, power_ev_of_limit b L j ∘ u ≈ pi j :=
  iprod_ump (fun _ : J => b) L c pi.

Definition limit_is_power {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) :
  IsPower b (power_of_limit b L) (power_ev_of_limit b L) :=
  limit_is_indexed_product (fun _ : J => b) L.

Definition copower_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) : C :=
  @power_of_limit (C^op) J b L.

Definition copower_inj_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) (j : J) :
  b ~> copower_of_colimit b L :=
  @power_ev_of_limit (C^op) J b L j.

Definition copower_ump_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b)))
  (c : C) (iota : ∀ _ : J, b ~> c) :
  ∃! u : copower_of_colimit b L ~> c,
    ∀ j : J, u ∘ copower_inj_of_colimit b L j ≈ iota j :=
  @power_ump_of_limit (C^op) J b L c iota.

Definition colimit_is_copower {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) :
  IsCopower b (copower_of_colimit b L) (copower_inj_of_colimit b L) :=
  @limit_is_power (C^op) J b L.

(** ** Notation, opt-in *)

Declare Scope power_scope.
Delimit Scope power_scope with power.

Notation "J ⋔ b" := (power J b)
  (at level 30, right associativity) : power_scope.
Notation "J · b" := (copower J b)
  (at level 30, right associativity) : power_scope.
