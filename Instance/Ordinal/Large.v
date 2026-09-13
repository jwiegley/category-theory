Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The large thin preorder of small ordinals *)

(* Mac Lane §V.6, book pp. 122-123 (maclane:V.6:remark-ord-counterexample);
   Awodey §9.8 Remark 9.30, printed pp. 253-254 (awodey:9.8:remark30).
   nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
         https://ncatlab.org/nlab/show/von+Neumann+ordinal
         https://ncatlab.org/nlab/show/W-type

   BACKGROUND.  Mac Lane's §V.6 remark is that the solution set condition
   cannot be dropped from the adjoint functor theorems, and his first
   witness is the ordered class of all small ordinals: it is small-complete
   (read in the direction in which a small product is a supremum), the
   constant one-point functor on it preserves every small limit, and yet
   that functor is not representable, because a representing object would
   be a largest small ordinal.  Awodey's Remark 9.30 makes the same point
   about the size discipline generally: the solution set must be a genuine
   set and the source complete at that size, or the theorem is not true.

   The ordinals here are the Aczel/W-type presentation rather than the von
   Neumann one: an ordinal IS a family of smaller ordinals, indexed by a
   small type -- the W-type W(Type, id).  Aczel introduced this shape for
   the type-theoretic interpretation of constructive set theory (Aczel,
   "The type theoretic interpretation of constructive set theory", Logic
   Colloquium '77, North-Holland 1978), and Taylor develops the ordinals of
   it (Taylor, "Intuitionistic sets and ordinals", Journal of Symbolic
   Logic 61, 1996).  The familiar Brouwer ordinal notations
   ([Zero | Succ | Lim (nat -> _)]) are the branching-restricted special
   case, not a different idea.  The ORDER is the extensional one: [x <= y]
   when every element of [x] is dominated by some element of [y].  That
   relation is reflexive and transitive but not antisymmetric, which is
   exactly what the library's Instance/Proset.v asks for -- a preorder, not
   a poset -- and is why no quotient is taken here.

   WHY THE UNIVERSE LEVEL IS THE WHOLE POINT.  [SmallOrd@{u}] is declared at
   [Type@{u+1}] while its index types range over [Type@{u}].  So the
   construction [osup] accepts exactly the [Type@{u}]-indexed families --
   the SMALL ones -- and [SmallOrd@{u}] itself is not among the types it
   accepts.  Every small family has a supremum ([ojoin]); the family of ALL
   ordinals does not, and could not, because a supremum of it would be a
   greatest element and [osucc] refutes that.  The two facts are not in
   tension only because of the level gap, and this file states them at
   levels that are MEASURED rather than asserted: see UNIVERSES below, where
   the same constant [Complete] is inhabited at one instance and refuted at
   another.

   The size boundary is the one Adjunction/GAFT.v:101-114 describes and
   Structure/Complete.v:64-76 cites Freyd for: a SMALL complete category is
   a preorder (Structure/Complete/Freyd.v's [small_complete_is_thin]).  The
   category below is a preorder, so it is consistent with Freyd's collapse
   and does not contradict it; what it adds is that being large is what lets
   a small-complete preorder have no top.

   WHAT IS DELIVERED (41 declaration heads -- 2 [Inductive], 39
   [Definition]/[Fixpoint]/[Lemma]/[Theorem]/[Example] -- introducing 43
   names once the two constructors [osup] and [opair] are counted;
   [Print Assumptions] reports "Closed under the global context" for all 43
   -- see the PRINT ASSUMPTIONS paragraph).
     (1) THE TYPE AND THE ORDER.  [SmallOrd@{u} : Type@{u+1}] with the single
         constructor [osup : forall Ix : Type@{u}, (Ix -> SmallOrd) ->
         SmallOrd]; the destructors [oidx] (the index type) and [oelt] (the
         indexed family); [ole] by structural recursion on its FIRST
         argument only -- [osup A f <= osup B g] iff every [f a] is below
         some [g b] -- and [olt x y] as "[x] is below some element of [y]".
         [ole_unfold] is the destructor-shaped characterisation; it is the
         one lemma proved by destructing both ordinals, and every later
         proof goes through it instead, which is what keeps the induction
         hypotheses usable.  [ole_refl], [ole_elem] (an element of an
         ordinal precedes it), [ole_trans], and the [PreOrder] instance
         [ole_preorder].  NO antisymmetry is claimed or needed.
     (2) THE THIN CATEGORY.  [SmallOrd_Proset] is [Proset ole_preorder] and
         [SmallOrd_op_Proset] is [Proset (op_PreOrder ole_preorder)] -- the
         same objects with the order reversed, which is what Mac Lane's
         "Ord^op" is.  Hom-sets are subsingletons on the nose:
         [smallord_equiv_is_True] records [(f ≈ g) = True] at [eq_refl], and
         [SmallOrd_Thin] / [SmallOrd_op_Thin] package that as
         Structure/Thin.v's predicate.  [SmallOrd_op_Proset] is used, rather
         than [SmallOrd_Proset^op], because the two categories are NOT
         convertible, and the divergence was LOCATED rather than guessed.
         In a section over an arbitrary [(P : PreOrder R)], under this
         file's import list, [eq_refl] is accepted for
         [obj[Proset (op_PreOrder P)] = obj[(Proset P)^op]] and for the
         same equation at [@hom], [@id], [@compose], and at the [equiv]
         component of the hom-setoid; it is REFUSED at
         [@Setoid.setoid_equiv _ (@homset (Proset (op_PreOrder P)) x y) =
         @Setoid.setoid_equiv _ (@homset ((Proset P)^op) x y)] and hence at
         [@homset] and at the whole [Category] record.  So the obstacle is
         not the category LAWS: it is the [Qed]-opaque [Program] obligation
         inside Instance/Proset.v's hom-setoid, which is one constant
         applied to [P] on one side and to [op_PreOrder P] on the other.
         (Instance/Proset/Limit.v:547 records a DIFFERENT non-equality, of
         [Cocomplete (Proset P)] with [Complete (Proset (op_PreOrder P))];
         it is not this one.)  All the order machinery of
         Instance/Proset/Limit.v is stated over an arbitrary [PreOrder], so
         it applies to the reversed preorder directly and nothing is lost by
         using it.
     (3) SMALL SUPREMA.  [osum]/[opair] is the dependent-pair index type,
         declared here rather than taken from [sigT] so that BOTH components
         stay in [Type@{u}] by declaration instead of by inference;
         [ojoin A f] is [osup] of the disjoint union of the index types of
         the [f a], hence a small ordinal again.  [ojoin_ub] and
         [ojoin_least] say it is a least upper bound, and [ojoin_IsLUB]
         packages that as Instance/Proset/Limit.v's [IsLUB].  Note that
         [osup A f] itself is NOT the supremum of the [f a] -- it is the
         supremum of their successors -- which is why [ojoin] flattens.
         [ozero] is [osup] of the empty family and [ozero_least] makes it a
         bottom; [osucc] is [osup] of a [poly_unit]-indexed family, with
         [ole_osucc], [olt_osucc] and [osucc_not_ole].
     (4) SMALL-COMPLETENESS OF THE OPPOSITE.  [SmallOrd_HasAllJoins :
         HasAllJoins ole] is [ojoin] read through the bound predicates, and
         [SmallOrd_op_Complete : @Complete SmallOrd_op_Proset] is
         Instance/Proset/Limit.v's [Proset_op_Complete_of_all_joins] applied
         to it.  Its measured universe instance is the content: see
         UNIVERSES.  [SmallOrd_op_indexed_limit] is the indexed-product
         reading for a single family ([Proset_LUB_Limit], the shape being
         [DiscreteCat_Functor]), and [SmallOrd_op_Terminal] is the nullary
         case, the terminal object of [SmallOrd^op] being the least ordinal.
         [smallord_lub_not_zero] is the non-vacuity control in the style of
         Instance/Proset/Limit.v:745's [nat_glb_not_4]: [IsLUB] is a
         refutable predicate here, so the positive statements are not
         statements about a uniformly inhabited type.
     (5) NO GREATEST ELEMENT, AND THE UNIVERSE ARGUMENT MADE EXPLICIT.
         [olt_irrefl] (no ordinal is one of its own elements) is the one
         genuinely inductive negative lemma; from it [osucc_not_ole] and
         then [SmallOrd_no_greatest : forall m, ¬ forall x, ole x m].  The
         categorical readings are [SmallOrd_no_Terminal] and
         [SmallOrd_op_no_Initial].  Two further statements isolate WHERE the
         level gap does the work:
           - [SmallOrd_no_small_cofinal_family]: there is no [A : Type@{u}]
             and [e : A -> SmallOrd@{u}] with every ordinal below some
             [e a].  So [SmallOrd@{u}] is not cofinally [Type@{u}]-small --
             the sup construction of (3) cannot be applied to the whole
             class, and this is the precise sense in which (4) and (5) are
             compatible.
           - [SmallOrd_op_no_self_limit] and
             [SmallOrd_op_not_large_complete]: the identity diagram on
             [SmallOrd_op_Proset] has no limit, since a cone over it is a
             greatest element; hence [Complete] read with the DIAGRAM shape
             at the category's own object level is refuted, while (4)
             inhabits [Complete] with the diagram shape one level down.
             The two are instances of one constant at two universe
             instances, printed below.

   UNIVERSES (every line below is an [About] reading taken under
   [Set Printing Universes] on the compiled file; the constraint blocks are
   quoted verbatim except where a line says which entries are elided).
     - 27 of the 43 names carry an EMPTY constraint block over a single
       universe [u]: [SmallOrd@{u} : Type@{u+1}], [osup], [oidx@{u} :
       SmallOrd@{u} -> Type@{u}], [oelt], [ole@{u} : SmallOrd@{u} ->
       SmallOrd@{u} -> Prop], [ole_unfold], [ole_refl], [ole_elem],
       [ole_trans], [olt], [olt_ole], [olt_irrefl], [osum], [opair],
       [ojoin@{u} : forall A : Type@{u}, (A -> SmallOrd@{u}) ->
       SmallOrd@{u}], [ojoin_ub], [ojoin_least], [ozero], [ozero_least],
       [osucc], [ole_osucc], [olt_osucc], [osucc_not_ole],
       [SmallOrd_no_greatest@{u}], [SmallOrd_no_small_cofinal_family@{u}],
       [oidx_osup], [oelt_osup].  Nothing is identified with anything and
       [u] is free: the entire order theory, including both negative
       theorems of section 5, is one-universe.
     - [ole_preorder@{u} : PreOrder ole@{u}] is the first constant to leave
       that block, and it leaves it only for [u < RelationClasses.Defs.u0]
       -- the stdlib's own level for [PreOrder], not a level of this
       development.
     - [SmallOrd_Proset@{u u0 u1} : Category@{u u0 u0}] with [u1 < u]
       (the rest of its block is [u1 < RelationClasses.Defs.u0],
       [u <= RelationClasses.Defs.u0],
       [u <= Relation_Definitions.Relation_Definition.u0]).  Here [u1] is
       the ordinals' own universe and [u] the category's object universe:
       the category is LARGE by exactly one level, by construction and not
       by accident.  [SmallOrd_op_Proset] and [SmallOrd_op_Terminal] have
       the same signature shape.
     - [SmallOrd_HasAllJoins@{u u0 u1 u2 u3} : HasAllJoins@{u u0 u0 u1 u2 u3}
       ole@{u1}] with [u1 < u], [u <= u0], [u2 <= u0] (and
       [u <= Relation_Definitions.Relation_Definition.u0]).  The index
       universe of [HasAllJoins] -- its fourth binder, and the THIRD of
       [HasAllMeets], which [HasAllJoins] instantiates -- is
       [u1], the ordinals' own universe, one level BELOW the [u] at which
       [SmallOrd@{u1}] itself lives.  That identification is what makes the
       next line say "small", and it is forced by [ojoin], which accepts
       only a [Type@{u1}]-indexed family.
     - THE SLOT DECODER, so that the two [Complete] readings below can be
       compared without guessing.  [SmallOrd_op_indexed_limit@{u u0 u1 u2 u3}]
       reads [forall (A : Type@{u}) (d : A -> SmallOrd@{u}),
       Limit@{u u Set u0} (DiscreteCat_Functor@{u u0 u1 Set} d)] with
       [u < u0].  Its diagram shape is [DiscreteCat A] with [A : Type@{u}]
       and its ambient category is [SmallOrd_op_Proset] at object level
       [u0]; so in [Limit@{a b c d}] the SECOND slot is the shape's object
       universe, the THIRD the shared hom universe, and the FOURTH the
       ambient category's object universe.  [Complete@{a b c d} :
       Category@{d c c} -> Type] follows the same layout.
     - [SmallOrd_op_Complete@{u u0 u1 u2 u3 u4 u5} : Complete@{u u Set u0}]
       with [u < u0] among its constraints.  Read through the decoder: the
       diagram shape's objects sit at [u] and the ambient category's at
       [u0], with [u < u0] between them.  That is small-completeness, in the
       only vocabulary the library has for it.
     - [SmallOrd_op_not_large_complete@{u u0 u1 u2} : Complete@{u u1 u2 u1}
       -> False] with [u0 < u1], [u1 <= u], [u2 <= u].  The second and
       fourth slots are now the SAME universe [u1]: the diagram shape
       ranges over the ambient category's own object level.  Compare the
       previous line, where they are [u] and [u0] with [u < u0] between.
       One constant, inhabited at one instance and refuted at another: that
       is the universe argument, printed rather than narrated.
       [SmallOrd_op_no_self_limit@{u u0 u1 u2} : Limit@{u u1 u2 u1}
       Id@{u1 u2} -> False] is the same reading one layer down.
     - Stdlib levels reached.  [Proset] carries [RelationClasses.Defs.u0]
       and [Relation_Definitions.Relation_Definition.u0], inherited by
       every category-level constant here.  [SmallOrd_op_Complete]
       additionally carries, from [Proset_op_Complete_of_all_joins],
       [JMeq.JMeq.u0 <= JMeq.JMeq.u1], [u <= eq.u0],
       [u <= Logic_lemmas.equality.u0], several [projections]/[Projections]
       bounds and four [Set < ...] bounds.  Those are level constraints
       only: [Print Assumptions] on all 43 names reports "Closed under the
       global context", with no [Axioms:] line anywhere.
     - Instance/Discrete.v's [DiscreteCat_Functor] does NOT pin the SOURCE
       SHAPE's objects to [Set] here, which is worth recording because
       issue #1309 tracks exactly that artifact for a neighbouring use.
       Measured: [DiscreteCat_Functor@{u u0 u1 Set} d] in
       [SmallOrd_op_indexed_limit] has the shape's object universe at [u],
       the family's own, with [Set] only in the fourth slot and a
       [Set < u1] side constraint; likewise the [Set] in [Limit@{u u Set u0}]
       is the HOM level, which is harmless because every hom-set of a
       [Proset] and of a [DiscreteCat] is a proposition.  No object type of
       this development is at [Set].

   ONE TRAP WORTH RECORDING.  [I] is the Prelude's constructor of [True], so
   a [match] branch written [osup I f => I] is read with [I] as a PATTERN
   CONSTANT, and the elaborator reports "The term ... is expected to have
   type True" pointing at the binder.  The index binder is therefore named
   [Ix] in the inductive and [A]/[B] in every [match] below.  The message is
   stable under any import list, since it comes from the Prelude.

   PRINT ASSUMPTIONS.  Every one of the 43 names reports "Closed
   under the global context"; there are no [Axioms:] lines.  That includes
   [SmallOrd_op_Complete], which reaches [Proset_op_Complete_of_all_joins]
   and through it Structure/Limit.v and Instance/Discrete.v.

   STALE PREMISES OF ISSUE #444, RE-MEASURED (commands run over the [.v]
   files of the tree excluding [doc/], with [find . -name '*.v' | xargs
   grep], since [grep] here honours [.gitignore] on recursive traversal).
     - "The library has no ordinals as a category ([rg -w 'Ord|OrdCat'] -> a
       lone prose cross-reference in Instance/Proset.v:19)": the CONCLUSION
       is true, the evidence is not.  That figure is not re-measurable and an earlier revision of this
       sentence gave it as "96 hits in 8 files"; re-measured here with the
       command stated, [find . -name '*.v' -not -path './Instance/Ordinal/Large.v'
       | xargs grep -wn 'Ord\|OrdCat' | wc -l], the tree gives 79 matching
       lines (93 occurrences under [grep -wo]).  The exact figure is not the
       point and is recorded only so the sentence can be checked; what matters
       is that the issue's "a lone prose cross-reference" is wrong by two
       orders of magnitude
       category of PREORDERS (Mac Lane's Preord, #372), with satellites
       Instance/Ord/Poset.v, Test/ProbeOrd372.v, Instance/Roster.v,
       Construction/Reflective/Colimit.v, Construction/Subcategory/Dense.v
       and Instance/Top/Kolmogorov.v.  Neither that [Ord] nor
       Instance/Ordinal.v's [Ordinal (n : nat) : Category] (the FINITE
       ordinal [n] read as a category) is a category of ordinals, so no
       existing name is displaced and none is reused; this file's names are
       all prefixed [SmallOrd] or [o] and none of the 43 occurs elsewhere in
       the tree (checked word-wise, with a positive control).
     - "no smallness/largeness machinery": FALSE.  Theory/Size.v:106 has
       [Class LocallySmall], :161 [Class Small], :144
       [locally_small_ambient], :175 [small_locally_small] and :220
       [One_Small].  This file does not consume them -- see NOT DELIVERED --
       but the premise that they are missing is wrong.  The same claim in
       the issue's Awodey §9.8 checkbox ("the library has no smallness or
       local-smallness predicate at all") is wrong for the same reason.
     - "it records no example of a continuous functor without a left adjoint
       ([rg -i 'counterexample|no left adjoint'] -> nothing of this kind)":
       the grep is off (60 hits in more than 20 files), the conclusion
       stands for the sharp reading.  [not representable|continuous yet
       not|continuous but not] has exactly ONE hit in the tree,
       Adjunction/GAFT.v:122, and it is PROSE -- the Joyal/Mac Lane product
       of representables over the simple groups, cited, not built.
       Instance/Sets/NoAdjoint.v's twelve no-adjoint theorems are
       obstructions by limit preservation, a different shape.
     - "Complete Boolean algebras and Solovay's theorem are entirely absent
       ([rg -i 'solovay|complete boolean|CABA'] -> 0 hits)": ONE hit, not
       zero -- Instance/FdVect/NoRightAdjoint.v:104 names Solovay, for the
       Solovay/Shelah measurability result, not for complete Boolean
       algebras.  The conclusion (no complete Boolean algebras, no free-CBA
       theorem) stands.
     - The cited background prose: Adjunction/GAFT.v:101 ff. is the size
       obstruction, as claimed; Structure/Complete.v:64-76 is Freyd's
       collapse, as claimed; Instance/Poset.v:80-87 is NOT the adjoint
       functor discussion -- at those lines the file is on Lawvere's
       enrichment over the truth values.  The intended paragraph is
       Instance/Poset.v:88-95, "Thinness also marks a size boundary in the
       adjoint functor theorems".
     - The dependency on #422 is live: Instance/Proset/Limit.v supplies
       [IsLUB], [HasAllJoins], [Proset_op_Complete_of_all_joins] and
       [Proset_LUB_Limit], all consumed here unchanged.

   NOT DELIVERED.
     - The functor half of the counterexample.  The constant one-point
       functor [SmallOrd^op ⟶ Sets], its continuity, and the refutation of
       its representability are NOT in this file; it supplies the category
       and the two order facts they need ([SmallOrd_op_Complete] and
       [SmallOrd_no_greatest], the latter in the categorical forms
       [SmallOrd_no_Terminal] and [SmallOrd_op_no_Initial]).  The issue
       places that half in Adjunction/GAFT/Necessity.v.
     - The Solovay/complete-Boolean-algebra half of §V.6: untouched.
     - Any connection to Theory/Size.v.  [SmallOrd_Proset] is NOT shown to
       be [LocallySmall] and is NOT shown to be non-[Small]; the largeness
       here is a universe-level fact recorded by [About], not a term of
       Theory/Size.v.  Making it one is a separate piece of work, because
       [Small] asks for a resizing of the OBJECT type and refuting it needs
       an argument that no such resizing exists, which is not what the
       universe gap gives on its own.
     - Antisymmetry, trichotomy, well-foundedness of [olt], ordinal
       arithmetic, the comparison with Instance/Omega.v's ω or with
       Instance/Ordinal.v's finite ordinals: none of it.  [ole] is a
       preorder and nothing more is claimed of it.
     - A [Test/] refutation probe.  The two refusals this file relies on for
       its strength claims (the non-convertibility of
       [Proset (op_PreOrder P)] with [(Proset P)^op], and the universe
       instance separating the two readings of [Complete]) are measured and
       quoted above but are not pinned by a refutation probe, so a later
       change could weaken them silently.  Filing that probe, in the style
       of the [Test/Probe*] files, is outstanding work.
     - No edit to any existing [.v] file.  Four support edits were made and
       are listed here so nothing is smuggled: the [_CoqProject] line; the
       two file counts in CLAUDE.md (981/985 -> 982/986, so that
       [make claude-md-counts-check] stays green) together with the
       [Instance/Ordinal.v] entry of its Order map; one bullet appended to
       docs/INDEX.md under "Concrete Instances" (269 -> 270 bullets, five
       headings before and after, [make index-check] green); and one
       [Print Assumptions] block appended to the Makefile's
       [print-assumptions] gate carrying all 43 names fully qualified. *)

(** ** The type of small ordinals *)

(* An ordinal is a [Type@{u}]-indexed family of ordinals.  The result lives
   at [Type@{u+1}], one level above the types that may index it: that gap
   is the whole subject of this file. *)
Inductive SmallOrd@{u} : Type@{u+1} :=
  osup : forall (Ix : Type@{u}), (Ix -> SmallOrd) -> SmallOrd.

(* The index type of an ordinal, and its indexed family of elements.  The
   index binder is written [A] and never [I]: see the trap recorded in the
   header. *)
Definition oidx@{u} (x : SmallOrd@{u}) : Type@{u} :=
  match x return Type@{u} with osup A _ => A end.

Definition oelt@{u} (x : SmallOrd@{u}) : oidx@{u} x -> SmallOrd@{u} :=
  match x as x0 return (oidx@{u} x0 -> SmallOrd@{u}) with osup _ f => f end.

(* Both destructors compute on a constructor application. *)
Example oidx_osup@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  oidx (osup A f) = A := eq_refl.

Example oelt_osup@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  oelt (osup A f) = f := eq_refl.

(** ** The extensional order *)

(* [x <= y] when every element of [x] is dominated by some element of [y].
   The recursion is structural in the FIRST argument alone -- the inner
   [match] on [y] is a case analysis, not a recursive call -- which is what
   keeps the definition inside Coq's guard condition without a mutual
   fixpoint. *)
Fixpoint ole@{u} (x : SmallOrd@{u}) : SmallOrd@{u} -> Prop :=
  match x with
  | osup A f =>
      fun y => match y with
               | osup B g => forall a : A, exists b : B, ole (f a) (g b)
               end
  end.

(* The destructor-shaped reading of [ole].  Every proof below goes through
   this rather than destructing an ordinal, which is what keeps the
   induction hypotheses usable. *)
Lemma ole_unfold@{u} (x y : SmallOrd@{u}) :
  ole x y <-> (forall a : oidx x, exists b : oidx y, ole (oelt x a) (oelt y b)).
Proof. destruct x, y; simpl; split; exact (fun h => h). Qed.

Lemma ole_refl@{u} (x : SmallOrd@{u}) : ole x x.
Proof. induction x as [A f IH]; simpl; intro a; exists a; exact (IH a). Qed.

(* Each element of an ordinal precedes it; equivalently, [osup A f] is an
   upper bound of its own family [f].  It is discharged by the induction
   hypothesis alone, with no case analysis on [f a]. *)
Lemma ole_elem@{u} (x : SmallOrd@{u}) (a : oidx x) : ole (oelt x a) x.
Proof.
  revert a; induction x as [A f IH]; intro a.
  apply ole_unfold; intro a0; exists a; exact (IH a a0).
Qed.

Lemma ole_trans@{u} (x y z : SmallOrd@{u}) : ole x y -> ole y z -> ole x z.
Proof.
  revert y z; induction x as [A f IH]; intros y z Hxy Hyz.
  apply ole_unfold; intro a.
  destruct (proj1 (ole_unfold _ _) Hxy a) as [b Hb].
  destruct (proj1 (ole_unfold _ _) Hyz b) as [c Hc].
  exists c; exact (IH a _ _ Hb Hc).
Qed.

(* A preorder, and deliberately no more: [ole] is not antisymmetric, and a
   thin category needs only reflexivity and transitivity. *)
Definition ole_preorder@{u} : PreOrder ole@{u} :=
  {| PreOrder_Reflexive  := ole_refl@{u}
   ; PreOrder_Transitive := ole_trans@{u} |}.

(* The strict order: [x] precedes some element of [y]. *)
Definition olt@{u} (x y : SmallOrd@{u}) : Prop :=
  exists b : oidx y, ole x (oelt y b).

Lemma olt_ole@{u} (x y : SmallOrd@{u}) : olt x y -> ole x y.
Proof. intros [b Hb]; exact (ole_trans _ _ _ Hb (ole_elem y b)). Qed.

(* No ordinal precedes one of its own elements.  This is the only genuinely
   inductive negative fact in the file, and everything that says "there is
   no top" reduces to it. *)
Lemma olt_irrefl@{u} (x : SmallOrd@{u}) : olt x x -> False.
Proof.
  induction x as [A f IH]; intros [a Ha].
  exact (IH a (proj1 (ole_unfold _ _) Ha a)).
Qed.

(** ** The thin category, and its opposite *)

(* The objects are the small ordinals -- a [Type@{u+1}] -- and a hom-set is
   the PROPOSITION [ole x y]. *)
Definition SmallOrd_Proset : Category := @Proset SmallOrd ole ole_preorder.

(* Mac Lane's [Ord^op], built as the proset of the reversed preorder rather
   than as [SmallOrd_Proset^op].  The two are not convertible: they agree at
   [obj], [hom], [id], [compose] and the hom-setoid's [equiv], and diverge at
   [setoid_equiv], which is a [Qed]-opaque [Program] obligation of
   Instance/Proset.v applied to two different preorders (located, not
   guessed; the measurement is in the header).  Every theorem of
   Instance/Proset/Limit.v is stated over an arbitrary [PreOrder], so
   nothing is lost by building the reversed one directly. *)
Definition SmallOrd_op_Proset : Category :=
  @Proset SmallOrd (op_rel ole) (op_PreOrder ole_preorder).

(* Hom-sets are subsingletons on the nose: the hom-setoid of a proset
   relates any two parallel morphisms by [True], and that holds by
   reduction. *)
Example smallord_equiv_is_True (x y : SmallOrd)
  (f g : x ~{SmallOrd_Proset}~> y) : (f ≈ g) = True := eq_refl.

Definition SmallOrd_Thin : Thin SmallOrd_Proset :=
  fun _ _ _ _ => Logic.I.

Definition SmallOrd_op_Thin : Thin SmallOrd_op_Proset :=
  fun _ _ _ _ => Logic.I.

(** ** Small suprema *)

(* The index type of a join: the disjoint union, over [a : A], of the index
   types of the [f a].  It is declared here rather than taken from [sigT]
   so that both components are held at [Type@{u}] by DECLARATION; that is
   what keeps [ojoin] a small ordinal rather than making its smallness
   depend on how [sigT]'s levels happen to be inferred. *)
Inductive osum@{u} (A : Type@{u}) (B : A -> Type@{u}) : Type@{u} :=
  opair : forall a : A, B a -> osum.

Arguments opair {A B} a b.

(* The supremum of a SMALL family of ordinals.  Note that [osup A f] is not
   itself that supremum -- it is the supremum of the successors of the
   [f a] -- so the construction flattens one level. *)
Definition ojoin@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) : SmallOrd@{u} :=
  osup (osum A (fun a => oidx (f a)))
       (fun p => match p with opair a k => oelt (f a) k end).

Lemma ojoin_ub@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) (a : A) :
  ole (f a) (ojoin A f).
Proof. apply ole_unfold; intro k; exists (opair a k); exact (ole_refl _). Qed.

Lemma ojoin_least@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) (y : SmallOrd@{u})
  (H : forall a, ole (f a) y) : ole (ojoin A f) y.
Proof.
  apply ole_unfold; intros [a k].
  exact (proj1 (ole_unfold _ _) (H a) k).
Qed.

(* The two clauses packaged as Instance/Proset/Limit.v's predicate. *)
Definition ojoin_IsLUB@{u +} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  IsLUB ole f (ojoin A f) :=
  (ojoin_ub A f, fun n Hn => ojoin_least A f n Hn).

(* The least ordinal: the empty family.  [False] serves as the empty index
   type at every level, by cumulativity, so no [Set]-level empty type is
   pinned here. *)
Definition ozero@{u} : SmallOrd@{u} := osup False (fun e => match e with end).

Lemma ozero_least@{u} (x : SmallOrd@{u}) : ole ozero x.
Proof. apply ole_unfold; intros []. Qed.

(* The successor: a one-element family.  [poly_unit] is the library's
   universe-polymorphic unit (Lib/Setoid.v:56); [unit] would pin the index
   type to [Set]. *)
Definition osucc@{u} (x : SmallOrd@{u}) : SmallOrd@{u} :=
  osup poly_unit@{u} (fun _ => x).

Lemma ole_osucc@{u} (x : SmallOrd@{u}) : ole x (osucc x).
Proof. exact (ole_elem (osucc x) ttt). Qed.

Lemma olt_osucc@{u} (x : SmallOrd@{u}) : olt x (osucc x).
Proof. exists ttt; exact (ole_refl x). Qed.

(* The successor is STRICTLY above: this is [olt_irrefl] read at [x]. *)
Lemma osucc_not_ole@{u} (x : SmallOrd@{u}) : ole (osucc x) x -> False.
Proof. intro H; exact (olt_irrefl x (proj1 (ole_unfold _ _) H ttt)). Qed.

(** ** Small-completeness of the opposite category *)

(* Every [Type@{u}]-indexed family of ordinals has a join.  The index
   universe of [HasAllJoins] is the ordinals' OWN universe here, which is
   what turns the next definition into a small-completeness statement; the
   measured instance is quoted in the header. *)
Definition SmallOrd_HasAllJoins : HasAllJoins ole :=
  fun A f => existT _ (ojoin A f) (ojoin_IsLUB A f).

(* Mac Lane's "Ord^op is small-complete".  Every diagram whose shape
   category has objects at the ordinals' own universe -- one level BELOW
   the object type of [SmallOrd_op_Proset] -- has a limit. *)
Definition SmallOrd_op_Complete : @Complete SmallOrd_op_Proset :=
  Proset_op_Complete_of_all_joins ole_preorder SmallOrd_HasAllJoins.

(* The indexed-product reading of one family, through
   Instance/Proset/Limit.v's [Proset_LUB_Limit]: the limit in
   [SmallOrd^op] of a discrete diagram is the join of its objects. *)
Definition SmallOrd_op_indexed_limit@{u +}
  (A : Type@{u}) (d : A -> SmallOrd@{u}) :
  Limit (DiscreteCat_Functor (C:=SmallOrd_op_Proset) d) :=
  Proset_LUB_Limit ole_preorder d (ojoin A d) (ojoin_IsLUB A d).

(* The nullary case: the terminal object of [SmallOrd^op] is the least
   ordinal.  (The INITIAL object of [SmallOrd^op] would be a greatest
   ordinal, and is refuted below.) *)
Definition SmallOrd_op_Terminal : @Terminal SmallOrd_op_Proset :=
  Proset_Terminal (op_PreOrder ole_preorder) ozero ozero_least.

(* Non-vacuity, in the sense of Instance/Proset/Limit.v:745's
   [nat_glb_not_4]: [IsLUB] is refutable here, so the positive statements
   above are not statements about a uniformly inhabited type.  Zero is not
   a join of {zero, zero+1}. *)
Lemma smallord_lub_not_zero@{u +} :
  IsLUB ole@{u} (pair_family ozero@{u} (osucc@{u} ozero@{u})) ozero@{u}
  -> False.
Proof. intros [Hub _]; exact (osucc_not_ole ozero (Hub false)). Qed.

(** ** No greatest ordinal, and where the universe gap does the work *)

(* There is no greatest small ordinal: the successor of a candidate would
   have to precede it, and [olt_irrefl] refutes that. *)
Theorem SmallOrd_no_greatest@{u} (m : SmallOrd@{u})
  (H : forall x : SmallOrd@{u}, ole x m) : False.
Proof. exact (osucc_not_ole m (H (osucc m))). Qed.

(* THE UNIVERSE ARGUMENT, STATED.  [SmallOrd@{u}] has no cofinal family
   indexed by a [Type@{u}]: if it had one, [ojoin] would turn it into a
   greatest element.  So the supremum construction of the previous section,
   which accepts every [Type@{u}]-indexed family, cannot be applied to the
   class of ALL ordinals -- not because the construction is partial, but
   because [SmallOrd@{u} : Type@{u+1}] is not a [Type@{u}] and no
   [Type@{u}] is cofinal in it.  This is the precise sense in which
   small-completeness and the absence of a top are compatible. *)
Theorem SmallOrd_no_small_cofinal_family@{u}
  (A : Type@{u}) (e : A -> SmallOrd@{u})
  (H : forall x : SmallOrd@{u}, exists a : A, ole x (e a)) : False.
Proof.
  apply (SmallOrd_no_greatest (ojoin A e)); intro x.
  destruct (H x) as [a Ha].
  exact (ole_trans _ _ _ Ha (ojoin_ub A e a)).
Qed.

(* The order facts read categorically. *)
Theorem SmallOrd_no_Terminal (T : @Terminal SmallOrd_Proset) : False.
Proof.
  exact (SmallOrd_no_greatest _ (terminal_is_greatest ole_preorder T)).
Qed.

Theorem SmallOrd_op_no_Initial (Iobj : @Initial SmallOrd_op_Proset) : False.
Proof.
  exact (SmallOrd_no_greatest _
           (initial_is_least (op_PreOrder ole_preorder) Iobj)).
Qed.

(* The identity diagram on [SmallOrd^op] has no limit: a cone over it has a
   leg to every object, and in the reversed order that leg family IS the
   statement that the apex is a greatest ordinal.  Only the CONE is used,
   not the universal property. *)
Theorem SmallOrd_op_no_self_limit
  (L : Limit (Id[SmallOrd_op_Proset])) : False.
Proof.
  destruct L as [[v legs] _].
  apply (SmallOrd_no_greatest v); intro x.
  exact (@vertex_map _ _ _ _ legs x).
Qed.

(* Hence [Complete] is refuted when its DIAGRAM shape is allowed to range
   over the category's own object universe -- while
   [SmallOrd_op_Complete] inhabits [Complete] with the diagram shape one
   universe below.  Same constant, two instances; the printed instances are
   quoted in the header's UNIVERSES paragraph, and they are the sharp form
   of Mac Lane's remark that the size discipline is doing real work. *)
Theorem SmallOrd_op_not_large_complete
  (HC : @Complete SmallOrd_op_Proset) : False.
Proof. exact (SmallOrd_op_no_self_limit (HC SmallOrd_op_Proset Id)). Qed.

(** ** The control that keeps the previous theorem from being a triviality

    [SmallOrd_op_not_large_complete] refutes [Complete] at the diagonal
    instance, and a reader is entitled to ask whether that instance is
    uninhabitable for every category, in which case the refutation would say
    nothing about the ordinals.  It is not.  The SAME diagonal shape is
    inhabited in the UNREVERSED order, where [ozero] is a greatest lower
    bound of the identity diagram because it is least:

      About SmallOrd_self_limit  ->  Limit@{u u1 u0 u1} Id[SmallOrd_Proset]

    slots 2 and 4 both [u1], which is the pairing
    [SmallOrd_op_no_self_limit] refutes on the other side.  So the
    refutation is about the absence of a GREATEST ordinal, not about the
    universe pairing being unusable, and that is exactly the content
    Mac Lane's remark needs. *)

Definition SmallOrd_self_limit : Limit (Id[SmallOrd_Proset]) :=
  Proset_Limit_general ole_preorder (Id[SmallOrd_Proset]) ozero
    (ozero_least, fun n Hn => Hn ozero).
