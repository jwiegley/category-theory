Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Orthogonality.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Regular.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Projective and injective objects *)

(* Mac Lane §V.4 Definitions 3 and 4 (book p. 118; maclane:V.4:def3,
   maclane:V.4:def4); Awodey §2.4's prose definition of a projective object
   (awodey:2.4:def-projective).
   nLab: https://ncatlab.org/nlab/show/projective+object
         https://ncatlab.org/nlab/show/injective+object

   BACKGROUND.  An object p is projective when every arrow out of it lifts
   through every epimorphism — equivalently, when the covariant hom-functor
   C(p, −) carries epis to epis, i.e. to surjections of hom-setoids — and q
   is injective when every arrow into it extends along every monomorphism,
   the dual.  These are the two lifting notions under homological algebra
   (enough projectives, resolutions), none of which is built here.

   STALE PREMISES, RE-MEASURED.
     - "No projectivity or injectivity notion exists": TRUE (0 declarations
       matching Projective/Injective; the issue's own occurrence counts are
       off — 'projective' occurs in 9 lines of 6 [.v] files, all prose:
       projective limits (Structure/Limit.v:43/:51, Instance/Sets/
       InverseLimit.v:51), a free module (Instance/Mod/Free.v:175),
       projective geometry (Construction/Opposite.v:27/:40/:43), the
       projective tensor product of Banach spaces (Structure/Closed.v:67) and
       "enough projectives" (Structure/Abelian.v:97, the one line about this
       file's notion); and 'injective' in 437 lines of 100 files, all but
       one the SETOID-MAP notion — Lib/Setoid.v:117 [injective],
       Instance/Sets.v:379 [injectivity_is_monic], Theory/Concrete/
       Morphisms.v:70 [concrete_injective_monic], Adjunction/LeftInverse.v:
       352 [InjectiveOnObjects], … — the exception being Structure/
       Abelian.v:98's "injective resolutions", prose about the categorical
       notion).  (An earlier revision glossed the nine as "limits or modules"
       and the 437 as all setoid-map; corrected to the measured lists.)
     - "No lifting property beyond Theory/Orthogonality.v:43": PARTIAL.
       [Orthogonal e m] (unique filler, two arrows, over [≈]) is also what
       Structure/Factorization/StrongEpi.v:36-39's [strong_lift] and
       Theory/Morphisms/Stability.v's cobase change route through; every
       lifting statement in the tree carries the uniqueness clause, so the
       lift-EXISTENCE notion was indeed absent.
     - "No lemma about hom-functors preserving epis": TRUE (Theory/
       Functor.v:443/:459 has REFLECTION, [faithful_reflects_monic] and
       [faithful_reflects_epic]; Functor/Hom/Limit.v has preservation of
       limits, not of epis).
     - What the issue does not mention and this file rests on:
       Instance/Sets.v:515 [surjectivity_is_epic : (∀ b, ∃ a, h a ≈ b) ↔
       Epic h], BOTH directions, constructively ([surjective_implies_epic]
       :534, [epic_implies_surjective] :538, the latter through the
       cokernel-pair probe of :454-511), which makes both halves of the
       hom-functor characterization provable.
     - "As data or as an ∃-statement, disclosing which": in this library
       there is no choice.  [∃] IS [sigT] (Lib/Foundation.v:61 rebinds
       [exists], :66 defines [∃] from it), and a Prop-valued existential
       over [≈] cannot even be stated, [≈] on morphisms being Type-valued
       (probe N6).  The lift is data, written [∃ h, g ∘ h ≈ f] as
       Structure/Pullback.v's [ump_pullbacks] and Theory/Morphisms.v's
       witnesses already are.

   WHAT IS DELIVERED (45 named constants plus 3 [Program] obligations,
   every one closed under the global context).
     (1) [Projective p] — a [Class] like [Epic]/[Monic], one field
         [projective_lift {b c} (g : b ~> c) (He : Epic g) (f : p ~> c) : ∃ h
         : p ~> b, g ∘ h ≈ f] — with the accessors [proj_lift] /
         [proj_lift_comm].
     (2) [Injective C] as a NOTATION for [@Projective (C^op)] (with the
         [@Injective C] form), the idiom of Structure/Initial.v:97-100 and
         Structure/Cocartesian.v:115-118; covariant accessors
         [injective_extend m Hm f : ∃ h : b ~> q, h ∘ m ≈ f] (through
         Theory/Morphisms/Duality.v:44-58's [op_Epic_of_Monic] — [Monic] in
         C and [Epic] in [C^op] are DISTINCT records, probe N4-N5, though
         the objects and homs of the duality convert), [inj_extend],
         [inj_extend_comm]; readbacks [inj_is_op_proj] and
         [inj_stmt_readback] (the C-facing statement IS the [C^op] one) at
         [eq_refl].
     (3) THE HOM-FUNCTOR CHARACTERIZATION, both directions.
         [proj_is_hom_surjectivity] ([eq_refl]: "surjections of hom-setoids"
         is the definition unfolded, [fmap[[Hom p ,─]] g h = g ∘ h] being
         [hom_fmap_is_postcomp]), [projective_hom_surjective] (Lib/Setoid.v's
         [surjective] class), [projective_hom_epic] (Epic in Sets, by
         [surjective_implies_epic]), [hom_epic_projective] (the converse, by
         [epic_implies_surjective]), and the issue's pinned
         [projective_iff_hom_preserves_epi].  Dually [cohom_is_op_hom]
         ([eq_refl]: [[Hom ─, q]] over C IS [[Hom q ,─]] over [C^op]),
         [injective_cohom_epic], [cohom_epic_injective],
         [injective_iff_cohom_preserves_mono] — each a [:=] of the
         projective form at [C^op] plus one Duality.v bridge.
     (4) ORTHOGONALITY.  [ortho_lift_exists] (Theory/Orthogonality.v's
         [Orthogonal] with its uniqueness clause dropped, one projection);
         and, over an [Initial] object — the arrow whose left lifting
         property is at issue is [zero : 0 ~> p] — [ortho_zero_Projective]
         (orthogonality against every epi gives projectivity) and
         [Projective_ortho_weak] (projectivity gives a filler, not
         necessarily unique, for every such square).  No implication
         between projectivity and [StrongEpi] is claimed: the latter lifts a
         MORPHISM against monos, a different class.
     (5) CLOSURE.  [Retraction_Projective] and [Section_Projective]
         (Theory/Morphisms.v:56/:70's [Section]/[Retraction]; the tree has
         no [Retract] name), [Coprod_Projective] (binary, through
         [merge_comp] / [merge_inl_inr]), [IndexedCoprod_Projective]
         (Structure/Limit/Coproduct.v's [IsIndexedCoproduct], the lift at
         each index chosen by [icoprod_desc] — the case that shows why the
         lift must be data), and the duals [Prod_Injective],
         [Section_Injective], [IndexedProd_Injective], [terminal_obj_Injective]
         as [:=] instantiations at [C^op] with the readbacks
         [op_op_Cartesian : @Cartesian C = @Cocartesian (C^op)] and
         [op_Coprod_is_product] at [eq_refl].
     (6) WITNESSES.  [initial_obj_Projective] (the lift is [zero]),
         [Retraction_lifts] and [every_epi_splits_Projective] (a split epi
         lifts everything), [Sets_Leibniz_Projective : ∀ T : Type, Projective
         (LeibnizSetoid T)] — every setoid whose [≈] is Leibniz equality is
         projective in Sets, CONSTRUCTIVELY: the preimage is
         [epic_implies_surjective]'s and respectfulness is free on a Leibniz
         carrier — and, on the walking arrow, [TwoX_Projective] (through
         [two_X_initial : @Initial _2]) with [TwoY_not_Projective]
         ([TwoXY] is epic, [id[TwoY]] has no lift, Instance/Two.v:128's
         [TwoHom_Y_X_absurd] closes it), packaged as
         [two_projective_not_all]: the property is neither vacuous nor
         universal in one category.  The three witnesses' lifts COMPUTE
         (probe readbacks at [eq_refl]).
     (7) THE PRICE OF "EVERY OBJECT IS PROJECTIVE".
         [Projective_codomain_splits] (the identity lifts, so the epi
         splits), [all_projective_iff_every_epi_splits], and over Sets
         [sets_all_projective_entails_splitting] and
         [sets_all_projective_entails_LEM : (∀ p : Sets, Projective p) → ∀ P
         : Prop, P + (P → False)] through Instance/Sets/Regular.v:242/:256's
         [BlanketSplitting] and its Diaconescu-shaped [blanket_splitting_
         entails_LEM] — "every set is projective" decides every proposition,
         so Awodey's examples of that shape (awodey:2.4:example15,
         awodey:2:ex3) are not discharged here and cannot be constructively.

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 45
   constants).
     - [Projective@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] →
       Type@{max(u,u0)}] with an EMPTY constraint block: C's hom and proof
       levels are identified, and every constant of the file is over a
       [Category@{a b b}] binder with NO equation in its block.  The
       identification is [Epic]'s (and [Monic]'s), not this development's:
       probe N1-N3 refuse [@Epic Cu x y f], [@Monic Cu x y f] and
       [@Projective Cu x] alike under [Constraint vh < vp], with [Cu], its
       hom type and [f] accepted as controls.  Object levels are only
       bounded.
     - The hom characterizations sit at the usual Sets shape:
       [projective_iff_hom_preserves_epi@{u u0 u1 u2 u3}] over [C :
       Category@{u3 u2 u2}] with [u2 < u1] (Sets' object level strictly
       above C's hom level), [injective_iff_cohom_preserves_mono] likewise;
       [IndexedCoprod_Projective] carries [A : Type@{u}] with [u <= u3],
       bounded and identified with nothing; [Sets_Leibniz_Projective@{h p}]
       carries [p < h] ([epic_implies_surjective@{h p}]'s own shape, with
       [A B : SetoidObject@{p p}]) and the stdlib bounds [eq_ind], [eq_ind_r],
       [eq_rect_r], [prod_rect] and [Logic_lemmas.equality] from
       [LeibnizSetoid]'s Leibniz setoid and the surjectivity donor.
     - [Set] appears in exactly five blocks or types, all inherited: the
       four [_2] witnesses ([two_X_initial], [TwoX_Projective],
       [TwoY_not_Projective], [two_projective_not_all]) because [_2]
       (Instance/Two.v:140) is declared bare with a [Set]-valued hom, and
       [sets_all_projective_entails_LEM@{u}] with [Set < u], from
       [bool_setoid_object] inside [blanket_splitting_entails_LEM] — which
       STRENGTHENS the reading: the entailment holds already at [Set]-sized
       carriers.  No other constant names [Set].

   COUNTS AND CONVENTIONS.
     - 45 [.glob] declaration heads (40 [def], 3 [prf], the class [rec] and
       its [proj]) plus 3 [Program] obligations ([LeibnizSetoid] 1,
       [two_X_initial] 2), all "Closed under the global context", zero
       [Axioms:] lines; the gate carries the 45 heads, fully qualified, the
       issue's [Projective], [Injective]'s carrier [injective_extend] and
       [projective_iff_hom_preserves_epi] among them ([Injective] itself is
       a notation, not a constant).
     - Twelve [Defined], each flipped to [Qed] alone in a copy of the file
       with the probe recompiled against it: THREE are load-bearing —
       [Retraction_lifts], [initial_obj_Projective],
       [Sets_Leibniz_Projective], whose lifts the probe reads back at
       [eq_refl] — and the other nine (the hom characterizations, the
       orthogonality and closure constants) compile with the probe unchanged
       and stay transparent because they produce lifts.  Two [Qed]
       ([TwoY_not_Projective], a negation; [two_X_initial]'s uniqueness
       obligation).
     - Closure 34 files excluding self: Structure/Limit/Coproduct.v costs 8
       at the margin (the indexed case), Functor/Hom.v 3, Theory/Morphisms/
       Duality.v 2, Instance/Sets/Regular.v 1, Instance/Two.v 1,
       Structure/Cocartesian.v 1, Theory/Orthogonality.v 1, the other ten
       [Require]s 0.  [[Hom p ,─]] is used directly rather than
       Functor/Hom/Limit.v's [HomFrom], which would add 23 files for the
       same functor (an earlier revision said 12; measured 34 → 57).
       [two_X_initial : @Initial _2] DUPLICATES
       Theory/Equivalence/Strict.v:725's [Two_Initial], whose [Require]
       would add 17 files; the consolidation of both into Instance/Two.v is
       surfaced for the maintainer, not done.  Name collisions: [Projective]
       occurs as a word in Structure/Limit.v's prose ("projective limit"),
       not as a declaration; every other name has 0 occurrences elsewhere.
     - NAME HAZARD, RECORDED.  The [@Injective C] notation claims the lexer
       token [@Injective], as Structure/Initial.v's [@Initial C] and
       Structure/Cocartesian.v's [@Cocartesian C] claim theirs: no constant
       whose name begins with [Injective], [Initial] or [Cocartesian] can be
       written with an [@] prefix while those notations are in scope (probe
       N7-N8; the tree's [InjectiveOnObjects] is currently never written with
       [@]; [@Terminal…] and [@Coproduct…] ARE accepted — no such notation
       exists — an earlier revision listed them as blocked).  The names below
       avoid every blocked prefix.
     - Test/ProbeProjective429.v mirrors the [Require] list and carries 9
       refutation commands (1 instrument + N1-N3 UNIVERSE + N4 CONVERSION +
       N5-N6 TYPING + N7-N8 PARSING), each stripped one at a time in a copy
       of the whole file and each beside its accepted controls; ten
       [eq_refl] readbacks (an earlier revision said eleven, counting the N4
       negative's own [eq_refl]); guard coverage 28 identifier tokens inside
       the refutations / 22 also named outside, comments stripped, with six
       exhaustive exceptions (the keyword, a binder, the three refuted
       declarations' names, the absent name); rename-simulated 5/5 over the
       library names the negatives use ([Projective], [Epic], [Monic],
       [op_Epic_of_Monic], [Category]; module paths excluded), every first
       break on a positive line — the two parsing negatives concern a lexer
       token, so renaming their probe-local placeholders is uninformative
       and is not counted.  [make todo] grows by those 9 lines only (2237 →
       2246 over f86ebdbe, master 1de68608 with #428), so the issue's "adds
       no new hits" box is not met as written; disclosed.  (An earlier
       revision of the probe
       wrote the Prelude's [ex] as [Corelib.Init.Logic.ex], which Coq
       8.19/8.20 do not know — their prelude is [Coq.] — and the Nix source
       builds stopped there; the unqualified name is used now, and the guard
       figure moved from 31/25 to the 28/22 above with it.)

   NOT DELIVERED.
     - Enough projectives, projective or injective resolutions, injective
       hulls, Baer's criterion (Structure/Abelian.v:96-106 frames these as
       background prose; nothing built).
     - Free modules are projective (Instance/Mod/Free.v:175 records the
       absence; it needs that module's machinery).
     - Any relation between projectivity and [StrongEpi] (different
       classes; none holds without further hypotheses).
     - "Every object of Sets is projective" — refuted as a constructive
       goal by (7); Awodey's examples of that shape stay open.
     - Anything registered as an [Instance]: [Projective] is a class, but
       no instance is declared, so nothing becomes globally resolvable.
     - No edit to Theory/Morphisms.v, Theory/Morphisms/Duality.v,
       Theory/Orthogonality.v, Instance/Sets.v, Instance/Sets/Regular.v or
       Instance/Two.v. *)

Class Projective {C : Category} (p : C) := {
  projective_lift {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) :
    ∃ h : p ~> b, g ∘ h ≈ f
}.

Definition proj_lift {C : Category} {p : C} `{P : @Projective C p}
  {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) : p ~> b :=
  `1 (projective_lift g He f).

Definition proj_lift_comm {C : Category} {p : C} `{P : @Projective C p}
  {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) :
  g ∘ proj_lift g He f ≈ f :=
  `2 (projective_lift g He f).

Notation "'Injective' C" := (@Projective (C^op))
  (at level 9) : category_theory_scope.
Notation "@Injective C" := (@Projective (C^op))
  (at level 9) : category_theory_scope.

Definition injective_extend {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) :
  ∃ h : b ~> q, h ∘ m ≈ f :=
  @projective_lift (C^op) q Q b a m (op_Epic_of_Monic m Hm) f.

Definition inj_extend {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) : b ~> q :=
  `1 (injective_extend m Hm f).

Definition inj_extend_comm {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) :
  inj_extend m Hm f ∘ m ≈ f :=
  `2 (injective_extend m Hm f).

Example inj_is_op_proj {C : Category} (q : C) :
  @Injective C q = @Projective (C^op) q := eq_refl.

Example inj_stmt_readback {C : Category} {q a b : C} (m : a ~> b) (f : a ~> q) :
  (∃ h : b ~{C}~> q, h ∘[C] m ≈ f)
    = (∃ h : q ~{C^op}~> b, m ∘[C^op] h ≈ f) := eq_refl.

(** ** The hom-functor characterization *)

Example hom_fmap_is_postcomp {C : Category} (p : C) {b c : C} (g : b ~> c)
  (h : p ~> b) : fmap[[Hom p ,─]] g h = g ∘ h := eq_refl.

(* The "surjections of hom-setoids" reading is the DEFINITION unfolded: the
   lifting clause and the surjectivity of [fmap] agree at [eq_refl]. *)
Example proj_is_hom_surjectivity {C : Category} (p : C) {b c : C}
  (g : b ~> c) :
  (∀ f : p ~> c, ∃ h : p ~> b, fmap[[Hom p ,─]] g h ≈ f)
    = (∀ f : p ~> c, ∃ h : p ~> b, g ∘ h ≈ f) := eq_refl.

Definition projective_hom_surjective {C : Category} {p : C}
  (P : @Projective C p) {b c : C} (g : b ~> c) (He : Epic g) :
  surjective (fmap[[Hom p ,─]] g) :=
  {| surj := fun f => @projective_lift C p P b c g He f |}.

Theorem projective_hom_epic {C : Category} {p : C} (P : @Projective C p)
  {b c : C} (g : b ~> c) (He : Epic g) :
  @Epic Sets _ _ (fmap[[Hom p ,─]] g).
Proof.
  apply surjective_implies_epic.
  intro f.
  exact (@projective_lift C p P b c g He f).
Defined.

Theorem hom_epic_projective {C : Category} (p : C)
  (H : ∀ (b c : C) (g : b ~> c), Epic g → @Epic Sets _ _ (fmap[[Hom p ,─]] g)) :
  @Projective C p.
Proof.
  construct.
  exact (epic_implies_surjective (fmap[[Hom p ,─]] g) (H b c g He) f).
Defined.

Definition projective_iff_hom_preserves_epi {C : Category} (p : C) :
  @Projective C p
    ↔ (∀ (b c : C) (g : b ~> c), Epic g → @Epic Sets _ _ (fmap[[Hom p ,─]] g)) :=
  (fun P b c g He => @projective_hom_epic C p P b c g He,
   @hom_epic_projective C p).

(* The dual, at C^op: [Hom ─,q] over C IS [Hom q,─] over C^op, definitionally. *)
Example cohom_is_op_hom {C : Category} (q : C) :
  @Curried_CoHom C q = @Curried_Hom (C^op) q := eq_refl.

Definition injective_cohom_epic {C : Category} {q : C} (Q : @Injective C q)
  {a b : C} (m : a ~> b) (Hm : Monic m) :
  @Epic Sets _ _ (fmap[[Hom ─, q]] m) :=
  @projective_hom_epic (C^op) q Q b a m (op_Epic_of_Monic m Hm).

Definition cohom_epic_injective {C : Category} (q : C)
  (H : ∀ (a b : C) (m : a ~> b), Monic m → @Epic Sets _ _ (fmap[[Hom ─, q]] m)) :
  @Injective C q :=
  @hom_epic_projective (C^op) q
    (fun b a m Hm => H a b m (@Monic_of_op_Epic C a b m Hm)).

Definition injective_iff_cohom_preserves_mono {C : Category} (q : C) :
  @Injective C q
    ↔ (∀ (a b : C) (m : a ~> b), Monic m →
         @Epic Sets _ _ (fmap[[Hom ─, q]] m)) :=
  (fun Q a b m Hm => @injective_cohom_epic C q Q a b m Hm,
   @cohom_epic_injective C q).

(** ** Orthogonality: the unique-filler strengthening *)

Definition ortho_lift_exists {C : Category} {a b x y : C}
  (e : a ~> b) (m : x ~> y) (O : Orthogonal e m)
  {u : a ~> x} {v : b ~> y} (comm : m ∘ u ≈ v ∘ e) :
  ∃ d : b ~> x, (d ∘ e ≈ u) ∧ (m ∘ d ≈ v) :=
  (unique_obj (ortho_lift comm); unique_property (ortho_lift comm)).

Definition ortho_zero_Projective {C : Category} `{I : @Initial C} (p : C)
  (H : ∀ (b c : C) (g : b ~> c), Epic g → Orthogonal (zero (x:=p)) g) :
  @Projective C p.
Proof.
  construct.
  destruct (ortho_lift_exists _ _ (H b c g He) (u:=zero) (v:=f)
              (ltac:(apply zero_unique))) as [d [_ Hd]].
  exists d; exact Hd.
Defined.

Definition Projective_ortho_weak {C : Category} `{I : @Initial C} {p : C}
  (P : @Projective C p) {b c : C} (g : b ~> c) (He : Epic g)
  (u : @initial_obj C I ~> b) (v : p ~> c) (comm : g ∘ u ≈ v ∘ zero) :
  ∃ d : p ~> b, (d ∘ zero ≈ u) ∧ (g ∘ d ≈ v).
Proof.
  destruct (@projective_lift C p P b c g He v) as [d Hd].
  exists d; split; [ apply zero_unique | exact Hd ].
Defined.

(** ** Closure facts *)

Definition Retraction_Projective {C : Category} {p q : C} (r : p ~> q)
  (R : Retraction r) (P : @Projective C p) : @Projective C q.
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ r)) as [h Hh].
  exists (h ∘ retract).
  rewrite comp_assoc, Hh, <- comp_assoc, retract_comp; cat.
Defined.

Definition Section_Projective {C : Category} {p q : C} (s : q ~> p)
  (S : Section s) (P : @Projective C p) : @Projective C q.
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ section)) as [h Hh].
  exists (h ∘ s).
  rewrite comp_assoc, Hh, <- comp_assoc, section_comp; cat.
Defined.

Definition Coprod_Projective {C : Category} `{O : @Cocartesian C} {p q : C}
  (P : @Projective C p) (Q : @Projective C q) :
  @Projective C (@Coprod C O p q).
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ inl)) as [h1 H1].
  destruct (@projective_lift C q Q b c g He (f ∘ inr)) as [h2 H2].
  exists (h1 ▽ h2).
  rewrite <- merge_comp, H1, H2, merge_comp, merge_inl_inr; cat.
Defined.

Definition IndexedCoprod_Projective {C : Category} {A : Type} (fam : A → C)
  (s : C) (inj : ∀ a : A, fam a ~> s) (H : IsIndexedCoproduct fam s inj)
  (P : ∀ a : A, @Projective C (fam a)) : @Projective C s.
Proof.
  construct.
  pose (lifts := fun a : A =>
          @projective_lift C (fam a) (P a) b c g He (f ∘ inj a)).
  pose (D := @icoprod_desc C A fam s inj H b (fun a => `1 (lifts a))).
  pose (E := @icoprod_desc C A fam s inj H c (fun a => f ∘ inj a)).
  exists (unique_obj D).
  transitivity (unique_obj E).
  - symmetry; apply (uniqueness E).
    intro a.
    rewrite <- comp_assoc, (unique_property D a).
    exact (`2 (lifts a)).
  - apply (uniqueness E).
    intro a; reflexivity.
Defined.

(** ** The injective duals, by instantiation at C^op *)

Example op_op_Cartesian {C : Category} : @Cartesian C = @Cocartesian (C^op) :=
  eq_refl.

Example op_Coprod_is_product {C : Category} `{O : @Cartesian C} (p q : C) :
  @Coprod (C^op) O p q = @product_obj C O p q := eq_refl.

Definition Prod_Injective {C : Category} `{O : @Cartesian C} {p q : C}
  (P : @Injective C p) (Q : @Injective C q) :
  @Injective C (@product_obj C O p q) :=
  @Coprod_Projective (C^op) O p q P Q.

Definition Section_Injective {C : Category} {p q : C} (s : q ~> p)
  (S : Section s) (P : @Injective C p) : @Injective C q :=
  @Retraction_Projective (C^op) p q s (op_Retraction_of_Section s S) P.

(* The hypothesis is stated in C's own vocabulary: [IsIndexedCoproduct] over
   [C^op] IS [IsIndexedProduct] over C (Structure/Limit/Coproduct.v:82-84). *)
Definition IndexedProd_Injective {C : Category} {A : Type} (fam : A → C)
  (s : C) (proj : ∀ a : A, s ~> fam a)
  (H : @IsIndexedProduct C A fam s proj)
  (P : ∀ a : A, @Injective C (fam a)) : @Injective C s :=
  @IndexedCoprod_Projective (C^op) A fam s proj H P.

(** ** Witnesses *)

Definition Retraction_lifts {C : Category} {p b c : C} (g : b ~> c)
  (R : Retraction g) (f : p ~> c) : ∃ h : p ~> b, g ∘ h ≈ f.
Proof.
  exists (retract ∘ f).
  rewrite comp_assoc, retract_comp; cat.
Defined.

Definition every_epi_splits_Projective {C : Category}
  (S : ∀ (b c : C) (g : b ~> c), Epic g → Retraction g) (p : C) :
  @Projective C p.
Proof.
  construct.
  exact (Retraction_lifts g (S b c g He) f).
Defined.

Definition initial_obj_Projective {C : Category} `{I : @Initial C} :
  @Projective C (@initial_obj C I).
Proof.
  construct.
  exists zero.
  apply zero_unique.
Defined.

Definition terminal_obj_Injective {C : Category} `{T : @Terminal C} :
  @Injective C (@terminal_obj C T) :=
  @initial_obj_Projective (C^op) T.

Program Definition LeibnizSetoid@{o p} (T : Type@{o}) : SetoidObject@{o p} :=
  {| carrier := T; is_setoid := {| equiv := @eq T |} |}.

Definition Sets_Leibniz_Projective@{h p} (T : Type@{p}) :
  @Projective Sets@{p h} (LeibnizSetoid@{p p} T).
Proof.
  construct.
  unshelve eexists.
  - refine {| morphism :=
                fun t => `1 (epic_implies_surjective@{h p} g He (f t)) |}.
    now intros t t' Ht; rewrite Ht.
  - intro t; simpl.
    exact (`2 (epic_implies_surjective@{h p} g He (f t))).
Defined.

Lemma TwoY_not_Projective : @Projective _2 TwoY → False.
Proof.
  intro P.
  exact (TwoHom_Y_X_absurd
           (`1 (@projective_lift _2 TwoY P TwoX TwoY TwoXY TwoXY_epic id))).
Qed.

Program Definition two_X_initial : @Initial _2 := {| terminal_obj := TwoX |}.
Next Obligation. destruct x; [ exact TwoIdX | exact TwoXY ]. Defined.
Next Obligation. apply Two_thin. Qed.

Definition TwoX_Projective : @Projective _2 TwoX :=
  @initial_obj_Projective _2 two_X_initial.

(* Projectivity is not a vacuous property of _2: it holds at TwoX and not
   at TwoY. *)
Definition two_projective_not_all :
  @Projective _2 TwoX * (@Projective _2 TwoY → False) :=
  (TwoX_Projective, TwoY_not_Projective).

(** ** The price of "every object is projective" *)

(* In any category, projectivity of the codomain of an epi splits it: take
   the identity as the map to lift. *)
Definition Projective_codomain_splits {C : Category} {b c : C} (g : b ~> c)
  (P : @Projective C c) (He : Epic g) : Retraction g :=
  {| retract      := `1 (@projective_lift C c P b c g He id)
   ; retract_comp := `2 (@projective_lift C c P b c g He id) |}.

Definition all_projective_iff_every_epi_splits {C : Category} :
  (∀ p : C, @Projective C p)
    ↔ (∀ (b c : C) (g : b ~> c), Epic g → Retraction g) :=
  (fun HP b c g He => Projective_codomain_splits g (HP c) He,
   fun HS => fun p => @every_epi_splits_Projective C HS p).

(* Over [Sets] that principle is not merely unavailable: it DECIDES EVERY
   PROPOSITION.  Instance/Sets/Regular.v proves [BlanketSplitting → LEM]
   axiom-free by a Diaconescu-shaped countermodel; "every setoid is
   projective" implies [BlanketSplitting] in one line. *)
Definition sets_all_projective_entails_splitting :
  (∀ p : @obj Sets, @Projective Sets p) → BlanketSplitting :=
  fun HP A B a0 f E => Projective_codomain_splits f (HP B) E.

Definition sets_all_projective_entails_LEM :
  (∀ p : @obj Sets, @Projective Sets p) → ∀ P : Prop, (P + (P → False))%type :=
  fun HP => blanket_splitting_entails_LEM
              (sets_all_projective_entails_splitting HP).

