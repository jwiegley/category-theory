Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(** * Freyd's collapse: a small complete category is a preorder *)

(* Mac Lane §V.2 Proposition 3 (book p. 114; maclane:V.2:prop3); Awodey §9.8
   Proposition 9.34 (awodey:9.8:prop34); Riehl §3.7 Proposition 3.7.3
   (riehl:3.7:prop3) and Epilogue §E.1 (riehl:E.1:thm-large-products-poset);
   Riehl's Definition 3.7.2 (riehl:3.7:def2) is the size measure Prop 3.7.3
   is stated against and is consumed here as an ORDER ([ArrowIndex]), NOT
   delivered as a cardinal — its checkbox is not met as written (see NOT
   DELIVERED).
   nLab: https://ncatlab.org/nlab/show/complete+small+category

   BACKGROUND.  Freyd's argument: were a category with products indexed by
   its own arrow collection to carry two distinct parallel arrows f, g : a
   ⇉ b, the 2^K choices "f or g at each index" would give 2^K arrows into
   the K-fold power of b, more than the K arrows there are in all — Cantor.
   So a small complete category is a preorder, and the completeness that
   matters is that of LARGE categories; Adjunction/GAFT.v:104-105 and
   Instance/Poset.v:92-95 record the consequence for the adjoint functor
   theorems, and Structure/Complete.v:64-77 the statement.  Near-namesakes:
   Structure/Premonoidal/Freyd.v is about Freyd CATEGORIES (premonoidal),
   unrelated; Structure/Limit/FromProducts.v:279 opens a [Section
   ArrowIndex] around its [ArrowIx] index type (section names do not
   survive [End], so there is no clash), and Theory/Size.v:280's [TotalMor]
   is the same idea as a Σ-type — the witness of item (2) uses it.

   STALE PREMISES, RE-MEASURED.  The issue's "Verified ABSENT" paragraph is
   wrong on three of its four clauses; both files postdate the issue text.
     - "no thin-category predicate": Structure/Thin.v:76 [Thin C := ∀ x y
       (f g : x ~> y), f ≈ g], with [Thin_Opposite]/[Opposite_Thin] (:83/:86),
       [thin_preorder] (:136), [thin_PreOrder] (:142) and [HomChoice] (:170),
       all consumed here.
     - "no smallness predicate, no global arrow-set": Theory/Size.v:106
       [LocallySmall], :161 [Small], :280 [TotalMor C := {x & {y & x ~> y}}];
       Adjunction/SAFT.v:56's "NO size / smallness machinery" is stale as to
       smallness.  [Small] is deliberately NOT consumed (below).
     - "no cardinality vocabulary beyond the finite counter": true, and
       none is added — but the counter is Theory/Metacategory.v:434
       [cardinality] (the issue says :415), its note "counts the identity
       arrows" is at :114 (not :102), [ThreeArrows_card_3] at :466 (not
       :447), and it counts OBJECTS, so it is not Riehl 3.7.2 either.
     - The Cantor step is in the tree: Instance/Fun/Discrete.v:524
       [cantor_predicates], :536 [cantor_bool] (four lines).  A Structure/
       file does not require Instance/Fun, so [freyd_cantor_bool] below is a
       named twin; relocating the original to Lib/ is surfaced, not done.
     - #422 has landed: Instance/Proset/Limit.v:485
       [proset_Complete_iff_all_meets], consumed by item (7).
     - Decidable object equality is in the tree: Construction/Quotient.v:163
       [ObjDecEq] (a definitional class; [obj_uip] at :167 is [UIP_dec] on
       it), consumed by item (2).  An earlier revision declared a duplicate
       [DecObj] with the same statement; the audit found the twin.
     - Prose locations: the Freyd paragraph of Structure/Complete.v is
       :64-77 (issue: :63-72), the Hyland caveat :102-112 (issue: :99-106),
       Instance/Poset.v's sentence :92-95 (issue: :83-86); GAFT.v:104-105
       is right.  Still absent, measured: [SmallCategory]/[is_small] (0
       hits), a morphism cardinal, and any [Complete C → HasIndexedProducts]
       bridge (every consumer builds its product by hand, e.g. SAFT.v:184).

   WHAT IS DELIVERED (38 constants, every one closed under the global
   context).
     (1) THE SMALLNESS WITNESS.  [ArrowIndex C]: a type [ai_index] with an
         encoding of every arrow and a decoding RELATIVE TO A DEFAULT whose
         round trip is the identity up to [≈] for every default — i.e.
         |hom x y| ≤ |ai_index| for every inhabited hom-set, Riehl's
         "products of families as large as its own cardinality", so the
         theorem covers large categories and discharges her §3.7 stronger
         hypothesis; the dual [ArrowIndex_op] is field for field the same
         data (EMPTY constraint block), through [@Build_ArrowIndex (C^op)]
         because the anonymous literal is refused (probe N2), and it is an
         involution at [eq_refl] (probe).  No cardinal ARITHMETIC is
         introduced: the proof consumes the ORDER "no bigger than K", which
         is what Riehl's Definition 3.7.2 is used for; disclosed as such.
         Theory/Size.v's [Small] is not consumed: it resizes per hom-set
         through [ObjEq] transports, and the proof needs one index type for
         all arrows.
     (2) THE WITNESS IS NOT VACUOUS.  Over Construction/Quotient.v:163's
         [ObjDecEq C] (decidable object equality), [td]/[td_enc] (decode a
         bundled arrow at requested endpoints, round trip by
         Coq.Logic.Eqdep_dec's [UIP_dec] — a theorem, not an axiom),
         [canonical_ArrowIndex : ObjDecEq C → ArrowIndex C] at index
         [TotalMor C].  Every category with decidable object equality has an
         [ArrowIndex], thin or not; the strength of the theorem sits in the
         products at that index.  (The terminal category satisfies all
         three hypotheses of item (6), so they are jointly satisfiable; no
         non-trivial in-tree instance is exhibited.)
     (3) THE CONSTRUCTIVE KERNEL.  Section [FreydCore] consumes ONE
         elementary [IsIndexedProduct (fun _ : K => b) P pr] and a boolean
         separator [sep] of the pair ([sep_resp], [sep f = true], [sep g =
         false]): [fr_mk] (the 2^K arrows), [fr_decode]/[fr_decode_mk]
         (read the choice back), [fr_rd]/[fr_rd_enc] (the index surjects
         onto [a ~> P]), [fr_Fam_surjective] (hence onto [K → bool]), and
         [freyd_no_separated_pair : False] by [freyd_cantor_bool].  No
         axiom, no excluded middle, no decidability, no [Set].
     (4) THINNESS FROM DECIDABLE HOMS.  [DecHom C := ∀ x y (u v : x ~> y),
         (u ≈ v) + (u ≈ v → False)] (a [sum]: [≈] is Type-valued,
         Lib/Setoid.v), the separator [fr_sep h := if D h f then true else
         false] with [fr_sep_resp]/[fr_sep_f]/[fr_sep_g], and
         [freyd_thin : ArrowIndex C → HasIndexedProducts C → DecHom C →
         Thin C]; [freyd_thin_canonical] at [ObjDecEq]; [DecHom_op] and
         [freyd_thin_dual] (products in [C^op], Riehl §E.1's "or
         coproducts", via [Opposite_Thin]).
     (5) THE WALL, LOCATED.  From [f ≉ g] ALONE — no separator, no
         decidability — [fr_mk_injective] (injective up to [≈]) and
         [fr_inj_injective]: an injection [(K → bool) → K] on the nose.
         Refuting it needs a left inverse, i.e. testing at each index
         whether the leg is f or g, i.e. [DecHom]; the Russell/Cantor
         no-injection argument for Prop-valued families (stated by no
         in-tree constant — Instance/Fun/Discrete.v:524's
         [cantor_predicates] is the surjection form) is not available
         because the family needs a BOOLEAN choice.  This is exactly
         Hyland's effective-topos
         counterexample (Structure/Complete.v:102-112): the theorem is NOT
         constructively provable without [DecHom], which is why the
         decider is an explicit hypothesis and [Print Assumptions] stays
         closed.  The probe carries the injection as a positive control
         and no refutation, since unprovability is metatheoretic.
     (6) FROM [Complete], WITHOUT A [Set] PIN.  Section [CompleteBridge]:
         [complete_iprod_obj]/[complete_iprod_proj]/[complete_iprod :
         IsIndexedProduct d …] for any [d : A → C], through
         Structure/Limit/Comparison.v's annotated [DiscreteCat_Functor'] and
         [discrete_IsIndexedProduct_of_IsLimitCone]; the unannotated route
         pins C's hom level to [Set] (probe N1, "Cannot enforce Set = uh"),
         and the carrier of that pin is Structure/Limit/Product.v:119's
         [limit_is_indexed_product], whose binder is [C : Category@{_ Set
         Set}] — [DiscreteCat_Functor]'s own binder leaves C free; it
         emits a shape with [Set] homs, and the limit vocabulary identifies
         the shape's hom level with the ambient's (the equations of the
         UNIVERSES section below).  This is the [Complete →
         IsIndexedProduct] bridge the tree lacked.  Then the issue's pinned
         [small_complete_is_thin : ArrowIndex C → Complete C → DecHom C →
         Thin C] and [small_cocomplete_is_thin] (Riehl §E.1's cocomplete
         half, via Construction/Product/Limit.v:389's
         [Complete_op_of_Cocomplete]).
     (7) THE SECOND HALF: GREATEST LOWER BOUNDS.  [complete_has_glbs :
         Complete C → HomChoice C → HasAllMeets (thin_preorder C)]: a
         product IS a greatest lower bound in the preorder reflection of
         ANY category — neither smallness nor thinness enters, which is why
         the issue's pinned NAME [small_complete_has_glbs] is not declared
         (a name asserting a hypothesis the statement does not use).  The
         one hypothesis is [HomChoice] (Structure/Thin.v:170): the lower
         bounds arrive [inhabited]-squashed and the mediator needs the
         arrows.  [complete_Proset_Complete : Complete C → HomChoice C →
         Complete (Proset (thin_PreOrder C))] closes the loop with #422's
         [proset_Complete_iff_all_meets].
     (8) PROSE.  Structure/Complete.v:64-77 now points at
         [small_complete_is_thin]/[complete_has_glbs] and :102-112 names
         [DecHom] as the constructive hypothesis — both edits LINE-NEUTRAL,
         so Instance/Sets/Products.v:160's citation of ":64-72" still
         lands on Freyd's statement.  GAFT.v:104-105 and Poset.v:92-95 are
         untouched (pointers surfaced, not added).

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 38
   constants).
     - 35 of the 38 blocks carry no universe equation.  The three of
       section [CompleteBridge] — [complete_iprod], [complete_iprod_obj],
       [complete_iprod_proj] — each carry [o = u0], [h = p], [h = uh],
       [h = up] and [uh = up]: the limit vocabulary identifies the shape's
       hom and proof levels with C's and the shape's object level with
       [Complete]'s index, the fact Adjunction/SAFT.v:138-139 records in
       prose and the FromProducts.v bullet as [u2 = u4].  No equation
       reaches the kernel, [freyd_thin], [small_complete_is_thin],
       [complete_has_glbs] or [complete_Proset_Complete].  (An earlier
       revision said "NO universe equation in any block"; the audit
       measured these five.)  [ArrowIndex@{u u0 u1} : Category@{u0 u1 u1}
       → Type@{max(u+1,u0,u1)}] and [ArrowIndex_op@{u u0 u1}] carry EMPTY
       blocks — the index level [u] is unrelated to C's levels; [DecHom],
       [DecHom_op] and [fr_sep] carry only the bounds [u0 <= u], [u1 <= u]
       placing C's levels below the result sort.
     - The kernel carries no stdlib bound at all: [freyd_no_separated_pair
       @{u u0 u1 u2} : ∀ {C : Category@{u u0 u0}} (AI : ArrowIndex@{u1 u u0}
       C) …, IsIndexedProduct@{u1 u2 u u0} …] with [u0 <= u2], [u1 <= u2]
       only.  [freyd_thin@{u u0 u1 u2 u3}] adds only [False_rect.u0].
     - The canonical witness: [td] is bounded by [eq_rect.u0/u1] and
       [Projections.u0/u1] only; [td_enc], [canonical_ArrowIndex] and
       [freyd_thin_canonical] add [Eqdep_dec.UIP_dec.u0] and [eq_rect_r.u1]
       — the price of [UIP_dec] (an earlier revision put [UIP_dec] on [td]
       too and omitted [Projections]).  [fr_inj_injective] carries
       [eq_rect.*]/[eq_rect_r.u1] (rewriting on [=]).
     - The [Complete]-fed constants ([complete_iprod_obj/proj],
       [complete_iprod], [small_complete_is_thin], [small_cocomplete_is_thin],
       [complete_has_glbs], [complete_Proset_Complete]) inherit [JMeq.u0 <=
       JMeq.u1], [EqdepFacts.eq_sigT_sig_eq.u2] and [eq_rect_r.u1] bounds
       through [DiscreteCat_Functor'] (Comparison.v's header attributes them
       to its Program auxiliary), plus [eq.u0], [eq_ind.u0],
       [Logic_lemmas.equality.u0] on the shape levels.
     - [small_complete_is_thin@{u u0 u1 u2 u3} : ∀ {C : Category@{u2 u3 u3}},
       ArrowIndex@{u0 u2 u3} C → Complete@{u u0 u3 u2} → DecHom@{u1 u2 u3} C
       → Thin@{u1 u2 u3} C] with [u0 <= u] (the index level sits below the
       shape-object level [Complete] quantifies over) and no [Set].
     - The ONLY [Set] in any block: [complete_Proset_Complete] concludes
       [Complete@{u u Set u0}] — the hom level of [Proset], whose homs are
       Props, inherited from Instance/Proset/Limit.v:485's statement.

   COUNTS AND CONVENTIONS.
     - 38 constants (19 [def], 14 [prf], 4 [proj], 1 [rec] DECLARATION
       entries in the [.glob]; the constructor [Build_ArrowIndex] appears
       there only as an [R … constr] reference, so it is not among the 38;
       an earlier revision counted 39 with the duplicate [DecObj]), all
       "Closed under the global context", zero [Axioms:] lines, all gated
       fully qualified.  Thirteen [Qed]; one [Defined] ([complete_has_glbs],
       data: [HasAllMeets] is [sigT]-valued), which flips to [Qed] freely
       and is kept [Defined] by the data convention.
     - Closure 72 files excluding self: Instance/Proset/Limit.v costs 23 at
       the margin (item (7)'s vocabulary and #422's theorem),
       Structure/Limit/Comparison.v 7, Construction/Product/Limit.v 4,
       Construction/Quotient.v, Structure/Thin.v and Theory/Size.v 1 each,
       the other ten [Require]s 0 (an earlier revision also required
       Category.Theory.Functor, the one droppable [Require]; dropped).  No
       collision: each new name has 0 declaration hits elsewhere in the
       tree.
     - Test/ProbeFreyd423.v mirrors the [Require] list and carries 3
       refutation commands (1 instrument + N1 UNIVERSE + N2 TYPING), each
       stripped one at a time in a copy of the whole file; the involution
       readback at [eq_refl]; three positive controls (the canonical
       witness, the injection of item (5), [Small] coexisting with products
       over the category's own arrows); guard coverage 25 identifier tokens
       inside the refutations / 14 also named outside, comments stripped,
       with eleven exhaustive exceptions (the keyword, seven binder names
       and keywords of the record literal, the notation token [op], the
       refuted declaration's name, the absent name); rename-simulated 6/6
       ([ArrowIndex], [DiscreteCat_Functor], [limit_is_indexed_product],
       [TotalMor], [ai_dec_enc], [complete_iprod], each renamed throughout
       a copy) with every first break on a positive line.  [make todo]
       grows by those 3 lines only (2209 → 2212), so the issue's "adds no
       new hits" box is not met as written; disclosed.

   NOT DELIVERED.
     - Thinness WITHOUT [DecHom]: not provable here (Hyland), and the wall
       is pinned positively by [fr_inj_injective]; the issue's "scope it
       classically" remedy is replaced by the explicit hypothesis, which
       keeps the file axiom-free.
     - The issue's pinned [small_complete_has_glbs] under that name: the
       statement needs no smallness (item (7)), so it is [complete_has_glbs].
     - A cardinal number for a category's morphisms (Riehl 3.7.2 as
       arithmetic): only the order hypothesis [ArrowIndex] is introduced,
       so the issue's riehl:3.7:def2 checkbox is NOT met as written
       (disclosed beside the [make todo] box).
     - A non-trivial in-tree category satisfying [ArrowIndex] + [Complete]
       + [DecHom] (the terminal category does, trivially); the theorem is
       conditional, and docs/INHABITATION.md is not edited here.
     - A [HasIndexedProducts C] CLASS instance from [Complete C]: only the
       elementary [IsIndexedProduct] per family is built (item (6)), which
       is what the kernel consumes; the class's single index universe was
       not attempted.
     - Relocating Instance/Fun/Discrete.v's [cantor_bool] to Lib/; pointers
       in Adjunction/GAFT.v and Instance/Poset.v (surfaced for John).
     - No edit to Structure/Thin.v, Theory/Size.v, Instance/Proset/Limit.v,
       Structure/Limit/Comparison.v or Instance/Fun/Discrete.v. *)

(** ** The Cantor step, as a boolean diagonal *)

(* Twin of Instance/Fun/Discrete.v:536's [cantor_bool], re-proved here
   because a Structure/ file does not require Instance/Fun.  Relocating the
   original to Lib/ is surfaced, not done. *)
Theorem freyd_cantor_bool {A : Type} (f : A → A → bool) :
  ¬ (∀ g : A → bool, exists a : A, ∀ x : A, f a x = g x).
Proof.
  intro H.
  destruct (H (fun x => negb (f x x))) as [a Ha].
  specialize (Ha a).
  destruct (f a a); discriminate.
Qed.

(** ** The smallness witness the proof consumes *)

(* [ai_index] is a single type indexing ALL the arrows of C: every hom-set
   is a retract of it RELATIVE TO A DEFAULT.  The default makes [ai_dec]
   total without asking the caller to decide anything, and the law says the
   round trip is the identity up to the hom-setoid, for every default.
   Content: |hom x y| ≤ |ai_index| for every inhabited hom-set — Riehl's
   "products of families as large as its own cardinality" (§3.7 Prop 3), so
   the theorem covers large categories.  Theory/Size.v's [Small] is
   deliberately NOT consumed: it resizes per hom-set through [ObjEq]
   transports, and the proof needs one index type for all arrows. *)
Record ArrowIndex (C : Category) := {
  ai_index   : Type;
  ai_enc     : ∀ {x y : C}, (x ~> y) → ai_index;
  ai_dec     : ∀ {x y : C}, ai_index → (x ~> y) → (x ~> y);
  ai_dec_enc : ∀ {x y : C} (h d : x ~> y), ai_dec (ai_enc h) d ≈ h
}.

Arguments ai_index {C} _.
Arguments ai_enc {C} _ {x y} _.
Arguments ai_dec {C} _ {x y} _ _.
Arguments ai_dec_enc {C} _ {x y} _ _.

(* The dual is field for field the same data ([hom[C^op] x y] is [hom[C] y x]
   definitionally).  The constructor must be applied at [C^op] explicitly:
   the anonymous record literal elaborates its binders at [obj[C]] and is
   refused against [ArrowIndex (C^op)] (probe). *)
Definition ArrowIndex_op {C : Category} (AI : ArrowIndex C) :
  ArrowIndex (C^op) :=
  @Build_ArrowIndex (C^op) (ai_index AI)
    (fun x y h => ai_enc AI h)
    (fun x y m d => ai_dec AI m d)
    (fun x y h d => ai_dec_enc AI h d).

(** ** The canonical witness: decidable object equality suffices *)

(* Decidable object equality is Construction/Quotient.v:163's [ObjDecEq]
   (a definitional class: an instance IS the decider), consumed as is —
   an earlier revision declared a duplicate [DecObj]; the audit found the
   twin. *)

(* Decode a bundled arrow at a requested pair of endpoints, falling back on
   the default when the endpoints do not match.  No universe binders are
   written here on purpose: stdlib [eq] is pinned to a global universe on
   Coq 8.19/8.20 (Theory/Size.v:74-90). *)
Definition td {C : Category} (DO : ObjDecEq C) {x y : obj[C]}
  (m : TotalMor C) (d : x ~> y) : x ~> y :=
  match DO (projT1 m) x with
  | left ex =>
      match DO (projT1 (projT2 m)) y with
      | left ey =>
          eq_rect (projT1 m) (fun u => u ~> y)
            (eq_rect (projT1 (projT2 m)) (fun v => projT1 m ~> v)
               (projT2 (projT2 m)) y ey)
            x ex
      | right _ => d
      end
  | right _ => d
  end.

Lemma td_enc {C : Category} (DO : ObjDecEq C) {x y : obj[C]} (h d : x ~> y) :
  td DO (existT _ x (existT _ y h)) d ≈ h.
Proof.
  unfold td; simpl.
  destruct (DO x x) as [ex | ne]; [| destruct (ne eq_refl)].
  destruct (DO y y) as [ey | ne]; [| destruct (ne eq_refl)].
  rewrite (UIP_dec DO ex eq_refl).
  rewrite (UIP_dec DO ey eq_refl).
  reflexivity.
Qed.

(* EVERY category with decidable object equality carries an [ArrowIndex] at
   its own total arrow collection (Theory/Size.v's [TotalMor]).  So the
   hypothesis is not disguised thinness or finiteness: the strength of the
   theorem sits in the products at that index. *)
Definition canonical_ArrowIndex {C : Category} (DO : ObjDecEq C) :
  ArrowIndex C :=
  {| ai_index   := TotalMor C
   ; ai_enc     := fun x y h => existT _ x (existT _ y h)
   ; ai_dec     := fun x y m d => td DO m d
   ; ai_dec_enc := fun x y h d => td_enc DO h d |}.

(** ** The separated-pair core, fully constructive *)

(* The core consumes ONE elementary product: the [K]-fold power of [b],
   given as an [IsIndexedProduct] of the constant family.  Both the class
   [HasIndexedProducts] and a [Complete] instance feed it below. *)
Section FreydCore.

Context {C : Category}.
Context (AI : ArrowIndex C).
Context {a b : C}.
Context (f g : a ~> b).

Notation K := (ai_index AI).

Context (P : C) (pr : K → (P ~> b)).
Context (HP : IsIndexedProduct (fun _ : K => b) P pr).

(* A boolean separator for the pair, respecting the hom-setoid. *)
Context (sep : (a ~> b) → bool).
Context (sep_resp : ∀ u v : a ~> b, u ≈ v → sep u = sep v).
Context (sep_f : sep f = true).
Context (sep_g : sep g = false).

(* The [2^K]-indexed family of arrows [a ~> P]: at index [k] choose [f] or
   [g] according to [phi k]. *)
Definition fr_mk (phi : K → bool) : a ~> P :=
  unique_obj (iprod_desc HP (fun k => if phi k then f else g)).

Lemma fr_mk_commutes (phi : K → bool) (k : K) :
  pr k ∘ fr_mk phi ≈ (if phi k then f else g).
Proof.
  exact (unique_property (iprod_desc HP (fun k => if phi k then f else g)) k).
Qed.

(* Reading the choice back off an arrow, one index at a time. *)
Definition fr_decode (h : a ~> P) : K → bool := fun k => sep (pr k ∘ h).

Lemma fr_decode_mk (phi : K → bool) (k : K) : fr_decode (fr_mk phi) k = phi k.
Proof using sep_resp sep_f sep_g.
  unfold fr_decode.
  rewrite (sep_resp _ _ (fr_mk_commutes phi k)).
  destruct (phi k); assumption.
Qed.

(* Smallness turns [K] into a surjection onto the hom-set [a ~> P] ... *)
Definition fr_rd (k : K) : a ~> P := ai_dec AI k (fr_mk (fun _ => true)).

Lemma fr_rd_enc (h : a ~> P) : fr_rd (ai_enc AI h) ≈ h.
Proof. exact (ai_dec_enc AI h (fr_mk (fun _ => true))). Qed.

(* ... and hence into a K-indexed family of elements of [K → bool]. *)
Definition fr_Fam : K → K → bool := fun k => fr_decode (fr_rd k).

Lemma fr_Fam_surjective :
  ∀ phi : K → bool, exists k : K, ∀ i, fr_Fam k i = phi i.
Proof using sep_resp sep_f sep_g.
  intro phi.
  exists (ai_enc AI (fr_mk phi)).
  intro i.
  unfold fr_Fam, fr_decode.
  rewrite (sep_resp _ _ (compose_respects _ _ (reflexivity (pr i))
                           _ _ (fr_rd_enc (fr_mk phi)))).
  exact (fr_decode_mk phi i).
Qed.

(* THE CORE.  No axioms, no classical logic, no decidability: a parallel
   pair separated by a boolean predicate cannot exist in a category whose
   arrows are indexed by [K] and which has the [K]-fold power of [b]. *)
Theorem freyd_no_separated_pair : False.
Proof using All.
  exact (freyd_cantor_bool fr_Fam fr_Fam_surjective).
Qed.

End FreydCore.

(** ** Decidable hom-setoids reach thinness *)

(* [≈] is Type-valued (Lib/Setoid.v), so the decider is a [sum]. *)
Definition DecHom (C : Category) : Type :=
  ∀ (x y : C) (u v : x ~> y), ((u ≈ v) + ((u ≈ v) → False))%type.

Definition DecHom_op {C : Category} (D : DecHom C) : DecHom (C^op) :=
  fun x y u v => D y x u v.

(* From a decider, the separator "is it f?" and its three laws. *)
Section Separator.

Context {C : Category} (D : DecHom C) {x y : C} (f g : x ~> y)
  (Hne : (f ≈ g) → False).

Definition fr_sep (h : x ~> y) : bool := if D x y h f then true else false.

Lemma fr_sep_resp (u v : x ~> y) : u ≈ v → fr_sep u = fr_sep v.
Proof.
  intro Huv; unfold fr_sep.
  destruct (D x y u f) as [Hu | Hu]; destruct (D x y v f) as [Hv | Hv];
    try reflexivity.
  - destruct (Hv (transitivity (symmetry Huv) Hu)).
  - destruct (Hu (transitivity Huv Hv)).
Qed.

Lemma fr_sep_f : fr_sep f = true.
Proof.
  unfold fr_sep.
  destruct (D x y f f) as [Hff | Hff]; [reflexivity |].
  destruct (Hff (reflexivity f)).
Qed.

Lemma fr_sep_g : fr_sep g = false.
Proof using Hne.
  unfold fr_sep.
  destruct (D x y g f) as [Hgf | Hgf]; [| reflexivity].
  destruct (Hne (symmetry Hgf)).
Qed.

End Separator.

(* Mac Lane §V.2 Proposition 3 / Riehl §3.7 Proposition 3.7.3, over the
   class of indexed products: arrows indexed by [K], products over [K],
   decidable hom-setoids ⇒ thin. *)
Theorem freyd_thin {C : Category}
  (AI : ArrowIndex C) (HP : HasIndexedProducts C) (D : DecHom C) : Thin C.
Proof.
  intros x y f g.
  destruct (D x y f g) as [Heq | Hne]; [exact Heq |].
  exfalso.
  exact (freyd_no_separated_pair AI f g
           (indexed_product (fun _ : ai_index AI => y))
           (indexed_product_proj (fun _ : ai_index AI => y))
           (indexed_product_ump (fun _ : ai_index AI => y))
           (fr_sep D f) (fr_sep_resp D f) (fr_sep_f D f) (fr_sep_g D f g Hne)).
Qed.

(* Assembled at C's own arrow collection. *)
Definition freyd_thin_canonical {C : Category}
  (DO : ObjDecEq C) (HP : HasIndexedProducts C) (D : DecHom C) : Thin C :=
  freyd_thin (canonical_ArrowIndex DO) HP D.

(* Riehl §E.1's "or coproducts": products in [C^op], thinness self-dual. *)
Definition freyd_thin_dual {C : Category}
  (AI : ArrowIndex C) (HP : HasIndexedProducts (C^op)) (D : DecHom C) : Thin C :=
  Opposite_Thin (freyd_thin (ArrowIndex_op AI) HP (DecHom_op D)).

(** ** The constructive wall, located: an injection [(K → bool) ↣ K] from
       [f ≉ g] alone *)

Section Wall.

Context {C : Category}.
Context (AI : ArrowIndex C).
Context {a b : C} (f g : a ~> b) (Hne : (f ≈ g) → False).

Notation K := (ai_index AI).

Context (P : C) (pr : K → (P ~> b)).
Context (HP : IsIndexedProduct (fun _ : K => b) P pr).

(* [fr_mk] is injective UP TO the hom-setoid, from [f ≉ g] alone — no
   separator, no decidability, no classical logic. *)
Lemma fr_mk_injective (phi psi : K → bool) :
  fr_mk AI f g P pr HP phi ≈ fr_mk AI f g P pr HP psi → ∀ k, phi k = psi k.
Proof using Hne.
  intros Heq k.
  pose proof (fr_mk_commutes AI f g P pr HP phi k) as Hp.
  pose proof (fr_mk_commutes AI f g P pr HP psi k) as Hq.
  assert (Hc : (if phi k then f else g) ≈ (if psi k then f else g)).
  { rewrite <- Hp, <- Hq.
    apply compose_respects; [reflexivity | exact Heq]. }
  destruct (phi k); destruct (psi k); try reflexivity.
  - destruct (Hne Hc).
  - destruct (Hne (symmetry Hc)).
Qed.

(* Composing with the smallness encoding gives an INJECTION
   [(K → bool) → K] on the nose (Leibniz equality on [K]). *)
Definition fr_inj (phi : K → bool) : K := ai_enc AI (fr_mk AI f g P pr HP phi).

Lemma fr_inj_injective (phi psi : K → bool) :
  fr_inj phi = fr_inj psi → ∀ k, phi k = psi k.
Proof using Hne.
  intro He.
  apply fr_mk_injective.
  rewrite <- (ai_dec_enc AI (fr_mk AI f g P pr HP phi) (fr_mk AI f g P pr HP phi)).
  rewrite <- (ai_dec_enc AI (fr_mk AI f g P pr HP psi) (fr_mk AI f g P pr HP phi)).
  unfold fr_inj in He; rewrite He; reflexivity.
Qed.

End Wall.

(** ** From [Complete]: the product at any index, with no [Set] pin *)

Section CompleteBridge.

Universe o h p uo uh up.

Context {C : Category@{uo uh up}} (comp : @Complete C).

(* The limit of the discrete diagram on [d], through the annotated
   [DiscreteCat_Functor'] (Structure/Limit/Comparison.v) — the unannotated
   [DiscreteCat_Functor] pins C's hom and proof levels to [Set] (probe). *)
Definition complete_iprod_obj {A : Type@{o}} (d : A → C) : C :=
  vertex_obj[@limit_cone _ _ _
    (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))].

Definition complete_iprod_proj {A : Type@{o}} (d : A → C) (i : A) :
  complete_iprod_obj d ~> d i :=
  cone_leg (@limit_cone _ _ _
    (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))) i.

Definition complete_iprod {A : Type@{o}} (d : A → C) :
  IsIndexedProduct d (complete_iprod_obj d) (complete_iprod_proj d) :=
  discrete_IsIndexedProduct_of_IsLimitCone
    (DiscreteCat_Functor' d)
    (@limit_cone _ _ _
       (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d)))
    (@ump_limits _ _ _
       (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))).

End CompleteBridge.

(* The issue's pinned statement: a category whose arrows are indexed by a
   type at which it is complete, with decidable hom-setoids, is thin. *)
Theorem small_complete_is_thin {C : Category}
  (AI : ArrowIndex C) (comp : @Complete C) (D : DecHom C) : Thin C.
Proof.
  intros x y f g.
  destruct (D x y f g) as [Heq | Hne]; [exact Heq |].
  exfalso.
  exact (freyd_no_separated_pair AI f g
           (complete_iprod_obj comp (fun _ : ai_index AI => y))
           (complete_iprod_proj comp (fun _ : ai_index AI => y))
           (complete_iprod comp (fun _ : ai_index AI => y))
           (fr_sep D f) (fr_sep_resp D f) (fr_sep_f D f) (fr_sep_g D f g Hne)).
Qed.

(* Riehl §E.1's cocomplete half. *)
Definition small_cocomplete_is_thin {C : Category}
  (AI : ArrowIndex C) (cocomp : @Cocomplete C) (D : DecHom C) : Thin C :=
  Opposite_Thin
    (small_complete_is_thin (ArrowIndex_op AI)
       (Complete_op_of_Cocomplete cocomp) (DecHom_op D)).

(** ** The second half: all greatest lower bounds in the preorder reflection *)

(* A product is a greatest lower bound in the preorder reflection
   [thin_preorder C] (Structure/Thin.v) of ANY category — smallness and
   thinness play no part.  The one hypothesis is [HomChoice C]: the family
   of lower-bound witnesses is [inhabited]-squashed, and the mediator needs
   the arrows themselves. *)
Definition complete_has_glbs {C : Category} (comp : @Complete C)
  (ch : HomChoice C) : HasAllMeets (thin_preorder C).
Proof.
  intros Ix d.
  exists (complete_iprod_obj comp d).
  split.
  - intro i; exact (inhabits (complete_iprod_proj comp d i)).
  - intros n Hn.
    exact (inhabits (unique_obj (iprod_desc (complete_iprod comp d)
             (fun i => ch n (d i) (Hn i))))).
Defined.

(* Through #422's characterisation (Instance/Proset/Limit.v), the preorder
   reflection of a complete category is itself a complete preorder. *)
Definition complete_Proset_Complete {C : Category} (comp : @Complete C)
  (ch : HomChoice C) : @Complete (Proset (thin_PreOrder C)) :=
  snd (proset_Complete_iff_all_meets (thin_PreOrder C))
      (complete_has_glbs comp ch).
