Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.

Generalizable All Variables.

(** * Contractible pairs, and the coequalizers that are split *)

(* Book:   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
           Springer GTM 5, 1998, §VI.6 "Split Coequalizers", Exercise 2,
           printed p. 150 (PDF p. 159) — maclane:VI.6:ex2; the definitions
           of fork and split fork, printed p. 149 (PDF p. 158)
   nLab:   https://ncatlab.org/nlab/show/split+coequalizer, the section
           "Contractible pairs"

   WHAT THE BOOK SAYS, read from the page images.  On p. 149 a split fork
   is a fork a ⇉ b → c, the pair ∂₀, ∂₁ and the arrow e, "with two more
   arrows" t : b → a and s : c → b satisfying "e∂₀ = e∂₁, es = 1, ∂₀t = 1,
   ∂₁t = se. (3)".  On p. 150: "By a split coequalizer of ∂₀ and ∂₁ we
   shall mean the arrow e of such a split fork on ∂₀ and ∂₁.  It is
   possible to characterize those parallel pairs ∂₀, ∂₁ for which any
   (and hence every) coequalizer is split (Exercise 2)."  Exercise 2: "A
   parallel pair ∂₀, ∂₁ : a ⇉ b is said to be contractible (Beck) if
   there is an arrow t : b → a with ∂₀t = 1 and ∂₁t∂₀ = ∂₁t∂₁.  (a) In
   any split fork (1), prove ∂₀, ∂₁ contractible; (b) If a contractible
   pair has a coequalizer, prove that this coequalizer is split."

   WHAT IS HERE.  ∂₀ and ∂₁ are f and g, as in Structure/Coequalizer/
   Split.v, whose [SplitCoequalizer] carries Mac Lane's (3) as its laws 1
   to 4, in his order.
     - [ContractiblePair f g]: a contraction [contr_t] with
       [contr_section], f ∘ t ≈ id, and [contr_cofork],
       g ∘ t ∘ f ≈ g ∘ t ∘ g.  Composition associates to the left, so the
       second equation reads (g ∘ t) ∘ f ≈ (g ∘ t) ∘ g: g ∘ t coforks the
       pair, in the form Structure/Coequalizer.v's [coeq_desc] consumes.
     - (a) [split_coequalizer_contractible]: the pair of every split fork
       is contracted by the fork's own t ([split_coequalizer_contractible_t],
       at [eq_refl]).  The first equation is law 3; the second is nLab's
       chain g t f = s e f = s e g = g t g, by laws 4, 1 and 4.
     - (b) [contractible_coequalizer_split]: a contractible pair with an
       elementary coequalizer [IsCoequalizer f g q e] has a split
       coequalizer on the same object and arrow, its t the contraction
       and its s the descent of g ∘ t through e (all four at [eq_refl]:
       [contractible_coequalizer_split_obj], [_e], [_s], [_t]).  Law 4,
       s e ≈ g t, is the descent's triangle; law 2, e s ≈ 1, follows from
       e s e ≈ e g t ≈ e f t ≈ e because e is epic, by
       Structure/Coequalizer.v's [coequalizer_epic].  This is the argument
       nLab gives.  [contractible_coequalizer_split_s_unique]: given e and
       the contraction, s is the only arrow up to ≈ satisfying law 4, by
       the uniqueness clause of the descent.
     - "Any (and hence every)": [every_coequalizer_split] reads a
       contraction off one split coequalizer by (a) and feeds it to (b),
       so if a pair has one split coequalizer then EVERY coequalizer of it
       is split, on its own object and arrow and by the given fork's t
       ([every_coequalizer_split_obj], [_e], [_t], at [eq_refl]).
     - The characterization the book announces,
       [split_coequalizer_iff_contractible]: a pair has a split
       coequalizer exactly when it is contractible and has a coequalizer,
       by (a) and Split.v's [split_coequalizer_is_coequalizer], Mac Lane's
       Lemma, one way and by (b) the other.
     - The pair (1, i) of an idempotent i (Theory/Morphisms.v's
       [Idempotent]) is contracted by 1 ([idempotent_contractible]), and
       every coequalizer r of it splits i through r
       ([coequalizer_splits_idempotent], a [SplitIdempotent] whose
       idempotent is i and whose retraction is r, both at [eq_refl]:
       [coequalizer_splits_idempotent_idem], [_r]), its section the s of
       (b).
     - [functor_preserves_contractible]: every functor carries a
       contractible pair to one, contracted by the image of t
       ([functor_preserves_contractible_t], at [eq_refl]).  The
       definition is equational, and the proof goes equation by equation
       through [fmap_comp], [fmap_id] and [fmap_respects], as those of
       Split.v's [functor_preserves_split] and Reflexive.v's
       [functor_preserves_reflexive] do.
     - Structure/Coequalizer/Absolute.v's
       [contractible_coequalizer_absolute]: every coequalizer of a
       contractible pair is absolute, its [split_coequalizer_absolute]
       (#477) applied to (b).  It is stated there, Absolute.v requiring
       this file, so that this file does not load Absolute.v's closure
       (CLOSURE, below).
   The issue asks for the definition, (a) and (b).  The rest is beyond
   it: "any (and hence every)" and the characterization read the book's
   sentence of p. 150; the idempotent pair and the two corollaries are
   not asked for.

   THE CONVERSE DIRECTION, measured in Test/ProbeContractible480.v.
   (b) after (a), at the coequalizer of Mac Lane's Lemma
   ([split_coequalizer_is_coequalizer]), returns the split fork's object,
   e and t at [eq_refl] (C1 to C3) and its s only up to ≈ (C4, from
   [contractible_coequalizer_split_s_unique] and law 4); [eq_refl] is
   refused (R1).  R1 is not opacity: in a scratch file with transparent
   copies of Split.v's [Qed]-closed [split_coeq_desc] and of Mac Lane's
   Lemma, the round trip's s computes to (g ∘ t) ∘ s at [eq_refl], the
   Lemma's descent h ∘ s at h := g ∘ t, which is s only up to ≈, and
   [eq_refl] against s is still refused.  (a) after (b) returns the
   contraction and the proof of the first equation at [eq_refl] (C5,
   C6), but not the proof of the second (R2): (a) rebuilds it from the
   laws of the split fork (b) builds.  Nor is R2 opacity: the normal
   form of the rebuilt proof ([Eval cbv], in a scratch file) names no
   constant but projections of the variables C, P and E, its head
   ([Eval hnf]) the transitivity of C's own hom-setoid, where
   [contr_cofork P] is a projection of the variable P.

   BOUNDARIES.  NOT EVERY PAIR WITH A COEQUALIZER IS CONTRACTIBLE, NOR
   EVERY REFLEXIVE ONE.  Mac Lane's own pair G ×₀ N ⇉ G of p. 150 at Z/4
   over {0, 2} (#479, Instance/Grp/Coequalizer.v) is reflexive by #479's
   [semidirect_reflexive], whose common section [semidirect_refl] is
   x ↦ ⟨x, 0⟩ there, and has the coequalizer p; a contraction would
   split p by (b), and #479's [Z4_two_not_split_in_Grp] refutes that (C16
   to C19 of the probe).  The pair at A₃ ◁ S₃, which #479 splits in Grp,
   is contractible by (a) (C24).
     NOR HAS EVERY CONTRACTIBLE PAIR A COEQUALIZER, NOR IS IT REFLEXIVE.
   In Instance/Presented/Cyclic.v's [IdemCat], Awodey's one-object
   category of an idempotent s ∘ s = s, the pair (1, s) is contracted by 1
   ([idempotent_contractible], C20), and it has no coequalizer: a
   coequalizer e would split s, e ∘ s' ≈ 1 and s' ∘ e ≈ s
   ([coequalizer_splits_idempotent]), and no two of the category's
   arrows, which are 1 and s alone ([idem_exhaust]), form such a pair
   (C21).  The pair (s, s) has a coequalizer there, 1 (C23).  Nor is
   (1, s) reflexive: a common section r would have s ∘ r ≈ 1 (C22).  So
   [ContractiblePair] and Structure/Coequalizer/Reflexive.v's
   [ReflexivePair] are incomparable.  The last two sections of the probe
   alone require #479's module and Cyclic.v.

   STRENGTHS.  At [eq_refl]: the eleven readbacks named above.  At ≈, the
   category's own equality: the two equations of a contraction, the four
   laws of each split coequalizer, the two laws of the split idempotent
   and the uniqueness of s.

   UNIVERSES, read off [About] for every name.  [ContractiblePair], its
   constructor and its three projections are [@{u u0}] over
   C : Category@{u u0 u0}, with no constraint, the record in [Type@{u0}],
   the shape of Reflexive.v's [ReflexivePair].  Every other name but
   three binds C's two levels and nothing else: (a), (b),
   [every_coequalizer_split], [contractible_coequalizer_split_s_unique],
   the idempotent pair's two constants and ten of the eleven readbacks.
   [split_coequalizer_iff_contractible] binds one more level, the sort of
   the biconditional, at or above both of C's: its right side quantifies
   over C's objects and arrows.  [functor_preserves_contractible] and its
   readback bind [@{co ch do dh}] with "ch <= dh" alone, [Functor]'s own
   bound (its block carries h1 <= h2); Split.v's [functor_preserves_split],
   proved by [rewrite], binds one more level, above D's hom level.
   Without the binders D's hom level was identified with C's (measured),
   and C15 accepts ch < dh strict; Reflexive.v's
   [functor_preserves_reflexive], whose bare binders make that
   identification, is among the carriers #1363 tracks.
     The proofs of (a), (b) and [functor_preserves_contractible] use
   [transitivity], [symmetry], [compose_respects], [fmap_respects] and
   the laws of categories and functors, and no [rewrite]: proved by
   [rewrite]s of one side at a time, as in this file's first version,
   (a) and (b) bound a further level strictly above C's hom level and
   the functor corollary one above D's, and so did every name that then
   mentioned them (measured).  A [rewrite] of both sides of an ≈ in one
   step adds caps at the standard library's [prod_rect] besides (#1371).
   On Rocq 9.1.1 no block carries an equation, a [Set] or a
   standard-library universe cap.  On Coq 8.19.2 and 8.20.1 ([About] in
   a source overlay of the changed files' closure with the probe and a
   scratch file, 155 files, under each) every name binds as many levels
   as on Rocq 9.1.1, and the blocks add caps at the standard library's
   [eq.u0], identically on the two versions: none on the record's five
   names, on (a), on [idempotent_contractible] or on
   [functor_preserves_contractible]; on C's hom level in the fourteen
   other names that bind C's two levels alone, and on its object level
   as well in the two [_obj] readbacks; on D's hom level in
   [functor_preserves_contractible_t]; on C's and the target's hom
   levels in Absolute.v's [contractible_coequalizer_absolute], where
   [split_coequalizer_absolute] caps the target's alone; and at [eq],
   [prod] and [sigT] on C's levels and on its own in
   [split_coequalizer_iff_contractible].  No explicit universe instance
   of a new constant is written.

   CLOSURE.  A [Require] of this file loads 25 [Category] modules, this
   one included ([Print Libraries], counting the lines that name a
   [Category] module).  Stated here, the absolute corollary would load
   Absolute.v's closure, 23 modules more; stated in Absolute.v, which
   requires this file, it costs Absolute.v this one module (47 to 48, by
   the same count).  Monad/Monadicity/Beck.v, the consumer named under
   NOT DELIVERED, loads every module this file loads but this one.

   STALE PREMISES, dated from gh.  Issue #480 (filed 2026-07-23) says
   that no contractible-pair definition exists, that "contractible"
   occurs only for terminal-hom and [poly_unit] contractibility and never
   for a parallel pair, and that part (b) has no counterpart.  The
   definition and part (b) were absent until this file: at #479's
   commit, this development's base, no [.v] file names any of the
   twenty-five names it declares (its twenty-four constants and the
   record's constructor), nor does any [.glob] file outside it; and a
   [Search], over the thirteen modules outside Test/ that name both, for
   declarations that take an [IsCoequalizer] and return a
   [SplitCoequalizer] finds only (b) and [every_coequalizer_split].  The
   survey of the word was accurate when filed.  Since PR #1041 (merged
   2026-08-08) it has also been used of groupoids, and later of loop and
   path spaces and of topological spaces; #479's Instance/Grp/
   Coequalizer.v names this exercise among the things it does not
   deliver.  At #479's commit the eleven .v files that use the word
   besides that one (git grep -il contractib) say it of hom-sets, types,
   groupoids and spaces, and none defines a contractible pair.

   NOT DELIVERED.  The characterization through the idempotent g ∘ t (a
   contractible pair has a coequalizer, and then a split one, exactly
   when g ∘ t splits; nLab's second argument), and with it the split
   coequalizer of every contractible pair in a category whose
   idempotents split (Construction/Karoubi/Universal.v's
   [IdempotentsSplit]).  Of it, the pair (1, i) above gives one
   direction at that pair, a coequalizer splitting i; the other, a split
   coequalizer of (1, s ∘ r) from a splitting (r, s) of i, is item 2 of
   #957 (Riehl's split idempotents).  Monad/Monadicity/Beck.v's creation
   of coequalizers is stated for U-split pairs
   ([CreatesUSplitCoequalizers]) and is not restated for contractible
   ones. *)

(** ** The definition *)

(* A contraction t of the pair: a section of f through which g ∘ t
   coforks the pair. *)
Record ContractiblePair {C : Category} {x y : C} (f g : x ~> y) := {
  contr_t : y ~> x;                                (* the contraction *)

  contr_section : f ∘ contr_t ≈ id;                (* ∂₀ t = 1 *)
  contr_cofork  : g ∘ contr_t ∘ f ≈ g ∘ contr_t ∘ g
                                                   (* ∂₁ t ∂₀ = ∂₁ t ∂₁ *)
}.

Arguments contr_t       {_ _ _ _ _} _.
Arguments contr_section {_ _ _ _ _} _.
Arguments contr_cofork  {_ _ _ _ _} _.

(** ** (a) The pair of a split fork is contractible *)

(* t is the split fork's t: law 3 is ∂₀ t = 1, and g t f = s e f = s e g
   = g t g by laws 4, 1 and 4. *)
Definition split_coequalizer_contractible {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) : ContractiblePair f g.
Proof.
  unshelve refine {| contr_t := scoeq_t S; contr_section := scoeq_law3 S |}.
  transitivity (scoeq_s S ∘ scoeq_e S ∘ f).
  { (* law 4 *)
    refine (compose_respects _ _ (scoeq_law4 S) _ _ _).
    reflexivity. }
  transitivity (scoeq_s S ∘ scoeq_e S ∘ g).
  { (* law 1, under s *)
    transitivity (scoeq_s S ∘ (scoeq_e S ∘ f)).
    { symmetry.
      apply comp_assoc. }
    transitivity (scoeq_s S ∘ (scoeq_e S ∘ g)).
    { refine (compose_respects _ _ _ _ _ (scoeq_law1 S)).
      reflexivity. }
    apply comp_assoc. }
  (* law 4 *)
  refine (compose_respects _ _ _ _ _ _).
  - symmetry.
    exact (scoeq_law4 S).
  - reflexivity.
Defined.

Example split_coequalizer_contractible_t {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) :
  contr_t (split_coequalizer_contractible S) = scoeq_t S := eq_refl.

(** ** (b) A coequalizer of a contractible pair is split *)

(* On the same object and arrow: s is the descent of g ∘ t through e,
   which the second equation makes possible; then s e = g t is law 4, and
   e s e = e g t = e f t = e gives law 2, e being epic. *)
Definition contractible_coequalizer_split {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : SplitCoequalizer f g.
Proof.
  unshelve refine
    {| scoeq_obj := q
     ; scoeq_e   := e
     ; scoeq_s   := unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P))
     ; scoeq_t   := contr_t P |}.
  - (* law 1 *)
    exact (cofork E).
  - (* law 2: (e ∘ s) ∘ e ≈ id ∘ e, then e is epic *)
    apply (@epic _ _ _ e (coequalizer_epic f g E)).
    transitivity
      (e ∘ (unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) ∘ e)).
    { symmetry.
      apply comp_assoc. }
    transitivity (e ∘ (g ∘ contr_t P)).
    { refine (compose_respects _ _ _ _ _
                (unique_property
                   (coeq_desc E (g ∘ contr_t P) (contr_cofork P)))).
      reflexivity. }
    transitivity (e ∘ g ∘ contr_t P).
    { apply comp_assoc. }
    transitivity (e ∘ f ∘ contr_t P).
    { refine (compose_respects _ _ _ _ _ _).
      - symmetry.
        exact (cofork E).
      - reflexivity. }
    transitivity (e ∘ (f ∘ contr_t P)).
    { symmetry.
      apply comp_assoc. }
    transitivity (e ∘ id).
    { refine (compose_respects _ _ _ _ _ (contr_section P)).
      reflexivity. }
    transitivity e.
    { apply id_right. }
    symmetry.
    apply id_left.
  - (* law 3 *)
    exact (contr_section P).
  - (* law 4 *)
    symmetry.
    exact (unique_property (coeq_desc E (g ∘ contr_t P) (contr_cofork P))).
Defined.

Example contractible_coequalizer_split_obj {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_obj (contractible_coequalizer_split P E) = q := eq_refl.

Example contractible_coequalizer_split_e {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_e (contractible_coequalizer_split P E) = e := eq_refl.

Example contractible_coequalizer_split_s {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_s (contractible_coequalizer_split P E)
    = unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) := eq_refl.

Example contractible_coequalizer_split_t {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_t (contractible_coequalizer_split P E) = contr_t P := eq_refl.

(* Given the coequalizer and the contraction, s is unique up to ≈: any s'
   satisfying law 4 is the descent of g ∘ t. *)
Lemma contractible_coequalizer_split_s_unique {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) (s : q ~> y) (Hs : g ∘ contr_t P ≈ s ∘ e) :
  scoeq_s (contractible_coequalizer_split P E) ≈ s.
Proof.
  exact (uniqueness (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) s
           (symmetry Hs)).
Qed.

(** ** "Any (and hence every) coequalizer is split" *)

Definition every_coequalizer_split {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : SplitCoequalizer f g :=
  contractible_coequalizer_split (split_coequalizer_contractible S) E.

Example every_coequalizer_split_obj {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_obj (every_coequalizer_split S E) = q := eq_refl.

Example every_coequalizer_split_e {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_e (every_coequalizer_split S E) = e := eq_refl.

(* Every coequalizer of the pair is split by the same t. *)
Example every_coequalizer_split_t {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_t (every_coequalizer_split S E) = scoeq_t S := eq_refl.

(** ** The characterization *)

(* A pair has a split coequalizer exactly when it is contractible and has
   a coequalizer: (a) and Mac Lane's Lemma one way, (b) the other. *)
Definition split_coequalizer_iff_contractible {C : Category} {x y : C}
  (f g : x ~> y) :
  SplitCoequalizer f g ↔
  (ContractiblePair f g ∧ ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e).
Proof.
  split.
  - intros S.
    split.
    + exact (split_coequalizer_contractible S).
    + exists (scoeq_obj S), (scoeq_e S).
      exact (split_coequalizer_is_coequalizer f g S).
  - intros [P [q [e E]]].
    exact (contractible_coequalizer_split P E).
Defined.

(** ** The pair (1, i) of an idempotent *)

(* Contracted by 1: the second equation is i ∘ 1 ∘ 1 ≈ i ∘ 1 ∘ i, both
   sides being i up to ≈, the right one by idempotence. *)
Definition idempotent_contractible {C : Category} {x : C} (i : x ~> x)
  (I : Idempotent i) : ContractiblePair id i.
Proof.
  unshelve refine {| contr_t := id; contr_section := id_left id |}.
  transitivity i.
  - transitivity (i ∘ id).
    + apply id_right.
    + apply id_right.
  - transitivity (i ∘ i).
    + symmetry.
      exact idem.
    + refine (compose_respects _ _ _ _ _ _).
      * symmetry.
        apply id_right.
      * reflexivity.
Defined.

(* A coequalizer r of (1, i) splits i through r: s ∘ r ≈ i is law 4 of
   (b), i ∘ 1 ≈ s ∘ r, and r ∘ s ≈ 1 is its law 2. *)
Definition coequalizer_splits_idempotent {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) : @SplitIdempotent C x q.
Proof.
  unshelve refine
    {| split_idem   := i
     ; split_idem_r := r
     ; split_idem_s := scoeq_s (contractible_coequalizer_split
                                  (idempotent_contractible i I) E) |}.
  - (* s ∘ r ≈ i *)
    symmetry.
    transitivity (i ∘ id).
    + symmetry.
      apply id_right.
    + exact (scoeq_law4 (contractible_coequalizer_split
                           (idempotent_contractible i I) E)).
  - (* r ∘ s ≈ 1 *)
    exact (scoeq_law2 (contractible_coequalizer_split
                         (idempotent_contractible i I) E)).
Defined.

Example coequalizer_splits_idempotent_idem {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) :
  @split_idem C x q (coequalizer_splits_idempotent i I E) = i := eq_refl.

Example coequalizer_splits_idempotent_r {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) :
  @split_idem_r C x q (coequalizer_splits_idempotent i I E) = r := eq_refl.

(** ** Functors preserve contractible pairs *)

Theorem functor_preserves_contractible@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  ContractiblePair f g → ContractiblePair (fmap[F] f) (fmap[F] g).
Proof.
  intros P.
  unshelve refine {| contr_t := fmap[F] (contr_t P) |}.
  - (* F f ∘ F t ≈ F (f ∘ t) ≈ F id ≈ id *)
    transitivity (fmap[F] (f ∘ contr_t P)).
    + symmetry.
      apply fmap_comp.
    + transitivity (fmap[F] (@id C y)).
      * apply fmap_respects.
        exact (contr_section P).
      * apply fmap_id.
  - (* F g ∘ F t ∘ F f ≈ F (g ∘ t ∘ f) ≈ F (g ∘ t ∘ g) ≈ F g ∘ F t ∘ F g *)
    transitivity (fmap[F] (g ∘ contr_t P ∘ f)).
    { transitivity (fmap[F] (g ∘ contr_t P) ∘ fmap[F] f).
      - refine (compose_respects _ _ _ _ _ _).
        + symmetry.
          apply fmap_comp.
        + reflexivity.
      - symmetry.
        apply fmap_comp. }
    transitivity (fmap[F] (g ∘ contr_t P ∘ g)).
    { apply fmap_respects.
      exact (contr_cofork P). }
    transitivity (fmap[F] (g ∘ contr_t P) ∘ fmap[F] g).
    { apply fmap_comp. }
    refine (compose_respects _ _ _ _ _ _).
    + apply fmap_comp.
    + reflexivity.
Defined.

Example functor_preserves_contractible_t@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} {f g : x ~> y} (P : ContractiblePair f g) :
  contr_t (functor_preserves_contractible F f g P) = fmap[F] (contr_t P)
  := eq_refl.
