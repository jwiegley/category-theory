Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Finite products from a terminal object and binary products *)

(* nLab:      https://ncatlab.org/nlab/show/finite+product
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Book:      Mac Lane, CWM 2nd ed., §III.5 Proposition 1 (p. 73)
   Book:      Awodey, Category Theory 1st ed., §2.7

   Mac Lane's Proposition 1 is that a terminal object together with binary
   products yields a product diagram for EVERY finite family.  Awodey states
   the same for arity at least two as the LEFT-associated
   [A × B × C := (A × B) × C], the terminal object supplying the nullary and
   unary cases.  The fold built here is the RIGHT one; the two are NOT the
   same object (refuted at [eq_refl], below), and they are related instead
   by a canonical isomorphism commuting with all three projections --
   [awodey_fold_iso] with [awodey_fold_iso_to] / [awodey_fold_iso_from].

   WHAT IS NEW, STATED PRECISELY.  The tree already has three iterated
   binary-product folds, and it would be false to say otherwise:
   [law_pow] (Theory/Lawvere.v:150), folding [law_of_nat 1];
   [pow] (Theory/Multicategory/Endomorphism.v:69), folding [X]; and
   [Pow] (Instance/Fun/Discrete.v:254), folding [B] one level up, in [Cat].
   ALL THREE FOLD A CONSTANT FAMILY -- they compute [X × X × … × X], a
   power.  What is absent, and what this file supplies, is a fold of a
   VARYING family [f : Fin.t n → C] together with its universal property.
   SCOPE THAT CENSUS: it ranges over folds of the BINARY PRODUCT [×].
   Folds of a monoidal [⨂] exist too and are not counted -- [nf]
   (Construction/FreeMonoidal/Normal.v:66) and [tpower] (Spider.v:217) are
   constant-family, while [tensor_list]/[tfold]
   (Theory/Multicategory/Representable.v:55,67) DO fold a varying family.
   So "a fold of a varying family" is not by itself distinguishing; what
   distinguishes this one is the binary product together with its
   universal property.
   The gap is conceded in the donor's own prose: Structure/Cartesian.v:19-21
   reads "A cartesian category is a category equipped with finite products.
   This class axiomatizes the binary product; the nullary product (the
   terminal object 1) is supplied separately by [Terminal]" -- so the class
   says of itself that it covers only the binary and (via [Terminal]) the
   nullary case.

   WHAT IS PROVED.  Over [Cartesian C] together with [Terminal C] -- two
   genuinely separate hypotheses, since [Class Cartesian]
   (Structure/Cartesian.v:121) carries no terminal object -- the right fold

     fin_prod 0 f       = 1
     fin_prod (S m) f   = f F1 × fin_prod m (fun i => f (FS i))

   with projections [fin_proj] by [Fin] recursion and tupling [fin_tuple],
   is an indexed product in the sense of the elementary record
   [IsIndexedProduct] (Structure/Limit/Product.v:51):

     fin_IsIndexedProduct n f
       : IsIndexedProduct f (fin_prod n f) (fin_proj n f)

   proved by induction on [n].  The family is indexed by [Fin.t n → C], so
   [A := Fin.t n] plugs into that record with no adapter -- there is no list
   of objects and no heterogeneous telescope anywhere.  [HasFiniteProducts]
   packages a choice of such a product, mirroring [HasIndexedProducts]'s
   three-field shape with [{n : nat} (f : Fin.t n → C)] in place of
   [{A : Type} (f : A → C)], and [Cartesian_Terminal_HasFiniteProducts]
   produces it.

   THE FOLD IS THE [Pow] FOLD, AND SO IS THE WART.  [Pow]
   (Instance/Fun/Discrete.v:254) is the same right fold one level up -- the
   n-fold power of a CATEGORY, with the terminal category as its empty case
   -- and it carries the same trailing unit factor, exhibiting the literal
   [B ∏ B] at n = 2 only through [prod_one_r].  So [fin_prod 1 f] is
   [f F1 × 1] and NOT [f F1], and [fin_prod 2 f] is [f F1 × (f (FS F1) × 1)]
   and NOT [f F1 × f (FS F1)].  Both readings are pinned as [eq_refl]
   [Example]s below ([fin_prod_one], [fin_prod_two]) and both un-warted
   readings are REFUTED at [eq_refl] (measured; see STRENGTHS).  The repair
   costs one unitor: [fin_prod_one_iso] IS [prod_one_r], a [:=] with no
   tactic, and [fin_prod_two_iso] is that same unitor under
   [prod_respects_iso].

   STRENGTHS, MEASURED STRICT-FIRST.  Positive, each checked at [eq_refl]:
   the three object computations above; [fin_proj 1 f F1 = exl];
   [fin_proj 2 f (FS F1) = exl ∘ exr];
   [fin_tuple 2 f c pi = pi F1 △ (pi (FS F1) △ one)] -- these six are
   [Example]s in this file.  The identifications that follow were checked
   in a scratch file with this file's import list; FOUR of them are now
   pinned in Test/ProbeFiniteProducts335.v and the rest remain
   scratch-only, itemized after the list rather than left to the reader:
   [to (fin_prod_one_iso f) = fin_proj 1 f F1]
   (the unitor's forward leg IS the projection);
   [finite_product (Cartesian_Terminal_HasFiniteProducts CP T) n f
      = fin_prod n f] and the same for the projections;
   [terminal_obj (HasFiniteProducts_Terminal (Cartesian_Terminal_... CP T))
      = terminal_obj T];
   [product_obj (HasFiniteProducts_Cartesian (Cartesian_Terminal_... CP T))
      x y = x × (y × 1)], whose [exl] and [exr] are [exl] and [exl ∘ exr];
   and on the dual side [fin_coprod CC I 2 f = f F1 + (f (FS F1) + 0)] and
   [finite_coproduct (Cocartesian_Initial_HasFiniteCoproducts CC I) n f
      = fin_coprod CC I n f].  On the Awodey comparison, five more,
   all
   [eq_refl]: the three [awodey_proj] components are [exl ∘ exl],
   [exr ∘ exl] and [exr]; [to (awodey_fold_iso CP T x y z)] IS
   [awodey_tuple] of the right fold's projections and
   [from (awodey_fold_iso CP T x y z)] IS [fin_tuple] of the left fold's --
   so the comparison map is not an opaque mediator but the tupling one
   would write by hand.

   FOUR OF THOSE ARE NO LONGER SCRATCH-ONLY.  Test/ProbeFiniteProducts335.v
   pins, as [Example]s beside the refutations they bound: the class
   returning the fold and its projections; [terminal_obj] being recovered
   on the nose; and the padded product being [x × (y × 1)].  That last
   pair is the point of pinning both halves -- the [Terminal] RECORD is
   NOT recovered (refutation 5) while the terminal OBJECT is, and only
   having both in one file makes that boundary legible.  The remaining
   identifications above -- the unitor leg, the two dual-side ones, the
   [exl]/[exr] readings of the padded product, and the FIVE Awodey ones
   (three [awodey_proj] components plus [to] and [from] of
   [awodey_fold_iso]; an earlier draft of this header said four, and also
   omitted the [exl]/[exr] item from this accounting) -- are still
   measured in scratch files only.

   SEVEN REFUTATIONS, all CONVERSION failures -- each was stripped of its
   [Fail] once and its error read, and each reported "cannot unify":
     1. [fin_prod 1 f = f F1]
     2. [fin_prod 2 f = f F1 × f (FS F1)]
     3. [product_obj (HasFiniteProducts_Cartesian
           (Cartesian_Terminal_HasFiniteProducts CP T)) x y = x × y] --
        going out to the class and back does NOT return the original binary
        product; it returns the padded one.
     4. [HasFiniteProducts_Cartesian (Cartesian_Terminal_... CP T) = CP]
     5. [HasFiniteProducts_Terminal (Cartesian_Terminal_... CP T) = T]
     6. [Cartesian_Terminal_HasFiniteProducts
           (HasFiniteProducts_Cartesian H) (HasFiniteProducts_Terminal H)
         = H] at [H := Cartesian_Terminal_HasFiniteProducts CP T] -- the
        composite is not the identity on the nose, because the recovered
        [Cartesian] has the padded product and the fold is then taken over
        THAT.  This is refutation 3 propagated, not an independent fact.
     7. [fin_prod 3 (fin3 x y z) = awodey_prod CP x y z] -- the right and
        left folds are genuinely different objects, which is why the
        comparison below is an isomorphism and nothing stronger.
   ALL SEVEN ARE PINNED, in Test/ProbeFiniteProducts335.v, as its
   negatives 1-7.  This file ships no [Fail] of its own -- the guarding is
   the probe's job -- and each of the seven was stripped of its [Fail]
   there and its failure KIND confirmed to be "cannot unify" rather than
   some unrelated elaboration failure.

   UNIVERSES, read off the constraint blocks ([Set Printing Universes] then
   [About]), never off the binders.
     - [fin_prod@{u u0} : ∀ {C : Category@{u u0 u0}}, Cartesian@{u u0} →
       Terminal@{u u0} → ∀ n, (Fin.t n → obj[C]) → obj[C]] has an EMPTY
       constraint block, and so does [fin_tuple].  The OBJECT universe is
       neither identified with nor bounded by the hom universe.
     - The hom-and-proof identification [Category@{u u0 u0}] is INHERITED,
       and from three donors INDEPENDENTLY: [Cartesian@{u u0}] and
       [Terminal@{u u0}] are each declared over [Category@{u u0 u0}], and
       [IsIndexedProduct@{u u0 u1 u2}] over [Category@{u1 u2 u2}].  Under a
       section declaring [Constraint uh < up] over [C : Category@{uo uh up}]
       all three are rejected, while the control
       [Check (fun x y : C => x ~{C}~> y)] is accepted.  Nothing here adds
       to the identification, and it is NOT claimed unavoidable.  All
       three rejections and that control are pinned as negatives 8-10 of
       Test/ProbeFiniteProducts335.v, each confirmed to report
       "universe inconsistency: Cannot enforce up = uh".
     - [fin_proj] additionally carries [u0 <= Fin.case0.u0] and
       [u0 <= Fin.caseS'.u0], the stdlib eliminators; again inherited.
     - [iprod_unique_iso@{u u0 u1 u2 u3 u4}] leaves the INDEX universe [u]
       only BOUNDED ([u <= u2], [u <= u3]), never identified.

   HOW THIS SITS BETWEEN ITS TWO NEIGHBOURS.  [Terminal_Limit]
   (Structure/Limit/Terminal.v:33) is [Limit F ↔ @Terminal C] for the empty
   diagram [F : 0 ⟶ C], the n = 0 case; [Cartesian_Limit]
   (Structure/Limit/Cartesian.v:39) is
   [(∀ F : Two_Discrete ⟶ C, Limit F) ↔ @Cartesian C], the n = 2 case.
   Three differences, stated rather than gestured at.
     (i) Both neighbours are at LIMIT level over a named shape.  Nothing
         here forms a [Limit] or a [Cone] at all; the whole file is at the
         elementary [IsIndexedProduct] level, DELIBERATELY, because
         [DiscreteCat_Functor] (Instance/Discrete.v:52) is
         universe-unannotated and routing through it pins C's hom and proof
         universes to [Set].  No [Limit]-shaped corollary is delivered.
    (ii) Both neighbours fix ONE arity; this theorem quantifies over all
         finite arities at once.
   (iii) Both neighbours are biconditionals, and so is this one:
         [HasFiniteProducts_iff C : HasFiniteProducts C ↔
          (@Cartesian C * @Terminal C)], with [HasFiniteProducts_Terminal]
         and [HasFiniteProducts_Cartesian] the converse legs.  It is NOT an
         equivalence of structures; refutations 3-6 measure the gap.
   The two specializations ARE proved, and from the universal property
   rather than by inspection: [fin_zero_IsTerminalObj] gives
   [IsTerminalObj (fin_prod 0 f)] and [fin_two_IsCartesianProduct] gives
   [@IsCartesianProduct C x y (fin_prod 2 (fin2fam x y))], each by
   instantiating a generic reading ([iprod_zero_IsTerminalObj],
   [iprod_two_IsCartesianProduct]) at [fin_IsIndexedProduct].  What they
   recover is the CONCLUSION of each neighbour -- a terminal object, a
   binary product -- not its [Limit]-level statement.

   AWODEY §2.7 IS DISCHARGED, NOT DISCLAIMED.  [awodey_prod CP x y z] is
   the literal [(x × y) × z] with [awodey_proj] the three composite
   projections, and [awodey_IsIndexedProduct] proves it an indexed product
   of [fin3 x y z].  NOTE ITS HYPOTHESIS: [Cartesian] alone, with NO
   [Terminal] -- Awodey's construction pads with nothing, which is exactly
   why the terminal object is needed only for the nullary and unary cases,
   and the file makes that visible by putting the ternary section in a
   [Terminal]-free [Context].  [awodey_fold_iso] then relates it to the
   right fold, with BOTH leg families ([awodey_fold_iso_to] and
   [awodey_fold_iso_from]) -- a bare [≅] would be the weak form.  SCOPE:
   this is Awodey's own DISPLAYED instance, the ternary one, at literal
   left association.  A left fold for ARBITRARY [n] is not built; see NOT
   DELIVERED.

   TWO BY-PRODUCTS are declared here rather than in their natural homes,
   because this commit adds one file and edits none.
     - [iprod_unique_iso]: essential uniqueness for [IsIndexedProduct], WITH
       the leg equations [iprod_compare_commutes] and
       [iprod_compare_inv_commutes].  The tree had none: outside this file
       [IsIndexedProduct] occurs in thirteen [.v] files (four of them
       [Test/] probes -- Test/ProbeFiniteProducts335.v, shipped with this
       commit, is the thirteenth and fourth) and not one states
       uniqueness, while
       [Structure/Limit/Unique.v]'s [limit_unique_iso] is about [IsALimit],
       a different record.  It is short, as one would hope -- [iprod_desc]
       already carries the [∃!] -- and it is what licenses the Awodey
       comparison above, so it is instantiated rather than left unused.
       Natural home: Structure/Limit/Product.v.
     - [Cartesian_of_IsCartesianProduct]: every pair having an
       [IsCartesianProduct] makes C cartesian.  Structure/Cartesian.v
       declares both classes (:121, :145) with no passage between them;
       Functor/Hom/Limit.v:539 supplies the OTHER direction
       ([cartesian_IsCartesianProduct]) and records the absence at :218.
       Natural home: Structure/Cartesian.v.
   Neither is registered as an [Instance].

   THE DUAL.  [HasFiniteCoproducts C := @HasFiniteProducts (C^op)], a
   [Definition] plus [Existing Class], exactly the shape
   Structure/Limit/Coproduct.v gives [HasIndexedCoproducts] and for the
   reason recorded there (resolution keys on the head constant and does not
   look through the unfolding).  Every consumer-facing type is covariant --
   [finite_coproduct_inj f i : f i ~> finite_coproduct f], and
   [fin_coprod_ump] is stated with [u ∘ fin_inj n f i ≈ iota i] -- and no
   [^op] occurs in any of them; every passage is a [:=] term with no
   tactic, since [C^op] unfolds [hom] and [compose] definitionally.
   DISPLAY HAZARD: [Cocartesian C] and [Initial C] are NOTATIONS for
   [@Cartesian (C^op)] and [@Terminal (C^op)] whose category argument is
   implicit, so [Check]ing e.g. [HasFiniteCoproducts_Cocartesian] prints
   its conclusion as a bare [Cartesian] -- the [^op] is hidden by
   implicit-argument suppression, not absent.  [Set Printing Implicit]
   shows it.

   NON-VACUITY.  The five [coq_*] [Example]s at the end instantiate at
   Instance/Coq.v and COMPUTE by [eq_refl]:
   [fin_prod 3 (fun _ => nat) = nat * (nat * (nat * unit))], a mixed
   two-factor fold, the tupling of [Nat.eqb ─ 0] with [S] evaluated at 3 to
   [(false, (4, tt))], and the second projection evaluated to [2].  They
   exercise the fold's DATA, not its universal property; no concrete
   [HasFiniteProducts] instance is registered for any category.

   STATUS: 77 constants -- 76 in the [.glob] (66 [def], 6 [prf], 3 [proj],
   1 [rec]) plus [Build_HasFiniteProducts], which the glob does not record
   -- all reporting "Closed under the global context".  No [Program]
   anywhere in the file.

   NOT DELIVERED.
     - No left fold for ARBITRARY arity.  Awodey's displayed ternary case
       IS delivered ([awodey_fold_iso] and its two leg families), but a
       general left-associated [fin_prod_l n f] is not built, so no
       statement quantifies over [n] on the left-associated side.  The
       obstruction is not the universal property -- [fin_prod_unique_iso]
       would supply the comparison for any such fold, given its
       [IsIndexedProduct].  AN EARLIER DRAFT OF THIS HEADER GAVE A REASON
       THAT IS FALSE, and it is recorded here rather than deleted: it said
       a left fold peels the LAST index while [Fin.t (S m)] peels at the
       FRONT, so a back-peeling eliminator would have to be built first.
       Both halves are wrong.  Stdlib already HAS a back-peeling
       eliminator ([Fin.case_L_R'], with iota rules [case_L_R'_L] and
       [case_L_R'_R]); and no back-peeling is needed in any case, since an
       ACCUMULATOR turns front peeling into left association --
       [fold_l (S m) acc f := fold_l m (acc × f F1) (f ∘ FS)] -- for which
       [fin_prod_l 2 (fin3 x y z) = awodey_prod CP x y z] holds by
       [eq_refl] (compiled out of tree, audit-supplied).  So the general
       comparison is UNATTEMPTED, not obstructed; what remains genuinely
       untested is its universal property, not its definition.
     - No [Limit] or [Cone] anywhere, hence no
       [Limit (DiscreteCat_Functor f)]-shaped corollary and no bridge to
       [Terminal_Limit] or [Cartesian_Limit] as STATEMENTS; only their
       conclusions are recovered.
     - No [HasFiniteProducts] or [HasFiniteCoproducts] instance for any
       concrete category, and no [Instance] registration of anything here.
     - No relation to Structure/Limit/Power.v's [power] (the constant-family
       case) and none to Structure/Limit/Indexed/Hom.v's hom bijections; no
       naturality or functoriality of [fin_prod] in [f] or in [n]; no
       associativity or commutativity coherence for the fold; no
       [Fin.t (m + n)] splitting.
     - (An earlier draft of this header ended with "No [Test/] probe",
       and miscounted the refutations as six; there are SEVEN, enumerated
       above.  Both are corrected: Test/ProbeFiniteProducts335.v ships in
       the same commit and pins all ten measurements.)
     - Three proofs carry an explicit [Proof using] --
       [iprod_two_IsCartesianProduct], [iprod_unique_iso] and
       [awodey_IsIndexedProduct] -- because Lib.v sets
       [Default Proof Using "Type"] and each has section hypotheses
       ([proj]/[HP], [HP]/[HQ], [CP]) that do not appear in its statement.
       Nothing else in the file needs one. *)

(** ** Index vocabulary *)

Definition fin0_rect (P : Fin.t 0 → Type) (i : Fin.t 0) : P i :=
  Fin.case0 P i.

Definition fin2fam_rect (P : Fin.t 2 → Type)
  (p1 : P Fin.F1) (p2 : P (Fin.FS Fin.F1)) (i : Fin.t 2) : P i :=
  Fin.caseS' i P p1
    (fun j => Fin.caseS' j (fun j => P (Fin.FS j)) p2
                (fun k => Fin.case0 (fun k => P (Fin.FS (Fin.FS k))) k)).

Definition fin0 {C : Category} : Fin.t 0 → C :=
  fin0_rect (fun _ => C).

Definition fin2fam {C : Category} (x y : C) : Fin.t 2 → C :=
  fin2fam_rect (fun _ => C) x y.

Definition fin0_legs {C : Category} {a : C} (f : Fin.t 0 → C) :
  ∀ i : Fin.t 0, a ~> f i :=
  fin0_rect (fun i => a ~> f i).

Definition fin2_legs {C : Category} {a x y : C}
  (f : a ~> x) (g : a ~> y) : ∀ i : Fin.t 2, a ~> fin2fam x y i :=
  fin2fam_rect (fun i => a ~> fin2fam x y i) f g.

Definition fin3_rect (P : Fin.t 3 → Type) (p1 : P Fin.F1)
  (p2 : P (Fin.FS Fin.F1)) (p3 : P (Fin.FS (Fin.FS Fin.F1)))
  (i : Fin.t 3) : P i :=
  Fin.caseS' i P p1 (fun j => fin2fam_rect (fun j => P (Fin.FS j)) p2 p3 j).

Definition fin3 {C : Category} (x y z : C) : Fin.t 3 → C :=
  fin3_rect (fun _ => C) x y z.

Definition fin3_legs {C : Category} {a x y z : C}
  (f : a ~> x) (g : a ~> y) (h : a ~> z) :
  ∀ i : Fin.t 3, a ~> fin3 x y z i :=
  fin3_rect (fun i => a ~> fin3 x y z i) f g h.

(** ** The right fold *)

Section FiniteProducts.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Fixpoint fin_prod (n : nat) : (Fin.t n → C) → C :=
  match n as n0 return (Fin.t n0 → C) → C with
  | O    => fun _ => 1%object
  | S m  => fun f => (f Fin.F1 × fin_prod m (fun i => f (Fin.FS i)))%object
  end.

Fixpoint fin_proj (n : nat) :
  ∀ (f : Fin.t n → C) (i : Fin.t n), fin_prod n f ~> f i :=
  match n as n0
    return ∀ (f : Fin.t n0 → C) (i : Fin.t n0), fin_prod n0 f ~> f i with
  | O    => fun f i => Fin.case0 (fun i => fin_prod 0 f ~> f i) i
  | S m  => fun f i =>
      Fin.caseS' i (fun i => fin_prod (S m) f ~> f i)
        exl
        (fun j => fin_proj m (fun k => f (Fin.FS k)) j ∘ exr)
  end.

Fixpoint fin_tuple (n : nat) :
  ∀ (f : Fin.t n → C) (c : C) (pi : ∀ i, c ~> f i), c ~> fin_prod n f :=
  match n as n0
    return ∀ (f : Fin.t n0 → C) (c : C) (pi : ∀ i, c ~> f i),
             c ~> fin_prod n0 f with
  | O    => fun _ _ _ => one
  | S m  => fun f c pi =>
      pi Fin.F1
        △ fin_tuple m (fun k => f (Fin.FS k)) c (fun k => pi (Fin.FS k))
  end.

Lemma fin_proj_fin_tuple (c : C) :
  ∀ (n : nat) (f : Fin.t n → C) (pi : ∀ i, c ~> f i) (i : Fin.t n),
    fin_proj n f i ∘ fin_tuple n f c pi ≈ pi i.
Proof.
  intros n; induction n as [|m IHm]; intros f pi i.
  - exact (Fin.case0
             (fun i => fin_proj 0 f i ∘ fin_tuple 0 f c pi ≈ pi i) i).
  - pattern i; apply (Fin.caseS' i); simpl.
    + apply exl_fork.
    + intro j.
      rewrite <- comp_assoc.
      rewrite exr_fork.
      apply (IHm (fun k => f (Fin.FS k)) (fun k => pi (Fin.FS k)) j).
Qed.

Lemma fin_tuple_unique (c : C) :
  ∀ (n : nat) (f : Fin.t n → C) (pi : ∀ i, c ~> f i)
    (u : c ~> fin_prod n f),
    (∀ i, fin_proj n f i ∘ u ≈ pi i) → u ≈ fin_tuple n f c pi.
Proof.
  intros n; induction n as [|m IHm]; intros f pi u Hu.
  - apply one_unique.
  - simpl.
    apply (snd (ump_products _ _ _)).
    split.
    + apply (Hu Fin.F1).
    + apply IHm.
      intro j.
      rewrite comp_assoc.
      apply (Hu (Fin.FS j)).
Qed.

Definition fin_prod_ump (n : nat) (f : Fin.t n → C)
  (c : C) (pi : ∀ i, c ~> f i) :
  ∃! u : c ~> fin_prod n f, ∀ i, fin_proj n f i ∘ u ≈ pi i.
Proof.
  unshelve eapply Build_Unique.
  - exact (fin_tuple n f c pi).
  - exact (fin_proj_fin_tuple c n f pi).
  - intros v Hv.
    symmetry.
    exact (fin_tuple_unique c n f pi v Hv).
Defined.

Definition fin_IsIndexedProduct (n : nat) (f : Fin.t n → C) :
  IsIndexedProduct f (fin_prod n f) (fin_proj n f) :=
  {| iprod_desc := fun c pi => fin_prod_ump n f c pi |}.

(** ** The small arities *)

Example fin_prod_zero (f : Fin.t 0 → C) : fin_prod 0 f = 1%object := eq_refl.

Example fin_prod_one (f : Fin.t 1 → C) :
  fin_prod 1 f = (f Fin.F1 × 1)%object := eq_refl.

Example fin_prod_two (f : Fin.t 2 → C) :
  fin_prod 2 f = (f Fin.F1 × (f (Fin.FS Fin.F1) × 1))%object := eq_refl.

Example fin_proj_one (f : Fin.t 1 → C) : fin_proj 1 f Fin.F1 = exl := eq_refl.

Example fin_proj_two_snd (f : Fin.t 2 → C) :
  fin_proj 2 f (Fin.FS Fin.F1) = exl ∘ exr := eq_refl.

Example fin_tuple_two (f : Fin.t 2 → C) (c : C) (pi : ∀ i, c ~> f i) :
  fin_tuple 2 f c pi = pi Fin.F1 △ (pi (Fin.FS Fin.F1) △ one) := eq_refl.

Definition fin_prod_one_iso (f : Fin.t 1 → C) : fin_prod 1 f ≅ f Fin.F1 :=
  prod_one_r.

Definition fin_prod_two_iso (f : Fin.t 2 → C) :
  fin_prod 2 f ≅ (f Fin.F1 × f (Fin.FS Fin.F1))%object :=
  prod_respects_iso _ _ iso_id _ _ prod_one_r.

End FiniteProducts.

Arguments fin_prod {C _ _} n f.
Arguments fin_proj {C _ _} n f i.
Arguments fin_tuple {C _ _} n f c pi.

(** ** Reading an indexed product at the two bracketing arities *)

Definition iprod_zero_IsTerminalObj {C : Category} (f : Fin.t 0 → C)
  (p : C) (proj : ∀ i, p ~> f i) (HP : IsIndexedProduct f p proj) :
  IsTerminalObj p.
Proof.
  intro x.
  destruct (iprod_desc HP (@fin0_legs C x f)) as [u _ Hu].
  unshelve eapply Build_Unique.
  - exact u.
  - exact I.
  - intros v _.
    apply Hu.
    exact (fun i => fin0_rect (fun i => proj i ∘ v ≈ fin0_legs f i) i).
Defined.

Section IndexedProductTwo.

Context {C : Category} (x y p : C).
Context (proj : ∀ i, p ~> fin2fam x y i).
Context (HP : IsIndexedProduct (fin2fam x y) p proj).

Definition iprod2_med {a : C} (f : a ~> x) (g : a ~> y) : a ~> p :=
  unique_obj (iprod_desc HP (fin2_legs f g)).

Definition iprod2_med_commutes {a : C} (f : a ~> x) (g : a ~> y) :
  ∀ i, proj i ∘ iprod2_med f g ≈ fin2_legs f g i :=
  unique_property (iprod_desc HP (fin2_legs f g)).

Definition iprod2_med_unique {a : C} (f : a ~> x) (g : a ~> y) (v : a ~> p) :
  (∀ i, proj i ∘ v ≈ fin2_legs f g i) → iprod2_med f g ≈ v :=
  uniqueness (iprod_desc HP (fin2_legs f g)) v.

Definition iprod_two_IsCartesianProduct : @IsCartesianProduct C x y p.
Proof using C HP p proj x y.
  unshelve econstructor.
  - exact (@iprod2_med).
  - exact (proj Fin.F1).
  - exact (proj (Fin.FS Fin.F1)).
  - intros a f1 f2 Hf g1 g2 Hg.
    apply iprod2_med_unique.
    apply (fin2fam_rect
             (fun i => proj i ∘ iprod2_med f2 g2 ≈ fin2_legs f1 g1 i)).
    + etransitivity; [ apply iprod2_med_commutes | symmetry; exact Hf ].
    + etransitivity; [ apply iprod2_med_commutes | symmetry; exact Hg ].
  - intros a f g h.
    split; intros HH.
    + split.
      * rewrite HH; apply (iprod2_med_commutes f g Fin.F1).
      * rewrite HH; apply (iprod2_med_commutes f g (Fin.FS Fin.F1)).
    + destruct HH as [H1 H2].
      symmetry.
      apply iprod2_med_unique.
      exact (fin2fam_rect (fun i => proj i ∘ h ≈ fin2_legs f g i) H1 H2).
Defined.

End IndexedProductTwo.

(** ** Essential uniqueness of an indexed product *)

Section IndexedProductUnique.

Context {C : Category} {A : Type} (f : A → C) (p q : C).
Context (projp : ∀ a, p ~> f a) (projq : ∀ a, q ~> f a).
Context (HP : IsIndexedProduct f p projp).
Context (HQ : IsIndexedProduct f q projq).

Definition iprod_compare : p ~> q := unique_obj (iprod_desc HQ projp).

Definition iprod_compare_inv : q ~> p := unique_obj (iprod_desc HP projq).

Definition iprod_compare_commutes : ∀ a, projq a ∘ iprod_compare ≈ projp a :=
  unique_property (iprod_desc HQ projp).

Definition iprod_compare_inv_commutes :
  ∀ a, projp a ∘ iprod_compare_inv ≈ projq a :=
  unique_property (iprod_desc HP projq).

Definition iprod_unique_iso : p ≅ q.
Proof using A C HP HQ f p projp projq q.
  unshelve econstructor.
  - exact iprod_compare.
  - exact iprod_compare_inv.
  - destruct (iprod_desc HQ projq) as [u _ Hun].
    rewrite <- (Hun id (fun a => id_right (projq a))).
    symmetry.
    apply Hun.
    intro a.
    rewrite comp_assoc.
    rewrite iprod_compare_commutes.
    apply iprod_compare_inv_commutes.
  - destruct (iprod_desc HP projp) as [u _ Hun].
    rewrite <- (Hun id (fun a => id_right (projp a))).
    symmetry.
    apply Hun.
    intro a.
    rewrite comp_assoc.
    rewrite iprod_compare_inv_commutes.
    apply iprod_compare_commutes.
Defined.

End IndexedProductUnique.

Definition Cartesian_of_IsCartesianProduct {C : Category}
  (P : C → C → C) (HP : ∀ x y : C, @IsCartesianProduct C x y (P x y)) :
  @Cartesian C := {|
  product_obj   := P;
  fork          := fun x y z f g => @fork' C y z (P y z) (HP y z) x f g;
  exl           := fun x y => @exl' C x y (P x y) (HP x y);
  exr           := fun x y => @exr' C x y (P x y) (HP x y);
  fork_respects := fun x y z => @fork'_respects C y z (P y z) (HP y z) x;
  ump_products  := fun x y z => @ump_product C y z (P y z) (HP y z) x
|}.

(** ** The class of finite products, and its two directions *)

Class HasFiniteProducts (C : Category) := {
  finite_product {n : nat} (f : Fin.t n → C) : C;
  finite_product_proj {n : nat} (f : Fin.t n → C) (i : Fin.t n) :
    finite_product f ~> f i;
  finite_product_ump {n : nat} (f : Fin.t n → C) :
    IsIndexedProduct f (finite_product f) (finite_product_proj f)
}.

Definition Cartesian_Terminal_HasFiniteProducts {C : Category}
  (CP : @Cartesian C) (T : @Terminal C) : HasFiniteProducts C := {|
  finite_product      := fun n f => fin_prod n f;
  finite_product_proj := fun n f i => fin_proj n f i;
  finite_product_ump  := fun n f => fin_IsIndexedProduct n f
|}.

Definition HasFiniteProducts_Terminal {C : Category}
  (HP : HasFiniteProducts C) : @Terminal C :=
  Terminal_from_IsTerminalObj
    (iprod_zero_IsTerminalObj fin0 (finite_product fin0)
       (finite_product_proj fin0) (finite_product_ump fin0)).

Definition HasFiniteProducts_Cartesian {C : Category}
  (HP : HasFiniteProducts C) : @Cartesian C :=
  Cartesian_of_IsCartesianProduct
    (fun x y => finite_product (fin2fam x y))
    (fun x y => iprod_two_IsCartesianProduct x y
                  (finite_product (fin2fam x y))
                  (finite_product_proj (fin2fam x y))
                  (finite_product_ump (fin2fam x y))).

Theorem HasFiniteProducts_iff (C : Category) :
  HasFiniteProducts C ↔ (@Cartesian C * @Terminal C)%type.
Proof.
  split.
  - intro HP.
    exact (HasFiniteProducts_Cartesian HP, HasFiniteProducts_Terminal HP).
  - intros [CP T].
    exact (Cartesian_Terminal_HasFiniteProducts CP T).
Defined.

(** ** The two bracketing arities of the fold itself *)

Definition fin_zero_IsTerminalObj {C : Category}
  (CP : @Cartesian C) (T : @Terminal C) (f : Fin.t 0 → C) :
  IsTerminalObj (fin_prod 0 f) :=
  iprod_zero_IsTerminalObj f (fin_prod 0 f) (fin_proj 0 f)
    (fin_IsIndexedProduct 0 f).

Definition fin_two_IsCartesianProduct {C : Category}
  (CP : @Cartesian C) (T : @Terminal C) (x y : C) :
  @IsCartesianProduct C x y (fin_prod 2 (fin2fam x y)) :=
  iprod_two_IsCartesianProduct x y (fin_prod 2 (fin2fam x y))
    (fin_proj 2 (fin2fam x y)) (fin_IsIndexedProduct 2 (fin2fam x y)).

(* The right fold is canonically isomorphic to ANY other n-ary product of
   the same family -- a left fold included, once that left fold is shown to
   be an [IsIndexedProduct].  Awodey's ternary one is shown to be one below,
   so this is instantiated rather than left hanging. *)
Definition fin_prod_unique_iso {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (n : nat) (f : Fin.t n → C) (q : C)
  (projq : ∀ i, q ~> f i) (HQ : IsIndexedProduct f q projq) :
  fin_prod n f ≅ q :=
  iprod_unique_iso f (fin_prod n f) q (fin_proj n f) projq
    (fin_IsIndexedProduct n f) HQ.

(* ... and the isomorphism commutes with the projections, in both
   directions.  A bare [≅] would be the weak form. *)
Definition fin_prod_unique_iso_to {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (n : nat) (f : Fin.t n → C) (q : C)
  (projq : ∀ i, q ~> f i) (HQ : IsIndexedProduct f q projq) :
  ∀ i, projq i ∘ to (fin_prod_unique_iso CP T n f q projq HQ)
         ≈ fin_proj n f i :=
  iprod_compare_commutes f (fin_prod n f) q (fin_proj n f) projq HQ.

Definition fin_prod_unique_iso_from {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (n : nat) (f : Fin.t n → C) (q : C)
  (projq : ∀ i, q ~> f i) (HQ : IsIndexedProduct f q projq) :
  ∀ i, fin_proj n f i ∘ from (fin_prod_unique_iso CP T n f q projq HQ)
         ≈ projq i :=
  iprod_compare_inv_commutes f (fin_prod n f) q (fin_proj n f) projq
    (fin_IsIndexedProduct n f).

(** ** Awodey's left-associated ternary product *)

Section AwodeyTernary.

(* NOTE the hypothesis: [Cartesian] alone, with NO [Terminal].  Awodey's
   [A × B × C := (A × B) × C] pads with nothing, which is exactly why the
   terminal object is needed only for the nullary and unary cases. *)
Context {C : Category}.
Context (CP : @Cartesian C).
Context (x y z : C).

Definition awodey_prod : C := ((x × y) × z)%object.

Definition awodey_proj : ∀ i, awodey_prod ~> fin3 x y z i :=
  fin3_rect (fun i => awodey_prod ~> fin3 x y z i)
    (exl ∘ exl) (exr ∘ exl) exr.

Definition awodey_tuple {c : C} (pi : ∀ i, c ~> fin3 x y z i) :
  c ~> awodey_prod :=
  (pi Fin.F1 △ pi (Fin.FS Fin.F1)) △ pi (Fin.FS (Fin.FS Fin.F1)).

(* The three triangles, stated with the projections written out so that no
   tactic has to unfold [awodey_proj]; they are convertible with it. *)
Lemma awodey_tuple_1 {c : C} (pi : ∀ i, c ~> fin3 x y z i) :
  (exl ∘ exl) ∘ awodey_tuple pi ≈ pi Fin.F1.
Proof.
  unfold awodey_tuple.
  rewrite <- comp_assoc, exl_fork.
  apply exl_fork.
Qed.

Lemma awodey_tuple_2 {c : C} (pi : ∀ i, c ~> fin3 x y z i) :
  (exr ∘ exl) ∘ awodey_tuple pi ≈ pi (Fin.FS Fin.F1).
Proof.
  unfold awodey_tuple.
  rewrite <- comp_assoc, exl_fork.
  apply exr_fork.
Qed.

Lemma awodey_tuple_3 {c : C} (pi : ∀ i, c ~> fin3 x y z i) :
  exr ∘ awodey_tuple pi ≈ pi (Fin.FS (Fin.FS Fin.F1)).
Proof.
  unfold awodey_tuple.
  apply exr_fork.
Qed.

Definition awodey_IsIndexedProduct :
  IsIndexedProduct (fin3 x y z) awodey_prod awodey_proj.
Proof using C CP x y z.
  constructor.
  intros c pi.
  unshelve eapply Build_Unique.
  - exact (awodey_tuple pi).
  - apply (fin3_rect (fun i => awodey_proj i ∘ awodey_tuple pi ≈ pi i)).
    + exact (awodey_tuple_1 pi).
    + exact (awodey_tuple_2 pi).
    + exact (awodey_tuple_3 pi).
  - intros v Hv.
    unfold awodey_tuple.
    symmetry.
    apply (snd (ump_products _ _ _)).
    split.
    + apply (snd (ump_products _ _ _)).
      split.
      * rewrite comp_assoc.
        exact (Hv Fin.F1).
      * rewrite comp_assoc.
        exact (Hv (Fin.FS Fin.F1)).
    + exact (Hv (Fin.FS (Fin.FS Fin.F1))).
Defined.

End AwodeyTernary.

(* Awodey §2.7's displayed ternary product IS this file's right fold, up to
   a canonical isomorphism commuting with all three projections. *)
Definition awodey_fold_iso {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (x y z : C) :
  fin_prod 3 (fin3 x y z) ≅ awodey_prod CP x y z :=
  fin_prod_unique_iso CP T 3 (fin3 x y z) (awodey_prod CP x y z)
    (awodey_proj CP x y z) (awodey_IsIndexedProduct CP x y z).

Definition awodey_fold_iso_to {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (x y z : C) :
  ∀ i, awodey_proj CP x y z i ∘ to (awodey_fold_iso CP T x y z)
         ≈ fin_proj 3 (fin3 x y z) i :=
  fin_prod_unique_iso_to CP T 3 (fin3 x y z) (awodey_prod CP x y z)
    (awodey_proj CP x y z) (awodey_IsIndexedProduct CP x y z).

Definition awodey_fold_iso_from {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (x y z : C) :
  ∀ i, fin_proj 3 (fin3 x y z) i ∘ from (awodey_fold_iso CP T x y z)
         ≈ awodey_proj CP x y z i :=
  fin_prod_unique_iso_from CP T 3 (fin3 x y z) (awodey_prod CP x y z)
    (awodey_proj CP x y z) (awodey_IsIndexedProduct CP x y z).

(** ** The dual *)

Section FiniteCoproducts.

Context {C : Category}.
Context (CC : @Cocartesian C).
Context (I : @Initial C).

Definition fin_coprod (n : nat) (f : Fin.t n → C) : C :=
  @fin_prod (C^op) CC I n f.

Definition fin_inj (n : nat) (f : Fin.t n → C) (i : Fin.t n) :
  f i ~> fin_coprod n f :=
  @fin_proj (C^op) CC I n f i.

Definition fin_cotuple (n : nat) (f : Fin.t n → C) (c : C)
  (iota : ∀ i, f i ~> c) : fin_coprod n f ~> c :=
  @fin_tuple (C^op) CC I n f c iota.

Definition fin_coprod_ump (n : nat) (f : Fin.t n → C)
  (c : C) (iota : ∀ i, f i ~> c) :
  ∃! u : fin_coprod n f ~> c, ∀ i, u ∘ fin_inj n f i ≈ iota i :=
  @fin_prod_ump (C^op) CC I n f c iota.

Definition fin_IsIndexedCoproduct (n : nat) (f : Fin.t n → C) :
  IsIndexedCoproduct f (fin_coprod n f) (fin_inj n f) :=
  @fin_IsIndexedProduct (C^op) CC I n f.

End FiniteCoproducts.

Arguments fin_coprod {C} CC I n f.
Arguments fin_inj {C} CC I n f i.
Arguments fin_cotuple {C} CC I n f c iota.

Definition HasFiniteCoproducts (C : Category) : Type :=
  @HasFiniteProducts (C^op).

Existing Class HasFiniteCoproducts.

Definition Build_HasFiniteCoproducts {C : Category}
  (cobj : ∀ n : nat, (Fin.t n → C) → C)
  (cinj : ∀ (n : nat) (f : Fin.t n → C) (i : Fin.t n), f i ~> cobj n f)
  (cump : ∀ (n : nat) (f : Fin.t n → C),
            IsIndexedCoproduct f (cobj n f) (cinj n f)) :
  HasFiniteCoproducts C :=
  @Build_HasFiniteProducts (C^op) cobj cinj cump.

Section FiniteCoproductAPI.

Context {C : Category}.
Context {H : HasFiniteCoproducts C}.

Definition finite_coproduct {n : nat} (f : Fin.t n → C) : C :=
  @finite_product (C^op) H n f.

Definition finite_coproduct_inj {n : nat} (f : Fin.t n → C) (i : Fin.t n) :
  f i ~> finite_coproduct f :=
  @finite_product_proj (C^op) H n f i.

Definition finite_coproduct_ump {n : nat} (f : Fin.t n → C) :
  IsIndexedCoproduct f (finite_coproduct f) (finite_coproduct_inj f) :=
  @finite_product_ump (C^op) H n f.

End FiniteCoproductAPI.

Definition Cocartesian_Initial_HasFiniteCoproducts {C : Category}
  (CC : @Cocartesian C) (I : @Initial C) : HasFiniteCoproducts C :=
  @Cartesian_Terminal_HasFiniteProducts (C^op) CC I.

Definition HasFiniteCoproducts_Cocartesian {C : Category}
  (HP : HasFiniteCoproducts C) : @Cocartesian C :=
  @HasFiniteProducts_Cartesian (C^op) HP.

Definition HasFiniteCoproducts_Initial {C : Category}
  (HP : HasFiniteCoproducts C) : @Initial C :=
  @HasFiniteProducts_Terminal (C^op) HP.

(** ** Non-vacuity: the fold computes *)

Example coq_fin_prod_zero (f : Fin.t 0 → Coq) :
  fin_prod 0 f = unit := eq_refl.

Example coq_fin_prod_three :
  fin_prod 3 (fun _ : Fin.t 3 => nat : Coq)
    = (nat * (nat * (nat * unit)))%type := eq_refl.

Example coq_fin_prod_mixed :
  fin_prod 2 (fin2fam (bool : Coq) (nat : Coq))
    = (bool * (nat * unit))%type := eq_refl.

Example coq_fin_tuple_computes :
  fin_tuple 2 (fin2fam (bool : Coq) (nat : Coq)) (nat : Coq)
    (fin2_legs (fun n : nat => Nat.eqb n O) (fun n : nat => S n))
    (S (S (S O))) = (false, (S (S (S (S O))), tt)) := eq_refl.

Example coq_fin_proj_computes :
  fin_proj 2 (fin2fam (bool : Coq) (nat : Coq)) (Fin.FS Fin.F1)
    (true, (S (S O), tt)) = S (S O) := eq_refl.
