Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Comma.
Require Import Category.Construction.FAlg.
Require Import Category.Construction.Funny.Comparison.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Coq.Lists.
Require Import List.

Generalizable All Variables.

(** * The free monoid on a type, and its universal property *)

(* nLab:      https://ncatlab.org/nlab/show/free+monoid
   Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

   For a type [X], the free monoid on [X] is the type [list X] of finite words
   over [X], multiplied by concatenation with the empty word as unit, together
   with the insertion of generators [p : X → list X] sending a letter to the
   one-letter word.  Its universal property is that [p] is universal among maps
   from [X] into (the underlying set of) a monoid: every [h : X → U L] extends
   along [p] to one and only one monoid homomorphism [list X → L], namely the
   fold that replaces concatenation by the multiplication of [L] and the empty
   word by its unit.

   Everything here is developed at [Mon Coq], the category of monoid objects
   (Theory/Algebra/Monoid.v) in the cartesian monoidal category of Coq types
   (Instance/Coq.v, [Coq_Monoidal]), with [Mon_Forget] as the underlying-type
   functor U.  A monoid object over that base is exactly an ordinary monoid:
   [mu : x * x → x], [eta : unit → x], and the three laws are associativity and
   the two unit laws with the cartesian associator and unitors — which over
   [Coq] are the evident reassociation and projections — inserted to make the
   maps composable.  Morphism equivalence in [Coq] is pointwise Leibniz
   equality, so no function extensionality is needed anywhere below: two
   monoid homomorphisms are identified exactly when they agree at every word,
   which is what list induction proves.

   The book statements this file discharges are quoted from the catalog
   inventories under doc/plan/books/{maclane,awodey,7sketches}/inventory/, and
   the wordings paraphrased here are the CATALOG'S PARAPHRASE, not the books'
   own wording.  A recap mapping each catalog item to the constants that
   deliver it closes this header. *)

(* Free constructions, folds, and why the monoid case is the one everyone
   meets first

   nLab:      https://ncatlab.org/nlab/show/free+monoid
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Free_monoid
   Wikipedia: https://en.wikipedia.org/wiki/Kleene_star

   The free monoid is the oldest surviving example of a universal mapping
   problem and, by some distance, the most heavily used.  Under the name
   "Kleene star" it is the closure operation of formal language theory:
   Kleene introduced A* while analysing the events representable in nerve
   nets, and the star of an alphabet is precisely the underlying set of the
   free monoid on that alphabet (Kleene, "Representation of events in nerve
   nets and finite automata", in Shannon and McCarthy, Automata Studies,
   Princeton 1956; Wikipedia, "Kleene star").  Every statement about strings
   — concatenation is associative, the empty string is neutral, a
   substitution is determined by its action on single letters — is a
   statement about this monoid, and the last of those is exactly the
   universal property proved below.

   Mac Lane presents it as a corollary rather than a construction.  The free
   category on a graph is built in CWM §II.7, and the free monoid falls out
   by reading a monoid as a one-object category: a graph with one vertex is a
   set of loops, and the free category on it has the words in those loops as
   arrows (Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Springer 1998, §II.7 Corollary 2, pp. 50–51).  Awodey goes the other way,
   constructing A* directly in §1.7 and using it as the first non-trivial
   universal property in the book, then returning to it in §9.1 as the
   motivating adjunction (Awodey, "Category Theory", 1st ed., Carnegie Mellon
   pre-print, September 2005, §1.7 pp. 19–22, §9.1 pp. 213–214).  Fong and
   Spivak reach the same object through the free category on the one-vertex
   loop graph and ask for its elements at a two-letter alphabet (Fong and
   Spivak, "An Invitation to Applied Category Theory: Seven Sketches in
   Compositionality", CUP 2019, §5.2.3 Exercise 5.24).  In-tree both routes
   exist: Construction/Free/Quiver.v carries the free category on a quiver
   with its universal arrow, and this file carries the monoid case directly.
   The identification of the two — free monoid as the delooping of the free
   category on a one-vertex quiver — is NOT proved here; see the deferral
   note at the end of this header.

   The programming-language reading is the fold.  A [Foldable] container is
   one that maps into any monoid, and the fold of a list is the unique monoid
   homomorphism out of the free monoid determined by the element map; this is
   why [foldMap] takes a function into a monoid and nothing more.  In-tree
   Theory/Coq/Foldable.v states that correspondence in prose over an ops-only
   class, and Instance/Coq/Lists.v proves the sibling fact that [list A] is
   the initial algebra of [ListF A X = 1 + A × X], whose unique algebra map is
   the same fold.  The bridge between the two universal properties — the
   monoid-homomorphism extension IS the [ListF]-algebra fold — is proved
   below ([free_ext_is_fold], [free_ext_is_the_unique_algebra_map]), which is
   the sense in which "structural recursion over lists" and "the free monoid"
   are one fact seen twice.

   Finally, the adjunction.  Free-forgetful adjunctions are the paradigm case
   of Kan's notion, and this one is the example every introduction uses: the
   left adjoint of the underlying-set functor on monoids.  Its unit is the
   insertion of generators, natural because a homomorphism out of a free
   monoid is determined by its action on generators (Awodey §7.5 Example
   7.7); its counit at a monoid L is the evaluation of words in L, and the
   fact that the counit's underlying map splits — every element is the value
   of its own one-letter word — is the categorical form of "every monoid is a
   quotient of a free one" (Awodey §9.9 Exercise 2).  The pattern generalises
   verbatim to groups, rings, modules and algebras, which is why Samuel could
   already see one problem behind all of them (Theory/Universal/Arrow.v's
   header tells that story). *)

#[local] Notation MonCoq := (@Mon Coq Coq_Monoidal).
#[local] Notation UMon := (@Mon_Forget Coq Coq_Monoidal).

#[local] Obligation Tactic := idtac.

(** ** An element-level view of a monoid object over [Coq]

    The three [Monoid] laws are stated with the cartesian associator and
    unitors inserted.  Over [Coq] those are the evident reassociation and
    projections, so each law instantiated at an explicit tuple is an ordinary
    equation between elements.  Naming those instances once keeps every proof
    below free of tensor bookkeeping. *)

Section Elements.

Context (L : MonCoq).

Definition mmul (a b : `1 L) : `1 L := mu[`2 L] (a, b).
Definition mone : `1 L := eta[`2 L] tt.

Lemma mmul_assoc (a b c : `1 L) : mmul (mmul a b) c = mmul a (mmul b c).
Proof. exact (@mu_assoc Coq Coq_Monoidal _ (`2 L) ((a, b), c)). Qed.

Lemma mone_left (a : `1 L) : mmul mone a = a.
Proof. exact (@mu_unit_left Coq Coq_Monoidal _ (`2 L) (tt, a)). Qed.

Lemma mone_right (a : `1 L) : mmul a mone = a.
Proof. exact (@mu_unit_right Coq Coq_Monoidal _ (`2 L) (a, tt)). Qed.

End Elements.

Arguments mmul {L} a b.
Arguments mone {L}.

(* The two homomorphism laws in the same element-level form. *)
Lemma hom_mmul {L N : MonCoq} (g : L ~{MonCoq}~> N) (a b : `1 L) :
  `1 g (mmul a b) = mmul (`1 g a) (`1 g b).
Proof. exact (@hom_mu Coq Coq_Monoidal _ _ _ _ _ (`2 g) (a, b)). Qed.

Lemma hom_mone {L N : MonCoq} (g : L ~{MonCoq}~> N) :
  `1 g (@mone L) = @mone N.
Proof. exact (@hom_eta Coq Coq_Monoidal _ _ _ _ _ (`2 g) tt). Qed.

(** ** The free monoid: words under concatenation

    Mac Lane §II.7 Corollary 2 and Awodey §1.7: for a type [X] the finite
    words over [X] form a monoid under concatenation with the empty word as
    unit.  The unit laws hold on the nose in one direction ([nil ++ l] is
    [l] by computation) and by [app_nil_r] in the other. *)

Program Definition FreeMonoidStructure (X : Type) :
  @Monoid Coq Coq_Monoidal (list X) := {|
  mu  := fun p => (fst p ++ snd p)%list;
  eta := fun _ => @nil X
|}.
Next Obligation.
  intros X p; destruct p as [[a b] c]; simpl.
  symmetry; apply app_assoc.
Qed.
Next Obligation.
  intros X p; destruct p as [u a]; destruct u; reflexivity.
Qed.
Next Obligation.
  intros X p; destruct p as [a u]; simpl.
  apply app_nil_r.
Qed.

(* The free monoid on [X] as an object of [Mon Coq]. *)
Definition FreeMon (X : Coq) : MonCoq := (list X; FreeMonoidStructure X).

(* Its multiplication and unit are concatenation and the empty word, on the
   nose. *)
Example free_mmul_is_app (X : Coq) (u v : list X) :
  mmul (L:=FreeMon X) u v = (u ++ v)%list := eq_refl.

Example free_mone_is_nil (X : Coq) : @mone (FreeMon X) = @nil X := eq_refl.

(** ** The insertion of generators

    Awodey's [i : A → A*], sending a letter to the one-letter word. *)

Definition insert (X : Coq) : X ~{Coq}~> UMon (FreeMon X) :=
  fun a => (a :: nil)%list.

(** ** The extension of a map into a monoid: the fold

    Awodey §1.7 Proposition 1.9 computes the extension of [h : A → |N|] as
    [f(a₁…aᵢ) = h(a₁) * … * h(aᵢ)], the empty word going to the unit.  That
    is the right fold. *)

Fixpoint free_ext {X : Coq} {L : MonCoq} (h : X → `1 L) (l : list X)
  : `1 L :=
  match l with
  | nil       => @mone L
  | cons a l' => mmul (h a) (free_ext h l')
  end.

(* The extension carries concatenation to multiplication: induction on the
   left word, using the left unit law at [nil] and associativity at [cons]. *)
Lemma free_ext_app {X : Coq} {L : MonCoq} (h : X → `1 L) (u v : list X) :
  free_ext h (u ++ v)%list = mmul (free_ext h u) (free_ext h v).
Proof.
  induction u as [|a u IH]; simpl.
  - symmetry; apply mone_left.
  - rewrite IH; symmetry; apply mmul_assoc.
Qed.

(* ... and it agrees with [h] on the generators, by computation. *)
Lemma free_ext_generators {X : Coq} {L : MonCoq} (h : X → `1 L) (a : X) :
  free_ext h (insert X a) = h a.
Proof. simpl; apply mone_right. Qed.

(* Hence it is a monoid homomorphism out of the free monoid. *)
Program Definition free_ext_MonoidHom {X : Coq} {L : MonCoq} (h : X → `1 L) :
  @MonoidHom Coq Coq_Monoidal (list X) (`1 L)
             (FreeMonoidStructure X) (`2 L) (free_ext h) := {|
  hom_mu  := _;
  hom_eta := _
|}.
Next Obligation.
  intros X L h p; destruct p as [u v]; simpl.
  apply free_ext_app.
Qed.
Next Obligation. intros X L h u; destruct u; reflexivity. Qed.

Definition free_hom {X : Coq} {L : MonCoq} (h : X → `1 L)
  : FreeMon X ~{MonCoq}~> L :=
  (free_ext h; free_ext_MonoidHom h).

(* Uniqueness: any monoid homomorphism out of the free monoid agreeing with
   [h] on the generators IS the fold.  This is the list induction of Awodey
   §1.7 Proposition 1.9, and it uses both homomorphism laws — the unit law at
   the empty word, the multiplication law at the [cons] split
   [a :: l = (a :: nil) ++ l]. *)
Lemma free_ext_unique {X : Coq} {L : MonCoq} (h : X → `1 L)
      (g : FreeMon X ~{MonCoq}~> L)
      (Hg : forall a : X, `1 g (insert X a) = h a) (l : list X) :
  `1 g l = free_ext h l.
Proof.
  induction l as [|a l IH]; simpl.
  - exact (hom_mone g).
  - rewrite <- IH, <- (Hg a).
    exact (hom_mmul g (a :: nil)%list l).
Qed.

(** ** The universal property

    Awodey §1.7 Proposition 1.9, in the shape
    [Theory/Universal/Arrow.v]'s [universal_arrow_from_UMP] consumes: for
    every monoid [L] and every [h : X → U L] there is exactly one monoid
    homomorphism [g] with [U g ∘ insert ≈ h].  Uniqueness is up to the
    ambient [≈], which in [Mon Coq] is pointwise equality of the underlying
    functions. *)

Theorem free_monoid_universal (X : Coq) :
  forall (L : MonCoq) (h : X ~{Coq}~> UMon L),
    ∃! g : FreeMon X ~{MonCoq}~> L, h ≈ fmap[UMon] g ∘ insert X.
Proof.
  intros L h.
  unshelve eexists.
  - exact (free_hom h).
  - intro a; simpl.
    symmetry; apply free_ext_generators.
  - intros g Hg a; simpl.
    symmetry; apply free_ext_unique.
    intro b; symmetry; exact (Hg b).
Qed.

(* The free monoid packaged as a universal arrow from [X] to [Mon_Forget].
   By [Theory/Universal/Arrow.v] this IS an initial object of the comma
   category [=(X) ↓ Mon_Forget]. *)
Definition free_monoid_universal_arrow (X : Coq) : UniversalArrow X UMon :=
  universal_arrow_from_UMP X UMon (FreeMon X) (insert X)
                           (free_monoid_universal X).

(* The same content in the direct encoding, where the universal object is
   named rather than projected. *)
Program Definition free_monoid_AUniversalArrow (X : Coq)
  : AUniversalArrow X UMon (FreeMon X) := {|
  universal_arrow := insert X
|}.
Next Obligation.
  intros X L h.
  unshelve eexists.
  - exact (free_hom h).
  - intro a; simpl; apply free_ext_generators.
  - intros g Hg a; simpl.
    symmetry; apply free_ext_unique.
    intro b; exact (Hg b).
Qed.

(** ** The free-forgetful adjunction

    Awodey §9.1.  The free functor and the adjunction are assembled by the
    generic machinery of Theory/Universal/Arrow.v from the family of
    universal arrows. *)

Definition FreeMonoid : Coq ⟶ MonCoq :=
  LeftAdjointFunctorFromUniversalArrows UMon free_monoid_universal_arrow.

Definition free_monoid_adjunction : FreeMonoid ⊣ UMon :=
  AdjunctionFromUniversalArrows UMon free_monoid_universal_arrow.

(* The free functor's object part is the word monoid, definitionally. *)
Example FreeMonoid_obj (X : Coq) : FreeMonoid X = FreeMon X := eq_refl.

(* The universal arrow of [free_monoid_universal_arrow] is the insertion of
   generators on the nose: [universal_arrow_from_UMP] stores the supplied
   morphism as the second projection of the comma object it builds, so no
   proof is involved. *)
Example free_arrow_is_insert (X : Coq) :
  @arrow _ _ X UMon (free_monoid_universal_arrow X) = insert X := eq_refl.

(* Hence so is the unit of the adjunction: the transpose of the identity is
   [fmap[U] id ∘ arrow], and [fmap[U] id] is the identity function. *)
Example free_monoid_unit_is_insert (X : Coq) (a : X) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_monoid_adjunction X a
    = insert X a := eq_refl.

(** ** The free functor acts on arrows as [List.map]

    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a word has to
    be proved.  It is [map]: the defining factorization says exactly that
    generators go to generators, and the uniqueness half of the universal
    property then identifies the homomorphism with [map]. *)

Lemma free_fmap_generators {X Y : Coq} (f : X ~{Coq}~> Y) (a : X) :
  `1 (fmap[FreeMonoid] f) (insert X a) = insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_monoid_universal_arrow X)
              (@arrow _ _ Y UMon (free_monoid_universal_arrow Y) ∘ f)) a).
Qed.

(* The fold of [a ↦ [f a]] into the free monoid on Y is [map f]. *)
Lemma free_ext_insert {X Y : Coq} (f : X ~{Coq}~> Y) (l : list X) :
  free_ext (L:=FreeMon Y) (fun a => insert Y (f a)) l = map f l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|now rewrite IH].
Qed.

Theorem free_fmap_is_map {X Y : Coq} (f : X ~{Coq}~> Y) (l : list X) :
  `1 (fmap[FreeMonoid] f) l = map f l.
Proof.
  etransitivity.
  - apply (free_ext_unique (L:=FreeMon Y) (fun a => insert Y (f a))
             (fmap[FreeMonoid] f) (free_fmap_generators f) l).
  - apply free_ext_insert.
Qed.

(** ** The insertion of generators as a natural transformation

    Awodey §7.5 Example 7.7: [η_X : X → U M(X)] is natural in X, "because the
    induced homomorphism M(f) is determined by its action on generators".
    That sentence is [free_fmap_generators], and it is the whole naturality
    square. *)

Program Definition insert_Transform : Id[Coq] ⟹ UMon ◯ FreeMonoid := {|
  transform := insert
|}.
Next Obligation. intros X Y f a; apply free_fmap_generators. Qed.
Next Obligation. intros X Y f a; symmetry; apply free_fmap_generators. Qed.

(* It is the unit of the adjunction, componentwise on the nose — so the
   instance asked for by Awodey's example and the generic transformation
   produced from any adjunction by [Adjunction_to_Transform]
   (Adjunction/Natural/Transformation/Universal.v) agree. *)
Example insert_Transform_is_adjunction_unit (X : Coq) (a : X) :
  transform[insert_Transform] X a
    = transform[@unit _ _ _ _
                  (@Adjunction_to_Transform _ _ _ _ free_monoid_adjunction)] X a
  := eq_refl.

(** ** The transposition formula

    Awodey §9.1 asks for the bijection between monoid homomorphisms out of
    the free monoid and functions into the underlying set.  That bijection is
    [adj] of [free_monoid_adjunction]; the formula for its forward direction
    is the generic [to_adj_unit] read at this adjunction, and unwinds to
    "restrict the homomorphism to the one-letter words". *)

Corollary free_monoid_transposition {X : Coq} {L : MonCoq}
      (g : FreeMonoid X ~{MonCoq}~> L) :
  to (@adj _ _ _ _ free_monoid_adjunction X L) g
    ≈ fmap[UMon] g ∘ insert X.
Proof. exact (@to_adj_unit _ _ _ _ free_monoid_adjunction X L g). Qed.

Corollary free_monoid_transposition_at {X : Coq} {L : MonCoq}
      (g : FreeMonoid X ~{MonCoq}~> L) (a : X) :
  to (@adj _ _ _ _ free_monoid_adjunction X L) g a = `1 g (insert X a).
Proof. exact (free_monoid_transposition g a). Qed.

(* The inverse direction is the fold: transposing a function back gives the
   homomorphism that extends it. *)
Corollary free_monoid_transposition_inv {X : Coq} {L : MonCoq}
      (h : X ~{Coq}~> UMon L) (l : list X) :
  `1 (from (@adj _ _ _ _ free_monoid_adjunction X L) h) l = free_ext h l.
Proof.
  apply free_ext_unique.
  intro a.
  etransitivity.
  - symmetry.
    exact (@free_monoid_transposition_at X L
             (from (@adj _ _ _ _ free_monoid_adjunction X L) h) a).
  - exact (@from_adj_comp_law _ _ _ _ free_monoid_adjunction X L h a).
Qed.

(** ** The counit, and "every monoid is a quotient of a free one"

    Awodey §9.9 Exercise 2.  Two statements have to be kept apart, and the
    library had neither: [Theory/Adjunction.v]'s [adj_monic] is the mono-side
    result and has no epi counterpart.

    (a) The counit's IMAGE under U is a SPLIT epimorphism, split by the unit.
        This holds for every adjunction with no hypothesis at all: it is one
        of the two triangle identities, [fmap_counit_unit].

    (b) The counit ITSELF is an epimorphism, provided U is faithful.  This
        does need the hypothesis, and [Mon_Forget_Faithful] supplies it here.

    What is NOT claimed is that the counit is a split epimorphism in Mon: a
    section would have to be a monoid homomorphism [L → M(U L)], and the
    evident candidate [m ↦ [m]] is not one (it sends a product to a
    one-letter word, not to a two-letter one).  Whether some other section
    exists depends on L, so no general statement of that shape is available,
    and none is needed: the exercise's "quotient" is the surjection of
    underlying sets, which is (a). *)

Section AdjunctionCounit.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* (a) [U ε] splits, with the unit as its section. *)
Program Definition adjunction_counit_underlying_retraction (x : C) :
  Retraction (fmap[U] (@Category.Theory.Adjunction.counit _ _ _ _ A x)) := {|
  retract := @Category.Theory.Adjunction.unit _ _ _ _ A (U x)
|}.
Next Obligation.
  intro x.
  exact (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ A x).
Qed.

(* (b) A faithful right adjoint makes the counit epic: transport the
   cancellation through U, where the split from (a) does the work. *)
Program Definition adjunction_counit_epic (FU : Faithful U) (x : C) :
  Epic (@Category.Theory.Adjunction.counit _ _ _ _ A x) := {| epic := _ |}.
Next Obligation.
  intros FU x z g1 g2 Heq.
  apply (fmap_inj (F:=U)).
  rewrite <- (id_right (fmap[U] g1)), <- (id_right (fmap[U] g2)).
  rewrite <- (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ A x).
  rewrite !comp_assoc, <- !fmap_comp.
  now rewrite Heq.
Qed.

End AdjunctionCounit.

(* The free-monoid instances. *)
Definition free_monoid_counit_underlying_retraction (L : MonCoq) :
  Retraction (fmap[UMon]
                (@Category.Theory.Adjunction.counit _ _ _ _
                   free_monoid_adjunction L)) :=
  adjunction_counit_underlying_retraction free_monoid_adjunction L.

Definition free_monoid_counit_epic (L : MonCoq) :
  Epic (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L) :=
  adjunction_counit_epic free_monoid_adjunction
    (@Mon_Forget_Faithful Coq Coq_Monoidal) L.

(* Concretely: every element of L is the value of its own one-letter word, so
   the underlying map of the counit is surjective with a chosen preimage. *)
Corollary free_monoid_counit_surjective (L : MonCoq) (m : `1 L) :
  `1 (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L)
     (insert (UMon L) m) = m.
Proof. exact (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ free_monoid_adjunction L m). Qed.

(* And the counit is the evaluation of a word in L: the fold of the identity
   map on the underlying type. *)
Theorem free_monoid_counit_is_free_ext (L : MonCoq) (w : list (`1 L)) :
  `1 (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L) w
    = free_ext (fun m : `1 L => m) w.
Proof.
  apply free_ext_unique.
  exact (free_monoid_counit_surjective L).
Qed.

(** ** Uniqueness of the free monoid

    Awodey §1.7 Proposition 1.10: two monoids satisfying the free-monoid
    universal property on the same generating type are related by a unique
    isomorphism commuting with the generator insertions.  The generic lemma
    is [auniversal_arrow_unique] (Theory/Universal/Arrow.v, added for this
    purpose); what is specific here is only that [FreeMon X] inhabits the
    hypothesis. *)

Definition free_monoid_unique {X : Coq} {M N : MonCoq}
      (UM : AUniversalArrow X UMon M) (UN : AUniversalArrow X UMon N) :
  Unique (fun i : M ≅ N =>
            fmap[UMon] (to i) ∘ @universal_arrow _ _ X UMon M UM
              ≈ @universal_arrow _ _ X UMon N UN) :=
  auniversal_arrow_unique UM UN.

(* At the word monoid: any monoid with the free-monoid UMP on X is uniquely
   isomorphic to [FreeMon X] over the insertion of generators. *)
Definition free_monoid_unique_iso {X : Coq} {N : MonCoq}
      (UN : AUniversalArrow X UMon N) :
  Unique (fun i : FreeMon X ≅ N =>
            fmap[UMon] (to i) ∘ insert X
              ≈ @universal_arrow _ _ X UMon N UN) :=
  auniversal_arrow_unique (free_monoid_AUniversalArrow X) UN.

(** ** The comma presentation: Awodey's category A-Mon

    Awodey §2.9 Exercise 4 defines A-**Mon**: objects are monoids M together
    with a function A → U M, arrows are monoid homomorphisms commuting with
    those structure maps, and the exercise is to show that an initial object
    of A-**Mon** is the same thing as a free monoid on A.

    That category IS the comma category [=(X) ↓ Mon_Forget] — its objects are
    triples (ttt, L, h : X ~> U L), and a morphism to (ttt, N, k) is a pair
    consisting of the unique arrow of the one-object category and a monoid
    homomorphism g with k ∘ id ≈ U g ∘ h.  The "same thing" is then not a
    theorem to prove but the DEFINITION of [UniversalArrow] in
    Theory/Universal/Arrow.v, whose only field is an initial object of that
    comma category; both directions are recorded below as named constants so
    that the identification is stated rather than left implicit. *)

Definition AMon (X : Coq) : Category := (=(X) ↓ UMon).

Definition AMon_ob {X : Coq} (L : MonCoq) (h : X ~{Coq}~> UMon L) : AMon X :=
  ((ttt, L); h).

Program Definition AMon_hom {X : Coq} {L N : MonCoq}
        {h : X ~{Coq}~> UMon L} {k : X ~{Coq}~> UMon N}
        (g : L ~{MonCoq}~> N) (Hg : k ≈ fmap[UMon] g ∘ h) :
  AMon_ob L h ~{AMon X}~> AMon_ob N k := ((id, g); _).
Next Obligation.
  intros X L N h k g Hg.
  simpl.
  rewrite ?fmap_id, ?id_right.
  assumption.
Qed.

(* Forward: the free monoid is an initial object of A-Mon. *)
Definition free_monoid_initial (X : Coq) : @Initial (AMon X) :=
  @arrow_initial _ _ X UMon (free_monoid_universal_arrow X).

Example free_monoid_initial_obj (X : Coq) :
  @initial_obj (AMon X) (free_monoid_initial X) = AMon_ob (FreeMon X) (insert X)
  := eq_refl.

(* Backward: an initial object of A-Mon is a universal arrow, hence a free
   monoid on X together with its insertion of generators. *)
Definition AMon_initial_universal_arrow (X : Coq) (I : @Initial (AMon X))
  : UniversalArrow X UMon := {| arrow_initial := I |}.

Example AMon_initial_round (X : Coq) :
  @arrow_initial _ _ X UMon
    (AMon_initial_universal_arrow X (free_monoid_initial X))
  = free_monoid_initial X := eq_refl.

(** ** Words over a two-element set, and [ListMon]

    Fong and Spivak, Seven Sketches §5.2.3 Exercise 5.24(3), asks for the
    elements of the free monoid on a two-element set: the words over {a, b}.
    Taking [bool] as that set, [FreeMon bool] has [list bool] as its
    underlying type, multiplication is concatenation, and the unit is the
    empty word — all by computation.

    [ListMon] (Construction/Funny/Comparison.v) is the one-object category
    with [list bool] as its hom-set, built there as a discriminating target
    for the funny tensor product and never identified as a free monoid.  It
    is one: its hom-set IS the underlying type of [FreeMon bool], its
    identity IS the unit, and its composition IS the multiplication with the
    arguments in diagrammatic order — the file's own header notes that
    "words read source-to-target while composition reads right-to-left", and
    the equations below pin that down. *)

Example ListMon_hom_is_free_carrier :
  (ttt ~{ListMon}~> ttt) = UMon (FreeMon bool) := eq_refl.

Example ListMon_id_is_free_unit :
  @id ListMon ttt = @mone (FreeMon bool) := eq_refl.

Example ListMon_compose_is_free_mul (u v : list bool) :
  @compose ListMon ttt ttt ttt u v = mmul (L:=FreeMon bool) v u := eq_refl.

(* Two letters, and words in them. *)
Definition wa : list bool := (true :: nil)%list.
Definition wb : list bool := (false :: nil)%list.

Example wa_is_generator : wa = insert bool true := eq_refl.
Example wb_is_generator : wb = insert bool false := eq_refl.

Example word_ab :
  mmul (L:=FreeMon bool) wa wb = (true :: false :: nil)%list := eq_refl.
Example word_ba :
  mmul (L:=FreeMon bool) wb wa = (false :: true :: nil)%list := eq_refl.
Example word_noncommutative :
  mmul (L:=FreeMon bool) wa wb <> mmul (L:=FreeMon bool) wb wa.
Proof. discriminate. Qed.
Example word_assoc :
  mmul (L:=FreeMon bool) (mmul (L:=FreeMon bool) wa wb) wa
    = mmul (L:=FreeMon bool) wa (mmul (L:=FreeMon bool) wb wa) := eq_refl.
Example word_unit_left :
  mmul (L:=FreeMon bool) (@mone (FreeMon bool)) wa = wa := eq_refl.
Example word_unit_right :
  mmul (L:=FreeMon bool) wa (@mone (FreeMon bool)) = wa := eq_refl.

(* A target monoid to fold into, so the universal property is exercised on
   closed data rather than merely stated: [bool] under exclusive or, with
   [false] as unit.  (Deliberately not (ℕ, +): the reading of ℕ as the free
   monoid on one generator is issue #802's, not this file's.) *)

Program Definition XorMonoidStructure : @Monoid Coq Coq_Monoidal bool := {|
  mu  := fun p => xorb (fst p) (snd p);
  eta := fun _ => false
|}.
Next Obligation.
  intros p; destruct p as [[a b] c]; simpl.
  apply Bool.xorb_assoc_reverse.
Qed.
Next Obligation. intros p; destruct p as [u a]; destruct u; reflexivity. Qed.
Next Obligation.
  intros p; destruct p as [a u]; simpl; apply Bool.xorb_false_r.
Qed.

Definition XorMon : MonCoq := (bool; XorMonoidStructure).

(* The extension of the identity map on letters counts the parity of the word,
   and computes. *)
Example fold_into_xor_1 :
  free_ext (L:=XorMon) (fun b : bool => b) (true :: false :: true :: nil)%list
    = false := eq_refl.

Example fold_into_xor_2 :
  `1 (free_hom (L:=XorMon) (fun b : bool => b))
     (mmul (L:=FreeMon bool) wa wb) = true := eq_refl.

(* And it really is a monoid homomorphism out of the word monoid, computed on
   a concatenation. *)
Example fold_into_xor_hom :
  `1 (free_hom (L:=XorMon) (fun b : bool => b))
     (mmul (L:=FreeMon bool) (mmul (L:=FreeMon bool) wa wa) wb)
    = mmul (L:=XorMon)
        (`1 (free_hom (L:=XorMon) (fun b : bool => b))
            (mmul (L:=FreeMon bool) wa wa))
        (`1 (free_hom (L:=XorMon) (fun b : bool => b)) wb) := eq_refl.

(** ** Bridge to the initial [ListF]-algebra

    Instance/Coq/Lists.v proves [list A] initial among [ListF A]-algebras,
    the unique algebra map being the fold.  A monoid L together with a map
    [h : X → U L] induces such an algebra — [None ↦ unit], [Some (a, m) ↦
    h a * m] — and the free-monoid extension of h IS the fold determined by
    it.  So the two universal properties of [list X] produce the same
    function, and "structural recursion over lists" and "the free monoid on
    X" are the same fact seen twice. *)

Definition monoid_ListF_alg {X : Coq} {L : MonCoq} (h : X → `1 L)
  : ListF X (`1 L) ~{Coq}~> `1 L :=
  fun o => match o with
           | None          => @mone L
           | Some (a, m)   => mmul (h a) m
           end.

Definition monoid_FAlg {X : Coq} {L : MonCoq} (h : X → `1 L) : FAlg (ListF X) :=
  existT (FAlgebra (ListF X)) (`1 L) (monoid_ListF_alg h).

Theorem free_ext_is_fold {X : Coq} {L : MonCoq} (h : X → `1 L) (l : list X) :
  free_ext h l = fold (monoid_ListF_alg h) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|now rewrite IH].
Qed.

(* The unique [ListF X]-algebra map out of [(list X, alg X)] into the induced
   algebra is the free-monoid extension. *)
Theorem free_ext_is_initial_algebra_map {X : Coq} {L : MonCoq}
        (h : X → `1 L) (l : list X) :
  falg_hom[@zero (FAlg (ListF X)) (list_initial X) (monoid_FAlg h)] l
    = free_ext h l.
Proof. symmetry; apply free_ext_is_fold. Qed.

(* Stated without the [FAlg] packaging: any map satisfying the algebra square
   is the extension. *)
Corollary free_ext_is_the_unique_algebra_map {X : Coq} {L : MonCoq}
        (h : X → `1 L) (g : list X → `1 L)
        (Hg : forall o, g (alg X o) = monoid_ListF_alg h (fmap[ListF X] g o))
        (l : list X) : g l = free_ext h l.
Proof.
  rewrite (hom_is_fold (monoid_ListF_alg h) g Hg l).
  symmetry; apply free_ext_is_fold.
Qed.

(** ** Recap: what discharges which catalog item

    - [maclane:II.7:cor2] and [awodey:1.7:construction-free-monoid] — the free
      monoid on X as an object of [Mon Coq] with its insertion of generators:
      [FreeMonoidStructure], [FreeMon], [insert] (with [free_mmul_is_app],
      [free_mone_is_nil] pinning the operations by computation).

    - [awodey:1.7:prop9] — the universal property, extension by the fold and
      its uniqueness: [free_ext], [free_ext_MonoidHom], [free_ext_unique],
      and the packaged [free_monoid_universal] (the ∃! statement),
      [free_monoid_universal_arrow], [free_monoid_AUniversalArrow].

    - [awodey:9.1:construction-free-monoid-adjunction] — the adjunction:
      [FreeMonoid], [free_monoid_adjunction], with the transposition formula
      [free_monoid_transposition] / [free_monoid_transposition_at] and its
      inverse [free_monoid_transposition_inv].

    - [awodey:7.5:example7] — the insertion of generators as a natural
      transformation: [insert_Transform], whose naturality square is
      [free_fmap_generators]; [insert_Transform_is_adjunction_unit] records
      that it agrees componentwise with the transformation the generic
      [Adjunction_to_Transform] produces.

    - [awodey:9:ex2] — the counit: [adjunction_counit_underlying_retraction]
      (generic, hypothesis-free) and [adjunction_counit_epic] (generic, needs
      a faithful right adjoint), instantiated as
      [free_monoid_counit_underlying_retraction], [free_monoid_counit_epic],
      with the concrete [free_monoid_counit_surjective] and the computation
      [free_monoid_counit_is_free_ext].  Split-epi-ness IN Mon is not claimed;
      see the discussion above that section.

    - [awodey:1.7:prop10] and the QA scope increment — uniqueness up to a
      unique isomorphism: the generic lemmas [universal_arrow_unique] and
      [auniversal_arrow_unique] were ADDED to Theory/Universal/Arrow.v, and
      are specialised here as [free_monoid_unique] and
      [free_monoid_unique_iso].

    - [awodey:2:ex4] — the A-Mon comma presentation: [AMon], [AMon_ob],
      [AMon_hom], with [free_monoid_initial] one way and
      [AMon_initial_universal_arrow] the other.

    - [7sketches:5.2.3:ex5.24] — words over a two-element set and the
      [ListMon] identification: [ListMon_hom_is_free_carrier],
      [ListMon_id_is_free_unit], [ListMon_compose_is_free_mul], plus the
      computing witnesses [word_ab] … [word_unit_right] and the folds
      [fold_into_xor_1] … [fold_into_xor_hom].

    Bridges (issue work item 4): [free_ext_is_fold],
    [free_ext_is_initial_algebra_map] and
    [free_ext_is_the_unique_algebra_map] relate the extension to
    Instance/Coq/Lists.v's [list_initial].

    NOT BUILT, deliberately.

    - The (ℕ, +)-as-free-monoid-on-one-generator consequence is owned by
      issue #802 and nothing here anticipates it; the only monoid used as a
      fold target is [XorMon].

    - The one-object-graph reading is recorded but not transferred: Mac Lane
      obtains the free monoid as the free category on a one-vertex graph, and
      Construction/Free/Quiver.v carries that theorem
      ([UniversalArrowQuiverCat], [FreeForgetfulAdjunction]) with its
      universal property stated in StrictCat under strict functor equality.
      Identifying [FreeMon X] with the hom-monoid of [FreeOnQuiver] at a
      one-vertex quiver needs the delooping dictionary at functor level
      (Construction/Deloop.v defers exactly that step, and its transport is
      issue #220); it is NOT proved here, and no file
      Construction/Free/Quiver/Loop.v exists to cite.  What IS proved is the
      free-monoid universal property directly, which is what the citing
      issues ask for. *)

