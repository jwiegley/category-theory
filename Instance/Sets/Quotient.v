Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(* The global obligation tactic ([cat_simpl], Lib/Tactics.v:225) introduces
   the obligations' binders under names of its own choosing, which makes the
   proof scripts below brittle; [idtac] hands each obligation over
   untouched, as Instance/Sets/Complete.v does. *)
#[local] Obligation Tactic := idtac.

(** * The quotient of a setoid by an equivalence relation *)

(* nLab:      https://ncatlab.org/nlab/show/quotient+set
   nLab:      https://ncatlab.org/nlab/show/setoid
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_class
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_set

   Mac Lane, "Categories for the Working Mathematician" 2nd ed., §III.1
   construction 4 (p. 57): for an equivalence relation E on a set S, the
   projection p : S -> S/E is universal among functions out of S that
   respect E.  Every h : S -> X with h x = h y whenever x E y factors
   through p by a unique u : S/E -> X.

   In a setoid library that construction is not a construction at all: a
   quotient IS another choice of `≈` on the same carrier.  The design is
   stated as such at Instance/Sets.v:66 ("a quotient is just another
   choice of `≈` on the same carrier") and at Theory/Category.v:93, and
   it is what Construction/Quotient.v does one dimension up (a quotient
   of a CATEGORY by a hom-congruence, identity on objects).  This file
   supplies the missing element-level operator: given a [SetoidObject] A
   and an equivalence relation R on its carrier, [SetsQuotient A R] is A
   with `≈` replaced by R, and [sets_quot_proj] is the identity function
   read as a setoid map.

   Because carrier and function are untouched, Mac Lane's universal
   property becomes almost tautologous -- and that is the content, not a
   defect.  The mediator IS the given function; its respectfulness for
   the coarser relation IS the hypothesis that it respects E; and the
   defining triangle holds pointwise by [reflexivity].  What has to be
   built is only the ENVIRONMENT in which "universal" can be stated: the
   functor X |-> {E-respecting maps A -> X}, which is covariant by
   postcomposition, and against which ⟨A/R, p⟩ is a universal element in
   the sense of Theory/Universal/Element.v (Mac Lane's §III.1
   definition 2). *)

(* Where this sits, and why the carrier does not move

   Text:  Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967
   Text:  Mac Lane, "Categories for the Working Mathematician", Springer
          1998, §III.1 (pp. 55-59) and §III.3 (pp. 64-68)
   Text:  Fong and Spivak, "Seven Sketches in Compositionality", CUP 2019,
          §1.2.1 (printed p. 10)
   Paper: Barthe, Capretta, Pons, "Setoids in type theory", JFP 13(2) 2003
   Thesis: Hofmann, "Extensional Concepts in Intensional Type Theory",
           LFCS report ECS-LFCS-95-327, University of Edinburgh, 1995

   Two presentations of a quotient have been current since Bishop.  The
   first, which the Seven Sketches definition (§1.2.1) gives, takes the
   quotient to BE the set of parts of the induced partition: an element
   of A/R is a subset of A.  The second, which Bishop's own development
   uses and which Hofmann's models of intensional type theory formalise,
   never separates a carrier from its equality: A/R is A again, under a
   coarser equality.  The two agree classically.  They do not agree
   constructively without care, and Instance/Sets/Quotient/Partition.v is
   where that care is spent -- it builds the class presentation, proves
   the comparison with this file's, and measures exactly what the
   comparison costs.

   This file takes the second presentation because the library does.  The
   choice buys three things.  Function extensionality is not needed, since
   no new function space is introduced.  No choice principle is needed,
   since no representative is ever selected -- Mac Lane's classical proof
   picks a representative of each class and checks independence, and here
   there is nothing to pick.  And the whole construction stays at the
   universe of the carrier, whereas a set of subsets does not
   (Instance/Sets/Powerset.v establishes exactly that, and the sequel file
   pins the consequence).

   The one thing the choice costs is that "quotient" no longer has a
   canonical meaning independent of the relation's proof content.  R is
   [crelation]-valued, so R x y is a TYPE, and two different derivations
   of R x y are two different elements.  That does not affect anything in
   this file -- `≈` in a [SetoidObject] is Type-valued for the same reason
   and the hom-setoid of [Sets] compares maps, not proofs -- but it does
   affect the class presentation, and again the sequel file is where it
   is measured. *)

(* WHAT IS DELIVERED

   * [SetoidCoarser] and [SetoidRespectsRel], the two hypotheses the
     literature states, and [coarser_iff_respects] proving them EQUIVALENT
     for an equivalence relation.  This settles a question the source
     issue raises twice in different words: Mac Lane's §III.1 asks for a
     "setoid-respecting" E and Seven Sketches §1.2.1 for an R "coarser
     than `≈`", and these are the same hypothesis, not two.  Each
     direction consumes exactly one law of R -- transitivity forward,
     reflexivity back -- and both are recorded.

   * [SetsQuotient A R HR], the quotient setoid, and [sets_quot_proj], the
     projection.  Note WHICH hypothesis each needs: the OBJECT needs only
     that R is an equivalence, and [SetoidCoarser] enters exactly at the
     PROJECTION, where it is what makes the identity function respectful.

   * The functor [RespFunctor A R : Sets ⟶ Sets] sending X to the setoid
     of R-respecting maps A -> X, covariant by postcomposition.  It needs
     NOTHING of R -- neither that R is an equivalence nor that it is
     coarser than `≈` -- which is why it is defined before either.

   * [sets_quot_universal_element], Mac Lane §III.1 construction 4 as an
     [AUniversalElement] over #303's class, used DIRECTLY.  With the
     mediator calculus [sets_quot_med] / [_commutes] / [_unique], and
     [eq_refl] checks that the class's element IS the projection and the
     class's mediator IS [sets_quot_med].

   * A representation, by the YONEDA-FREE route.  [ue_representation] and
     [AUniversalElement_of_repr] (Theory/Universal/Element.v) build the
     natural isomorphism [Hom (A/R),─] ≅ RespFunctor without mentioning
     [Yoneda_Lemma]; [sets_quot_representation] and
     [sets_quot_Representable] are the results.  The Yoneda route is NOT
     available here and that is not a matter of taste: [Yoneda_Lemma] is
     stated over [C : Category@{u0 u0 u0}] -- object, hom and proof
     universes identified -- while [Sets@{o so} : Category@{so o o}] has
     its objects strictly above its homs.  Test/ProbeSetsQuotient.v pins
     the refusal against a positive control.

   * Non-vacuity, by proof rather than by assertion.  [nat_parity] is a
     concrete coarsening of the naturals under `=` in which the quotient
     identifies 0 with 2 and provably does not identify 0 with 1.  The two
     degenerate coarsenings are named and separated from it: the FINEST,
     R := `≈`, returns the object it started from ([sets_quot_finest_eq],
     by [eq_refl] on the whole record), and the COARSEST, R := the total
     relation, collapses everything ([sets_quot_total_collapses]) -- and
     [nat_parity] is proved to be neither ([nat_parity_not_finest],
     [nat_parity_not_coarsest]).

   WHAT IS NOT DELIVERED

   * NO CLASS PRESENTATION.  The quotient as the set of parts of the
     induced partition is Instance/Sets/Quotient/Partition.v, together
     with the comparison and the universe measurement.  Nothing here
     mentions a subset.

   * NO COEQUALIZERS.  [Sets_HasCoequalizers] and the identification of
     A/R with the coequalizer of the two projections of R are
     Instance/Sets/Coequalizer.v, which is this file's only in-tree
     consumer.

   * NO [Cocomplete Sets].  This file supplies one colimit shape's object,
     not the general construction; Instance/Sets/Complete.v:106 records
     that the general one is not attempted, and that note stands.

   * NO FUNCTORIALITY IN THE RELATION.  A refinement R ⊆ R' induces a map
     A/R -> A/R', and that map is not built; nor is any comparison with
     Construction/Quotient.v's category-level quotient, which is a
     different construction on a different kind of object.

   STATUS: axiom-free.  45 named constants plus 6 [Program] obligations
   ([RespMap_Setoid_obligation_1], [RespFunctor_obligation_1] through
   [_4], [sets_quot_universal_element_obligation_1]), each measured
   separately, all reporting "Closed under the global context"; the
   Makefile's [print-assumptions] target audits thirteen of them. *)

(** ** The two forms of the hypothesis *)

Section Hypotheses.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).

(* Seven Sketches' form: R is COARSER than the carrier's own equality,
   i.e. `≈` is contained in R. *)
Definition SetoidCoarser : Type := ∀ x y : carrier A, x ≈ y → R x y.

(* Mac Lane's form: R RESPECTS the carrier's equality, i.e. R may be
   transported along `≈` in either argument.  Stated one-directionally;
   symmetry of `≈` gives the other direction. *)
Definition SetoidRespectsRel : Type :=
  ∀ x x' y y' : carrier A, x ≈ x' → y ≈ y' → R x y → R x' y'.

(* Forward: coarseness gives respect, and the law of R it consumes is
   TRANSITIVITY. *)
Lemma coarser_respects (HR : Transitive R) : SetoidCoarser → SetoidRespectsRel.
Proof.
  intros Hc x x' y y' Hx Hy Hxy.
  transitivity y.
  - transitivity x; [ apply Hc; now symmetry | exact Hxy ].
  - now apply Hc.
Qed.

(* Back: respect gives coarseness, and the law of R it consumes is
   REFLEXIVITY.  Given x ≈ y, transport R x x along `≈` in the second
   argument. *)
Lemma respects_coarser (HR : Reflexive R) : SetoidRespectsRel → SetoidCoarser.
Proof.
  intros Hr x y Hxy.
  exact (Hr x x x y (reflexivity x) Hxy (HR x)).
Qed.

(* ... hence for an equivalence relation the two hypotheses are one.  The
   source issue asks for a quotient by a "setoid-respecting" relation in
   its main body and for one by a relation "coarser than `≈`" in a
   trailing block harvested from a different book; this says that those
   two requests are the same request. *)
Theorem coarser_iff_respects (HR : Equivalence R) :
  SetoidCoarser ↔ SetoidRespectsRel.
Proof.
  split.
  - apply coarser_respects; apply HR.
  - apply respects_coarser; apply HR.
Qed.

End Hypotheses.

Arguments SetoidCoarser {A} R.
Arguments SetoidRespectsRel {A} R.

(** ** The quotient object and its projection *)

(* The quotient setoid: SAME CARRIER, coarser `≈`.  Note that
   [SetoidCoarser] does not appear -- an equivalence relation on the
   carrier is already enough to name a setoid.  It is the projection that
   needs the relation to be coarser. *)
Definition SetsQuotient (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) : SetoidObject :=
  {| carrier := carrier A ; is_setoid := {| equiv := R ; setoid_equiv := HR |} |}.

(* The carrier is untouched, by conversion -- the [eq_refl] exception to
   the `≈` discipline, and the point of the construction. *)
Example sets_quot_carrier (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) : carrier (SetsQuotient A R HR) = carrier A.
Proof. reflexivity. Qed.

(* The projection is the identity function.  Its respectfulness clause,
   [Proper (equiv ==> equiv) (fun a => a)], is CONVERTIBLE with
   [SetoidCoarser R] and has no other content -- but writing
   [proper_morphism := HC] in the record literal is rejected, the
   elaborator not unfolding [SetoidCoarser] during unification, so the
   field is supplied by the one-step script below.  The same shape
   recurs at [sets_quot_med]. *)
Definition sets_quot_proj (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (HC : SetoidCoarser R) :
  A ~{Sets}~> SetsQuotient A R HR.
Proof.
  unshelve refine {| morphism := fun a : carrier A => a |}.
  intros x y Hxy; exact (HC x y Hxy).
Defined.

(* ... and its action is the identity, by conversion. *)
Example sets_quot_proj_at (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (HC : SetoidCoarser R) (a : carrier A) :
  sets_quot_proj A R HR HC a = a.
Proof. reflexivity. Qed.

(* Two elements are identified in the quotient exactly when R relates
   them -- again by conversion, so the quotient's `≈` is readable. *)
Example sets_quot_equiv (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (x y : carrier A) :
  @equiv _ (SetsQuotient A R HR) x y = R x y.
Proof. reflexivity. Qed.

(** ** The functor of R-respecting maps *)

Section RespFunctor.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).

(* h respects R when it cannot tell R-related elements apart.  This is
   Mac Lane's condition on the functions that descend. *)
Definition SetsRespects (X : SetoidObject) (h : A ~{Sets}~> X) : Type :=
  ∀ x y : carrier A, R x y → h x ≈ h y.

Definition RespMap (X : SetoidObject) : Type :=
  { h : A ~{Sets}~> X & SetsRespects X h }.

(* Two respecting maps are compared by their underlying maps; the
   respectfulness witness carries no equational weight, exactly as in
   Instance/Grp/Quotient.v's [Kills_Setoid]. *)
Program Definition RespMap_Setoid (X : SetoidObject) : Setoid (RespMap X) :=
  {| equiv := fun p q => `1 p ≈ `1 q |}.
Next Obligation.
  intros.
  constructor.
  - intros p x; reflexivity.
  - intros p q Hpq x; now symmetry.
  - intros p q r Hpq Hqr x; now transitivity (`1 q x).
Qed.

(* Postcomposition preserves respectfulness. *)
Lemma RespMap_post {X Y : SetoidObject} (k : X ~{Sets}~> Y) (p : RespMap X) :
  SetsRespects Y (k ∘ `1 p).
Proof.
  intros x y Hxy; simpl; unfold Basics.compose.
  apply proper_morphism.
  exact (`2 p x y Hxy).
Qed.

(* The functor.  It is COVARIANT -- postcomposition, not precomposition --
   which is what makes ⟨A/R, p⟩ a universal element in Mac Lane's sense
   rather than a representing object of a presheaf.  Nothing in this
   definition uses any law of R. *)
Program Definition RespFunctor : Sets ⟶ Sets := {|
  fobj := fun X => {| carrier := RespMap X ; is_setoid := RespMap_Setoid X |};
  fmap := fun X Y k =>
    {| morphism := fun p : RespMap X =>
         existT (SetsRespects Y) (k ∘ `1 p) (RespMap_post k p) |}
|}.
Next Obligation. intros X Y k p q Hpq a; simpl; now rewrite (Hpq a). Qed.
Next Obligation. intros X Y k k' Hk p a; simpl; exact (Hk _). Qed.
Next Obligation. intros X p a; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z k k' p a; simpl; reflexivity. Qed.

End RespFunctor.

Arguments SetsRespects {A} R X h.
Arguments RespMap {A} R X.
Arguments RespFunctor {A} R.

(** ** The mediator *)

Section Mediator.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).

(* Descent.  In the group case (Instance/Grp/Quotient.v's
   [kills_descends]) this is a computation; here the mediator's
   respectfulness clause is CONVERTIBLE with the given map's
   [SetsRespects] witness, because the quotient's `≈` IS R and the
   mediator's underlying function IS the given one -- so the script is
   again one step, for the elaboration reason noted at
   [sets_quot_proj]. *)
Definition sets_quot_med {X : SetoidObject} (p : RespMap R X) :
  SetsQuotient A R HR ~{Sets}~> X.
Proof.
  unshelve refine
    {| morphism := fun a : carrier (SetsQuotient A R HR) => `1 p a |}.
  intros x y Hxy; exact (`2 p x y Hxy).
Defined.

(* The defining triangle, pointwise by [reflexivity]: the projection is
   the identity function, so there is nothing to compute. *)
Lemma sets_quot_med_commutes (HC : SetoidCoarser R) {X : SetoidObject}
  (p : RespMap R X) : sets_quot_med p ∘ sets_quot_proj A R HR HC ≈ `1 p.
Proof. intro a; simpl; reflexivity. Qed.

Lemma sets_quot_med_unique (HC : SetoidCoarser R) {X : SetoidObject}
  (p : RespMap R X) (v : SetsQuotient A R HR ~{Sets}~> X)
  (Hv : v ∘ sets_quot_proj A R HR HC ≈ `1 p) : sets_quot_med p ≈ v.
Proof. intro a; simpl; symmetry; exact (Hv a). Qed.

End Mediator.

Arguments sets_quot_med {A} R HR {X} p.

(** ** Mac Lane §III.1 construction 4: ⟨A/R, p⟩ is a universal element *)

Section Universal.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).
Context (HC : SetoidCoarser R).

(* The projection, packaged as an element of (RespFunctor R)(A/R).  Its
   respectfulness witness is the IDENTITY implication -- "R x y implies
   R x y" -- since the target's `≈` is R.

   The sigma's predicate is spelled out rather than left to inference,
   and that is a PORTABILITY fix, not decoration: on Coq 8.19/8.20 the
   elaborator resolves the [_] against the TYPE of the second component,
   here [∀ x y, R x y → R x y], instead of against the expected
   [RespMap], and rejects the definition.  Rocq 9.1 accepts either form,
   so the break is invisible on the default toolchain; it is the same
   trap Instance/Rng/Frac.v records for its fraction constructor, and
   every [existT] in these four files is written this way for it. *)
Definition sets_quot_elem : RespMap R (SetsQuotient A R HR) :=
  existT (SetsRespects R (SetsQuotient A R HR))
    (sets_quot_proj A R HR HC) (fun x y (h : R x y) => h).

(* Mac Lane's construction 4.  Every R-respecting map out of A is
   (RespFunctor R u) applied to the projection, for a UNIQUE
   u : A/R -> X.  #303's [AUniversalElement] is used DIRECTLY, so neither
   of Theory/Universal/Element.v's routes to [Representable] is touched
   and no universe restriction is inherited at this point. *)
Program Definition sets_quot_universal_element :
  AUniversalElement (RespFunctor R) (SetsQuotient A R HR) := {|
  aue_elem := sets_quot_elem
|}.
Next Obligation.
  intros X x.
  unshelve refine {| unique_obj := sets_quot_med R HR x |}.
  - exact (sets_quot_med_commutes R HR HC x).
  - intros v Hv; simpl in *.
    exact (sets_quot_med_unique R HR HC x v Hv).
Defined.

(* The class's element IS the projection, and the class's mediator IS
   [sets_quot_med] -- both by convertibility, the [eq_refl] exception,
   checking that the packaging rebuilt nothing. *)
Example sets_quot_universal_elem_is_proj :
  `1 (@aue_elem _ (RespFunctor R) (SetsQuotient A R HR)
        sets_quot_universal_element)
    = sets_quot_proj A R HR HC.
Proof. reflexivity. Qed.

Example sets_quot_universal_med_is_med {X : SetoidObject} (x : RespMap R X) :
  unique_obj (@aue_universal _ (RespFunctor R) (SetsQuotient A R HR)
                sets_quot_universal_element X x)
    = sets_quot_med R HR x.
Proof. reflexivity. Qed.

(** ** The representation, by the Yoneda-free route *)

(* [ue_representation] (Theory/Universal/Element.v) builds
   [Hom (A/R),─] ≅ RespFunctor R directly, mentioning no Yoneda lemma.
   The Yoneda-based [universal_element_yoneda] is NOT usable at [Sets]:
   its donor identifies object, hom and proof universes, and
   [Sets@{o so} : Category@{so o o}] does not.  Test/ProbeSetsQuotient.v
   pins that refusal, with a positive control at a category whose three
   universes can be identified. *)
(* [@Build_Representable] rather than the `{| ... |}` literal: for a Class,
   the literal sends the elaborator looking for an instance of the head
   before the ambient category is fixed -- the same trap
   Theory/Universal/Element.v records at [AUniversalElement_of_hom]. *)
Definition sets_quot_Representable : Representable (RespFunctor R) :=
  @Build_Representable Sets (RespFunctor R) (SetsQuotient A R HR)
    (ue_representation (RespFunctor R) (SetsQuotient A R HR)
       sets_quot_universal_element).

(* The natural isomorphism itself, named.  Its type is
   [@Isomorphism (Fun Sets Sets) (fobj[Curried_Hom Sets] (A/R))
      (RespFunctor R)], i.e. [Hom (A/R),─] ≅ RespFunctor R in [Sets, Sets];
   it is left to be read off [represented] rather than ascribed, because
   spelling [@Curried_Hom _ (A/R)] in a type leaves the ambient category an
   unresolved evar (the object must be one of [C^op], and nothing in the
   annotation fixes [C]).  It is [ue_representation]'s value on the nose,
   the [represented] projection returning it by conversion. *)
Definition sets_quot_representation :=
  @represented _ (RespFunctor R) sets_quot_Representable.

(* The representing object is the quotient on the nose. *)
Example sets_quot_repr_obj :
  @repr_obj _ (RespFunctor R) sets_quot_Representable = SetsQuotient A R HR.
Proof. reflexivity. Qed.

End Universal.

Arguments sets_quot_elem {A} R HR HC.
Arguments sets_quot_universal_element {A} R HR HC.

(** ** The two degenerate coarsenings, named *)

(* THE FINEST: R := the carrier's own `≈`.  The quotient is the object it
   started from, and it is so ON THE NOSE -- Leibniz equality of the whole
   [SetoidObject] record, by [eq_refl].  Primitive projections give record
   eta, so [is_setoid A] and the rebuilt [{| equiv := ...; setoid_equiv :=
   ... |}] are the same term. *)
Example sets_quot_finest_eq (A : SetoidObject) :
  SetsQuotient A (@equiv _ A) (@setoid_equiv _ A) = A.
Proof. reflexivity. Qed.

Definition sets_quot_finest_coarser (A : SetoidObject) :
  SetoidCoarser (@equiv _ A) := fun _ _ h => h.

(* THE COARSEST: R := the total relation, which identifies everything. *)
Definition TotalRelT (A : SetoidObject) : crelation (carrier A) :=
  fun _ _ => poly_unit.

Lemma TotalRelT_Equivalence (A : SetoidObject) : Equivalence (TotalRelT A).
Proof.
  constructor.
  - intro x; exact ttt.
  - intros x y _; exact ttt.
  - intros x y z _ _; exact ttt.
Qed.

Definition TotalRelT_coarser (A : SetoidObject) : SetoidCoarser (TotalRelT A) :=
  fun _ _ _ => ttt.

Lemma sets_quot_total_collapses (A : SetoidObject) (x y : carrier A) :
  @equiv _ (SetsQuotient A (TotalRelT A) (TotalRelT_Equivalence A)) x y.
Proof. exact ttt. Qed.

(** ** Non-vacuity: a quotient that neither keeps everything apart nor
       collapses everything *)

(* Parity on the naturals, as a coarsening of the DISCRETE setoid on
   [nat] -- so `≈` there is Leibniz equality and the coarsening is
   genuine.  [Nat.even] is a boolean, so the relation is a decidable
   equation of booleans; that is what lets the negative results below be
   proved rather than merely expected. *)
Definition NatDiscrete : SetoidObject :=
  {| carrier := nat ; is_setoid := eq_Setoid nat |}.

Definition nat_parity : crelation (carrier NatDiscrete) :=
  fun m n => Nat.even m = Nat.even n.

Lemma nat_parity_Equivalence : Equivalence nat_parity.
Proof.
  constructor.
  - intro m; reflexivity.
  - intros m n H; now symmetry.
  - intros m n k H1 H2; now transitivity (Nat.even n).
Qed.

Definition nat_parity_coarser : SetoidCoarser nat_parity :=
  fun m n (H : m = n) => f_equal Nat.even H.

Definition NatParity : SetoidObject :=
  SetsQuotient NatDiscrete nat_parity nat_parity_Equivalence.

(* The quotient IDENTIFIES: 0 and 2 are equal in it, by computation. *)
Example nat_parity_merges : @equiv _ NatParity 0%nat 2%nat.
Proof. reflexivity. Qed.

(* The quotient SEPARATES: 0 and 1 are not.  This is where a decidable
   invariant earns its keep -- the relation unfolds to [true = false]. *)
Lemma nat_parity_separates : @equiv _ NatParity 0%nat 1%nat → False.
Proof. intro H; discriminate H. Qed.

(* ... so the parity quotient is neither degenerate case.  It is not the
   finest, since the finest keeps 0 and 2 apart; and it is not the
   coarsest, since the coarsest identifies 0 and 1.  Both are stated as
   refutations of the RELATIONS, which is the level at which the two
   degeneracies were defined. *)
Lemma nat_parity_not_finest :
  (∀ m n : carrier NatDiscrete, nat_parity m n → @equiv _ NatDiscrete m n) → False.
Proof.
  intro H.
  pose proof (H 0%nat 2%nat eq_refl) as E; discriminate E.
Qed.

Lemma nat_parity_not_coarsest :
  (∀ m n : carrier NatDiscrete, TotalRelT NatDiscrete m n → nat_parity m n) → False.
Proof. intro H; exact (nat_parity_separates (H 0%nat 1%nat ttt)). Qed.

(* And the universal property is inhabited at it: the parity map itself
   is a respecting map, so the mediator out of the quotient exists and
   computes on closed input. *)
Definition BoolSet : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

(* [BoolSet] and [NatDiscrete] are discrete, so [proper_morphism] here is
   respect for Leibniz equality and instance resolution discharges it;
   both carriers are concrete ([nat], [bool]), so no universe
   polymorphism is at stake in leaving it to resolution. *)
Definition nat_even_map : NatDiscrete ~{Sets}~> BoolSet.
Proof.
  unshelve refine {| morphism := Nat.even |}.
Defined.

Definition nat_even_resp : RespMap nat_parity BoolSet :=
  existT (SetsRespects nat_parity BoolSet)
    nat_even_map (fun m n (H : nat_parity m n) => H).

(* The descended map on the quotient, evaluated. *)
Example nat_parity_med_at_4 :
  sets_quot_med nat_parity nat_parity_Equivalence nat_even_resp 4%nat = true.
Proof. reflexivity. Qed.

Example nat_parity_med_at_7 :
  sets_quot_med nat_parity nat_parity_Equivalence nat_even_resp 7%nat = false.
Proof. reflexivity. Qed.
