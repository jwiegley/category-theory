Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(** * The comma diagram over the arrow category, and its universal property *)

(* Reference: Saunders Mac Lane, "Categories for the Working Mathematician",
              2nd ed., §II.6, pp. 47-48: the projections and the diagram of
              displays (5) and (6) [maclane:II.6:construction1], their
              arrow-level definitions [maclane:II.6:ex3], and the universal
              property [maclane:II.6:ex5].  Every statement summary below is
              the catalog's paraphrase (doc/plan/books/maclane/inventory/
              II.json), not the book's own wording.
   nLab:      https://ncatlab.org/nlab/show/comma+category
   nLab:      https://ncatlab.org/nlab/show/arrow+category
   nLab:      https://ncatlab.org/nlab/show/comma+object
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   In the catalog's paraphrase of [maclane:II.6:construction1], the comma
   category carries projection functors to the two domains -- on objects
   <e, d, f> giving e and d -- together with a functor to C^2 giving the
   arrow f itself, all fitting into a commutative diagram over the row

       E --T--> C <--∂0-- C^2 --∂1--> C <--S-- D

   where ∂0 and ∂1, induced by the two functors 1 ⟶ 2, send each arrow of C
   to its domain and to its codomain.  Exercise 3 asks for the three functors
   on arrows; Exercise 5 asks that any category X with functors making the
   same diagram commute factor uniquely through the comma category, which is
   what exhibits it as a "pullback"-style limit.

   ** Dictionary

   Mac Lane writes (T ↓ S) for T : E ⟶ C and S : D ⟶ C; this tree writes
   (S ↓ T) for S : A ⟶ C and T : B ⟶ C (Construction/Comma.v).  The letters
   are interchanged and nothing else differs:

     Mac Lane      here                            defined in
     ----------------------------------------------------------------------
     T : E ⟶ C     S : A ⟶ C
     S : D ⟶ C     T : B ⟶ C
     P             [comma_proj1]                   Construction/Comma.v:196
     Q             [comma_proj2]                   Construction/Comma.v:204
     R             [Comma_to_Arrow]                this file
     C^2           [Arrow C] = (Id[C] ↓ Id[C])     Construction/Arrow.v:131
     C^{d0}        [Arrow_dom]                     this file
     C^{d1}        [Arrow_cod]                     this file

   [Arrow_dom] and [Arrow_cod] are not wrappers: they are [comma_proj1] and
   [comma_proj2] instantiated at S = T = Id[C], and the two [Example]s below
   pin that by [eq_refl].  Exercise 3 is answered the same way: on a
   commuting square, each of P, Q, ∂0 and ∂1 returns the relevant leg and R
   returns the pair of S- and T-images of the two legs, all definitionally,
   so the arrow-level definitions are [eq_refl] readings rather than proofs
   ([comma_proj1_fmap], [comma_proj2_fmap], [Arrow_dom_fmap],
   [Arrow_cod_fmap], [Comma_to_Arrow_dom_leg], [Comma_to_Arrow_cod_leg]).

   ** What the diagram equations cost

   Both squares of display (5) commute at STRICT strength, at
   [Functor_StrictEq_Setoid] -- equal object maps with [fmap] agreeing after
   transport -- and with the object component [fun _ => eq_refl], i.e. the
   two composites have literally the same object map:
   [comma_diagram_dom] and [comma_diagram_cod].  This is the strongest form
   available: Leibniz equality of the functor RECORDS is not provable, the
   [fmap_respects]/[fmap_id]/[fmap_comp] fields being proof terms built
   differently on the two sides.  The [≈[Cat]] readings
   [comma_diagram_dom_Cat]/[comma_diagram_cod_Cat] are strictly weaker
   corollaries obtained through [strict_equiv_implies_fun_equiv]
   (Instance/StrictCat/ToCat.v); recall that [≈[Cat]] identifies functors
   only up to natural isomorphism (Instance/Cat.v).

   ** Exercise 5, and where proof relevance bites

   The hypotheses on a competitor (X, P', Q', R') are taken STRICT, as
   Mac Lane's diagram is: the two composites agree at
   [Functor_StrictEq_Setoid].  The mediator [comma_mediator] then sends x to
   the comma object (P' x, Q' x) whose mediating arrow is that of R' x
   transported along the two object equalities the hypotheses supply, and the
   three factorizations hold at strict strength:
   [comma_mediator_proj1] and [comma_mediator_proj2] with object component
   [eq_refl], and [comma_mediator_arrow] with object component built from the
   hypotheses' own object equalities.  Its morphism half spends exactly the
   hypotheses' arrow components and nothing else.  So EXISTENCE is on the
   nose in Mac Lane's sense.

   UNIQUENESS is where a proof-relevant setting differs from the book's, and
   the difference is not an artifact of the formalization.  The three
   equations are INDEPENDENT data.  From [Comma_to_Arrow ◯ L' ≈ R'] one
   recovers only [S (fst ``(L' x)) = fst ``(R' x)], an equation in C; since S
   need not be injective on objects, no equation in A follows, so
   [comma_proj1 ◯ L' ≈ P'] is genuinely additional information, and
   symmetrically for B.  A competitor therefore arrives carrying two
   INDEPENDENT proofs of one and the same object equation
   [S (fst ``(L' x)) = S (P' x)] -- one obtained by [f_equal S] from the
   first equation, one by composing the third with the hypothesis on R'.
   Identifying them is uniqueness of identity proofs on the objects of C, and
   identifying the morphisms they induce is that same principle again.  In
   Mac Lane's set-based reading the question does not arise, equality of
   objects being proof-irrelevant there.

   Rather than assume UIP, [MediatesDiagram] states the third equation
   RELATIVE to the first two: the mediating arrow of L x, transported to
   S (P' x) ~> T (Q' x) along the object equalities the first two equations
   supply, agrees up to [≈] with the one R' supplies.  That is the [≈]-level
   content of "R' = R ◯ L'" with only one family of object proofs in play; it
   is satisfied on the nose by the mediator built here
   ([comma_mediator_mediates], whose third clause is [reflexivity]); and from
   it uniqueness follows at [≈[Cat]] ([comma_mediator_unique]), the natural
   isomorphism having the object-equality casts as its components.  The two
   halves are packaged as [comma_diagram_ump].

   Three things are therefore NOT delivered, and are named rather than left
   to inference.  First, strict uniqueness -- "L' x = L x as objects of
   S ↓ T" -- which beyond the proof reconciliation above would demand Leibniz
   equality of two mediating MORPHISMS, since a comma object carries its
   morphism as data and a setoid library supplies only [≈] between morphisms.
   Second, the PSEUDO version, in which the hypotheses commute only up to
   natural isomorphism: that is the comma OBJECT in the 2-categorical sense,
   which Construction/Comma.v:104-108 already records as documentation-level
   only -- comma objects are PIE-limits, constructible from pullbacks and the
   power C^2 (nLab, "comma object") -- and Mac Lane's Exercise 5 is the
   strict statement, which is what is proven here.  Third, and a consequence
   of the first: the uniqueness clause quantifies over [MediatesDiagram]
   competitors, a class INCOMPARABLE with Mac Lane's literal one -- weaker on
   the mediating morphism ([≈] where an equality of Arrow-objects would
   demand Leibniz) and stated relative to the competitor's own k1/k2 proof
   families -- so his uniqueness statement is rendered, not subsumed.

   [comma_diagram_self] and [comma_diagram_self_via_ump] close the loop and
   keep BOTH halves of the universal property from being vacuous: the comma
   category's own diagram is a competitor -- its hypotheses are literally
   [comma_diagram_dom] and [comma_diagram_cod] -- the mediator produced there
   is [≈[Cat]] the identity (and strictly so, [comma_diagram_self_strict]),
   and the identity itself satisfies [MediatesDiagram] by three
   reflexivities ([comma_id_mediates]), so the UNIQUENESS theorem is
   exercised at the one competitor whose answer is forced.

   ** Reuse, and two small kits

   [comma_proj_nat] (Construction/Comma.v:214) is Mac Lane's R in
   transformation form, and this file relates itself to it rather than
   duplicating it.  It cannot simply be plugged in: its component is a
   [Program] obligation that MATCHES on the comma object, and neither [sigT]
   nor [prod] carries definitional eta in this development, so
   [comma_proj_nat x] is not convertible with [`2 x].  [Comma_to_Arrow] takes
   [`2 x] directly -- which is what keeps the diagram equations definitional
   -- and the agreement is recorded as [Comma_to_Arrow_is_proj_nat], a
   Leibniz equality proved by one [destruct].  The commuting square that
   makes [fmap[Comma_to_Arrow]] well typed IS the naturality of that
   transformation, and [Comma_to_Arrow_naturality] says so in
   [comma_proj_nat]'s own vocabulary, by [naturality_sym].

   [Functor_StrictEq_Setoid] spells its morphism condition with raw
   [transport]/[transport_r]; every proof below works instead with the
   [hom_cast] kit of Construction/Quotient.v, over the one-line bridge
   [hom_cast_of_transports]/[transports_of_hom_cast] and the two derived
   helpers [strict_fmap_cast] and [Build_strict_eq].  This is the same trade
   Theory/Skeleton.v makes with [transport_square] and
   [strict_equiv_of_id_cast_nat]; those are phrased with [id_cast] rather
   than [hom_cast] and are not reused here only because that file's
   dependency cone is far heavier than this one's.

   Every principal is universe-polymorphic with nothing pinned to [Set].  The
   universal property does identify the hom/proof universes of A, B, C and X,
   which is forced by the statement: the comma category's own homs live at
   C's hom universe, and the statement composes functors in both directions
   across it (the equalities first appear at [comma_mediator]; the comma
   construction itself carries only inequalities).

   ** Neighbours

   Construction/Comma/Special.v settles Mac Lane's §II.6 remark on the
   specializations of the construction (slice, coslice, arrow category, and
   the discrete category on a hom-set), and its header carries the closed
   list; Construction/Comma/Natural/Transformation.v is Exercise 4, Huq's
   correspondence between natural transformations and functors sectioning
   both projections.  Construction/Arrow/Functor.v is the neighbouring
   Exercise II.4.7 -- functors INTO the arrow category are natural
   transformations -- and Theory/Shapes.v's [Two_Fun_Arrow] is the
   [[_2, C] ≅[Cat] Arrow C] comparison; neither is needed below. *)

(** ** Transport and [hom_cast]: the two spellings of strict functor equality *)

Section StrictCastKit.

Context {D : Category}.

Lemma hom_cast_of_transports {a a' b b' : D}
      (ea : a = a') (eb : b = b') (f : a ~{D}~> b) (g : a' ~{D}~> b') :
  transport (fun z => a ~{D}~> z) eb f
    ≈ transport_r (fun z => z ~{D}~> b') ea g
  → hom_cast ea eb f ≈ g.
Proof. destruct ea, eb; simpl; unfold transport_r; simpl; auto. Qed.

Lemma transports_of_hom_cast {a a' b b' : D}
      (ea : a = a') (eb : b = b') (f : a ~{D}~> b) (g : a' ~{D}~> b') :
  hom_cast ea eb f ≈ g
  → transport (fun z => a ~{D}~> z) eb f
      ≈ transport_r (fun z => z ~{D}~> b') ea g.
Proof. destruct ea, eb; simpl; unfold transport_r; simpl; auto. Qed.

End StrictCastKit.

Definition strict_fmap_cast {C D : Category} {F G : C ⟶ D}
           (H : @equiv _ (@Functor_StrictEq_Setoid C D) F G)
           {x y : C} (f : x ~> y) :
  hom_cast (`1 H x) (`1 H y) (fmap[F] f) ≈ fmap[G] f :=
  hom_cast_of_transports _ _ _ _ (`2 H x y f).

Definition Build_strict_eq {C D : Category} {F G : C ⟶ D}
           (eo : ∀ x : C, F x = G x)
           (em : ∀ (x y : C) (f : x ~> y),
                   hom_cast (eo x) (eo y) (fmap[F] f) ≈ fmap[G] f) :
  @equiv _ (@Functor_StrictEq_Setoid C D) F G :=
  (eo; fun x y f => transports_of_hom_cast _ _ _ _ (em x y f)).

(** ** The domain and codomain functors of the arrow category *)

Definition Arrow_dom {C : Category} : @Arrow C ⟶ C := @comma_proj1 C C C Id[C] Id[C].
Definition Arrow_cod {C : Category} : @Arrow C ⟶ C := @comma_proj2 C C C Id[C] Id[C].

Example Arrow_dom_is_comma_proj1 {C : Category} :
  @Arrow_dom C = @comma_proj1 C C C Id[C] Id[C] := eq_refl.

Example Arrow_cod_is_comma_proj2 {C : Category} :
  @Arrow_cod C = @comma_proj2 C C C Id[C] Id[C] := eq_refl.

Example Arrow_dom_fobj {C : Category} (x : @Arrow C) :
  Arrow_dom x = fst ``x := eq_refl.

Example Arrow_cod_fobj {C : Category} (x : @Arrow C) :
  Arrow_cod x = snd ``x := eq_refl.

Example Arrow_dom_fmap {C : Category} (x y : @Arrow C) (f : x ~> y) :
  fmap[Arrow_dom] f = fst ``f := eq_refl.

Example Arrow_cod_fmap {C : Category} (x y : @Arrow C) (f : x ~> y) :
  fmap[Arrow_cod] f = snd ``f := eq_refl.

Lemma Arrow_square {C : Category} (x y : @Arrow C) (f : x ~> y) :
  `2 y ∘ fmap[Arrow_dom] f ≈ fmap[Arrow_cod] f ∘ `2 x.
Proof. exact (`2 f). Qed.

(** ** Mac Lane's functor [R] : the comma category over the arrow category *)

Section CommaToArrow.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition Comma_to_Arrow : (S ↓ T) ⟶ @Arrow C := {|
  fobj := fun x => ((S (fst ``x), T (snd ``x)); `2 x);
  fmap := fun _ _ f => ((fmap[S] (fst ``f), fmap[T] (snd ``f)); _)
|}.
Next Obligation. intros x y f; exact (`2 f). Defined.
Next Obligation.
  intros x y f g [e0 e1]; split; simpl.
  - now rewrite e0.
  - now rewrite e1.
Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

Example Comma_to_Arrow_fobj (x : S ↓ T) :
  Comma_to_Arrow x = ((S (fst ``x), T (snd ``x)); `2 x) := eq_refl.

Example Comma_to_Arrow_mediating (x : S ↓ T) :
  `2 (Comma_to_Arrow x) = `2 x := eq_refl.

Example Comma_to_Arrow_dom_leg (x y : S ↓ T) (f : x ~> y) :
  fmap[Arrow_dom] (fmap[Comma_to_Arrow] f) = fmap[S] (fst ``f) := eq_refl.

Example Comma_to_Arrow_cod_leg (x y : S ↓ T) (f : x ~> y) :
  fmap[Arrow_cod] (fmap[Comma_to_Arrow] f) = fmap[T] (snd ``f) := eq_refl.

(* Exercise 3 for [P] and [Q] as well: both projections act on a comma
   morphism -- a commuting square -- by returning its leg in the relevant
   factor, definitionally. *)
Example comma_proj1_fmap (x y : S ↓ T) (f : x ~> y) :
  fmap[comma_proj1] f = fst ``f := eq_refl.

Example comma_proj2_fmap (x y : S ↓ T) (f : x ~> y) :
  fmap[comma_proj2] f = snd ``f := eq_refl.

Lemma Comma_to_Arrow_is_proj_nat (x : S ↓ T) :
  `2 (Comma_to_Arrow x) = comma_proj_nat x.
Proof. destruct x as [[a b] h]; reflexivity. Qed.

Lemma Comma_to_Arrow_naturality (x y : S ↓ T) (f : x ~> y) :
  comma_proj_nat y ∘ fmap[S ◯ comma_proj1] f
    ≈ fmap[T ◯ comma_proj2] f ∘ comma_proj_nat x.
Proof. apply naturality_sym. Qed.

(** ** The commuting diagram, Mac Lane's displays (5)-(6) *)

(* [Defined], not [Qed], for the same reason as [comma_mediator_proj1] below:
   [comma_diagram_self] feeds these two back in as the hypotheses of the
   universal property and needs their object components to reduce. *)
Theorem comma_diagram_dom :
  @equiv _ (@Functor_StrictEq_Setoid (S ↓ T) C)
         (Arrow_dom ◯ Comma_to_Arrow) (S ◯ comma_proj1).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Theorem comma_diagram_cod :
  @equiv _ (@Functor_StrictEq_Setoid (S ↓ T) C)
         (Arrow_cod ◯ Comma_to_Arrow) (T ◯ comma_proj2).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Example comma_diagram_dom_obj (x : S ↓ T) : `1 comma_diagram_dom x = eq_refl
  := eq_refl.

Example comma_diagram_cod_obj (x : S ↓ T) : `1 comma_diagram_cod x = eq_refl
  := eq_refl.

Corollary comma_diagram_dom_Cat :
  Arrow_dom ◯ Comma_to_Arrow ≈[Cat] S ◯ comma_proj1.
Proof. apply strict_equiv_implies_fun_equiv, comma_diagram_dom. Qed.

Corollary comma_diagram_cod_Cat :
  Arrow_cod ◯ Comma_to_Arrow ≈[Cat] T ◯ comma_proj2.
Proof. apply strict_equiv_implies_fun_equiv, comma_diagram_cod. Qed.

End CommaToArrow.

(** ** Rebuilding a comma / arrow object from its cast components *)

Lemma arrow_eta_cast {C : Category} (z : @Arrow C) {d0 d1 : C}
      (p : Arrow_dom z = d0) (q : Arrow_cod z = d1) :
  (((d0, d1); hom_cast p q (`2 z)) : @Arrow C) = z.
Proof. destruct z as [[c0 c1] h]; simpl in *; destruct p, q; reflexivity. Defined.

(* A [hom_cast] between two arrow objects presented through [arrow_eta_cast]
   is settled by its two legs, which is all the hom-setoid of the arrow
   category records.  Every endpoint here is a variable, so the whole proof is
   a [destruct] of the four object equalities; the lemma is then applied — not
   rewritten with — so that unification may unfold [Arrow] to [Id ↓ Id]. *)
Lemma arrow_eta_cast_legs {C : Category} (z w : @Arrow C) {d0 d1 e0 e1 : C}
      (p : Arrow_dom z = d0) (q : Arrow_cod z = d1)
      (p' : Arrow_dom w = e0) (q' : Arrow_cod w = e1)
      (u : (((d0, d1); hom_cast p q (`2 z)) : @Arrow C)
             ~> (((e0, e1); hom_cast p' q' (`2 w)) : @Arrow C))
      (v : z ~{@Arrow C}~> w) :
  hom_cast p p' (fmap[Arrow_dom] v) ≈ fmap[Arrow_dom] u
  → hom_cast q q' (fmap[Arrow_cod] v) ≈ fmap[Arrow_cod] u
  → hom_cast (arrow_eta_cast z p q) (arrow_eta_cast w p' q') u ≈ v.
Proof.
  destruct z as [[c0 c1] h], w as [[c0' c1'] h']; simpl in *.
  destruct p, q, p', q'; simpl.
  intros H0 H1; split; [ now symmetry | now symmetry ].
Qed.

(** ** Mac Lane §II.6 Exercise 5: the universal property *)

Section UMP.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.
Context {X : Category}.
Context {P' : X ⟶ A}.
Context {Q' : X ⟶ B}.
Context {R' : X ⟶ @Arrow C}.

Context (Hdom : @equiv _ (@Functor_StrictEq_Setoid X C)
                       (Arrow_dom ◯ R') (S ◯ P')).
Context (Hcod : @equiv _ (@Functor_StrictEq_Setoid X C)
                       (Arrow_cod ◯ R') (T ◯ Q')).

Definition ump_dom_obj (x : X) : Arrow_dom (R' x) = S (P' x) := `1 Hdom x.
Definition ump_cod_obj (x : X) : Arrow_cod (R' x) = T (Q' x) := `1 Hcod x.

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition comma_mediator : X ⟶ (S ↓ T) := {|
  fobj := fun x => ((P' x, Q' x);
                    hom_cast (ump_dom_obj x) (ump_cod_obj x) (`2 (R' x)));
  fmap := fun _ _ g => ((fmap[P'] g, fmap[Q'] g); _)
|}.
Next Obligation.
  intros x y g; simpl.
  rewrite <- (strict_fmap_cast Hdom g), <- (strict_fmap_cast Hcod g).
  rewrite !hom_cast_comp.
  apply hom_cast_respects.
  exact (`2 (fmap[R'] g)).
Qed.
Next Obligation.
  intros x y f g e; split; simpl; now rewrite e.
Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

(* [Defined], not [Qed]: [comma_mediator_mediates] below projects out the
   object-equality component and needs it to reduce to [eq_refl]. *)
Theorem comma_mediator_proj1 :
  @equiv _ (@Functor_StrictEq_Setoid X A) (comma_proj1 ◯ comma_mediator) P'.
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Theorem comma_mediator_proj2 :
  @equiv _ (@Functor_StrictEq_Setoid X B) (comma_proj2 ◯ comma_mediator) Q'.
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Example comma_mediator_proj1_obj (x : X) : `1 comma_mediator_proj1 x = eq_refl
  := eq_refl.

Example comma_mediator_proj2_obj (x : X) : `1 comma_mediator_proj2 x = eq_refl
  := eq_refl.

Theorem comma_mediator_arrow :
  @equiv _ (@Functor_StrictEq_Setoid X (@Arrow C))
         (Comma_to_Arrow ◯ comma_mediator) R'.
Proof.
  apply (Build_strict_eq (F := Comma_to_Arrow ◯ comma_mediator) (G := R')
           (fun x => arrow_eta_cast (R' x) (ump_dom_obj x) (ump_cod_obj x))).
  intros x y g.
  apply arrow_eta_cast_legs.
  - exact (strict_fmap_cast Hdom g).
  - exact (strict_fmap_cast Hcod g).
Qed.

(** The three commuting equations for a competing mediator. *)
Definition MediatesDiagram (L : X ⟶ (S ↓ T)) : Type :=
  { k1 : @equiv _ (@Functor_StrictEq_Setoid X A) (comma_proj1 ◯ L) P' &
  { k2 : @equiv _ (@Functor_StrictEq_Setoid X B) (comma_proj2 ◯ L) Q' &
    ∀ x : X,
      hom_cast (f_equal S (`1 k1 x)) (f_equal T (`1 k2 x)) (`2 (L x))
        ≈ hom_cast (ump_dom_obj x) (ump_cod_obj x) (`2 (R' x)) }}.

Lemma comma_mediator_mediates : MediatesDiagram comma_mediator.
Proof.
  exists comma_mediator_proj1, comma_mediator_proj2.
  intro x; reflexivity.
Qed.

Theorem comma_mediator_unique (L : X ⟶ (S ↓ T)) :
  MediatesDiagram L → L ≈[Cat] comma_mediator.
Proof.
  intros [k1 [k2 k3]].
  unshelve eexists.
  - intro x.
    unshelve refine
      (@Build_Isomorphism (S ↓ T) (L x) (comma_mediator x)
         ((id_cast (`1 k1 x), id_cast (`1 k2 x)); _)
         ((id_cast (eq_sym (`1 k1 x)), id_cast (eq_sym (`1 k2 x))); _)
         _ _).
    + simpl.
      rewrite !fmap_id_cast.
      rewrite <- (k3 x), hom_cast_decompose.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
    + simpl.
      rewrite !fmap_id_cast, <- !eq_sym_map_distr.
      rewrite <- (k3 x), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l.
      now rewrite id_left.
    + split; simpl; apply id_cast_inv_r.
    + split; simpl; apply id_cast_inv_l.
  - intros x y g; split; simpl.
    + rewrite <- (strict_fmap_cast k1 g), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l, id_left.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
    + rewrite <- (strict_fmap_cast k2 g), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l, id_left.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
Qed.

Theorem comma_diagram_ump :
  { L : X ⟶ (S ↓ T)
  & (MediatesDiagram L * (∀ L' : X ⟶ (S ↓ T), MediatesDiagram L' → L' ≈[Cat] L))%type }.
Proof.
  exists comma_mediator.
  split.
  - exact comma_mediator_mediates.
  - exact comma_mediator_unique.
Defined.

End UMP.

(** ** Non-vacuity: the comma category is its own mediator *)

(* The hypotheses of the universal property are inhabited -- by the diagram
   the comma category itself carries, where they are literally
   [comma_diagram_dom] and [comma_diagram_cod] -- and at that competitor the
   mediator produced is [≈[Cat]] the identity functor (strictly so, in fact:
   [comma_diagram_self_strict]).  The identity moreover satisfies
   [MediatesDiagram] outright ([comma_id_mediates], three reflexivities), so
   [comma_mediator_unique] can be EXERCISED at it
   ([comma_diagram_self_via_ump]) -- with that, both halves of Exercise 5 are
   checked against the one case whose answer is forced. *)
Section SelfMediation.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

Definition comma_self_mediator : (S ↓ T) ⟶ (S ↓ T) :=
  comma_mediator (P' := comma_proj1) (Q' := comma_proj2) (R' := Comma_to_Arrow)
                 comma_diagram_dom comma_diagram_cod.

Example comma_self_mediator_fobj (x : S ↓ T) :
  comma_self_mediator x = ((fst ``x, snd ``x); `2 x) := eq_refl.

Theorem comma_diagram_self : comma_self_mediator ≈[Cat] Id[S ↓ T].
Proof.
  unshelve eexists.
  - intro x.
    unshelve refine
      (@Build_Isomorphism (S ↓ T) (comma_self_mediator x) x
         ((id, id); _) ((id, id); _) _ _).
    + abstract (simpl; rewrite !fmap_id, id_left; now rewrite id_right).
    + abstract (simpl; rewrite !fmap_id, id_left; now rewrite id_right).
    + split; simpl; apply id_left.
    + split; simpl; apply id_left.
  - intros x y g; split; simpl; now rewrite id_left, id_right.
Qed.

(* The strict form is also available: the self-mediator and the identity
   have literally the same object map, and their fmaps agree by the
   category laws. *)
Theorem comma_diagram_self_strict :
  @equiv _ Functor_StrictEq_Setoid comma_self_mediator Id[S ↓ T].
Proof.
  unshelve eexists.
  - intro x; destruct x as [[a b] h]; reflexivity.
  - intros [[a b] h] [[a' b'] h'] f; split; simpl; cat.
Qed.

(* The identity functor satisfies [MediatesDiagram] at the comma's own
   diagram by three reflexivities -- which lets the UNIQUENESS half of the
   universal property be exercised, not merely stated: [comma_mediator_unique]
   at this competitor re-derives [comma_diagram_self] from the other side.
   (Adapted from the adversarial audit's probe, with thanks.) *)
Lemma comma_id_mediates :
  MediatesDiagram (P' := comma_proj1) (Q' := comma_proj2) (R' := Comma_to_Arrow)
                  comma_diagram_dom comma_diagram_cod (Id[S ↓ T]).
Proof.
  unshelve eexists.
  - exists (fun _ => eq_refl); intros; reflexivity.
  - unshelve eexists.
    + exists (fun _ => eq_refl); intros; reflexivity.
    + intro x; reflexivity.
Qed.

Theorem comma_diagram_self_via_ump : Id[S ↓ T] ≈[Cat] comma_self_mediator.
Proof. exact (comma_mediator_unique _ _ _ comma_id_mediates). Qed.

End SelfMediation.
