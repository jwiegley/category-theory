Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Top.

Generalizable All Variables.

(** * The underlying-set functor of Top and its adjoint triple

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.9
    (book pp. 132-135): the underlying-set functor of spaces
    [maclane:V.9:construction1] and Exercise 2 [maclane:V.9:ex2].
    Riehl, "Category Theory in Context", §4.1, Example 4.1.6: the adjoint
    triple D ⊣ U ⊣ I for spaces, each adjunction a transposition bijection
    on continuous maps.
    Fong and Spivak, "Seven Sketches in Compositionality", §7.3.2,
    Example 7.28 and Exercise 7.29: the two extreme topologies on a set,
    and the fact that every function out of a discrete space is continuous.
    nLab: https://ncatlab.org/nlab/show/Top
    nLab: https://ncatlab.org/nlab/show/adjoint+triple

    The classical statement: the functor stripping a space to its set of
    points is faithful and sits in an adjoint triple

        Discrete  ⊣  Forget  ⊣  Indiscrete,

    so it preserves all limits and all colimits; and the triple stops
    there — the indiscrete functor has no right adjoint, because a right
    adjoint would make it preserve colimits and it visibly does not
    (Exercise 2).  Both extreme topologies already live in Instance/Top.v
    ([Discrete_Top], [Indiscrete_Top] — Seven Sketches' Example 7.28), as
    do both transposes: [out_of_discrete_continuous] (every setoid map out
    of a discrete space is continuous — Exercise 7.29, the counit-side
    transpose of the first adjunction) and [into_indiscrete_continuous]
    (every setoid map into an indiscrete space is continuous — the
    unit-side transpose of the second).

    WHERE THE PACKAGED ADJUNCTIONS CANNOT LIVE, AND WHY.  In this library
    the statement above meets a genuine size stratification, and the file's
    shape is dictated by it, so it is spelled out once, here.

      - The hom-sets of [Top] are LARGE: continuity is Type-valued data
        quantifying over the opens of the codomain, so a continuous map
        does not fit at the level [o] of the points — the hom level [h]
        of [Top@{h o}] carries the strict constraint o < h
        (Instance/Top.v, header point 2 and [ContinuousMorphism_equiv]).
      - Every functor in this library imposes h₁ ≤ h₂ between its domain
        and codomain hom levels: the [fmap_respects] field of [Functor] is
        a [Proper] instance taken at the CODOMAIN's levels
        (Theory/Functor.v), which squeezes the hom-map's function space
        into the codomain level.
      - [Sets@{o so}] has objects SetoidObject@{o o} and homs at level
        [o], and the records involved are not cumulative.

    Consequently a functor [Top@{h o} ⟶ Sets@{o so}] — the underlying-set
    functor valued in the Sets WHOSE OBJECTS ARE THE POINT SETOIDS — is
    rejected by the elaborator outright (it would need h ≤ o against
    o < h).  A functor out of [Top] must land one level up, in
    [Sets@{h so}], with the point setoids lifted ([Setoid_Lift],
    Instance/Sets/Classifier.v — the lift changes carrier and equivalence
    not at all, only their universe packaging); this is the same placement
    Instance/Top/Closed.v gives its open- and closed-set functors out of
    [Top^op].  Dually, a functor INTO [Top@{h o}] from a Sets must come
    from [Sets@{o so}] exactly — its objects must be point setoids.  An
    [Adjunction] record between the two would need both functors to share
    ONE Sets, at levels o and h simultaneously, with o < h: the packaged
    triple is unformable at every universe assignment.  This is the
    library's familiar classifier phenomenon (Instance/Sets/Classifier.v
    keeps the Sets classifier as cross-universe theorems for the same
    reason), not a defect of the mathematics: with invariant records, "the
    category of sets containing the points" and "the category of sets
    large enough to receive the homs of Top" are different instantiations
    of [Sets].

    WHAT IS DELIVERED INSTEAD — the strongest formable readings, in the
    Classifier.v style:

      - [Top_Forget : Top@{h o} ⟶ Sets@{h so}], the underlying-set
        functor into the lifted Sets, with [Top_Forget_Faithful].
      - [Top_Discrete], [Top_Indiscrete] : Sets@{o so} ⟶ Top@{h o}, the
        two extreme-topology functors at their natural level.
      - The two adjunctions as CROSS-UNIVERSE TRANSPOSITION ISOMORPHISMS
        of hom-setoids ([discrete_adj], [indiscrete_adj]) with all four
        naturality squares each, packaged as
        [discrete_forget_indiscrete_triple].  Both bijections are the
        identity on underlying maps.  (Where the classical naturality
        square mentions [fmap] of the forgetful functor, the formable
        statement uses the stripped map itself — the lifted [fmap] lives
        between lifted objects and cannot be composed with the unlifted
        transpose.)
      - Preservation of limits and colimits by the underlying-set functor,
        stated shape-wise: the per-diagram stripping functor
        [Forget_Diagram] (for shapes small enough to carry it, which every
        concrete shape in this library is), and the theorems
        [Forget_preserves_limit_cone] / [Forget_preserves_colimit_cocone],
        proved by the two transposes exactly as the adjunctions would have
        — a competing cone in [Sets] transposes along Discrete, a
        competing cocone along Indiscrete.  (The competitor side is stated
        as raw vertex-legs-coherence data; the preservation section
        explains the second stratification that forces this.)  Cone-level
        preservation for the LIFTED functor is neither claimed nor
        concluded: its competitors have big vertices, which no space can
        receive.
      - Exercise 2 in two strengths:
          [indiscrete_image_not_colimiting] — the indiscrete image of the
            coproduct cocone 1 + 1 = 2 of [Sets] is not colimiting in
            [Top]: the indiscrete functor does not preserve a coproduct.
            (The packaged contrapositive through
            [CocontinuousFunctor] cannot even be instantiated at
            [Top_Indiscrete] — see the preservation section — so the
            concrete refutation is the statement.)
          [indiscrete_no_right_adjoint] — no adjunction-shaped data for a
            right adjoint exists: quantifying over an object map
            [R₀ : TopSpace → SetoidObject] together with a transposition
            bijection natural in the Sets variable — exactly the data any
            right adjoint would restrict to, and strictly less than
            functoriality — still yields False.  The classical statement
            "there is no functor R : Top ⟶ Sets with Indiscrete ⊣ R" is
            subsumed: here the TYPE of such an R is itself unformable
            (first bullet above), and the theorem refutes even the data a
            candidate at any level would provide.

    THE OBSTRUCTION, CONCRETELY.  The refuted colimit is the issue's
    suggested one.  In [Sets] the coproduct of two one-point setoids is
    the two-point setoid with its constant injections; [Top_Indiscrete]
    sends it to the two-point indiscrete space, but the coproduct of two
    one-point spaces in [Top] is the two-point DISCRETE space.  The
    mediating map the colimit property would produce into the discrete
    competitor sends true to true and false to false — the identity
    carrier map from the indiscrete two-point space to the discrete one,
    which Instance/Top.v's [indiscrete_to_discrete_id_not_continuous]
    already refutes; here the refutation is re-derived directly: the
    preimage of [singleton_true_open] would be an open of the indiscrete
    space holding at true but not at false, and indiscrete opens are
    UNIFORM.  (Issue #432 will package the adjoint-obstruction idiom
    reusably; it has not landed, so per the issue's correction the
    contrapositive is taken locally.) *)

#[local] Obligation Tactic := idtac.

(** ** The underlying-set functor *)

(* Objects to their point setoids — lifted one level, as the header
   explains — and arrows to their setoid maps.  Carrier and equivalence
   of every image are definitionally those of the space's own points. *)
Program Definition Top_Forget@{o h so | o < h, h < so +} :
  Top@{h o} ⟶ Sets@{h so} := {|
  fobj := fun X : TopSpace@{o} => Setoid_Lift@{o h} (top_carrier X);
  fmap := fun X Y f => SetoidMorphism_Lift@{o h} (continuous_map f)
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(* Faithfulness, Mac Lane's "concrete category" clause for Top: the
   hom-setoid of [Top] compares exactly what the image compares — the
   action on points — so injectivity of fmap is the identity. *)
#[export] Instance Top_Forget_Faithful : Faithful Top_Forget.
Proof. constructor; intros x y f g H p; exact (H p). Qed.

(** ** The discrete-topology functor and its transposition *)

Program Definition Top_Discrete@{o h so | o < h, o < so +} :
  Sets@{o so} ⟶ Top@{h o} := {|
  fobj := fun A : SetoidObject@{o o} => Discrete_Top@{o o} A;
  fmap := fun A B f => {|
    continuous_map := f;
    continuity := out_of_discrete_continuous A (Discrete_Top B) f
  |}
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(* The transposition bijection of Discrete ⊣ Forget: a continuous map out
   of a discrete space IS its underlying setoid map ([to]), and every
   setoid map out of a discrete space is continuous ([from] — Seven
   Sketches' Exercise 7.29, [out_of_discrete_continuous]).  The Sets-side
   hom-setoid is lifted to sit beside Top's large hom-setoid in one
   ambient Sets — the piecewise-lift discipline of
   Instance/Sets/Classifier.v. *)
Program Definition discrete_adj (A : SetoidObject) (Y : TopSpace) :
  @Isomorphism Sets
    {| carrier := Top_Discrete A ~{Top}~> Y
     ; is_setoid := @homset Top (Top_Discrete A) Y |}
    (Setoid_Lift
       {| carrier := A ~{Sets}~> top_carrier Y
        ; is_setoid := @homset Sets A (top_carrier Y) |}) := {|
  to := {| morphism := fun f => continuous_map f |};
  from := {| morphism := fun g =>
    {| continuous_map := g;
       continuity := out_of_discrete_continuous A Y g |} |}
|}.
Next Obligation. intros A Y f g H; exact H. Qed.
Next Obligation. intros A Y f g H; exact H. Qed.
Next Obligation. intros A Y g p; reflexivity. Qed.
Next Obligation. intros A Y f p; reflexivity. Qed.

(* The four naturality squares of the adjunction, for the forward and the
   inverse transpose.  Where the classical square would say
   [fmap[Top_Forget] f] the statement uses the stripped map
   [continuous_map f] — see the header. *)
Lemma discrete_adj_nat_l (A A' : SetoidObject) (Y : TopSpace)
  (f : Top_Discrete A ~{Top}~> Y) (g : A' ~{Sets}~> A) :
  to (discrete_adj A' Y) (f ∘[Top] fmap[Top_Discrete] g)
    ≈ to (discrete_adj A Y) f ∘[Sets] g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_nat_r (A : SetoidObject) (Y Z : TopSpace)
  (f : Y ~{Top}~> Z) (g : Top_Discrete A ~{Top}~> Y) :
  to (discrete_adj A Z) (f ∘[Top] g)
    ≈ continuous_map f ∘[Sets] to (discrete_adj A Y) g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_inv_nat_l (A A' : SetoidObject) (Y : TopSpace)
  (f : A ~{Sets}~> top_carrier Y) (g : A' ~{Sets}~> A) :
  from (discrete_adj A' Y) (f ∘[Sets] g)
    ≈ from (discrete_adj A Y) f ∘[Top] fmap[Top_Discrete] g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_inv_nat_r (A : SetoidObject) (Y Z : TopSpace)
  (f : Y ~{Top}~> Z) (g : A ~{Sets}~> top_carrier Y) :
  from (discrete_adj A Z) (continuous_map f ∘[Sets] g)
    ≈ f ∘[Top] from (discrete_adj A Y) g.
Proof. intro p; reflexivity. Qed.

(** ** The indiscrete-topology functor and its transposition *)

Program Definition Top_Indiscrete@{o h so | o < h, o < so +} :
  Sets@{o so} ⟶ Top@{h o} := {|
  fobj := fun A : SetoidObject@{o o} => Indiscrete_Top@{o o} A;
  fmap := fun A B f => {|
    continuous_map := f;
    continuity := into_indiscrete_continuous (Indiscrete_Top A) B f
  |}
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(* The transposition bijection of Forget ⊣ Indiscrete: a continuous map
   into an indiscrete space IS its underlying setoid map ([from]), and
   every setoid map into an indiscrete space is continuous ([to] —
   [into_indiscrete_continuous]).  This time the small side is the
   Sets-hom out of the points, lifted as before. *)
Program Definition indiscrete_adj (X : TopSpace) (B : SetoidObject) :
  @Isomorphism Sets
    (Setoid_Lift
       {| carrier := top_carrier X ~{Sets}~> B
        ; is_setoid := @homset Sets (top_carrier X) B |})
    {| carrier := X ~{Top}~> Top_Indiscrete B
     ; is_setoid := @homset Top X (Top_Indiscrete B) |} := {|
  to := {| morphism := fun g =>
    {| continuous_map := g;
       continuity := into_indiscrete_continuous X B g |} |};
  from := {| morphism := fun f => continuous_map f |}
|}.
Next Obligation. intros X B f g H; exact H. Qed.
Next Obligation. intros X B f g H; exact H. Qed.
Next Obligation. intros X B f p; reflexivity. Qed.
Next Obligation. intros X B g p; reflexivity. Qed.

Lemma indiscrete_adj_nat_l (X X' : TopSpace) (B : SetoidObject)
  (g : top_carrier X ~{Sets}~> B) (f : X' ~{Top}~> X) :
  to (indiscrete_adj X' B) (g ∘[Sets] continuous_map f)
    ≈ to (indiscrete_adj X B) g ∘[Top] f.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_nat_r (X : TopSpace) (B B' : SetoidObject)
  (g' : B ~{Sets}~> B') (g : top_carrier X ~{Sets}~> B) :
  to (indiscrete_adj X B') (g' ∘[Sets] g)
    ≈ fmap[Top_Indiscrete] g' ∘[Top] to (indiscrete_adj X B) g.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_inv_nat_l (X X' : TopSpace) (B : SetoidObject)
  (f : X ~{Top}~> Top_Indiscrete B) (g : X' ~{Top}~> X) :
  from (indiscrete_adj X' B) (f ∘[Top] g)
    ≈ from (indiscrete_adj X B) f ∘[Sets] continuous_map g.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_inv_nat_r (X : TopSpace) (B B' : SetoidObject)
  (g' : B ~{Sets}~> B') (f : X ~{Top}~> Top_Indiscrete B) :
  from (indiscrete_adj X B') (fmap[Top_Indiscrete] g' ∘[Top] f)
    ≈ g' ∘[Sets] from (indiscrete_adj X B) f.
Proof. intro p; reflexivity. Qed.

(* Mac Lane §V.9's construction, packaged: the two natural transposition
   bijections flanking the underlying-set functor, with their eight
   naturality squares.  This is Riehl's Example 4.1.6 in the only form the
   universe stratification lets the library state it. *)
Definition discrete_forget_indiscrete_triple :=
  (@discrete_adj, @indiscrete_adj,
   (@discrete_adj_nat_l, @discrete_adj_nat_r,
    @discrete_adj_inv_nat_l, @discrete_adj_inv_nat_r),
   (@indiscrete_adj_nat_l, @indiscrete_adj_nat_r,
    @indiscrete_adj_inv_nat_l, @indiscrete_adj_inv_nat_r)).

(** ** The underlying-set functor preserves limits and colimits

    Shape-wise, through the stripping functor: for a diagram in [Top] over
    a (small-hommed) shape, the underlying diagram in [Sets] at the
    natural level.  The two preservation theorems are RAPL and LAPC for
    the adjoint triple, proved exactly as the adjunctions would prove
    them: a competing cone in [Sets] transposes along Discrete to a
    competing cone in [Top], a competing cocone along Indiscrete.

    ONE MORE STRATIFICATION NOTE, parallel to the header's.  The
    limit-cone predicates share a single hom universe between the shape
    and the ambient category: [IsLimitCone] and [IsColimitCocone]
    (Structure/Limit/Preservation.v) accept only cones at instance
    Cone@{u u0 u0 u1 u0 u0}, and [Cocone] (Structure/Cone.v) pins the
    same identification, so LIMITING cones over ONE shape variable
    cannot live in [Top] (homs at h) and in [Sets] (homs at o) within
    one statement.  (The bare [Cone] record itself imposes only
    shape-hom ≤ ambient-hom; both cones exist separately — it is the
    predicate applied to both that cannot be formed.)  The competitor side is therefore stated RAW —
    vertex, legs and coherence as bare data, which is [IsLimitCone] with
    the competing cone's record unfolded — while the [Top] side keeps the
    record vocabulary.  For the same reason the packaged image-cone
    machinery ([FCocone], [PreservesColimitCocone], and the
    Continuous/CocontinuousFunctor classes of
    Structure/Limit/Preservation.v) cannot be instantiated across the
    o < h gap at all: preservation for [Top_Forget] is carried by the raw
    statements below, and the breakdown of preservation for
    [Top_Indiscrete] by the concrete colimit refutation of Exercise 2. *)

(* The raw competitors of the two theorems below are cones over this
   functor up to conversion — [legs j : A ~{Sets}~> top_carrier (K j)]
   IS [A ~{Sets}~> Forget_Diagram K j] definitionally; only the
   [IsLimitCone]-level packaging is unformable. *)
Program Definition Forget_Diagram {J : Category} (K : J ⟶ Top) :
  J ⟶ Sets := {|
  fobj := fun j => top_carrier (K j);
  fmap := fun i j f => continuous_map (fmap[K] f)
|}.
Next Obligation.
  intros J K i j f g H p.
  exact (@fmap_respects _ _ K i j f g H p).
Qed.
Next Obligation. intros J K j p; exact (@fmap_id _ _ K j p). Qed.
Next Obligation.
  intros J K i j k f g p; exact (@fmap_comp _ _ K i j k f g p).
Qed.

(* Stripping preserves limiting cones.  The competitor is raw Sets-side
   data (vertex, legs, coherence); it transposes along the discrete
   topology to a genuine cone in [Top], the limit property of N answers,
   and the mediator strips back down.  This is RAPL for Discrete ⊣ Forget,
   in the only cross-universe form the [Cone] record allows. *)
Theorem Forget_preserves_limit_cone {J : Category} {K : J ⟶ Top}
  (N : Cone K) (HN : IsLimitCone N)
  (A : SetoidObject) (legs : ∀ j : J, A ~{Sets}~> top_carrier (K j))
  (coh : ∀ (x y : J) (f : x ~{J}~> y),
     continuous_map (fmap[K] f) ∘[Sets] legs x ≈ legs y) :
  ∃! u : A ~{Sets}~> top_carrier (vertex_obj[N]),
    ∀ j : J, continuous_map (cone_leg N j) ∘[Sets] u ≈ legs j.
Proof.
  pose (M' := @Build_Cone J Top K (Discrete_Top A)
    (@Build_ACone J Top (Discrete_Top A) K
       (fun j => Build_ContinuousMorphism (Discrete_Top A) (K j)
                   (legs j)
                   (out_of_discrete_continuous A (K j) (legs j)))
       (fun x y f => coh x y f))).
  destruct (HN M') as [u Hu Huniq].
  unshelve refine {| unique_obj := continuous_map u |}.
  - intros j p; exact (Hu j p).
  - intros v Hv p.
    exact (Huniq (Build_ContinuousMorphism (Discrete_Top A)
                    (vertex_obj[N]) v
                    (out_of_discrete_continuous A (vertex_obj[N]) v))
                 (fun j q => Hv j q) p).
Defined.

(* Stripping preserves colimiting cocones, dually: a raw Sets-side
   cocone competitor transposes along the indiscrete topology.  LAPC for
   Forget ⊣ Indiscrete. *)
Theorem Forget_preserves_colimit_cocone {J : Category} {K : J ⟶ Top}
  (N : Cocone K) (HN : IsColimitCocone N)
  (A : SetoidObject) (injs : ∀ j : J, top_carrier (K j) ~{Sets}~> A)
  (coh : ∀ (x y : J) (f : x ~{J}~> y),
     injs y ∘[Sets] continuous_map (fmap[K] f) ≈ injs x) :
  ∃! u : top_carrier (vertex_obj[N]) ~{Sets}~> A,
    ∀ j : J, u ∘[Sets] continuous_map (cocone_inj N j) ≈ injs j.
Proof.
  pose (M' := @Build_Cone (J^op) (Top^op) (K^op) (Indiscrete_Top A)
    (@Build_ACone (J^op) (Top^op) (Indiscrete_Top A) (K^op)
       (fun j => Build_ContinuousMorphism (K j) (Indiscrete_Top A)
                   (injs j)
                   (into_indiscrete_continuous (K j) A (injs j)))
       (fun x y f => coh y x f))).
  destruct (HN M') as [u Hu Huniq].
  unshelve refine {| unique_obj := continuous_map u |}.
  - intros j p; exact (Hu j p).
  - intros v Hv p.
    exact (Huniq (Build_ContinuousMorphism (vertex_obj[N])
                    (Indiscrete_Top A) v
                    (into_indiscrete_continuous (vertex_obj[N]) A v))
                 (fun j q => Hv j q) p).
Defined.

(** ** Exercise 2: the indiscrete functor has no right adjoint *)

(* THE SHAPE.  The two-object discrete shape is taken as [DiscreteCat bool]
   (Instance/Discrete.v) rather than the tree's walking pair
   [Two_Discrete]: the limit-cone predicates and [Cocone] pin the
   shape's hom level to the ambient category's (the stratification note
   above), [Two_Discrete]'s
   hom level is declared at [Set], and [Top]'s hom level is strictly above
   its point level, so no cocone in [Top] can sit over a [Two_Discrete]
   diagram at all.  [DiscreteCat] is universe-flexible, so its instances
   can meet [Sets] at the point level and [Top] at the hom level. *)

(* Coherence of a cocone over a discrete shape, in any category: the only
   arrows are (transported) identities. *)
Lemma discrete_cocone_coherence {A : Type} {C : Category}
  (H : DiscreteCat A ⟶ C) (c : C) (inj : ∀ x : A, H x ~{C}~> c)
  {x y : A} (f : y ~{DiscreteCat A}~> x) :
  inj x ∘ fmap[H] f ≈ inj y.
Proof.
  destruct f.
  change (inj y ∘ fmap[H] (@id (DiscreteCat A) y) ≈ inj y).
  rewrite fmap_id; apply id_right.
Qed.

(* The discrete pair of one-point setoids. *)
Definition unit_pair_diagram : DiscreteCat bool ⟶ Sets :=
  @DiscreteCat_Functor bool Sets (fun _ => unit_setoid_object).

(* The coproduct cocone: apex the two-point setoid, injections the two
   constants. *)
Definition bool_cocone : Cocone unit_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Sets^op) (unit_pair_diagram^op)
    bool_setoid_object
    (@Build_ACone ((DiscreteCat bool)^op) (Sets^op) bool_setoid_object
       (unit_pair_diagram^op)
       (fun b => const_morphism unit_setoid_object bool_setoid_object b)
       (fun x y f => discrete_cocone_coherence unit_pair_diagram
                       bool_setoid_object _ f)).

(* [bool] with the constant injections is a colimiting cocone in [Sets]:
   the mediator reads a competitor's two legs off at the point, and any
   competitor agrees with it on both booleans.  ([IsColimitCocone] pins
   the ambient hom level to the shape's, and [bool : Set], so the
   colimit property is established at the Set hom level — the level at
   which the whole Exercise-2 argument runs.) *)
Definition bool_cocone_colimit : IsColimitCocone bool_cocone.
Proof.
  intro M.
  unshelve refine
    {| unique_obj := {| morphism := fun b : bool =>
         if b then cocone_inj M true ttt else cocone_inj M false ttt |} |}.
  - intros x; destruct x; intro p; destruct p; simpl; reflexivity.
  - intros v Hv b; destruct b.
    + symmetry; exact (Hv true ttt).
    + symmetry; exact (Hv false ttt).
Defined.

(* The image diagram, presented at the target level: the discrete pair of
   one-point indiscrete spaces.  (The composite
   [Top_Indiscrete ◯ unit_pair_diagram] and the generic
   [FCocone Top_Indiscrete bool_cocone] cannot be formed: like the
   limit-cone predicates, the composition and image-cocone constants pin
   ONE hom level across their categories, and the composite would need
   the shape's instance at both levels.  This diagram is the composite presented directly — the same
   objects definitionally, and the only arrows are identities.) *)
Program Definition indiscrete_pair_diagram@{o h so | o < h, o < so +} :
  DiscreteCat@{h h h} bool ⟶ Top@{h o} := {|
  fobj := fun _ : bool => Indiscrete_Top@{o o} unit_setoid_object@{o o};
  fmap := fun _ _ _ => top_id
|}.
Next Obligation. intros x y f g H p; reflexivity. Qed.
Next Obligation. intros x p; reflexivity. Qed.
Next Obligation. intros x y z f g p; reflexivity. Qed.

(* The indiscrete image of the coproduct cocone: apex the two-point
   indiscrete space, injections the images of the two constants. *)
Definition indiscrete_image_cocone : Cocone indiscrete_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Top^op) (indiscrete_pair_diagram^op)
    TwoPoint_Indiscrete
    (@Build_ACone ((DiscreteCat bool)^op) (Top^op) TwoPoint_Indiscrete
       (indiscrete_pair_diagram^op)
       (fun b => fmap[Top_Indiscrete]
                   (const_morphism unit_setoid_object bool_setoid_object b))
       (fun x y f => discrete_cocone_coherence indiscrete_pair_diagram
                       TwoPoint_Indiscrete _ f)).

(* The competing cocone in [Top]: the DISCRETE two-point space, with the
   two point injections — continuous because any map out of a one-point
   space is, its preimages being constant predicates ([open_const]). *)
Definition disc_leg (b : bool) :
  Indiscrete_Top unit_setoid_object ~{Top}~> Bool_Discrete :=
  Build_ContinuousMorphism (Indiscrete_Top unit_setoid_object) Bool_Discrete
    (const_morphism unit_setoid_object bool_setoid_object b)
    (fun U _ => open_const (Indiscrete_Top unit_setoid_object) (U b)).

Definition disc_cocone : Cocone indiscrete_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Top^op) (indiscrete_pair_diagram^op)
    Bool_Discrete
    (@Build_ACone ((DiscreteCat bool)^op) (Top^op) Bool_Discrete
       (indiscrete_pair_diagram^op)
       (fun b => disc_leg b)
       (fun x y f => discrete_cocone_coherence indiscrete_pair_diagram
                       Bool_Discrete _ f)).

(* The image cocone is NOT colimiting: the mediator to the discrete
   competitor would send true to true and false to false, and the
   preimage of [singleton_true_open] under it would be a non-uniform open
   of an indiscrete space.  With [bool_cocone_colimit] this is exactly
   "the indiscrete functor does not preserve the coproduct 1 + 1". *)
Theorem indiscrete_image_not_colimiting :
  IsColimitCocone indiscrete_image_cocone → False.
Proof.
  intro P.
  pose proof (colimitcocone_ump P disc_cocone) as U.
  pose proof (unique_property U true ttt) as Ht.
  pose proof (unique_property U false ttt) as Hf.
  simpl in Ht, Hf.
  pose proof (continuity (unique_obj U)
                (fun b : bool_setoid_object => b = true)
                singleton_true_open true false) as HO.
  discriminate (eq_trans (eq_sym Hf) (HO Ht)).
Qed.

(* Mac Lane §V.9, Exercise 2, in adjunction-shaped form.  The hypotheses
   are the data any right adjoint R would provide at the objects involved:
   its object map, and the transposition bijection
   Top(Indiscrete A, Y) ≅ Sets(A, R₀ Y), natural in A.  Nothing else is
   assumed — no functoriality of R₀, no naturality in Y — and False
   follows.  The proof mirrors the standard one: transposing the discrete
   competitor's legs and transposing back the induced map produces the
   non-continuous mediator of [indiscrete_image_not_colimiting]. *)
Theorem indiscrete_no_right_adjoint
  (R₀ : TopSpace → SetoidObject)
  (φ : ∀ (A : SetoidObject) (Y : TopSpace),
     @Isomorphism Sets
       {| carrier := Top_Indiscrete A ~{Top}~> Y
        ; is_setoid := @homset Top (Top_Indiscrete A) Y |}
       (Setoid_Lift
          {| carrier := A ~{Sets}~> R₀ Y
           ; is_setoid := @homset Sets A (R₀ Y) |}))
  (φ_nat : ∀ (A A' : SetoidObject) (g : A' ~{Sets}~> A) (Y : TopSpace)
             (f : Top_Indiscrete A ~{Top}~> Y),
     to (φ A' Y) (f ∘[Top] fmap[Top_Indiscrete] g)
       ≈ to (φ A Y) f ∘[Sets] g) :
  False.
Proof.
  (* the transposed legs, as points of R₀ Bool_Discrete *)
  pose (r := fun b : bool =>
               to (φ unit_setoid_object Bool_Discrete) (disc_leg b) ttt).
  (* the induced map out of the coproduct, and its transpose back *)
  assert (sp : Proper (respectful (@equiv _ (is_setoid bool_setoid_object))
                                  (@equiv _ (is_setoid (R₀ Bool_Discrete))))
                 (fun b : bool => if b then r true else r false)).
  { intros b b' Hb; simpl in Hb; subst; reflexivity. }
  pose (s := {| morphism := fun b : bool => if b then r true else r false
              ; proper_morphism := sp |}
             : bool_setoid_object ~{Sets}~> R₀ Bool_Discrete).
  pose (h := from (φ bool_setoid_object Bool_Discrete) s).
  (* h restricts along each injection to the corresponding leg: transpose,
     compute through the bijection's round trips, transpose back *)
  assert (Hleg : ∀ b : bool,
    h ∘[Top] fmap[Top_Indiscrete]
        (const_morphism unit_setoid_object bool_setoid_object b)
      ≈ disc_leg b).
  { intro b.
    assert (E : to (φ unit_setoid_object Bool_Discrete)
                   (h ∘[Top] fmap[Top_Indiscrete]
                      (const_morphism unit_setoid_object
                         bool_setoid_object b))
                  ≈ to (φ unit_setoid_object Bool_Discrete) (disc_leg b)).
    { etransitivity.
      { exact (φ_nat _ _ (const_morphism unit_setoid_object
                            bool_setoid_object b) _ h). }
      intro p; destruct p, b; simpl.
      - exact (iso_to_from (φ bool_setoid_object Bool_Discrete) s true).
      - exact (iso_to_from (φ bool_setoid_object Bool_Discrete) s false).
    }
    transitivity (from (φ unit_setoid_object Bool_Discrete)
                    (to (φ unit_setoid_object Bool_Discrete)
                        (h ∘[Top] fmap[Top_Indiscrete]
                           (const_morphism unit_setoid_object
                              bool_setoid_object b)))).
    { symmetry.
      exact (iso_from_to (φ unit_setoid_object Bool_Discrete) _). }
    transitivity (from (φ unit_setoid_object Bool_Discrete)
                    (to (φ unit_setoid_object Bool_Discrete) (disc_leg b))).
    { exact (proper_morphism (from (φ unit_setoid_object Bool_Discrete))
               _ _ E). }
    exact (iso_from_to (φ unit_setoid_object Bool_Discrete) (disc_leg b)).
  }
  (* whence h true = true and h false = false; continuity is refuted *)
  pose proof (Hleg true ttt) as Ht; simpl in Ht.
  pose proof (Hleg false ttt) as Hf; simpl in Hf.
  pose proof (continuity h (fun b : bool_setoid_object => b = true)
                singleton_true_open true false) as HO.
  discriminate (eq_trans (eq_sym Hf) (HO Ht)).
Qed.

(** ** Acceptance tests

    The definitional facts the header claims really are definitional. *)

(* Both adjoints are sections of the forgetful functor on objects, on the
   nose: forgetting either extreme topology returns the very lift of the
   original setoid. *)
Example forget_discrete_on_objects (A : SetoidObject) :
  Top_Forget (Top_Discrete A) = Setoid_Lift A := eq_refl.
Example forget_indiscrete_on_objects (A : SetoidObject) :
  Top_Forget (Top_Indiscrete A) = Setoid_Lift A := eq_refl.

(* Both transposition bijections are the identity on underlying maps. *)
Example discrete_transpose_identity (A : SetoidObject) (Y : TopSpace)
  (f : Top_Discrete A ~{Top}~> Y) :
  to (discrete_adj A Y) f = continuous_map f := eq_refl.
Example indiscrete_transpose_identity (X : TopSpace) (B : SetoidObject)
  (f : X ~{Top}~> Top_Indiscrete B) :
  from (indiscrete_adj X B) f = continuous_map f := eq_refl.

(* The indiscrete image of the coproduct apex is exactly the two-point
   indiscrete probe space of Instance/Top.v. *)
Example image_apex_is_TwoPoint_Indiscrete :
  vertex_obj[indiscrete_image_cocone] = TwoPoint_Indiscrete := eq_refl.
Example image_apex_is_indiscrete_of_bool :
  vertex_obj[indiscrete_image_cocone]
    = Top_Indiscrete (vertex_obj[bool_cocone]) := eq_refl.
