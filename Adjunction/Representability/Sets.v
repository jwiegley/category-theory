Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.Representability.

Generalizable All Variables.

(** * The representability theorem

    Mac Lane §V.6 Theorem 3 and Definition 3 (book p. 122,
    `maclane:V.6:thm3`, `maclane:V.6:def3`) with §V.8 Exercise 1 (book
    p. 131) and Riehl's 4.7.14, over `Sets`-valued functors: a functor
    [K : C ⟶ Sets] on a complete category that preserves limits and
    satisfies the solution set condition is REPRESENTABLE, and conversely.
    A satellite of Adjunction/Representability.v (#348) rather than an
    extension of it: the ingredients here are GAFT's and the hom-functor
    continuity of #428, and requiring them in the parent would take the
    closure every downstream consumer of #348's biconditional pays from 40
    modules to about 95.

    DEFINITION 3, and why the tree already had half of it.
    [ElementSolutionSet K] is the book's element-wise form — a [Type] of
    indices, an object and an ELEMENT of [K] at each, and a factorization
    of every element of every [K c] through one of them.  Adjunction/GAFT.v
    's [SolutionSet U d] is the hom-shaped form, and the two agree at the
    singleton: [sols_of_esols] and [esols_of_sols] pass between them,
    keeping index, objects and elements on the nose (four [eq_refl]
    readbacks).  The passage rests on elements being global points, which
    is Theory/Universal/Element.v:292's [global_elements_iso] — the issue
    asks for that bridge to be proved as a "reusable lemma"; it has existed
    since #318 and nothing here re-proves it.  The two records are NOT
    convertible, only inter-derivable (probe N1).

    THEOREM 3.  A representation is a universal element, hence an initial
    object of the category of elements, which Construction/Elements.v
    presents as the comma category [=(1) ↓ K]; GAFT's own machinery turns a
    solution set there into that initial object.  That step was sealed
    inside [GAFT]'s [Qed], so this issue exports it as
    Adjunction/GAFT.v's [comma_initial_of_sols] (appended at that file's
    end — every line above it stays put, eleven external citations pointing
    at its line 241 — with [GAFT_via_comma_initial] re-deriving GAFT from
    it as a cross-check that it IS the same step; the theorem itself is not
    rewritten to use it).  [representability_theorem] is then four existing
    constants composed with no tactic, and [representability_iff] adds the
    converse: a representable functor preserves limits
    ([continuous_of_representable], through Functor/Hom/Continuous.v:723's
    [representable_iso_ContinuousFunctor] — the #428 leg the issue does not
    name) and supplies its own element-wise solution set, the single object
    being the representing one and the single element the identity read
    across the isomorphism.

    §V.8 EXERCISE 1.  Forward: [HomAfter K 1] IS [Hom(1,−) ◯ K] on the nose
    (readback), global points make it [K] up to [homafter_one_iso] — NOT on
    the nose (probe N2) — so #348's [adj_representable] at the singleton
    transports onto [K], and [representable_of_left_adjoint] returns the
    left adjoint at the singleton as its representing object ([eq_refl]).
    Riehl 4.7.14 is the same passage after SAFT: [saft_representable].
    CONVERSE: it CANNOT be run with the tree's copowers.  Every copower in
    tree (Structure/Limit/Power.v, #366) is indexed by a bare [Type] and so
    yields plain functions out of the index, where a [Sets]-valued
    adjunction needs setoid morphisms respecting [≈]; a setoid-indexed
    copower does not exist in tree (probe N5 pins the mismatch).  So the
    converse is delivered as an axiom-free CONDITIONAL over
    [HasSetsCopowers], stated exactly as #348's
    [adjunction_iff_pointwise_representable] consumes it — which makes the
    hypothesis, by that same biconditional, "the represented functor has a
    left adjoint".  That is disclosed rather than hidden: the conditional
    is honest, not deep.

    WITNESSES.  Two, both with every premise discharged in tree.  The
    points functor [Sets_points := Hom(1,−)] on [Sets]: its element-wise
    solution set is the singleton at [1] with the identity as its element,
    its limit preservation is Functor/Hom/Limit.v's [hom_ContinuousFunctor],
    and [Sets_points_repr] is Theorem 3 applied; [Sets_points_iso] compares
    the object the theorem produces with [1] through
    [repr_unique_iso].  And the identity functor on [Sets], twice over:
    [Sets_Id_repr] by Theorem 3 from Adjunction/GAFT/Sets.v's own solution
    set, and [Sets_Id_repr_of_adjoint] by Exercise 1 from [GAFT_at_Sets_Id]
    's adjunction, whose representing object reads back at [eq_refl] as
    that adjoint at the singleton.

    STALE PREMISES — the issue's "Current state" is wrong in five
    substantive claims and six line numbers.  FALSE: "no
    [(1 ~{Sets}~> X) ≅ carrier X] lemma" (it is [global_elements_iso],
    Theory/Universal/Element.v:292, with the natural form at :1015);
    "the library never performs that instantiation" (Element.v:810 and :829
    relate [AUniversalArrow SetsOne H r] and [AUniversalElement H r] with
    [eq_refl] and [≈] round trips); "nothing produces a [Representable]
    from anything, and in particular not from an adjunction; no file even
    imports it" (14 sites conclude [Representable], one of them
    Adjunction/Representability.v:268's [adj_representable]); "no category
    of elements for a [Sets]-valued functor" (Construction/Elements.v has
    [Elements], [ElementsComma] and the proved comparison
    [Elements_Comma]); and "#366 is the filed obligation" for copowers
    (#366 landed).  STALE LINE NUMBERS: [Representable] is
    Functor/Representable.v:51, not :46 (the issue cites :46 six times);
    [representability_by_yoneda] is Structure/UniversalProperty.v:73, not
    :67-72; Instance/Sets.v:248 is :258 and the object wanted is
    Construction/Elements.v:230's [SetsOne]; Adjunction/Continuity.v:202 is
    :208-218; Construction/Comma/Limit.v:245 is :247;
    Theory/WeaklyInitial.v:89 is :102.  Correct as cited: GAFT.v:159 and
    :241, SAFT.v:274, Theory/Profunctor/Adjunction.v:70.  The
    [Sets_global_points] named in the issue's Verification block exists
    nowhere in tree, and is not created here — the bridge it seems to want
    is [global_elements_iso].

    UNIVERSES ([About] under `Set Printing Universes`).  Definition 3 is
    UNPINNED: [ElementSolutionSet@{u u0 u1 u2}] is over
    [C : Category@{u u0 u0}] with one strict constraint ([u0 < u1], the
    functor's) and no [Set].  Everything downstream of the comma-initial
    step inherits GAFT's pin instead — [representability_theorem] and
    [representability_iff] are over [C : Category@{_ Set Set}], hom AND
    proof at [Set], with [Set < u] — which is why the theorem is stated at
    TOP LEVEL: inside a section that has already elaborated a category with
    those levels apart the ascription is refused, and probe N4 pins exactly
    that ("universe inconsistency: Cannot enforce sp = sh because sh < sp").
    The witnesses land at [Sets@{Set u}], the same place
    Adjunction/GAFT/Sets.v's header records for [GAFT_at_Sets_Id].  Stdlib
    caps ([JMeq], [eq], [Logic_lemmas.equality], [Projections],
    [projections], [Basics.compose], [ID]) all arrive with the GAFT and
    [Sets] donors; none is introduced here.

    MEASURED.  38 `.glob` heads (32 `def`, 1 `prf`, 4 `proj`, 1 `rec`) and
    14 [Program] obligations (6 of [homafter_one_iso], discharged by its
    local tactic; 8 of [homafter_whisker], closed by hand under [idtac]),
    plus Adjunction/GAFT.v's 2 new heads — 54 constants, all "Closed under
    the global context", zero `Axioms:` lines; the `make print-assumptions`
    gate carries the 38 and the 2.  Four `Defined` in this file, each
    LOAD-BEARING (flipped to `Qed` one at a time in a copy of the whole
    file: [sols_of_esols] and [esols_of_sols] stop their index and element
    readbacks, [representability_iff] stops
    [representability_iff_fst], and [Sets_points_esol] stops
    [Sets_points_esol_obj]); eight `Qed`, all of them [homafter_whisker]'s
    obligations.  GAFT.v's [comma_initial_of_sols] is [Defined] because it
    produces DATA, matching [wif_of_sols] beside it, but the flip is NOT
    load-bearing — nothing in tree reads its components back, and it is
    disclosed here rather than claimed.  Closure 99 excluding self
    (Functor/Hom/Continuous.v 10 at the margin, Adjunction/GAFT/Sets.v 2,
    Adjunction/Representability.v 2, Construction/Comma/Creation.v 2,
    Adjunction/SAFT.v 1, the other twenty-one `Require`s 0; none is
    droppable).  Zero name collisions for the 38 names (`grep -rlw
    --include='*.v'`).  Test/ProbeRepresentability437.v mirrors this file's
    `Require` list and carries 6 refutation commands = 1 instrument + N1-N2
    CONVERSION (the two solution-set records are not the same type;
    [HomAfter K 1] is not [K]) + N3, N5 TYPING (the apex-only
    [PreservesAllLimits] does not ascribe where the cone-level
    [PreservesImageLimit] is asked; a [Type]-indexed copower family is not
    a [HasSetsCopowers] — "The term "X" has type "Type" while it is
    expected to have type "obj[Sets]"") + N4 UNIVERSE, each stripped one at
    a time in a copy of the whole file beside its accepted control; seven
    `eq_refl` readbacks; guard coverage 34/24 with ten exhaustive
    exceptions (identifier tokens inside the six refutation commands /
    also named outside them, comments stripped: two keywords, four bound
    variables and the four refuted names); rename-simulated 14 library
    names — [ElementSolutionSet], [SolutionSet], [SetsOne], [HomAfter],
    [Curried_Hom], [Compose], [representability_theorem],
    [PreservesAllLimits], [PreservesImageLimit], [Complete],
    [HasSetsCopowers], [Representable], [eq_refl], [Category] — every
    first break on a positive line.  `make todo` grows by the 6 refutation
    lines only (2283 → 2289 over #435's tip), so the issue's "adds no new
    hits" box is not met as written (disclosed, as in #430-#435); Coq 8.19
    and 8.20 are checked by nix source builds of the committed revision,
    which the PR records.

    NOT DELIVERED.  A setoid-indexed copower, hence no unconditional
    converse to Exercise 1 (above); any inhabitant of [HasSetsCopowers];
    the rewriting of [GAFT] itself to use the exported step (its lines must
    not move); GAFT as a biconditional; the [Sets_global_points] of the
    issue's Verification block, which names nothing that exists;
    representability at any target but [Sets]; a witness at any category
    but [Sets]; naturality of [homafter_one_iso] in [K], or functoriality
    of any construction here; no edit to Functor/Representable.v,
    Theory/Universal/Element.v, Construction/Elements.v,
    Functor/Hom/Continuous.v, Adjunction/SAFT.v,
    Adjunction/Representability.v, Instance/Sets/Complete.v or
    Adjunction/GAFT/Sets.v, and none to Adjunction/GAFT.v above its last
    line. *)

Section Definition3.

Context {C : Category}.
Context (K : C ⟶ Sets).

(** ** Mac Lane §V.6 Definition 3: the solution set condition, element-wise

    A set of objects and ELEMENTS through which every element factors.  This
    is Definition 3 as the book states it; [SolutionSet] of Adjunction/GAFT.v
    is the hom-shaped form, and the two agree at the singleton set. *)

Record ElementSolutionSet := {
  esol_index : Type;
  esol_obj : esol_index → C;
  esol_elem : ∀ i, K (esol_obj i);
  esol_covers {c : C} (x : K c) :
    { i : esol_index & { t : esol_obj i ~{C}~> c
                       & fmap[K] t (esol_elem i) ≈ x } }
}.

(** ** The two forms agree at the singleton

    Elements of [K c] are global points [1 ~> K c] — Theory/Universal/
    Element.v's [global_element] and [global_elements_iso], which already
    exist; nothing here re-proves that bridge. *)

Definition sols_of_esols (E : ElementSolutionSet) : SolutionSet K SetsOne.
Proof.
  unshelve refine
    {| sol_index := esol_index E
     ; sol_obj := esol_obj E
     ; sol_arr := fun i => global_element (esol_elem E i) |}.
  intros c h.
  destruct (esol_covers E (h ttt)) as [i [t e]].
  exists i, t.
  intro u; destruct u; exact e.
Defined.

Definition esols_of_sols (S : SolutionSet K SetsOne) : ElementSolutionSet.
Proof.
  unshelve refine
    {| esol_index := sol_index S
     ; esol_obj := sol_obj S
     ; esol_elem := fun i => sol_arr S i ttt |}.
  intros c x.
  destruct (sol_covers S (global_element x)) as [i [t e]].
  exists i, t.
  exact (e ttt).
Defined.

(* Both passages keep the index and the objects on the nose. *)
Example sols_of_esols_index (E : ElementSolutionSet) :
  sol_index (sols_of_esols E) = esol_index E := eq_refl.

Example sols_of_esols_obj (E : ElementSolutionSet) (i : esol_index E) :
  sol_obj (sols_of_esols E) i = esol_obj E i := eq_refl.

Example esols_of_sols_index (S : SolutionSet K SetsOne) :
  esol_index (esols_of_sols S) = sol_index S := eq_refl.

Example esols_of_sols_elem (S : SolutionSet K SetsOne) (i : sol_index S) :
  esol_elem (esols_of_sols S) i = sol_arr S i ttt := eq_refl.

(** ** A representation out of an initial object of the elements comma *)

Definition representable_of_comma_initial (I : @Initial (=(SetsOne) ↓ K)) :
  Representable K :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement
       (AUniversalElement_of_AUniversalArrow K _
          (aua_of_ua (Build_UniversalArrow SetsOne K I)))).

End Definition3.

Arguments ElementSolutionSet {C} K.
Arguments esol_index {C K} _.
Arguments esol_obj {C K} _ _.
Arguments esol_elem {C K} _ _.

(** ** Mac Lane §V.6 Theorem 3

    Stated at top level: [comma_initial_of_sols] pins the hom AND proof
    universes of both categories to [Set] (GAFT's own pin), and inside a
    section that has already elaborated [Sets] the ascription is refused. *)

Definition representability_theorem {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) (cont : @PreservesImageLimit C Sets K)
  (E : ElementSolutionSet K) : Representable K :=
  representable_of_comma_initial K
    (comma_initial_of_sols K SetsOne comp cont (sols_of_esols K E)).

(** ** Transport of a representation along a natural isomorphism *)

Definition Representable_transport {C : Category} {F G : C ⟶ Sets}
  (i : F ≅[[C, Sets]] G) (R : Representable F) : Representable G :=
  {| repr_obj := @repr_obj C F R
   ; represented := iso_compose i (@represented C F R) |}.

Example Representable_transport_obj {C : Category} {F G : C ⟶ Sets}
  (i : F ≅[[C, Sets]] G) (R : Representable F) :
  @repr_obj C G (Representable_transport i R) = @repr_obj C F R := eq_refl.

(** ** §V.8 Exercise 1, forward: a left adjoint makes the functor representable

    [HomAfter K 1] IS [Hom(1,−) ◯ K] on the nose, and global points make it
    [K] itself, so #348's [adj_representable] at the singleton transports
    onto [K]. *)

Section Ex81.

Context {C : Category}.
Context (K : C ⟶ Sets).

Example homafter_one_is_composite :
  HomAfter K SetsOne = Compose (fobj[Curried_Hom Sets] SetsOne) K := eq_refl.

#[local] Obligation Tactic :=
  simpl; intros;
  repeat match goal with [ H : poly_unit |- _ ] => destruct H end;
  try (srewrite (@fmap_id _ _ K); reflexivity); try reflexivity.

Program Definition homafter_one_iso : HomAfter K SetsOne ≅[[C, Sets]] K := {|
  to   := {| transform := fun c => global_elements_to (K c) |};
  from := {| transform := fun c => global_elements_from (K c) |}
|}.

Definition representable_of_left_adjoint {L : Sets ⟶ C} (A : L ⊣ K) :
  Representable K :=
  Representable_transport homafter_one_iso (adj_representable A SetsOne).

(* The representing object is the left adjoint at the singleton. *)
Example representable_of_left_adjoint_obj {L : Sets ⟶ C} (A : L ⊣ K) :
  @repr_obj C K (representable_of_left_adjoint A) = L SetsOne := eq_refl.

End Ex81.

(** ** The converse leg: a representable functor is continuous *)

Definition continuous_of_representable {C : Category} {K : C ⟶ Sets}
  (R : Representable K) : ContinuousFunctor K :=
  representable_iso_ContinuousFunctor (@repr_obj C K R)
    (iso_equiv (@represented C K R)).

Definition preserves_image_of_representable {C : Category} {K : C ⟶ Sets}
  (R : Representable K) : @PreservesImageLimit C Sets K :=
  Continuous_PreservesImageLimit (continuous_of_representable R).

(** ** Theorem 3 as a biconditional

    A representation supplies its own element-wise solution set: the single
    object is the representing one and the single element is the identity
    read across the isomorphism. *)

Theorem representability_iff {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) :
  (@PreservesImageLimit C Sets K * ElementSolutionSet K)%type
    ↔ Representable K.
Proof.
  split.
  - intros [cont E]; exact (representability_theorem K comp cont E).
  - intro R.
    split.
    + exact (preserves_image_of_representable R).
    + unshelve refine {| esol_index := poly_unit
                       ; esol_obj := fun _ => @repr_obj C K R
                       ; esol_elem := fun _ =>
                           transform[to (@represented C K R)]
                             (@repr_obj C K R) id |}.
      intros c x.
      exists ttt.
      exists (transform[from (@represented C K R)] c x).
      pose proof (@naturality _ _ _ _ (to (@represented C K R))
                    (@repr_obj C K R) c
                    (transform[from (@represented C K R)] c x) id) as N.
      simpl in N.
      rewrite id_right in N.
      rewrite N.
      pose proof (iso_to_from (@represented C K R) c x) as HH;
        simpl in HH; rewrite HH; srewrite (@fmap_id _ _ K c); reflexivity.
Defined.

Example representability_iff_fst {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) (cont : @PreservesImageLimit C Sets K)
  (E : ElementSolutionSet K) :
  fst (representability_iff K comp) (cont, E)
    = representability_theorem K comp cont E := eq_refl.

(** ** Riehl 4.7.14: SAFT's hypotheses give representability *)

Definition saft_representable {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) (cont : @PreservesImageLimit C Sets K)
  (G : Cogenerator C) (WP : ∀ x : C, SubobjectIndex x)
  (cover : SubobjectCover K comp G WP) : Representable K :=
  representable_of_left_adjoint K (projT2 (SAFT K comp cont G WP cover)).

(** ** §V.8 Exercise 1, converse: copowers give the left adjoint

    The tree's copowers (Structure/Limit/Power.v, #366) are indexed by a
    bare [Type] and so yield plain functions out of the index, where a
    [Sets]-valued adjunction needs setoid morphisms respecting [≈]; a
    setoid-indexed copower is not in the tree.  [HasSetsCopowers] is that
    missing structure, stated exactly as the representability #348's
    biconditional consumes it — so the converse lands as an axiom-free
    CONDITIONAL, and the condition is, by that same biconditional, "the
    represented functor has a left adjoint". *)

Definition HasSetsCopowers (C : Category) : Type :=
  ∀ (b : C) (X : Sets),
    Representable (HomAfter (fobj[@Curried_Hom C] b) X).

Section Ex81Converse.

Context {C : Category}.
Context {K : C ⟶ Sets}.
Context (R : Representable K).

#[local] Notation r := (@repr_obj C K R).

(* Whiskering [K ≅ [Hom r,−)] by [Hom_Sets(X,−)]. *)
#[local] Obligation Tactic := idtac.

Program Definition homafter_whisker (X : Sets) :
  HomAfter K X ≅[[C, Sets]] HomAfter (fobj[@Curried_Hom C] r) X := {|
  to   := {| transform := fun c =>
    {| morphism := fun f => transform[from (@represented C K R)] c ∘ f |} |};
  from := {| transform := fun c =>
    {| morphism := fun f => transform[to (@represented C K R)] c ∘ f |} |}
|}.
Next Obligation. intros X c u v Huv z; simpl; now rewrite (Huv z). Qed.
Next Obligation.
  intros X x y f u z; simpl.
  exact (@naturality _ _ _ _ (from (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X x y f u z; simpl.
  symmetry.
  exact (@naturality _ _ _ _ (from (@represented C K R)) x y f (u z)).
Qed.
Next Obligation. intros X c u v Huv z; simpl; now rewrite (Huv z). Qed.
Next Obligation.
  intros X x y f u z; simpl.
  exact (@naturality _ _ _ _ (to (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X x y f u z; simpl.
  symmetry.
  exact (@naturality _ _ _ _ (to (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X c u z; simpl.
  pose proof (iso_from_to (@represented C K R) c (u z)) as HH;
    simpl in HH; rewrite HH; now rewrite id_left.
Qed.
Next Obligation.
  intros X c u z; simpl.
  pose proof (iso_to_from (@represented C K R) c (u z)) as HH;
    simpl in HH; rewrite HH; srewrite (@fmap_id _ _ K c); reflexivity.
Qed.

Definition left_adjoint_of_representable_Sets (cop : HasSetsCopowers C) :
  { L : Sets ⟶ C & L ⊣ K } :=
  fst (adjunction_iff_pointwise_representable K)
      (fun X => Representable_transport
                  (iso_sym (homafter_whisker X)) (cop r X)).

End Ex81Converse.

(** ** Witnesses at Sets

    Two functors, each with every premise discharged in tree. *)

(** *** The points functor [Hom(1,−)] on Sets *)

Definition Sets_points : Sets ⟶ Sets := @HomFrom Sets SetsOne.

Definition Sets_points_esol : ElementSolutionSet Sets_points.
Proof.
  unshelve refine
    {| esol_index := poly_unit
     ; esol_obj := fun _ => SetsOne
     ; esol_elem := fun _ =>
         (@id Sets SetsOne : carrier (fobj[Sets_points] SetsOne)) |}.
  intros c x.
  exists ttt, x.
  simpl; intro u; destruct u; simpl.
  reflexivity.
Defined.

(* The single member is the singleton itself, and the single element is its
   identity — which is what keeps [Sets_points_esol] transparent. *)
Example Sets_points_esol_obj (u : esol_index Sets_points_esol) :
  esol_obj Sets_points_esol u = SetsOne := eq_refl.

Definition Sets_points_cont : @PreservesImageLimit Sets Sets Sets_points :=
  Continuous_PreservesImageLimit (hom_ContinuousFunctor SetsOne).

Definition Sets_points_repr : Representable Sets_points :=
  representability_theorem Sets_points Sets_Complete Sets_points_cont
    Sets_points_esol.

(* The object the theorem produces represents the same functor as the
   singleton does, so the two agree up to the canonical isomorphism. *)
Definition Sets_points_iso :
  @repr_obj Sets Sets_points Sets_points_repr ≅ SetsOne :=
  repr_unique_iso (Hom_Representable SetsOne) Sets_points_repr.

(** *** The identity functor on Sets, both routes *)

Definition Sets_Id_esol : ElementSolutionSet (@Id Sets) :=
  esols_of_sols (@Id Sets) (Sets_Id_SolutionSet SetsOne).

Definition Sets_Id_repr : Representable (@Id Sets) :=
  representability_theorem (@Id Sets) Sets_Complete
    Sets_Id_PreservesImageLimit Sets_Id_esol.

Definition Sets_Id_repr_iso :
  @repr_obj Sets (@Id Sets) Sets_Id_repr ≅ SetsOne :=
  repr_unique_iso (Representable_transport global_elements_natural
                     (Hom_Representable SetsOne)) Sets_Id_repr.

(* And by Exercise V.8.1's forward direction, from GAFT's own adjunction. *)
Definition Sets_Id_repr_of_adjoint : Representable (@Id Sets) :=
  representable_of_left_adjoint (@Id Sets) (projT2 GAFT_at_Sets_Id).

Example Sets_Id_repr_of_adjoint_obj :
  @repr_obj Sets (@Id Sets) Sets_Id_repr_of_adjoint
    = projT1 GAFT_at_Sets_Id SetsOne := eq_refl.
