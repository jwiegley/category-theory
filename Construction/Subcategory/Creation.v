(** * Full subcategories closed under limits are created into

    A full subcategory whose objects are closed under the limits of the
    ambient category inherits those limits, and its inclusion CREATES them
    in Mac Lane's sense (§V.1, the definition Structure/Limit/Creation.v
    carries as [CreatesLimit]): every limiting cone in the ambient category
    over a diagram of subcategory objects lifts, uniquely up to the
    canonical isomorphism, to a limiting cone in the subcategory.  This is
    the elementary half of the folklore that a limit-closed full
    subcategory is "as complete as its ambient category" (nLab:
    https://ncatlab.org/nlab/show/created+limit, and Mac Lane §V.4
    Theorem 2 for the passage from creation to completeness).  Until
    this file the tree's only route from a subcategory to [CreatesLimit]
    went through reflectivity (Construction/Reflective/Limit.v:494,
    [reflective_CreatesLimit]); closure under limits is the weaker and
    more common hypothesis, and it is the one Instance/Top/CompHaus.v
    needs to STATE the compact-Hausdorff creation question without a
    reflector.

    WHAT IS DELIVERED.  Over [C : Category], [S : Subcategory C] with
    [full : Full C S]:
    - [ClosedUnderLimits S : Type], the hypothesis: for every shape [J],
      diagram [K : J ⟶ Sub C S] and cone [N] over [Incl C S ◯ K] that is
      limiting in [C], the apex [vertex_obj[N]] satisfies [sobj S].  No
      clause about legs is needed: [S] is full, so every arrow of [C]
      between [S]-objects is an [S]-arrow.
    - [sub_lift N HN : Cone K], the lifted cone — the SAME apex and the
      SAME legs, packaged with the closure and fullness witnesses; both
      read back at [eq_refl] ([sub_lift_apex], [sub_lift_leg]).
    - [sub_cone_iso N HN : ConeIso (FCone (Incl C S) (sub_lift N HN)) N],
      the comparison, which is the IDENTITY isomorphism.
    - [sub_ReflectsLimitCone K : ReflectsLimitCone K (Incl C S)], from
      Theory/Equivalence/Limit.v's [ff_reflect_ump]: the inclusion is full
      ([Full_Implies_Full_Functor]) and faithful ([Incl_Faithful]), and
      fully faithful functors reflect limits — the same route
      Construction/Reflective/Limit.v takes at :484-487.
    - [sub_CreatesLimit K : CreatesLimit K (Incl C S)], the three fields
      above; [sub_CreatesAllLimits : CreatesAllLimits (Incl C S)]; and
      [sub_Complete : Complete C → Complete (Sub C S)] through
      Structure/Limit/Creation.v's [creates_limits_Complete] (Mac Lane
      §V.4 Theorem 2, second half).

    HYPOTHESES SPENT.  [full] enters the lift's legs and the reflection;
    [closed] enters the lift's apex only.  Nothing is registered as an
    [Instance], following Structure/Limit/Creation.v:125-128's discipline
    that creation witnesses are passed explicitly.

    UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK OVER ALL 9 CONSTANTS. ZERO
    word-bounded [Set]. [ClosedUnderLimits@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9} :
    ∀ {C : Category@{u u0 u0}}, Subcategory@{u u0 u1 u2} C → Type@{u4}] carries
    no equation, nor do [sub_CreatesAllLimits] and [sub_Complete]. [sub_lift],
    [sub_lift_apex], [sub_lift_leg], [sub_cone_iso] and [sub_CreatesLimit] each
carry FIVE block equations: [u0 = u11] identifies the ambient hom universe
    with the shape's — Structure/Limit/Preservation.v's [IsLimitCone] pin,
    inherited — and [u0 = u13] with [Sub]'s, imposed by [Compose] in [Incl C S
    ◯ K] ([Compose] types its three categories at one hom universe; an audit
    isolated the two causes with two probes), and [u5 = u12], [u6 = u14], [u9 =
    u10] identify the closure hypothesis' quantified shape and [Sub] levels
    with the diagram's, so the hypothesis is consumed at the diagram's own
    universe instance; [sub_ReflectsLimitCone] carries the first two only.
    [sub_CreatesLimit@{u … u17} : ∀ {C : Category@{u u0 u0}} (S :
    Subcategory@{u u0 u1 u2} C), Full C S → ClosedUnderLimits S → ∀ {J :
    Category@{u10 u11 u11}} (K : J ⟶ Sub C S), CreatesLimit@{u6 u7 u u15 u8 u10
    u11 u12} K (Incl C S)].

    COUNTS. 9/9 constants (7 [Definition], 2 [Example]) closed under the global
    context with ZERO [Axioms:] lines, all in the [make print-assumptions] gate
    FULLY QUALIFIED; no [Program]. Two [Defined]-terminated proofs:
    [sub_lift]'s flip to [Qed] breaks this file at its own readback
    [sub_lift_apex] (load-bearing); [sub_cone_iso]'s flip leaves this file,
    Instance/Top/CompHaus.v and Test/ProbeCompHaus413.v green and it is kept
    [Defined] by the data convention. Closure 35 modules excluding self —
    Theory/Equivalence/Limit.v costs 10 at the margin,
    Structure/Limit/Creation.v 3, Construction/Subcategory.v 1, each of the
    other eight [Category.*] [Require]s 0 (eleven in all, each dropped alone).
    Zero collisions over the 9 names. Pinned and read back at [eq_refl] by
    Test/ProbeCompHaus413.v: the lift's apex and legs.

    NOT DELIVERED.  The non-full case (a [Subcategory] whose [shom] is
    not everything: the lift's legs would need an [shom] witness the
    closure hypothesis does not provide); the converse (that a full
    subcategory whose inclusion creates limits is closed under them — true
    by [creates_lift], but not stated); strict creation
    ([StrictlyCreatesLimit]); the colimit dual; any witness of
    [ClosedUnderLimits] at a concrete subcategory (Instance/Top/CompHaus.v
    applies the lemma as a CONDITIONAL, [Top] having no limits beyond the
    terminal object to be closed under); and any relation to
    reflectivity (a reflective subcategory is closed under limits, but that
    implication is not proved here). *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * A full subcategory closed under limits is created into by its inclusion *)

Section SubcategoryCreation.

Context {C : Category} (S : Subcategory C) (full : Full C S).

(* Closure under limits: the apex of any limiting cone in [C] over a diagram
   of [S]-objects is again an [S]-object.  The legs need no clause because
   [S] is full. *)
Definition ClosedUnderLimits : Type :=
  ∀ (J : Category) (K : J ⟶ Sub C S) (N : Cone (Incl C S ◯ K)),
    IsLimitCone N → sobj C S (vertex_obj[N]).

Context (closed : ClosedUnderLimits).

Section AtDiagram.
Context {J : Category} (K : J ⟶ Sub C S).

(* The lift: the same apex and the same legs, now inside [Sub C S]. *)
Definition sub_lift (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) : Cone K.
Proof using C J K S closed full.
  unshelve refine
    (@Build_Cone J (Sub C S) K (vertex_obj[N]; closed J K N HN)
       (@Build_ACone J (Sub C S) (vertex_obj[N]; closed J K N HN) K
          (fun x => (cone_leg N x; full _ _ _ _ (cone_leg N x))) _)).
  intros x y f; simpl.
  exact (@cone_coherence J C (vertex_obj[N]) (Incl C S ◯ K) coneFrom x y f).
Defined.

Example sub_lift_apex (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) :
  (`1 vertex_obj[sub_lift N HN]) = vertex_obj[N] := eq_refl.

Example sub_lift_leg (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) (x : J) :
  (`1 (cone_leg (sub_lift N HN) x)) = cone_leg N x := eq_refl.

(* The image of the lift is [N] itself, up to the identity isomorphism. *)
Definition sub_cone_iso (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) :
  ConeIso (FCone (Incl C S) (sub_lift N HN)) N.
Proof using C J K S closed full.
  exists iso_id.
  intro x; simpl. now rewrite id_right.
Defined.

(* Reflection: [Incl C S] is full and faithful. *)
Definition sub_ReflectsLimitCone : ReflectsLimitCone K (Incl C S) :=
  fun M H =>
    @ff_reflect_ump (Sub C S) C (Incl C S)
      (Full_Implies_Full_Functor C S full) (Incl_Faithful C S)
      J K M (limitcone_isalimit H) (fun x => reflexivity _).

Definition sub_CreatesLimit : CreatesLimit K (Incl C S) :=
  {| creates_lift      := sub_lift
   ; creates_lift_over := sub_cone_iso
   ; creates_reflect   := sub_ReflectsLimitCone |}.

End AtDiagram.

Definition sub_CreatesAllLimits : CreatesAllLimits (Incl C S) :=
  fun J K => sub_CreatesLimit K.

(* Mac Lane §V.4 Theorem 2, second half, at a full subcategory closed under
   limits: the subcategory inherits completeness. *)
Definition sub_Complete (HC : @Complete C) : @Complete (Sub C S) :=
  creates_limits_Complete (Incl C S) HC sub_CreatesAllLimits.

End SubcategoryCreation.
