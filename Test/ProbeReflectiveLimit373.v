Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Construction.Reflective.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.TorsionFree.

Generalizable All Variables.

(** * Boundary probe for Construction/Reflective/Limit.v (issue #373) *)

(* Every boundary the target file's header states as measured is pinned
   here, from OUTSIDE that file: an in-file negative renames in lockstep
   with the constant it guards and so cannot detect a rename.  The
   [Require] list above mirrors the target's exactly, plus this file's own
   target and the four modules the concrete witness needs.

   Eight negatives of THREE kinds, kept lexically apart, plus one
   scope-free instrument check:

     CONVERSION  1  the two routes to [PreservesLimitCone K (Incl C S)]
                    are not the same term
     CONVERSION  2  ... nor do their produced mediators agree on the nose
     CONVERSION  3  [reflective_counit_iso]'s forward leg is not the
                    counit on the nose (that lemma is closed with [Qed]
                    while producing data)
     TYPING      4  [CreatesLimit] is not [PreservesLimitCone]
     TYPING      5  [CreatesLimit] is not [StrictlyCreatesLimit]
     FORMABILITY 6  [Subcategory] identifies its category's hom and proof
                    universes
     FORMABILITY 7  [cone_leg] identifies the shape's hom-and-proof level
                    with the ambient category's
     FORMABILITY 8  ... and so does [IsLimitCone], separately

   Negatives 7 and 8 sit on a DIFFERENT axis from negative 6 (two
   categories' levels, rather than one category's hom against its proof),
   and each is testable apart from the others: [Cone F] and [Ju ⟶ Cu] are
   both accepted at the very levels where they are rejected, so neither
   [Cone] nor [Functor] is a donor.

   Each negative was stripped ONE AT A TIME, with the others left as
   [Fail], and the whole error read.  Negatives 4 and 5 report a plain
   "has type ... while it is expected to have type ...", with no "cannot
   unify" clause and no universe clause; negatives 1-3 end in "cannot
   unify"; negative 6 ends in "universe inconsistency: Cannot enforce
   cp = ch because ch < cp", and negatives 7 and 8 in "universe
   inconsistency: Cannot enforce vh = jh because jh < vh".

   Every constant a negative names also appears outside a [Fail], in a
   control below.  The controls were checked by rename simulation: each
   such constant was renamed throughout this file, and the file then
   stopped compiling at a control rather than compiling with a vacuously
   green [Fail]. *)

(** ** Instrument check *)

(* If this command ever succeeds, the [Fail] wrapper is not doing its job
   and every negative below is worthless. *)

Fail Check probe373_no_such_constant_anywhere.

Section Boundaries.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context {J : Category}.
Context (K : J ⟶ Sub C S).

(** ** Controls *)

Check (Subcategory C).
Check (Sub C S).
Check (Incl C S).
Check (reflector R).
Check (reflective_adj R).
Check (reflective_CreatesLimit R K : CreatesLimit K (Incl C S)).
Check (reflective_Incl_PreservesLimitCone R K
         : PreservesLimitCone K (Incl C S)).
Check (fun L : Limit (Incl C S ◯ K) =>
         creation_preserves_limit (reflective_CreatesLimit R K) L).
Check (fun x : Sub C S => to (reflective_counit_iso R x)).
Check (fun x : Sub C S =>
         @counit _ _ (reflector R) (Incl C S) (reflective_adj R) x).
Check (fun (N : Cone K) (H : IsLimitCone N) => unique_obj (H N)).
Check (fun (N : Cone K) (x : J) => cone_leg N x).
Check (fun (N : Cone K) => FCone (Incl C S) N).
Check (@StrictlyCreatesLimit J (Sub C S) C K (Incl C S)).
Check (fun (L : Limit (Incl C S ◯ K)) (M : Cone K) (HM : IsLimitCone M)
           (P : Cone (Incl C S ◯ K)) =>
         reflective_two_routes_agree R K L M HM P).
Check (reflective_inherits_limits R K).
Check (reflective_lift R K).
Check (reflective_CreatesAllLimits R).
Check (reflective_Complete R).

(** ** CONVERSION 1: the two preservation routes are different terms *)

Fail Example probe_two_routes (L : Limit (Incl C S ◯ K)) :
  creation_preserves_limit (reflective_CreatesLimit R K) L
    = reflective_Incl_PreservesLimitCone R K := eq_refl.

(** ** CONVERSION 2: ... and their mediators do not agree on the nose *)

Fail Example probe_two_routes_med (L : Limit (Incl C S ◯ K))
  (M : Cone K) (HM : IsLimitCone M) (P : Cone (Incl C S ◯ K)) :
  unique_obj
    (creation_preserves_limit (reflective_CreatesLimit R K) L M HM P)
    = unique_obj (reflective_Incl_PreservesLimitCone R K M HM P) := eq_refl.

(** ** CONVERSION 3: the counit isomorphism does not reduce *)

(* [reflective_counit_iso] (Construction/Reflective.v:92) produces data
   and is closed with [Qed], so its forward leg does not reduce to the
   counit.  This is a second, independent reason -- beyond the structural
   one recorded in the target's header, that the lemma speaks about an
   object of the subcategory rather than an arbitrary object of C -- why
   it does not shorten the comparison isomorphism. *)

Fail Example probe_counit_iso_leg (x : Sub C S) :
  to (reflective_counit_iso R x)
    = @counit _ _ (reflector R) (Incl C S) (reflective_adj R) x := eq_refl.

(** ** TYPING 4: creation is not preservation *)

Fail Check (reflective_CreatesLimit R K
              : PreservesLimitCone K (Incl C S)).

(** ** TYPING 5: creation is not STRICT creation *)

(* [StrictLift]'s [slift_eq] field (Structure/Limit/Creation.v:288) asks
   for a LEIBNIZ equality of apexes downstairs.  The lift built in the
   target has apex [Incl C S (reflector R L)], which the comparison
   isomorphism relates to L but does not equate to it. *)

Fail Check (reflective_CreatesLimit R K
              : StrictlyCreatesLimit K (Incl C S)).

End Boundaries.

(** ** FORMABILITY 6: [Subcategory] identifies hom with proof *)

(* The target's constants are all over [Category@{u u0 u0}], and the
   identification is inherited rather than introduced: [Subcategory]
   alone already forces it, with the category's own hom-set and identity
   accepted at the very levels where [Subcategory] is rejected.  The
   identification sits in [Subcategory]'s BINDER; its constraint block is
   empty. *)

Section UniverseProbe.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).
Check (@homset Cu xu yu).

Fail Check (Subcategory Cu).

End UniverseProbe.

(** ** FORMABILITY 7 and 8: the cone vocabulary identifies J with C *)

(* The shape-indexed constants of the target additionally carry [u0 = u8],
   collapsing the shape's hom-and-proof level onto the ambient category's.
   That is the cone vocabulary's doing, not the functor's and not the
   [Cone] record's: with the shape's hom level declared strictly BELOW the
   ambient one, the functor type and the [Cone] record are both formable,
   while [cone_leg] and [IsLimitCone] are each rejected on their own.
   These are the same donor family Structure/Limit/Initial.v's header
   (:127-145) records for a RELATED collapse; the axis there is the
   shape's own hom against its own proof, and it names [IsALimit] as a
   third donor.  [IsALimit] is a donor on THIS axis too, as are [Limit],
   [ConeIso] and [FCone], each rejected alone at these levels while
   [vertex_obj] is accepted: measured out of tree and recorded in the
   target's header, NOT pinned here -- the two below are a sample of the
   family, not an enumeration. *)

Section ShapeUniverseProbe.

Universes jo jh jp vo vh vp.
Constraint jh < vh.

Context (Ju : Category@{jo jh jp}).
Context (Vu : Category@{vo vh vp}).

Check (obj[Ju]).
Check (obj[Vu]).
Check (Ju ⟶ Vu).

Context (Fu : Ju ⟶ Vu).

Check (@Cone Ju Vu Fu).
Check (@ACone Ju Vu).

Fail Check (@cone_leg Ju Vu Fu).
Fail Check (@IsLimitCone Ju Vu Fu).

End ShapeUniverseProbe.

(** ** Non-vacuity: the torsion-free abelian groups *)

(* [TorsionFree_Reflective] (Instance/Ab/TorsionFree.v:524) is a full
   reflective subcategory of [Ab], and [Ab] has a terminal object
   ([Ab_Terminal], Instance/Ab.v:244).  The empty diagram therefore has a
   limit downstairs, and Mac Lane's exercise produces one upstairs.

   The limit downstairs is built here rather than taken from
   [Terminal_Limit] (Structure/Limit/Terminal.v:33): that theorem is
   closed with [Qed], so its apex would not reduce and the readbacks below
   would say nothing.  The hand-built version is [Defined], and the
   created apex then reduces all the way to the quotient of the terminal
   abelian group by its torsion subgroup.

   The witness deliberately lives here rather than in the target, so that
   [Instance/Ab] stays out of the target's dependency closure. *)

Definition probe_KAb : 0 ⟶ Sub Ab TorsionFree_Sub :=
  From_0 (Sub Ab TorsionFree_Sub).

Definition probe_ab_cone : Cone (Incl Ab TorsionFree_Sub ◯ probe_KAb).
Proof.
  unshelve refine {| vertex_obj := @terminal_obj Ab Ab_Terminal |}.
  unshelve econstructor; intro x; inversion x.
Defined.

Definition probe_ab_limit : Limit (Incl Ab TorsionFree_Sub ◯ probe_KAb).
Proof.
  unshelve refine {| limit_cone := probe_ab_cone |}.
  intro N.
  unshelve econstructor.
  - exact (@one Ab Ab_Terminal _).
  - intro x; inversion x.
  - intros v Hv; apply (@one_unique Ab Ab_Terminal).
Defined.

Example probe_ab_limit_apex :
  vertex_obj[@limit_cone _ _ _ probe_ab_limit]
    = @terminal_obj Ab Ab_Terminal := eq_refl.

Definition probe_ab_created : Limit probe_KAb :=
  reflective_inherits_limits TorsionFree_Reflective probe_KAb probe_ab_limit.

(* The created cone IS the lift of the cone downstairs ... *)

Example probe_ab_created_cone :
  @limit_cone _ _ _ probe_ab_created
    = reflective_lift TorsionFree_Reflective probe_KAb probe_ab_cone
  := eq_refl.

(* ... its apex IS the reflector applied to the terminal object ... *)

Example probe_ab_created_apex :
  vertex_obj[@limit_cone _ _ _ probe_ab_created]
    = fobj[reflector TorsionFree_Reflective] (@terminal_obj Ab Ab_Terminal)
  := eq_refl.

(* ... and the created apex's carrier is the torsion quotient.  Read that
   at its strength: [torsion_reflector_obj] (Instance/Ab/TorsionFree.v)
   holds at an ARBITRARY object, so this readback pins the definitional
   unfolding of the reflector's object action and not that the reflection
   did anything here -- the terminal group is itself torsion-free, so the
   reflection is inert up to isomorphism, and the shape being [0] means
   every leg condition is exercised at no index at all ([IsLimitCone] at
   the empty shape is terminality).  The witness shows the assembly runs
   end to end and reduces, not that it is non-degenerate. *)

Example probe_ab_created_carrier :
  `1 (vertex_obj[@limit_cone _ _ _ probe_ab_created])
    = AbModTorsion (@terminal_obj Ab Ab_Terminal) := eq_refl.

(* The subcategory is complete as soon as [Ab] is; no completeness
   witness for [Ab] is claimed here, so this is a conditional. *)

Check (reflective_Complete TorsionFree_Reflective).
