Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Absolute.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Lift.

Generalizable All Variables.

(** * Absolute coequalizers *)

(* Book:   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
           §VI.6 "Split Coequalizers", book p. 149 (PDF p. 158), item
           maclane:VI.6:def2, read from the page image
   Paper:  Paré, "On absolute colimits", J. Algebra 19 (1971) 80-95
   nLab:   https://ncatlab.org/nlab/show/absolute+colimit
   nLab:   https://ncatlab.org/nlab/show/split+coequalizer

   WHAT THE BOOK SAYS.  "An arrow e is called an absolute coequalizer of
   ∂₀ and ∂₁ in C if for any functor T: C → X (to any category X
   whatever) the resulting fork Ta ⇉ Tb → Tc still has Te a coequalizer
   (of T∂₀ and T∂₁).  In particular, an absolute coequalizer is
   automatically a coequalizer."  A split fork adds s : c → b and
   t : b → a with e∂₀ = e∂₁, es = 1, ∂₀t = 1 and ∂₁t = se, and the
   Lemma: "In every split fork, e is the coequalizer of ∂₀ and ∂₁", by
   f' = fs, unique since f = ke gives fs = kes = k.

   WHAT IS HERE.
     - [AbsoluteCoequalizer f g q e]: for every category X and functor
       T : C ⟶ X, [IsCoequalizer (fmap[T] f) (fmap[T] g) (T q)
       (fmap[T] e)].  Mac Lane's definition over the tree's elementary
       [IsCoequalizer] (Structure/Coequalizer.v), the form the tree
       consumes: before #477, 27 files outside doc/ and Test/ name it
       (git grep -lw), Monad/Monadicity's Beck.v, BeckObjects.v and
       Crude.v among them, against 2 that name the bundled
       [Coequalizer (APair f g)].  Like the
       issue's statement it quantifies only; Mac Lane's presupposed fork
       is the [cofork] field of the T := Id instance.
     - [AbsoluteCoequalizer_IsCoequalizer]: "automatically a
       coequalizer", the instance T := Id, whose type is
       [IsCoequalizer f g q e] by conversion.
     - The instances are ordered: through Construction/Lift.v's
       [LiftCat], which re-reads a category at higher universe levels,
       an instance at target levels (yo, yh) implies the instance at
       every (xo, xh) below them ([AbsoluteCoequalizer_down]), and an
       instance at any levels at or above C's own is a coequalizer in C,
       its cofork included ([AbsoluteCoequalizer_IsCoequalizer_up]), so
       "automatically a coequalizer" holds from every such instance.
     - Mac Lane's Lemma is Structure/Coequalizer/Split.v's
       [split_coequalizer_is_coequalizer], whose proof is the book's:
       the descent is h ∘ s, and e ∘ s ≈ id makes it unique (Split.v's
       laws are Mac Lane's (3) with f, g for ∂₀, ∂₁).
       [split_coequalizer_absolute]: every split fork is absolute,
       Split.v's [split_coequalizer_preserved] read as the predicate.
     - The image bridge, per functor: [image_coequalizer_colimit] and
       [image_colimit_coequalizer] turn an elementary coequalizer of the
       image pair into a colimiting image cocone over [T ◯ APair f g]
       and back.  Both are Structure/Coequalizer.v's diagram-general
       conversions ([parallel_coequalizer_colimit],
       [parallel_colimit_coequalizer], #477) at [K := T ◯ APair f g]:
       the second by conversion, the first through a cone isomorphism
       whose apex map is the identity.  The tree records three times
       (Monad/Monadicity/Crude.v, Monad/Eilenberg/Moore/Limit.v,
       Adjunction/Continuity/Equalizer.v) that [T ◯ APair f g] is not
       identified with [APair (fmap[T] f) (fmap[T] g)]; the general
       conversions make that identification unnecessary on the
       coequalizer side, by case analysis on the two objects of
       [Parallel], and Continuity/Equalizer.v's equalizer side is not
       met.
     - The agreement: for a cofork [H : e ∘ f ≈ e ∘ g],
       [AbsoluteCoequalizer_AbsoluteColimitCocone] and
       [AbsoluteColimitCocone_AbsoluteCoequalizer] carry the predicate
       to Structure/Limit/Absolute.v's [AbsoluteColimitCocone] of the
       cofork cocone [cofork_cocone f g e H] and back, so the absolute
       coequalizer IS the cofork-shaped absolute colimit, instance by
       instance at the cocone side's hom level (UNIVERSES).
     - Split forks at cone level: [split_cofork_AbsoluteColimitCocone],
       and [split_coequalizer_PreservesColimitCocone]: every functor
       preserves, in the cone sense, EVERY coequalizer of a pair that
       has a split coequalizer, not just the given one.

   STRENGTHS.  The image cocone's injections are [fmap[T] (e ∘ f)] over
   [ParX] and [fmap[T] e] over [ParY] at [eq_refl]
   ([image_cofork_inj_ParX], [image_cofork_inj_ParY]); over [ParX] it is
   not [fmap[T] e ∘ fmap[T] f] at [eq_refl] (refused in the probe), which
   is the [fmap_comp] step of [image_coequalizer_colimit]'s cone
   isomorphism.  The descent built by [image_colimit_coequalizer] IS the
   colimit's mediator at the cofork cocone of the coforking map
   ([image_colimit_coequalizer_desc], [eq_refl]).  The three [Example]s
   are restated in the probe.

   UNIVERSES, by [About] on every constant.  [AbsoluteCoequalizer@{co ch
   xo xh u}] is over [C : Category@{co ch ch}] and quantifies over
   [X : Category@{xo xh xh}] with "ch <= xh" and no equation: every
   target whose hom level is at or above C's, a universe-polymorphic
   family with the predicate's sort [u] strictly above [xo] and [xh].
   That is as general as [Functor] allows in the hom level; the target's
   proof level is its hom level, as [IsCoequalizer@{u u0}], over
   [Category@{u u0 u0}], requires, where [Functor] would allow it above.
   It is more general than the cone-level predicate, whose targets share
   C's hom level by three carriers that Structure/Limit/Absolute.v
   names: Preservation.v's [cone_leg] and [IsLimitCone], [Compose], and
   for cocones [Opposite_Functor].
     Two consequences were measured.  First, Split.v's
   [functor_preserves_split] and [split_coequalizer_preserved] read
   [@{u u0 u1 u2}] over [C : Category@{u1 u2 u2}] and
   [D : Category@{u u2 u2}], one hom level for both, so absoluteness of
   a split fork reached only targets at C's hom level; the same proofs
   compile with the target's hom level strictly above, and #477 writes
   their binders out ([@{co ch do dh u}], "ch <= dh").  Second, with
   that done, [split_coequalizer_absolute] still came out at
   [AbsoluteCoequalizer@{co ch u0 ch u}]: minimization set the target
   hom level, bounded below by [ch] alone, to [ch].  So its statement
   names the instance, [AbsoluteCoequalizer@{co ch xo xh _}]; it now
   reads "ch <= xh", and the probe accepts it with "ch < xh" strict.
   [AbsoluteCoequalizer_IsCoequalizer_up@{co ch xo xh u}] carries
   "co <= xo" and "ch <= xh", and
   [AbsoluteCoequalizer_down@{co ch xo xh yo yh …}] "xo <= yo" and
   "xh <= yh", with no equation, and their statements name the instances
   they consume and produce for the same reason: four explicit universe
   instances of a new constant in this file, in three constants.
   [AbsoluteCoequalizer_IsCoequalizer] consumes the instance
   [@{co ch co ch u}], X at C's own levels: "take T := Id".  The probe
   refuses it from a target hom level above C's at C's own object level
   (R6), a pin of that lemma's signature and not of what the predicate
   yields: R6's statement is accepted through
   [AbsoluteCoequalizer_IsCoequalizer_up] (C26) and through
   [AbsoluteCoequalizer_down] (C27).  The agreement lemmas pair
   [AbsoluteCoequalizer@{co ch u ch u0}] with the cocone predicate at
   the same target object level [u]: at a target hom level above C's the
   cone-level side does not exist, and through
   [AbsoluteCoequalizer_down] any elementary instance at or above
   (u, ch) feeds them.  They take the cofork [H] as an argument because
   their target object level [u] is unrelated to C's and may lie below
   it, where no instance returns the cofork; at or above C's levels
   [AbsoluteCoequalizer_IsCoequalizer_up] does.

   STALE PREMISES, dated from gh.  The issue (filed 2026-07-23, Riehl's
   box appended 2026-07-31) says that a grep for [Absolute*] declarations
   returns nothing and that no [Absolute*] identifier exists: accurate
   when written, stale since PR #1229 (merged 2026-08-31, for #356),
   whose Structure/Limit/Constant.v declares the apex-only
   [AbsoluteLimit] and [AbsoluteColimit].  Its optional [AbsoluteColimit]
   is delivered at cone level as [AbsoluteColimitCocone], those names
   being taken.  Its line citations are replaced by names here.  "Beck's
   condition (ii) cannot be phrased" was accurate until this change; it
   can now be phrased, and issue #484 (open) is to phrase it.

   NOT DELIVERED.  An elementary [AbsoluteEqualizer]: the limit side is
   [AbsoluteLimitCone] at the walking parallel pair, and Mac Lane names
   only the coequalizer.  The equalizer twin of Structure/Coequalizer.v's
   diagram-general conversions.  Paré's converse direction (an absolute
   coequalizer is split in his generalized sense).  A concrete absolute
   coequalizer that is not split, and a concrete coequalizer that is not
   absolute (the non-vacuity witnesses of Structure/Limit/Absolute.v are
   of the empty shape).  Beck's theorem with the absolute condition
   (issue #484) and Riehl's split idempotents (issue #957). *)

(** ** The predicate, and Mac Lane's two remarks *)

Definition AbsoluteCoequalizer@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} (f g : x ~> y) (q : C) (e : y ~> q) :
  Type :=
  ∀ (X : Category@{xo xh xh}) (T : C ⟶ X),
    IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e).

Definition AbsoluteCoequalizer_IsCoequalizer@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer f g q e) : IsCoequalizer f g q e :=
  A C Id.

(* The instance is named: left to Rocq, minimization sets the target's
   hom level [xh] to [ch], its only lower bound. *)

Definition split_coequalizer_absolute@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) :
  AbsoluteCoequalizer@{co ch xo xh _} f g (scoeq_obj S) (scoeq_e S) :=
  fun X T => split_coequalizer_preserved T f g S.

(** ** Every instance at or above C's levels: the lift *)

(* An absolute coequalizer at ANY target level at or above C's is a
   coequalizer in C, its cofork included: C is read at that level by
   Construction/Lift.v's [LiftCat], and [Lift_in C] plays the part of
   [Id].  The instance of the hypothesis is named, its target levels
   being bounded below by C's alone. *)

Definition AbsoluteCoequalizer_IsCoequalizer_up@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer@{co ch xo xh _} f g q e) :
  IsCoequalizer f g q e.
Proof.
  pose (E := A (LiftCat C) (Lift_in C)).
  unshelve econstructor.
  - exact (cofork E).
  - intros z h Hh.
    pose (U := coeq_desc E (z := z) h Hh).
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + exact (unique_property U).
    + intros v Hv. exact (uniqueness U v Hv).
Defined.

(* Each instance implies every lower one: a target X below the
   hypothesis' levels is read at them, and [Lift_after T] replaces T. *)

Definition AbsoluteCoequalizer_down@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer@{co ch yo yh _} f g q e) :
  AbsoluteCoequalizer@{co ch xo xh _} f g q e.
Proof.
  intros X T.
  pose (E := A (LiftCat X) (Lift_after T)).
  unshelve econstructor.
  - exact (cofork E).
  - intros z h Hh.
    pose (U := coeq_desc E (z := z) h Hh).
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + exact (unique_property U).
    + intros v Hv. exact (uniqueness U v Hv).
Defined.

(** ** The image of a cofork: elementary and cocone-level readings agree *)

Example image_cofork_inj_ParX@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g) :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParX = fmap[T] (e ∘ f)
  := eq_refl.

Example image_cofork_inj_ParY@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g) :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParY = fmap[T] e
  := eq_refl.

(* Both directions are Structure/Coequalizer.v's diagram-general
   conversions at [K := T ◯ APair f g], whose pair is [fmap[T] f] and
   [fmap[T] g] by conversion.  Over [ParX] the cofork cocone of the image
   pair has the injection [fmap[T] e ∘ fmap[T] f] and the image cocone
   [fmap[T] (e ∘ f)], equal at ≈ by [fmap_comp]; so the first direction
   transports along a cone isomorphism whose apex map is the identity,
   and the second is the conversion itself. *)

Definition image_coequalizer_colimit@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (E : IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e)) :
  IsColimitCocone (FCocone T (cofork_cocone f g e H)).
Proof.
  refine (limitcone_transport _
            (parallel_coequalizer_colimit (T ◯ APair f g) E)).
  exists (@iso_id (X^op) (T q)).
  intro p; destruct p; simpl.
  - rewrite id_left.
    exact (fmap_comp e f).
  - apply id_left.
Defined.

Definition image_colimit_coequalizer@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (HC : IsColimitCocone (FCocone T (cofork_cocone f g e H))) :
  IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e) :=
  parallel_colimit_coequalizer (T ◯ APair f g) _ HC.

Example image_colimit_coequalizer_desc@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (HC : IsColimitCocone (FCocone T (cofork_cocone f g e H)))
  {z : X} (h : T y ~{X}~> z) (Hh : h ∘ fmap[T] f ≈ h ∘ fmap[T] g) :
  unique_obj (coeq_desc (image_colimit_coequalizer T H HC) h Hh)
    = unique_obj (HC (parallel_cofork_cocone (T ◯ APair f g) h Hh))
  := eq_refl.

(** ** The absolute coequalizer is the cofork-shaped absolute colimit *)


Definition AbsoluteCoequalizer_AbsoluteColimitCocone@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (H : e ∘ f ≈ e ∘ g) (A : AbsoluteCoequalizer f g q e) :
  AbsoluteColimitCocone (cofork_cocone f g e H) :=
  fun D T => image_coequalizer_colimit T H (A D T).

Definition AbsoluteColimitCocone_AbsoluteCoequalizer@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (H : e ∘ f ≈ e ∘ g) (A : AbsoluteColimitCocone (cofork_cocone f g e H)) :
  AbsoluteCoequalizer f g q e :=
  fun D T => image_colimit_coequalizer T H (A D T).

(** ** Split coequalizers, at cone level *)

Definition split_cofork_AbsoluteColimitCocone@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) :
  AbsoluteColimitCocone (cofork_cocone f g (scoeq_e S) (scoeq_law1 S)) :=
  AbsoluteCoequalizer_AbsoluteColimitCocone (scoeq_law1 S)
    (split_coequalizer_absolute S).

(* The cofork cocone of a split fork is colimiting by Mac Lane's Lemma,
   through Structure/Coequalizer.v's [is_coequalizer_cocone_ump]. *)

Definition split_coequalizer_PreservesColimitCocone@{co ch do +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) (D : Category@{do ch ch}) (F : C ⟶ D) :
  PreservesColimitCocone (APair f g) F :=
  AbsoluteColimitCocone_preserves
    ((fun N => is_coequalizer_cocone_ump f g
                 (split_coequalizer_is_coequalizer f g S) N)
       : IsColimitCocone (cofork_cocone f g (scoeq_e S) (scoeq_law1 S)))
    (split_cofork_AbsoluteColimitCocone S) D F.
