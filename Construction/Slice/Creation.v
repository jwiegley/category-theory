Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.

Set Universe Polymorphism.

Generalizable All Variables.

(** * The coslice projection creates limits *)

(* nLab: https://ncatlab.org/nlab/show/over+category#limits_and_colimits
   nLab: https://ncatlab.org/nlab/show/created+limit

   Mac Lane §V.1 Exercise 1 (book p. 112) asks for the coslice case of the
   comma lemma: the projection [c ̸co C ⟶ C] creates every limit [C] has.
   Riehl states the same as the limit half of §3.4 Proposition 8 (printed
   p. 106) and again as §4.7 Lemma 2 (printed p. 174), whose Exercise
   (printed p. 180) asks for the direct argument.

   The comma side of that is Construction/Comma/Creation.v, which needs no
   hypothesis here beyond one this library already supplies: [Id] is a right
   adjoint ([adj_id], Instance/Adjoints.v:70, re-exported as
   [Adjunction_Id], Adjunction/Compose.v:65), and
   [right_adjoint_PreservesImageLimit] (Construction/Comma/Limit.v:266)
   turns any adjunction into the preservation witness.  So
   [@PreservesImageLimit C C Id] is inhabited for EVERY category, with no
   premise at all, and every statement in this file is unconditional in that
   sense — the only hypothesis anywhere below is a [Complete C] where
   completeness is the conclusion's subject.

   What transports and what does not.  [Comma_Coslice] (Construction/Slice.v:182 —
   issue #438 and five in-tree sites cite :181, which is the [#[export]]
   attribute heading that same declaration)
   is an isomorphism [c ̸co C ≅ =(c) ↓ Id] in [Cat], hence an equivalence,
   hence a creator of all limits (Theory/Equivalence/Creation.v), so
   completeness and CreatesLimit both cross over.  STRICT creation does NOT
   cross over: the transported projection [comma_proj2 ◯ Coslice_to_Comma]
   has an object action that does not reduce to the first projection —
   [Comma_Coslice] is a [Program Instance] whose [fobj] is an obligation —
   and there is no [StrictlyCreatesLimit_compose] to compose strictness
   through.  Test/ProbeCommaCreation438.v's negatives n3 and n4 pin both
   halves: the object action is refused against [`1 x], and the coslice is
   not the comma category on the nose.

   That is a fact about the TRANSPORT, not about coslice projections.  An
   earlier revision of this header drew the wrong conclusion from it — that
   a plain unconditioned projection [c ̸co C ⟶ C] would have to be built
   from scratch, all three in-tree coslice projections carrying an extra
   hypothesis on [C].  Measured, that is false for two of the three:
   [Coslice_Proj] (Construction/Slice/Adjunction.v:392) prints as
   [∀ {C : Category} (a : obj[C]), (a ̸co C) ⟶ C] and [Coslice_proj]
   (Instance/Cat/Pullback.v:847) as the same, because the [Cocartesian] and
   [ObjUIP] variables of the sections they sit in are never discharged into
   them — their bodies do not use them.  Only [Coslice_Forget]
   (Construction/Slice/Terminal.v:206) genuinely carries one, an [Initial].
   So the second half of this file does the direct argument for
   [Coslice_Proj] itself, and n6 records that the plain and the transported
   projection are nevertheless different functors, so neither result
   transfers to the other by conversion. *)

(** ** The identity is its own right adjoint, so the comma side is free *)

Definition Id_PreservesImageLimit {C : Category} : @PreservesImageLimit C C Id
  := right_adjoint_PreservesImageLimit (@Adjunction_Id C).

Section CosliceComma.

Context {C : Category}.
Context (c : C).

(* Strict creation for the coslice READ AS A COMMA.  Here the projection is
   [comma_proj2] itself, so the strictness of Construction/Comma/Creation.v
   survives: apex by [eq_refl], legs by [reflexivity], at every limiting
   cone downstairs. *)

Definition coslice_comma_StrictlyCreatesLimit
  {J : Category} (K : J ⟶ (=(c) ↓ Id)) :
  StrictlyCreatesLimit K comma_proj2 :=
  comma_StrictlyCreatesLimit K
    (fun N HN => Id_PreservesImageLimit J (Gdiag K)
                   (@Build_Limit J C (Gdiag K) N HN)).

Definition coslice_comma_CreatesAllLimits :
  CreatesAllLimits (@comma_proj2 _ _ _ (=(c)) (Id[C])) :=
  fun J K => StrictlyCreatesLimit_CreatesLimit
               (coslice_comma_StrictlyCreatesLimit K).

(* Completeness of the coslice-as-comma, obtained THROUGH creation rather
   than through [Comma_Complete]. *)

Definition coslice_comma_Complete (HC : @Complete C) : @Complete (=(c) ↓ Id) :=
  creates_limits_Complete comma_proj2 HC coslice_comma_CreatesAllLimits.

(* The same completeness by the route the issue names, kept as a
   cross-check: [Comma_Complete_right_adjoint] at [Adjunction_Id] does
   type-check, exactly as the issue's "Also covered by" section claims.  It
   is a different term from the one above — that one goes through creation,
   this one through Construction/Comma/Limit.v's [Comma_Complete]. *)

Definition coslice_comma_Complete_via_adjoint (HC : @Complete C) :
  @Complete (=(c) ↓ Id) :=
  Comma_Complete_right_adjoint (@Adjunction_Id C) c HC.

(** ** Transporting along [Comma_Coslice] *)

Definition Coslice_to_Comma : (c ̸co C) ⟶ (=(c) ↓ Id) :=
  to (Comma_Coslice C c).

Definition Coslice_Comma_Equivalence :
  @EquivalenceOfCategories (c ̸co C) (=(c) ↓ Id) Coslice_to_Comma :=
  Cat_Iso_to_Equivalence (Comma_Coslice C c).

Definition Coslice_to_Comma_CreatesAllLimits :
  CreatesAllLimits Coslice_to_Comma :=
  equivalence_CreatesAllLimits Coslice_Comma_Equivalence.

Definition Coslice_Complete (HC : @Complete C) : @Complete (c ̸co C) :=
  creates_limits_Complete Coslice_to_Comma (coslice_comma_Complete HC)
    Coslice_to_Comma_CreatesAllLimits.

(* The coslice projection, as the transported comma projection. *)

Definition coslice_comma_proj : (c ̸co C) ⟶ C := comma_proj2 ◯ Coslice_to_Comma.

Definition coslice_comma_proj_CreatesLimit {J : Category} (K : J ⟶ (c ̸co C)) :
  CreatesLimit K coslice_comma_proj :=
  CreatesLimit_compose (Coslice_to_Comma_CreatesAllLimits J K)
    (coslice_comma_CreatesAllLimits J (Coslice_to_Comma ◯ K)).

Definition coslice_comma_proj_CreatesAllLimits :
  CreatesAllLimits coslice_comma_proj :=
  fun J K => coslice_comma_proj_CreatesLimit K.

End CosliceComma.

(** ** Strict creation for the PLAIN coslice projection *)

(* Everything above goes through [Comma_Coslice], and strictness does not
   survive that transport.  It does not have to: [Coslice_Proj]
   (Construction/Slice/Adjunction.v:392) is an unconditioned functor
   [c ̸co C ⟶ C] — the [Cocartesian] variable of the section it sits in is
   not discharged into it, because its body does not use it — and both its
   data fields reduce, [fobj] to [`1 x] and [fmap] to [`1 f] by [eq_refl].
   So the [StrictLift] apex clause is definitional for it, and Riehl's §4.7
   exercise — the direct argument, "along the lines of the argument for the
   analogous statement about slice/coslice projections" — can be carried out
   here rather than deferred.

   It is carried out below, and it needs NO hypothesis whatever: the step
   that consumes preservation in the comma case is the passage from the
   limit downstairs to a limit of its [U]-image, and with [U] the identity
   that passage is the given limiting cone itself.  The structure maps
   [`2 (K j) : c ~> `1 (K j)] of the diagram's objects form a cone with apex
   [c] over the projected diagram, whose mediator into the given limiting
   cone is the lifted object's own structure map; the lifted legs are the
   given legs, so the projection returns them on the nose.

   [Instance/Cat/Pullback.v:847]'s [Coslice_proj] is a second unconditioned
   projection with the same two data fields, and it reduces the same way;
   it is not used here, since importing that file would cost twelve modules
   of closure against this file's five for Construction/Slice/Adjunction.v,
   and the two functors are distinct records. *)

Section CosliceCreate.

Context {C : Category}.
Context (c : C).
Context {J : Category}.
Context (K : J ⟶ (c ̸co C)).

Lemma coslice_structure_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Coslice_Proj c ◯ K] f ∘ `2 (K x) ≈ `2 (K y).
Proof.
  symmetry.
  exact (`2 (fmap[K] f)).
Qed.

Definition coslice_structure_cone : Cone (Coslice_Proj c ◯ K) :=
  @Build_Cone J C (Coslice_Proj c ◯ K) c
    (@Build_ACone J C c (Coslice_Proj c ◯ K)
       (fun j => `2 (K j)) (@coslice_structure_coherence)).

(* Reflection needs no chosen cone downstairs, so it sits outside the
   section that fixes one. *)

Definition coslice_reflect_at (M : Cone K)
  (HM : IsLimitCone (FCone (Coslice_Proj c) M)) : IsLimitCone M.
Proof.
  intro N.
  destruct (HM (FCone (Coslice_Proj c) N)) as [w Hw Hwu].
  assert (Hsq : `2 (vertex_obj[M]) ≈ w ∘ `2 (vertex_obj[N])).
  { transitivity (unique_obj (HM coslice_structure_cone)).
    - symmetry.
      apply (uniqueness (HM coslice_structure_cone)).
      intro j.
      symmetry.
      exact (`2 (cone_leg M j)).
    - apply (uniqueness (HM coslice_structure_cone)).
      intro j.
      rewrite comp_assoc.
      rewrite (Hw j).
      symmetry.
      exact (`2 (cone_leg N j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j.
    exact (Hw j).
  - intros v Hv.
    apply Hwu.
    intro j.
    exact (Hv j).
Defined.

Section CosliceLift.

Context (N : Cone (Coslice_Proj c ◯ K)).
Context (HN : IsLimitCone N).

Definition coslice_med : c ~{C}~> vertex_obj[N] :=
  unique_obj (HN coslice_structure_cone).

Lemma coslice_med_commutes (j : J) :
  cone_leg N j ∘ coslice_med ≈ `2 (K j).
Proof.
  exact (unique_property (HN coslice_structure_cone) j).
Qed.

Definition coslice_lift_obj : c ̸co C := (vertex_obj[N]; coslice_med).

Definition coslice_lift_leg (j : J) : coslice_lift_obj ~{c ̸co C}~> K j.
Proof.
  unshelve refine (cone_leg N j; _).
  symmetry.
  exact (coslice_med_commutes j).
Defined.

Lemma coslice_lift_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ coslice_lift_leg x ≈ coslice_lift_leg y.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f).
Qed.

Definition coslice_lift_cone : Cone K :=
  @Build_Cone J (c ̸co C) K coslice_lift_obj
    (@Build_ACone J (c ̸co C) coslice_lift_obj K
       coslice_lift_leg (@coslice_lift_coherence)).

Definition coslice_lift_ump (M : Cone K) :
  ∃! u : vertex_obj[M] ~{c ̸co C}~> coslice_lift_obj,
    ∀ j : J, coslice_lift_leg j ∘ u ≈ cone_leg M j.
Proof.
  destruct (HN (FCone (Coslice_Proj c) M)) as [w Hw Hwu].
  assert (Hsq : coslice_med ≈ w ∘ `2 (vertex_obj[M])).
  { unfold coslice_med.
    apply (uniqueness (HN coslice_structure_cone)).
    intro j.
    rewrite comp_assoc.
    rewrite (Hw j).
    symmetry.
    exact (`2 (cone_leg M j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j.
    exact (Hw j).
  - intros v Hv.
    apply Hwu.
    intro j.
    exact (Hv j).
Defined.

Definition coslice_limit_at : Limit K :=
  @Build_Limit J (c ̸co C) K coslice_lift_cone coslice_lift_ump.

(* Mac Lane's [F a = x] and [F σ = τ], at the GIVEN limiting cone. *)

Definition coslice_strict_lift : StrictLift K (Coslice_Proj c) N :=
  @Build_StrictLift J (c ̸co C) C K (Coslice_Proj c) N
    coslice_lift_cone eq_refl (fun x => reflexivity _).

Definition coslice_lift_apex :
  fobj[Coslice_Proj c] (vertex_obj[coslice_lift_cone]) = vertex_obj[N]
  := eq_refl.

Definition coslice_lift_legs (j : J) :
  fmap[Coslice_Proj c] (cone_leg coslice_lift_cone j) = cone_leg N j
  := eq_refl.

End CosliceLift.

Definition Coslice_Proj_StrictlyCreatesLimit :
  StrictlyCreatesLimit K (Coslice_Proj c).
Proof.
  unshelve refine {| screates := coslice_strict_lift |}.
  - intros N HN.
    exact (limit_limitcone (coslice_limit_at N HN)).
  - exact coslice_reflect_at.
Defined.

Definition Coslice_Proj_CreatesLimit : CreatesLimit K (Coslice_Proj c) :=
  StrictlyCreatesLimit_CreatesLimit Coslice_Proj_StrictlyCreatesLimit.

End CosliceCreate.

Definition Coslice_Proj_CreatesAllLimits {C : Category} (c : C) :
  CreatesAllLimits (Coslice_Proj c) :=
  fun J K => Coslice_Proj_CreatesLimit c K.

(* Completeness of the coslice without any transport at all.  [Coslice_Complete]
   above reaches the same conclusion through [Comma_Coslice]; the two are
   kept side by side because the transported one is what an equivalence
   gives in general, and this one is what the direct argument gives. *)

Definition Coslice_Complete_direct {C : Category} (c : C) (HC : @Complete C) :
  @Complete (c ̸co C) :=
  creates_limits_Complete (Coslice_Proj c) HC (Coslice_Proj_CreatesAllLimits c).
