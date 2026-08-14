Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.

Set Universe Polymorphism.

Generalizable All Variables.

(** * The comma projection creates limits *)

(* nLab: https://ncatlab.org/nlab/show/comma+category#limits_and_colimits
   nLab: https://ncatlab.org/nlab/show/created+limit

   The projection [comma_proj2 : =(d) ↓ U ⟶ C] creates limits, as the prose
   at Construction/Comma.v:100 and Construction/Comma/Limit.v:33 has always
   said.  Construction/Comma/Limit.v proves existence; what is added here is
   the reflection clause [comma_creates_reflect] and the packaging
   [comma_CreatesLimit] against Structure/Limit/Creation.v.  Nothing in
   Construction/Comma/Limit.v is changed.

   Two consequences worth naming.  First, [PreservesImageLimit]
   (Construction/Comma/Limit.v:110), the honest cone-level hypothesis that
   file introduced and that Adjunction/GAFT.v and Adjunction/SAFT.v consume,
   is [PreservesLimitCone] quantified over all shapes, up to repackaging a
   [Limit] record as a cone together with its universal property: the two
   bridges below carry no proof, and both round trips hold by [eq_refl]
   (the two [Type]s are not themselves convertible, one binding [Limit G]
   where the other binds a cone and an [IsLimitCone]).  So GAFT and SAFT
   already speak the general vocabulary under an older name.

   Second, the created lift lies over an ARBITRARY downstairs limit [L] on
   the nose — [comma_strict_apex] and [comma_strict_legs] are [eq_refl] for
   every [L], not merely for the one a [Complete C] happens to choose.  That
   is the generalization this file's header previously deferred: [Limit.v]
   now takes [Ldiag] as a section parameter instead of computing it as
   [HC J Gdiag], so [comma_limit] is parameterized by the limit it is built
   from and the projection lands on that limit definitionally.  The exported
   type of [Comma_Complete] is unchanged by the move — it simply supplies
   [HC J (Gdiag K)] as the parameter — so Adjunction/GAFT.v and
   Adjunction/SAFT.v are untouched.

   On the house rule that morphisms are compared with [≈]: [comma_strict_legs]
   is the one statement here that writes [=] between morphisms, and it does
   so because both sides are the SAME term — the witness is [eq_refl].  It
   records Mac Lane's [F σ = τ] at full strength, which is strictly stronger
   than the [≈] the class asks for; every proof below uses [≈]. *)

(** ** [PreservesImageLimit] is cone-level preservation at every shape *)

Definition PreservesImageLimit_Continuous
  {C D : Category} {U : C ⟶ D} (H : @PreservesImageLimit C D U) :
  ContinuousFunctor U :=
  fun J K N HN => H J K (@Build_Limit J C K N HN).

Definition Continuous_PreservesImageLimit
  {C D : Category} {U : C ⟶ D} (H : ContinuousFunctor U) :
  @PreservesImageLimit C D U :=
  fun J K L => H J K (@limit_cone _ _ _ L) (limit_limitcone L).

(** ** The reflection clause *)

Section CommaReflect.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (HU : @PreservesImageLimit C D U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(* The cone with apex [d] over [U ◯ (comma_proj2 ◯ K)] read off the comma
   data of K.  This is the general-diagram analogue of [base_cone]
   (Construction/Comma/Limit.v:146), restated because that one is fixed to
   the chosen [Gdiag]. *)

Lemma rbase_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[comma_proj2 ◯ K] f) ∘ `2 (K x) ≈ `2 (K y).
Proof using Type.
  symmetry.
  transitivity (`2 (K y) ∘ id[d]).
  - rewrite id_right; reflexivity.
  - exact (`2 (fmap[K] f)).
Qed.

Definition rbase_cone : Cone (U ◯ (comma_proj2 ◯ K)) :=
  @Build_Cone J D (U ◯ (comma_proj2 ◯ K)) d
    (@Build_ACone J D d (U ◯ (comma_proj2 ◯ K))
       (fun j => `2 (K j)) (@rbase_coherence)).

(* A cone over K whose C-projection is limiting is itself limiting.  The
   C-component of the mediator is given by the projected cone; the comma
   component is the triangle over [d], and that triangle is forced by
   uniqueness of the mediator into the image limit — which is exactly what
   [PreservesImageLimit] supplies. *)

Definition comma_creates_reflect (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj2 M)) : IsLimitCone M.
Proof using HU.
  intro N.
  pose (L := @Build_Limit J C (comma_proj2 ◯ K) (FCone comma_proj2 M) HM).
  destruct (HM (FCone comma_proj2 N)) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ id[d]
                  ≈ fmap[U] w ∘ `2 vertex_obj[N]).
  { rewrite id_right.
    apply (limit_med_eq (image_is_alimit HU L) rbase_cone).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j) ∘ (`2 vertex_obj[M])
                ≈ `2 (K j)).
      symmetry.
      exact (comma_square (cone_leg M j)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j)
                ∘ (fmap[U] w ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (Hw j).
      symmetry.
      exact (comma_square (cone_leg N j)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (Hw j).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro j.
      exact (snd (Hv j)).
Defined.

End CommaReflect.

(** ** The instance *)

Section CommaCreates.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (HU : @PreservesImageLimit C D U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(* An ARBITRARY limit of the base diagram downstairs.  This used to be the
   chosen [Ldiag HC K] coming from a [Complete C]; making it a parameter is
   what upgrades the strictness statements below from "at the chosen limit"
   to "at every limit". *)
Context (L : Limit (Gdiag K)).

(* The image of the comma limit cone IS that downstairs limit cone, by
   conversion. *)

Definition comma_image_limitcone :
  IsLimitCone (FCone comma_proj2 (@limit_cone _ _ _ (comma_limit HU K L)))
  := fun N => @ump_limit _ _ _ _ (limit_is_alimit L) N.

Definition comma_CreatesLimit : CreatesLimit K comma_proj2.
Proof using HU L.
  unshelve refine
    {| creates_lift := fun _ _ => @limit_cone _ _ _ (comma_limit HU K L) |}.
  - intros N HN.
    exact (limitcone_iso comma_image_limitcone HN).
  - exact (comma_creates_reflect HU K).
Defined.

End CommaCreates.

(** ** Strictness at EVERY limit: apex and legs on the nose *)

(* These now quantify over an arbitrary downstairs limit [L] rather than the
   one chosen by a [Complete C].  The witnesses are still [eq_refl]: the
   comma limit is BUILT from [L], so the projection lands on [L]'s apex and
   legs definitionally, whichever limit [L] is.  This is Mac Lane's [F σ = τ]
   at full strength, and it is what the header of this file previously
   deferred as a separate proposal. *)

Definition comma_strict_apex {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U)
  {J : Category} (K : J ⟶ (=(d) ↓ U)) (L : Limit (Gdiag K)) :
  comma_proj2 (vertex_obj[comma_limit HU K L]) = vertex_obj[L]
  := eq_refl.

Definition comma_strict_legs {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U)
  {J : Category} (K : J ⟶ (=(d) ↓ U)) (L : Limit (Gdiag K)) (j : J) :
  fmap[comma_proj2] (cone_leg (comma_limit HU K L) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.
