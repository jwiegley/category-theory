Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Span.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Apex-only preservation is strictly weaker than cone-level preservation

    The library has said for some time — in prose — that the apex-only
    preservation class is too weak: Construction/Comma/Limit.v's STATUS
    header records that two cone structures on one apex can differ by a
    non-invertible endomorphism, so knowing that the image APEX carries some
    limit structure does not make the image CONE universal.  This file turns
    that standing paragraph into theorems, with the cheapest concrete
    witness the tree affords and no hand-rolled categories:

      C := Roof            (Instance/Roof.v — the walking span)
      J := Two_Discrete    (Instance/Two/Discrete.v — two objects, no arrows)
      D := Coq             (Instance/Coq.v)
      K := Pick_Two RNeg RPos          (the two feet of the span)
      F := ASpan fst fst   (Structure/Span.v — both legs to first projection)

    Upstairs, RZero with the legs ZeroNeg/ZeroPos is the limiting cone of K
    — the span has no other object with maps to both feet.  Downstairs the
    composite diagram picks out (bool, bool), whose limit is bool × bool
    with the two genuine projections.  But F sends BOTH legs of the limiting
    cone to fst, so the image cone at bool × bool has legs (fst, fst) — and
    a cone whose two legs disagree, such as (id, negb) at apex bool, has
    no mediator through it ([sep_image_not_limiting]).

    The results, in increasing strength:
    [apex_limit_without_limit_cone] — the image apex DOES carry a limit of
    the composite diagram while the image cone at that very apex is not
    universal (per-diagram separation); [sep_PreservesLimit] +
    [sep_not_PreservesLimitCone] — the apex-only class is inhabited at
    (K, F) while the cone-level class is refuted (class-level separation);
    [PreservesLimit_not_PreservesLimitCone] — no uniform strengthening
    exists; [sep_comparison_is_dup] / [sep_comparison_not_iso] /
    [sep_apex_iso] — the documented endomorphism exhibited: the canonical
    comparison IS the duplicator (w, w') ↦ (w, w), not invertible, even
    though the apex-only witness still yields SOME isomorphism between the
    same two objects.  The weak class produces an isomorphism; it just
    cannot promise the canonical one.

    The other half of the comparison story — cone-level preservation IS
    invertibility of the canonical comparison — is
    [LimitCone_comparison_iso] / [comparison_iso_LimitCone] in
    Structure/Limit/Preservation.v; this file supplies the strictness of
    the inclusion. *)

(** ** A coherence helper for the two-object discrete shape *)

Lemma two_discrete_cone_coherence {C : Category} (H : Two_Discrete ⟶ C)
  (c : C) (leg : ∀ x : Two_Discrete, c ~{C}~> H x)
  {x y : Two_Discrete} (f : x ~{Two_Discrete}~> y) :
  fmap[H] f ∘ leg x ≈ leg y.
Proof.
  destruct f;
  [ change (fmap[H] (@id Two_Discrete TwoDX) ∘ leg TwoDX ≈ leg TwoDX)
  | change (fmap[H] (@id Two_Discrete TwoDY) ∘ leg TwoDY ≈ leg TwoDY) ];
  rewrite fmap_id; apply id_left.
Qed.

(** ** The diagram: the two feet of the walking span *)

Definition SepK : Two_Discrete ⟶ Roof := @Pick_Two Roof RNeg RPos.

Definition sep_cone : Cone SepK :=
  @Build_Cone Two_Discrete Roof SepK RZero
    (@Build_ACone Two_Discrete Roof RZero SepK
       (fun x => match x return RZero ~{Roof}~> SepK x with
                 | TwoDX => ZeroNeg
                 | TwoDY => ZeroPos
                 end)
       (fun x y f => I)).

(* Only the apex of the span carries legs into both feet. *)

Lemma sep_apex (v : Roof) (f : v ~{Roof}~> RNeg) (g : v ~{Roof}~> RPos) :
  RZero = v.
Proof.
  destruct v.
  - exact (False_rect _ (RNeg_RPos_absurd g)).
  - reflexivity.
  - exact (False_rect _ (RPos_RNeg_absurd f)).
Qed.

Definition sep_med (v : Roof) (f : v ~{Roof}~> RNeg) (g : v ~{Roof}~> RPos) :
  v ~{Roof}~> RZero.
Proof.
  destruct v.
  - exact (False_rect _ (RNeg_RPos_absurd g)).
  - exact IdZero.
  - exact (False_rect _ (RPos_RNeg_absurd f)).
Defined.

Definition sep_IsLimitCone : IsLimitCone sep_cone.
Proof.
  intro M.
  unshelve refine
    {| unique_obj := sep_med _ (cone_leg M TwoDX) (cone_leg M TwoDY) |}.
  - intro x; exact I.
  - intros v _; exact I.
Defined.

(** ** The functor: both legs of the span go to the first projection *)

Definition SepF : Roof ⟶ Coq :=
  @ASpan Coq (prod bool bool) bool bool (@fst bool bool) (@fst bool bool).

(** ** [bool × bool] with its genuine projections is the limit downstairs *)

Definition sep_prod_cone : Cone (SepF ◯ SepK) :=
  @Build_Cone Two_Discrete Coq (SepF ◯ SepK) (prod bool bool)
    (@Build_ACone Two_Discrete Coq (prod bool bool) (SepF ◯ SepK)
       (fun x => match x return
                   prod bool bool ~{Coq}~> (SepF ◯ SepK) x with
                 | TwoDX => @fst bool bool
                 | TwoDY => @snd bool bool
                 end)
       (fun x y f => two_discrete_cone_coherence (SepF ◯ SepK) _ _ f)).

Definition sep_prod_IsLimitCone : IsLimitCone sep_prod_cone.
Proof.
  intro M.
  unshelve refine
    {| unique_obj := fun w => (cone_leg M TwoDX w, cone_leg M TwoDY w) |}.
  - intros x w; destruct x; reflexivity.
  - intros v Hv w.
    pose proof (Hv TwoDX w) as H1.
    pose proof (Hv TwoDY w) as H2.
    destruct (v w) as [a b] eqn:Hw.
    assert (Ha : a = cone_leg M TwoDX w)
      by (rewrite <- H1; change (a = fst (v w)); rewrite Hw; reflexivity).
    assert (Hb : b = cone_leg M TwoDY w)
      by (rewrite <- H2; change (b = snd (v w)); rewrite Hw; reflexivity).
    subst; reflexivity.
Defined.

(** ** The image cone is NOT limiting, though its apex carries a limit *)

Definition sep_image_isalimit : IsALimit (SepF ◯ SepK) (SepF RZero) :=
  limitcone_isalimit sep_prod_IsLimitCone.

Definition sep_bad_cone : Cone (SepF ◯ SepK) :=
  @Build_Cone Two_Discrete Coq (SepF ◯ SepK) bool
    (@Build_ACone Two_Discrete Coq bool (SepF ◯ SepK)
       (fun x => match x return bool ~{Coq}~> (SepF ◯ SepK) x with
                 | TwoDX => fun b : bool => b
                 | TwoDY => negb
                 end)
       (fun x y f => two_discrete_cone_coherence (SepF ◯ SepK) _ _ f)).

Theorem sep_image_not_limiting : IsLimitCone (FCone SepF sep_cone) → False.
Proof.
  intro H.
  destruct (H sep_bad_cone) as [u Hu _].
  pose proof (Hu TwoDX true) as H1.
  pose proof (Hu TwoDY true) as H2.
  change (fst (u true) = true) in H1.
  change (fst (u true) = false) in H2.
  rewrite H1 in H2; discriminate.
Qed.

(* Statement (A): the apex carries a limit of the composite diagram, and the
   image cone at that very apex is not universal. *)

Definition apex_limit_without_limit_cone :
  IsALimit (SepF ◯ SepK) vertex_obj[FCone SepF sep_cone]
    * (IsLimitCone (FCone SepF sep_cone) → False) :=
  (sep_image_isalimit, sep_image_not_limiting).

(** ** Statement (B): the class-level separation *)

Definition sep_PreservesLimit : PreservesLimit SepK SepF :=
  @Build_PreservesLimit Two_Discrete Roof SepK Coq SepF
    (fun L =>
       match sep_apex _ (cone_leg (@limit_cone _ _ _ L) TwoDX)
                        (cone_leg (@limit_cone _ _ _ L) TwoDY)
         in _ = z return IsALimit (SepF ◯ SepK) (SepF z)
       with eq_refl => sep_image_isalimit end).

Definition sep_not_PreservesLimitCone : PreservesLimitCone SepK SepF → False :=
  fun P => sep_image_not_limiting (P sep_cone sep_IsLimitCone).

Theorem PreservesLimit_not_PreservesLimitCone :
  (∀ (J C D : Category) (K : J ⟶ C) (F : C ⟶ D),
     PreservesLimit K F → PreservesLimitCone K F) → False.
Proof.
  intro H.
  exact (sep_not_PreservesLimitCone (H _ _ _ SepK SepF sep_PreservesLimit)).
Qed.

(** ** The documented non-invertible endomorphism, exhibited *)

Definition sep_dup : prod bool bool ~{Coq}~> prod bool bool :=
  fun p => (fst p, fst p).

Lemma sep_image_reindexes (x : Two_Discrete) :
  cone_leg sep_prod_cone x ∘ sep_dup ≈ cone_leg (FCone SepF sep_cone) x.
Proof. destruct x; intro w; reflexivity. Qed.

Lemma sep_dup_not_iso : IsIsomorphism sep_dup → False.
Proof.
  intros [g Hr _].
  pose proof (f_equal fst (Hr (true, false))) as E1.
  pose proof (f_equal snd (Hr (true, false))) as E2.
  change (fst (g (true, false)) = true) in E1.
  change (fst (g (true, false)) = false) in E2.
  rewrite E1 in E2; discriminate.
Qed.

Lemma sep_comparison_is_dup :
  cone_comparison SepF sep_cone sep_prod_IsLimitCone ≈ sep_dup.
Proof.
  apply cone_comparison_unique.
  exact sep_image_reindexes.
Qed.

Theorem sep_comparison_not_iso :
  IsIsomorphism (cone_comparison SepF sep_cone sep_prod_IsLimitCone) → False.
Proof.
  intros [g Hr Hl].
  apply sep_dup_not_iso.
  unshelve refine {| two_sided_inverse := g |}.
  - rewrite <- sep_comparison_is_dup; exact Hr.
  - rewrite <- sep_comparison_is_dup; exact Hl.
Qed.

(* And yet the apex-only witness produces an isomorphism between the same two
   objects — just not the canonical one. *)

Definition sep_apex_iso (L : Limit SepK) :
  SepF (vertex_obj[L]) ≅ vertex_obj[sep_prod_cone] :=
  apex_iso_of_PreservesLimit SepF sep_PreservesLimit L sep_prod_IsLimitCone.
