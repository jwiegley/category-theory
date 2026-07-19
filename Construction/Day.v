Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Coend.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.Coend.
Require Import Category.Theory.Coend.Yoneda.
Require Import Category.Theory.Coend.Fubini.

Generalizable All Variables.

(* Discharge every [Program] obligation by hand: the default [cat_simpl] would
   destructure the product-category objects, renaming the variables the proofs
   below refer to. *)
#[local] Obligation Tactic := idtac.

(** Element-level readings of the functor laws for a [Sets]-valued functor. *)
Local Lemma fmap_id_app {K : Category} (G : K ⟶ Sets) {x : K} (z : G x) :
  fmap[G] (@id K x) z ≈ z.
Proof. exact (@fmap_id K Sets G x z). Qed.

Local Lemma fmap_comp_app {K : Category} (G : K ⟶ Sets) {x y z : K}
  (g : y ~{K}~> z) (f : x ~{K}~> y) (w : G x) :
  fmap[G] (g ∘ f) w ≈ fmap[G] g (fmap[G] f w).
Proof. exact (@fmap_comp K Sets G x y z g f w). Qed.

(** * Day convolution on [[C, Sets]] *)

(* nLab:      https://ncatlab.org/nlab/show/Day+convolution
   Wikipedia: https://en.wikipedia.org/wiki/Day_convolution

   For a monoidal category [(C, ⨂, I)] the Day convolution of two functors
   [F, G : C ⟶ Sets] is the functor whose value at [c] is the coend

     (Day F G) c  :=  ∫^{a,b}  C(a ⨂ b, c) × F a × G b.

   It is the left Kan extension of [F ⊗ G] along [⨂], and makes [[C, Sets]] a
   monoidal category with unit the covariant representable [C(I, −)]. This file
   realises it over the concrete [Sets]-coend of Instance/Sets/Coend, so every
   construction is [funext]-free.

   For a fixed target [c] the integrand is the bifunctor

     DayI F G c : (C ∏ C)^op ∏ (C ∏ C) ⟶ Sets,
       ((a1,b1),(a2,b2)) ↦ C(a1 ⨂ b1, c) × F a2 × G b2,

   contravariant in [(a1,b1)] through the hom [C(a1 ⨂ b1, c)] (precomposition
   by the tensor of the two moves) and covariant in [(a2,b2)] through
   [F a2 × G b2]; its diagonal [DayI F G c ((a,b),(a,b)) = C(a ⨂ b, c) × F a × G b]
   is the coend summand. As in Construction/Profunctor/Compose the integrand is
   written directly so that [fmap[DayI F G c]] computes definitionally to the
   pointwise triple map, and the setoid product is [prod_setoid] (Lib/Datatypes).

   [Day F G] is functorial in [c] covariantly (post-compose the hom [C(a ⨂ b, −)]),
   the action being the coend mediator of the transported injections. The
   bifunctoriality in [(F, G)], the unit [C(I, −)], the unitor isomorphisms
   (via the co-Yoneda reduction of Theory/Coend/Yoneda), and the associator
   isomorphism [Day (Day F G) H ≅ Day F (Day G H)] are developed below. The
   associator is a natural isomorphism of functors, built by hand from a pair of
   nested coend mediators (one per side of the tensor) glued by the monoidal
   associator [tensor_assoc] of [C]; the abstract Fubini theorem of
   Theory/Coend/Fubini does not apply directly here, since the doubly-nested
   integrand lives over a product category and needs the interchange gluing
   supplied explicitly below. The induced monoidal structure on [[C, Sets]]
   itself — the [Day_Monoidal] instance packaging these isomorphisms with the
   pentagon and triangle coherences — is deferred to a downstream file
   (ledger 5). *)

Section Day.

Context {C : Category}.
Context `{M : @Monoidal C}.

(** ** The integrand bifunctor at a fixed target *)

(* [DayI F G c ((a1,b1),(a2,b2)) = C(a1 ⨂ b1, c) × F a2 × G b2]. The action on
   [((ua,ub),(va,vb))] precomposes the hom with [ua ⨂ ub] (contravariant) and
   acts by [fmap[F] va], [fmap[G] vb] on the covariant factors. *)
Program Definition DayI (F G : C ⟶ Sets) (c : C) :
  (C ∏ C)^op ∏ (C ∏ C) ⟶ Sets := {|
  fobj := fun p =>
    {| carrier   := ((fst (fst p) ⨂[M] snd (fst p)) ~{C}~> c)
                      * (carrier (F (fst (snd p))) * carrier (G (snd (snd p))))
     ; is_setoid :=
         @prod_setoid _ _ (@homset C (fst (fst p) ⨂[M] snd (fst p)) c)
           (@prod_setoid _ _ (is_setoid (F (fst (snd p))))
                              (is_setoid (G (snd (snd p))))) |};
  fmap := fun x y f =>
    {| morphism := fun hfg =>
         (fst hfg ∘ bimap[@tensor C M] (fst (fst f)) (snd (fst f)),
          (fmap[F] (fst (snd f)) (fst (snd hfg)),
           fmap[G] (snd (snd f)) (snd (snd hfg)))) |}
|}.
Next Obligation.
  unfold Proper, respectful.
  intros F G c x y f [h [a b]] [h' [a' b']] [Hh [Ha Hb]]; split; simpl in *.
  - now rewrite Hh.
  - split; simpl.
    + now rewrite Ha.
    + now rewrite Hb.
Qed.
Next Obligation.
  unfold Proper, respectful.
  intros F G c x y f g [[Hf1 Hf2] [Hg1 Hg2]] [h [a b]]; split; simpl in *.
  - now rewrite Hf1, Hf2.
  - split; simpl.
    + exact (@fmap_respects _ _ F _ _ (fst (snd f)) (fst (snd g)) Hg1 a).
    + exact (@fmap_respects _ _ G _ _ (snd (snd f)) (snd (snd g)) Hg2 b).
Qed.
Next Obligation.
  intros F G c x [h [a b]]; split; simpl in *.
  - rewrite bimap_id_id.
    now rewrite id_right.
  - split; simpl.
    + apply fmap_id_app.
    + apply fmap_id_app.
Qed.
Next Obligation.
  intros F G c x y z f g [h [a b]]; split; simpl in *.
  - rewrite <- comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite bimap_comp.
    reflexivity.
  - split; simpl.
    + apply fmap_comp_app.
    + apply fmap_comp_app.
Qed.

(** The Day convolution object at [c]: the coend apex of the integrand. *)
Definition Day_obj (F G : C ⟶ Sets) (c : C) : SetoidObject :=
  coend_apex_setoid (DayI F G c).

(** ** Functoriality in the target [c] *)

(* The change-of-target map at [((a1,b1),(a2,b2))]: post-compose the hom factor
   with [k], leaving [F], [G] untouched. *)
Program Definition Day_theta_map (F G : C ⟶ Sets) (c1 c2 : C)
  (k : c1 ~{C}~> c2) (p : (C ∏ C)^op ∏ (C ∏ C)) :
  DayI F G c1 p ~{Sets}~> DayI F G c2 p := {|
  morphism := fun hfg => (k ∘ fst hfg, snd hfg) |}.
Next Obligation.
  unfold Proper, respectful.
  intros F G c1 c2 k p [h fg] [h' fg'] [Hh Hfg]; split; simpl in *.
  - now rewrite Hh.
  - exact Hfg.
Qed.

(* Naturality of the change-of-target map in the coend index. *)
Lemma Day_theta_natural (F G : C ⟶ Sets) (c1 c2 : C) (k : c1 ~{C}~> c2) :
  ∀ (x y : (C ∏ C)^op ∏ (C ∏ C)) (m : x ~{(C ∏ C)^op ∏ (C ∏ C)}~> y),
    fmap[DayI F G c2] m ∘ Day_theta_map F G c1 c2 k x
      ≈ Day_theta_map F G c1 c2 k y ∘ fmap[DayI F G c1] m.
Proof.
  intros x y m [h [a b]]; split; simpl.
  - symmetry; apply comp_assoc.
  - split; reflexivity.
Qed.

Definition Day_theta (F G : C ⟶ Sets) (c1 c2 : C) (k : c1 ~{C}~> c2) :
  DayI F G c1 ⟹ DayI F G c2 :=
  Build_Transform' (Day_theta_map F G c1 c2 k)
                   (Day_theta_natural F G c1 c2 k).

(* On the diagonal the change-of-target map for [id] is the identity. *)
Lemma Day_theta_id (F G : C ⟶ Sets) (c : C) (ab : C ∏ C) :
  transform[Day_theta F G c c id] (ab, ab) ≈ id.
Proof.
  intros [h [a b]]; split; simpl.
  - apply id_left.
  - split; reflexivity.
Qed.

(* On the diagonal the change-of-target map sends a composite to a composite. *)
Lemma Day_theta_comp (F G : C ⟶ Sets) (c1 c2 c3 : C)
  (k1 : c1 ~{C}~> c2) (k2 : c2 ~{C}~> c3) (ab : C ∏ C) :
  transform[Day_theta F G c2 c3 k2] (ab, ab)
    ∘ transform[Day_theta F G c1 c2 k1] (ab, ab)
  ≈ transform[Day_theta F G c1 c3 (k2 ∘ k1)] (ab, ab).
Proof.
  intros [h [a b]]; split; simpl.
  - apply comp_assoc.
  - split; reflexivity.
Qed.

(* Change-of-target respects equivalence of the target morphism. *)
Lemma Day_theta_respects (F G : C ⟶ Sets) (c1 c2 : C)
  (k k' : c1 ~{C}~> c2) (ab : C ∏ C) :
  k ≈ k' ->
  transform[Day_theta F G c1 c2 k] (ab, ab)
    ≈ transform[Day_theta F G c1 c2 k'] (ab, ab).
Proof.
  intros Hk [h [a b]]; split; simpl.
  - now rewrite Hk.
  - split; reflexivity.
Qed.

(* The transported injections form a cowedge over the source integrand. *)
Lemma Day_leg_cowedge (F G : C ⟶ Sets) (c1 c2 : C) (k : c1 ~{C}~> c2) :
  Cowedge_cond (DayI F G c1)
    (coend_obj (SetsCoend (DayI F G c2)))
    (fun ab => coend_inj (SetsCoend (DayI F G c2))
               ∘ transform[Day_theta F G c1 c2 k] (ab, ab)).
Proof.
  intros x y g.
  pose proof (coend_cowedge (SetsCoend (DayI F G c2)) g) as Hcw.
  unfold bimap in *.
  rewrite <- comp_assoc.
  rewrite (naturality_sym (Day_theta F G c1 c2 k) (y, x) (x, x) (op g, id)).
  rewrite comp_assoc.
  rewrite Hcw.
  symmetry.
  rewrite <- comp_assoc.
  rewrite (naturality_sym (Day_theta F G c1 c2 k) (y, x) (y, y) (id, g)).
  rewrite comp_assoc.
  reflexivity.
Qed.

(* The action of [Day F G] on a target morphism: the coend mediator. *)
Definition Day_map (F G : C ⟶ Sets) (c1 c2 : C) (k : c1 ~{C}~> c2) :
  coend_obj (SetsCoend (DayI F G c1))
    ~{Sets}~> coend_obj (SetsCoend (DayI F G c2)) :=
  coend_med (SetsCoend (DayI F G c1))
            (coend_obj (SetsCoend (DayI F G c2)))
            (fun ab => coend_inj (SetsCoend (DayI F G c2))
                       ∘ transform[Day_theta F G c1 c2 k] (ab, ab))
            (Day_leg_cowedge F G c1 c2 k).

(* The mediator recovers each transported injection. *)
Lemma Day_map_inj (F G : C ⟶ Sets) (c1 c2 : C) (k : c1 ~{C}~> c2) (ab : C ∏ C) :
  Day_map F G c1 c2 k ∘ coend_inj (SetsCoend (DayI F G c1))
    ≈ coend_inj (SetsCoend (DayI F G c2))
      ∘ transform[Day_theta F G c1 c2 k] (ab, ab).
Proof.
  exact (coend_med_inj (SetsCoend (DayI F G c1))
           (coend_obj (SetsCoend (DayI F G c2)))
           (fun ab => coend_inj (SetsCoend (DayI F G c2))
                      ∘ transform[Day_theta F G c1 c2 k] (ab, ab))
           (Day_leg_cowedge F G c1 c2 k) ab).
Qed.

(** The Day convolution [Day F G : C ⟶ Sets]. *)
Program Definition Day (F G : C ⟶ Sets) : C ⟶ Sets := {|
  fobj := fun c => coend_obj (SetsCoend (DayI F G c));
  fmap := fun c1 c2 k => Day_map F G c1 c2 k
|}.
Next Obligation.
  intros F G c1 c2 k k' Hk.
  apply (coend_med_eq (SetsCoend (DayI F G c1))
           (coend_obj (SetsCoend (DayI F G c2)))
           (fun ab => coend_inj (SetsCoend (DayI F G c2))
                      ∘ transform[Day_theta F G c1 c2 k'] (ab, ab))
           (Day_leg_cowedge F G c1 c2 k')).
  - intro ab.
    transitivity (coend_inj (SetsCoend (DayI F G c2))
                  ∘ transform[Day_theta F G c1 c2 k] (ab, ab)).
    + exact (Day_map_inj F G c1 c2 k ab).
    + rewrite (Day_theta_respects F G c1 c2 k k' ab Hk).
      reflexivity.
  - intro ab.
    exact (Day_map_inj F G c1 c2 k' ab).
Qed.
Next Obligation.
  intros F G c.
  apply (coend_med_eq (SetsCoend (DayI F G c))
           (coend_obj (SetsCoend (DayI F G c)))
           (fun ab => coend_inj (SetsCoend (DayI F G c))
                      ∘ transform[Day_theta F G c c id] (ab, ab))
           (Day_leg_cowedge F G c c id)).
  - intro ab.
    exact (Day_map_inj F G c c id ab).
  - intro ab.
    rewrite id_left.
    rewrite (Day_theta_id F G c ab).
    rewrite id_right.
    reflexivity.
Qed.
Next Obligation.
  intros F G c1 c2 c3 k1 k2.
  apply (coend_med_eq (SetsCoend (DayI F G c1))
           (coend_obj (SetsCoend (DayI F G c3)))
           (fun ab => coend_inj (SetsCoend (DayI F G c3))
                      ∘ transform[Day_theta F G c1 c3 (k1 ∘ k2)] (ab, ab))
           (Day_leg_cowedge F G c1 c3 (k1 ∘ k2))).
  - intro ab.
    exact (Day_map_inj F G c1 c3 (k1 ∘ k2) ab).
  - intro ab.
    rewrite <- comp_assoc.
    rewrite (Day_map_inj F G c1 c2 k2 ab).
    rewrite comp_assoc.
    rewrite (Day_map_inj F G c2 c3 k1 ab).
    rewrite <- comp_assoc.
    rewrite (Day_theta_comp F G c1 c2 c3 k2 k1 ab).
    reflexivity.
Qed.

(** ** The monoidal unit: the covariant representable at [I] *)

Program Definition unit_Day : C ⟶ Sets := {|
  fobj := fun x => {| carrier := I ~{C}~> x; is_setoid := @homset C I x |};
  fmap := fun x y f => {| morphism := fun g => f ∘ g |}
|}.
Next Obligation.
  unfold Proper, respectful.
  intros x y f g g' Hg; simpl.
  now rewrite Hg.
Qed.
Next Obligation.
  unfold Proper, respectful.
  intros x y f f' Hf g; simpl.
  now rewrite Hf.
Qed.
Next Obligation.
  intros x g; simpl.
  apply id_left.
Qed.
Next Obligation.
  intros x y z f h g; simpl.
  symmetry; apply comp_assoc.
Qed.

(** ** Left unitor: [Day unit_Day G ≅ G] via co-Yoneda *)

Section LeftUnitor.
Context (G : C ⟶ Sets).

(* Forward leg at [(a,b)]: collapse the [C(I,a)] factor into the hom by
   [u ↦ h ∘ (u ⨂ 1) ∘ λ⁻¹], then transport [y : G b] along that map [b ~> c]. *)
Program Definition lu_leg (c : C) (ab : C ∏ C) :
  DayI unit_Day G c (ab, ab) ~{Sets}~> G c := {|
  morphism := fun huy =>
    fmap[G] (fst huy
             ∘ bimap[@tensor C M] (fst (snd huy)) (@id C (snd ab))
             ∘ (@unit_left C M (snd ab))⁻¹) (snd (snd huy)) |}.
Next Obligation.
  unfold Proper, respectful.
  intros c ab [h [u y]] [h' [u' y']] [Hh [Hu Hy]]; simpl in *.
  assert (Hm : h ∘ bimap[@tensor C M] u (@id C (snd ab))
                 ∘ (@unit_left C M (snd ab))⁻¹
             ≈ h' ∘ bimap[@tensor C M] u' (@id C (snd ab))
                 ∘ (@unit_left C M (snd ab))⁻¹) by (now rewrite Hh, Hu).
  transitivity (fmap[G] (h ∘ bimap[@tensor C M] u (@id C (snd ab))
                           ∘ (@unit_left C M (snd ab))⁻¹) y').
  - exact (proper_morphism (fmap[G] _) y y' Hy).
  - exact (@fmap_respects _ _ G _ _ _ _ Hm y').
Qed.

Lemma lu_cowedge (c : C) : Cowedge_cond (DayI unit_Day G c) (G c) (lu_leg c).
Proof.
  intros x y f [h' [u y0]]; simpl.
  rewrite <- !fmap_comp_app.
  refine (@fmap_respects _ _ G _ _ _ _ _ y0).
  change (fst (op f)) with (fst f).
  change (snd (op f)) with (snd f).
  rewrite (id_left u).
  transitivity (h' ∘ bimap[@tensor C M] (fst f ∘ u) (snd f)
                   ∘ (@unit_left C M (snd x))⁻¹).
  - rewrite id_right.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite comp_assoc, <- bimap_comp, id_right.
    reflexivity.
  - symmetry.
    rewrite bimap_id_id, id_right.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite <- from_unit_left_natural.
    rewrite comp_assoc, <- bimap_comp, id_right, id_left.
    reflexivity.
Qed.

(* Forward map at [c]: the coend mediator collapsing the [C(I,−)] factor. *)
Definition lu_to (c : C) :
  coend_apex_setoid (DayI unit_Day G c) ~{Sets}~> G c :=
  coend_mediator (DayI unit_Day G c) (lu_leg c) (lu_cowedge c).

(* Inverse map at [c]: [z ↦ ci (I,c) (λ_c, 1_I, z)]. *)
Program Definition lu_from (c : C) :
  G c ~{Sets}~> coend_apex_setoid (DayI unit_Day G c) := {|
  morphism := fun z => ci (DayI unit_Day G c) (I, c)
                          (to (@unit_left C M c), (@id C I, z)) |}.
Next Obligation.
  unfold Proper, respectful; intros c z z' Hz.
  apply ce_point; split; simpl; [ reflexivity | split; [ reflexivity | exact Hz ] ].
Qed.

(* The pointwise left-unitor isomorphism [Day unit_Day G c ≅ G c]. *)
Program Definition lu_iso_pt (c : C) :
  coend_apex_setoid (DayI unit_Day G c) ≅[Sets] G c := {|
  to   := lu_to c;
  from := lu_from c |}.
Next Obligation.
  intros c z; simpl.
  transitivity (fmap[G] (@id C c) z).
  - refine (@fmap_respects _ _ G _ _ _ _ _ z).
    rewrite bimap_id_id, id_right.
    apply iso_to_from.
  - apply fmap_id_app.
Qed.
Next Obligation.
  intro c.
  apply (coend_med_eq (SetsCoend (DayI unit_Day G c))
           (coend_apex_setoid (DayI unit_Day G c))
           (fun ab => coend_inj (SetsCoend (DayI unit_Day G c)) (x := ab))
           (fun ab ab' g => coend_cowedge (SetsCoend (DayI unit_Day G c)) g)).
  - intro ab; destruct ab as [a b]; intros [h [u y0]]; simpl.
    (* [ci (I,c) (λ_c, 1, fmap m y0) ≈ ci (a,b) (h,u,y0)], the co-Yoneda glue
       chain collapsing [a := I] through [u : I ~> a], with [m := h ∘ (u⨂1) ∘ λ_b⁻¹]. *)
    apply ce_sym.
    apply (ce_trans (DayI unit_Day G c) _
             (ci (DayI unit_Day G c) (a, b)
                (h ∘ bimap[@tensor C M] (@id C a) (@id C b),
                 (u ∘ @id C I, fmap[G] (@id C b) y0))) _).
    { apply ce_point; split; simpl.
      - rewrite bimap_id_id; symmetry; apply id_right.
      - split; simpl; [ symmetry; apply id_right | symmetry; apply fmap_id_app ]. }
    apply (ce_trans (DayI unit_Day G c) _
             (ci (DayI unit_Day G c) (I, b)
                (h ∘ bimap[@tensor C M] u (@id C b),
                 (@id C I ∘ @id C I, fmap[G] (@id C b) y0))) _).
    { apply ce_sym.
      exact (ce_glue (DayI unit_Day G c) (I, b) (a, b) (u, @id C b)
                     (h, (@id C I, y0))). }
    apply (ce_trans (DayI unit_Day G c) _
             (ci (DayI unit_Day G c) (I, b)
                (to (@unit_left C M c)
                   ∘ bimap[@tensor C M] (@id C I)
                       (h ∘ bimap[@tensor C M] u (@id C b) ∘ (@unit_left C M b)⁻¹),
                 (@id C I ∘ @id C I, fmap[G] (@id C b) y0))) _).
    { apply ce_point; split; simpl.
      - rewrite <- (to_unit_left_natural
                     (h ∘ bimap[@tensor C M] u (@id C b) ∘ (@unit_left C M b)⁻¹)).
        rewrite <- comp_assoc, (iso_from_to (@unit_left C M b)), id_right.
        reflexivity.
      - split; reflexivity. }
    apply (ce_trans (DayI unit_Day G c) _
             (ci (DayI unit_Day G c) (I, c)
                (to (@unit_left C M c) ∘ bimap[@tensor C M] (@id C I) (@id C c),
                 (@id C I ∘ @id C I,
                  fmap[G] (h ∘ bimap[@tensor C M] u (@id C b)
                            ∘ (@unit_left C M b)⁻¹) y0))) _).
    { exact (ce_glue (DayI unit_Day G c) (I, b) (I, c)
                     (@id C I, h ∘ bimap[@tensor C M] u (@id C b)
                                 ∘ (@unit_left C M b)⁻¹)
                     (to (@unit_left C M c), (@id C I, y0))). }
    apply ce_point; split; simpl.
    + rewrite bimap_id_id; apply id_right.
    + split; simpl; [ apply id_right | reflexivity ].
  - intro ab. apply id_left.
Qed.

(* Post-composition by [fmap[G] k] keeps the forward legs a cowedge. *)
Lemma lu_leg_post_cowedge (c1 c2 : C) (k : c1 ~{C}~> c2) :
  Cowedge_cond (DayI unit_Day G c1) (G c2)
    (fun ab => fmap[G] k ∘ lu_leg c1 ab).
Proof.
  intros x y f.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  exact (lu_cowedge c1 x y f).
Qed.

(* Naturality of the forward map in the target [c]. *)
Lemma lu_to_natural (c1 c2 : C) (k : c1 ~{C}~> c2) :
  fmap[G] k ∘ lu_to c1 ≈ lu_to c2 ∘ Day_map unit_Day G c1 c2 k.
Proof.
  apply (coend_med_eq (SetsCoend (DayI unit_Day G c1)) (G c2)
           (fun ab => fmap[G] k ∘ lu_leg c1 ab)
           (lu_leg_post_cowedge c1 c2 k)).
  - intros ab z; reflexivity.
  - intro ab.
    rewrite <- comp_assoc.
    rewrite (Day_map_inj unit_Day G c1 c2 k ab).
    rewrite comp_assoc.
    intros [h [u y]]; simpl.
    rewrite <- fmap_comp_app.
    refine (@fmap_respects _ _ G _ _ _ _ _ y).
    rewrite <- !comp_assoc.
    reflexivity.
Qed.

(* The natural left-unitor isomorphism [Day unit_Day G ≅ G] in [[C, Sets]]. *)
Definition lu_iso : Day unit_Day G ≅[Fun] G.
Proof.
  apply equiv_iso.
  exists (fun c => lu_iso_pt c).
  intros c1 c2 k.
  change (from (lu_iso_pt c2)) with (lu_from c2).
  change (to (lu_iso_pt c1)) with (lu_to c1).
  symmetry.
  rewrite <- comp_assoc.
  rewrite (lu_to_natural c1 c2 k).
  rewrite comp_assoc.
  change (lu_from c2 ∘ lu_to c2) with (from (lu_iso_pt c2) ∘ to (lu_iso_pt c2)).
  rewrite (iso_from_to (lu_iso_pt c2)).
  apply id_left.
Defined.

End LeftUnitor.

(** ** Right unitor: [Day F unit_Day ≅ F] via co-Yoneda *)

Section RightUnitor.
Context (F : C ⟶ Sets).

(* Forward leg at [(a,b)]: collapse the [C(I,b)] factor into the hom by
   [v ↦ h ∘ (1 ⨂ v) ∘ ρ⁻¹], then transport [x : F a] along that map [a ~> c]. *)
Program Definition ru_leg (c : C) (ab : C ∏ C) :
  DayI F unit_Day c (ab, ab) ~{Sets}~> F c := {|
  morphism := fun hxv =>
    fmap[F] (fst hxv
             ∘ bimap[@tensor C M] (@id C (fst ab)) (snd (snd hxv))
             ∘ (@unit_right C M (fst ab))⁻¹) (fst (snd hxv)) |}.
Next Obligation.
  unfold Proper, respectful.
  intros c ab [h [x v]] [h' [x' v']] [Hh [Hx Hv]]; simpl in *.
  assert (Hm : h ∘ bimap[@tensor C M] (@id C (fst ab)) v
                 ∘ (@unit_right C M (fst ab))⁻¹
             ≈ h' ∘ bimap[@tensor C M] (@id C (fst ab)) v'
                 ∘ (@unit_right C M (fst ab))⁻¹) by (now rewrite Hh, Hv).
  transitivity (fmap[F] (h ∘ bimap[@tensor C M] (@id C (fst ab)) v
                           ∘ (@unit_right C M (fst ab))⁻¹) x').
  - exact (proper_morphism (fmap[F] _) x x' Hx).
  - exact (@fmap_respects _ _ F _ _ _ _ Hm x').
Qed.

Lemma ru_cowedge (c : C) : Cowedge_cond (DayI F unit_Day c) (F c) (ru_leg c).
Proof.
  intros x y f [h' [x0 v]]; simpl.
  rewrite <- !fmap_comp_app.
  refine (@fmap_respects _ _ F _ _ _ _ _ x0).
  change (fst (op f)) with (fst f).
  change (snd (op f)) with (snd f).
  rewrite (id_left v).
  transitivity (h' ∘ bimap[@tensor C M] (fst f) (snd f ∘ v)
                   ∘ (@unit_right C M (fst x))⁻¹).
  - rewrite id_right.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite comp_assoc, <- bimap_comp, id_right.
    reflexivity.
  - symmetry.
    rewrite bimap_id_id, id_right.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite <- from_unit_right_natural.
    rewrite comp_assoc, <- bimap_comp, id_right, id_left.
    reflexivity.
Qed.

Definition ru_to (c : C) :
  coend_apex_setoid (DayI F unit_Day c) ~{Sets}~> F c :=
  coend_mediator (DayI F unit_Day c) (ru_leg c) (ru_cowedge c).

Program Definition ru_from (c : C) :
  F c ~{Sets}~> coend_apex_setoid (DayI F unit_Day c) := {|
  morphism := fun z => ci (DayI F unit_Day c) (c, I)
                          (to (@unit_right C M c), (z, @id C I)) |}.
Next Obligation.
  unfold Proper, respectful; intros c z z' Hz.
  apply ce_point; split; simpl; [ reflexivity | split; [ exact Hz | reflexivity ] ].
Qed.

Program Definition ru_iso_pt (c : C) :
  coend_apex_setoid (DayI F unit_Day c) ≅[Sets] F c := {|
  to   := ru_to c;
  from := ru_from c |}.
Next Obligation.
  intros c z; simpl.
  transitivity (fmap[F] (@id C c) z).
  - refine (@fmap_respects _ _ F _ _ _ _ _ z).
    rewrite bimap_id_id, id_right.
    apply iso_to_from.
  - apply fmap_id_app.
Qed.
Next Obligation.
  intro c.
  apply (coend_med_eq (SetsCoend (DayI F unit_Day c))
           (coend_apex_setoid (DayI F unit_Day c))
           (fun ab => coend_inj (SetsCoend (DayI F unit_Day c)) (x := ab))
           (fun ab ab' g => coend_cowedge (SetsCoend (DayI F unit_Day c)) g)).
  - intro ab; destruct ab as [a b]; intros [h [x0 v]]; simpl.
    apply ce_sym.
    apply (ce_trans (DayI F unit_Day c) _
             (ci (DayI F unit_Day c) (a, b)
                (h ∘ bimap[@tensor C M] (@id C a) (@id C b),
                 (fmap[F] (@id C a) x0, v ∘ @id C I))) _).
    { apply ce_point; split; simpl.
      - rewrite bimap_id_id; symmetry; apply id_right.
      - split; simpl; [ symmetry; apply fmap_id_app | symmetry; apply id_right ]. }
    apply (ce_trans (DayI F unit_Day c) _
             (ci (DayI F unit_Day c) (a, I)
                (h ∘ bimap[@tensor C M] (@id C a) v,
                 (fmap[F] (@id C a) x0, @id C I ∘ @id C I))) _).
    { apply ce_sym.
      exact (ce_glue (DayI F unit_Day c) (a, I) (a, b) (@id C a, v)
                     (h, (x0, @id C I))). }
    apply (ce_trans (DayI F unit_Day c) _
             (ci (DayI F unit_Day c) (a, I)
                (to (@unit_right C M c)
                   ∘ bimap[@tensor C M]
                       (h ∘ bimap[@tensor C M] (@id C a) v ∘ (@unit_right C M a)⁻¹)
                       (@id C I),
                 (fmap[F] (@id C a) x0, @id C I ∘ @id C I))) _).
    { apply ce_point; split; simpl.
      - rewrite <- (to_unit_right_natural
                     (h ∘ bimap[@tensor C M] (@id C a) v ∘ (@unit_right C M a)⁻¹)).
        rewrite <- comp_assoc, (iso_from_to (@unit_right C M a)), id_right.
        reflexivity.
      - split; reflexivity. }
    apply (ce_trans (DayI F unit_Day c) _
             (ci (DayI F unit_Day c) (c, I)
                (to (@unit_right C M c) ∘ bimap[@tensor C M] (@id C c) (@id C I),
                 (fmap[F] (h ∘ bimap[@tensor C M] (@id C a) v
                            ∘ (@unit_right C M a)⁻¹) x0,
                  @id C I ∘ @id C I))) _).
    { exact (ce_glue (DayI F unit_Day c) (a, I) (c, I)
                     (h ∘ bimap[@tensor C M] (@id C a) v ∘ (@unit_right C M a)⁻¹,
                      @id C I)
                     (to (@unit_right C M c), (x0, @id C I))). }
    apply ce_point; split; simpl.
    + rewrite bimap_id_id; apply id_right.
    + split; simpl; [ reflexivity | apply id_right ].
  - intro ab. apply id_left.
Qed.

Lemma ru_leg_post_cowedge (c1 c2 : C) (k : c1 ~{C}~> c2) :
  Cowedge_cond (DayI F unit_Day c1) (F c2)
    (fun ab => fmap[F] k ∘ ru_leg c1 ab).
Proof.
  intros x y f.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  exact (ru_cowedge c1 x y f).
Qed.

Lemma ru_to_natural (c1 c2 : C) (k : c1 ~{C}~> c2) :
  fmap[F] k ∘ ru_to c1 ≈ ru_to c2 ∘ Day_map F unit_Day c1 c2 k.
Proof.
  apply (coend_med_eq (SetsCoend (DayI F unit_Day c1)) (F c2)
           (fun ab => fmap[F] k ∘ ru_leg c1 ab)
           (ru_leg_post_cowedge c1 c2 k)).
  - intros ab z; reflexivity.
  - intro ab.
    rewrite <- comp_assoc.
    rewrite (Day_map_inj F unit_Day c1 c2 k ab).
    rewrite comp_assoc.
    intros [h [x0 v]]; simpl.
    rewrite <- fmap_comp_app.
    refine (@fmap_respects _ _ F _ _ _ _ _ x0).
    rewrite <- !comp_assoc.
    reflexivity.
Qed.

Definition ru_iso : Day F unit_Day ≅[Fun] F.
Proof.
  apply equiv_iso.
  exists (fun c => ru_iso_pt c).
  intros c1 c2 k.
  change (from (ru_iso_pt c2)) with (ru_from c2).
  change (to (ru_iso_pt c1)) with (ru_to c1).
  symmetry.
  rewrite <- comp_assoc.
  rewrite (ru_to_natural c1 c2 k).
  rewrite comp_assoc.
  change (ru_from c2 ∘ ru_to c2) with (from (ru_iso_pt c2) ∘ to (ru_iso_pt c2)).
  rewrite (iso_from_to (ru_iso_pt c2)).
  apply id_left.
Defined.

End RightUnitor.

(** ** The Day tensor as a bifunctor [[C,Sets] ∏ [C,Sets] ⟶ [C,Sets]] *)

(* Change-of-functor map on the integrand: apply [α] and [β] on the covariant
   [F]- and [G]-factors, leaving the hom factor untouched. *)
Program Definition DFG_map (F F' G G' : C ⟶ Sets)
  (α : F ⟹ F') (β : G ⟹ G') (c : C) (p : (C ∏ C)^op ∏ (C ∏ C)) :
  DayI F G c p ~{Sets}~> DayI F' G' c p := {|
  morphism := fun hxy =>
    (fst hxy, (transform[α] (fst (snd p)) (fst (snd hxy)),
               transform[β] (snd (snd p)) (snd (snd hxy)))) |}.
Next Obligation.
  unfold Proper, respectful.
  intros F F' G G' α β c p [h [x y]] [h' [x' y']] [Hh [Hx Hy]]; split; simpl in *.
  - exact Hh.
  - split; simpl; [ now rewrite Hx | now rewrite Hy ].
Qed.

Lemma DFG_natural (F F' G G' : C ⟶ Sets)
  (α : F ⟹ F') (β : G ⟹ G') (c : C) :
  ∀ (x y : (C ∏ C)^op ∏ (C ∏ C)) (m : x ~{(C ∏ C)^op ∏ (C ∏ C)}~> y),
    fmap[DayI F' G' c] m ∘ DFG_map F F' G G' α β c x
      ≈ DFG_map F F' G G' α β c y ∘ fmap[DayI F G c] m.
Proof.
  intros x y m [h [a b]]; split; simpl.
  - reflexivity.
  - split; simpl.
    + exact (naturality[α] _ _ (fst (snd m)) a).
    + exact (naturality[β] _ _ (snd (snd m)) b).
Qed.

Definition DFG_theta (F F' G G' : C ⟶ Sets)
  (α : F ⟹ F') (β : G ⟹ G') (c : C) : DayI F G c ⟹ DayI F' G' c :=
  Build_Transform' (DFG_map F F' G G' α β c) (DFG_natural F F' G G' α β c).

(* On the diagonal, identity transformations act as the identity. *)
Lemma DFG_theta_id (F G : C ⟶ Sets) (c : C) (ab : C ∏ C) :
  transform[DFG_theta F F G G (@nat_id C Sets F) (@nat_id C Sets G) c] (ab, ab)
    ≈ id.
Proof.
  intros [h [a b]]; split; simpl;
    [ reflexivity | split; [ apply fmap_id_app | apply fmap_id_app ] ].
Qed.

(* On the diagonal, composition of transformations composes. *)
Lemma DFG_theta_comp (F F' F'' G G' G'' : C ⟶ Sets)
  (α : F ⟹ F') (α' : F' ⟹ F'') (β : G ⟹ G') (β' : G' ⟹ G'')
  (c : C) (ab : C ∏ C) :
  transform[DFG_theta F' F'' G' G'' α' β' c] (ab, ab)
    ∘ transform[DFG_theta F F' G G' α β c] (ab, ab)
  ≈ transform[DFG_theta F F'' G G'' (nat_compose α' α) (nat_compose β' β) c]
      (ab, ab).
Proof.
  intros [h [a b]]; split; simpl; [ reflexivity | split; reflexivity ].
Qed.

(* Change-of-functor respects equivalence of the transformations. *)
Lemma DFG_theta_respects (F F' G G' : C ⟶ Sets)
  (α α' : F ⟹ F') (β β' : G ⟹ G') (c : C) (ab : C ∏ C) :
  α ≈ α' -> β ≈ β' ->
  transform[DFG_theta F F' G G' α β c] (ab, ab)
    ≈ transform[DFG_theta F F' G G' α' β' c] (ab, ab).
Proof.
  intros Hα Hβ [h [a b]]; split; simpl.
  - reflexivity.
  - split; [ exact (Hα (fst ab) a) | exact (Hβ (snd ab) b) ].
Qed.

(* The change-of-functor legs form a cowedge over the source integrand. *)
Lemma DFG_leg_cowedge (F F' G G' : C ⟶ Sets)
  (α : F ⟹ F') (β : G ⟹ G') (c : C) :
  Cowedge_cond (DayI F G c)
    (coend_obj (SetsCoend (DayI F' G' c)))
    (fun ab => coend_inj (SetsCoend (DayI F' G' c))
               ∘ transform[DFG_theta F F' G G' α β c] (ab, ab)).
Proof.
  intros x y g.
  pose proof (coend_cowedge (SetsCoend (DayI F' G' c)) g) as Hcw.
  unfold bimap in *.
  rewrite <- comp_assoc.
  rewrite (naturality_sym (DFG_theta F F' G G' α β c) (y, x) (x, x) (op g, id)).
  rewrite comp_assoc.
  rewrite Hcw.
  symmetry.
  rewrite <- comp_assoc.
  rewrite (naturality_sym (DFG_theta F F' G G' α β c) (y, x) (y, y) (id, g)).
  rewrite comp_assoc.
  reflexivity.
Qed.

(* The action of the Day tensor on a pair of transformations, at target [c]. *)
Definition DFG_c (F F' G G' : C ⟶ Sets)
  (α : F ⟹ F') (β : G ⟹ G') (c : C) :
  coend_obj (SetsCoend (DayI F G c))
    ~{Sets}~> coend_obj (SetsCoend (DayI F' G' c)) :=
  coend_med (SetsCoend (DayI F G c))
            (coend_obj (SetsCoend (DayI F' G' c)))
            (fun ab => coend_inj (SetsCoend (DayI F' G' c))
                       ∘ transform[DFG_theta F F' G G' α β c] (ab, ab))
            (DFG_leg_cowedge F F' G G' α β c).

Lemma DFG_c_inj (F F' G G' : C ⟶ Sets)
  (α : F ⟹ F') (β : G ⟹ G') (c : C) (ab : C ∏ C) :
  DFG_c F F' G G' α β c ∘ coend_inj (SetsCoend (DayI F G c))
    ≈ coend_inj (SetsCoend (DayI F' G' c))
      ∘ transform[DFG_theta F F' G G' α β c] (ab, ab).
Proof.
  exact (coend_med_inj (SetsCoend (DayI F G c))
           (coend_obj (SetsCoend (DayI F' G' c)))
           (fun ab => coend_inj (SetsCoend (DayI F' G' c))
                      ∘ transform[DFG_theta F F' G G' α β c] (ab, ab))
           (DFG_leg_cowedge F F' G G' α β c) ab).
Qed.

(* Any transform of Day-integrands post-composed with the injections is a
   cowedge; this abstracts the naturality-plus-coend-glue argument shared by the
   target- and functor-change legs. *)
Lemma day_theta_leg_cowedge (A A' B B' : C ⟶ Sets) (c1 c2 : C)
  (T : DayI A B c1 ⟹ DayI A' B' c2) :
  Cowedge_cond (DayI A B c1)
    (coend_obj (SetsCoend (DayI A' B' c2)))
    (fun ab => coend_inj (SetsCoend (DayI A' B' c2)) ∘ transform[T] (ab, ab)).
Proof.
  intros x y g.
  pose proof (coend_cowedge (SetsCoend (DayI A' B' c2)) g) as Hcw.
  unfold bimap in *.
  rewrite <- comp_assoc.
  rewrite (naturality_sym T (y, x) (x, x) (op g, id)).
  rewrite comp_assoc, Hcw.
  symmetry.
  rewrite <- comp_assoc.
  rewrite (naturality_sym T (y, x) (y, y) (id, g)).
  rewrite comp_assoc.
  reflexivity.
Qed.

(* Naturality of the functor-change action in the target [c]. *)
Lemma DFG_c_natural (F F' G G' : C ⟶ Sets)
  (α : F ⟹ F') (β : G ⟹ G') (c1 c2 : C) (k : c1 ~{C}~> c2) :
  fmap[Day F' G'] k ∘ DFG_c F F' G G' α β c1
    ≈ DFG_c F F' G G' α β c2 ∘ fmap[Day F G] k.
Proof.
  apply (coend_med_eq (SetsCoend (DayI F G c1))
           (coend_obj (SetsCoend (DayI F' G' c2)))
           (fun ab => coend_inj (SetsCoend (DayI F' G' c2))
                      ∘ transform[nat_compose (DFG_theta F F' G G' α β c2)
                                    (Day_theta F G c1 c2 k)] (ab, ab))
           (day_theta_leg_cowedge F F' G G' c1 c2
              (nat_compose (DFG_theta F F' G G' α β c2)
                 (Day_theta F G c1 c2 k)))).
  - intro ab.
    change (fmap[Day F' G'] k) with (Day_map F' G' c1 c2 k).
    rewrite <- comp_assoc.
    rewrite (DFG_c_inj F F' G G' α β c1 ab).
    rewrite comp_assoc.
    rewrite (Day_map_inj F' G' c1 c2 k ab).
    rewrite <- comp_assoc.
    intros [h [x y]]; reflexivity.
  - intro ab.
    change (fmap[Day F G] k) with (Day_map F G c1 c2 k).
    rewrite <- comp_assoc.
    rewrite (Day_map_inj F G c1 c2 k ab).
    rewrite comp_assoc.
    rewrite (DFG_c_inj F F' G G' α β c2 ab).
    rewrite <- comp_assoc.
    intros [h [x y]]; reflexivity.
Qed.

(* The Day tensor of a pair of transformations, as a morphism of [[C, Sets]]. *)
Definition Day_tensor_nat (F F' G G' : C ⟶ Sets)
  (α : F ⟹ F') (β : G ⟹ G') : Day F G ⟹ Day F' G' :=
  Build_Transform' (F := Day F G) (G := Day F' G')
                   (fun c => DFG_c F F' G G' α β c)
                   (fun c1 c2 k => DFG_c_natural F F' G G' α β c1 c2 k).

(** The Day convolution tensor as a bifunctor on [[C, Sets]]. *)
Program Definition Day_Tensor : ([C, Sets] ∏ [C, Sets]) ⟶ [C, Sets] := {|
  fobj := fun FG => Day (fst FG) (snd FG);
  fmap := fun FG FG' αβ =>
            Day_tensor_nat (fst FG) (fst FG') (snd FG) (snd FG')
                           (fst αβ) (snd αβ)
|}.
Next Obligation.
  intros [F G] [F' G'] [α β] [α' β'] [Hα Hβ] c; simpl in *.
  apply (coend_med_eq (SetsCoend (DayI F G c))
           (coend_obj (SetsCoend (DayI F' G' c)))
           (fun ab => coend_inj (SetsCoend (DayI F' G' c))
                      ∘ transform[DFG_theta F F' G G' α' β' c] (ab, ab))
           (DFG_leg_cowedge F F' G G' α' β' c)).
  - intro ab.
    rewrite (DFG_c_inj F F' G G' α β c ab).
    apply compose_respects; [ reflexivity | ].
    exact (DFG_theta_respects F F' G G' α α' β β' c ab Hα Hβ).
  - intro ab.
    exact (DFG_c_inj F F' G G' α' β' c ab).
Qed.
Next Obligation.
  intros [F G] c; simpl.
  apply (coend_med_eq (SetsCoend (DayI F G c))
           (coend_obj (SetsCoend (DayI F G c)))
           (fun ab => coend_inj (SetsCoend (DayI F G c)) (x := ab))
           (fun ab ab' g => coend_cowedge (SetsCoend (DayI F G c)) g)).
  - intro ab.
    rewrite (DFG_c_inj F F G G (@nat_id C Sets F) (@nat_id C Sets G) c ab).
    rewrite (DFG_theta_id F G c ab).
    apply id_right.
  - intro ab.
    rewrite (Day_map_inj F G c c id ab).
    rewrite (Day_theta_id F G c ab).
    apply id_right.
Qed.
Next Obligation.
  intros [F G] [F' G'] [F'' G''] [α β] [α' β'] c.
  apply (coend_med_eq (SetsCoend (DayI F G c))
           (coend_obj (SetsCoend (DayI F'' G'' c)))
           (fun ab => coend_inj (SetsCoend (DayI F'' G'' c))
                      ∘ transform[DFG_theta F F'' G G''
                                    (nat_compose α α') (nat_compose β β') c]
                          (ab, ab))
           (DFG_leg_cowedge F F'' G G'' (nat_compose α α') (nat_compose β β') c)).
  - intro ab.
    exact (DFG_c_inj F F'' G G'' (nat_compose α α') (nat_compose β β') c ab).
  - intro ab.
    change (transform[Day_tensor_nat F' F'' G' G'' α β] c
              ∘ transform[Day_tensor_nat F F' G G' α' β'] c
              ∘ coend_inj (SetsCoend (DayI F G c))
            ≈ coend_inj (SetsCoend (DayI F'' G'' c))
                ∘ transform[DFG_theta F F'' G G''
                              (nat_compose α α') (nat_compose β β') c] (ab, ab)).
    rewrite <- comp_assoc.
    rewrite (DFG_c_inj F F' G G' α' β' c ab).
    rewrite comp_assoc.
    rewrite (DFG_c_inj F' F'' G' G'' α β c ab).
    rewrite <- comp_assoc.
    rewrite (DFG_theta_comp F F' F'' G G' G'' α' α β' β c ab).
    reflexivity.
Qed.


Section Associator.
Context (F G H : C ⟶ Sets).
Context (c : C).

Program Definition ato_inner_leg (p d : C)
  (k : (p ⨂[M] d)%object ~{C}~> c) (e : H d) (ab : C ∏ C) :
  DayI F G p (ab, ab)
    ~{Sets}~> coend_obj (SetsCoend (DayI F (Day G H) c)) := {|
  morphism := fun hfg =>
    ci (DayI F (Day G H) c) (fst ab, (snd ab ⨂[M] d)%object)
       (k ∘ bimap[@tensor C M] (fst hfg) (@id C d)
          ∘ (@tensor_assoc C M (fst ab) (snd ab) d)⁻¹,
        (fst (snd hfg),
         ci (DayI G H (snd ab ⨂[M] d)%object) (snd ab, d)
            (@id C (snd ab ⨂[M] d)%object,
             (snd (snd hfg), e)))) |}.
Next Obligation.
  unfold Proper, respectful.
  intros p d k e ab [h [f g]] [h' [f' g']] [Hh [Hf Hg]]; simpl in *.
  apply ce_point; split; simpl.
  - now rewrite Hh.
  - split; simpl.
    + exact Hf.
    + apply ce_point; split; simpl.
      * reflexivity.
      * split; [ exact Hg | reflexivity ].
Qed.

Lemma hom_L_eq (p d : C) (k : (p ⨂[M] d)%object ~{C}~> c)
  (a1 b1 a2 b2 : C) (ga : a1 ~{C}~> a2) (gb : b1 ~{C}~> b2)
  (h0 : (a2 ⨂[M] b2)%object ~{C}~> p) :
  k ∘ bimap[@tensor C M] (h0 ∘ bimap[@tensor C M] ga gb) (@id C d)
    ∘ (@tensor_assoc C M a1 b1 d)⁻¹
  ≈ (k ∘ bimap[@tensor C M] h0 (@id C d) ∘ (@tensor_assoc C M a2 b2 d)⁻¹)
      ∘ bimap[@tensor C M] ga (bimap[@tensor C M] gb (@id C d)).
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- (from_tensor_assoc_natural ga gb (@id C d)).
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_left.
  reflexivity.
Qed.

Lemma ato_inner_cowedge (p d : C)
  (k : (p ⨂[M] d)%object ~{C}~> c) (e : H d) :
  Cowedge_cond (DayI F G p)
    (coend_obj (SetsCoend (DayI F (Day G H) c)))
    (ato_inner_leg p d k e).
Proof.
  intros [a1 b1] [a2 b2] [ga gb] [h0 [u v]].
  pose (φ := ((ga, bimap[@tensor C M] gb (@id C d))
              : (a1, (b1 ⨂[M] d)%object) ~{C ∏ C}~> (a2, (b2 ⨂[M] d)%object))).
  pose (elem := ((k ∘ bimap[@tensor C M] h0 (@id C d)
                    ∘ (@tensor_assoc C M a2 b2 d)⁻¹),
                 (u, ci (DayI G H (b1 ⨂[M] d)%object) (b1, d)
                       (@id C (b1 ⨂[M] d)%object, (v, e))))
              : DayI F (Day G H) c
                  ((a2, (b2 ⨂[M] d)%object), (a1, (b1 ⨂[M] d)%object))).
  pose (ψ := ((gb, @id C d) : (b1, d) ~{C ∏ C}~> (b2, d))).
  pose (inner_elem := ((@id C (b2 ⨂[M] d)%object, (v, e))
              : DayI G H (b2 ⨂[M] d)%object ((b2, d), (b1, d)))).
  apply (ce_trans (DayI F (Day G H) c) _
    (ci (DayI F (Day G H) c) (a1, (b1 ⨂[M] d)%object)
       (bimap[DayI F (Day G H) c] (op φ) (@id (C ∏ C) _) elem)) _).
  - apply ce_point.
    simpl.
    split; [ | split ].
    + exact (hom_L_eq p d k a1 b1 a2 b2 ga gb h0).
    + reflexivity.
    + apply (ce_trans (DayI G H (b1 ⨂[M] d)%object) _
               (ci (DayI G H (b1 ⨂[M] d)%object) (b1, d)
                  (@id C (b1 ⨂[M] d)%object, (v, e))) _).
      * apply ce_point; split;
          [ reflexivity | split; [ apply fmap_id_app | reflexivity ] ].
      * apply ce_sym. apply (fmap_id_app (Day G H)).
  - apply (ce_trans (DayI F (Day G H) c) _
      (ci (DayI F (Day G H) c) (a2, (b2 ⨂[M] d)%object)
         (bimap[DayI F (Day G H) c] (@id (C ∏ C) _) φ elem)) _).
    + exact (ce_glue (DayI F (Day G H) c) (a1, (b1 ⨂[M] d)%object)
               (a2, (b2 ⨂[M] d)%object) φ elem).
    + apply ce_point.
      simpl.
      split; [ | split ].
      * rewrite !bimap_id_id, !id_right; reflexivity.
      * reflexivity.
      * apply (ce_trans (DayI G H (b2 ⨂[M] d)%object) _
          (ci (DayI G H (b2 ⨂[M] d)%object) (b1, d)
             (bimap[@tensor C M] gb (@id C d) ∘ @id C (b1 ⨂[M] d)%object,
              (v, e))) _).
        { exact (Day_map_inj G H (b1 ⨂[M] d)%object (b2 ⨂[M] d)%object
                   (bimap[@tensor C M] gb (@id C d)) (b1, d)
                   (@id C (b1 ⨂[M] d)%object, (v, e))). }
        apply (ce_trans (DayI G H (b2 ⨂[M] d)%object) _
          (ci (DayI G H (b2 ⨂[M] d)%object) (b1, d)
             (bimap[DayI G H (b2 ⨂[M] d)%object] (op ψ) (@id (C ∏ C) _)
                inner_elem)) _).
        { apply ce_point; simpl; split; [ | split ].
          - rewrite id_right; rewrite id_left; reflexivity.
          - symmetry; apply fmap_id_app.
          - symmetry; apply fmap_id_app. }
        apply (ce_trans (DayI G H (b2 ⨂[M] d)%object) _
          (ci (DayI G H (b2 ⨂[M] d)%object) (b2, d)
             (bimap[DayI G H (b2 ⨂[M] d)%object] (@id (C ∏ C) _) ψ
                inner_elem)) _).
        { exact (ce_glue (DayI G H (b2 ⨂[M] d)%object) (b1, d) (b2, d)
                   ψ inner_elem). }
        apply ce_point; simpl; split; [ | split ].
        { rewrite bimap_id_id; rewrite id_left; reflexivity. }
        { reflexivity. }
        { apply fmap_id_app. }
Qed.

(* The inner forward leg respects equivalence of [k] and [e]. *)
Lemma ato_inner_leg_respects (p d : C) (k k' : (p ⨂[M] d)%object ~{C}~> c)
  (e e' : H d) (ab : C ∏ C) :
  k ≈ k' -> e ≈ e' ->
  ato_inner_leg p d k e ab ≈ ato_inner_leg p d k' e' ab.
Proof.
  intros Hk He [h [f g]]; simpl.
  apply ce_point; split; [ | split ].
  - apply compose_respects;
      [ apply compose_respects; [ exact Hk | reflexivity ] | reflexivity ].
  - reflexivity.
  - apply ce_point; split; [ reflexivity | split; [ reflexivity | exact He ] ].
Qed.

(* The inner forward mediator out of [(Day F G) p]. *)
Definition ato_inner_med (p d : C) (k : (p ⨂[M] d)%object ~{C}~> c) (e : H d) :
  coend_obj (SetsCoend (DayI F G p))
    ~{Sets}~> coend_obj (SetsCoend (DayI F (Day G H) c)) :=
  coend_med (SetsCoend (DayI F G p))
            (coend_obj (SetsCoend (DayI F (Day G H) c)))
            (ato_inner_leg p d k e)
            (ato_inner_cowedge p d k e).

(* The outer forward leg at [(p,d)]: apply the inner mediator to the
   [(Day F G) p] datum, carrying the hom [k] and the [H] datum [e]. *)
Program Definition ato_outer_leg (pd : C ∏ C) :
  DayI (Day F G) H c (pd, pd)
    ~{Sets}~> coend_obj (SetsCoend (DayI F (Day G H) c)) := {|
  morphism := fun kxe =>
    ato_inner_med (fst pd) (snd pd) (fst kxe) (snd (snd kxe)) (fst (snd kxe)) |}.
Next Obligation.
  unfold Proper, respectful.
  intros pd [k [x e]] [k' [x' e']] [Hk [Hx He]]; simpl in *.
  assert (Hmed : ato_inner_med (fst pd) (snd pd) k e
                 ≈ ato_inner_med (fst pd) (snd pd) k' e').
  { apply (coend_med_eq (SetsCoend (DayI F G (fst pd)))
             (coend_obj (SetsCoend (DayI F (Day G H) c)))
             (ato_inner_leg (fst pd) (snd pd) k' e')
             (ato_inner_cowedge (fst pd) (snd pd) k' e')
             (ato_inner_med (fst pd) (snd pd) k e)
             (ato_inner_med (fst pd) (snd pd) k' e')).
    - intro ab.
      transitivity (ato_inner_leg (fst pd) (snd pd) k e ab).
      + exact (coend_med_inj (SetsCoend (DayI F G (fst pd)))
                 (coend_obj (SetsCoend (DayI F (Day G H) c)))
                 (ato_inner_leg (fst pd) (snd pd) k e)
                 (ato_inner_cowedge (fst pd) (snd pd) k e) ab).
      + apply ato_inner_leg_respects; assumption.
    - intro ab.
      exact (coend_med_inj (SetsCoend (DayI F G (fst pd)))
               (coend_obj (SetsCoend (DayI F (Day G H) c)))
               (ato_inner_leg (fst pd) (snd pd) k' e')
               (ato_inner_cowedge (fst pd) (snd pd) k' e') ab). }
  apply (ce_trans (DayI F (Day G H) c) _
    (ato_inner_med (fst pd) (snd pd) k e x') _).
  - exact (proper_morphism (ato_inner_med (fst pd) (snd pd) k e) x x' Hx).
  - exact (Hmed x').
Qed.

(* The inner mediator computes on an injection to the inner leg. *)
Lemma ato_inner_med_ci (p d : C) (k : (p ⨂[M] d)%object ~{C}~> c) (e : H d)
  (ab : C ∏ C) (elt : DayI F G p (ab, ab)) :
  ato_inner_med p d k e (ci (DayI F G p) ab elt)
    ≈ ato_inner_leg p d k e ab elt.
Proof.
  exact (coend_med_inj (SetsCoend (DayI F G p))
           (coend_obj (SetsCoend (DayI F (Day G H) c)))
           (ato_inner_leg p d k e) (ato_inner_cowedge p d k e) ab elt).
Qed.

(* Hom reassociation for the outer [(p,d)]-move. *)
Lemma hom_outer_eq (p1 d1 p2 d2 : C) (k : (p2 ⨂[M] d2)%object ~{C}~> c)
  (a0 b0 : C) (gp : p1 ~{C}~> p2) (gd : d1 ~{C}~> d2)
  (h0 : (a0 ⨂[M] b0)%object ~{C}~> p1) :
  (k ∘ bimap[@tensor C M] gp gd)
    ∘ bimap[@tensor C M] (@id C p1 ∘ h0) (@id C d1)
    ∘ (@tensor_assoc C M a0 b0 d1)⁻¹
  ≈ ((k ∘ bimap[@tensor C M] (@id C p2) (@id C d2))
       ∘ bimap[@tensor C M] (gp ∘ h0) (@id C d2)
       ∘ (@tensor_assoc C M a0 b0 d2)⁻¹)
      ∘ bimap[@tensor C M] (@id C a0) (bimap[@tensor C M] (@id C b0) gd).
Proof.
  rewrite <- !comp_assoc.
  rewrite <- (from_tensor_assoc_natural (@id C a0) (@id C b0) gd).
  apply compose_respects; [ reflexivity | ].
  rewrite !comp_assoc.
  rewrite <- !bimap_comp.
  rewrite !bimap_id_id.
  rewrite !id_left, !id_right.
  reflexivity.
Qed.

Lemma ato_outer_cowedge :
  Cowedge_cond (DayI (Day F G) H c)
    (coend_obj (SetsCoend (DayI F (Day G H) c)))
    ato_outer_leg.
Proof.
  intros [p1 d1] [p2 d2] [gp gd] [k [x0 e]].
  destruct x0 as [[a0 b0] [h0 [f0 g0]]].
  simpl.
  pose (χ := ((@id C a0, bimap[@tensor C M] (@id C b0) gd)
              : (a0, (b0 ⨂[M] d1)%object) ~{C ∏ C}~> (a0, (b0 ⨂[M] d2)%object))).
  pose (elem_χ := ((k ∘ bimap[@tensor C M] (@id C p2) (@id C d2)
                      ∘ bimap[@tensor C M] (gp ∘ h0) (@id C d2)
                      ∘ (@tensor_assoc C M a0 b0 d2)⁻¹),
                   (f0, ci (DayI G H (b0 ⨂[M] d1)%object) (b0, d1)
                          (@id C (b0 ⨂[M] d1)%object, (g0, fmap[H] (@id C d1) e))))
              : DayI F (Day G H) c
                  ((a0, (b0 ⨂[M] d2)%object), (a0, (b0 ⨂[M] d1)%object))).
  pose (ψ' := ((@id C b0, gd) : (b0, d1) ~{C ∏ C}~> (b0, d2))).
  pose (inner_elem' := ((@id C (b0 ⨂[M] d2)%object,
                         (g0, fmap[H] (@id C d1) e))
              : DayI G H (b0 ⨂[M] d2)%object ((b0, d2), (b0, d1)))).
  apply (ce_trans (DayI F (Day G H) c) _
    (ato_inner_leg p1 d1 (k ∘ bimap[@tensor C M] gp gd) (fmap[H] (@id C d1) e)
       (a0, b0) (@id C p1 ∘ h0, (f0, g0))) _).
  { apply (ce_trans (DayI F (Day G H) c) _
      (ato_inner_med p1 d1 (k ∘ bimap[@tensor C M] gp gd) (fmap[H] (@id C d1) e)
         (ci (DayI F G p1) (a0, b0) (@id C p1 ∘ h0, (f0, g0)))) _).
    { apply (proper_morphism (ato_inner_med p1 d1
               (k ∘ bimap[@tensor C M] gp gd) (fmap[H] (@id C d1) e))).
      exact (Day_map_inj F G p1 p1 (@id C p1) (a0, b0) (h0, (f0, g0))). }
    { exact (ato_inner_med_ci p1 d1 (k ∘ bimap[@tensor C M] gp gd)
               (fmap[H] (@id C d1) e) (a0, b0) (@id C p1 ∘ h0, (f0, g0))). } }
  apply (ce_trans (DayI F (Day G H) c) _
    (ato_inner_leg p2 d2 (k ∘ bimap[@tensor C M] (@id C p2) (@id C d2))
       (fmap[H] gd e) (a0, b0) (gp ∘ h0, (f0, g0))) _).
  { simpl.
    apply (ce_trans (DayI F (Day G H) c) _
      (ci (DayI F (Day G H) c) (a0, (b0 ⨂[M] d1)%object)
         (bimap[DayI F (Day G H) c] (op χ) (@id (C ∏ C) _) elem_χ)) _).
    { apply ce_point; simpl; split; [ | split ].
      { exact (hom_outer_eq p1 d1 p2 d2 k a0 b0 gp gd h0). }
      { symmetry; apply fmap_id_app. }
      { apply ce_sym. apply (fmap_id_app (Day G H)). } }
    apply (ce_trans (DayI F (Day G H) c) _
      (ci (DayI F (Day G H) c) (a0, (b0 ⨂[M] d2)%object)
         (bimap[DayI F (Day G H) c] (@id (C ∏ C) _) χ elem_χ)) _).
    { exact (ce_glue (DayI F (Day G H) c) (a0, (b0 ⨂[M] d1)%object)
               (a0, (b0 ⨂[M] d2)%object) χ elem_χ). }
    apply ce_point; simpl; split; [ | split ].
    { rewrite !bimap_id_id, !id_right; reflexivity. }
    { apply fmap_id_app. }
    { apply (ce_trans (DayI G H (b0 ⨂[M] d2)%object) _
        (ci (DayI G H (b0 ⨂[M] d2)%object) (b0, d1)
           (bimap[@tensor C M] (@id C b0) gd ∘ @id C (b0 ⨂[M] d1)%object,
            (g0, fmap[H] (@id C d1) e))) _).
      { exact (Day_map_inj G H (b0 ⨂[M] d1)%object (b0 ⨂[M] d2)%object
                 (bimap[@tensor C M] (@id C b0) gd) (b0, d1)
                 (@id C (b0 ⨂[M] d1)%object, (g0, fmap[H] (@id C d1) e))). }
      apply (ce_trans (DayI G H (b0 ⨂[M] d2)%object) _
        (ci (DayI G H (b0 ⨂[M] d2)%object) (b0, d1)
           (bimap[DayI G H (b0 ⨂[M] d2)%object] (op ψ') (@id (C ∏ C) _)
              inner_elem')) _).
      { apply ce_point; simpl; split; [ | split ].
        { rewrite id_right; rewrite id_left; reflexivity. }
        { symmetry; apply fmap_id_app. }
        { symmetry; apply fmap_id_app. } }
      apply (ce_trans (DayI G H (b0 ⨂[M] d2)%object) _
        (ci (DayI G H (b0 ⨂[M] d2)%object) (b0, d2)
           (bimap[DayI G H (b0 ⨂[M] d2)%object] (@id (C ∏ C) _) ψ'
              inner_elem')) _).
      { exact (ce_glue (DayI G H (b0 ⨂[M] d2)%object) (b0, d1) (b0, d2)
                 ψ' inner_elem'). }
      apply ce_point; simpl; split; [ | split ].
      { rewrite bimap_id_id; rewrite id_left; reflexivity. }
      { apply fmap_id_app. }
      { transitivity (fmap[H] (gd ∘ @id C d1) e).
        - symmetry; apply fmap_comp_app.
        - exact (@fmap_respects _ _ H _ _ (gd ∘ @id C d1) gd (id_right gd) e). } } }
  apply ce_sym.
  apply (ce_trans (DayI F (Day G H) c) _
    (ato_inner_med p2 d2 (k ∘ bimap[@tensor C M] (@id C p2) (@id C d2))
       (fmap[H] gd e) (ci (DayI F G p2) (a0, b0) (gp ∘ h0, (f0, g0)))) _).
  { apply (proper_morphism (ato_inner_med p2 d2
             (k ∘ bimap[@tensor C M] (@id C p2) (@id C d2)) (fmap[H] gd e))).
    exact (Day_map_inj F G p1 p2 gp (a0, b0) (h0, (f0, g0))). }
  { exact (ato_inner_med_ci p2 d2 (k ∘ bimap[@tensor C M] (@id C p2) (@id C d2))
             (fmap[H] gd e) (a0, b0) (gp ∘ h0, (f0, g0))). }
Qed.

(* The forward mediator [Day (Day F G) H c ~> Day F (Day G H) c]. *)
Definition assoc_to :
  coend_obj (SetsCoend (DayI (Day F G) H c))
    ~{Sets}~> coend_obj (SetsCoend (DayI F (Day G H) c)) :=
  coend_med (SetsCoend (DayI (Day F G) H c))
            (coend_obj (SetsCoend (DayI F (Day G H) c)))
            ato_outer_leg ato_outer_cowedge.

(* ---------------------------------------------------------------- *)
(* Backward direction: [Day F (Day G H) c ~> Day (Day F G) H c].    *)
(* Mirror of the forward machinery: the inner coend now eliminates  *)
(* the [(Day G H) x] factor on the right, reassociating with        *)
(* [tensor_assoc] (rather than its inverse).                        *)
(* ---------------------------------------------------------------- *)

Program Definition afr_inner_leg (a x : C)
  (k : (a ⨂[M] x)%object ~{C}~> c) (f : F a) (bd : C ∏ C) :
  DayI G H x (bd, bd)
    ~{Sets}~> coend_obj (SetsCoend (DayI (Day F G) H c)) := {|
  morphism := fun mgh =>
    ci (DayI (Day F G) H c) ((a ⨂[M] fst bd)%object, snd bd)
       (k ∘ bimap[@tensor C M] (@id C a) (fst mgh)
          ∘ (@tensor_assoc C M a (fst bd) (snd bd)),
        (ci (DayI F G (a ⨂[M] fst bd)%object) (a, fst bd)
            (@id C (a ⨂[M] fst bd)%object, (f, fst (snd mgh))),
         snd (snd mgh))) |}.
Next Obligation.
  unfold Proper, respectful.
  intros a x k f bd [m [g hh]] [m' [g' hh']] [Hm [Hg Hhh]]; simpl in *.
  apply ce_point; split; simpl.
  - now rewrite Hm.
  - split; simpl.
    + apply ce_point; split; simpl.
      * reflexivity.
      * split; [ reflexivity | exact Hg ].
    + exact Hhh.
Qed.

Lemma hom_R_eq (a x : C) (k : (a ⨂[M] x)%object ~{C}~> c)
  (b1 d1 b2 d2 : C) (gb : b1 ~{C}~> b2) (gd : d1 ~{C}~> d2)
  (m0 : (b2 ⨂[M] d2)%object ~{C}~> x) :
  k ∘ bimap[@tensor C M] (@id C a) (m0 ∘ bimap[@tensor C M] gb gd)
    ∘ (@tensor_assoc C M a b1 d1)
  ≈ (k ∘ bimap[@tensor C M] (@id C a) m0 ∘ (@tensor_assoc C M a b2 d2))
      ∘ bimap[@tensor C M] (bimap[@tensor C M] (@id C a) gb) gd.
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- (to_tensor_assoc_natural (@id C a) gb gd).
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_left.
  reflexivity.
Qed.

Lemma afr_inner_cowedge (a x : C)
  (k : (a ⨂[M] x)%object ~{C}~> c) (f : F a) :
  Cowedge_cond (DayI G H x)
    (coend_obj (SetsCoend (DayI (Day F G) H c)))
    (afr_inner_leg a x k f).
Proof.
  intros [b1 d1] [b2 d2] [gb gd] [m0 [u v]].
  pose (φ := ((bimap[@tensor C M] (@id C a) gb, gd)
              : ((a ⨂[M] b1)%object, d1)
                  ~{C ∏ C}~> ((a ⨂[M] b2)%object, d2))).
  pose (elem := ((k ∘ bimap[@tensor C M] (@id C a) m0
                    ∘ (@tensor_assoc C M a b2 d2)),
                 (ci (DayI F G (a ⨂[M] b1)%object) (a, b1)
                     (@id C (a ⨂[M] b1)%object, (f, u)), v))
              : DayI (Day F G) H c
                  (((a ⨂[M] b2)%object, d2), ((a ⨂[M] b1)%object, d1))).
  pose (ψ := ((@id C a, gb) : (a, b1) ~{C ∏ C}~> (a, b2))).
  pose (inner_elem := ((@id C (a ⨂[M] b2)%object, (f, u))
              : DayI F G (a ⨂[M] b2)%object ((a, b2), (a, b1)))).
  apply (ce_trans (DayI (Day F G) H c) _
    (ci (DayI (Day F G) H c) ((a ⨂[M] b1)%object, d1)
       (bimap[DayI (Day F G) H c] (op φ) (@id (C ∏ C) _) elem)) _).
  - apply ce_point.
    simpl.
    split; [ | split ].
    + exact (hom_R_eq a x k b1 d1 b2 d2 gb gd m0).
    + apply (ce_trans (DayI F G (a ⨂[M] b1)%object) _
               (ci (DayI F G (a ⨂[M] b1)%object) (a, b1)
                  (@id C (a ⨂[M] b1)%object, (f, u))) _).
      * apply ce_point; split;
          [ reflexivity | split; [ reflexivity | apply fmap_id_app ] ].
      * apply ce_sym. apply (fmap_id_app (Day F G)).
    + reflexivity.
  - apply (ce_trans (DayI (Day F G) H c) _
      (ci (DayI (Day F G) H c) ((a ⨂[M] b2)%object, d2)
         (bimap[DayI (Day F G) H c] (@id (C ∏ C) _) φ elem)) _).
    + exact (ce_glue (DayI (Day F G) H c) ((a ⨂[M] b1)%object, d1)
               ((a ⨂[M] b2)%object, d2) φ elem).
    + apply ce_point.
      simpl.
      split; [ | split ].
      * rewrite !bimap_id_id, !id_right; reflexivity.
      * apply (ce_trans (DayI F G (a ⨂[M] b2)%object) _
          (ci (DayI F G (a ⨂[M] b2)%object) (a, b1)
             (bimap[@tensor C M] (@id C a) gb ∘ @id C (a ⨂[M] b1)%object,
              (f, u))) _).
        { exact (Day_map_inj F G (a ⨂[M] b1)%object (a ⨂[M] b2)%object
                   (bimap[@tensor C M] (@id C a) gb) (a, b1)
                   (@id C (a ⨂[M] b1)%object, (f, u))). }
        apply (ce_trans (DayI F G (a ⨂[M] b2)%object) _
          (ci (DayI F G (a ⨂[M] b2)%object) (a, b1)
             (bimap[DayI F G (a ⨂[M] b2)%object] (op ψ) (@id (C ∏ C) _)
                inner_elem)) _).
        { apply ce_point; simpl; split; [ | split ].
          - rewrite id_right; rewrite id_left; reflexivity.
          - symmetry; apply fmap_id_app.
          - symmetry; apply fmap_id_app. }
        apply (ce_trans (DayI F G (a ⨂[M] b2)%object) _
          (ci (DayI F G (a ⨂[M] b2)%object) (a, b2)
             (bimap[DayI F G (a ⨂[M] b2)%object] (@id (C ∏ C) _) ψ
                inner_elem)) _).
        { exact (ce_glue (DayI F G (a ⨂[M] b2)%object) (a, b1) (a, b2)
                   ψ inner_elem). }
        apply ce_point; simpl; split; [ | split ].
        { rewrite bimap_id_id; rewrite id_left; reflexivity. }
        { apply fmap_id_app. }
        { reflexivity. }
      * reflexivity.
Qed.

Lemma afr_inner_leg_respects (a x : C) (k k' : (a ⨂[M] x)%object ~{C}~> c)
  (f f' : F a) (bd : C ∏ C) :
  k ≈ k' -> f ≈ f' ->
  afr_inner_leg a x k f bd ≈ afr_inner_leg a x k' f' bd.
Proof.
  intros Hk Hf [m [g hh]]; simpl.
  apply ce_point; split; [ | split ].
  - apply compose_respects;
      [ apply compose_respects; [ exact Hk | reflexivity ] | reflexivity ].
  - apply ce_point; split; [ reflexivity | split; [ exact Hf | reflexivity ] ].
  - reflexivity.
Qed.

Definition afr_inner_med (a x : C) (k : (a ⨂[M] x)%object ~{C}~> c) (f : F a) :
  coend_obj (SetsCoend (DayI G H x))
    ~{Sets}~> coend_obj (SetsCoend (DayI (Day F G) H c)) :=
  coend_med (SetsCoend (DayI G H x))
            (coend_obj (SetsCoend (DayI (Day F G) H c)))
            (afr_inner_leg a x k f)
            (afr_inner_cowedge a x k f).

Lemma afr_inner_med_ci (a x : C) (k : (a ⨂[M] x)%object ~{C}~> c) (f : F a)
  (bd : C ∏ C) (elt : DayI G H x (bd, bd)) :
  afr_inner_med a x k f (ci (DayI G H x) bd elt)
    ≈ afr_inner_leg a x k f bd elt.
Proof.
  exact (coend_med_inj (SetsCoend (DayI G H x))
           (coend_obj (SetsCoend (DayI (Day F G) H c)))
           (afr_inner_leg a x k f) (afr_inner_cowedge a x k f) bd elt).
Qed.

Program Definition afr_outer_leg (ax : C ∏ C) :
  DayI F (Day G H) c (ax, ax)
    ~{Sets}~> coend_obj (SetsCoend (DayI (Day F G) H c)) := {|
  morphism := fun kfW =>
    afr_inner_med (fst ax) (snd ax) (fst kfW) (fst (snd kfW)) (snd (snd kfW)) |}.
Next Obligation.
  unfold Proper, respectful.
  intros ax [k [f W]] [k' [f' W']] [Hk [Hf HW]]; simpl in *.
  assert (Hmed : afr_inner_med (fst ax) (snd ax) k f
                 ≈ afr_inner_med (fst ax) (snd ax) k' f').
  { apply (coend_med_eq (SetsCoend (DayI G H (snd ax)))
             (coend_obj (SetsCoend (DayI (Day F G) H c)))
             (afr_inner_leg (fst ax) (snd ax) k' f')
             (afr_inner_cowedge (fst ax) (snd ax) k' f')
             (afr_inner_med (fst ax) (snd ax) k f)
             (afr_inner_med (fst ax) (snd ax) k' f')).
    - intro bd.
      transitivity (afr_inner_leg (fst ax) (snd ax) k f bd).
      + exact (coend_med_inj (SetsCoend (DayI G H (snd ax)))
                 (coend_obj (SetsCoend (DayI (Day F G) H c)))
                 (afr_inner_leg (fst ax) (snd ax) k f)
                 (afr_inner_cowedge (fst ax) (snd ax) k f) bd).
      + apply afr_inner_leg_respects; assumption.
    - intro bd.
      exact (coend_med_inj (SetsCoend (DayI G H (snd ax)))
               (coend_obj (SetsCoend (DayI (Day F G) H c)))
               (afr_inner_leg (fst ax) (snd ax) k' f')
               (afr_inner_cowedge (fst ax) (snd ax) k' f') bd). }
  apply (ce_trans (DayI (Day F G) H c) _
    (afr_inner_med (fst ax) (snd ax) k f W') _).
  - exact (proper_morphism (afr_inner_med (fst ax) (snd ax) k f) W W' HW).
  - exact (Hmed W').
Qed.

Lemma hom_R_outer_eq (a1 x1 a2 x2 : C) (k : (a2 ⨂[M] x2)%object ~{C}~> c)
  (b0 d0 : C) (ga : a1 ~{C}~> a2) (gx : x1 ~{C}~> x2)
  (m0 : (b0 ⨂[M] d0)%object ~{C}~> x1) :
  (k ∘ bimap[@tensor C M] ga gx)
    ∘ bimap[@tensor C M] (@id C a1) (@id C x1 ∘ m0)
    ∘ (@tensor_assoc C M a1 b0 d0)
  ≈ ((k ∘ bimap[@tensor C M] (@id C a2) (@id C x2))
       ∘ bimap[@tensor C M] (@id C a2) (gx ∘ m0)
       ∘ (@tensor_assoc C M a2 b0 d0))
      ∘ bimap[@tensor C M] (bimap[@tensor C M] ga (@id C b0)) (@id C d0).
Proof.
  rewrite <- !comp_assoc.
  rewrite <- (to_tensor_assoc_natural ga (@id C b0) (@id C d0)).
  apply compose_respects; [ reflexivity | ].
  rewrite !comp_assoc.
  rewrite <- !bimap_comp.
  rewrite !bimap_id_id.
  rewrite !id_left, !id_right.
  reflexivity.
Qed.

Lemma afr_outer_cowedge :
  Cowedge_cond (DayI F (Day G H) c)
    (coend_obj (SetsCoend (DayI (Day F G) H c)))
    afr_outer_leg.
Proof.
  intros [a1 x1] [a2 x2] [ga gx] [k [f0 W]].
  destruct W as [[b0 d0] [m0 [g0 hh0]]].
  simpl.
  pose (χR := ((bimap[@tensor C M] ga (@id C b0), @id C d0)
              : ((a1 ⨂[M] b0)%object, d0)
                  ~{C ∏ C}~> ((a2 ⨂[M] b0)%object, d0))).
  pose (elem_χR := ((k ∘ bimap[@tensor C M] (@id C a2) (@id C x2)
                       ∘ bimap[@tensor C M] (@id C a2) (gx ∘ m0)
                       ∘ (@tensor_assoc C M a2 b0 d0)),
                    (ci (DayI F G (a1 ⨂[M] b0)%object) (a1, b0)
                        (@id C (a1 ⨂[M] b0)%object, (fmap[F] (@id C a1) f0, g0)),
                     hh0))
              : DayI (Day F G) H c
                  (((a2 ⨂[M] b0)%object, d0), ((a1 ⨂[M] b0)%object, d0))).
  pose (ψR := ((ga, @id C b0) : (a1, b0) ~{C ∏ C}~> (a2, b0))).
  pose (inner_elemR := ((@id C (a2 ⨂[M] b0)%object, (fmap[F] (@id C a1) f0, g0))
              : DayI F G (a2 ⨂[M] b0)%object ((a2, b0), (a1, b0)))).
  apply (ce_trans (DayI (Day F G) H c) _
    (afr_inner_leg a1 x1 (k ∘ bimap[@tensor C M] ga gx) (fmap[F] (@id C a1) f0)
       (b0, d0) (@id C x1 ∘ m0, (g0, hh0))) _).
  { apply (ce_trans (DayI (Day F G) H c) _
      (afr_inner_med a1 x1 (k ∘ bimap[@tensor C M] ga gx)
         (fmap[F] (@id C a1) f0)
         (ci (DayI G H x1) (b0, d0) (@id C x1 ∘ m0, (g0, hh0)))) _).
    { apply (proper_morphism (afr_inner_med a1 x1
               (k ∘ bimap[@tensor C M] ga gx) (fmap[F] (@id C a1) f0))).
      exact (Day_map_inj G H x1 x1 (@id C x1) (b0, d0) (m0, (g0, hh0))). }
    { exact (afr_inner_med_ci a1 x1 (k ∘ bimap[@tensor C M] ga gx)
               (fmap[F] (@id C a1) f0) (b0, d0) (@id C x1 ∘ m0, (g0, hh0))). } }
  apply (ce_trans (DayI (Day F G) H c) _
    (afr_inner_leg a2 x2 (k ∘ bimap[@tensor C M] (@id C a2) (@id C x2))
       (fmap[F] ga f0) (b0, d0) (gx ∘ m0, (g0, hh0))) _).
  { simpl.
    apply (ce_trans (DayI (Day F G) H c) _
      (ci (DayI (Day F G) H c) ((a1 ⨂[M] b0)%object, d0)
         (bimap[DayI (Day F G) H c] (op χR) (@id (C ∏ C) _) elem_χR)) _).
    { apply ce_point; simpl; split; [ | split ].
      { exact (hom_R_outer_eq a1 x1 a2 x2 k b0 d0 ga gx m0). }
      { apply ce_sym. apply (fmap_id_app (Day F G)). }
      { symmetry; apply fmap_id_app. } }
    apply (ce_trans (DayI (Day F G) H c) _
      (ci (DayI (Day F G) H c) ((a2 ⨂[M] b0)%object, d0)
         (bimap[DayI (Day F G) H c] (@id (C ∏ C) _) χR elem_χR)) _).
    { exact (ce_glue (DayI (Day F G) H c) ((a1 ⨂[M] b0)%object, d0)
               ((a2 ⨂[M] b0)%object, d0) χR elem_χR). }
    apply ce_point; simpl; split; [ | split ].
    { rewrite !bimap_id_id, !id_right; reflexivity. }
    { apply (ce_trans (DayI F G (a2 ⨂[M] b0)%object) _
        (ci (DayI F G (a2 ⨂[M] b0)%object) (a1, b0)
           (bimap[@tensor C M] ga (@id C b0) ∘ @id C (a1 ⨂[M] b0)%object,
            (fmap[F] (@id C a1) f0, g0))) _).
      { exact (Day_map_inj F G (a1 ⨂[M] b0)%object (a2 ⨂[M] b0)%object
                 (bimap[@tensor C M] ga (@id C b0)) (a1, b0)
                 (@id C (a1 ⨂[M] b0)%object, (fmap[F] (@id C a1) f0, g0))). }
      apply (ce_trans (DayI F G (a2 ⨂[M] b0)%object) _
        (ci (DayI F G (a2 ⨂[M] b0)%object) (a1, b0)
           (bimap[DayI F G (a2 ⨂[M] b0)%object] (op ψR) (@id (C ∏ C) _)
              inner_elemR)) _).
      { apply ce_point; simpl; split; [ | split ].
        - rewrite id_right; rewrite id_left; reflexivity.
        - symmetry; apply fmap_id_app.
        - symmetry; apply fmap_id_app. }
      apply (ce_trans (DayI F G (a2 ⨂[M] b0)%object) _
        (ci (DayI F G (a2 ⨂[M] b0)%object) (a2, b0)
           (bimap[DayI F G (a2 ⨂[M] b0)%object] (@id (C ∏ C) _) ψR
              inner_elemR)) _).
      { exact (ce_glue (DayI F G (a2 ⨂[M] b0)%object) (a1, b0) (a2, b0)
                 ψR inner_elemR). }
      apply ce_point; simpl; split; [ | split ].
      { rewrite bimap_id_id; rewrite id_left; reflexivity. }
      { transitivity (fmap[F] (ga ∘ @id C a1) f0).
        - symmetry; apply fmap_comp_app.
        - exact (@fmap_respects _ _ F _ _ (ga ∘ @id C a1) ga (id_right ga) f0). }
      { apply fmap_id_app. } }
    { apply fmap_id_app. } }
  apply ce_sym.
  apply (ce_trans (DayI (Day F G) H c) _
    (afr_inner_med a2 x2 (k ∘ bimap[@tensor C M] (@id C a2) (@id C x2))
       (fmap[F] ga f0)
       (ci (DayI G H x2) (b0, d0) (gx ∘ m0, (g0, hh0)))) _).
  { apply (proper_morphism (afr_inner_med a2 x2
             (k ∘ bimap[@tensor C M] (@id C a2) (@id C x2)) (fmap[F] ga f0))).
    exact (Day_map_inj G H x1 x2 gx (b0, d0) (m0, (g0, hh0))). }
  { exact (afr_inner_med_ci a2 x2 (k ∘ bimap[@tensor C M] (@id C a2) (@id C x2))
             (fmap[F] ga f0) (b0, d0) (gx ∘ m0, (g0, hh0))). }
Qed.

(* The backward mediator [Day F (Day G H) c ~> Day (Day F G) H c]. *)
Definition assoc_from :
  coend_obj (SetsCoend (DayI F (Day G H) c))
    ~{Sets}~> coend_obj (SetsCoend (DayI (Day F G) H c)) :=
  coend_med (SetsCoend (DayI F (Day G H) c))
            (coend_obj (SetsCoend (DayI (Day F G) H c)))
            afr_outer_leg afr_outer_cowedge.

(* ---------------------------------------------------------------- *)
(* Round trips.                                                     *)
(* ---------------------------------------------------------------- *)

(* Reinjection of a [(Day G H) x] datum into [Day F (Day G H) c] at [(a,x)]. *)
Program Definition afr_rebuild (a x : C)
  (k : (a ⨂[M] x)%object ~{C}~> c) (f0 : F a) :
  coend_obj (SetsCoend (DayI G H x))
    ~{Sets}~> coend_obj (SetsCoend (DayI F (Day G H) c)) := {|
  morphism := fun W => ci (DayI F (Day G H) c) (a, x) (k, (f0, W)) |}.
Next Obligation.
  intros a x k f0 W W' HW; simpl.
  apply ce_point; simpl; split; [ reflexivity | split; [ reflexivity | exact HW ] ].
Qed.

(* On the inner coend, [assoc_to] undoes [afr_inner_med]: the outer/inner
   [tensor_assoc] introduced by [afr_inner_leg] cancels the [tensor_assoc]
   inverse of [ato_inner_leg], and a single [ce_glue] at [(id, m)] realigns
   the outer coend index. *)
Lemma round_to_from (a x : C)
  (k : (a ⨂[M] x)%object ~{C}~> c) (f0 : F a) :
  assoc_to ∘ afr_inner_med a x k f0 ≈ afr_rebuild a x k f0.
Proof.
  apply (coend_med_eq (SetsCoend (DayI G H x))
    (coend_obj (SetsCoend (DayI F (Day G H) c)))
    (fun bd => afr_rebuild a x k f0
               ∘ @coend_inj (C ∏ C) Sets (DayI G H x) (SetsCoend (DayI G H x)) bd)
    (postcompose_cowedge (DayI G H x) (SetsCoend (DayI G H x))
       (coend_obj (SetsCoend (DayI F (Day G H) c))) (afr_rebuild a x k f0))
    (assoc_to ∘ afr_inner_med a x k f0)
    (afr_rebuild a x k f0)).
  - intros [b d] [m [g hh]].
    pose (φ := ((@id C a, m) : (a, (b ⨂[M] d)%object) ~{C ∏ C}~> (a, x))).
    pose (elt := ((k, (f0, ci (DayI G H (b ⨂[M] d)%object) (b, d)
                          (@id C (b ⨂[M] d)%object, (g, hh))))
                : DayI F (Day G H) c ((a, x), (a, (b ⨂[M] d)%object)))).
    transitivity (assoc_to (afr_inner_leg a x k f0 (b, d) (m, (g, hh)))).
    { apply (proper_morphism assoc_to).
      exact (afr_inner_med_ci a x k f0 (b, d) (m, (g, hh))). }
    transitivity (ato_inner_med (a ⨂[M] b)%object d
      (k ∘ bimap[@tensor C M] (@id C a) m ∘ (@tensor_assoc C M a b d)) hh
      (ci (DayI F G (a ⨂[M] b)%object) (a, b)
         (@id C (a ⨂[M] b)%object, (f0, g)))).
    { exact (coend_med_inj (SetsCoend (DayI (Day F G) H c))
               (coend_obj (SetsCoend (DayI F (Day G H) c)))
               ato_outer_leg ato_outer_cowedge ((a ⨂[M] b)%object, d)
               (k ∘ bimap[@tensor C M] (@id C a) m ∘ (@tensor_assoc C M a b d),
                (ci (DayI F G (a ⨂[M] b)%object) (a, b)
                    (@id C (a ⨂[M] b)%object, (f0, g)), hh))). }
    transitivity (ato_inner_leg (a ⨂[M] b)%object d
      (k ∘ bimap[@tensor C M] (@id C a) m ∘ (@tensor_assoc C M a b d)) hh
      (a, b) (@id C (a ⨂[M] b)%object, (f0, g))).
    { exact (ato_inner_med_ci (a ⨂[M] b)%object d
               (k ∘ bimap[@tensor C M] (@id C a) m ∘ (@tensor_assoc C M a b d)) hh
               (a, b) (@id C (a ⨂[M] b)%object, (f0, g))). }
    transitivity (ci (DayI F (Day G H) c) (a, (b ⨂[M] d)%object)
      (bimap[DayI F (Day G H) c] (op φ) (@id (C ∏ C) _) elt)).
    { apply ce_point; simpl; split; [ | split ].
      - rewrite bimap_id_id, id_right, <- comp_assoc, iso_to_from, id_right;
          reflexivity.
      - symmetry; apply fmap_id_app.
      - apply ce_sym; apply (fmap_id_app (Day G H)). }
    transitivity (ci (DayI F (Day G H) c) (a, x)
      (bimap[DayI F (Day G H) c] (@id (C ∏ C) _) φ elt)).
    { exact (ce_glue (DayI F (Day G H) c) (a, (b ⨂[M] d)%object) (a, x) φ elt). }
    apply ce_point; simpl; split; [ | split ].
    + rewrite bimap_id_id; rewrite id_right; reflexivity.
    + apply fmap_id_app.
    + apply (ce_trans (DayI G H x) _
        (ci (DayI G H x) (b, d) (m ∘ @id C (b ⨂[M] d)%object, (g, hh))) _).
      { exact (Day_map_inj G H (b ⨂[M] d)%object x m (b, d)
                 (@id C (b ⨂[M] d)%object, (g, hh))). }
      apply ce_point; simpl; split; [ | split ].
      * rewrite id_right; reflexivity.
      * reflexivity.
      * reflexivity.
  - intro bd; reflexivity.
Qed.

Lemma assoc_to_from : assoc_to ∘ assoc_from ≈ id.
Proof.
  apply (coend_med_eq (SetsCoend (DayI F (Day G H) c))
    (coend_obj (SetsCoend (DayI F (Day G H) c)))
    (fun ax => @coend_inj (C ∏ C) Sets (DayI F (Day G H) c)
                 (SetsCoend (DayI F (Day G H) c)) ax)
    (fun x y f => @coend_cowedge (C ∏ C) Sets (DayI F (Day G H) c)
                    (SetsCoend (DayI F (Day G H) c)) x y f)
    (assoc_to ∘ assoc_from) id).
  - intros [a x] [k [f0 W]].
    transitivity (assoc_to (afr_inner_med a x k f0 W)).
    + apply (proper_morphism assoc_to).
      exact (coend_med_inj (SetsCoend (DayI F (Day G H) c))
               (coend_obj (SetsCoend (DayI (Day F G) H c)))
               afr_outer_leg afr_outer_cowedge (a, x) (k, (f0, W))).
    + exact (round_to_from a x k f0 W).
  - intros [a x] elt; reflexivity.
Qed.

(* Reinjection of a [(Day F G) p] datum into [Day (Day F G) H c] at [(p,d)]. *)
Program Definition ato_rebuild (p d : C)
  (k : (p ⨂[M] d)%object ~{C}~> c) (e : H d) :
  coend_obj (SetsCoend (DayI F G p))
    ~{Sets}~> coend_obj (SetsCoend (DayI (Day F G) H c)) := {|
  morphism := fun W => ci (DayI (Day F G) H c) (p, d) (k, (W, e)) |}.
Next Obligation.
  intros p d k e W W' HW; simpl.
  apply ce_point; simpl; split; [ reflexivity | split; [ exact HW | reflexivity ] ].
Qed.

(* On the inner coend, [assoc_from] undoes [ato_inner_med]. *)
Lemma round_from_to (p d : C)
  (k : (p ⨂[M] d)%object ~{C}~> c) (e : H d) :
  assoc_from ∘ ato_inner_med p d k e ≈ ato_rebuild p d k e.
Proof.
  apply (coend_med_eq (SetsCoend (DayI F G p))
    (coend_obj (SetsCoend (DayI (Day F G) H c)))
    (fun ab => ato_rebuild p d k e
               ∘ @coend_inj (C ∏ C) Sets (DayI F G p) (SetsCoend (DayI F G p)) ab)
    (postcompose_cowedge (DayI F G p) (SetsCoend (DayI F G p))
       (coend_obj (SetsCoend (DayI (Day F G) H c))) (ato_rebuild p d k e))
    (assoc_from ∘ ato_inner_med p d k e)
    (ato_rebuild p d k e)).
  - intros [a b] [h [f g]].
    pose (φ' := ((h, @id C d) : ((a ⨂[M] b)%object, d) ~{C ∏ C}~> (p, d))).
    pose (elt' := ((k, (ci (DayI F G (a ⨂[M] b)%object) (a, b)
                          (@id C (a ⨂[M] b)%object, (f, g)), e))
                : DayI (Day F G) H c ((p, d), ((a ⨂[M] b)%object, d)))).
    transitivity (assoc_from (ato_inner_leg p d k e (a, b) (h, (f, g)))).
    { apply (proper_morphism assoc_from).
      exact (ato_inner_med_ci p d k e (a, b) (h, (f, g))). }
    transitivity (afr_inner_med a (b ⨂[M] d)%object
      (k ∘ bimap[@tensor C M] h (@id C d) ∘ (@tensor_assoc C M a b d)⁻¹) f
      (ci (DayI G H (b ⨂[M] d)%object) (b, d)
         (@id C (b ⨂[M] d)%object, (g, e)))).
    { exact (coend_med_inj (SetsCoend (DayI F (Day G H) c))
               (coend_obj (SetsCoend (DayI (Day F G) H c)))
               afr_outer_leg afr_outer_cowedge (a, (b ⨂[M] d)%object)
               (k ∘ bimap[@tensor C M] h (@id C d) ∘ (@tensor_assoc C M a b d)⁻¹,
                (f, ci (DayI G H (b ⨂[M] d)%object) (b, d)
                       (@id C (b ⨂[M] d)%object, (g, e))))). }
    transitivity (afr_inner_leg a (b ⨂[M] d)%object
      (k ∘ bimap[@tensor C M] h (@id C d) ∘ (@tensor_assoc C M a b d)⁻¹) f
      (b, d) (@id C (b ⨂[M] d)%object, (g, e))).
    { exact (afr_inner_med_ci a (b ⨂[M] d)%object
               (k ∘ bimap[@tensor C M] h (@id C d) ∘ (@tensor_assoc C M a b d)⁻¹) f
               (b, d) (@id C (b ⨂[M] d)%object, (g, e))). }
    transitivity (ci (DayI (Day F G) H c) ((a ⨂[M] b)%object, d)
      (bimap[DayI (Day F G) H c] (op φ') (@id (C ∏ C) _) elt')).
    { apply ce_point; simpl; split; [ | split ].
      - rewrite bimap_id_id, id_right, <- comp_assoc, iso_from_to, id_right;
          reflexivity.
      - apply ce_sym; apply (fmap_id_app (Day F G)).
      - symmetry; apply fmap_id_app. }
    transitivity (ci (DayI (Day F G) H c) (p, d)
      (bimap[DayI (Day F G) H c] (@id (C ∏ C) _) φ' elt')).
    { exact (ce_glue (DayI (Day F G) H c) ((a ⨂[M] b)%object, d) (p, d) φ' elt'). }
    apply ce_point; simpl; split; [ | split ].
    + rewrite bimap_id_id; rewrite id_right; reflexivity.
    + apply (ce_trans (DayI F G p) _
        (ci (DayI F G p) (a, b) (h ∘ @id C (a ⨂[M] b)%object, (f, g))) _).
      { exact (Day_map_inj F G (a ⨂[M] b)%object p h (a, b)
                 (@id C (a ⨂[M] b)%object, (f, g))). }
      apply ce_point; simpl; split; [ | split ].
      * rewrite id_right; reflexivity.
      * reflexivity.
      * reflexivity.
    + apply fmap_id_app.
  - intro ab; reflexivity.
Qed.

Lemma assoc_from_to : assoc_from ∘ assoc_to ≈ id.
Proof.
  apply (coend_med_eq (SetsCoend (DayI (Day F G) H c))
    (coend_obj (SetsCoend (DayI (Day F G) H c)))
    (fun pd => @coend_inj (C ∏ C) Sets (DayI (Day F G) H c)
                 (SetsCoend (DayI (Day F G) H c)) pd)
    (fun x y f => @coend_cowedge (C ∏ C) Sets (DayI (Day F G) H c)
                    (SetsCoend (DayI (Day F G) H c)) x y f)
    (assoc_from ∘ assoc_to) id).
  - intros [p d] [k [W e]].
    transitivity (assoc_from (ato_inner_med p d k e W)).
    + apply (proper_morphism assoc_from).
      exact (coend_med_inj (SetsCoend (DayI (Day F G) H c))
               (coend_obj (SetsCoend (DayI F (Day G H) c)))
               ato_outer_leg ato_outer_cowedge (p, d) (k, (W, e))).
    + exact (round_from_to p d k e W).
  - intros [p d] elt; reflexivity.
Qed.

(* The pointwise associator isomorphism [Day (Day F G) H c ≅ Day F (Day G H) c]. *)
Program Definition assoc_iso_pt :
  coend_obj (SetsCoend (DayI (Day F G) H c))
    ≅[Sets] coend_obj (SetsCoend (DayI F (Day G H) c)) := {|
  to   := assoc_to;
  from := assoc_from |}.
Next Obligation. exact assoc_to_from. Qed.
Next Obligation. exact assoc_from_to. Qed.

End Associator.

(* ---------------------------------------------------------------- *)
(* Naturality in [c] and the natural associator isomorphism.         *)
(* ---------------------------------------------------------------- *)

Section AssocNat.
Context (F G H : C ⟶ Sets).

(* Naturality of the forward associator in the coend variable [c]. On a
   generator both sides collapse to the same [ci], differing only by the
   reassociation [k ∘ (kk ∘ …) = (k ∘ kk) ∘ …]. *)
Lemma assoc_to_natural (c1 c2 : C) (k : c1 ~{C}~> c2) :
  Day_map F (Day G H) c1 c2 k ∘ assoc_to F G H c1
    ≈ assoc_to F G H c2 ∘ Day_map (Day F G) H c1 c2 k.
Proof.
  apply (coend_med_eq (SetsCoend (DayI (Day F G) H c1))
    (coend_obj (SetsCoend (DayI F (Day G H) c2)))
    (fun pd => (Day_map F (Day G H) c1 c2 k ∘ assoc_to F G H c1)
               ∘ @coend_inj (C ∏ C) Sets (DayI (Day F G) H c1)
                   (SetsCoend (DayI (Day F G) H c1)) pd)
    (postcompose_cowedge (DayI (Day F G) H c1) (SetsCoend (DayI (Day F G) H c1))
       (coend_obj (SetsCoend (DayI F (Day G H) c2)))
       (Day_map F (Day G H) c1 c2 k ∘ assoc_to F G H c1))
    (Day_map F (Day G H) c1 c2 k ∘ assoc_to F G H c1)
    (assoc_to F G H c2 ∘ Day_map (Day F G) H c1 c2 k)).
  - intro pd; reflexivity.
  - intros [p d] [kk [W e]].
    destruct W as [[a b] [h [f g]]].
    transitivity (ci (DayI F (Day G H) c2) (a, (b ⨂[M] d)%object)
      (k ∘ kk ∘ bimap[@tensor C M] h (@id C d) ∘ (@tensor_assoc C M a b d)⁻¹,
       (f, ci (DayI G H (b ⨂[M] d)%object) (b, d)
              (@id C (b ⨂[M] d)%object, (g, e))))).
    { transitivity (assoc_to F G H c2
        (ci (DayI (Day F G) H c2) (p, d)
           (k ∘ kk, (ci (DayI F G p) (a, b) (h, (f, g)), e)))).
      { apply (proper_morphism (assoc_to F G H c2)).
        exact (Day_map_inj (Day F G) H c1 c2 k (p, d)
                 (kk, (ci (DayI F G p) (a, b) (h, (f, g)), e))). }
      transitivity (ato_inner_med F G H c2 p d (k ∘ kk) e
        (ci (DayI F G p) (a, b) (h, (f, g)))).
      { exact (coend_med_inj (SetsCoend (DayI (Day F G) H c2))
                 (coend_obj (SetsCoend (DayI F (Day G H) c2)))
                 (ato_outer_leg F G H c2) (ato_outer_cowedge F G H c2) (p, d)
                 (k ∘ kk, (ci (DayI F G p) (a, b) (h, (f, g)), e))). }
      exact (ato_inner_med_ci F G H c2 p d (k ∘ kk) e (a, b) (h, (f, g))). }
    symmetry.
    transitivity (ci (DayI F (Day G H) c2) (a, (b ⨂[M] d)%object)
      (k ∘ (kk ∘ bimap[@tensor C M] h (@id C d) ∘ (@tensor_assoc C M a b d)⁻¹),
       (f, ci (DayI G H (b ⨂[M] d)%object) (b, d)
              (@id C (b ⨂[M] d)%object, (g, e))))).
    { transitivity (Day_map F (Day G H) c1 c2 k
        (ato_inner_leg F G H c1 p d kk e (a, b) (h, (f, g)))).
      { apply (proper_morphism (Day_map F (Day G H) c1 c2 k)).
        transitivity (ato_inner_med F G H c1 p d kk e
          (ci (DayI F G p) (a, b) (h, (f, g)))).
        { exact (coend_med_inj (SetsCoend (DayI (Day F G) H c1))
                   (coend_obj (SetsCoend (DayI F (Day G H) c1)))
                   (ato_outer_leg F G H c1) (ato_outer_cowedge F G H c1) (p, d)
                   (kk, (ci (DayI F G p) (a, b) (h, (f, g)), e))). }
        exact (ato_inner_med_ci F G H c1 p d kk e (a, b) (h, (f, g))). }
      exact (Day_map_inj F (Day G H) c1 c2 k (a, (b ⨂[M] d)%object)
               (kk ∘ bimap[@tensor C M] h (@id C d) ∘ (@tensor_assoc C M a b d)⁻¹,
                (f, ci (DayI G H (b ⨂[M] d)%object) (b, d)
                       (@id C (b ⨂[M] d)%object, (g, e))))). }
    apply ce_point; simpl; split; [ | split ].
    + rewrite !comp_assoc; reflexivity.
    + reflexivity.
    + apply ce_point; simpl; split; [ reflexivity | split; reflexivity ].
Qed.

(* The natural associator isomorphism [Day (Day F G) H ≅ Day F (Day G H)]
   in [[C, Sets]]. *)
Definition day_assoc_iso : Day (Day F G) H ≅[Fun] Day F (Day G H).
Proof.
  apply equiv_iso.
  exists (fun c => assoc_iso_pt F G H c).
  intros c1 c2 k.
  change (from (assoc_iso_pt F G H c2)) with (assoc_from F G H c2).
  change (to (assoc_iso_pt F G H c1)) with (assoc_to F G H c1).
  symmetry.
  rewrite <- comp_assoc.
  rewrite (assoc_to_natural c1 c2 k).
  rewrite comp_assoc.
  change (assoc_from F G H c2 ∘ assoc_to F G H c2)
    with (from (assoc_iso_pt F G H c2) ∘ to (assoc_iso_pt F G H c2)).
  rewrite (iso_from_to (assoc_iso_pt F G H c2)).
  apply id_left.
Defined.

End AssocNat.

End Day.
