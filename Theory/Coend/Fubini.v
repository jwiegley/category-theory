Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.End.
Require Import Category.Structure.Coend.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Coend.

Generalizable All Variables.

(** Element-level readings of the functor laws for a [Sets]-valued functor. *)
Local Lemma fmap_id_app {K : Category} (G : K ⟶ Sets) {x : K} (z : G x) :
  fmap[G] (@id K x) z ≈ z.
Proof. exact (@fmap_id K Sets G x z). Qed.

Local Lemma fmap_comp_app {K : Category} (G : K ⟶ Sets) {x y z : K}
  (g : y ~{K}~> z) (f : x ~{K}~> y) (w : G x) :
  fmap[G] (g ∘ f) w ≈ fmap[G] g (fmap[G] f w).
Proof. exact (@fmap_comp K Sets G x y z g f w). Qed.

(** Collapse a two-fold [fmap] into a single one along a morphism equality:
    the workhorse for the coend bookkeeping below. *)
Local Lemma fmap_two {K : Category} (G : K ⟶ Sets) {x y z : K}
  (m1 : y ~{K}~> z) (m2 : x ~{K}~> y) (m3 : x ~{K}~> z)
  (Hm : m1 ∘ m2 ≈ m3) (w : G x) :
  fmap[G] m1 (fmap[G] m2 w) ≈ fmap[G] m3 w.
Proof.
  transitivity (fmap[G] (m1 ∘ m2) w).
  - symmetry; apply fmap_comp_app.
  - exact (@fmap_respects _ _ G _ _ (m1 ∘ m2) m3 Hm w).
Qed.

Section Fubini.

Context {C D : Category}.
Context (H : (C ∏ D)^op ∏ (C ∏ D) ⟶ Sets).

(** The inner integrand at fixed [c1 c2 : C]: the [D]-profunctor
    [(d1, d2) ↦ H ((c1, d1), (c2, d2))], contravariant in [d1], covariant in
    [d2], obtained by holding the [C]-coordinates fixed at [c1], [c2]. *)
(** The action of [H] on a "rectangle" of moves: a contravariant [C]-move [u],
    a covariant [C]-move [v], a contravariant [D]-move [g1] and a covariant
    [D]-move [g2], with every object explicit so that no projection sits inside
    the morphism literal (which is what makes Coq insert [eq_rect] transports).
    This single engine drives every functorial action below; the inner coend
    fixes [u], [v] at identities, the [Inner] functor fixes [g1], [g2] at
    identities, and every composition collapses through [Hact_comp]. *)
Definition Hact (c1 c2 c1' c2' : C) (d1 d2 d1' d2' : D)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2')
  (g1 : d1' ~{D}~> d1) (g2 : d2 ~{D}~> d2') :
  H ((c1, d1), (c2, d2)) ~{Sets}~> H ((c1', d1'), (c2', d2')) :=
  fmap[H] (((u, g1), (v, g2))
             : ((c1, d1), (c2, d2))
                 ~{(C ∏ D)^op ∏ (C ∏ D)}~> ((c1', d1'), (c2', d2'))).

(** [Hact] at all identities is the identity of [H]. *)
Lemma Hact_id (c1 c2 : C) (d1 d2 : D) (w : H ((c1, d1), (c2, d2))) :
  Hact c1 c2 c1 c2 d1 d2 d1 d2
    (@id C c1) (@id C c2) (@id D d1) (@id D d2) w ≈ w.
Proof. exact (fmap_id_app H w). Qed.

(** [Hact] respects [≈] in all four morphism arguments. *)
Lemma Hact_respects (c1 c2 c1' c2' : C) (d1 d2 d1' d2' : D)
  (u u' : c1' ~{C}~> c1) (v v' : c2 ~{C}~> c2')
  (g1 g1' : d1' ~{D}~> d1) (g2 g2' : d2 ~{D}~> d2')
  (Hu : u ≈ u') (Hv : v ≈ v') (Hg1 : g1 ≈ g1') (Hg2 : g2 ≈ g2')
  (w : H ((c1, d1), (c2, d2))) :
  Hact c1 c2 c1' c2' d1 d2 d1' d2' u v g1 g2 w
    ≈ Hact c1 c2 c1' c2' d1 d2 d1' d2' u' v' g1' g2' w.
Proof.
  unfold Hact.
  refine (@fmap_respects _ _ H _ _ _ _ _ w).
  split; split; simpl; assumption.
Qed.

(** Composing two [Hact]s collapses to a single one: the contravariant legs
    ([u], [g1]) compose reversed (they live in the opposite factors, which is
    definitional), the covariant legs ([v], [g2]) forwards. *)
Lemma Hact_comp (c1 c2 c1' c2' c1'' c2'' : C) (d1 d2 d1' d2' d1'' d2'' : D)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2')
  (u' : c1'' ~{C}~> c1') (v' : c2' ~{C}~> c2'')
  (g1 : d1' ~{D}~> d1) (g2 : d2 ~{D}~> d2')
  (g1' : d1'' ~{D}~> d1') (g2' : d2' ~{D}~> d2'')
  (w : H ((c1, d1), (c2, d2))) :
  Hact c1' c2' c1'' c2'' d1' d2' d1'' d2'' u' v' g1' g2'
    (Hact c1 c2 c1' c2' d1 d2 d1' d2' u v g1 g2 w)
    ≈ Hact c1 c2 c1'' c2'' d1 d2 d1'' d2''
        (u ∘ u') (v' ∘ v) (g1 ∘ g1') (g2' ∘ g2) w.
Proof.
  unfold Hact.
  apply fmap_two.
  reflexivity.
Qed.

(** A [Hact_comp] variant that also rewrites the four composed morphisms to
    chosen targets, so callers can absorb the identity laws in one step. *)
Lemma Hact_comp_clean (c1 c2 c1' c2' c1'' c2'' : C)
  (d1 d2 d1' d2' d1'' d2'' : D)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2')
  (u' : c1'' ~{C}~> c1') (v' : c2' ~{C}~> c2'')
  (g1 : d1' ~{D}~> d1) (g2 : d2 ~{D}~> d2')
  (g1' : d1'' ~{D}~> d1') (g2' : d2' ~{D}~> d2'')
  (uu : c1'' ~{C}~> c1) (vv : c2 ~{C}~> c2'')
  (gg1 : d1'' ~{D}~> d1) (gg2 : d2 ~{D}~> d2'')
  (Hu : u ∘ u' ≈ uu) (Hv : v' ∘ v ≈ vv)
  (Hg1 : g1 ∘ g1' ≈ gg1) (Hg2 : g2' ∘ g2 ≈ gg2)
  (w : H ((c1, d1), (c2, d2))) :
  Hact c1' c2' c1'' c2'' d1' d2' d1'' d2'' u' v' g1' g2'
    (Hact c1 c2 c1' c2' d1 d2 d1' d2' u v g1 g2 w)
    ≈ Hact c1 c2 c1'' c2'' d1 d2 d1'' d2'' uu vv gg1 gg2 w.
Proof.
  transitivity (Hact c1 c2 c1'' c2'' d1 d2 d1'' d2''
                  (u ∘ u') (v' ∘ v) (g1 ∘ g1') (g2' ∘ g2) w).
  - apply Hact_comp.
  - apply Hact_respects; assumption.
Qed.

(** The inner integrand at fixed [c1 c2 : C]: the [D]-profunctor
    [(d1, d2) ↦ H ((c1, d1), (c2, d2))], its functorial action being [Hact]
    with the [C]-coordinates held at identities. *)
Program Definition InnerIntegrand (c1 c2 : C) : D^op ∏ D ⟶ Sets := {|
  fobj := fun dp => H ((c1, fst dp), (c2, snd dp));
  fmap := fun dp dq g =>
    Hact c1 c2 c1 c2 (fst dp) (snd dp) (fst dq) (snd dq)
      (@id C c1) (@id C c2) (fst g) (snd g)
|}.
Next Obligation.
  unfold Proper, respectful; intros g g' [Hg1 Hg2] x.
  apply Hact_respects; try reflexivity; assumption.
Qed.
Next Obligation. apply Hact_id. Qed.
Next Obligation.
  transitivity (Hact c1 c2 c1 c2 o3 o4 o o0
                  (id ∘ id) (id ∘ id) (h ∘ h1) (h2 ∘ h0) x0).
  - apply Hact_respects;
      [ symmetry; apply id_left | symmetry; apply id_left
      | reflexivity | reflexivity ].
  - symmetry; apply Hact_comp.
Qed.

(** The leg at [d] of the [Inner]-functorial action of a [C]-move [(u, v)]:
    apply the [C]-move by [Hact] (identities on the [D]-coordinate) and inject
    into the inner coend at [c1', c2']. *)
Program Definition outer_leg (c1 c2 c1' c2' : C)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2') (d : D) :
  SetoidMorphism (InnerIntegrand c1 c2 (d, d))
                 (coend_apex_setoid (InnerIntegrand c1' c2')) :=
  {| morphism := fun w =>
       ci (InnerIntegrand c1' c2') d
         (Hact c1 c2 c1' c2' d d d d u v (@id D d) (@id D d) w) |}.
Next Obligation.
  unfold Proper, respectful; intros w w' Hww'.
  apply ce_point.
  apply proper_morphism; exact Hww'.
Qed.

Lemma outer_leg_cond (c1 c2 c1' c2' : C)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2') :
  Cowedge_cond (InnerIntegrand c1 c2)
    (coend_apex_setoid (InnerIntegrand c1' c2'))
    (outer_leg c1 c2 c1' c2' u v).
Proof.
  unfold Cowedge_cond; intros x y f a; simpl.
  (* The two nested [Hact]s collapse to the [InnerIntegrand c1' c2'] cowedge
     legs applied to [w''], and the middle step is that coend's own glue. *)
  pose (w'' := Hact c1 c2 c1' c2' y x y x u v (@id D y) (@id D x) a).
  apply (ce_trans (InnerIntegrand c1' c2') _
           (ci (InnerIntegrand c1' c2') x
              (Hact c1' c2' c1' c2' y x x x
                 (@id C c1') (@id C c2') (op f) (@id D x) w''))).
  { apply ce_point.
    transitivity (Hact c1 c2 c1' c2' y x x x u v (op f) (@id D x) a).
    - apply Hact_comp_clean;
        [ apply id_left | apply id_right | apply id_right | apply id_left ].
    - symmetry; apply Hact_comp_clean;
        [ apply id_right | apply id_left | apply id_left | apply id_left ]. }
  apply (ce_trans (InnerIntegrand c1' c2') _
           (ci (InnerIntegrand c1' c2') y
              (Hact c1' c2' c1' c2' y x y y
                 (@id C c1') (@id C c2') (@id D y) f w''))).
  { exact (ce_glue (InnerIntegrand c1' c2') x y f w''). }
  apply ce_point.
  transitivity (Hact c1 c2 c1' c2' y x y y u v (@id D y) f a).
  - apply Hact_comp_clean;
      [ apply id_right | apply id_left | apply id_left | apply id_right ].
  - symmetry; apply Hact_comp_clean;
      [ apply id_left | apply id_right | apply id_left | apply id_left ].
Qed.

(** The [Inner]-functorial action of a [C]-move as the coend mediator of the
    legs above. *)
Definition inner_fmap (c1 c2 c1' c2' : C)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2') :
  coend_apex_setoid (InnerIntegrand c1 c2)
    ~{Sets}~> coend_apex_setoid (InnerIntegrand c1' c2') :=
  coend_mediator (InnerIntegrand c1 c2)
    (outer_leg c1 c2 c1' c2' u v) (outer_leg_cond c1 c2 c1' c2' u v).

(** Computation rule of the mediator on a generator (definitional). *)
Lemma inner_fmap_ci (c1 c2 c1' c2' : C)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2') (d : D)
  (w : H ((c1, d), (c2, d))) :
  inner_fmap c1 c2 c1' c2' u v (ci (InnerIntegrand c1 c2) d w)
    ≈ ci (InnerIntegrand c1' c2') d
        (Hact c1 c2 c1' c2' d d d d u v (@id D d) (@id D d) w).
Proof. reflexivity. Qed.

(** The iterated-coend functor [Inner (c1, c2) = ∫^d H ((c1, d), (c2, d))],
    contravariant in [c1], covariant in [c2]. *)
Program Definition Inner : C^op ∏ C ⟶ Sets := {|
  fobj := fun p => coend_apex_setoid (InnerIntegrand (fst p) (snd p));
  fmap := fun p q uv =>
    inner_fmap (fst p) (snd p) (fst q) (snd q) (fst uv) (snd uv)
|}.
Next Obligation.
  unfold Proper, respectful; intros uv uv' [Huv1 Huv2].
  apply (coend_med_eq (SetsCoend (InnerIntegrand o1 o2))
           (coend_apex_setoid (InnerIntegrand o o0))
           (outer_leg o1 o2 o o0 (fst uv') (snd uv'))
           (outer_leg_cond o1 o2 o o0 (fst uv') (snd uv'))).
  - intros d w.
    transitivity (ci (InnerIntegrand o o0) d
                    (Hact o1 o2 o o0 d d d d (fst uv) (snd uv)
                       (@id D d) (@id D d) w)).
    + apply inner_fmap_ci.
    + apply ce_point.
      apply Hact_respects; [ exact Huv1 | exact Huv2 | reflexivity | reflexivity ].
  - intros d w.
    apply inner_fmap_ci.
Qed.
Next Obligation.
  destruct x0 as [d w].
  apply ce_point.
  apply Hact_id.
Qed.
Next Obligation.
  destruct x0 as [d w].
  apply ce_point.
  symmetry.
  apply Hact_comp_clean;
    [ reflexivity | reflexivity | apply id_left | apply id_left ].
Qed.

(** The diagonal contravariant image [bimap[H] (op (u,g)) id] in [Hact] form;
    a definitional identity, phrased with an explicit hom annotation so the pair
    [(u, g)] elaborates as a [C ∏ D] morphism rather than a bare product. *)
Local Lemma bimap_diag (c1 c2 : C) (d1 d2 : D)
  (u : c1 ~{C}~> c2) (g : d1 ~{D}~> d2) (w : H ((c2, d2), (c1, d1))) :
  bimap[H] (op ((u, g) : (c1, d1) ~{C ∏ D}~> (c2, d2))) (id, id) w
    ≈ Hact c2 c1 c1 c1 d2 d1 d1 d1 u (@id C c1) g (@id D d1) w.
Proof. reflexivity. Qed.

(** The diagonal covariant image [bimap[H] id (op-free) (u,g)] in [Hact] form. *)
Local Lemma bimap_codiag (c1 c2 : C) (d1 d2 : D)
  (u : c1 ~{C}~> c2) (g : d1 ~{D}~> d2) (w : H ((c2, d2), (c1, d1))) :
  bimap[H] (id, id) ((u, g) : (c1, d1) ~{C ∏ D}~> (c2, d2)) w
    ≈ Hact c2 c1 c2 c2 d2 d1 d2 d2 (@id C c2) u (@id D d2) g w.
Proof. reflexivity. Qed.

(** ** The Fubini comparison [∫^{(c,d)} H ≅ ∫^c ∫^d H] *)

(** Forward leg at [(c, d)]: [h ↦ ci c (ci d h)] (outer over [C] of inner over
    [D]). *)
Program Definition fwd_leg (cd : C ∏ D) :
  SetoidMorphism (H (cd, cd)) (coend_apex_setoid Inner) :=
  match cd as cd0
    return SetoidMorphism (H (cd0, cd0)) (coend_apex_setoid Inner) with
  | (c, d) =>
      {| morphism := fun h => ci Inner c (ci (InnerIntegrand c c) d h) |}
  end.
Next Obligation.
  unfold Proper, respectful; intros h h' Hh.
  apply ce_point; apply ce_point; exact Hh.
Qed.

Lemma fwd_cond : Cowedge_cond H (coend_apex_setoid Inner) fwd_leg.
Proof.
  unfold Cowedge_cond; intros x y f a.
  destruct x as [c1 d1], y as [c2 d2], f as [fc fd]; simpl.
  (* The two witnesses moving [a] partway around the square. *)
  pose (b1 := Hact c2 c1 c1 c1 d2 d1 d2 d1 fc (@id C c1) (@id D d2) (@id D d1) a).
  pose (a2 := Hact c2 c1 c2 c1 d2 d1 d2 d2 (@id C c2) (@id C c1) (@id D d2) fd a).
  (* Step 1: rewrite the diagonal image as the inner [op fd]-image of [b1]. *)
  apply (ce_trans Inner _
    (ci Inner c1 (ci (InnerIntegrand c1 c1) d1
       (Hact c1 c1 c1 c1 d2 d1 d1 d1 (@id C c1) (@id C c1) fd (@id D d1) b1)))).
  { apply ce_point; apply ce_point.
    rewrite (bimap_diag c1 c2 d1 d2 fc fd a); subst b1; symmetry.
    apply Hact_comp_clean;
      [ apply id_right | apply id_left | apply id_left | apply id_left ]. }
  (* Step 2: the inner [D]-coend glue at [c1] for [fd]. *)
  apply (ce_trans Inner _
    (ci Inner c1 (ci (InnerIntegrand c1 c1) d2
       (Hact c1 c1 c1 c1 d2 d1 d2 d2 (@id C c1) (@id C c1) (@id D d2) fd b1)))).
  { apply ce_point; exact (ce_glue (InnerIntegrand c1 c1) d1 d2 fd b1). }
  (* Step 3: collapse the inner image to [Z]. *)
  apply (ce_trans Inner _
    (ci Inner c1 (ci (InnerIntegrand c1 c1) d2
       (Hact c2 c1 c1 c1 d2 d1 d2 d2 fc (@id C c1) (@id D d2) fd a)))).
  { apply ce_point; apply ce_point; subst b1.
    apply Hact_comp_clean;
      [ apply id_right | apply id_left | apply id_left | apply id_right ]. }
  (* Step 4: exhibit [Z] as the outer [op fc]-image of [ci d2 a2]. *)
  apply (ce_trans Inner _
    (ci Inner c1 (inner_fmap c2 c1 c1 c1 fc (@id C c1)
       (ci (InnerIntegrand c2 c1) d2 a2)))).
  { apply ce_point.
    transitivity (ci (InnerIntegrand c1 c1) d2
                    (Hact c2 c1 c1 c1 d2 d2 d2 d2 fc (@id C c1)
                       (@id D d2) (@id D d2) a2)).
    - apply ce_point; subst a2; symmetry.
      apply Hact_comp_clean;
        [ apply id_left | apply id_left | apply id_left | apply id_left ].
    - symmetry; apply inner_fmap_ci. }
  (* Step 5: the outer [C]-coend glue for [fc]. *)
  apply (ce_trans Inner _
    (ci Inner c2 (inner_fmap c2 c1 c2 c2 (@id C c2) fc
       (ci (InnerIntegrand c2 c1) d2 a2)))).
  { exact (ce_glue Inner c1 c2 fc (ci (InnerIntegrand c2 c1) d2 a2)). }
  (* Step 6: collapse the outer image to [Y]. *)
  apply ce_point.
  transitivity (ci (InnerIntegrand c2 c2) d2
                  (Hact c2 c1 c2 c2 d2 d2 d2 d2 (@id C c2) fc
                     (@id D d2) (@id D d2) a2)).
  - apply inner_fmap_ci.
  - apply ce_point.
    rewrite (bimap_codiag c1 c2 d1 d2 fc fd a); subst a2.
    apply Hact_comp_clean;
      [ apply id_left | apply id_right | apply id_left | apply id_left ].
Qed.

(** The forward comparison map [∫^{(c,d)} H → ∫^c ∫^d H]. *)
Definition fwd :
  coend_apex_setoid H ~{Sets}~> coend_apex_setoid Inner :=
  coend_mediator H fwd_leg fwd_cond.

(** Post-composing a coend morphism onto the injections yields a cowedge: the
    legs [fun x => m ∘ coend_inj E] inherit their glue from [E]'s own. *)
Lemma postcompose_cowedge {K : Category} (G : K^op ∏ K ⟶ Sets)
  (E : Coend G) (Q : SetoidObject) (m : coend_obj E ~{Sets}~> Q) :
  Cowedge_cond G Q (fun x => m ∘ @coend_inj K Sets G E x).
Proof.
  intros x y f.
  rewrite <- !comp_assoc, (coend_cowedge E f).
  reflexivity.
Qed.

(** Backward inner cowedge at [c]: inject [∫^d H((c,d),(c,d))] into [∫ H] by
    landing at index [(c, d)]; the [D]-glue for [g] is [H]'s own glue at the
    pair morphism [(id, g)]. *)
Lemma bwd_inner_cond (c : C) :
  Cowedge_cond (InnerIntegrand c c) (coend_apex_setoid H)
    (fun d => coend_inj_mor H (c, d)).
Proof.
  intros d1 d2 g a.
  exact (ce_glue H (c, d1) (c, d2) (id, g) a).
Qed.

(** Backward leg at [c]: the mediator [∫^d H((c,d),(c,d)) → ∫ H].  Its domain
    is stated as [Inner (c, c)] (definitionally the inner coend apex) so that
    the compositions with [bimap[Inner]] below resolve their category. *)
Definition bwd_leg (c : C) :
  Inner (c, c) ~{Sets}~> coend_apex_setoid H :=
  coend_mediator (InnerIntegrand c c) (fun d => coend_inj_mor H (c, d))
    (bwd_inner_cond c).

(** Backward outer cowedge: the [C]-glue for [fc] reduces, on generators, to a
    single [H]-glue at the pair morphism [(fc, id)]; the two sides agree with
    the common cowedge [fun d => bwd_leg c1 ∘ bimap[Inner] (op fc) id ∘ inj_d]. *)
Lemma bwd_cond : Cowedge_cond Inner (coend_apex_setoid H) bwd_leg.
Proof.
  intros c1 c2 fc.
  apply (coend_med_eq (SetsCoend (InnerIntegrand c2 c1)) (coend_apex_setoid H)
    (fun d => (bwd_leg c1 ∘ bimap[Inner] (op fc) id)
              ∘ @coend_inj D Sets (InnerIntegrand c2 c1)
                  (SetsCoend (InnerIntegrand c2 c1)) d)
    (postcompose_cowedge (InnerIntegrand c2 c1)
       (SetsCoend (InnerIntegrand c2 c1)) (coend_apex_setoid H)
       (bwd_leg c1 ∘ bimap[Inner] (op fc) id))
    (bwd_leg c1 ∘ bimap[Inner] (op fc) id)
    (bwd_leg c2 ∘ bimap[Inner] id fc)).
  - intro d; reflexivity.
  - intros d w.
    symmetry.
    exact (ce_glue H (c1, d) (c2, d) (fc, id) w).
Qed.

(** The backward comparison map [∫^c ∫^d H → ∫^{(c,d)} H]. *)
Definition bwd :
  coend_apex_setoid Inner ~{Sets}~> coend_apex_setoid H :=
  coend_mediator Inner bwd_leg bwd_cond.

(** [fwd] undoes [bwd_leg] fibrewise: on a generator [ci d h] both send it to
    [ci c (ci d h)]. *)
Lemma fwd_bwd_leg (c : C) :
  fwd ∘ bwd_leg c ≈ coend_inj_mor Inner c.
Proof.
  apply (coend_med_eq (SetsCoend (InnerIntegrand c c)) (coend_apex_setoid Inner)
    (fun d => (coend_inj_mor Inner c
                 : Inner (c, c) ~{Sets}~> coend_apex_setoid Inner)
              ∘ @coend_inj D Sets (InnerIntegrand c c)
                  (SetsCoend (InnerIntegrand c c)) d)
    (postcompose_cowedge (InnerIntegrand c c)
       (SetsCoend (InnerIntegrand c c)) (coend_apex_setoid Inner)
       (coend_inj_mor Inner c))
    (fwd ∘ bwd_leg c) (coend_inj_mor Inner c)).
  - intros d h; reflexivity.
  - intro d; reflexivity.
Qed.

(** Round trip on [∫^c ∫^d H]: [fwd ∘ bwd ≈ id]. *)
Lemma fubini_to_from : fwd ∘ bwd ≈ id.
Proof.
  apply (coend_med_eq (SetsCoend Inner) (coend_apex_setoid Inner)
    (coend_inj_mor Inner) (coend_apex_cowedge Inner) (fwd ∘ bwd) id).
  - intro c.
    transitivity (fwd ∘ bwd_leg c).
    + intro s; reflexivity.
    + exact (fwd_bwd_leg c).
  - intros c s; reflexivity.
Qed.

(** Round trip on [∫^{(c,d)} H]: [bwd ∘ fwd ≈ id]. *)
Lemma fubini_from_to : bwd ∘ fwd ≈ id.
Proof.
  apply (coend_med_eq (SetsCoend H) (coend_apex_setoid H)
    (coend_inj_mor H) (coend_apex_cowedge H) (bwd ∘ fwd) id).
  - intro p; destruct p as [c d]; intros h; reflexivity.
  - intros p h; reflexivity.
Qed.

(** The Fubini isomorphism [∫^{(c,d)} H ≅ ∫^c ∫^d H] in [Sets]. *)
Definition coend_fubini :
  coend_obj (SetsCoend H) ≅[Sets] coend_obj (SetsCoend Inner) :=
  {| to := fwd;
     from := bwd;
     iso_to_from := fubini_to_from;
     iso_from_to := fubini_from_to |}.

End Fubini.
