Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Construction.Slice.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Pullback.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Continuity.

Set Universe Polymorphism.

Generalizable All Variables.

(** * Creation of limits is stable under the fibre product of categories *)

(* nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/pullback

   Mac Lane §V.6 Exercises 3 and 4 (book p. 125).  Exercise 3 asks that
   creation of limits be stable under pullback in [Cat]: given a cospan
   [F : A ⟶ C], [G : B ⟶ C] and the pullback [P] of the two, if [F] creates
   the limits [G] preserves then the projection [P ⟶ B] creates them.
   Exercise 4 asks that the comma category be recovered as such a pullback,
   giving a second proof that its projection creates limits.

   READ THE FIRST WORD OF THAT PRECISELY, because the tree already refutes
   the naive reading.  Instance/Cat/Pullback.v proves
   [FibreProduct_not_Cat_pullback]: the fibre product of categories is NOT a
   pullback in [Cat].  Read THAT narrowly in turn, as its own file insists
   (Instance/Cat/Pullback.v:64-67, :553-555): it is a refutation AT ONE
   COSPAN, [1 --true--> Indiscrete bool <--false-- 1], where the apex is
   object-empty; the same cospan does have a [Cat] pullback, and nothing in
   the tree refutes [FibreProduct (Coslice_Proj d) U] as a [Cat] pullback of
   ITS cospan.  (An earlier revision of this header, of the commit message
   and of the docs/INDEX.md bullet said the coslice apex was "refuted for
   this object"; measured, the refutation is at the [Indiscrete bool]
   cospan and says nothing about the coslice one.)  What the fibre product
   is is a pullback in [StrictCat], and even there only under [ObjUIP C]
   ([FibreProduct_IsPullback]); whether [Cat] has pullbacks at all is
   neither proved nor refuted anywhere.  So the honest Exercise 3 is a
   theorem about [FibreProduct] — the object that IS the pullback where the
   tree can say so — and that is what is proved here.  Nothing below asserts
   a pullback square in [Cat].

   Two things are worth naming before the statements.

   First, this proof needs NO [ObjUIP].  It never touches
   [FibreProduct_IsPullback]; it works with the apex's own data, the stored
   equality [`2 (K j) : F (KA j) = G (KB j)] and the stored cast condition
   on arrows, both of which are definitional.  The printed type of
   [fp_snd_StrictlyCreatesLimit] carries no [uip] argument.

   Second, what it DOES need is that the bottom functor create limits
   STRICTLY, not merely up to isomorphism.  The created apex pairs the
   upstairs lift's vertex with the given cone's and stores [slift_eq] as its
   third component, and that component must be a Leibniz [=] because that is
   what an object of a fibre product stores; an isomorphism will not go in
   its place.
   Test/ProbeCatCreation439.v's negative n3 records the refusal against the
   accepted control beside it.  In exchange the conclusion is strict too:
   both [StrictLift] fields come out [eq_refl] and [reflexivity], at every
   limiting cone downstairs.

   The generic kit — [CreatesLimit_transport] and the [IsLimitCone]
   transport it rests on — is not about [Cat] at all, and its natural home
   is Structure/Limit/Creation.v, where appending is line-neutral for all
   fifteen of that file's citations (the highest is :440, the upper
   endpoint of the range cited at doc/plan/books/qa; an earlier revision of
   this sentence said :439, the highest single-line citation, and both are
   inside the 518-line file).  It lives here instead, for this change,
   because that costs no rebuild of that file's large reverse-dependency
   set and because it is where #428 put the analogous
   [PreservesLimitCone_transport] (Functor/Hom/Continuous.v:367).  A later
   move costs nothing.

   Of the two [IsLimitCone] transports below only [islimitcone_dtransport_inv]
   is consumed; [islimitcone_dtransport] is its mirror image, shipped for
   symmetry with NO consumer in this file or anywhere in the tree.  An
   earlier revision of this sentence said the kit rests on both.

   Two further disclosures of prior art, neither of them reuse.
   [fp_square_iso] re-derives a fact Instance/Cat/Pullback.v:388 already
   carries as [FP_commutes_cat : F ∘[Cat] FP_fst ≈[Cat] G ∘[Cat] FP_snd]:
   whiskering that with this file's own [fun_equiv_whisker_r] typechecks at
   exactly [fp_square_iso]'s type, though the two terms are not convertible.
   And [fun_equiv_whisker_r] itself is written as a tactic proof for a
   version reason recorded at its definition. *)

(** ** Cast algebra, with all endpoints variables *)

Lemma cast_solve {C : Category} {a b a' b' : C} (ex : a = a') (ey : b = b')
  (u : a ~{C}~> b) (v : a' ~{C}~> b') :
  id_cast ey ∘ u ∘ id_cast (eq_sym ex) ≈ v →
  u ≈ id_cast (eq_sym ey) ∘ v ∘ id_cast ex.
Proof.
  destruct ex, ey; simpl; intro H.
  rewrite id_left, id_right in H.
  rewrite id_left, id_right.
  now symmetry.
Qed.

Lemma cast_from_rew {C : Category} {a b c d : C} (p : a = b) (q : c = d)
  (u : a ~{C}~> c) (v : b ~{C}~> d) :
  hom_rew p u ≈ id_cast (eq_sym q) ∘ v → hom_cast p q u ≈ v.
Proof.
  destruct p, q; simpl; intro H.
  rewrite id_left in H.
  exact H.
Qed.

Lemma cast_shuffle {C : Category} {a b c d : C} (p : a = b) (q : c = d)
  (u : a ~{C}~> c) (v : b ~{C}~> d) :
  id_cast q ∘ u ∘ id_cast (eq_sym p) ≈ v →
  u ∘ id_cast (eq_sym p) ≈ id_cast (eq_sym q) ∘ v.
Proof.
  destruct p, q; simpl; intro H.
  rewrite id_left, id_right in H.
  rewrite !id_right, id_left.
  now symmetry.
Qed.

Lemma cast_unit_cod {C : Category} {a b : C} (e : a = b) :
  hom_cast eq_refl e (id_cast (eq_sym e)) ≈ id.
Proof. destruct e; simpl; reflexivity. Qed.

Lemma cast_unit_dom {C : Category} {a b : C} (e : a = b) :
  hom_cast e eq_refl (id_cast e) ≈ id.
Proof. destruct e; simpl; reflexivity. Qed.

Lemma cast_transfer {C : Category} {a b a' b' t : C}
  (e : a = a') (e' : b = b') (k : a ~{C}~> b) (u : t ~{C}~> a)
  (v : t ~{C}~> b) (m : a' ~{C}~> b') :
  v ≈ k ∘ u → id_cast e' ∘ k ∘ id_cast (eq_sym e) ≈ m →
  id_cast e' ∘ v ≈ m ∘ (id_cast e ∘ u).
Proof.
  destruct e, e'; simpl; intros H1 H2.
  rewrite id_left, id_right in H2.
  rewrite !id_left.
  now rewrite H1, <- H2.
Qed.

(** ** A limiting cone stays limiting along an isomorphism of diagrams *)

Section DiagTransport.

Context {J C : Category}.
Context {G G' : J ⟶ C}.
Context (e : G ≈ G').

Definition islimitcone_dtransport {N : Cone G} (HN : IsLimitCone N) :
  IsLimitCone (cone_transport e N).
Proof.
  intro M.
  unshelve refine {| unique_obj := unique_obj (HN (cone_transport_inv e M)) |}.
  - intro x.
    change (to (`1 e x) ∘ cone_leg N x
              ∘ unique_obj (HN (cone_transport_inv e M)) ≈ cone_leg M x).
    rewrite <- comp_assoc.
    rewrite (unique_property (HN (cone_transport_inv e M)) x).
    change (to (`1 e x) ∘ (from (`1 e x) ∘ cone_leg M x) ≈ cone_leg M x).
    rewrite comp_assoc, iso_to_from.
    now rewrite id_left.
  - intros v Hv.
    apply (uniqueness (HN (cone_transport_inv e M))).
    intro x.
    change (cone_leg N x ∘ v ≈ from (`1 e x) ∘ cone_leg M x).
    rewrite <- (Hv x).
    change (cone_leg N x ∘ v
              ≈ from (`1 e x) ∘ (to (`1 e x) ∘ cone_leg N x ∘ v)).
    rewrite !comp_assoc, iso_from_to.
    now rewrite id_left.
Defined.

Definition islimitcone_dtransport_inv {N : Cone G'} (HN : IsLimitCone N) :
  IsLimitCone (cone_transport_inv e N).
Proof.
  intro M.
  unshelve refine {| unique_obj := unique_obj (HN (cone_transport e M)) |}.
  - intro x.
    change (from (`1 e x) ∘ cone_leg N x
              ∘ unique_obj (HN (cone_transport e M)) ≈ cone_leg M x).
    rewrite <- comp_assoc.
    rewrite (unique_property (HN (cone_transport e M)) x).
    change (from (`1 e x) ∘ (to (`1 e x) ∘ cone_leg M x) ≈ cone_leg M x).
    rewrite comp_assoc, iso_from_to.
    now rewrite id_left.
  - intros v Hv.
    apply (uniqueness (HN (cone_transport e M))).
    intro x.
    change (cone_leg N x ∘ v ≈ to (`1 e x) ∘ cone_leg M x).
    rewrite <- (Hv x).
    change (cone_leg N x ∘ v
              ≈ to (`1 e x) ∘ (from (`1 e x) ∘ cone_leg N x ∘ v)).
    rewrite !comp_assoc, iso_to_from.
    now rewrite id_left.
Defined.

End DiagTransport.

(** ** Creation transports along an isomorphism of the functor *)

(* The creation analogue of Functor/Hom/Continuous.v:367's
   [PreservesLimitCone_transport].  It carries CREATION, not strictness:
   there is still no [StrictlyCreatesLimit_transport] and none is claimed. *)

#[local] Obligation Tactic := idtac.

(* Written as a tactic proof rather than as the anonymous-constructor term
   [(fun j => `1 e (K j); fun x y f => `2 e _ _ (fmap[K] f))], which Rocq 9.1
   accepts but Coq 8.19 and 8.20 refuse: checking that pair against the
   expected type, their elaborator compares [fmap[F ◯ K] f] with
   [fmap[F] (fmap[K] f)] by unification rather than by conversion and
   reports "cannot unify".  [exact] uses full conversion and is accepted by
   all three.  The [Defined] is load-bearing: [CreatesLimit_transport]'s
   proof does a [change] through this definition's first component, and
   [Qed] here stops the file at that step with "Not convertible". *)

Definition fun_equiv_whisker_r {J C D : Category} {F F' : C ⟶ D}
  (e : F ≈ F') (K : J ⟶ C) : (F ◯ K) ≈ (F' ◯ K).
Proof.
  exists (fun j => `1 e (K j)).
  intros x y f.
  exact (`2 e _ _ (fmap[K] f)).
Defined.

Section CreatesTransport.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context {F F' : C ⟶ D}.
Context (e : F ≈ F').
Context (CR : CreatesLimit K F).

Notation w := (fun_equiv_whisker_r e K).

Definition ctr_lift (N : Cone (F' ◯ K)) (HN : IsLimitCone N) : Cone K :=
  creates_lift (cone_transport_inv w N) (islimitcone_dtransport_inv w HN).

Program Definition ctr_over (N : Cone (F' ◯ K)) (HN : IsLimitCone N) :
  ConeIso (FCone F' (ctr_lift N HN)) N :=
  (iso_compose
     `1 (creates_lift_over (cone_transport_inv w N)
           (islimitcone_dtransport_inv w HN))
     (iso_sym (`1 e (vertex_obj[ctr_lift N HN]))); _).
Next Obligation.
  intros N HN x.
  pose proof (`2 (creates_lift_over (cone_transport_inv w N)
                    (islimitcone_dtransport_inv w HN)) x) as Hx.
  cbv beta in Hx.
  change (cone_leg (cone_transport_inv w N) x)
    with (from (`1 e (K x)) ∘ cone_leg N x) in Hx.
  simpl.
  rewrite comp_assoc.
  assert (Hy : cone_leg N x
                 ∘ to `1 (creates_lift_over (cone_transport_inv w N)
                            (islimitcone_dtransport_inv w HN))
               ≈ to (`1 e (K x)) ∘ fmap[F] (cone_leg (ctr_lift N HN) x)).
  { rewrite <- Hx.
    rewrite !comp_assoc, iso_to_from.
    now rewrite id_left. }
  rewrite Hy.
  rewrite <- comp_assoc.
  rewrite (fun_equiv_fmap_from e _ _ (cone_leg (ctr_lift N HN) x)).
  rewrite comp_assoc, iso_to_from.
  now rewrite id_left.
Qed.

Program Definition ctr_fcone_iso (M : Cone K) :
  ConeIso (cone_transport_inv w (FCone F' M)) (FCone F M) :=
  (iso_sym (`1 e (vertex_obj[M])); _).
Next Obligation.
  intros M x.
  simpl.
  exact (fun_equiv_fmap_from e _ _ (cone_leg M x)).
Qed.

Definition ctr_reflect (M : Cone K) (H : IsLimitCone (FCone F' M)) :
  IsLimitCone M :=
  creates_reflect M
    (limitcone_transport (ctr_fcone_iso M)
       (islimitcone_dtransport_inv w H)).

Definition CreatesLimit_transport : CreatesLimit K F' :=
  {| creates_lift      := ctr_lift;
     creates_lift_over := ctr_over;
     creates_reflect   := ctr_reflect |}.

End CreatesTransport.

(** ** Mac Lane §V.6 Exercise 3 *)

Section Ex3.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).
Context {J : Category}.
Context (K : J ⟶ FibreProduct F G).

Notation P  := (FibreProduct F G).
Notation p1 := (FP_fst F G).
Notation p2 := (FP_snd F G).
Notation KA := (p1 ◯ K).
Notation KB := (p2 ◯ K).

(* The square commutes definitionally: both components are the fibre
   product's own stored data, read off the diagram. *)

Definition fp_square_obj (j : J) : F (KA j) = G (KB j) := `2 (K j).

Definition fp_square_hom {x y : J} (f : x ~{J}~> y) :
  hom_cast (fp_square_obj x) (fp_square_obj y) (fmap[F ◯ KA] f) ≈ fmap[G ◯ KB] f
  := `2 (fmap[K] f).

Program Definition fp_square_iso : (F ◯ KA) ≈ (G ◯ KB) :=
  (fun j => id_cast_iso (fp_square_obj j); _).
Next Obligation.
  intros x y f.
  pose proof (fp_square_hom f) as Hf; cbv beta in Hf.
  rewrite hom_cast_decompose in Hf.
  exact (cast_solve _ _ _ _ Hf).
Qed.

(* The [F]-image of the [A]-projection of a cone is limiting as soon as the
   [G]-image of its [B]-projection is — the square, read as a transport. *)

Section FImage.

Context (W : Cone K).
Context (HW : IsLimitCone (FCone G (FCone p2 W))).

Program Definition fp_F_image_coneiso :
  ConeIso (cone_transport_inv fp_square_iso (FCone G (FCone p2 W)))
          (FCone F (FCone p1 W)) :=
  (id_cast_iso (eq_sym (`2 vertex_obj[W])); _).
Next Obligation.
  intro x.
  pose proof (`2 (cone_leg W x)) as Hx; cbv beta in Hx.
  rewrite hom_cast_decompose in Hx.
  exact (cast_shuffle _ _ _ _ Hx).
Qed.

Definition fp_F_image_limiting : IsLimitCone (FCone F (FCone p1 W)) :=
  limitcone_transport fp_F_image_coneiso
    (islimitcone_dtransport_inv fp_square_iso HW).

End FImage.

(** ** Pairing the two coordinate mediators *)

Section Pairing.

Context (W : Cone K).
Context (H1 : IsLimitCone (FCone p1 W)).
Context (H2 : IsLimitCone (FCone p2 W)).
Context (H3 : IsLimitCone (FCone G (FCone p2 W))).

Section AtCompetitor.

Context (Q : Cone K).

(* The fibre product's side condition on the paired mediator is not extra
   data: it is uniqueness in [C], both sides mediating the same cone. *)

Lemma fp_med_cast :
  hom_cast (`2 vertex_obj[Q]) (`2 vertex_obj[W])
    (fmap[F] (unique_obj (H1 (FCone p1 Q))))
  ≈ fmap[G] (unique_obj (H2 (FCone p2 Q))).
Proof using H1 H2 H3.
  transitivity (unique_obj (H3 (FCone G (FCone p2 Q)))).
  - symmetry.
    apply (uniqueness (H3 (FCone G (FCone p2 Q)))).
    intro j.
    change (fmap[G] (fmap[p2] (cone_leg W j))
              ∘ hom_cast (`2 vertex_obj[Q]) (`2 vertex_obj[W])
                  (fmap[F] (unique_obj (H1 (FCone p1 Q))))
            ≈ fmap[G] (fmap[p2] (cone_leg Q j))).
    rewrite <- (`2 (cone_leg W j)).
    rewrite hom_cast_comp.
    rewrite <- fmap_comp.
    rewrite (unique_property (H1 (FCone p1 Q)) j).
    exact (`2 (cone_leg Q j)).
  - apply (uniqueness (H3 (FCone G (FCone p2 Q)))).
    intro j.
    change (fmap[G] (fmap[p2] (cone_leg W j))
              ∘ fmap[G] (unique_obj (H2 (FCone p2 Q)))
            ≈ fmap[G] (fmap[p2] (cone_leg Q j))).
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact (unique_property (H2 (FCone p2 Q)) j).
Qed.

Definition fp_med : vertex_obj[Q] ~{P}~> vertex_obj[W] :=
  ((unique_obj (H1 (FCone p1 Q)), unique_obj (H2 (FCone p2 Q))); fp_med_cast).

End AtCompetitor.

Definition fp_islimitcone : IsLimitCone W.
Proof using H1 H2 H3.
  intro Q.
  unshelve refine {| unique_obj := fp_med Q |}.
  - intro j.
    split.
    + exact (unique_property (H1 (FCone p1 Q)) j).
    + exact (unique_property (H2 (FCone p2 Q)) j).
  - intros v Hv.
    split.
    + apply (uniqueness (H1 (FCone p1 Q))).
      intro j. exact (fst (Hv j)).
    + apply (uniqueness (H2 (FCone p2 Q))).
      intro j. exact (snd (Hv j)).
Defined.

End Pairing.

(** ** The exercise itself *)

Section Create.

Context (SC : StrictlyCreatesLimit KA F).
Context (HG : PreservesLimitCone KB G).

Section AtCone.

Context (N : Cone KB).
Context (HN : IsLimitCone N).

Definition fp_image_cone : Cone (F ◯ KA) :=
  cone_transport_inv fp_square_iso (FCone G N).

Definition fp_image_limiting_at : IsLimitCone fp_image_cone :=
  islimitcone_dtransport_inv fp_square_iso (HG N HN).

Definition fp_upstairs_lift : StrictLift KA F fp_image_cone := screates fp_image_cone fp_image_limiting_at.

(* Here, and only here, is the bottom functor's strictness spent: the third
   component of a fibre-product object is a Leibniz equality. *)

Definition fp_lift_apex : P :=
  ((vertex_obj[slift_cone fp_upstairs_lift], vertex_obj[N]); slift_eq fp_upstairs_lift).

Definition fp_lift_leg (j : J) : fp_lift_apex ~{P}~> K j.
Proof using.
  refine ((cone_leg (slift_cone fp_upstairs_lift) j, cone_leg N j); _).
  apply cast_from_rew.
  exact (slift_legs fp_upstairs_lift j).
Defined.

Lemma fp_lift_coh {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ fp_lift_leg x ≈ fp_lift_leg y.
Proof using.
  split.
  - exact (cone_leg_coh (slift_cone fp_upstairs_lift) f).
  - exact (cone_leg_coh N f).
Qed.

Definition fp_lift_cone : Cone K :=
  @Build_Cone J P K fp_lift_apex
    (@Build_ACone J P fp_lift_apex K fp_lift_leg (@fp_lift_coh)).

Definition fp_strict_lift : StrictLift K p2 N :=
  @Build_StrictLift J P B K p2 N fp_lift_cone eq_refl (fun x => reflexivity _).

Definition fp_lift_limiting : IsLimitCone fp_lift_cone :=
  fp_islimitcone fp_lift_cone (screates_limiting fp_image_cone fp_image_limiting_at) HN (HG N HN).

End AtCone.

Definition fp_reflect (Mc : Cone K) (H : IsLimitCone (FCone p2 Mc)) :
  IsLimitCone Mc :=
  fp_islimitcone Mc
    (screates_reflect (FCone p1 Mc)
       (fp_F_image_limiting Mc (HG (FCone p2 Mc) H)))
    H (HG (FCone p2 Mc) H).

Definition fp_snd_StrictlyCreatesLimit : StrictlyCreatesLimit K p2 :=
  {| screates          := fp_strict_lift;
     screates_limiting := fp_lift_limiting;
     screates_reflect  := fp_reflect |}.

Definition fp_snd_CreatesLimit : CreatesLimit K p2 :=
  StrictlyCreatesLimit_CreatesLimit fp_snd_StrictlyCreatesLimit.

End Create.

End Ex3.

(* The all-shapes packaging comes in both strengths, and the strict one is
   the same term: [fp_snd_StrictlyCreatesLimit] is already strict at every
   diagram, so quantifying over shapes costs nothing.  An earlier revision
   shipped only [fp_snd_CreatesAllLimits], silently dropping the strictness
   the per-diagram theorem has. *)

Definition fp_snd_StrictlyCreatesLimits
  {A B C : Category} (F : A ⟶ C) (G : B ⟶ C)
  (SF : StrictlyCreatesLimits F) (HG : ContinuousFunctor G) :
  StrictlyCreatesLimits (FP_snd F G) :=
  fun J K => fp_snd_StrictlyCreatesLimit F G K (SF J _) (HG J _).

Definition fp_snd_CreatesAllLimits
  {A B C : Category} (F : A ⟶ C) (G : B ⟶ C)
  (SF : StrictlyCreatesLimits F) (HG : ContinuousFunctor G) :
  CreatesAllLimits (FP_snd F G) :=
  fun J K => fp_snd_CreatesLimit F G K (SF J _) (HG J _).

(* The issue's Verification block audits this name. *)

Definition creation_pullback_stable {A B C : Category} (F : A ⟶ C)
  (G : B ⟶ C) {J : Category} (K : J ⟶ FibreProduct F G)
  (SC : StrictlyCreatesLimit (FP_fst F G ◯ K) F)
  (HG : PreservesLimitCone (FP_snd F G ◯ K) G) :
  StrictlyCreatesLimit K (FP_snd F G) :=
  fp_snd_StrictlyCreatesLimit F G K SC HG.

(** ** Mac Lane §V.6 Exercise 4: the comma category as the fibre product *)

#[local] Set Transparent Obligations.

Section CommaAsFibreProduct.

Context {C D : Category}.
Context (U : C ⟶ D).
Context (d : D).

Notation FP := (FibreProduct (@Coslice_Proj D d) U).

Program Definition Comma_to_FP : (=(d) ↓ U) ⟶ FP := {|
  fobj := fun x => (((U (snd ``x); `2 x), snd ``x); eq_refl);
  fmap := fun x y f => ((( fmap[U] (snd ``f) ; _), snd ``f); _)
|}.
Next Obligation.
  intros x y f; simpl.
  pose proof (`2 f) as Hf; simpl in Hf.
  rewrite id_right in Hf.
  exact Hf.
Defined.
Next Obligation. intros x y f; simpl; reflexivity. Defined.
Next Obligation.
  intros x y f g [Hf1 Hf2]; simpl in *.
  split; simpl.
  - now rewrite Hf2.
  - exact Hf2.
Qed.
Next Obligation. intros x; simpl; split; simpl; [ apply fmap_id | reflexivity ]. Qed.
Next Obligation.
  intros x y z f g; simpl; split; simpl.
  - apply fmap_comp.
  - reflexivity.
Qed.

Program Definition FP_to_Comma : FP ⟶ (=(d) ↓ U) := {|
  fobj := fun x => ((ttt, snd ``x); id_cast (`2 x) ∘ `2 (fst ``x));
  fmap := fun x y f => ((ttt, snd ``f); _)
|}.
Next Obligation.
  intros x y f; simpl.
  pose proof (`2 (fst ``f)) as Hk; simpl in Hk.
  pose proof (`2 f) as Hc; simpl in Hc.
  rewrite hom_cast_decompose in Hc.
  rewrite id_right.
  exact (cast_transfer _ _ _ _ _ _ Hk Hc).
Defined.
Next Obligation.
  intros x y f g [Hf1 Hf2]; simpl in *.
  split; simpl; [ reflexivity | exact Hf2 ].
Qed.
Next Obligation. intros x; simpl; split; simpl; reflexivity. Qed.
Next Obligation. intros x y z f g; simpl; split; simpl; reflexivity. Qed.

(** ** The two round trips *)

Program Definition FP_round_to (x : FP) :
  Comma_to_FP (FP_to_Comma x) ~{FP}~> x :=
  (((id_cast (eq_sym (`2 x)); _), id); _).
Next Obligation.
  intros x; simpl.
  rewrite comp_assoc, id_cast_inv_l.
  now rewrite id_left.
Defined.
Next Obligation.
  intros x; cbv beta.
  rewrite fmap_id.
  apply cast_unit_cod.
Defined.

Program Definition FP_round_from (x : FP) :
  x ~{FP}~> Comma_to_FP (FP_to_Comma x) :=
  (((id_cast (`2 x); _), id); _).
Next Obligation. intros x; simpl; reflexivity. Defined.
Next Obligation.
  intros x; cbv beta.
  rewrite fmap_id.
  apply cast_unit_dom.
Defined.

Program Definition FP_round_iso (x : FP) :
  Comma_to_FP (FP_to_Comma x) ≅[FP] x := {|
  to := FP_round_to x; from := FP_round_from x
|}.
Next Obligation.
  intros x; split; simpl.
  - apply id_cast_inv_l.
  - apply id_left.
Qed.
Next Obligation.
  intros x; split; simpl.
  - apply id_cast_inv_r.
  - apply id_left.
Qed.

Program Definition FP_round : (Comma_to_FP ◯ FP_to_Comma) ≈ Id[FP] :=
  (FP_round_iso; _).
Next Obligation.
  intros x y f; split; simpl.
  - pose proof (`2 f) as Hf; simpl in Hf.
    rewrite hom_cast_decompose in Hf.
    now symmetry.
  - rewrite id_left; now rewrite id_right.
Qed.

Program Definition Comma_round_to (x : (=(d) ↓ U)) :
  FP_to_Comma (Comma_to_FP x) ~{(=(d) ↓ U)}~> x := ((ttt, id); _).
Next Obligation.
  intros x; cbv beta; simpl.
  rewrite fmap_id; cat.
Defined.

Program Definition Comma_round_from (x : (=(d) ↓ U)) :
  x ~{(=(d) ↓ U)}~> FP_to_Comma (Comma_to_FP x) := ((ttt, id); _).
Next Obligation.
  intros x; cbv beta; simpl.
  rewrite fmap_id; cat.
Defined.

Program Definition Comma_round_iso (x : (=(d) ↓ U)) :
  FP_to_Comma (Comma_to_FP x) ≅[(=(d) ↓ U)] x := {|
  to := Comma_round_to x; from := Comma_round_from x
|}.
Next Obligation. intros x; split; simpl; [ reflexivity | apply id_left ]. Qed.
Next Obligation. intros x; split; simpl; [ reflexivity | apply id_left ]. Qed.

Program Definition Comma_round :
  (FP_to_Comma ◯ Comma_to_FP) ≈ Id[(=(d) ↓ U)] :=
  (Comma_round_iso; _).
Next Obligation.
  intros x y f; split; simpl.
  - reflexivity.
  - rewrite id_left.
    symmetry; apply id_right.
Qed.

(* An ISOMORPHISM in [Cat].  Not a pullback in [Cat]: the tree refutes the
   fibre product as a [Cat] pullback at one cospan (the [Indiscrete bool]
   one), and nothing here establishes or refutes it at this cospan.  And
   THIS ROUTE does not yield a pullback in [StrictCat] either, since the
   round trip carries [id ∘ φ] rather than [φ] and so does not transport
   [FibreProduct_IsPullback] across — that is this comparison coming up
   short, not a proof that no comparison works. *)

Program Definition Comma_FP_iso : (=(d) ↓ U) ≅[Cat] FP := {|
  to := Comma_to_FP; from := FP_to_Comma
|}.
Next Obligation. exact FP_round. Defined.
Next Obligation. exact Comma_round. Defined.

Definition Comma_FP_Equivalence :
  @EquivalenceOfCategories (=(d) ↓ U) FP Comma_to_FP :=
  Cat_Iso_to_Equivalence Comma_FP_iso.

End CommaAsFibreProduct.

(** ** Exercise 4: the comma projection creates limits, by that route *)

(* This reaches the conclusion #438's [comma_CreatesAllLimits] already
   reaches, by a different argument.  It is a CROSS-CHECK, not a
   strengthening — but state the comparison against the right constant.

   Against [comma_CreatesAllLimits] (Construction/Comma/Creation.v:715) the
   two are of EQUAL strength.  That one takes [PreservesImageLimit], which
   quantifies over every shape just as [ContinuousFunctor U] does — indeed
   the two premises are interderivable by identity functions in that very
   file, [PreservesImageLimit_Continuous] at :227 and
   [Continuous_PreservesImageLimit] at :232 — and it concludes
   [CreatesAllLimits], which is pointwise [CreatesLimit], not
   [StrictlyCreatesLimit].

   The "weaker in both directions" comparison is true, and is true only, of
   #438's [comma_StrictlyCreatesLimit] (:556), which takes the per-diagram
   [PreservesLimitCone (Gdiag K) U] and concludes [StrictlyCreatesLimit].
   An earlier revision of this comment, of the commit message and of the
   docs/INDEX.md bullet made that comparison against
   [comma_CreatesAllLimits], which has neither that premise nor that
   conclusion; measured with [Check], the claim was false in both halves,
   and it under-sold this route while over-stating that constant. *)

Section Ex4.

Context {C D : Category}.
Context (U : C ⟶ D).
Context (d : D).

Notation FP := (FibreProduct (@Coslice_Proj D d) U).
Notation E  := (Comma_to_FP U d).

Program Definition ex4_functor_iso :
  (FP_snd (@Coslice_Proj D d) U ◯ E) ≈ (@comma_proj2 _1 C D (=(d)) U) :=
  (fun x => iso_id; _).
Next Obligation.
  intros x y f; simpl.
  rewrite id_left; symmetry; apply id_right.
Qed.

Context (HU : ContinuousFunctor U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

Definition ex4_fp_creates :
  StrictlyCreatesLimit (E ◯ K) (FP_snd (@Coslice_Proj D d) U) :=
  fp_snd_StrictlyCreatesLimit (@Coslice_Proj D d) U (E ◯ K)
    (Coslice_Proj_StrictlyCreatesLimit d _)
    (HU _ _).

Definition ex4_composite :
  CreatesLimit K (FP_snd (@Coslice_Proj D d) U ◯ E) :=
  CreatesLimit_compose
    (equivalence_CreatesAllLimits (Comma_FP_Equivalence U d) J K)
    (StrictlyCreatesLimit_CreatesLimit ex4_fp_creates).

Definition comma_proj2_creates_second :
  CreatesLimit K (@comma_proj2 _1 C D (=(d)) U) :=
  CreatesLimit_transport ex4_functor_iso ex4_composite.

End Ex4.

Definition comma_proj2_CreatesAllLimits_via_pullback
  {C D : Category} (U : C ⟶ D) (d : D) (HU : ContinuousFunctor U) :
  CreatesAllLimits (@comma_proj2 _1 C D (=(d)) U) :=
  fun J K => comma_proj2_creates_second U d HU K.

Definition comma_Complete_via_pullback
  {C D : Category} (U : C ⟶ D) (d : D) (HU : ContinuousFunctor U)
  (HC : @Complete C) : @Complete (=(d) ↓ U) :=
  creates_limits_Complete comma_proj2 HC
    (comma_proj2_CreatesAllLimits_via_pullback U d HU).

(* The issue's Verification block audits this name too. *)

Definition comma_creates_limits_second_proof {C D : Category} (U : C ⟶ D)
  (d : D) (HU : ContinuousFunctor U) {J : Category} (K : J ⟶ (=(d) ↓ U)) :
  CreatesLimit K (@comma_proj2 _1 C D (=(d)) U) :=
  comma_proj2_creates_second U d HU K.

(** ** The premise of Exercise 4 is inhabited, with nothing assumed *)

(* [Id] is its own right adjoint and a right adjoint is continuous, so
   [ContinuousFunctor Id] holds for EVERY category with no hypothesis —
   the same shape as Construction/Slice/Creation.v's
   [Id_PreservesImageLimit].  So the coslice-as-comma reading of Exercise 4
   is an unconditional theorem, and the results above are not vacuous. *)

Definition Id_ContinuousFunctor {C : Category} : ContinuousFunctor (@Id C) :=
  @right_adjoint_Continuous C C Id Id (@adj_id C).

Definition coslice_comma_proj2_creates_via_pullback {C : Category} (c : C)
  {J : Category} (K : J ⟶ (=(c) ↓ Id)) :
  CreatesLimit K (@comma_proj2 _1 C C (=(c)) Id) :=
  comma_proj2_creates_second Id c Id_ContinuousFunctor K.

Definition coslice_comma_Complete_via_pullback {C : Category} (c : C)
  (HC : @Complete C) : @Complete (=(c) ↓ Id) :=
  comma_Complete_via_pullback Id c Id_ContinuousFunctor HC.
