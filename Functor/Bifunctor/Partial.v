(** * Bifunctors and transformations from partial data *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.3, printed pp. 37–38 (PDF pp. 47–48) — maclane:II.3:prop1
              (a bifunctor is determined by its partial functors),
              maclane:II.3:def3 (naturality in one variable),
              maclane:II.3:prop2 (bifunctor naturality is componentwise)
   Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.6,
              Lemma 7.14 (the bifunctor lemma), printed p. 168 (PDF
              pp. 177–178) — awodey:7.6:lem14: the same iff, stated over
              raw object/arrow data
   nLab:      https://ncatlab.org/nlab/show/bifunctor

   Mac Lane's two propositions: a bifunctor is assembled from functors in
   each separate variable agreeing on objects exactly when the one-sided
   arrow actions satisfy the interchange condition (Proposition 1), and a
   family of arrows between bifunctors is a natural transformation exactly
   when it is natural in each variable separately (Proposition 2).  The
   NECESSITY directions have long been in tree as Functor/Bifunctor.v's
   bimap calculus; this file adds everything else:

     - [Partial_l]/[Partial_r]: the partial functors of a bifunctor,
       bundled as named [Functor]s (work item 1)
     - [Build_Bifunctor]: Awodey's raw-data smart constructor — an
       object map, two separately functorial arrow actions, and the
       interchange law yield a bifunctor — with [Build_Bifunctor_l]/
       [Build_Bifunctor_r] computing its partials back to the data and
       [Build_Bifunctor_unique] the uniqueness half, and
       [bifunctor_iff_partial] the FULL IFF over the bundled [RawLaws]
       (necessity by the bimap calculus through the casts, sufficiency
       the constructor)
     - [Bifunctor_from_partial]: Mac Lane's family form — functors
       [L c : B ⟶ D] and [M b : C ⟶ D] agreeing on objects, with the
       commutation condition — routed through the raw constructor
       along the agreement casts (design note 2)
     - [NaturalIn1]/[NaturalIn2] (definitionally the naturality of the
       partial-functor families — [NaturalIn1_partials] — with the
       per-c [Transform_partial_l]), [Transform_from_partial] with
       [transform_natural_in1]/[transform_natural_in2], and the iff
       [transform_iff_natural_in_each]: Proposition 2, both directions
       (work items 3–4), round trips in both composites

   Design:

   1. RAW DATA FIRST.  Awodey's phrasing takes a SINGLE object map
      [S₀ : B → C → D] with two arrow actions over it, so no object
      agreement — and hence no transport — appears anywhere in the
      CONSTRUCTOR or its computation lemmas; the interchange condition
      is stated directly.  (Uniqueness necessarily quantifies over an
      arbitrary bifunctor, so [Build_Bifunctor_unique] and the iff's
      realization side carry the agreement equation and its casts —
      that is the statement's content, not an artifact.)  Mac Lane's family form carries the agreement
      [L c b = M b c] as Leibniz equalities on objects (the only
      relation objects have here), and design note 2's [cast2] moves
      [M]'s arrow action onto [L]'s objects; the family constructor is
      then an instance of the raw one.

   2. THE FAMILY FORM PAYS FOR ITS OBJECT EQUATIONS.  [cast2] is the
      endpoint transport (the [acast] idiom of Theory/Multicategory.v,
      specialized to homs), and the family constructor's interchange
      hypothesis is stated UNDER the casts — exactly the price Mac
      Lane's "agreeing on objects" costs in a proof assistant, paid
      once here rather than by every consumer.

   3. UNIQUENESS IS [Functor_Setoid].  Proposition 1's "unique functor
      S" is rendered as uniqueness up to Cat's hom-equivalence: any
      bifunctor whose object map is the data's and whose arrow actions
      restrict to the data's one-sided actions is ≈ the constructed
      one.  The witnessing natural isomorphism has cast components
      built from the object agreement (identity components when the
      agreement is definitional). *)

(** ** Endpoint casts (design note 2) *)

Definition cast2 {D : Category} {x y x' y' : obj[D]}
  (ex : x = x') (ey : y = y') (f : x ~> y) : x' ~> y' :=
  eq_rect x (fun w => w ~> y')
    (eq_rect y (fun z => x ~> z) f y' ey) x' ex.

(* An object equality yields an isomorphism, the identity when the
   equality is reflexivity. *)
Definition eq_iso {D : Category} {x y : obj[D]} (e : x = y) : x ≅ y :=
  match e in _ = z return x ≅ z with eq_refl => iso_id end.

(* Cast algebra over generic equalities, each law by destructing them. *)
Lemma cast2_respects {D : Category} {x y x' y' : obj[D]}
  (ex : x = x') (ey : y = y') (f g : x ~> y) :
  f ≈ g → cast2 ex ey f ≈ cast2 ex ey g.
Proof.
  destruct ex, ey; simpl; intro H; exact H.
Qed.

Lemma cast2_id_same {D : Category} {x x' : obj[D]} (e : x = x') :
  cast2 e e (@id D x) ≈ id.
Proof.
  destruct e; simpl; reflexivity.
Qed.

Lemma cast2_comp {D : Category} {x y z x' y' z' : obj[D]}
  (e1 : x = x') (e2 : y = y') (e3 : z = z')
  (g : y ~> z) (g' : x ~> y) :
  cast2 e1 e3 (g ∘ g') ≈ cast2 e2 e3 g ∘ cast2 e1 e2 g'.
Proof.
  destruct e1, e2, e3; simpl; reflexivity.
Qed.

(** ** The partial functors of a bifunctor (work item 1) *)

Program Definition Partial_l {B C D : Category}
  (F : B ∏ C ⟶ D) (c : C) : B ⟶ D := {|
  fobj := fun b => F (b, c);
  fmap := fun b b' f => @bimap B C D F b b' c c f id
|}.
Next Obligation.
  intros B C D F c b b' f f' Hf.
  unfold bimap; apply fmap_respects; split; simpl.
  - exact Hf.
  - reflexivity.
Qed.
Next Obligation.
  intros B C D F c b; unfold bimap.
  exact (@fmap_id _ _ F (b, c)).
Qed.
Next Obligation.
  intros B C D F c b b' b'' f g; unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects; split; simpl.
  - reflexivity.
  - symmetry; apply id_left.
Qed.

Program Definition Partial_r {B C D : Category}
  (F : B ∏ C ⟶ D) (b : B) : C ⟶ D := {|
  fobj := fun c => F (b, c);
  fmap := fun c c' g => @bimap B C D F b b c c' id g
|}.
Next Obligation.
  intros B C D F b c c' g g' Hg.
  unfold bimap; apply fmap_respects; split; simpl.
  - reflexivity.
  - exact Hg.
Qed.
Next Obligation.
  intros B C D F b c; unfold bimap.
  exact (@fmap_id _ _ F (b, c)).
Qed.
Next Obligation.
  intros B C D F b c c' c'' f g; unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects; split; simpl.
  - symmetry; apply id_left.
  - reflexivity.
Qed.

(** ** Awodey's raw-data constructor (Proposition 1, converse) *)

Section BuildBifunctor.

Context {B C D : Category}.

(* The raw data: an object map, one-sided arrow actions, separate
   functoriality, and the interchange law. *)
Context (S0 : B → C → D).
Context (actl : ∀ (b b' : B), (b ~> b') → ∀ c : C, S0 b c ~> S0 b' c).
Context (actr : ∀ (b : B) (c c' : C), (c ~> c') → S0 b c ~> S0 b c').
Context (actl_respects : ∀ (b b' : B) (f f' : b ~> b') (c : C),
  f ≈ f' → actl b b' f c ≈ actl b b' f' c).
Context (actr_respects : ∀ (b : B) (c c' : C) (g g' : c ~> c'),
  g ≈ g' → actr b c c' g ≈ actr b c c' g').
Context (actl_id : ∀ (b : B) (c : C), actl b b (@id B b) c ≈ id).
Context (actr_id : ∀ (b : B) (c : C), actr b c c (@id C c) ≈ id).
Context (actl_comp : ∀ (b b' b'' : B) (f : b' ~> b'') (f' : b ~> b')
  (c : C), actl b b'' (f ∘ f') c ≈ actl b' b'' f c ∘ actl b b' f' c).
Context (actr_comp : ∀ (b : B) (c c' c'' : C) (g : c' ~> c'')
  (g' : c ~> c'), actr b c c'' (g ∘ g') ≈ actr b c' c'' g ∘ actr b c c' g').
Context (interchange : ∀ (b b' : B) (f : b ~> b') (c c' : C)
  (g : c ~> c'), actl b b' f c' ∘ actr b c c' g ≈ actr b' c c' g ∘ actl b b' f c).

(* The bifunctor: arrows act left-then-right; the interchange law makes
   the choice immaterial and drives the composition law. *)
Program Definition Build_Bifunctor : B ∏ C ⟶ D := {|
  fobj := fun p => S0 (fst p) (snd p);
  fmap := fun p q fg =>
    actl (fst p) (fst q) (fst fg) (snd q) ∘ actr (fst p) (snd p) (snd q) (snd fg)
|}.
Next Obligation.
  intros [b c] [b' c'] [f g] [f' g'] [Hf Hg]; simpl in *.
  apply compose_respects.
  - exact (actl_respects _ _ _ _ _ Hf).
  - exact (actr_respects _ _ _ _ _ Hg).
Qed.
Next Obligation.
  intros [b c]; simpl.
  rewrite actl_id, actr_id.
  apply id_left.
Qed.
Next Obligation.
  intros [b c] [b' c'] [b'' c''] [f g] [f' g']; simpl in *.
  rewrite actl_comp, actr_comp.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (actl b b' f' c'')).
  rewrite (interchange b b' f' c' c'' g).
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(* The constructed bifunctor's partials compute back to the data, with
   identity components: the one-sided actions of [Build_Bifunctor] are
   the given actions up to a unit law. *)
Lemma Build_Bifunctor_l (c : C) {b b' : B} (f : b ~> b') :
  fmap[Partial_l Build_Bifunctor c] f ≈ actl b b' f c.
Proof.
  simpl; unfold bimap; simpl.
  rewrite actr_id.
  apply id_right.
Qed.

Lemma Build_Bifunctor_r (b : B) {c c' : C} (g : c ~> c') :
  fmap[Partial_r Build_Bifunctor b] g ≈ actr b c c' g.
Proof.
  simpl; unfold bimap; simpl.
  rewrite actl_id.
  apply id_left.
Qed.

(* Uniqueness (Proposition 1's "unique functor S", design note 3): any
   bifunctor with the same object map whose one-sided actions are the
   data's agrees with the construction up to Functor_Setoid, with
   identity components. *)
Lemma Build_Bifunctor_unique (S' : B ∏ C ⟶ D)
  (Hobj : ∀ b c, S' (b, c) = S0 b c)
  (Hl : ∀ b b' (f : b ~> b') c,
     cast2 (Hobj b c) (Hobj b' c) (@bimap B C D S' b b' c c f id)
       ≈ actl b b' f c)
  (Hr : ∀ b c c' (g : c ~> c'),
     cast2 (Hobj b c) (Hobj b c') (@bimap B C D S' b b c c' id g)
       ≈ actr b c c' g) :
  S' ≈ Build_Bifunctor.
Proof.
  simpl.
  unshelve eexists.
  - intros [b c].
    exact (eq_iso (Hobj b c)).
  - intros [b c] [b' c'] [f g]; simpl.
    rewrite <- (Hl b b' f c'), <- (Hr b c c' g).
    revert Hl Hr.
    generalize (Hobj b c) (Hobj b' c) (Hobj b c') (Hobj b' c').
    intros e1 e2 e3 e4 Hl Hr.
    destruct e1, e2, e3, e4; simpl.
    unfold bimap.
    rewrite <- fmap_comp.
    rewrite id_left, id_right.
    apply fmap_respects; split; simpl.
    + symmetry; apply id_right.
    + symmetry; apply id_left.
Defined.

(* The laws of a bifunctor's own partial data, bundled: the necessity
   half of Proposition 1, each field one of Functor/Bifunctor.v's bimap
   lemmas.  [bifunctor_iff_partial] below is the full iff the
   propositions state. *)

End BuildBifunctor.

(** ** Mac Lane's family form (Proposition 1) *)

Section FamilyForm.

Context {B C D : Category}.
Context (L : C → (B ⟶ D)).
Context (M : B → (C ⟶ D)).
Context (agree : ∀ (c : C) (b : B), L c b = M b c).
Context (commute : ∀ (b b' : B) (f : b ~> b') (c c' : C) (g : c ~> c'),
  fmap[L c'] f
      ∘ cast2 (eq_sym (agree c b)) (eq_sym (agree c' b)) (fmap[M b] g)
    ≈ cast2 (eq_sym (agree c b')) (eq_sym (agree c' b')) (fmap[M b'] g)
        ∘ fmap[L c] f).

(* The family form, an instance of the raw constructor: objects through
   L, the right action through M along the agreement casts. *)
Program Definition Bifunctor_from_partial : B ∏ C ⟶ D :=
  Build_Bifunctor (fun b c => L c b)
    (fun b b' f c => fmap[L c] f)
    (fun b c c' g =>
       cast2 (eq_sym (agree c b)) (eq_sym (agree c' b)) (fmap[M b] g))
    _ _ _ _ _ _ _.
Next Obligation.
  intros b b' f f' c Hf; exact (fmap_respects _ _ _ _ Hf).
Qed.
Next Obligation.
  intros b c c' g g' Hg.
  exact (cast2_respects _ _ _ _ (fmap_respects _ _ _ _ Hg)).
Qed.
Next Obligation.
  intros b c; exact (@fmap_id _ _ (L c) b).
Qed.
Next Obligation.
  intros b c.
  refine (transitivity
            (cast2_respects _ _ _ _ (@fmap_id _ _ (M b) c)) _).
  exact (cast2_id_same _).
Qed.
Next Obligation.
  intros b b' b'' f f' c; exact (@fmap_comp _ _ (L c) _ _ _ f f').
Qed.
Next Obligation.
  intros b c c' c'' g g'.
  refine (transitivity
            (cast2_respects _ _ _ _ (@fmap_comp _ _ (M b) _ _ _ g g')) _).
  exact (cast2_comp _ _ _ _ _).
Qed.
Next Obligation.
  intros b b' f c c' g.
  exact (commute b b' f c c' g).
Qed.

End FamilyForm.

(* The family form's partial functors are the given families, on arrows
   (work item 2's "whose partial functors are the given families"): the
   left on the nose, the right up to the agreement casts — the asymmetry
   design note 2 prices. *)
Lemma Bifunctor_from_partial_l {B C D : Category}
  (L : C → (B ⟶ D)) (M : B → (C ⟶ D)) agree commute
  (c : C) {b b' : B} (f : b ~> b') :
  fmap[Partial_l (Bifunctor_from_partial L M agree commute) c] f
    ≈ fmap[L c] f.
Proof.
  exact (Build_Bifunctor_l _ _ _ _ _ _ _ _ _ _ c f).
Qed.

Lemma Bifunctor_from_partial_r {B C D : Category}
  (L : C → (B ⟶ D)) (M : B → (C ⟶ D)) agree commute
  (b : B) {c c' : C} (g : c ~> c') :
  fmap[Partial_r (Bifunctor_from_partial L M agree commute) b] g
    ≈ cast2 (eq_sym (agree c b)) (eq_sym (agree c' b)) (fmap[M b] g).
Proof.
  exact (Build_Bifunctor_r _ _ _ _ _ _ _ _ _ _ b g).
Qed.

(** ** Proposition 1 as an iff *)

(* The raw laws, bundled. *)
Record RawLaws {B C D : Category} (S0 : obj[B] → obj[C] → obj[D])
  (actl : ∀ b b' : B, (b ~> b') → ∀ c : C, S0 b c ~> S0 b' c)
  (actr : ∀ (b : B) (c c' : C), (c ~> c') → S0 b c ~> S0 b c') := {
  rl_lresp : ∀ (b b' : B) (f f' : b ~> b') (c : C),
    f ≈ f' → actl b b' f c ≈ actl b b' f' c;
  rl_rresp : ∀ (b : B) (c c' : C) (g g' : c ~> c'),
    g ≈ g' → actr b c c' g ≈ actr b c c' g';
  rl_lid : ∀ (b : B) (c : C), actl b b (@id B b) c ≈ id;
  rl_rid : ∀ (b : B) (c : C), actr b c c (@id C c) ≈ id;
  rl_lcomp : ∀ (b b' b'' : B) (f : b' ~> b'') (f' : b ~> b') (c : C),
    actl b b'' (f ∘ f') c ≈ actl b' b'' f c ∘ actl b b' f' c;
  rl_rcomp : ∀ (b : B) (c c' c'' : C) (g : c' ~> c'') (g' : c ~> c'),
    actr b c c'' (g ∘ g') ≈ actr b c' c'' g ∘ actr b c c' g';
  rl_inter : ∀ (b b' : B) (f : b ~> b') (c c' : C) (g : c ~> c'),
    actl b b' f c' ∘ actr b c c' g ≈ actr b' c c' g ∘ actl b b' f c
}.

(* Awodey's Lemma 7.14 / Mac Lane's Proposition 1, as the iff over raw
   data: the laws hold exactly when the data is realized by a bifunctor
   whose one-sided actions restrict to it (along the object agreement,
   with [cast2] pricing it as everywhere else). *)
Theorem bifunctor_iff_partial {B C D : Category}
  (S0 : obj[B] → obj[C] → obj[D])
  (actl : ∀ b b' : B, (b ~> b') → ∀ c : C, S0 b c ~> S0 b' c)
  (actr : ∀ (b : B) (c c' : C), (c ~> c') → S0 b c ~> S0 b c') :
  RawLaws S0 actl actr
    ↔ { S : B ∏ C ⟶ D
      & { Hobj : ∀ (b : B) (c : C), S (b, c) = S0 b c
        & (∀ (b b' : B) (f : b ~> b') (c : C),
             cast2 (Hobj b c) (Hobj b' c)
               (@bimap B C D S b b' c c f id) ≈ actl b b' f c)
          * (∀ (b : B) (c c' : C) (g : c ~> c'),
             cast2 (Hobj b c) (Hobj b c')
               (@bimap B C D S b b c c' id g) ≈ actr b c c' g) } }.
Proof.
  split.
  - intros [R1 R2 R3 R4 R5 R6 R7].
    exists (Build_Bifunctor S0 actl actr R1 R2 R3 R4 R5 R6 R7).
    exists (fun b c => eq_refl).
    split.
    + intros b b' f c; simpl.
      exact (Build_Bifunctor_l S0 actl actr R1 R2 R3 R4 R5 R6 R7 c f).
    + intros b c c' g; simpl.
      exact (Build_Bifunctor_r S0 actl actr R1 R2 R3 R4 R5 R6 R7 b g).
  - intros [S [Hobj [Hl Hr]]].
    constructor.
    + intros b b' f f' c Hf.
      rewrite <- (Hl b b' f c), <- (Hl b b' f' c).
      apply cast2_respects.
      unfold bimap; apply fmap_respects; split; simpl;
        [ exact Hf | reflexivity ].
    + intros b c c' g g' Hg.
      rewrite <- (Hr b c c' g), <- (Hr b c c' g').
      apply cast2_respects.
      unfold bimap; apply fmap_respects; split; simpl;
        [ reflexivity | exact Hg ].
    + intros b c.
      rewrite <- (Hl b b id c).
      refine (transitivity
                (cast2_respects _ _ _ _ (bimap_id_id (F:=S))) _).
      exact (cast2_id_same _).
    + intros b c.
      rewrite <- (Hr b c c id).
      refine (transitivity
                (cast2_respects _ _ _ _ (bimap_id_id (F:=S))) _).
      exact (cast2_id_same _).
    + intros b b' b'' f f' c.
      rewrite <- (Hl b b'' (f ∘ f') c),
              <- (Hl b' b'' f c), <- (Hl b b' f' c).
      refine (transitivity (cast2_respects _ _ _ _ _)
                (cast2_comp _ _ _ _ _)).
      unfold bimap; rewrite <- fmap_comp.
      apply fmap_respects; split; simpl;
        [ reflexivity | symmetry; apply id_left ].
    + intros b c c' c'' g g'.
      rewrite <- (Hr b c c'' (g ∘ g')),
              <- (Hr b c' c'' g), <- (Hr b c c' g').
      refine (transitivity (cast2_respects _ _ _ _ _)
                (cast2_comp _ _ _ _ _)).
      unfold bimap; rewrite <- fmap_comp.
      apply fmap_respects; split; simpl;
        [ symmetry; apply id_left | reflexivity ].
    + intros b b' f c c' g.
      rewrite <- (Hl b b' f c'), <- (Hl b b' f c),
              <- (Hr b c c' g), <- (Hr b' c c' g).
      refine (transitivity (symmetry (cast2_comp _ _ _ _ _)) _).
      refine (transitivity _ (cast2_comp _ _ _ _ _)).
      apply cast2_respects.
      exact (transitivity (@bimap_id_right_left B C D S b' b f c c' g)
               (symmetry (@bimap_id_left_right B C D S c' c g b b' f))).
Qed.

(** ** Proposition 2: naturality in each variable (work items 3–4) *)

Section PartialNaturality.

Context {B C D : Category}.
Context {S S' : B ∏ C ⟶ D}.

(* A family of components between bifunctors, and naturality in one
   variable at a time (maclane:II.3:def3): for each fixed c the family
   is natural in b, and dually. *)
Definition NaturalIn1 (α : ∀ b c, S (b, c) ~> S' (b, c)) : Type :=
  ∀ c b b' (f : b ~> b'),
    α b' c ∘ @bimap B C D S b b' c c f id
      ≈ @bimap B C D S' b b' c c f id ∘ α b c.

Definition NaturalIn2 (α : ∀ b c, S (b, c) ~> S' (b, c)) : Type :=
  ∀ b c c' (g : c ~> c'),
    α b c' ∘ @bimap B C D S b b c c' id g
      ≈ @bimap B C D S' b b c c' id g ∘ α b c.

(* Necessity: a natural transformation over the product is natural in
   each variable — instantiate at (f, id) and (id, g). *)
Definition transform_natural_in1 (τ : S ⟹ S') :
  NaturalIn1 (fun b c => transform τ (b, c)) :=
  fun c b b' f => @naturality_sym _ _ _ _ τ (b, c) (b', c) (f, id).

Definition transform_natural_in2 (τ : S ⟹ S') :
  NaturalIn2 (fun b c => transform τ (b, c)) :=
  fun b c c' g => @naturality_sym _ _ _ _ τ (b, c) (b, c') (id, g).

(* Sufficiency: componentwise naturality assembles to naturality over
   the product, by splitting a pair arrow through the interchange
   factorization bimap f g ≈ bimap f id ∘ bimap id g. *)
Program Definition Transform_from_partial
  (α : ∀ b c, S (b, c) ~> S' (b, c))
  (H1 : NaturalIn1 α) (H2 : NaturalIn2 α) : S ⟹ S' := {|
  transform := fun p =>
    match p as q return fobj[S] q ~> fobj[S'] q with
    | (b, c) => α b c
    end
|}.
Next Obligation.
  intros α H1 H2 [b c] [b' c'] [f g]; simpl in *.
  rewrite <- (@bimap_id_right_left B C D S' b' b f c c' g).
  rewrite <- (@bimap_id_right_left B C D S b' b f c c' g).
  rewrite <- comp_assoc.
  rewrite <- (H2 b c c' g).
  rewrite comp_assoc.
  rewrite <- (H1 c' b b' f).
  rewrite <- comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  intros α H1 H2 [b c] [b' c'] [f g]; simpl in *.
  symmetry.
  rewrite <- (@bimap_id_right_left B C D S' b' b f c c' g).
  rewrite <- (@bimap_id_right_left B C D S b' b f c c' g).
  rewrite <- comp_assoc.
  rewrite <- (H2 b c c' g).
  rewrite comp_assoc.
  rewrite <- (H1 c' b b' f).
  rewrite <- comp_assoc.
  reflexivity.
Qed.

(* One round-trip composite, definitionally: assembling a family and
   reading its components back is the identity. *)
Example Transform_from_partial_transform
  (α : ∀ b c, S (b, c) ~> S' (b, c))
  (H1 : NaturalIn1 α) (H2 : NaturalIn2 α) (b : B) (c : C) :
  transform (Transform_from_partial α H1 H2) (b, c) = α b c := eq_refl.

(* The other composite, pointwise: disassembling a transformation and
   reassembling it gives the same components. *)
Example Transform_from_partial_eta (τ : S ⟹ S') (p : obj[B ∏ C]) :
  transform
    (Transform_from_partial (fun b c => transform τ (b, c))
       (transform_natural_in1 τ) (transform_natural_in2 τ)) p
    ≈ transform τ p.
Proof.
  destruct p; simpl; reflexivity.
Qed.

(* [NaturalIn1] IS naturality of the partial-functor families, on the
   nose (work item 3's phrasing) — and the per-c Transform it promises. *)
Example NaturalIn1_partials (α : ∀ b c, S (b, c) ~> S' (b, c)) :
  NaturalIn1 α
    = (∀ (c : C) (b b' : B) (f : b ~> b'),
         α b' c ∘ fmap[Partial_l S c] f
           ≈ fmap[Partial_l S' c] f ∘ α b c) := eq_refl.

Program Definition Transform_partial_l
  (α : ∀ b c, S (b, c) ~> S' (b, c)) (H1 : NaturalIn1 α) (c : C) :
  Partial_l S c ⟹ Partial_l S' c := {|
  transform := fun b => α b c
|}.
Next Obligation.
  intros α H1 c b b' f; simpl.
  symmetry; exact (H1 c b b' f).
Qed.
Next Obligation.
  intros α H1 c b b' f; simpl.
  exact (H1 c b b' f).
Qed.

(* Proposition 2 as the iff: a family underlies a transformation over
   the product exactly when it is natural in each variable. *)
Theorem transform_iff_natural_in_each
  (α : ∀ b c, S (b, c) ~> S' (b, c)) :
  (NaturalIn1 α * NaturalIn2 α)
    ↔ { τ : S ⟹ S' & ∀ b c, transform τ (b, c) ≈ α b c }.
Proof.
  split.
  - intros [H1 H2].
    exists (Transform_from_partial α H1 H2).
    intros b c; simpl; reflexivity.
  - intros [τ Hτ]; split.
    + intros c b b' f.
      rewrite <- (Hτ b c), <- (Hτ b' c).
      exact (transform_natural_in1 τ c b b' f).
    + intros b c c' g.
      rewrite <- (Hτ b c), <- (Hτ b c').
      exact (transform_natural_in2 τ b c c' g).
Qed.

End PartialNaturality.
