Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Adjunction.Natural.Transformation.
Require Export Category.Adjunction.Natural.Transformation.Universal.
Require Export Category.Construction.Comma.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(**
              C                C
            ^   \            ^   \
          ψ/  ⇑  \πC      Id/  ⇑  \φ
          /   θ   v        /   id  v
  C ---> D   --->  E  ≃  C    --->  D ---> E
     φ        πD               φ       πD

              D                D
            ^   \            ^   \
          φ/  ⇑  \πD       φ/  ⇑  \ψ
          /   κ   v        /   η   v
  C ---> C   --->  E  ≃  C    --->  C ---> E
     Id       πC               Id      πC

This 2-cat equivalence establishes that:

    κ           : πC     ⟹ πD ○ φ
    θ           : πD     ⟹ πC ○ ψ
    θ ∘ φ       : πD ○ φ ⟹ πC ○ ψ ○ φ
    (θ ∘ φ) ⊙ κ : πC     ⟹ πC ○ ψ ○ φ

         η      :     Id ⟹      ψ ○ φ
    πC ∘ η      : πC     ⟹ πC ○ ψ ○ φ

    (θ ∘ φ) ⊙ (κ ∘ Id) ≈ (πD ∘ id) ⊙ (πC ∘ η)
                             ^--- this part is not correct
 *)

Definition iso_exchange_law {C D E : Category} (M : C ≅[Cat] D) :=
  let φ : C ⟶ D := to M in
  let ψ : D ⟶ C := from M in

  let η := from (equiv_iso (iso_from_to M)) in
  let μ := from (equiv_iso (iso_to_from M)) in

  ∀ (πC : C ~{Cat}~> E) (πD : D ~{Cat}~> E)
    (CD : πC ≈ πD ∘ φ)
    (DC : πD ≈ πC ∘ ψ),

  let κ := to (equiv_iso CD) in
  let θ := to (equiv_iso DC) in

  (* let outC := to   (equiv_iso (comp_assoc πC ψ φ)) in *)
  (* let inC  := from (equiv_iso (id_right πC)) in *)
  (* let outD := to   (equiv_iso (comp_assoc πD φ ψ)) in *)
  (* let inD  := from (equiv_iso (id_right πD)) in *)

  (* (outC ⊙ inside η πC ⊙ inC ≈ outside θ φ ⊙ κ) ∧ *)
  (* (outD ⊙ inside μ πD ⊙ inD ≈ outside κ ψ ⊙ θ). *)

  (∀ A, fmap[πC] (η A) ≈ θ (φ A) ∘ κ A) ∧
  (∀ A, fmap[πD] (μ A) ≈ κ (ψ A) ∘ θ A).

Section AdjunctionComma.

(* Wikipedia: "Lawvere showed that the functors F : C → D and G : D → C are
   adjoint if and only if the comma categories (F ↓ Id[D]) and (Id[C] ↓ G) are
   isomorphic, and equivalent elements in the comma category can be projected
   onto the same element of C × D. This allows adjunctions to be described
   without involving sets, and was in fact the original motivation for
   introducing comma categories."

   From ncatlab: "To give an adjunction i ⊣ r it suffices to give, for each k
   : x → pe in B ↓ p, an object rk in E such that prk = x and an arrow irk =
   1x → k in B ↓ p that is universal from i to k."

   Lawvere's own statement of the theorem, from his thesis (page 40):

   "For each functor f : A ⟶ B, there exists a functor g : B ⟶ A such that g
   is adjoint to f iff for every object B ∈ |B| there exists an object A ∈ |A|
   and a map φ : B ~> A in B such that for every object A′ ∈ |A| and every
   map x : B ~> A′ in B, there exists a unique map y : A ~> A′ in A such that
   x = φ(yf) in B." *)

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {G : C ⟶ D}.

Definition πD := comma_proj1.
Definition πC := comma_proj2.

Local Notation "⟨πD,πC⟩" := comma_proj (at level 100).

Record lawvere_equiv := {
  lawvere_iso : F ↓ Id[C] ≅[Cat] Id[D] ↓ G;

  φ := to lawvere_iso;
  ψ := from lawvere_iso;

  η {x} := from (`1 (iso_from_to lawvere_iso) x);
  μ {x} := from (`1 (iso_to_from lawvere_iso) x);

  projF : ⟨πD,πC⟩ ≈ ⟨πD,πC⟩ ○ φ;
  projG : ⟨πD,πC⟩ ≈ ⟨πD,πC⟩ ○ ψ;

  κ := `1 projF;
  θ := `1 projG;

  exchange : @iso_exchange_law (F ↓ Id[C]) (Id[D] ↓ G) (D ∏ C)
                               lawvere_iso;

  lawvere_to {a b} (f : F a ~> b) : a ~> G b :=
    let o := ((a, b); f) in
    fmap[G] (snd (from (κ o))) ∘ `2 (φ o) ∘ fst (to (κ o));

  lawvere_from {a b} (g : a ~> G b) : F a ~> b :=
    let o := ((a, b); g) in
    snd (from (θ o)) ∘ `2 (ψ o) ∘ fmap[F] (fst (to (θ o)));

  φ' {a b} (f : F a ~> b) := lawvere_to f;
  ψ' {a b} (g : a ~> G b) := lawvere_from g
}.

Context `(E : lawvere_equiv).

Lemma η_θ_κ : ∀ x, `1 (η E x) ≈ θ E (φ E x) ∘ κ E x.
Proof.
  intros.
  pose proof (exchange E _ _ (projF E) (projG E)).
  destruct X as [X _].
  specialize (X x); simpl in X.
  unfold equiv_iso, η, κ, θ, φ in *; simpl in *.
  destruct (iso_from_to (lawvere_iso E)), (projG E), (projF E).
  apply X.
Qed.

Lemma μ_κ_θ : ∀ x, `1 (μ E x) ≈ κ E (ψ E x) ∘ θ E x.
Proof.
  intros.
  pose proof (exchange E _ _ (projF E) (projG E)).
  destruct X as [_ X].
  specialize (X x); simpl in X.
  unfold equiv_iso, μ, κ, θ, ψ in *; simpl in *.
  destruct (iso_to_from (lawvere_iso E)), (projG E), (projF E).
  apply X.
Qed.

Theorem ψ_φ_equiv :
  ∀ x, snd (from (κ E x))
         ∘ snd (from (θ E (φ E x)))
         ∘ `2 (ψ E (φ E x))
         ∘ fmap[F] (fst (to (θ E (φ E x))))
         ∘ fmap[F] (fst (to (κ E x)))
         ≈ `2 x.
Proof.
  intros [[a b] f]; simpl in f; simpl.
  rewrite (snd_comp _ _ _ (κ E ((a, b); f))⁻¹ (θ E (φ E _))⁻¹).
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite (fst_comp _ _ _ (θ E (φ E _)) (κ E ((a, b); f))).
  rewrite <- (η_θ_κ E).
  rewrite (`2 (η E ((a, b); f))).
  rewrite (η_θ_κ E ((a, b); f)).
  rewrite !comp_assoc.
  rewrite (snd_comp _ _ _
             ((κ E _)⁻¹ ∘ (θ E (φ E _))⁻¹)
             (θ E (φ E _) ∘ κ E ((a, b); f))).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (θ E (φ E ((a, b); f)))⁻¹ _).
  rewrite iso_from_to, id_left.
  now rewrite iso_from_to; cat.
Qed.

Theorem φ_ψ_equiv :
  ∀ x, fmap[G] (snd (from (θ E x)))
         ∘ fmap[G] (snd (from (κ E (ψ E x))))
         ∘ `2 (φ E (ψ E x))
         ∘ fst (to (κ E (ψ E x)))
         ∘ fst (to (θ E x))
         ≈ `2 x.
Proof.
  intros [[a b] f]; simpl in f; simpl.
  rewrite <- fmap_comp.
  rewrite (snd_comp _ _ _ (θ E ((a, b); f))⁻¹ (κ E (ψ E _))⁻¹).
  rewrite <- !comp_assoc.
  rewrite (fst_comp _ _ _ (κ E (ψ E _)) (θ E ((a, b); f))).
  rewrite <- (μ_κ_θ E).
  rewrite (`2 (μ E ((a, b); f))).
  rewrite (μ_κ_θ E ((a, b); f)).
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite (snd_comp _ _ _
             ((θ E _)⁻¹ ∘ (κ E (ψ E _))⁻¹)
             (κ E (ψ E _) ∘ θ E ((a, b); f))).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (κ E (ψ E ((a, b); f)))⁻¹ _).
  rewrite iso_from_to, id_left.
  now rewrite iso_from_to; cat.
Qed.

Program Instance to_lawvere_iso_Proper :
  Proper (Isomorphism ==> Isomorphism) (φ E).
Next Obligation.
  proper.
  simpl in *.
  construct.
  - exact (fmap[φ E] (to X)).
  - exact (fmap[φ E] (from X)).
  - exact (iso_to_from (@fmap_iso _ _ (φ E) _ _ X)).
  - exact (iso_from_to (@fmap_iso _ _ (φ E) _ _ X)).
Qed.

Program Instance from_lawvere_iso_Proper :
  Proper (Isomorphism ==> Isomorphism) (ψ E).
Next Obligation.
  proper.
  simpl in *.
  construct.
  - exact (fmap[ψ E] (to X)).
  - exact (fmap[ψ E] (from X)).
  - exact (iso_to_from (@fmap_iso _ _ (ψ E) _ _ X)).
  - exact (iso_from_to (@fmap_iso _ _ (ψ E) _ _ X)).
Qed.

Program Instance lawvere_to_Proper {a b} :
  Proper (equiv ==> equiv) (@φ' E a b).
Next Obligation.
  proper.
  unfold φ', lawvere_to.
  given (ff : ((a, b); x) ~{ F ↓ Id[C] }~> ((a, b); y)).
    now refine ((id, id); _); abstract cat.
  spose (`2 (projF E) ((a, b); x) ((a, b); y) ff) as H0.
  destruct H0 as [H1 H2].
  symmetry.
  rewrite <- id_right.
  rewrite H1.
  comp_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fst _) _).
  spose (iso_to_from (κ E ((a, b); y))) as H0.
  destruct H0 as [H3 _].
  unfold κ in *.
  rewrite H3.
  rewrite id_left.
  symmetry.
  rewrite <- (id_left (snd _)).
  rewrite H2.
  rewrite !fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap (snd (to (κ E ((a, b); x)))))).
  rewrite <- fmap_comp.
  spose (iso_to_from (κ E ((a, b); x))) as H0.
  destruct H0 as [_ H4].
  rewrite H4.
  rewrite fmap_id, id_left.
  remember (fmap[to (lawvere_iso E)] _) as o.
  destruct o; simpl in *.
  symmetry.
  apply e.
Qed.

Program Instance lawvere_from_Proper {a b} :
  Proper (equiv ==> equiv) (@ψ' E a b).
Next Obligation.
  proper.
  unfold ψ', lawvere_from.
  spose (θ E) as H.
  given (ff : ((a, b); x) ~{ Id[D] ↓ G }~> ((a, b); y)).
    now refine ((id, id); _); abstract cat.
  spose (`2 (projG E) ((a, b); x) ((a, b); y) ff) as H0.
  destruct H0 as [H1 H2].
  rewrite <- id_left.
  rewrite H2.
  comp_left.
  rewrite (comp_assoc (snd (to (θ E ((a, b); x)))) (snd _)).
  spose (iso_to_from (θ E ((a, b); x))) as H0.
  destruct H0 as [_ H3].
  rewrite H3.
  rewrite id_left.
  symmetry.
  rewrite <- (id_right (fst _)).
  rewrite H1.
  rewrite comp_assoc.
  spose (iso_to_from (θ E ((a, b); y))) as H0.
  destruct H0 as [H4 _].
  rewrite comp_assoc.
  rewrite H4.
  rewrite !fmap_comp.
  comp_right.
  rewrite fmap_id, id_right.
  remember (fmap[from (lawvere_iso E)] _) as o.
  destruct o; simpl in *.
  apply e.
Qed.

Ltac pair_comp :=
  match goal with
  | [ |- context[@fst _ _ ?F ∘ @fst _ _ ?G] ] =>
    rewrite (@fst_comp _ _ _ _ _ F G)
  | [ |- context[@snd _ _ ?F ∘ @snd _ _ ?G] ] =>
    rewrite (@snd_comp _ _ _ _ _ F G)
  end.

Arguments φ' l {_ _} _.
Arguments ψ' l {_ _} _.

Lemma lawvere_iso_to {a b} (f : F a ~> b) :
  φ E ((a, b); f) ≅ ((a, b); φ' E f).
Proof.
  construct.
  - exists (from (κ E ((a, b); f))).
    abstract
      (unfold φ', lawvere_to;
       rewrite <- !comp_assoc;
       pair_comp;
       rewrite iso_to_from;
       simpl fst;
       now rewrite id_right).
  - exists (to (κ E ((a, b); f))).
    abstract
      (unfold φ', lawvere_to;
       rewrite !comp_assoc;
       rewrite <- !fmap_comp;
       pair_comp;
       rewrite iso_to_from;
       simpl snd;
       now rewrite fmap_id, id_left).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_from_to).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_to_from).
Defined.

Lemma lawvere_iso_from {a b} (g : a ~> G b) :
  ψ E ((a, b); g) ≅ ((a, b); ψ' E g).
Proof.
  construct.
  - exists (from (θ E ((a, b); g))).
    abstract
      (unfold ψ', lawvere_from;
      rewrite <- !comp_assoc;
      rewrite <- !fmap_comp;
      pair_comp;
      rewrite iso_to_from;
      simpl fst;
      now rewrite fmap_id, id_right).
  - exists (to (θ E ((a, b); g))).
    abstract
      (unfold ψ', lawvere_from;
       rewrite !comp_assoc;
       pair_comp;
       rewrite iso_to_from;
       simpl snd;
       now rewrite id_left).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_from_to).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_to_from).
Defined.

Lemma lawvere_iso_from_to {a b} (f : F a ~> b) :
  ψ E (φ E ((a, b); f)) ≅ ((a, b); ψ' E (φ' E f)).
Proof.
  refine (iso_compose (lawvere_iso_from (φ' E f)) _).
  apply fmap_iso.
  now apply lawvere_iso_to.
Defined.

Definition lawvere_iso_to_from {a b} (g : a ~> G b) :
  φ E (ψ E ((a, b); g)) ≅ ((a, b); φ' E (ψ' E g)).
Proof.
  refine (iso_compose (lawvere_iso_to (ψ' E g)) _).
  apply fmap_iso.
  now apply lawvere_iso_from.
Defined.

Definition lawvere_to_from_iso {a b} (g : a ~> G b) :
  ((a, b); φ' E (ψ' E g)) ≅[Id[D] ↓ G] ((a, b); g) :=
  iso_compose (`1 (iso_to_from (lawvere_iso E)) ((a, b); g))
              (iso_sym (@lawvere_iso_to_from _ _ g)).

Definition lawvere_from_to_iso {a b} (f : F a ~> b) :
  ((a, b); ψ' E (φ' E f)) ≅[F ↓ Id[C]] ((a, b); f) :=
  iso_compose (`1 (iso_from_to (lawvere_iso E)) ((a, b); f))
              (iso_sym (@lawvere_iso_from_to _ _ f)).

Lemma lawvere_to_functorial {a b} (f : F a ~{C}~> b)
      {a' b'} (i : a' ~> a) (j : b ~> b') :
  φ' E (j ∘ f ∘ fmap[F] i) ≈ fmap[G] j ∘ φ' E f ∘ i.
Proof.
  (* φ'(j ∘ f ∘ Fi) = φ'(j ∘ f) ∘ i *)

  given (Fi : ((a', b'); j ∘ f ∘ fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b'); j ∘ f)).
    now refine ((i, id); _); abstract cat.

  spose (`2 (to (lawvere_iso_to (j ∘ f))
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (j ∘ f ∘ fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', b'); j ∘ f ∘ fmap[F] i) ((a, b'); j ∘ f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite fmap_id, id_left in H.
  rewrite <- H.
  clear Fi H.

  (*                = G(j ∘ f) ∘ φ'(Fi) *)

  given (Fi : ((a', F a); fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b'); j ∘ f)).
    now refine ((i, j ∘ f); _); abstract cat.
  spose (`2 (to (lawvere_iso_to (j ∘ f))
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', F a); fmap[F] i) ((a, b'); j ∘ f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite H.
  clear Fi H.

  (*                = Gj ∘ Gf ∘ φ'(Fi) *)

  rewrite fmap_comp.

  (*                = Gj ∘ φ'(f) ∘ i *)

  given (Fi : ((a', F a); fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b); f)).
    now refine ((i, f); _); abstract cat.
  spose (`2 (to (lawvere_iso_to f)
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', F a); fmap[F] i) ((a, b); f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- comp_assoc.
  rewrite <- H.
  now cat.
Qed.

Lemma lawvere_from_functorial {a b} (g : a ~{D}~> G b)
      {a' b'} (i : a' ~> a) (j : b ~> b') :
  j ∘ ψ' E g ∘ fmap[F] i ≈ ψ' E (fmap[G] j ∘ g ∘ i).
Proof.
  (* ψ'(Gj ∘ g ∘ i) = j ∘ ψ'(g ∘ i) *)

  given (Gj : ((a', b); g ∘ i) ~{ Id[D] ↓ G }~> ((a', b'); fmap[G] j ∘ g ∘ i)).
    now refine ((id, j); _); simpl; abstract cat.
  spose (`2 (to (lawvere_iso_from (fmap[G] j ∘ g ∘ i))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g ∘ i)))) as H.
  spose (`2 (projG E) ((a', b); g ∘ i) ((a', b'); fmap[G] j ∘ g ∘ i) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite fmap_id, id_right in H.
  rewrite H.
  clear Gj H.

  (*                = ψ'(Gj) ∘ F(g ∘ i) *)

  given (Gj : ((a', b); g ∘ i) ~{ Id[D] ↓ G }~> ((G b, b'); fmap[G] j)).
    now refine ((g ∘ i, j); _); simpl; abstract cat.
  spose (`2 (to (lawvere_iso_from (fmap[G] j))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g ∘ i)))) as H.
  spose (`2 (projG E) ((a', b); g ∘ i) ((G b, b'); fmap[G] j) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- H.
  clear Gj H.

  (*                = ψ'(Gj) ∘ Fg ∘ Fi *)

  rewrite fmap_comp.

  (*                = Gj ∘ ψ'(f) ∘ i *)

  given (Gj : ((a, b); g) ~{ Id[D] ↓ G }~> ((G b, b'); fmap[G] j)).
    now refine ((g, j); _); simpl; abstract cat.
  spose (`2 (to (lawvere_iso_from (fmap[G] j))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g)))) as H.
  spose (`2 (projG E) ((a, b); g) ((G b, b'); fmap[G] j) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- H.
  now cat.
Qed.

Lemma surjective_tripleF (p : obj[F ↓ Id[C]]) :
  existT _ (fst `1 p, snd `1 p) (`2 p) = p.
Proof.
  destruct p; simpl.
  simpl_eq.
  destruct x; simpl.
  reflexivity.
Defined.

Lemma surjective_tripleG (p : obj[Id[D] ↓ G]) :
  existT _ (fst `1 p, snd `1 p) (`2 p) = p.
Proof.
  destruct p; simpl.
  simpl_eq.
  destruct x; simpl.
  reflexivity.
Defined.

Lemma expand_φ_ψ {a b} (g : a ~> G b) :
  φ E (ψ E ((a, b); g))
    ≈
  φ E
    ((fst `1 ((lawvere_iso E)⁻¹ ((a, b); g)),
      snd `1 ((lawvere_iso E)⁻¹ ((a, b); g)));
       `2 ((lawvere_iso E)⁻¹ ((a, b); g))).
Proof. now rewrite surjective_tripleF. Defined.

Lemma expand_ψ_φ {a b} (f : F a ~> b) :
  ψ E (φ E ((a, b); f))
    ≈
  ψ E
    ((fst `1 (φ E ((a, b); f)),
      snd `1 (φ E ((a, b); f)));
       `2 (φ E ((a, b); f))).
Proof. now rewrite surjective_tripleG. Defined.

(** Given that:

      π₁((A,B);f) = (A,B)
        = π₁(φ((A,B);f)) = π₁(φ((A,B);f))       [projF, projG]
      φ((A,B);f) ≅ ((A,B);φ'(f))                [lawvere_iso_to]
      ψ((A,B);f) ≅ ((A,B);ψ'(f))                [lawvere_iso_from]
      φ(ψ(f)) ≈ f and ψ(φ(f)) ≈ f               [lawvere_iso]

    it follows that:

      φ'(ψ'(f)) ≈ f and ψ'(φ'(f)) ≈ f *)

Lemma lawvere_to_from {a b} (g : a ~> G b) : φ' E (ψ' E g) ≈ g.
Proof.
  intros.
  unfold φ', ψ'.
  unfold lawvere_from.
  rewrite lawvere_to_functorial.
  unfold lawvere_to.
  simpl in *.
  spose (φ_ψ_equiv ((a, b); g)) as X1.
  spose (surjective_tripleF (ψ E ((a, b); g))) as X2.
  symmetry.
  etransitivity.
    symmetry in X1.
    apply X1.
  comp_left.
  comp_right.
  now rewrite <- X2.
Qed.

Lemma lawvere_from_to {a b} (f : F a ~> b) : ψ' E (φ' E f) ≈ f.
Proof.
  intros.
  unfold φ', ψ'.
  unfold lawvere_to.
  rewrite <- lawvere_from_functorial.
  unfold lawvere_from.
  simpl in *.
  spose (ψ_φ_equiv ((a, b); f)) as X1.
  spose (surjective_tripleG (φ E ((a, b); f))) as X2.
  symmetry.
  etransitivity.
    symmetry in X1.
    apply X1.
  comp_left.
  comp_right.
  now rewrite <- X2.
Qed.

Program Instance lawvere_morph_iso {a b} : F a ~> b ≊ a ~> G b := {
  to   := {| morphism := φ' E; proper_morphism := lawvere_to_Proper |};
  from := {| morphism := ψ' E; proper_morphism := lawvere_from_Proper |};
  iso_to_from := lawvere_to_from;
  iso_from_to := lawvere_from_to
}.

Corollary lawvere_to_morph_iso_functorial {a b} (f : F a ~{C}~> b)
          {a' b'} (i : a' ~> a) (j : b ~> b') :
  to lawvere_morph_iso (j ∘ f ∘ fmap[F] i)
    ≈ fmap[G] j ∘ to lawvere_morph_iso f ∘ i.
Proof. now apply lawvere_to_functorial. Qed.

Corollary lawvere_from_morph_iso_functorial {a b} (g : a ~{D}~> G b)
          {a' b'} (i : a' ~> a) (j : b ~> b') :
  j ∘ from lawvere_morph_iso g ∘ fmap[F] i
    ≈ from lawvere_morph_iso (fmap[G] j ∘ g ∘ i).
Proof. now apply lawvere_from_functorial. Qed.

Program Definition Left_Functor : D ⟶ (F ↓ Id[C]) := {|
  fobj := fun x : D => ((x, F x); id[F x]);
  fmap := fun _ _ f => ((f, fmap[F] f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. split; [ reflexivity | apply fmap_comp ]. Qed.

Program Definition Right_Functor : C ⟶ (Id[D] ↓ G) := {|
  fobj := fun x : C => ((G x, x); id[G x]);
  fmap := fun _ _ f => ((fmap[G] f, f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. split; [ apply fmap_comp | reflexivity ]. Qed.

Definition lawvere_eqv_unit {a} : a ~{ D }~> G (F a) :=
  to lawvere_morph_iso (`2 (Left_Functor a)).

Definition lawvere_eqv_counit {a} : F (G a) ~{ C }~> a :=
  from lawvere_morph_iso (`2 (Right_Functor a)).

Lemma lawvere_eqv_counit_fmap_unit {a} :
  lawvere_eqv_counit ∘ fmap[F] lawvere_eqv_unit ≈ id[F a].
Proof.
  simpl; intros.
  unfold lawvere_eqv_counit, lawvere_eqv_unit.
  rewrite <- id_left.
  rewrite comp_assoc.
  rewrite lawvere_from_morph_iso_functorial.
  simpl (`2 _).
  rewrite fmap_id, !id_left.
  now sapply (iso_from_to (@lawvere_morph_iso a (F a))).
Qed.

Lemma lawvere_eqv_fmap_counit_unit {a} :
  fmap[G] lawvere_eqv_counit ∘ lawvere_eqv_unit ≈ id[G a].
Proof.
  simpl; intros.
  unfold lawvere_eqv_counit, lawvere_eqv_unit.
  rewrite <- (id_right (to lawvere_morph_iso _)).
  rewrite comp_assoc.
  rewrite <- lawvere_to_morph_iso_functorial.
  simpl (`2 _).
  rewrite fmap_id, !id_right.
  now sapply (iso_to_from (@lawvere_morph_iso (G a) a)).
Qed.

Lemma Left_Functoriality
      x y (f : comma_proj (Left_Functor x) ~> comma_proj (Left_Functor y)) :
  fmap[G] (fmap[F] (fst f))
    ∘ (fmap[G] (snd (κ E (Left_Functor x))⁻¹)
         ∘ `2 (φ E (Left_Functor x))
         ∘ fst (to (κ E (Left_Functor x))))
    ≈ fmap[G] (snd (κ E (Left_Functor y))⁻¹)
        ∘ `2 (φ E (Left_Functor y))
        ∘ fst (to (κ E (Left_Functor y)))
        ∘ fst f.
Proof.
  Opaque Left_Functor.
  given (ff : (Left_Functor x) ~{ F ↓ Id[C] }~> (Left_Functor y)).
    exists (fst f, fmap[F] (fst f)).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  destruct (`2 (projF E) (Left_Functor x) (Left_Functor y) ff).
  simpl in *.
  rewrite e0.
  do 2 rewrite fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap[G] (snd (to (κ E (Left_Functor x)))))).
  rewrite <- fmap_comp.
  rewrite (snd (iso_to_from (κ E (Left_Functor x)))).
  simpl snd.
  rewrite fmap_id.
  rewrite id_left.
  symmetry.
  spose (`2 (fmap[φ E] ff)) as X.
  rewrite !comp_assoc.
  rewrite <- X.
  comp_left.
  rewrite e at 1.
  comp_right.
  rewrite (fst (iso_to_from (κ E (Left_Functor y)))).
  rewrite id_left.
  reflexivity.
Qed.

Lemma Right_Functoriality
      x y (f : comma_proj (Right_Functor x) ~> comma_proj (Right_Functor y)) :
  snd f ∘ (snd (θ E (Right_Functor x))⁻¹
        ∘ `2 ((lawvere_iso E)⁻¹ (Right_Functor x))
        ∘ fmap[F] (fst (to (θ E (Right_Functor x)))))
  ≈ snd (θ E (Right_Functor y))⁻¹
      ∘ `2 ((lawvere_iso E)⁻¹ (Right_Functor y))
      ∘ fmap[F] (fst (to (θ E (Right_Functor y))))
      ∘ fmap[F] (fmap[G] (snd f)).
Proof.
  Opaque Right_Functor.
  given (ff : (Right_Functor x) ~{ Id[D] ↓ G }~> (Right_Functor y)).
    exists (fmap[G] (snd f), snd f).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  destruct (`2 (projG E) (Right_Functor x) (Right_Functor y) ff).
  simpl in *.
  symmetry.
  rewrite e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite (fst (iso_to_from (θ E (Right_Functor y)))).
  rewrite id_left.
  symmetry.
  rewrite e0 at 1.
  comp_left.
  rewrite (comp_assoc (snd (to (θ E (Right_Functor x))))).
  rewrite (snd (iso_to_from (θ E (Right_Functor x)))).
  rewrite id_left.
  rewrite fmap_comp.
  comp_right.
  symmetry.
  apply (`2 (fmap[ψ E] ff)).
Qed.

Program Definition lawvere_eqv_unit_transform : Id ⟹ G ○ F := {|
  transform := @lawvere_eqv_unit;
  naturality := fun x y f =>
    Left_Functoriality x y (f, fmap[F] f);
  naturality_sym := fun x y f =>
    symmetry (Left_Functoriality x y (f, fmap[F] f))
|}.

Program Definition lawvere_eqv_counit_transform : F ○ G ⟹ Id := {|
  transform := @lawvere_eqv_counit;
  naturality := fun x y f =>
    Right_Functoriality x y (fmap[G] f, f);
  naturality_sym := fun x y f =>
    symmetry (Right_Functoriality x y (fmap[G] f, f))
|}.

Program Definition Comma_Functor_F_Id_Id_G (H : F ⊣ G) :
  (F ↓ Id[C]) ⟶ (Id[D] ↓ G) := {|
  fobj := fun x => (``x; to adj (`2 x));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- to_adj_nat_r;
  rewrite <- X;
  rewrite <- to_adj_nat_l;
  reflexivity.
Qed.

Program Definition Comma_Functor_Id_G_F_Id (H : F ⊣ G) :
  (Id[D] ↓ G) ⟶ (F ↓ Id[C]) := {|
  fobj := fun x => (``x; from adj (`2 x));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- from_adj_nat_r;
  rewrite <- X;
  rewrite <- from_adj_nat_l;
  reflexivity.
Qed.

Program Instance Comma_F_Id_Id_G_Iso (H : F ⊣ G) :
  (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G) := {
  to   := Comma_Functor_F_Id_Id_G H;
  from := Comma_Functor_Id_G_F_Id H
}.
Next Obligation.
  constructive; simpl.
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity).
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
Defined.
Next Obligation.
  constructive; simpl.
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity).
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
Defined.

End AdjunctionComma.

Theorem Adjunction_Comma `{F : D ⟶ C} `{G : C ⟶ D} :
  F ⊣ G  ↔  @lawvere_equiv _ _ F G.
Proof.
  split; intros H. {
    unshelve refine {| lawvere_iso := Comma_F_Id_Id_G_Iso H |}.
    - simpl; unshelve eexists; intros; split;
      destruct f; simpl; cat.
    - simpl; unshelve eexists; intros; split;
      destruct f; simpl; cat.
    - intros; simpl; cat.
    - intros; simpl; cat.
  }

  apply Adjunction_from_Transform.

  exact (Build_Adjunction_Transform
           (@lawvere_eqv_unit_transform _ _ _ _ H)
           (@lawvere_eqv_counit_transform _ _ _ _ H)
           (@lawvere_eqv_counit_fmap_unit _ _ _ _ H)
           (@lawvere_eqv_fmap_counit_unit _ _ _ _ H)).
Qed.
