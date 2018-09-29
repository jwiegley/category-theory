Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Adjunction.Natural.Transformation.
Require Export Category.Adjunction.Natural.Transformation.Universal.
Require Export Category.Construction.Comma.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

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
   x = φ(yf) in B."

   Repeating this using the names and syntax of this module:

   "∀ (G : C ⟶ D) (F : D ⟶ C), F ⊣ G ↔
      ∀ d : D, ∃ (c : C) (phi : d ~{D}~> G c),
        ∀ (c′ : C) (psi : d ~{D}~> G c′), ∃! y : c ~{C}~> c′,
          psi ≈ fmap[G] y ∘ phi" *)

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {G : C ⟶ D}.

Program Definition Left_Functor : D ⟶ (F ↓ Id[C]) := {|
  fobj := fun x : D => ((x, F x); id[F x]);
  fmap := fun _ _ f => ((f, fmap[F] f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  split.
    reflexivity.
  apply fmap_comp.
Qed.

Program Definition Right_Functor : C ⟶ (Id[D] ↓ G) := {|
  fobj := fun x : C => ((G x, x); id[G x]);
  fmap := fun _ _ f => ((fmap[G] f, f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  split.
    apply fmap_comp.
  reflexivity.
Qed.

Record lawvere_equiv := {
  lawvere_iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G);

  projF : comma_proj ≈[Cat] comma_proj ○ to lawvere_iso;
  projG : comma_proj ≈[Cat] comma_proj ○ from lawvere_iso
}.

Context `(E : lawvere_equiv).

Definition lawvere_to {a b} (f : F a ~> b) : a ~> G b :=
  let o := ((a, b); f) in
  fmap[G] (snd (from (`1 (projF E) o)))
    ∘ `2 (to (lawvere_iso E) o)
    ∘ fst (to (`1 (projF E) o)).

Ltac pair_comp :=
  match goal with
  | [ |- context[@fst _ _ ?F ∘ @fst _ _ ?G] ] =>
    rewrite (@fst_comp _ _ _ _ _ F G)
  | [ |- context[@snd _ _ ?F ∘ @snd _ _ ?G] ] =>
    rewrite (@snd_comp _ _ _ _ _ F G)
  end.

Lemma lawvere_iso_to {a b} (f : F a ~> b) :
  to (lawvere_iso E) ((a, b); f) ≅[Id[D] ↓ G] ((a, b); lawvere_to f).
Proof.
  construct.
  - exists (from (`1 (projF E) ((a, b); f))).
    unfold lawvere_to.
    rewrite <- !comp_assoc.
    pair_comp.
    rewrite iso_to_from.
    simpl fst.
    now rewrite id_right.
  - exists (to (`1 (projF E) ((a, b); f))).
    unfold lawvere_to.
    rewrite !comp_assoc.
    rewrite <- !fmap_comp.
    pair_comp.
    rewrite iso_to_from.
    simpl snd.
    now rewrite fmap_id, id_left.
  - simpl.
    split; pair_comp;
    now rewrite iso_from_to.
  - simpl.
    split; pair_comp;
    now rewrite iso_to_from.
Defined.

Definition lawvere_from {a b} (g : a ~> G b) : F a ~> b :=
  let o := ((a, b); g) in
  snd (from (`1 (projG E) o))
    ∘ `2 (from (lawvere_iso E) o)
    ∘ fmap (fst (to (`1 (projG E) o))).

Lemma lawvere_iso_from {a b} (g : a ~> G b) :
  from (lawvere_iso E) ((a, b); g) ≅[F ↓ Id[C]] ((a, b); lawvere_from g).
Proof.
  construct.
  - exists (from (`1 (projG E) ((a, b); g))).
    unfold lawvere_from.
    rewrite <- !comp_assoc.
    rewrite <- !fmap_comp.
    pair_comp.
    rewrite iso_to_from.
    simpl fst.
    now rewrite fmap_id, id_right.
  - exists (to (`1 (projG E) ((a, b); g))).
    unfold lawvere_from.
    rewrite !comp_assoc.
    pair_comp.
    rewrite iso_to_from.
    simpl snd.
    now rewrite id_left.
  - simpl.
    split; pair_comp;
    now rewrite iso_from_to.
  - simpl.
    split; pair_comp;
    now rewrite iso_to_from.
Defined.

Lemma lawvere_to_functorial {a b} (f : F a ~{C}~> b)
      {a' b'} (i : a' ~> a) (j : b ~> b') :
  lawvere_to (j ∘ f ∘ fmap[F] i) ≈ fmap[G] j ∘ lawvere_to f ∘ i.
Proof.
  (* φ'(j ∘ f ∘ Fi) = φ'(j ∘ f) ∘ i *)

  given (Fi : ((a', b'); j ∘ f ∘ fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b'); j ∘ f)).
    now refine ((i, id); _); abstract cat.

  spose (`2 (to (lawvere_iso_to (j ∘ f))
                ∘ fmap[to (lawvere_iso E)] Fi
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
                ∘ fmap[to (lawvere_iso E)] Fi
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
                ∘ fmap[to (lawvere_iso E)] Fi
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
  j ∘ lawvere_from g ∘ fmap[F] i ≈ lawvere_from (fmap[G] j ∘ g ∘ i).
Proof.
  (* ψ'(Gj ∘ g ∘ i) = j ∘ ψ'(g ∘ i) *)

  given (Gj : ((a', b); g ∘ i) ~{ Id[D] ↓ G }~> ((a', b'); fmap[G] j ∘ g ∘ i)).
    now refine ((id, j); _); simpl; abstract cat.
  spose (`2 (to (lawvere_iso_from (fmap[G] j ∘ g ∘ i))
                ∘ fmap[from (lawvere_iso E)] Gj
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
                ∘ fmap[from (lawvere_iso E)] Gj
                ∘ from (lawvere_iso_from (g ∘ i)))) as H.
  spose (`2 (projG E) ((a', b); g ∘ i) ((G b, b'); fmap[G] j) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- H.
  clear Gj H.

  (*                = ψ'(Gj) ∘ Gg ∘ Gi *)

  rewrite fmap_comp.

  (*                = Gj ∘ ψ'(f) ∘ i *)

  given (Gj : ((a, b); g) ~{ Id[D] ↓ G }~> ((G b, b'); fmap[G] j)).
    now refine ((g, j); _); simpl; abstract cat.
  spose (`2 (to (lawvere_iso_from (fmap[G] j))
                ∘ fmap[from (lawvere_iso E)] Gj
                ∘ from (lawvere_iso_from (g)))) as H.
  spose (`2 (projG E) ((a, b); g) ((G b, b'); fmap[G] j) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- H.
  now cat.
Qed.

Program Instance lawvere_morph_iso {a b} : F a ~> b ≊ a ~> G b := {
  to   := {| morphism := lawvere_to |};
  from := {| morphism := lawvere_from |}
}.
Next Obligation.
  proper.
(*
  unfold lawvere_to.
  given (h : ((F a, a); lawvere_to x) ~{ Id[D] ↓ G }~> ((G (F a), F a); id)).
    simpl.
    refine ((lawvere_to (`2 (Left_Functor a)), id); _).
    refine ((lawvere_to (`2 (Left_Functor a)), id); _).
    refine ((`2 (to (lawvere_iso E) ((a, b); x)), id); _).
    refine (((`2 (to (lawvere_iso_to _)
                ∘ to (lawvere_iso E) ((a, b); x)
                ∘ from (lawvere_iso_to _))), id); _).
    now refine ((id, id); _); simpl; abstract cat.
  pose ((`1 (projF E) ((a, b); x))⁻¹).
  simpl in h.
  given (h : _ ~{ F ↓ Id[C] }~> _).
    now refine (((`1 (projF E) ((a, b); x))⁻¹, id); _); simpl; abstract cat.
  pose proof (`2 (iso_to_from (lawvere_iso E))).
  simpl in X0.
  destruct E; simpl in *.
  destruct lawvere_iso0; simpl in *.
*)
Admitted.
Next Obligation.
  proper.
Admitted.
Next Obligation.
  unfold lawvere_to.
(*
  rewrite <- !snd_comp.
  rewrite <- !fst_comp.
  rewrite <- !fmap_comp.

  pose proof (`2 (iso_to_from (lawvere_iso E))).
  simpl in X.

  pose proof (monic (Monic:=iso_to_monic (lawvere_iso_to (lawvere_from g)))) as H.
  apply H.
  unfold lawvere_to.

  enough (lawvere_to (lawvere_from g) ≈ fmap id ∘ g ∘ id).
    now rewrite fmap_id, id_left, id_right in X.

  unfold lawvere_to.
  given (h : ((a, b); lawvere_from g) ~{ F ↓ Id[C] }~> ((a, b); lawvere_from g)).
    now refine ((id, id); _); simpl; abstract cat.
  spose (`2 (projF E) ((a, b); lawvere_from g) ((a, b); lawvere_from g) h) as H0.
  destruct H0 as [H1 H2].
  rewrite H1, H2; clear H1 H2.
  rewrite fmap_comp.
  rewrite fmap_comp.
  comp_left.
  comp_right.
  spose (`2 (from (lawvere_iso_from g)
                ∘ h
                ∘ to (lawvere_iso_from g))) as H.
  unfold h in *; clear h; simpl in *.

  spose (iso_to_from (`1 (iso_to_from (lawvere_iso E)) ((a, b); g))) as H.
  unfold lawvere_to.
  spose (`2 (to (lawvere_iso_to (lawvere_from g)))) as H0.
  spose (`2 (projF E) ((a, b); lawvere_from g)) as H1.
  rewrite <- H0.
  unfold lawvere_from.
  rewrite (`2 (to (lawvere_iso_from g))) as H0.
  rewrite <- H0.
  destruct H0, to.
*)
Admitted.
Next Obligation.
Admitted.

Lemma Left_Functoriality
      x y (f : comma_proj (Left_Functor x) ~> comma_proj (Left_Functor y)) :
  fmap[G] (fmap[F] (fst f))
    ∘ (fmap[G] (snd (`1 (projF E) (Left_Functor x))⁻¹)
         ∘ `2 (to (lawvere_iso E) (Left_Functor x))
         ∘ fst (to (`1 (projF E) (Left_Functor x))))
    ≈ fmap[G] (snd (`1 (projF E) (Left_Functor y))⁻¹)
        ∘ `2 (to (lawvere_iso E) (Left_Functor y))
        ∘ fst (to (`1 (projF E) (Left_Functor y)))
        ∘ fst f.
Proof.
  Opaque Left_Functor.
  given (ff :
    { f : (fst `1 (Left_Functor x) ~{ D }~> fst `1 (Left_Functor y)) *
          (snd `1 (Left_Functor x) ~{ C }~> snd `1 (Left_Functor y))
    & `2 (Left_Functor y) ∘ fmap[F] (fst f) ≈ snd f ∘ `2 (Left_Functor x) }).
    exists (fst f, fmap[F] (fst f)).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  destruct (`2 (projF E) (Left_Functor x) (Left_Functor y) ff).
  simpl in *.
  rewrite e0.
  do 2 rewrite fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap[G] (snd (to (`1 (projF E) (Left_Functor x)))))).
  rewrite <- fmap_comp.
  rewrite (snd (iso_to_from (`1 (projF E) (Left_Functor x)))).
  simpl snd.
  rewrite fmap_id.
  rewrite id_left.
  symmetry.
  spose (`2 (fmap[to (lawvere_iso E)] ff)) as X.
  rewrite !comp_assoc.
  rewrite <- X.
  comp_left.
  rewrite e at 1.
  comp_right.
  rewrite (fst (iso_to_from (`1 (projF E) (Left_Functor y)))).
  rewrite id_left.
  reflexivity.
Qed.

Lemma Right_Functoriality
      x y (f : comma_proj (Right_Functor x) ~> comma_proj (Right_Functor y)) :
  snd f ∘ (snd (`1 (projG E) (Right_Functor x))⁻¹
        ∘ `2 ((lawvere_iso E)⁻¹ (Right_Functor x))
        ∘ fmap[F] (fst (to (`1 (projG E) (Right_Functor x)))))
  ≈ snd (`1 (projG E) (Right_Functor y))⁻¹
      ∘ `2 ((lawvere_iso E)⁻¹ (Right_Functor y))
      ∘ fmap[F] (fst (to (`1 (projG E) (Right_Functor y))))
      ∘ fmap[F] (fmap[G] (snd f)).
Proof.
  Opaque Right_Functor.
  given (ff :
    { f : (fst `1 (Right_Functor x) ~{ D }~> fst `1 (Right_Functor y)) *
          (snd `1 (Right_Functor x) ~{ C }~> snd `1 (Right_Functor y))
    & `2 (Right_Functor y) ∘ fst f ≈ fmap[G] (snd f) ∘ `2 (Right_Functor x) }).
    exists (fmap[G] (snd f), snd f).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  destruct (`2 (projG E) (Right_Functor x) (Right_Functor y) ff).
  simpl in *.
  symmetry.
  rewrite e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite (fst (iso_to_from (`1 (projG E) (Right_Functor y)))).
  rewrite id_left.
  symmetry.
  rewrite e0 at 1.
  comp_left.
  rewrite (comp_assoc (snd (to (`1 (projG E) (Right_Functor x))))).
  rewrite (snd (iso_to_from (`1 (projG E) (Right_Functor x)))).
  rewrite id_left.
  rewrite fmap_comp.
  comp_right.
  symmetry.
  apply (`2 (fmap[from (lawvere_iso E)] ff)).
Qed.

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
    destruct x as [[x y] f]; cat.
    srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity.
  - exists (id, id).
    destruct x as [[x y] f]; cat.
    srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
Qed.
Next Obligation.
  constructive; simpl.
  - exists (id, id).
    destruct x as [[x y] f]; cat.
    srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity.
  - exists (id, id).
    destruct x as [[x y] f]; cat.
    srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
Qed.

Definition lawvere_eqv_unit `{E : @lawvere_equiv _ _ F G} {a} :
  a ~{ D }~> G (F a) := lawvere_to E (`2 (Left_Functor a)).

Definition lawvere_eqv_counit `{E : @lawvere_equiv _ _ F G} {a} :
  F (G a) ~{ C }~> a := lawvere_from E (`2 (Right_Functor a)).

Program Definition lawvere_eqv_unit_transform
        `{E : @lawvere_equiv _ _ F G} : Id ⟹ G ○ F := {|
  transform := @lawvere_eqv_unit E;
  naturality := fun x y f =>
    Left_Functoriality E x y (f, fmap[F] f);
  naturality_sym := fun x y f =>
    symmetry (Left_Functoriality E x y (f, fmap[F] f))
|}.

Program Definition lawvere_eqv_counit_transform
        `{E : @lawvere_equiv _ _ F G} : F ○ G ⟹ Id := {|
  transform := @lawvere_eqv_counit E;
  naturality := fun x y f =>
    Right_Functoriality E x y (fmap[G] f, f);
  naturality_sym := fun x y f =>
    symmetry (Right_Functoriality E x y (fmap[G] f, f))
|}.

Lemma lawvere_eqv_counit_fmap_unit `{E : @lawvere_equiv _ _ F G} {a} :
  @lawvere_eqv_counit E _ ∘ fmap[F] (@lawvere_eqv_unit E _) ≈ id[F a].
Proof.
  simpl; intros.
  unfold lawvere_eqv_counit, lawvere_eqv_unit.
  simpl.
  rewrite <- (id_left (lawvere_from _ _)).
  rewrite lawvere_from_functorial.
  cat.
  rewrite lawvere_from_to.
  reflexivity.
Qed.

Lemma lawvere_eqv_fmap_counit_unit `{E : @lawvere_equiv _ _ F G} {a} :
  fmap[G] (@lawvere_eqv_counit E _) ∘ @lawvere_eqv_unit E _ ≈ id[G a].
Proof.
  simpl; intros.
  unfold lawvere_eqv_counit, lawvere_eqv_unit.
  simpl.
  rewrite <- (id_right (lawvere_to _ _)).
  rewrite comp_assoc.
  rewrite lawvere_to_functorial.
  cat.
  rewrite lawvere_to_from.
  reflexivity.
Qed.

Theorem Adjunction_Comma : F ⊣ G  ↔  @lawvere_equiv _ _ F G.
Proof.
  split; intros H. {
    refine {| lawvere_iso := Comma_F_Id_Id_G_Iso H |}.
    - abstract (
        simpl; unshelve eexists; intros; split;
        destruct f; simpl; cat).
    - abstract (
        simpl; unshelve eexists; intros; split;
        destruct f; simpl; cat).
  }

  apply Adjunction_from_Transform.

  exact (Build_Adjunction_Transform
           (@lawvere_eqv_unit_transform H)
           (@lawvere_eqv_counit_transform H)
           (@lawvere_eqv_counit_fmap_unit H)
           (@lawvere_eqv_fmap_counit_unit H)).
Qed.

End AdjunctionComma.
