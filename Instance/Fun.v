Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section Fun.

Context {C : Category}.
Context {D : Category}.

(* nLab: https://ncatlab.org/nlab/show/functor+category
   Wikipedia: https://en.wikipedia.org/wiki/Functor_category

   The functor category `[C, D]` (also written `D^C`) has functors `C ⟶ D` as
   objects and natural transformations as morphisms. Composition is vertical
   composition of natural transformations (`nat_compose`), the identity is the
   identity natural transformation (`nat_id`), and the hom-setoid is
   componentwise: two natural transformations are equal exactly when their
   components agree at every object (this is the [Transform_Setoid] of
   [Theory.Natural.Transformation]). The unit and associativity laws hold
   componentwise, inherited from D, and are discharged by [Program] below.

   When D carries pointwise structure (limits, colimits, cartesian, closed),
   `[C, D]` inherits it pointwise from D; those instances live in their own
   files (e.g. under Structure) rather than here. *)

(* Where the functor category comes from, and what it is for

   nLab:  https://ncatlab.org/nlab/show/category+of+presheaves
   nLab:  https://ncatlab.org/nlab/show/Yoneda+embedding
   nLab:  https://ncatlab.org/nlab/show/Godement+product
   SEP:   https://plato.stanford.edu/entries/category-theory/
   Paper: Eilenberg, Mac Lane, "General Theory of Natural Equivalences",
          Transactions of the AMS 58, 1945

   The functor category is as old as category theory itself.  The founding
   paper of the subject already contains a section II.8 titled "Categories
   of functors", though a category of categories is nowhere mentioned in
   it, and its authors regarded everything beneath this level as
   scaffolding: "the whole concept of a category is essentially an
   auxiliary one; our basic concepts are essentially those of a functor
   and of natural transformation" (Eilenberg–Mac Lane 1945, p. 247, as
   quoted by the Stanford Encyclopedia of Philosophy).  Freyd compressed
   the genesis into a slogan — categories are what one must define in
   order to define functors, and functors are what one must define in
   order to define natural transformations (Freyd, "Abelian Categories",
   1964, introduction).  [Fun] realizes the construction as a first-class
   Category, so the ambient machinery of isomorphism, limit, and
   adjunction applies to functors one level up: "natural isomorphism" is
   nothing other than isomorphism in `[C, D]`, and
   [Functor_Setoid_Nat_Iso] (with standalone directions [iso_equiv] and
   [equiv_iso]) reduces such an isomorphism to a componentwise family, so
   invertibility of a transformation is checked one object at a time.

   Three canonical uses organize the applications.  Presheaf categories
   `[C^op, Sets]` are the leading case: their limits, colimits, epis and
   monos are computed objectwise, they are cartesian closed, and the
   Yoneda embedding into them is fully faithful — for a small category,
   its free cocompletion — so every category embeds into a functor
   category built from itself (nLab, "category of presheaves" and "Yoneda
   embedding"); in-tree, Functor/Hom/Yoneda.v develops the lemma and the
   embedding over exactly these hom-setoids, and Theory/Sheaf.v defines
   `Presheaves` as literally `[U^op, C]`.  Diagram categories are the
   domain of limit-taking: a J-shaped diagram in C is an object of
   `[J, C]`, a cone is a morphism out of a constant functor, and
   completeness is the adjoint sandwich colim ⊣ Δ ⊣ lim around the
   diagonal Δ : C ⟶ [J, C] of Functor/Diagonal.v.  And `[C, D]` is the
   exponential witnessing that Cat is cartesian closed
   (Instance/Cat/Cartesian/Closed.v); equivalently, functor categories
   are the hom-categories of the 2-category Cat (nLab, "functor
   category").  Representation theory rides the same construction: a
   representation is a functor out of a one-object domain, and an
   intertwiner between representations is a natural transformation
   (nLab, "representation").

   The 2-categorical reading explains the middle of this file.  The
   whiskering laws and the coherence isomorphisms [nat_λ], [nat_ρ], and
   [nat_α] are precisely the unitor and associator data that
   Instance/Cat/Bicategory.v consumes to make Cat a bicategory with
   `bicat C D ≡ [C, D]` definitionally, reconciling the reversed naming
   noted below (`hunit_left := nat_ρ`, `hunit_right := nat_λ`).
   Horizontal composition of natural transformations is the Godement
   product, named after Roger Godement, and the agreement of its two
   defining formulas IS the interchange law (nLab, "Godement product");
   [whisker_left_right] states its whiskered form here.  One level down,
   the endofunctor category `[C, C]` is monoidal under composition, and a
   monad is exactly a monoid in it (Monad/Monoid.v, [Compose_Monoidal]);
   the classes [Pointed] and [WellPointed] below live at the same
   address.

   The computational reading rests on parametricity.  In a polymorphic
   language a natural transformation is a function of type
   `forall a. F a -> G a`, and parametricity yields the naturality square
   as a free theorem, so functors and polymorphic functions form a
   functor category whose vertical composition is componentwise program
   composition (Milewski, "Natural Transformations", 2015).  Throughout,
   the governing principle is pointwise inheritance: when D has limits or
   colimits of a given shape, so does `[C, D]`, computed pointwise (with
   the caveat that an incomplete D can possess accidental limits that are
   not pointwise), and when C is small and D is cartesian closed and
   complete, `[C, D]` is cartesian closed (nLab, "functor category");
   Instance/Fun/Cartesian.v instantiates the cartesian case. *)

Program Definition Fun : Category := {|
  obj     := C ⟶ D;                 (* objects are functors C ⟶ D *)
  hom     := @Transform C D;        (* morphisms are natural transformations *)
  id      := @nat_id C D;           (* identity natural transformation *)
  compose := @nat_compose C D;      (* vertical composition of nat-transes *)

  compose_respects := @nat_compose_respects C D
|}.

End Fun.

Notation "[ C , D ]" := (@Fun C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "[[[ C , D ]]]( F , G )" := ({| carrier   := @hom (@Fun C D) F G
                                       ; is_setoid := @homset (@Fun C D) F G |})
  (at level 90, right associativity, format "[[[ C ,  D ]]]( F , G )") : homset_scope.

(* The category laws restated directly for `[C, D]`: left/right identity and
   associativity of vertical composition, each holding componentwise in D. *)

Corollary nat_id_left C D (F G : C ⟶ D) (N : F ⟹ G) :
  nat_id ∙ N ≈[Fun] N.
Proof. unfold nat_id, nat_compose; simpl; intros; cat. Qed.

Corollary nat_id_right C D (F G : C ⟶ D) (N : F ⟹ G) :
  N ∙ nat_id ≈[Fun] N.
Proof. unfold nat_id, nat_compose; simpl; intros; cat. Qed.

Corollary nat_comp_assoc C D (F G H J : C ⟶ D)
          (M : H ⟹ J) (N : G ⟹ H) (O : F ⟹ G) :
  M ∙ (N ∙ O) ≈[Fun] (M ∙ N) ∙ O.
Proof. unfold nat_compose; simpl; intros; cat. Qed.

(* Whiskering and coherence laws for natural transformations viewed in the
   functor category: whiskering the identity yields an identity, whiskering
   distributes over vertical composition, and the interchange law relates left
   and right whiskering (see Theory/Natural/Transformation.v for `⊲`/`⊳`). *)

Lemma whisker_right_id A B C (F : A ⟶ B) (G : B ⟶ C) : id{Fun} ⊲ F ≈ id{Fun}.
Proof. simpl; intros; cat. Qed.

Lemma whisker_left_id A B C (F : A ⟶ B) (G : B ⟶ C) : G ⊳ id{Fun} ≈ id{Fun}.
Proof. simpl; intros; cat. Qed.

Lemma whisker_left_dist A B C (F : A ⟶ B) (G H J : B ⟶ C)
      (η : G ⟹ H) (θ : H ⟹ J) : (θ ⊲ F) ∙ (η ⊲ F) ≈ (θ ∙ η) ⊲ F.
Proof. simpl; intros; cat. Qed.

Lemma whisker_right_dist A B C (F G H : A ⟶ B) (J : B ⟶ C)
      (η : F ⟹ G) (θ : G ⟹ H) : (J ⊳ θ) ∙ (J ⊳ η) ≈ J ⊳ (θ ∙ η).
Proof. simpl; intros; cat. now rewrite fmap_comp. Qed.

(* The unitors and associator as natural isomorphisms in `[A, B]` (resp.
   `[A, _]`), witnessing functor-composition coherence. Note the orientation:
   `nat_λ` is the right-unit isomorphism `F ◯ Id ≅ F` (identity on the right)
   and `nat_ρ` is the left-unit isomorphism `Id ◯ F ≅ F` (identity on the
   left); these names are local conventions and do not follow the usual
   monoidal left-/right-unitor naming (λ for `I ⊗ A`, ρ for `A ⊗ I`). *)

Definition nat_λ {A B} (F : A ⟶ B) : F ◯ Id ≅[Fun] F.
Proof.
  construct.
  - apply fun_id_right.
  - apply fun_id_right_sym.
  - apply fun_id_right_and_sym.
  - apply fun_id_right_sym_and.
Defined.

Definition nat_ρ {A B} (F : A ⟶ B) : Id ◯ F ≅[Fun] F.
Proof.
  construct.
  - apply fun_id_left.
  - apply fun_id_left_sym.
  - apply fun_id_left_and_sym.
  - apply fun_id_left_sym_and.
Defined.

Definition nat_α {A B C D} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
  H ◯ (G ◯ F) ≅[Fun] (H ◯ G) ◯ F.
Proof.
  construct.
  - apply fun_comp_assoc.
  - apply fun_comp_assoc_sym.
  - apply fun_comp_assoc_and_sym.
  - apply fun_comp_assoc_sym_and.
Defined.

Lemma whisker_left_right A B C (F G : A ⟶ B) (H J : B ⟶ C)
      (η : F ⟹ G) (θ : H ⟹ J) :
  (J ⊳ η) ∙ (θ ⊲ F) ≈ (θ ⊲ G) ∙ (H ⊳ η).
Proof. simpl; intros; cat; apply naturality. Qed.

Lemma whisker_flip A B C (F : A ⟶ B) (G : B ⟶ C) :
  (to (nat_λ G) ⊲ F) ∙ to (nat_α F Id G) ≈ G ⊳ (to (nat_ρ F)).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_right_comp
      A B C D (F : A ⟶ B) (G : B ⟶ C) (H J : C ⟶ D) (η : H ⟹ J) :
  to (nat_α F G J) ∙ η ⊲ (G ◯ F) ≈ (η ⊲ G) ⊲ F ∙ to (nat_α F G H).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_left_comp
      A B C D (F G : A ⟶ B) (H : B ⟶ C) (J : C ⟶ D) (η : F ⟹ G) :
  to (nat_α G H J) ∙ J ⊳ (H ⊳ η) ≈ (J ◯ H) ⊳ η ∙ to (nat_α F H J).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_assoc
      A B C D (F : A ⟶ B) (G H : B ⟶ C) (J : C ⟶ D) (η : G ⟹ H) :
  to (nat_α F H J) ∙ J ⊳ (η ⊲ F) ≈ (J ⊳ η) ⊲ F ∙ to (nat_α F G J).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_nat_α A B C D E (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (J : D ⟶ E) :
  (to (nat_α G H J) ⊲ F ∙ to (nat_α F (H ◯ G) J)) ∙ (J ⊳ (to (nat_α F G H)))
    ≈ to (nat_α F G (J ◯ H)) ∙ to (nat_α (G ◯ F) H J).
Proof. simpl; intros; cat. Qed.

(* nLab: https://ncatlab.org/nlab/show/pointed+endofunctor

   A pointed endofunctor is an endofunctor `F : C ⟶ C` equipped with a natural
   transformation `point : Id ⟹ F` from the identity functor. *)

Class Pointed {C : Category} (F : C ⟶ C) := {
  point : Id ⟹ F                        (* the point η : Id ⟹ F *)
}.

(* A pointed endofunctor is well-pointed when the two whiskerings of `point`
   with `F` agree as natural transformations `F ⟹ F ◯ F`, i.e. `F point` and
   `point F` coincide; the unitor isomorphisms `nat_λ`/`nat_ρ` reconcile the
   `F ◯ Id`/`Id ◯ F` source types with `F`. (A monad is well-pointed via its
   unit exactly when it is idempotent.) *)

Class WellPointed `{@Pointed C F} := {
  well_pointed :
    (F ⊳ point) ∙ from (nat_λ _) ≈ (point ⊲ F) ∙ from (nat_ρ _)
}.

(* nLab: https://ncatlab.org/nlab/show/natural+isomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Natural_transformation#Natural_isomorphism

   Isomorphisms in `[C, D]` are exactly natural isomorphisms, and a natural
   transformation is invertible iff each of its components is invertible in D.
   Here that pointwise-iso characterization is packaged as an equivalence with
   the functor setoid-equality `F ≈ G`: an iso in `[C, D]` yields a family of
   componentwise isomorphisms `F x ≅ G x` (the forward direction builds it),
   and conversely such a family assembles into a natural isomorphism. *)

Theorem Functor_Setoid_Nat_Iso `(F : C ⟶ D) (G : C ⟶ D) :
  F ≅[Fun] G  ↔  F ≈ G.
Proof.
  split; intros; simpl.
  - given (iso : ∀ x : C, F x ≅ G x). {
      intros; isomorphism; simpl; intros.
      - apply X.
      - apply (X⁻¹).
      - abstract (srewrite (iso_to_from X); cat).
      - abstract (srewrite (iso_from_to X); cat).
    }
    exists iso; simpl in *; intros.
    abstract
      (rewrite <- comp_assoc;
       rewrite (naturality[to X]);
       rewrite comp_assoc;
       srewrite (iso_from_to X); cat).
  - destruct X.
    isomorphism; simpl; intros.
    + transform; simpl; intros.
      * apply x.
      * abstract
          (rewrite e; simpl;
           rewrite !comp_assoc;
           rewrite iso_to_from; cat).
      * abstract
          (rewrite e; simpl;
           rewrite !comp_assoc;
           rewrite iso_to_from; cat).
    + transform; simpl; intros.
      * apply x.
      * abstract
          (rewrite e; simpl;
           rewrite <- !comp_assoc;
           rewrite iso_to_from; cat).
      * abstract
          (rewrite e; simpl;
           rewrite <- !comp_assoc;
           rewrite iso_to_from; cat).
    + abstract
        (rewrite fmap_id;
         apply iso_to_from).
    + abstract
        (rewrite fmap_id;
         apply iso_from_to).
Defined.

(* The two directions of [Functor_Setoid_Nat_Iso] as standalone conversions:
   a natural isomorphism gives functor equality, and vice versa. *)

Definition iso_equiv {C D : Category} {f g : C ⟶ D} :
  f ≅[Fun] g → f ≈ g := fst (Functor_Setoid_Nat_Iso _ _).

Definition equiv_iso {C D : Category} {f g : C ⟶ D} :
  f ≈ g → f ≅[Fun] g := snd (Functor_Setoid_Nat_Iso _ _).
