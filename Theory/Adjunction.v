Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   An adjunction F ⊣ U between F : D ⟶ C (the left adjoint) and U : C ⟶ D
   (the right adjoint) is given here in hom-set form: a family of isomorphisms
   adj {x y} : (F x ~{C}~> y) ≊ (x ~{D}~> U y) in the category of setoids,
   natural in both arguments. Writing ⌊f⌋ := to adj f and ⌈f⌉ := from adj f
   for the two transposes, naturality is recorded by [to_adj_nat_l],
   [to_adj_nat_r] (and the inverse-direction [from_adj_nat_l],
   [from_adj_nat_r]). The unit η := ⌊id⌋ : x ~> U (F x) and counit
   ε := ⌈id⌉ : F (U x) ~> x are the transposes of the identities, and the
   triangle (zig-zag) identities ε ∘ fmap[F] η ≈ id[F x] (counit_fmap_unit)
   and fmap[U] ε ∘ η ≈ id[U x] (fmap_counit_unit) hold as derived corollaries. *)

(* Origins, ubiquity, and the uses of adjunction

   nLab:  https://ncatlab.org/nlab/show/adjoint+functor
   Paper: Kan, "Adjoint functors", Transactions of the American
          Mathematical Society 87(2), 1958
   Paper: Lawvere, "Adjointness in Foundations", Dialectica 23(3/4), 1969;
          reprinted as TAC Reprints 16, 2006

   Adjoint functors were introduced by Daniel Kan — a homotopy theorist and
   doctoral student of Eilenberg — in the 1958 paper cited above.  The
   concept was suggested by the needs of homological algebra, where natural
   bijections of the shape Hom(F x, y) ≅ Hom(x, U y) had long been in
   working use, the paradigm case being the tensor-hom adjunction
   − ⊗ A ⊣ Hom(A, −) on abelian groups.  The name records an analogy with
   adjoint linear operators on a Hilbert space, ⟨L x, y⟩ = ⟨x, R y⟩; the
   nLab describes the categorical notion as a kind of categorification of
   that older one.  Mac Lane states the standard assessment in the preface
   of Categories for the Working Mathematician (Springer, 1971): "Adjoint
   functors arise everywhere", and the middle of that book presents
   universal constructions, limits, and free objects as so many faces of
   adjunction.

   Three presentations of the concept are equivalent, and the library
   formalizes each.  This file takes Kan's hom-set form as primitive: the
   natural family of setoid isomorphisms [adj].  The unit/counit form —
   η and ε subject to the two triangle identities, which appear here as the
   derived corollaries [counit_fmap_unit] and [fmap_counit_unit] — is the
   class [Adjunction_Transform] of Adjunction/Natural/Transformation.v,
   with the round trip between the two forms in
   Adjunction/Natural/Transformation/Universal.v.  The universal-arrow form
   is Theory/Universal/Arrow.v, whose [AdjunctionFromUniversalArrows]
   assembles an adjunction from a pointwise family of universal solutions
   and is the engine behind the adjoint functor theorems of
   Adjunction/GAFT.v.  An adjunction is weaker than an isomorphism or an
   equivalence of categories, yet strong enough to transport structure:
   adjoints are unique up to natural isomorphism ([right_adjoint_iso] and
   [left_adjoint_iso] below), right adjoints preserve limits and left
   adjoints colimits (Adjunction/Continuity.v, anticipated by the note
   ending this file), and every adjunction induces a monad.  The last
   observation is Huber's ("Homotopy theory in general categories",
   Mathematische Annalen 144, 1961), realized here as [Adjunction_Monad] in
   Monad/Adjunction.v; its converse — every monad so arises — was proved
   twice in 1965, by Kleisli ("Every standard construction is induced by a
   pair of adjoint functors", Proceedings of the AMS 16(3), 1965) with the
   initial resolution and by Eilenberg and Moore ("Adjoint functors and
   triples", 1965) with the terminal one, both in-tree as
   Monad/Kleisli/Adjunction.v and Monad/Eilenberg/Moore/Adjunction.v.

   Lawvere's "Adjointness in Foundations" argues that adjointness, first
   isolated and named in category theory, also pervades logic: cartesian
   closed structure is entirely given by adjunctions — currying is
   − × a ⊣ (−)^a — and the quantifiers form the adjoint triple
   ∃ ⊣ substitution ⊣ ∀ over the fibres of a hyperdoctrine, a triple that
   reappears as dependent sum and product in type theory and as base
   change in geometry.  Between posets, an adjunction is exactly a Galois
   connection, whose antitone variant recovers classical Galois theory;
   on this special case rests abstract interpretation (Cousot and Cousot,
   "Abstract interpretation: a unified lattice model for static analysis
   of programs by construction or approximation of fixpoints", POPL 1977),
   where a connection α ⊣ γ between concrete and abstract domains —
   c ⊑ γ(a) ⟺ α(c) ≼ a — is the soundness discipline of static
   analyzers, and such connections compose, so stages of approximation
   stack.

   For the functional programmer (Milewski, "Adjunctions", 2016), the
   transposes ⌊-⌋ and ⌈-⌉ are the leftAdjunct and rightAdjunct of
   Haskell's Adjunction class, while [unit] and [counit] specialize to
   return and extract.  The product type is right adjoint to the diagonal
   functor — concretely [Diagonal_Product_Adjunction] in
   Adjunction/Diagonal/Product.v — and the function type arises from
   − × a ⊣ (−)^a with eval as counit.  The free/forgetful reading of the
   next comment block, witnessed in-tree by [FreeForgetfulAdjunction] in
   Construction/Free/Quiver.v, is the historically central family of
   examples, though not the whole story: limits and Kan extensions are
   themselves adjoints, to the diagonal and restriction functors. *)

(* Adjunctions relate two functors that map between the same two categories
  (though in opposite directions), in a manner that is weaker than isomorphism
  or equivalence, but still quite informative. In general, one functor is
  forgetful, and maps constructions from a more expressive domain into one
  that captures only the essence of that structure; while the other is free,
  and maps essential constructions into the fuller setting.

  As an example: the category of ASTs may be mapped forgetfully to the
  category of interpretated objects, which themselves map freely to some
  "canonical" representation of each such object. So, "3", "1 + 2", and "2 +
  1" all mean 3, while 3 is canonically represented by the constant "3". The
  forgetful functor is the evaluator, and the free functor a parser, giving
  rise to the following isomorphism (in the category of Sets, whose objects
  may be hom-sets):

      AST x ~{category of syntax or ASTs}~> y
        ≅ x ~{category of semantics or denotations}~> Denote y *)

Section Adjunction.

Universes o1 h1 p1 o2 h2 p2.
Context {C : Category@{o1 h1 p1}}.
Context {D : Category@{o2 h2 p2}}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Reserved Notation "⌊ f ⌋".
Reserved Notation "⌈ f ⌉".

(* o3 p3 are universes larger than either C or D. *)
Class Adjunction@{o3 p3 so sh sp} := {
  (* adj {x y} : F x ~{C}~> y ≊ x ~{D}~> U y *)
  adj {x y} :
    @Isomorphism@{so sh p3} Sets@{o3 so}
      {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
      {| carrier := @hom D x (U y); is_setoid := @homset D x (U y) |}
    where "⌊ f ⌋" := (to   adj f)
      and "⌈ f ⌉" := (from adj f);

  (* Naturality of the iso in both arguments, stated for the forward transpose
     ⌊-⌋ = to adj (naturality in x, via F) and ... *)
  to_adj_nat_l {x y z} (f : F y ~> z) (g : x ~> y) :
    ⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g;
  (* ... naturality in y, via U. *)
  to_adj_nat_r {x y z} (f : y ~> z) (g : F x ~> y) :
    ⌊f ∘ g⌋ ≈ fmap[U] f ∘ ⌊g⌋;

  (* The dual (_sym) statements for the inverse transpose ⌈-⌉ = from adj;
     derivable from the above, but kept as fields so that opposite-side proofs
     are available by reflexivity-of-duality without re-deriving them. *)
  from_adj_nat_l {x y z} (f : y ~> U z) (g : x ~> y) :
    ⌈f ∘ g⌉ ≈ ⌈f⌉ ∘ fmap[F] g;
  from_adj_nat_r {x y z} (f : y ~> z) (g : x ~> U y) :
    ⌈fmap[U] f ∘ g⌉ ≈ f ∘ ⌈g⌉
}.

Definition Build_Adjunction'
  (adj : forall x y,
    @Isomorphism Sets
      {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
      {| carrier := @hom D x (U y); is_setoid := @homset D x (U y) |})
  (to_adj_nat_l : forall x y z (f : F y ~> z) (g : x ~> y),
      (to (adj _ _)  (f ∘ fmap[F] g) ≈ (to (adj _ _) f) ∘ g))
  (to_adj_nat_r : forall x y z (f : y ~> z) (g : F x ~> y),
      (to (adj _ _) (f ∘ g) ≈ fmap[U] f ∘ (to (adj _ _) g)))
  : Adjunction.
Proof.
  unshelve eapply Build_Adjunction.
  + apply to_adj_nat_l.
  + apply to_adj_nat_r.
  + intros x y z f g.
    set (f' := from (adj y z) f).
    apply ((snd (@injectivity_is_monic _ _ (adj x z))) _).
    change (to (adj x z) (from (adj x z) _)) with
      (((adj x z) ∘ (from (adj x z))) (f ∘ g)).
    rewrite ((iso_to_from (adj x z)) (f ∘ g)); simpl;
    rewrite to_adj_nat_l.
    refine (compose_respects _ _ _ g _ (Equivalence_Reflexive _)).
    unfold f'; symmetry.
    exact ((iso_to_from (adj y z)) f).
  + intros x y z f g.
    set (g' :=  from (adj x y) g).
    apply ((snd (@injectivity_is_monic _ _ (adj x z))) _).
    rewrite (iso_to_from (adj x z) (fmap[U] f ∘ g)); simpl.
    rewrite to_adj_nat_r.
    apply (compose_respects (fmap[U] f) _ (Equivalence_Reflexive _)).
    unfold g'; symmetry;
      apply (iso_to_from (adj x y) g).
Defined.

Context `{@Adjunction}.

Notation "⌊ f ⌋" := (to adj f).
Notation "⌈ f ⌉" := (from adj f).

Corollary adj_univ `(f : F x ~> y) (g : x ~> U y) :
  f ≈ ⌈g⌉ ↔ ⌊f⌋ ≈ g.
Proof.
  split; intros.
  - rewrite X.
    sapply (@iso_to_from Sets _ _ (@adj _ x y)).
  - rewrite <- X.
    symmetry.
    sapply (@iso_from_to Sets _ _ (@adj _ x y)).
Qed.

Corollary to_adj_comp_law {x y} (f : F x ~> y) :
  ⌈⌊f⌋⌉ ≈ f.
Proof. sapply (@iso_from_to Sets _ _ (@adj _ x y) f). Qed.

Corollary from_adj_comp_law {x y} (f : x ~> U y) :
  ⌊⌈f⌉⌋ ≈ f.
Proof. sapply (@iso_to_from Sets _ _ (@adj _ x y) f). Qed.

Definition unit   {x : D} : x ~> U (F x) := ⌊id⌋.
Definition counit {x : C} : F (U x) ~> x := ⌈id⌉.

Notation "'η'" := unit.
Notation "'ε'" := counit.

Corollary from_adj_unit {x} :
  ⌈η⌉ ≈ id[F x].
Proof. sapply (@iso_from_to Sets _ _ (@adj _ x (F x))). Qed.

Corollary to_adj_counit {x} :
  ⌊ε⌋ ≈ id[U x].
Proof. sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)). Qed.

Corollary counit_comp {x y} (f : F x ~> y) :
  ε ∘ fmap[F] (fmap[U] f) ≈ f ∘ ε.
Proof.
  unfold counit.
  rewrite <- from_adj_nat_l.
  rewrite <- from_adj_nat_r.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Corollary unit_comp {x y} (f : x ~> U y) :
  fmap[U] (fmap[F] f) ∘ η ≈ η ∘ f.
Proof.
  unfold unit.
  rewrite <- to_adj_nat_l.
  rewrite <- to_adj_nat_r.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Corollary adj_univ_impl {x y} (f : F x ~> y) (g : x ~> U y) :
  f ≈ ε ∘ fmap[F] g ↔ ⌊f⌋ ≈ g.
Proof.
  unfold counit.
  split; intros.
  - rewrite X; clear X.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    apply from_adj_comp_law.
  - rewrite <- X; clear X.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    symmetry.
    apply to_adj_comp_law.
Qed.

Corollary to_adj_unit {x y} (f : F x ~> y) :
  ⌊f⌋ ≈ fmap[U] f ∘ η.
Proof.
  rewrite <- (id_right f).
  rewrite to_adj_nat_r.
  rewrite fmap_comp; cat.
Qed.

Corollary from_adj_counit {x y} (f : x ~> U y) :
  ⌈f⌉ ≈ ε ∘ fmap[F] f.
Proof.
  rewrite <- (id_left f).
  rewrite from_adj_nat_l.
  rewrite fmap_comp; cat.
Qed.

Corollary counit_fmap_unit  {x} :
  ε ∘ fmap[F] η ≈ id[F x].
Proof.
  unfold unit, counit.
  rewrite <- from_adj_nat_l; cat.
  sapply (@iso_from_to Sets _ _ (@adj _ x (F x))).
Qed.

Corollary fmap_counit_unit  {x} :
  fmap[U] ε ∘ η ≈ id[U x].
Proof.
  unfold unit, counit.
  rewrite <- to_adj_nat_r; cat.
  sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)).
Qed.

Corollary fmap_from_adj_unit {x y} (f : x ~{D}~> y) : fmap[F] f ≈ ⌈η ∘ f⌉.
Proof.
  unfold unit.
  rewrite from_adj_nat_l.
  rewrite to_adj_comp_law; cat.
Qed.

Corollary fmap_to_adj_counit {x y} (f : x ~{C}~> y) : fmap[U] f ≈ ⌊f ∘ ε⌋.
Proof.
  unfold counit.
  rewrite to_adj_nat_r.
  rewrite from_adj_comp_law; cat.
Qed.

(* If F is a faithful functor, and f is monic, then adj f is monic. *)
Theorem adj_monic  {x y} (f : F x ~> y) c (g h : c ~> x) :
  Faithful F → Monic f ->
    ⌊f⌋ ∘ g ≈ ⌊f⌋ ∘ h → g ≈ h.
Proof.
  intros.
  rewrite <- !to_adj_nat_l in X1.
  assert
    (Proper
       (@equiv _ unit_setoid ==> equiv)
       (λ _ : unit_setoid_object, f ∘ fmap[F] g)) as XA by proper.
  assert
    (Proper
       (@equiv _ unit_setoid ==> equiv)
       (λ _ : unit_setoid_object, f ∘ fmap[F] h)) as XB by proper.
  pose proof
       (monic (Monic:=@iso_to_monic Sets
                                    {| is_setoid := homset (fobj[F] c) y |}
                                    {| is_setoid := homset c (fobj[U] y) |}
                                    (@adj H c y))
              unit_setoid_object
              {| morphism  := λ _ : unit_setoid_object, f ∘ fmap[F] g |}
              {| morphism  := λ _ : unit_setoid_object, f ∘ fmap[F] h |}) as X2.
  simpl in X2.
  now apply X, X0, X2.
Qed.

Corollary to_adj_respects {x y} (f g : F x ~{C}~> y) :
  f ≈ g → ⌊f⌋ ≈ ⌊g⌋.
Proof. intros; now rewrites. Qed.

Corollary from_adj_respects {x y} (f g : x ~{D}~> U y) :
  f ≈ g → ⌈f⌉ ≈ ⌈g⌉.
Proof. intros; now rewrites. Qed.

End Adjunction.

Arguments Adjunction {C D} F%_functor U%_functor.

Declare Scope adjunction_scope.
Declare Scope adjunction_type_scope.
Bind Scope adjunction_scope with Adjunction.
Delimit Scope adjunction_type_scope with adjunction_type.
Delimit Scope adjunction_scope with adjunction.
Open Scope adjunction_type_scope.
Open Scope adjunction_scope.

Notation "F ⊣ G" := (@Adjunction _ _ F G) (at level 59) : category_scope.
Notation "adj[ A ]" := (@adj _ _ _ _ A _ _)
  (at level 9, format "adj[ A ]") : morphism_scope.

(* Wikipedia: "If the functor F : C ← D has two right adjoints G and G', then
   G and G' are naturally isomorphic. The same is true for left adjoints." *)

Theorem right_adjoint_iso `(F : C ⟶ D) (G G' : D ⟶ C) :
  F ⊣ G → F ⊣ G' → G ≈ G'.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply adj; simpl.
      apply X; simpl.
      exact id.
    + apply adj; simpl.
      apply X0; simpl.
      exact id.
    + simpl.
      rewrite <- to_adj_nat_l.
      rewrite <- from_adj_nat_l.
      rewrite id_left.
      rewrite to_adj_comp_law.
      rewrite from_adj_comp_law.
      reflexivity.
    + simpl.
      rewrite <- to_adj_nat_l.
      rewrite <- from_adj_nat_l.
      rewrite id_left.
      rewrite to_adj_comp_law.
      rewrite from_adj_comp_law.
      reflexivity.
  - simpl.
    rewrite <- to_adj_nat_l.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    rewrite <- to_adj_nat_l.
    rewrite <- from_adj_nat_l.
    rewrite <- to_adj_nat_r.
    rewrite <- from_adj_nat_r.
    rewrite id_right.
    rewrite to_adj_comp_law.
    rewrite from_adj_comp_law.
    reflexivity.
Qed.

Theorem left_adjoint_iso `(G : D ⟶ C) (F F' : C ⟶ D) :
  F ⊣ G → F' ⊣ G → F ≈ F'.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply adj; simpl.
      apply X0; simpl.
      exact id.
    + apply adj; simpl.
      apply X; simpl.
      exact id.
    + simpl.
      rewrite <- from_adj_nat_r.
      rewrite <- to_adj_nat_r.
      rewrite id_right.
      rewrite from_adj_comp_law.
      rewrite to_adj_comp_law.
      reflexivity.
    + simpl.
      rewrite <- from_adj_nat_r.
      rewrite <- to_adj_nat_r.
      rewrite id_right.
      rewrite from_adj_comp_law.
      rewrite to_adj_comp_law.
      reflexivity.
  - simpl.
    rewrite <- from_adj_nat_r.
    rewrite <- to_adj_nat_r.
    rewrite id_right.
    rewrite <- from_adj_nat_l.
    rewrite <- to_adj_nat_l.
    rewrite id_left.
    rewrite from_adj_comp_law.
    rewrite to_adj_comp_law.
    reflexivity.
Qed.

(* Future direction (no scaffolding here yet):

   "The most important property of adjoints is their continuity: every
    functor that has a left adjoint (and therefore is a right adjoint) is
    continuous (i.e. commutes with limits in the category theoretical
    sense); every functor that has a right adjoint (and therefore is a
    left adjoint) is cocontinuous (i.e. commutes with colimits)."
                                                              -- Wikipedia

   These theorems are formalized in Adjunction/Continuity.v:
   [right_adjoint_preserves_limits] (RAPL, proved directly by transposing
   cones through the hom-setoid isomorphism) and
   [left_adjoint_preserves_colimits] (LAPC, by duality via
   Adjunction/Opposite.v), phrased with the preservation vocabulary of
   Structure/Limit/Preservation.v. *)
