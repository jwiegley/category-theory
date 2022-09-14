Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.

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
Context {C : Category@{o1 h1 p2}}.
Context {D : Category@{o2 h2 p2}}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Reserved Notation "⌊ f ⌋".
Reserved Notation "⌈ f ⌉".

(* o3 h3 p3 are universes larger than either C or D. *)
Class Adjunction@{o3 h3 p3 so sh sp} := {
  (* adj {x y} : F x ~{C}~> y ≊ x ~{D}~> U y *)
  adj {x y} :
    @Isomorphism@{so sh p3} Sets@{o3 h3 so sh p3}
      {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
      {| carrier := @hom D x (U y); is_setoid := @homset D x (U y) |}
    where "⌊ f ⌋" := (to   adj f)
      and "⌈ f ⌉" := (from adj f);

  to_adj_nat_l {x y z} (f : F y ~> z) (g : x ~> y) :
    ⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g;
  to_adj_nat_r {x y z} (f : y ~> z) (g : F x ~> y) :
    ⌊f ∘ g⌋ ≈ fmap[U] f ∘ ⌊g⌋;

  from_adj_nat_l {x y z} (f : y ~> U z) (g : x ~> y) :
    ⌈f ∘ g⌉ ≈ ⌈f⌉ ∘ fmap[F] g;
  from_adj_nat_r {x y z} (f : y ~> z) (g : x ~> U y) :
    ⌈fmap[U] f ∘ g⌉ ≈ f ∘ ⌈g⌉
}.

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

Arguments Adjunction {C D} F%functor U%functor.

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

(* jww (2017-06-02): TODO *)
(* Wikipedia: "The most important property of adjoints is their continuity:
   every functor that has a left adjoint (and therefore is a right adjoint) is
   continuous (i.e. commutes with limits in the category theoretical sense);
   every functor that has a right adjoint (and therefore is a left adjoint) is
   cocontinuous (i.e. commutes with colimits).

   Since many common constructions in mathematics are limits or colimits, this
   provides a wealth of information. For example:

   - applying a right adjoint functor to a product of objects yields the
   - product of the images; applying a left adjoint functor to a coproduct of
   - objects yields the coproduct of the images; every right adjoint functor
   - is left exact; every left adjoint functor is right exact." *)
