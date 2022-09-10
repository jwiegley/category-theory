Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(* Functors map objects and morphisms between categories, where such mappings
   preserve equivalences and basic categorical structure (identity and
   composition). Note that there are many species of functor, one each for the
   various categorical structures (included below), for example, the
   `CartesianFunctor` that maps products to products and preserves all its
   structural properties and laws. *)

Class Functor@{o1 h1 p1 o2 h2 p2}
  {C : Category@{o1 h1 p1}} {D : Category@{o2 h2 p2}} := {
  fobj : C → D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;

  fmap_respects : ∀ x y,
    Proper@{h2 p2} (respectful@{h1 p1 h2 p2 h2 p2}
                      equiv@{h1 p1} equiv@{h2 p2}) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.
#[export] Existing Instance fmap_respects.

Declare Scope functor_scope.
Declare Scope functor_type_scope.
Bind Scope functor_scope with Functor.
Delimit Scope functor_type_scope with functor_type.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.
Open Scope functor_scope.

(* Functors used as functions map objects of categories, similar to the way
   type constructors behave in Haskell. We cannot, unfortunately, have a
   similar coercion for morphisms, because coercions cannot be bound to
   scopes. *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

Arguments fmap
  {C%category D%category Functor%functor x%object y%object} f%morphism.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : morphism_scope.
Infix "<$[ F ]>" := (@fmap _ _ F%functor _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "fobj[ F ]" := (@fobj _ _ F%functor)
  (at level 9, format "fobj[ F ]") : object_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 9, format "fmap[ F ]") : morphism_scope.

#[export] Hint Rewrite @fmap_id : categories.

#[export]
Program Instance Functor_Setoid {C D : Category} : Setoid (C ⟶ D) := {
  (* Note that it doesn't make much sense (with our definition of [Category])
     to ask that [∀ x : C, F x = G x] and
     [∀ (x y :C) (f : x ~> y), fmap[F] f ≈ fmap[G] f] because the second
     condition is hard to work with in the type-system since it needs lots of
     equality proofs. *)
  equiv := fun F G =>
    (* Equality of objects in a category is taken to be a natural
       isomorphism *)
    { iso : ∀ x : C, F x ≅ G x
    & ∀ (x y : C) (f : x ~> y),
        fmap[F] f ≈ from (iso y) ∘ fmap[G] f ∘ to (iso x) }
}.
Next Obligation.
  equivalence.
  - isomorphism.
    + exact (from (x0 x1)).
    + exact (to (x0 x1)).
    + apply iso_from_to.
    + apply iso_to_from.
  - simpl.
    rewrite e.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    rewrite <- comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
  - isomorphism.
    + apply (to (x0 x2) ∘ to (x1 x2)).
    + apply (from (x1 x2) ∘ from (x0 x2)).
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x1 x2)).
      rewrite iso_to_from, id_left.
      apply iso_to_from.
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x0 x2)⁻¹).
      rewrite iso_from_to, id_left.
      apply iso_from_to.
  - simpl.
    rewrite !comp_assoc.
    rewrite <- (comp_assoc _ (x0 y0)⁻¹).
    rewrite <- (comp_assoc _ ((x0 y0)⁻¹ ∘ _)).
    rewrite <- e.
    apply e0.
Qed.

Lemma fun_equiv_to_fmap {C D : Category} {F G : C ⟶ D} (eqv : F ≈ G) :
  ∀ (x y : C) (f : x ~> y),
    to (``eqv y) ∘ fmap[F] f ≈ fmap[G] f ∘ to (``eqv x).
Proof.
  intros.
  rewrite <- id_right.
  rewrite ((`2 eqv) _ _).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now cat.
Qed.

Lemma fun_equiv_fmap_from {C D : Category} {F G : C ⟶ D} (eqv : F ≈ G) :
  ∀ (x y : C) (f : x ~> y),
    fmap[F] f ∘ from (``eqv x) ≈ from (``eqv y) ∘ fmap[G] f.
Proof.
  intros.
  rewrite <- id_left.
  rewrite ((`2 eqv) _ _).
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  now cat.
Qed.

Ltac constructive :=
  simpl;
  match goal with
    [ |- { iso : ?I & ?F } ] =>
    given (iso : I); [ intros; isomorphism; simpl; intros
                     | exists iso; intros ]
  end.

#[export]
Program Instance fobj_iso `(F : C ⟶ D) :
  Proper (Isomorphism ==> Isomorphism) (fobj[F]).
Next Obligation.
  proper.
  refine {| to   := fmap[F] (to X)
          ; from := fmap (from X) |}.
  - rewrite <- fmap_comp.
    rewrite iso_to_from; cat.
  - rewrite <- fmap_comp.
    rewrite iso_from_to; cat.
Defined.

#[export]
Instance fobj_respects `(F : C ⟶ D) :
  Proper (equiv ==> equiv) (@fobj C D F) := @fobj_iso C D F.

Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).

Program Definition Id {C : Category} : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Arguments Id {C} /.

Notation "Id[ C ]" := (@Id C) (at level 9, format "Id[ C ]") : functor_scope.

Program Definition Compose {C D E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. intros; rewrite !fmap_comp; reflexivity. Qed.

#[export] Hint Unfold Compose : categories.

Notation "F ◯ G" := (Compose F%functor G%functor)
  (at level 40, left associativity) : category_scope.

#[export]
Program Instance Compose_respects {C D E : Category} :
  Proper (equiv ==> equiv ==> equiv) (@Compose C D E).
Next Obligation.
  proper.
  - isomorphism; simpl; intros.
    + exact (fmap (to (x1 x3)) ∘ to (x2 (x0 x3))).
    + exact (from (x2 (x0 x3)) ∘ fmap (from (x1 x3))).
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x2 (x0 x3))).
      rewrite iso_to_from, id_left.
      rewrite <- fmap_comp.
      rewrite iso_to_from; cat.
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap _)).
      rewrite <- fmap_comp.
      rewrite iso_from_to, fmap_id, id_left.
      rewrite iso_from_to; cat.
  - simpl.
    rewrite e0, e.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap _)).
    rewrite <- fmap_comp.
    rewrite (comp_assoc (fmap _)).
    rewrite <- fmap_comp.
    rewrite !comp_assoc.
    reflexivity.
Qed.

Corollary fobj_Compose `(F : D ⟶ E) `(G : C ⟶ D) {x} :
  fobj[F ◯ G] x = fobj[F] (fobj[G] x).
Proof. reflexivity. Defined.

Lemma fun_equiv_id_right {A B} (F : A ⟶ B) : F ◯ Id ≈ F.
Proof. construct; cat. Qed.

Arguments fun_equiv_id_right {A B} F.

Lemma fun_equiv_id_left {A B} (F : A ⟶ B) : Id ◯ F ≈ F.
Proof. construct; cat. Qed.

Arguments fun_equiv_id_left {A B} F.

Lemma fun_equiv_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B)  :
  F ◯ (G ◯ H) ≈ (F ◯ G) ◯ H.
Proof. construct; cat. Qed.

Arguments fun_equiv_comp_assoc {A B C D} F G H.

Class Full `(F : C ⟶ D) := {
  prefmap {x y} (g : F x ~> F y) : x ~> y;

  prefmap_respects {x y} : Proper (equiv ==> equiv) (@prefmap x y);

  prefmap_id : ∀ x, @prefmap x x id ≈ id;
  prefmap_comp : ∀ x y z (f : F y ~> F z) (g : F x ~> F y),
    prefmap (f ∘ g) ≈ prefmap f ∘ prefmap g;

  fmap_sur {x y} (g : F x ~> F y) : fmap[F] (prefmap g) ≈ g
}.

Class Faithful `(F : C ⟶ D) := {
  fmap_inj {x y} (f g : x ~> y) : fmap[F] f ≈ fmap[F] g → f ≈ g
}.

(* Properties that follow from the above. *)
Lemma FullyFaithful `(F : C ⟶ D) `{@Full _ _ F} `{@Faithful _ _ F} :
  ∀ x y, F x ≅ F y → x ≅ y.
Proof.
  intros.
  construct.
  + apply prefmap, X.
  + apply prefmap, X.
  + abstract
      (simpl;
       rewrite <- prefmap_comp;
       destruct H;
       rewrite iso_to_from;
       apply prefmap_id).
  + abstract
      (simpl;
       rewrite <- prefmap_comp;
       destruct H;
       rewrite iso_from_to;
       apply prefmap_id).
Defined.

Definition FAlgebra `(F : C ⟶ C) (a : C) := F a ~> a.

Definition FCoalgebra `(F : C ⟶ C) (a : C) := a ~> F a.

Definition FGDialgebra `(F : C ⟶ C) `(G : C ⟶ C) (a : C) := F a ~> G a.

Section AFunctor.

Context {C D : Category}.

(* [AFunctor] allows the object mapping to be stated explicitly. *)
Class AFunctor (F : C → D) : Type := {
  a_fmap {x y : C} (f : x ~> y) : F x ~> F y;

  a_fmap_respects {x y : C} : Proper (equiv ==> equiv) (@a_fmap x y);

  a_fmap_id {x : C} : a_fmap (@id C x) ≈ id;
  a_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    a_fmap (f ∘ g) ≈ a_fmap f ∘ a_fmap g;
}.
#[export] Existing Instance a_fmap_respects.

Definition FromAFunctor `(AFunctor F) : C ⟶ D := {|
  fobj          := λ x, F x;
  fmap          := @a_fmap F _;
  fmap_respects := @a_fmap_respects F _;
  fmap_id       := @a_fmap_id F _;
  fmap_comp     := @a_fmap_comp F _;
|}.

Coercion FromAFunctor : AFunctor >-> Functor.

Definition ToAFunctor (F : C ⟶ D) : AFunctor F := {|
  a_fmap          := @fmap _ _ F;
  a_fmap_respects := @fmap_respects _ _ F;
  a_fmap_id       := @fmap_id _ _ F;
  a_fmap_comp     := @fmap_comp _ _ F;
|}.

Corollary FromAFunctor_ToAFunctor {F} :
  FromAFunctor (ToAFunctor F) = F.
Proof. reflexivity. Qed.

Corollary ToAFunctor_FromAFunctor `{H : AFunctor F} :
  ToAFunctor (FromAFunctor H) = H.
Proof. reflexivity. Qed.

End AFunctor.
