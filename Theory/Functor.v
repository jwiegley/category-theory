Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Equations.Prop.Logic.

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

Section StrictEq.
 Lemma transport_adjunction (A : Type) (B : A -> Type) (R: forall a :A, crelation (B a)) :
   forall (a a' : A) (p : a = a') (x : B a) (y : B a'),
    ((R _ x (transport_r B p y) -> R _ (transport B p x) y)) *
      (R _ (transport B p x) y -> (R _ x (transport_r B p y))).
  intros a a' p x y. split.
  - destruct p. now unfold transport_r.
  - destruct p. now unfold transport_r.
Defined.

Lemma transport_relation_exchange (A : Type) (R : crelation A) :
  forall (a a' b b': A) (p : a = b) (q : a' = b') (t : R a a'),
    transport (fun z => R b z) q
      (transport (fun k => R k a') p t) =
      transport (fun k => R k b') p
        (transport (fun z => R a z) q t).
Proof.
  intros a a' b b' p q t; destruct p, q; reflexivity.
Defined.

Lemma transport_trans (A : Type) (B : A -> Type) :
  forall (a0 a1 a2 : A) (x : B a0) (p : a0 = a1) (q : a1 = a2),
    transport B q (transport B p x) = transport B (eq_trans p q) x.
Proof.
  intros a0 a1 a2 x p q; destruct p, q; reflexivity.
Defined.

Lemma transport_r_trans (A : Type) (B : A -> Type) :
  forall (a0 a1 a2 : A) (x : B a2) (p : a0 = a1) (q : a1 = a2),
    transport_r B p (transport_r B q x) = transport_r B (eq_trans p q) x.
Proof.
  intros a0 a1 a2 x p q; destruct p, q; reflexivity.
Defined.

Global Instance proper_transport (A : Type) (B : A -> Type) (S : forall a : A, Setoid (B a)) :
  forall (a a' : A) (p : a = a'), Proper (equiv ==> equiv) (transport B p).
Proof.
  intros a b p. destruct p. now unfold transport.
Defined.

Global Instance proper_transport_r (A : Type) (B : A -> Type) (S : forall a : A, Setoid (B a)) :
  forall (a a' : A) (p : a = a'), Proper (equiv ==> equiv) (transport_r B p).
Proof.
  intros a b p. destruct p. now (unfold transport_r).
Defined.

(* Global Instance proper_transport_hom_cod (C : Category) (c d d': C) (p : d = d')  *)
(*   : Proper (equiv ==> equiv) (transport (fun z => hom c z) p). *)
(* Proof. *)
(*   destruct p. now trivial. *)
(* Defined. *)

(* Global Instance proper_transport_hom_dom (C : Category) (c c' d: C) (p : c = c')  *)
(*   : Proper (equiv ==> equiv) (transport (fun z => hom z d) p). *)
(* Proof. *)
(*   destruct p. now trivial. *)
(* Defined. *)

#[export] Instance proper_transport_dom (A: Type) (B : A -> A -> Type)
  (S : forall i j, Setoid (B i j)) (c c' d : A) (p : c = c') :
  Proper (equiv ==> equiv) (Logic.transport (fun z => B z d) p).
Proof.
  destruct p. now trivial.
Defined.

#[export] Instance proper_transport_cod (A: Type) (B : A -> A -> Type)
  (S : forall i j, Setoid (B i j)) (c d d' : A) (p : d = d') :
  Proper (equiv ==> equiv) (Logic.transport (fun z => B c z) p).
Proof.
  destruct p. now trivial.
Defined.

Program Instance Functor_StrictEq_Setoid {C D : Category} : Setoid (C ⟶ D) := {
    equiv := fun F G =>
      { eq_on_obj : ∀ x : C, F x = G x
                  & ∀ (x y : C) (f : x ~> y),
            transport (fun z => hom (fobj[ F ] x) z) (eq_on_obj y) (fmap[F] f) ≈ 
                   (transport_r (fun z => hom z (fobj[G] y)) (eq_on_obj x) (fmap[G] f)) }
}.
Next Obligation.
  equivalence.
  - unfold transport_r. rewrite eq_sym_involutive.
    fold (transport_r (λ z : obj[D], fobj[y] x1 ~{ D }~> z) (x0 y0)).
    symmetry. 
    rename x into F, y into G, x0 into eq_ob, x1 into x, y0 into y. 
    refine ((snd
               (transport_adjunction D (hom (fobj[G] x))
                  (fun d t s => t ≈ s) _ _ _ _ _)) _).
    rewrite transport_relation_exchange.
    refine ((fst
               (transport_adjunction D (fun d' => hom d' (fobj[G] y))
                  (fun d t s => t ≈ s) _ _ _ _ _)) _).
    exact (e _ _ _).
  - exact(eq_trans (x1 x2) (x0 x2)).
  - rename x into F, y into G, z into H, x1 into F_eq_ob_G,
      e0 into F_eq_ob_G_resp_mor, x0 into G_eq_ob_H,
      e into G_eq_ob_H_resp_mor, x2 into domf, y0 into codf.
    simpl.
    rewrite <- transport_trans, <- transport_r_trans.
    rewrite F_eq_ob_G_resp_mor.
    unfold transport_r at 1 2. rewrite transport_relation_exchange.
    apply proper_transport_dom.
    apply G_eq_ob_H_resp_mor.
Defined.

Lemma transport_f_equal (A B : Type) (C : B -> Type) (f : A -> B)
  (x y : A) (p : x = y) (t : C (f x))
  : transport (fun a => C (f a)) p t = transport (fun b => C b) (f_equal f p) t.
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_functorial_dom (C D: Category) (F : @Functor C D) (c c' d : C)
  (p : c = c') (f : hom c d)
  : fmap[F] (transport (fun z => hom z d) p f) =
      transport (fun z => hom z (fobj[F] d)) (f_equal (fobj[F]) p) (fmap[F] f).
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_functorial_cod (C D: Category) (F : @Functor C D) (c d d': C)
  (p : d = d') (f : hom c d)
  : fmap[F] (transport (fun z => hom c z) p f) =
      transport (fun z => hom (fobj[F] c) z) (f_equal (fobj[F]) p) (fmap[F] f).
Proof.
  destruct p. reflexivity.
Defined.

#[export]
 Program Instance Compose_respects_stricteq {C D E : Category} :
   Proper (equiv ==> equiv ==> equiv) (@Compose C D E).
 Next Obligation.
  intros F G [FG_eq_on_obj FG_morphismcoherence] H K [HK_eq_on_obj HK_morphismcoherence].
  unshelve eapply (_ ; _).
  - intro c; simpl. 
      exact(eq_trans (f_equal (fobj[F]) (HK_eq_on_obj c)) (FG_eq_on_obj (fobj[K] c))).
  - intros c c' f.
    simpl.
    rewrite <- transport_trans, <- transport_r_trans.
    rewrite <- transport_functorial_cod.
    rewrite HK_morphismcoherence.
    unfold transport_r at 1 2.
    rewrite transport_functorial_dom.
    rewrite transport_relation_exchange.
    rewrite <- eq_sym_map_distr.
    apply proper_transport_dom.
    now trivial.
 Defined.
    
 Lemma fun_strict_equiv_id_right {A B} (F : A ⟶ B) : F ◯ Id ≈ F.
 Proof. construct; cat. Qed.

 Arguments fun_strict_equiv_id_right {A B} F.

 Lemma fun_strict_equiv_id_left {A B} (F : A ⟶ B) : Id ◯ F ≈ F.
 Proof. construct; cat. Qed.

 Arguments fun_equiv_id_left {A B} F.

 Lemma fun_strict_equiv_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B)  :
   F ◯ (G ◯ H) ≈ (F ◯ G) ◯ H.
 Proof. construct; cat. Qed.

 Arguments fun_equiv_comp_assoc {A B C D} F G H.

End StrictEq.

