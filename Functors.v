Require Export Category.
Require Export Products.

Open Scope category_scope.

Generalizable All Variables.

Section Functors.

Context `{C : Category objC}.
Context `{D : Category objD}.

Class Functor (F : C → D) :=
{ fobj := F
; fmap : ∀ {X Y : objC}, (X ~> Y) → (F X ~> F Y)
; fmap_respects : ∀ {X Y : objC} (f f' : X ~> Y),
    f ≈ f' → fmap f ≈ fmap f'
; fun_identity : ∀ {X : objC}, fmap (id (A := X)) ≈ id
; fun_composition : ∀ {X Y Z : objC} (f : Y ~> Z) (g : X ~> Y),
    fmap f ∘ fmap g ≈ fmap (f ∘ g)
}.

Add Parametric Morphism (F : C → D) `(Functor F) (a b : objC) : fmap
  with signature ((@eqv objC C a b) ==> (@eqv objD D (F a) (F b)))
    as parametric_morphism_fmap'.
  intros; apply fmap_respects; auto.
Defined.

Coercion fobj : Functor >-> Funclass.

Class Natural (F : C → D) `{Functor F} (G : C → D) `{Functor G} :=
{ transport  : ∀ {X}, F X ~> G X
; naturality : ∀ {X Y} (f : X ~> Y),
    fmap f ∘ transport ≈ transport ∘ fmap f
}.

Definition nat_arrow `{Functor F} `{Functor G} (f : Natural F G) :=
  @transport F _ G _ f.

Definition nat_identity (F : C → D) `{Functor F} : Natural F F.
  apply Build_Natural with (transport := fun _ => id).
  intros.
  rewrite right_identity.
  rewrite left_identity.
  reflexivity.
Defined.

Hint Unfold nat_identity.

Definition nat_compose
  {F : C → D} `{Functor F}
  {G : C → D} `{Functor G}
  {K : C → D} `{Functor K}
  (f : Natural G K) (g : Natural F G) : Natural F K.
  apply Build_Natural
    with (transport := fun X => nat_arrow f X ∘ nat_arrow g X).
  intros.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.

Definition nat_equiv `{Functor F} `{Functor G} (f g : Natural F G) :=
  ∀ {X : C}, nat_arrow f X ≈ nat_arrow g X.

Hint Unfold nat_equiv.

Definition π1 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT1 k.
Definition π2 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT2 k.

(* Nat is the category whose morphisms are natural transformations from
   Functor C D to Functor C D.
*)
Global Instance Nat : Category { f : C → D & Functor f } :=
{ hom     := fun f g   => @Natural _ (π2 f) _ (π2 g)
; id      := fun f     => @nat_identity _ (π2 f)
; compose := fun _ _ _ => nat_compose
; eqv     := fun _ _   => nat_equiv
}.
Proof.
  - (* eqv_equivalence *)
    constructor; autounfold;
    intros; auto; crush.
  - (* compose_respects *)
    intros. auto.
  - (* right_identity *) crush.
  - (* left_identity *)  crush.
  - (* comp_assoc *)
    intros. autounfold.
    simpl. intros.
    rewrite comp_assoc. auto.
Defined.

End Functors.

Notation "C ⟶ D" := (@Nat _ C _ D) (at level 90, right associativity).

Definition Natural_In
  `{C : Category objC} `{D : Category objD}
  (F : {f : C → D & Functor f}) (G : {g : C → D & Functor g}) :=
  @Natural _ C _ D _ (π2 F) _ (π2 G).

Definition runNat
  `{C : Category objC} `{D : Category objD}
  (F : {f : C → D & Functor f}) (G : {g : C → D & Functor g})
  `{n : Natural_In F G}
  (f : F ~{ C ⟶ D }~> G) {A : C} : π1 F A ~{ D }~> π1 G A :=
  nat_arrow n A.

Definition fmap1
  `{C : Category objC} `{D : Category objD} `{E : Category objE}
  `(P : C → D ⟶ E) `(f : X ~{ D }~> Y) {A : C} :
  π1 (P A) X ~{ E }~> π1 (P A) Y :=
  @fmap _ D _ E _ (π2 (P A)) X Y f.

Definition bimap
  `{C : Category objC} `{D : Category objD} `{E : Category objE}
  (P : C → D ⟶ E) `{@Functor _ C _ (D ⟶ E) P}
  {X W : C} `{n : Natural_In (P X) (P W)}
  (f : X ~{ C }~> W) `(g : Y ~{ D }~> Z) :
  π1 (P X) Y ~{ E }~> π1 (P W) Z :=
  runNat (n := n) (P X) (P W) (fmap f) ∘ fmap1 P g.

(* Notation "F ⟶ G" := (Functor F G) (at level 9). *)
Notation "F ⟹ G" := (@transport F _ G _) (at level 40).

Definition Id `(C : Category objC) : Functor (fun X => X).
  apply Build_Functor with (fmap := fun X X f => f); crush.
Defined.

Theorem compose_equiv `{C : Category objC}
  : ∀ A X Y (f g : X ~> Y) (h : A ~> X),
  f ≈ g -> f ∘ h ≈ g ∘ h.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem fmap_set_eqv `{C : Category objC} (F : C -> Sets)
  `{@Functor objC C Type Sets F} : ∀ X Y (f g : X ~> Y),
  f ≈ g → fmap f = fmap g.
Proof.
Admitted.

Instance Hom `(C : Category objC) (A : objC)
  : @Functor objC C Type Sets (@hom objC C A) :=
{ fmap := @compose objC C A
}.
Proof.
  - (* fmap_respects *)
    intros.
    reduce.
    f_equal.
    rewrite H.
    admit.
  - (* fun_identity *)
    intros.
    reduce.
    (* rewrite left_identity. *)
    admit.
  - (* fun_composition *)
    crush.
Defined.

Reserved Notation "f ⊕ g" (at level 47, right associativity).

(* Class Monoidal `(C : Category objC) *)
(*   (ε : objC) (mappend : objC → objC → objC) := *)
(* { monoidal_left  : Hom(ε)  ⟹ Id *)
(* ; monoidal_right : CHom(ε) ⟹ Id *)
(* ; monoidal_assoc : ∀ a b c : objC, *)
(*     mappend (mappend a b) c ≈ mappend a (mappend b c) *)
(* }. *)

(* Notation "f ⊕ g" := (MAppend f g) (at level 47, right associativity). *)

Definition Tuple_map {Z X Y} (f : X → Y) (p : Z * X) : Z * Y :=
  match p with
  | pair z x => @pair Z Y z (f x)
  end.

Definition Tuple_Functor {Z} : Functor (fun (X : Type) => Z * X).
  apply Build_Functor with (fmap := @Tuple_map Z).
  - (* fmap_respects *)   crush.
  - (* fun_identity *)    crush.
  - (* fun_composition *) crush.
Defined.

Definition Tuple_bimap {X Y W Z} (f : X → W) (g : Y → Z)
  (p : X * Y) : W * Z :=
  match p with
  | pair z x => @pair W Z (f z) (g x)
  end.

(* Definition Tuple_Bifunctor : Bifunctor Coq Coq (fun (X Y : Type) => X * Y). *)
(*   apply Build_Bifunctor with (bimap := @Tuple_bimap). *)
(*   - (* bimap_respects *)    crush. *)
(*   - (* bifun_identity *)    crush. *)
(*   - (* bifun_composition *) crush. *)
(* Defined. *)

Inductive Either (E X : Type) :=
  | Left : E → Either E X
  | Right : X → Either E X.

Definition Either_map {Z X Y} (f : X → Y) (p : Either Z X) : Either Z Y :=
  match p with
  | Left z => Left Z Y z
  | Right x => Right Z Y (f x)
  end.

Definition Either_Functor {Z} : Functor (fun (X : Type) => Either Z X).
  apply Build_Functor with (fmap := @Either_map Z).
  - (* fmap_respects *)   crush.
  - (* fun_identity *)    crush.
  - (* fun_composition *) crush.
Defined.

Definition Either_bimap {X Y W Z} (f : X → W) (g : Y → Z)
  (p : Either X Y) : Either W Z :=
  match p with
  | Left z => Left W Z (f z)
  | Right x => Right W Z (g x)
  end.

(* Definition Either_Bifunctor : Bifunctor (fun (X Y : Type) => Either X Y). *)
(*   apply Build_Bifunctor with (bimap := @Either_bimap). *)
(*   - (* bimap_respects *)    crush. *)
(*   - (* bifun_identity *)    crush. *)
(*   - (* bifun_composition *) crush. *)
(* Defined. *)
