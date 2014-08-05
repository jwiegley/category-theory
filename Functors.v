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
; fun_identity : ∀ {X : objC}, fmap (id (A := X)) = id
; fun_composition : ∀ {X Y Z : objC} (f : Y ~> Z) (g : X ~> Y),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.

Coercion fobj : Functor >-> Funclass.

Class Natural (F : C → D) `{Functor F} (G : C → D) `{Functor G} :=
{ transport  : ∀ {X}, F X ~> G X
; naturality : ∀ {X Y} (f : X ~> Y),
    fmap f ∘ transport = transport ∘ fmap f
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

Definition π1 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT1 k.
Definition π2 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT2 k.

(* Nat is the category whose morphisms are natural transformations from
   Functor C D to Functor C D.
*)
Global Instance Nat : Category { f : C → D & Functor f } :=
{ hom     := fun f g   => @Natural _ (π2 f) _ (π2 g)
; id      := fun f     => @nat_identity _ (π2 f)
; compose := fun _ _ _ => nat_compose
}.
Proof.
  - (* right_identity *)
    intros. admit.
  - (* left_identity *)  admit.
  - (* comp_assoc *) admit.
    (* intros. autounfold. *)
    (* simpl. intros. *)
    (* rewrite comp_assoc. auto. *)
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

Definition Op `(C : Category objC) : Category objC.
  apply Build_Category with
    (hom     := fun x y => hom y x)
    (id      := @id objC C)
    (compose := fun a b c f g => g ∘ f).

  intros; apply (@left_identity objC C).
  intros; apply (@right_identity objC C).
  intros. symmetry; apply comp_assoc.
Defined.

Notation "C ^op" := (Op C) (at level 90) : category_scope.

(* Instance Hom `(C : Category objC) (A : objC) *)
(*   : @Functor _ C _ Sets (fun X => A ~> X) := *)
(* { fmap := fun _ _ f g => f ∘ g *)
(* }. *)
(* Proof. *)
(*   - (* fun_identity *)    crush. *)
(*   - (* fun_composition *) crush. *)
(* Defined. *)

Reserved Notation "f ⊕ g" (at level 47, right associativity).

(* Class Monoidal `(C : Category objC) *)
(*   (ε : objC) (mappend : objC → objC → objC) := *)
(* { monoidal_left  : Hom(ε)  ⟹ Id *)
(* ; monoidal_right : CHom(ε) ⟹ Id *)
(* ; monoidal_assoc : ∀ a b c : objC, *)
(*     mappend (mappend a b) c = mappend a (mappend b c) *)
(* }. *)

(* Notation "f ⊕ g" := (MAppend f g) (at level 47, right associativity). *)

Definition Tuple_map {Z X Y} (f : X → Y) (p : Z * X) : Z * Y :=
  match p with
  | pair z x => @pair Z Y z (f x)
  end.

Program Instance Tuple_Functor {Z} : Functor (fun X => Z * X) :=
{ fmap := @Tuple_map Z
}.
Obligation 1. ext_eq. crush. Defined.
Obligation 2. ext_eq. crush. Defined.

Definition Tuple_bimap {X Y W Z} (f : X → W) (g : Y → Z)
  (p : X * Y) : W * Z :=
  match p with
  | pair z x => @pair W Z (f z) (g x)
  end.

Inductive Either (E X : Type) :=
  | Left : E → Either E X
  | Right : X → Either E X.

Definition Either_map {Z X Y} (f : X → Y) (p : Either Z X) : Either Z Y :=
  match p with
  | Left z => Left Z Y z
  | Right x => Right Z Y (f x)
  end.

Program Instance Either_Functor {Z} : Functor (fun (X : Type) => Either Z X) :=
{ fmap := @Either_map Z
}.
Obligation 1. ext_eq. crush. Defined.
Obligation 2. ext_eq. crush. Defined.

Definition Either_bimap {X Y W Z} (f : X → W) (g : Y → Z)
  (p : Either X Y) : Either W Z :=
  match p with
  | Left z => Left W Z (f z)
  | Right x => Right W Z (g x)
  end.
