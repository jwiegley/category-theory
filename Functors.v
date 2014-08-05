Require Export Category.
Require Export Products.

Open Scope category_scope.

Generalizable All Variables.
(* Set Printing All. *)

Class Functor (C : Category) (D : Category) :=
{ fobj         : C → D
; fmap         : ∀ {X Y : C}, (X ~> Y) → (fobj X ~> fobj Y)
; fun_identity : ∀ {X : C}, fmap (id (A := X)) = id
; fun_compose  : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Y),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.

Coercion fobj : Functor >-> Funclass.

Class Natural `(F : @Functor C D) `(G : @Functor C D) :=
{ transport  : forall {X}, F X ~> G X
; naturality : ∀ {X Y} (f : X ~> Y),
    fmap f ∘ transport = transport ∘ fmap f
}.

Coercion transport : Natural >-> Funclass.

Definition nat_identity `{F : Functor} : Natural F F.
  apply Build_Natural with (transport := fun _ => id).
  intros.
  rewrite right_identity.
  rewrite left_identity.
  reflexivity.
Defined.

Hint Unfold nat_identity.

Definition nat_compose
  `{F : @Functor C D} `{G : @Functor C D} `{K : @Functor C D}
  (f : Natural G K) (g : Natural F G) : Natural F K.
  apply Build_Natural
    with (transport := fun X =>
           @transport C D G K f X ∘ @transport C D F G g X).
  intros.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.

Hint Unfold nat_compose.

Definition π1 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT1 k.
Definition π2 {A : Type} {P : A → Type} (k : {x : A & P x}) := projT2 k.

(* Nat is the category whose morphisms are natural transformations from
   Functor C D to Functor C D.
*)
Global Instance Nat (C : Category) (D : Category) : Category :=
{ ob      := @Functor C D
; hom     := @Natural C D
; id      := fun f     => @nat_identity C D f
; compose := fun _ _ _ => nat_compose
}.
Proof.
  - (* right_identity *)
    intros. admit.
  - (* left_identity *)  admit.
  - (* comp_assoc *)
    admit.
    (* intros. autounfold. *)
    (* simpl. intros. *)
    (* rewrite comp_assoc. auto. *)
Defined.

Notation "C ⟶ D" := (@Functor C D) (at level 90, right associativity).
Notation "C ⟹ D" := (Nat C D) (at level 90, right associativity).
Notation "F ⟾ G" := (@Natural _ _ F G) (at level 90, right associativity).

Definition fmap1 `{C : Category} `{D : Category} `{E : Category}
  `{P : C ⟶ D ⟹ E} {A : C} {X Y : D} :
  (X ~{D}~> Y) → (P A X ~{E}~> P A Y) := fmap.

Definition bimap `{C : Category} `{D : Category} `{E : Category}
  `{P : C ⟶ D ⟹ E} `(f : X ~{C}~> W) `(g : Y ~{D}~> Z) `{P X ⟾ P W} :
  P X Y ~{E}~> P W Z := transport ∘ fmap1 g.

Definition Id `(C : Category) : Functor C C.
  apply Build_Functor with
    (fobj := fun X => X)
    (fmap := fun X X f => f);
  crush.
Defined.

Definition Op `(C : Category) : Category.
  apply Build_Category with
    (hom     := fun x y => hom y x)
    (id      := @id C)
    (compose := fun a b c f g => g ∘ f).

  intros; apply (@left_identity C).
  intros; apply (@right_identity C).
  intros. symmetry; apply comp_assoc.
Defined.

Notation "C ^op" := (Op C) (at level 90) : category_scope.

(* Instance Hom `(C : Category) (A : C) : @Functor C Sets := *)
(* { fobj := fun X       => A ~> X *)
(* ; fmap := fun _ _ f g => f ∘ g *)
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

Program Instance Tuple_Functor {Z} : Functor Coq Coq :=
{ fobj := fun X => Z * X
; fmap := @Tuple_map Z
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

Program Instance Either_Functor {Z} : Functor Coq Coq :=
{ fobj := fun (X : Type) => Either Z X
; fmap := @Either_map Z
}.
Obligation 1. ext_eq. crush. Defined.
Obligation 2. ext_eq. crush. Defined.

Definition Either_bimap {X Y W Z} (f : X → W) (g : Y → Z)
  (p : Either X Y) : Either W Z :=
  match p with
  | Left z => Left W Z (f z)
  | Right x => Right W Z (g x)
  end.
