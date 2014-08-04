Require Export Category.
Require Export Products.

Open Scope category_scope.

Generalizable All Variables.

Section Functors.

Context `{C : Category objC homC}.
Context `{D : Category objD homD}.

Class Functor (Fobj : C -> D) :=
{ fobj := Fobj
; fmap : forall {X Y : objC}, (X ~> Y) -> Fobj X ~> Fobj Y

; fmap_respects : forall X Y (f f' : X ~> Y), f ≈ f' -> fmap f ≈ fmap f'

; fun_identity : forall {X : objC}, fmap (@id objC homC C X) ≈ id
; fun_composition : forall {X Y Z} (f : Y ~> Z) (g : X ~> Y),
    fmap f ∘ fmap g ≈ fmap (f ∘ g)
}.

Notation "F \ f" := (fmap F f) (at level 100) : category_scope.

Add Parametric Morphism (Fobj : C -> D) (F : Functor Fobj) (a b : C)
  : fmap
  with signature ((@eqv C _ C a b) ==> (@eqv D _ D (Fobj a) (Fobj b)))
    as parametric_morphism_fmap'.
  intros; apply fmap_respects; auto.
Defined.

Coercion fobj : Functor >-> Funclass.

(* Class Bifunctor (Biobj : C -> C -> D) := *)
(* { bifunctor_biobj := Biobj *)
(* ; bimap : forall {X Y W Z : objC}, *)
(*     (X ~> W) -> (Y ~> Z) -> Biobj X Y ~> Biobj W Z *)
(* ; first  {X W : objC} (f : X ~> W) := bimap f (@id objC homC C X) *)
(* ; second {Y Z : objC} (g : Y ~> Z) := bimap (@id objC homC C Y) g *)

(* ; bimap_respects : forall X Y W Z (f f' : X ~> W) (g g' : Y ~> Z), *)
(*     f ≈ f' -> g ≈ g' -> bimap f g ≈ bimap f' g' *)

(* ; bifun_identity : forall {X : objC}, *)
(*     bimap (@id objC homC C X) (@id objC homC C X) ≈ id *)
(* ; bifun_composition : forall {X Y W Z T U} *)
(*     (f : W ~> T) (g : X ~> W) (h : Z ~> U) (i : Y ~> Z), *)
(*     bimap f h ∘ bimap g i ≈ bimap (f ∘ g) (h ∘ i) *)
(* }. *)

(* Add Parametric Morphism (Biobj : C -> C -> D) (F : Bifunctor Biobj) *)
(*   (a b c d : C) : (@bimap Biobj F a b c d) *)
(*   with signature ((@eqv C _ C a c) ==> (@eqv C _ C b d) *)
(*                     ==> (@eqv D _ D (Biobj a b) (Biobj c d))) *)
(*     as parametric_morphism_bimap'. *)
(*   intros; apply bimap_respects; auto. *)
(* Defined. *)

(* Coercion bifunctor_biobj : Bifunctor >-> Funclass. *)

Class Natural (F : C -> D) `{Functor F} (G : C -> D) `{Functor G} :=
{ transport : forall {X : objC}, F X ~> G X
; naturality : forall {X Y : objC} (f : X ~> Y),
    fmap f ∘ transport ≈ transport ∘ fmap f
}.

Definition nat_identity (F : C -> D) `{Functor F} : Natural F F.
  apply Build_Natural with (transport := fun _ => id).
  intros.
  rewrite right_identity.
  rewrite left_identity.
  reflexivity.
Defined.

Hint Unfold nat_identity.

Definition nat_compose
  {F : C -> D} `{Functor F}
  {G : C -> D} `{Functor G}
  {K : C -> D} `{Functor K}
  (f : Natural G K) (g : Natural F G) : Natural F K.
  apply Build_Natural with (transport := fun X =>
    (@transport _ _ _ _ f X) ∘ (@transport _ _ _ _ g X)).
  intros.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.

Definition nat_equiv
  {F : C -> D} `{Functor F}
  {G : C -> D} `{Functor G}
  (f g : Natural F G) :=
  forall {X : objC}, (@transport _ _ _ _ f X) ≈ (@transport _ _ _ _ g X).

Hint Unfold nat_equiv.

(* Nat is the category whose morphisms are natural transformations from
   Functor C D to Functor C D.
*)
Instance Nat : Category
  {f : C -> D & Functor f}
  (fun f g => @Natural (projT1 f) (projT2 f) (projT1 g) (projT2 g)) :=
{ id      := fun f     => @nat_identity (projT1 f) (projT2 f)
; compose := fun _ _ _ => nat_compose
; eqv     := fun _ _   => nat_equiv
}.
Proof.
  - (* eqv_equivalence *)
    constructor; autounfold;
    intros; auto; crush.
  - (* compose_respects *) crush.
  - (* right_identity *)   crush.
  - (* left_identity *)    crush.
  - (* comp_assoc *)
    intros. autounfold.
    simpl. intros.
    rewrite comp_assoc. auto.
Defined.

End Functors.

Notation "C ⟶ D" := (@Nat _ _ C _ _ D) (at level 90, right associativity).

Definition runNat
  `{C : Category objC homC}
  `{D : Category objD homD}
  (F : {k : C → D & Functor k})
  (G : {h : C → D & Functor h})
  (f : F ~{ C ⟶ D }~> G)
  `{n : @Natural objC homC C objD homD D
                 (projT1 F) (projT2 F) (projT1 G) (projT2 G)}
  {A : objC} : projT1 F A ~{ D }~> projT1 G A :=
  @transport objC homC C objD homD D
    (projT1 F) (projT2 F) (projT1 G) (projT2 G) _ A.

Definition fmap1
  `{C : Category objC homC}
  `{D : Category objD homD}
  `{E : Category objE homE}
  (P : C -> (D ⟶ E))
  {X Y : objD}
  (f : X ~{ D }~> Y)
  {A : objC} : (projT1 (P A) X ~{ E }~> projT1 (P A) Y) :=
  @fmap objD homD D objE homE E (projT1 (P A)) (projT2 (P A)) X Y f.

Definition bimap
  `{C : Category objC homC}
  `{D : Category objD homD}
  `{E : Category objE homE}
  (P : C -> (D ⟶ E))
  `{@Functor objC homC C
     {f : D -> E & Functor f}
     (fun f g => @Natural objD homD D objE homE E
                          (projT1 f) (projT2 f) (projT1 g) (projT2 g))
     (D ⟶ E)
     P}
  {X W : objC} {Y Z : objD}
  `{@Natural objD homD D objE homE E
             (projT1 (P X)) (projT2 (P X)) (projT1 (P W)) (projT2 (P W))}
  (f : X ~{ C }~> W) (g : Y ~{ D }~> Z)
  : (projT1 (P X) Y ~{ E }~> projT1 (P W) Z) :=
  runNat (P X) (P W) (@fmap _ _ C _ _ (D ⟶ E) P _ X W f) ∘ fmap1 P g.

(* Notation "F ⟶ G" := (Functor F G) (at level 9). *)
Notation "F ⟹ G" := (@transport F _ G _) (at level 40).

Definition Id `(C : Category objC homC) : Functor C C (fun X => X).
  apply Build_Functor with (fmap := fun X X f => f).
  - (* fmap_respects *)   crush.
  - (* fun_identity *)    crush.
  - (* fun_composition *) crush.
Defined.

Definition Hom_map `(C : Category objC homC) (A : objC)
  {X Y : objC} (f : X ~> Y) (g : A ~> X) : A ~> Y := f ∘ g.

Definition Hom `(C : Category objC homC) (A : objC)
  : Functor C Sets (fun X => A ~> X).
  apply Build_Functor with (fmap := @Hom_map _ _ _ A).
  - (* fmap_respects *)
    intros. unfold Hom_map.
    unfold compose.
    pose (@eqv _ _ _ X Y f f').
  - (* fun_identity *)
    intros. unfold Hom_map. reduce.
  - (* fun_composition *) crush.
Defined.

Reserved Notation "f ⊕ g" (at level 47, right associativity).

Class Monoidal `(C : Category objC homC)
  (ε : objC) (mappend : objC -> objC -> objC) :=
{ monoidal_left  : Hom(ε)  ⟹ Id
; monoidal_right : CHom(ε) ⟹ Id
; monoidal_assoc : forall a b c : objC,
    mappend (mappend a b) c ≈ mappend a (mappend b c)
}.

Notation "f ⊕ g" := (MAppend f g) (at level 47, right associativity).

Definition Tuple_map {Z X Y} (f : X -> Y) (p : Z * X) : Z * Y :=
  match p with
  | pair z x => @pair Z Y z (f x)
  end.

Definition Tuple_Functor {Z} : Functor Coq Coq (fun (X : Type) => Z * X).
  apply Build_Functor with (fmap := @Tuple_map Z).
  - (* fmap_respects *)   crush.
  - (* fun_identity *)    crush.
  - (* fun_composition *) crush.
Defined.

Definition Tuple_bimap {X Y W Z} (f : X -> W) (g : Y -> Z)
  (p : X * Y) : W * Z :=
  match p with
  | pair z x => @pair W Z (f z) (g x)
  end.

Definition Tuple_Bifunctor : Bifunctor Coq Coq (fun (X Y : Type) => X * Y).
  apply Build_Bifunctor with (bimap := @Tuple_bimap).
  - (* bimap_respects *)    crush.
  - (* bifun_identity *)    crush.
  - (* bifun_composition *) crush.
Defined.

Inductive Either (E X : Type) :=
  | Left : E -> Either E X
  | Right : X -> Either E X.

Definition Either_map {Z X Y} (f : X -> Y) (p : Either Z X) : Either Z Y :=
  match p with
  | Left z => Left Z Y z
  | Right x => Right Z Y (f x)
  end.

Definition Either_Functor {Z} : Functor Coq Coq (fun (X : Type) => Either Z X).
  apply Build_Functor with (fmap := @Either_map Z).
  - (* fmap_respects *)   crush.
  - (* fun_identity *)    crush.
  - (* fun_composition *) crush.
Defined.

Definition Either_bimap {X Y W Z} (f : X -> W) (g : Y -> Z)
  (p : Either X Y) : Either W Z :=
  match p with
  | Left z => Left W Z (f z)
  | Right x => Right W Z (g x)
  end.

Definition Either_Bifunctor : Bifunctor Coq Coq (fun (X Y : Type) => Either X Y).
  apply Build_Bifunctor with (bimap := @Either_bimap).
  - (* bimap_respects *)    crush.
  - (* bifun_identity *)    crush.
  - (* bifun_composition *) crush.
Defined.
