(* NOTE: In curried category theory, Op is Yoneda. *)

(*
Lemma cat_irrelevance `(C : Category) `(D : Category)
  : forall (m n : ∀ {A}, A ~> A)
           (p q : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C))
           l l' r r' c c',
  @m = @n ->
  @p = @q ->
  {| ob             := C
   ; hom            := @hom C
   ; id             := @m
   ; compose        := @p
   ; left_identity  := l
   ; right_identity := r
   ; comp_assoc     := c
 |} =
  {| ob             := C
   ; hom            := @hom C
   ; id             := @n
   ; compose        := @q
   ; left_identity  := l'
   ; right_identity := r'
   ; comp_assoc     := c'
 |}.
Proof.
  intros. subst.
  f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.
*)

(* Cat is the category of all locally small categories.  We cannot represent
   this in Coq without universe polymorphism. *)

(*
Program Instance Cat : Category :=
{ ob      := Category
; hom     := Functor
; id      := Id
; compose := @fun_compose
}.
Obligation 1.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Abort.
Obligation 2.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Abort.
Obligation 3.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  reflexivity.
Abort.
*)

(* Representing Hom functors as functiors from C ⟶ Sets will also need
   universe polymorphism.
*)

(*
Instance CoHom `(C : Category) (X : C) : C ⟶ Sets :=
{ fobj := fun Y => X ~> Y
; fmap := fun _ _ f g => f ∘ g
}.
Proof.
  - (* fun_identity *)    intros. extensionality e. crush.
  - (* fun_composition *) intros. extensionality e. crush.
Abort.

Instance Hom `(C : Category) : C ⟶ C ⟹ Sets :=
{ fobj := @CoHom C
; fmap := fun X Y f => @transport C (C ⟹ Sets) f _ _ _
}.
Proof.
  - (* fun_identity *)    intros. extensionality e. crush.
  - (* fun_composition *) intros. extensionality e. crush.
Abort.
*)

(*
Definition Either_map {Z X Y} (f : X → Y) (p : @Either Z X) : @Either Z Y :=
  match p with
  | Left z => Left z
  | Right x => Right (f x)
  end.

Program Instance Either_Functor (Z : Type) : Coq ⟶ Coq :=
{ fobj := @Either Z
; fmap := @Either_map Z
}.
Obligation 1. extensionality e. crush. Defined.
Obligation 2. extensionality e. crush. Defined.

Program Instance Either_Natural `(f : X → Y)
  : Either_Functor X ⟾ Either_Functor Y :=
{ transport := fun X e =>
    match e with
    | Left x => Left (f x)
    | Right x => Right x
    end
}.
Obligation 1. extensionality e. crush. Defined.
*)

(* Reserved Notation "f ⊕ g" (at level 47, right associativity). *)

(* Class Monoidal `(C : Category objC) *)
(*   (ε : objC) (mappend : objC → objC → objC) := *)
(* { monoidal_left  : Hom(ε)  ⟹ Id *)
(* ; monoidal_right : CHom(ε) ⟹ Id *)
(* ; monoidal_assoc : ∀ a b c : objC, *)
(*     mappend (mappend a b) c = mappend a (mappend b c) *)
(* }. *)

(* Notation "f ⊕ g" := (MAppend f g) (at level 47, right associativity). *)
