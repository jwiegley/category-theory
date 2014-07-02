Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Setoids.Setoid.
Require        Setoid.
Require Export CpdtTactics.

Open Scope type_scope.

Ltac inv H := inversion H; subst; clear H.

(* Proof General seems to add an extra two columns of overhead *)
Set Printing Width 130.
Generalizable All Variables.

(* Unicode → is used to describe morphisms, even though it is rather similar
   to the way ASCII -> is displayed in Emacs.

   Unicode ≈ means equivalence, while ≅ is isomorphism and = is identity.

   Unicode ∘ is composition of morphisms.

   -{ C }-> specifically types a morphism as being in category C.
*)
Reserved Notation "a → b" (at level 90, right associativity).
Reserved Notation "f ≈ g" (at level 54).
Reserved Notation "f ∘ g" (at level 45).

(* A Category is defined by objects and morphisms between objects, plus the
   following structure:

   - Every object has an identity morphism.
   - Morphisms compose.

   - Composition respect a monoidal structure: left and right identity with
     identity morphisms, and associativity.

   - There is a notion of equivalence of morphsims in the category.
   - Composition must respect equivalence.
*)
Class Category (Ob : Type) (Hom : Ob -> Ob -> Type) :=
{ hom := Hom where "a → b" := (hom a b)
; ob  := Ob

; id : forall {A}, A → A
; compose : forall {A B C}, (B → C) -> (A → B) -> (A → C)
  where "f ∘ g" := (compose f g)
; eqv : forall {A B}, (A → B) -> (A → B) -> Prop where "f ≈ g" := (eqv f g)

; eqv_equivalence : forall {A B}, Equivalence (@eqv A B)
; compose_respects : forall {A B C}, Proper (@eqv B C ==> @eqv A B ==> @eqv A C) compose

; right_identity : forall {A B} (f : A → B), f ∘ id ≈ f
; left_identity : forall {A B} (f : A → B), id ∘ f ≈ f
; comp_assoc : forall {A B C D} (f : C → D) (g : B → C) (h : A → B) ,
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
}.

Coercion ob : Category >-> Sortclass.

Notation "a → b" := (hom a b) : category_scope.
Notation "f ≈ g" := (eqv f g) : category_scope.
Notation "f ∘ g" := (compose f g) : category_scope.
Notation "a -{ C }-> b" := (@hom _ _ C a b) (at level 100) : category_scope.

Open Scope category_scope.

Hint Extern 3 => apply compose_respects.
Hint Extern 1 => apply left_identity.
Hint Extern 1 => apply right_identity.

Add Parametric Relation (Ob : Type) (Hom : Ob -> Ob -> Type)
  `(C : Category Ob Hom) (a b : Ob) : (hom a b) (@eqv _ _ C a b)

  reflexivity proved by  (@Equivalence_Reflexive  _ _ eqv_equivalence)
  symmetry proved by     (@Equivalence_Symmetric  _ _ eqv_equivalence)
  transitivity proved by (@Equivalence_Transitive _ _ eqv_equivalence)
    as parametric_relation_eqv.

  Add Parametric Morphism `(c : Category Ob Hom) (a b c : Ob)
    : (@compose _ _ _ a b c)
    with signature (eqv ==> eqv ==> eqv) as parametric_morphism_comp.
    auto.
  Defined.

Hint Constructors Equivalence.

Hint Unfold Reflexive.
Hint Unfold Symmetric.
Hint Unfold Transitive.

Hint Extern 1 (Proper _ _) => unfold Proper; auto.
Hint Extern 1 (Reflexive ?X) => unfold Reflexive; auto.
Hint Extern 1 (Symmetric ?X) => unfold Symmetric; intros; auto.
Hint Extern 1 (Transitive ?X) => unfold Transitive; intros; auto.
Hint Extern 1 (Equivalence ?X) => apply Build_Equivalence.
Hint Extern 8 (respectful _ _ _ _) => unfold respectful; auto.

Hint Extern 4 (?A ≈ ?A) => reflexivity.
Hint Extern 6 (?X ≈ ?Y) => apply Equivalence_Symmetric.
Hint Extern 7 (?X ≈ ?Z) => match goal
  with [H : ?X ≈ ?Y, H' : ?Y ≈ ?Z |- ?X ≈ ?Z] => transitivity Y end.
Hint Extern 10 (?X ∘ ?Y ≈ ?Z ∘ ?Q) => apply compose_respects; auto.

(* The following are handy for rewriting. *)

Lemma juggle1
  : forall `{C : Category} `(f : d → e) `(g : c → d) `(h : b → c) `(k : a → b),
  ((f ∘ g) ∘ h) ∘ k ≈ f ∘ (g ∘ h) ∘ k.
  intros; repeat setoid_rewrite <- comp_assoc. reflexivity.
  Defined.

Lemma juggle2
  : forall `{C : Category} `(f : d → e) `(g : c → d) `(h : b → c) `(k : a → b),
  f ∘ (g ∘ (h ∘ k)) ≈ f ∘ (g ∘ h) ∘ k.
  intros; repeat setoid_rewrite <- comp_assoc. reflexivity.
  Defined.

Lemma juggle3
  : forall `{C : Category} `(f : d → e) `(g : c → d) `(h : b → c) `(k : a → b),
  (f ∘ g) ∘ (h ∘ k) ≈ f ∘ (g ∘ h) ∘ k.
  intros; repeat setoid_rewrite <- comp_assoc. reflexivity.
  Defined.

(* Coq is the category of Coq types and functions. *)
Global Instance Coq : Category Type (fun X Y => X -> Y) :=
{ id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
; eqv     := fun X Y f g => forall {x : X}, f x = g x
}.
Proof.
  (* The proofs of all of these follow trivially from their definitions. *)
  - (* eqv_equivalence *)  crush.
  - (* compose_respects *) crush.
  - (* right_identity *)   crush.
  - (* left_identity *)    crush.
  - (* comp_assoc *)       crush.
Defined.

Definition homomorphisms A := A -> A -> Type.

Record category := mkCat
{ objs : Type
; homs : homomorphisms objs
; cat  : Category objs homs
}.

Class Functor `(C : Category objC homC, D : Category objD homD)
  (Fobj : C -> D) :=
{ functor_fobj := Fobj
; fmap : forall {X Y : objC}, (X → Y) -> Fobj X → Fobj Y

; fmap_respects : forall X Y (f f' : X → Y), f ≈ f' -> fmap f ≈ fmap f'

; fun_identity : forall {X : objC}, fmap (@id objC homC C X) ≈ id
; fun_composition : forall {X Y Z} (f : Y → Z) (g : X → Y),
    fmap f ∘ fmap g ≈ fmap (f ∘ g)
}.
  (* register "fmap" so we can rewrite through it *)
  Arguments fmap            [ objC homC C objD homD D Fobj Functor X Y _ ].
  Arguments fmap_respects   [ objC homC C objD homD D Fobj Functor X Y _ _ _ ].
  Arguments fun_identity    [ objC homC C objD homD D Fobj Functor _ ].
  Arguments fun_composition [ objC homC C objD homD D Fobj Functor X Y Z _ _ ].

  Notation "F \ f" := (fmap F f) (at level 100) : category_scope.

  Add Parametric Morphism `(C1 : Category, C2 : Category)
    (Fobj : C1 -> C2)
    (F : Functor C1 C2 Fobj)
    (a b : C1)
    : (@fmap _ _ C1 _ _ C2 Fobj F a b)
    with signature ((@eqv C1 _ C1 a b) ==> (@eqv C2 _ C2 (Fobj a) (Fobj b)))
      as parametric_morphism_fmap'.
    intros; apply fmap_respects; auto.
  Defined.

Coercion functor_fobj : Functor >-> Funclass.

Inductive Maybe (X : Type) :=
  | Nothing : Maybe X
  | Just    : X -> Maybe X.

Definition Maybe_map {X Y} (f : X -> Y) (x : Maybe X) : Maybe Y :=
  match x with
   | Nothing => Nothing Y
   | Just x' => Just Y (f x')
  end.

Definition Maybe_Functor : Functor Coq Coq Maybe.
  apply Build_Functor with (fmap := @Maybe_map).
  - (* fmap_respects *)
    intros. reduce. unfold Maybe_map. destruct x.
      reflexivity.
      reduce_hyp H. f_equal. apply H.
  - (* fun_identity *)
    intros. reduce. unfold Maybe_map. destruct x; reflexivity.
  - (* fun_composition *)
    intros. reduce. unfold Maybe_map. destruct x; reflexivity.
Defined.

Inductive prod_obj `{C : Category objC homC} : Type :=
  pair_obj (x : ob) (y : ob) : prod_obj.

Definition fst_obj `{C : Category objC homC}
  (x : prod_obj) : ob :=
  match x with pair_obj a _ => a end.

(* Definition snd_obj x := match x with pair_obj _ b => b end. *)

Class Product `{C : Category objC homC}
  {A B : objC} (P : objC) (p1 : P → A) (p2 : P → B) :=
{ product_ump :
    forall (X : objC) (x1 : X → A) (x2 : X → B),
    exists (u : X → P), x1 ≈ p1 ∘ u /\ x2 ≈ p2 ∘ u
    /\ forall (v : X → P), p1 ∘ v ≈ x1 /\ p2 ∘ v ≈ x2 -> v ≈ u
}.

Inductive Tuple (X Y : Type) : Type := | Pair : X -> Y -> Tuple X Y.

(*
Definition fst {X Y} (p : Tuple X Y) : X := match p with Pair x _ => x end.
Definition snd {X Y} (p : Tuple X Y) : Y := match p with Pair _ y => y end.
*)

(* Tuples in the Coq category satisfy the UMP for products. *)
Global Instance Tuple_Product {A B : Type} : Product (A * B) fst snd.
Proof.
  intros. constructor. intros.
    apply ex_intro with (x := fun x => Pair A B (x1 x) (x2 x)).
    split.
      reduce. reflexivity.
      split.
        reduce. reflexivity.
        intros. reduce. inv H.
          reduce in H0. specialize (H0 x). rewrite <- H0.
          reduce in H1. specialize (H1 x). rewrite <- H1.
          compute. destruct (v x). reflexivity.
Defined.

(*
Definition Ctxt : list (Tuple nat Type).

Inductive Term (Γ : Ctxt) (a : Type) : Type :=
  | Var : (x : nat) -> Pair x a ∈ Γ -> Term Γ a

Global Instance Lamdba : Category Type (fun X Y => X -> Y) :=
{ id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
; eqv     := fun X Y f g => forall {x : X}, f x = g x
}.
Proof.
  (* The proofs of all of these follow trivially from their definitions. *)
  - (* eqv_equivalence *)  crush.
  - (* compose_respects *) crush.
  - (* right_identity *)   crush.
  - (* left_identity *)    crush.
  - (* comp_assoc *)       crush.
Defined.
*)